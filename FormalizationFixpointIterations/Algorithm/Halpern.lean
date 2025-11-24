import FormalizationFixpointIterations.Nonexpansive.Definitions
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Function
import FormalizationFixpointIterations.Theory.WeakSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.PNat.Basic

open Nonexpansive_operator Filter Topology BigOperators Function
set_option linter.unusedSectionVars false
set_option maxHeartbeats 999999999
set_option linter.style.commandStart false
set_option maxRecDepth 2000

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

structure Halpern (T : H → H) where
  x0 : H
  u : H  -- 30.1中的x
  x : ℕ → H
  α : ℕ → ℝ
  update : ∀ k : ℕ, x (k + 1) = (α k) • u + (1 - α k) • (T (x k))
  initial_value : x 0 = x0

#check norm_eq_iInf_iff_real_inner_le_zero--投影的形式

lemma log_ineq (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 1) :
  Real.log (1 - ξ) ≤ -ξ := by
  have h1 : 1 - ξ > 0 := by
    simp [Set.mem_Ioo] at hξ
    linarith
  have h2 : 1 - ξ < 1 := by
    simp [Set.mem_Ioo] at hξ
    linarith
  -- 使用 log(x) ≤ x - 1 对所有 x > 0
  have key : Real.log (1 - ξ) ≤ (1 - ξ) - 1 := Real.log_le_sub_one_of_pos h1
  linarith

lemma one_sub_pos_of_mem_Ioo {a : ℝ} (ha : a ∈ Set.Ioo 0 1) : 0 < 1 - a :=
  sub_pos.mpr ha.2

lemma prod_exp_sum
  {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (m n : ℕ) :
  ∏ x ∈ Finset.Icc m n, (1 - alg.α x) =
    Real.exp (∑ x ∈ Finset.Icc m n, Real.log (1 - alg.α x)) ∧
  Real.exp (∑ x ∈ Finset.Icc m n, Real.log (1 - alg.α x)) ≤
    Real.exp (∑ x ∈ Finset.Icc m n, -alg.α x) := by
  constructor
  · symm
    rw [Real.exp_sum]
    apply Finset.prod_congr
    · ext x
      simp
    intro x
    have hk : x ∈ Finset.Icc m n → 1 - alg.α x > 0 := by
      intro hk_mem
      have := h_α_range x
      simp [Set.mem_Ioo] at this
      linarith
    intro hx
    rw [Real.exp_log]
    exact hk hx
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro x hx
  exact log_ineq (alg.α x) (h_α_range x)

-- 30.4
lemma infinite_prod_zero
  {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N,
    alg.α n) atTop atTop)
  (m : ℕ) :
  Tendsto (fun n => ∏ k ∈ Finset.Icc m n, (1 - alg.α k)) atTop (𝓝 0) := by
  have h_prod_eq : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) =
      Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) := by
    intro n hn
    exact (prod_exp_sum alg h_α_range m n).1
  have h_exp_le : ∀ n ≥ m, Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) ≤
      Real.exp (∑ k ∈ Finset.Icc m n, -alg.α k) := by
    intro n hn
    exact (prod_exp_sum alg h_α_range m n).2
  have h_prod_le : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) ≤
      Real.exp (- ∑ k ∈ Finset.Icc m n, alg.α k) := by
    intro n hn
    rw [h_prod_eq n hn]
    convert h_exp_le n hn using 2
    simp [Finset.sum_neg_distrib]
  have h_prod_nonneg : ∀ n ≥ m, 0 ≤ ∏ k ∈ Finset.Icc m n, (1 - alg.α k) := by
    intro n hn
    apply Finset.prod_nonneg
    intro k hk
    have h_range := h_α_range k
    simp [Set.mem_Ioo] at h_range
    linarith
  have h_sum_icc_inf : Tendsto (fun n => ∑ k ∈ Finset.Icc m n, alg.α k) atTop atTop := by
    have h_decomp : ∀ n ≥ m,
        ∑ k ∈ Finset.range (n + 1), alg.α k =
        (∑ k ∈ Finset.range m, alg.α k) + (∑ k ∈ Finset.Icc m n, alg.α k) := by
      intro n hn
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_succ_of_le hn)]
      congr 1
    let C := ∑ k ∈ Finset.range m, alg.α k
    have h_eq : ∀ n ≥ m, ∑ k ∈ Finset.Icc m n, alg.α k =
        (∑ k ∈ Finset.range (n + 1), alg.α k) - C := by
      intro n hn
      have := h_decomp n hn
      linarith
    -- 现在证明收敛性
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp h_α_sum_inf) (b + C)
    use max m N
    intro n hn
    have hn_m : n ≥ m := le_of_max_le_left hn
    have hn_N : n ≥ N := le_of_max_le_right hn
    rw [h_eq n hn_m]
    have : ∑ k ∈ Finset.range (n + 1), alg.α k ≥ b + C := by
      apply hN
      omega
    linarith
  have h_neg_sum : Tendsto (fun n => -∑ k ∈ Finset.Icc m n, alg.α k) atTop atBot := by
    simpa
  have h_exp_to_zero : Tendsto (fun n => Real.exp
    (- ∑ k ∈ Finset.Icc m n, alg.α k)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_neg_sum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_exp_to_zero ?_ ?_
  · intro n
    apply Finset.prod_nonneg
    intro k _
    have := h_α_range k
    simp [Set.mem_Ioo] at this
    linarith
  · intro n
    by_cases hn : n ≥ m
    · exact h_prod_le n hn
    · simp [Finset.Icc_eq_empty_of_lt (Nat.not_le.mp hn)]

-- 4.23(i)
-- 拟非扩张映射的不动点集刻画
lemma quasinonexpansive_fixedPoint_characterization
  {D : Set H}
  (hD_nonempty : D.Nonempty)
  {T : H → H}
  (hT_quasi : QuasiNonexpansiveOn T D)
  : Fix T ∩ D = ⋂ x ∈ D, {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} := by
  ext y
  constructor
  · intro ⟨hy_fix, hy_D⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro x hx
    constructor
    · exact hy_D
    · have h_fix : IsFixedPt T y := hy_fix
      have hy_in_fix' : y ∈ Fix' T D := ⟨hy_D, h_fix⟩
      have h_quasi := hT_quasi hx hy_in_fix'
      have h_norm_sq : ‖T x - y‖^2 ≤ ‖x - y‖^2 := by
        apply sq_le_sq'
        · linarith [norm_nonneg (T x - y)]
        · exact h_quasi
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h_norm_sq
      have eq1 : inner ℝ (T x - y) (T x - y) = inner ℝ (T x - x) (T x - x) +
        2 * inner ℝ (T x - x) (x - y) + inner ℝ (x - y) (x - y) := by
        rw [← sub_add_sub_cancel (T x) y x]
        simp only [inner_add_left, inner_add_right,
          inner_sub_left, inner_sub_right, real_inner_comm]
        ring_nf
      rw [eq1] at h_norm_sq
      have eq2 : inner ℝ (T x - x) (T x - x) +
        2 * inner ℝ (T x - x) (x - T x) +  2 * inner ℝ (T x - x) (T x - y) ≤ 0 := by
        calc
          _ = inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - y) := by
            simp [inner_sub_left, inner_sub_right, real_inner_comm]
            ring_nf
          _ ≤ 0 := by linarith
      calc
        inner ℝ (y - T x) (x - T x)
          = -inner ℝ (y - T x) (T x - x) := by
            rw [inner_sub_right, inner_sub_right]
            ring
        _ ≤ -(inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)) / 2 := by
          have h_extract : 2 * inner ℝ (T x - x) (T x - y) ≤
              -(inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)) := by
            linarith [eq2]
          have h_div : inner ℝ (T x - x) (T x - y) ≤
              -(inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)) / 2 := by
            linarith [h_extract]
          have h_neg : inner ℝ (T x - x) (T x - y) = -inner ℝ (T x - x) (y - T x) := by
            rw [inner_sub_right, inner_sub_right]
            ring
          have h_sym : inner ℝ (T x - x) (y - T x) = inner ℝ (y - T x) (T x - x) :=
            real_inner_comm _ _
          linarith [h_div, h_neg, h_sym]
        _ = (1/2) * ‖T x - x‖^2 := by
          rw [real_inner_self_eq_norm_sq, mul_comm]
          have h_neg : inner ℝ (T x - x) (x - T x) = - inner ℝ (T x - x) (T x - x) := by
            rw [inner_sub_right, inner_sub_right]
            ring
          rw [h_neg]
          simp
          rw [real_inner_self_eq_norm_sq]
          ring_nf
  · intro hy
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
    constructor
    · obtain ⟨x0, hx0⟩ := hD_nonempty
      have hy_D : y ∈ D := (hy x0 hx0).1
      have h_y : inner ℝ (y - T y) (y - T y) ≤ 1 / 2 * ‖T y - y‖ ^ 2 := (hy y hy_D).2
      have h_eq : inner ℝ (y - T y) (y - T y) = ‖y - T y‖ ^ 2 := real_inner_self_eq_norm_sq _
      -- 注意 ‖y - T y‖² = ‖T y - y‖²
      have h_sym : ‖y - T y‖ ^ 2 = ‖T y - y‖ ^ 2 := by
        rw [norm_sub_rev]
      rw [h_eq, h_sym] at h_y
      have : (1/2) * ‖T y - y‖ ^ 2 ≤ 0 := by linarith
      have h_zero : ‖T y - y‖ ^ 2 = 0 := by
        have h_nonneg : 0 ≤ ‖T y - y‖ ^ 2 := sq_nonneg _
        linarith
      have : ‖T y - y‖ = 0 := by
        have := sq_eq_zero_iff.mp h_zero
        exact this
      exact eq_of_norm_sub_eq_zero this
    · obtain ⟨x0, hx0⟩ := hD_nonempty
      exact (hy x0 hx0).1

-- 辅助引理1：半空间是闭集
lemma halfspace_is_closed (a b : H) (c : ℝ) :
    IsClosed {x : H | ⟪x - a, b⟫ ≤ c} := by
  -- 内积是连续函数，因此原像是闭集
  have : {x : H | ⟪x - a, b⟫ ≤ c} = (fun x => ⟪x - a, b⟫) ⁻¹' Set.Iic c := by
    ext x
    simp [Set.mem_Iic]
  rw [this]
  apply IsClosed.preimage
  · apply Continuous.inner
    · exact continuous_id.sub continuous_const
    · exact continuous_const
  · exact isClosed_Iic

-- 辅助引理2：半空间是凸集
lemma halfspace_is_convex (a b : H) (c : ℝ) :
    Convex ℝ {x : H | ⟪x - a, b⟫ ≤ c} := by
  intro x hx y hy t1 t2 ht1 ht2 ht
  simp at hx hy ⊢
  -- 利用内积的线性性
  calc
    ⟪t1 • x + t2 • y - a, b⟫
      = ⟪t1 • x + t2 • y - (t1 • a + t2 • a), b⟫ := by
        congr 1
        rw [← add_smul]
        simp [ht]
    _ = ⟪t1 • (x - a) + t2 • (y - a), b⟫ := by
        congr 1
        simp [smul_sub, sub_add_eq_sub_sub, add_sub, add_comm]
    _ = t1 * ⟪x - a, b⟫ + t2 * ⟪y - a, b⟫ := by
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        norm_cast
    _ ≤ t1 * c + t2 * c := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hx ht1
        · exact mul_le_mul_of_nonneg_left hy (by linarith)
    _ = c := by
        rw [← add_mul]
        simp [ht]

-- 主引理：交集中每个集合都是闭凸集
lemma intersection_set_is_closed_convex
    {D : Set H}
    (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D)
    {T : H → H}
    (x : H) :
    IsClosed {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} ∧
    Convex ℝ {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} := by
  constructor
  · -- 闭性
    apply IsClosed.inter hD_closed
    exact halfspace_is_closed (T x) (x - T x) ((1/2) * ‖T x - x‖^2)
  · -- 凸性
    apply Convex.inter hD_convex
    exact halfspace_is_convex (T x) (x - T x) ((1/2) * ‖T x - x‖^2)

-- prop 4.23(ii)
-- 推论：不动点集的闭凸性
lemma quasinonexpansive_fixedPoint_closed_convex
  {D : Set H}
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  (hD_nonempty : D.Nonempty)
  {T : H → H}
  (hT_quasi : QuasiNonexpansiveOn T D)
  : IsClosed (Fix T ∩ D) ∧ Convex ℝ (Fix T ∩ D) := by
  rw [quasinonexpansive_fixedPoint_characterization hD_nonempty hT_quasi]
  constructor
  · apply isClosed_biInter
    intro x hx
    exact (intersection_set_is_closed_convex hD_closed hD_convex x).1
  · apply convex_iInter₂
    intro x hx
    exact (intersection_set_is_closed_convex hD_closed hD_convex x).2

-- quasi可以推出nonexpansive
lemma nonexpansive_leadsto_quasinonexpansive
  {D : Set H}
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D) :
  QuasiNonexpansiveOn T D := by
  intro x hx y hy
  rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
  rw [Fix'] at hy
  rcases hy with ⟨hyD,hyFix⟩
  have h_edist := hT_nonexp hx hyD
  simp only [ENNReal.coe_one, one_mul] at h_edist
  rw [hyFix] at h_edist
  rw [edist_dist, edist_dist] at h_edist
  have h_dist : dist (T x) y ≤ dist x y := by
    have h_nonneg1 : 0 ≤ dist (T x) y := dist_nonneg
    have h_nonneg2 : 0 ≤ dist x y := dist_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff h_nonneg2).mp h_edist
  rw [dist_eq_norm, dist_eq_norm] at h_dist
  exact h_dist

-- ln ∏ ≤ - Σ
lemma log_prod_one_sub_le_neg_sum
    {α : ℕ → ℝ} (m n : ℕ)
    (hα : ∀ k, α k ∈ Set.Ioo 0 1) :
    Real.log (∏ k ∈ Finset.Icc m n, (1 - α (k + 1)))
      ≤ - ∑ k ∈ Finset.Icc m n, α (k + 1) := by
  classical
  have hpos : ∀ k ∈ Finset.Icc m n, 0 < (1 - α (k + 1)) := by
    intro k hk; exact one_sub_pos_of_mem_Ioo (hα (k + 1))
  have hlog :
      Real.log (∏ k ∈ Finset.Icc m n, (1 - α (k + 1)))
        = ∑ k ∈ Finset.Icc m n, Real.log (1 - α (k + 1)) := by
    apply Real.log_prod _ _
    intro k hk
    exact Ne.symm (ne_of_lt (hpos k hk))
  have hterm :
      ∀ k ∈ Finset.Icc m n, Real.log (1 - α (k + 1)) ≤ - α (k + 1) := by
    intro k hk; exact log_ineq (α (k+1)) (hα (k+1))
  simpa [hlog] using Finset.sum_le_sum hterm

-- ∏ ≤ exp(- Σ)
lemma pro_one_sub_le_exp_neg_sum
    {α : ℕ → ℝ} (m n : ℕ)
    (hα : ∀ k, α k ∈ Set.Ioo 0 1) :
    ∏ k ∈ Finset.Icc m n, (1 - α (k + 1))
      ≤ Real.exp (- ∑ k ∈ Finset.Icc m n, α (k + 1)) := by
  have hlog_le := log_prod_one_sub_le_neg_sum m n hα
  rw [← Real.exp_le_exp] at hlog_le
  rw [Real.exp_log] at hlog_le
  · exact hlog_le
  have h_nonneg : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - α (k + 1)) ≥ 0 := by
    intro n hn
    apply Finset.prod_nonneg
    intro k hk
    have h_range := hα (k + 1)
    simp [Set.mem_Ioo] at h_range
    linarith
  have h_pos : ∀ k ∈ Finset.Icc m n, 0 < (1 - α (k + 1)) := by
    intro k hk; exact one_sub_pos_of_mem_Ioo (hα (k + 1))
  have : ∏ k ∈ Finset.Icc m n, (1 - α (k + 1)) > 0 := by
    apply Finset.prod_pos
    intro k hk
    exact h_pos k hk
  linarith

lemma halpern_distance_monotone
  {D : Set H}
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D)
  {C : Set H}
  (hC : C = Fix T ∩ D)
  (alg : Halpern T)
  (halg_x0 : alg.x0 ∈ D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (coincidence : alg.u = alg.x0)
  :
  ∀ z ∈ C, ∀ n,
    ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧
    ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖ := by
  -- 由非扩张性推出拟非扩张性
  have hT_quasinonexp := nonexpansive_leadsto_quasinonexpansive hT_nonexp
  intro z hzC n
  induction n with
  | zero =>
    constructor
    · -- 第一步：T 在不动点上是拟非扩张的
      have hz_in_fixD : z ∈ Fix T ∩ D := by convert hzC; exact hC.symm
      have ⟨hz_fix, hz_D⟩ := hz_in_fixD
      have hz_in_fix' : z ∈ Fix' T D := ⟨hz_D, hz_fix⟩
      rw [alg.initial_value]
      exact hT_quasinonexp halg_x0 hz_in_fix'
    · -- n=0 时，‖x₀ - z‖ ≤ ‖x₀ - z‖
      rw [alg.initial_value]
  | succ k ih =>
    constructor
    · -- 第一步：在第 k+1 步仍然保持拟非扩张性
      have hz_in_fixD : z ∈ Fix T ∩ D := by convert hzC; exact hC.symm
      have ⟨hz_fix, hz_D⟩ := hz_in_fixD
      have hz_in_fix' : z ∈ Fix' T D := ⟨hz_D, hz_fix⟩
      exact hT_quasinonexp (halg_x_in_D (k+1)) hz_in_fix'
    · -- 第二步：利用归纳假设，证明距离被 ‖x₀ - z‖ 控制
      rw [alg.update]
      calc
        ‖alg.α k • alg.u + (1 - alg.α k) • T (alg.x k) - z‖
            = ‖alg.α k • (alg.u - z) + (1 - alg.α k) • (T (alg.x k) - z)‖ := by
              congr 1; simp [smul_sub, sub_smul, add_sub, add_comm]
        _ ≤ alg.α k * ‖alg.u - z‖ + (1 - alg.α k) * ‖T (alg.x k) - z‖ := by
              -- 使用范数的凸性不等式
              apply norm_add_le_of_le
              · simp [norm_smul]
                gcongr
                have hα_pos : 0 < alg.α k := by
                  have := h_α_range k
                  simp [Set.mem_Ioo] at this
                  exact this.1
                rw [abs_of_pos hα_pos]
              · simp [norm_smul]
                gcongr
                have h1_minus_α_pos : 0 < 1 - alg.α k := by
                  have := h_α_range k
                  simp [Set.mem_Ioo] at this
                  linarith
                rw [abs_of_pos h1_minus_α_pos]
        _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x k - z‖ := by
              -- 这里用到 u = x₀
              rw [← coincidence]
              gcongr
              · have := h_α_range k
                simp [Set.mem_Ioo] at this
                linarith
              · exact ih.1
        _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x0 - z‖ := by
              -- 再次利用归纳假设 ih.2
              gcongr
              · have := h_α_range k
                simp [Set.mem_Ioo] at this
                linarith
              · exact ih.2
        _ = ‖alg.x0 - z‖ := by ring

-- μ is bounded
lemma halpern_mu_bound
  {T : H → H}
  (alg : Halpern T)
  {y : H}
  -- 三个前提：差分、Tx 偏差、序列均有统一上界
  (h_diff_bounded : ∃ M1, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M1)
  (h_Tx_bounded : ∃ M2, ∀ n, ‖T (alg.x n) - y‖ ≤ M2)
  (h_seq_bounded : ∃ M3, ∀ n, ‖alg.x n - y‖ ≤ M3)
  :
  ∃ μ : ℝ, μ > 0 ∧
    (∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ) ∧
    (∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ) := by
  -- 取各自的上界
  obtain ⟨M1, hM1⟩ := h_diff_bounded
  obtain ⟨M2, hM2⟩ := h_Tx_bounded
  obtain ⟨M3, hM3⟩ := h_seq_bounded
  -- 统一的 μ
  let μ := M1 + M2 + M3 + ‖alg.u - y‖ + 1
  refine ⟨μ, ?hpos, ?hstep, ?huTx⟩
  -- 证明 μ > 0
  · simp [μ]
    have hM1_nonneg : 0 ≤ M1 := by
      have := hM1 0; exact le_trans (norm_nonneg _) this
    have hM2_nonneg : 0 ≤ M2 := by
      have := hM2 0; exact le_trans (norm_nonneg _) this
    have hM3_nonneg : 0 ≤ M3 := by
      have := hM3 0; exact le_trans (norm_nonneg _) this
    have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _
    linarith
  -- 证明 ‖x_{n+1} - x_n‖ ≤ μ
  · intro n
    calc
      ‖alg.x (n + 1) - alg.x n‖
          = ‖(alg.x (n + 1) - T (alg.x n)) + (T (alg.x n) - alg.x n)‖ := by
            abel_nf
      _ ≤ ‖alg.x (n + 1) - T (alg.x n)‖ + ‖T (alg.x n) - alg.x n‖ := by
            apply norm_add_le
      _ ≤ M1 + ‖T (alg.x n) - alg.x n‖ := by
            gcongr; exact hM1 n
      _ = M1 + ‖(T (alg.x n) - y) + (y - alg.x n)‖ := by
            abel_nf
      _ ≤ M1 + (‖T (alg.x n) - y‖ + ‖y - alg.x n‖) := by
            apply add_le_add_left; apply norm_add_le
      _ ≤ M1 + (M2 + M3) := by
            gcongr
            · exact hM2 n
            · rw [norm_sub_rev]; exact hM3 n
      _ ≤ μ := by
            simp [μ]
            rw [← add_assoc]
            have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _
            linarith
  -- 证明 ‖u - T x_n‖ ≤ μ
  · intro n
    calc
      ‖alg.u - T (alg.x n)‖
          = ‖(alg.u - y) + (y - T (alg.x n))‖ := by
            abel_nf
      _ ≤ ‖alg.u - y‖ + ‖y - T (alg.x n)‖ := by
            apply norm_add_le
      _ ≤ ‖alg.u - y‖ + M2 := by
            gcongr; rw [norm_sub_rev]; exact hM2 n
      _ ≤ μ := by
            simp [μ]
            have hM1_nonneg : 0 ≤ M1 := by
              have := hM1 0; exact le_trans (norm_nonneg _) this
            have hM3_nonneg : 0 ≤ M3 := by
              have := hM3 0; exact le_trans (norm_nonneg _) this
            linarith


-- ‖x(n+2)-x(n+1)‖≤μ* Σ|λ(n+1)-λn| +(1-λ(n+1))*∏‖x(n+1)-x(n)‖
lemma halpern_telescoping_bound
  {x : ℕ → H} {α : ℕ → ℝ} {μ : ℝ}
  (hμ_nonneg : 0 ≤ μ)
  (hα_range : ∀ n, α n ∈ Set.Ioo 0 1)
  (h_norm_diff_ineq :
    ∀ n, ‖x (n + 2) - x (n + 1)‖
      ≤ μ * |α (n + 1) - α n|
        + (1 - α (n + 1)) * ‖x (n + 1) - x n‖)
  : ∀ n m, m ≤ n →
      ‖x (n + 2) - x (n + 1)‖
        ≤ μ * (∑ k ∈ Finset.Icc m n, |α (k + 1) - α k|)
          + ‖x (m + 1) - x m‖
              * (∏ k ∈ Finset.Icc m n, (1 - α (k + 1))) :=
  by
    intro n m hmn
    obtain ⟨k, rfl⟩ := exists_add_of_le hmn
    -- Induction on the length k of the segment [m, m+k].
    induction k with
    | zero =>
      -- Base case: n = m
      -- The RHS sums/products over Icc m m are singletons; simplify with the one–step inequality.
      simp
      have := h_norm_diff_ineq m
      linarith
    | succ k ih =>
      -- Step: extend from [m, m+k] to [m, m+k+1]
      calc
        ‖x (m + (k + 1) + 2) - x (m + (k + 1) + 1)‖
            ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))|
              + (1 - α (m + (k + 1) + 1))
                  * ‖x (m + (k + 1) + 1) - x (m + (k + 1))‖ := by
                    exact h_norm_diff_ineq (m + (k + 1))
        _ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))|
              + (1 - α (m + (k + 1) + 1)) *
                (μ * (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|) +
                  ‖x (m + 1) - x m‖ *
                    (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1)))) := by
                    gcongr
                    · have := hα_range (m + (k + 1) + 1)
                      simp [Set.mem_Ioo] at this
                      linarith
                    · have h_le : m ≤ m + k := by linarith
                      exact ih h_le
        _ = μ * |α (m + (k + 1) + 1) - α (m + (k + 1))|
              + (1 - α (m + (k + 1) + 1)) * μ *
                (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|)
              + (1 - α (m + (k + 1) + 1)) * ‖x (m + 1) - x m‖ *
                (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1))) := by
                  ring
        _ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))|
              + μ * (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|)
              + (1 - α (m + (k + 1) + 1)) * ‖x (m + 1) - x m‖ *
                (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1))) := by
                  have h1_minus_α_pos : 0 < 1 - α (m + (k + 1) + 1) := by
                    have := hα_range (m + (k + 1) + 1)
                    simp [Set.mem_Ioo] at this
                    linarith
                  gcongr
                  · apply Finset.sum_nonneg
                    intro l _
                    exact abs_nonneg _
                  · nth_rewrite 2[← one_mul μ]
                    apply mul_le_mul_of_nonneg_right
                    · simp
                      have := hα_range (m + (k + 1) + 1)
                      simp [Set.mem_Ioo] at this
                      linarith
                    · exact hμ_nonneg
        _ = μ * (∑ l ∈ Finset.Icc m (m + (k + 1)), |α (l + 1) - α l|)
              + ‖x (m + 1) - x m‖
                * (∏ l ∈ Finset.Icc m (m + (k + 1)), (1 - α (l + 1))) := by
                  rw [← add_assoc, ← Nat.succ_eq_add_one (m+k),
                      Finset.sum_Icc_succ_top, Finset.prod_Icc_succ_top,
                      Nat.succ_eq_add_one]
                  · ring_nf
                  · linarith
                  · linarith

-- x(n+2)-x(n+1)=λ(n+1)-λn)•(u-T xn)+(1-λ(n+1))•(T x(n+1)-T xn)
lemma halpern_diff_formula
  {T : H → H}
  (alg : Halpern T)
  : ∀ n,
    alg.x (n + 2) - alg.x (n + 1) =
    (alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n)) +
    (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n)) := by
  intro n
  rw [alg.update, alg.update]
  calc
    alg.α (n + 1) • alg.u
    + (1 - alg.α (n + 1)) • T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n))
    - (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n))
    = (alg.α (n + 1) • alg.u - alg.α n • alg.u)
      + ((1 - alg.α (n + 1)) • T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n))
        - (1 - alg.α n) • T (alg.x n)) := by abel
    _ = (alg.α (n + 1) - alg.α n) • alg.u
      + ((1 - alg.α (n + 1)) • T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n))
        - (1 - alg.α n) • T (alg.x n)) := by
          rw [sub_smul]
          simp
          rw [sub_smul]
    _ = (alg.α (n + 1) - alg.α n) • alg.u
      - (alg.α (n + 1) - alg.α n) • T (alg.x n)
      + (1 - alg.α (n + 1)) • (T (alg.α n • alg.u +
        (1 - alg.α n) • T (alg.x n)) - T (alg.x n)) := by
          simp [sub_smul, add_sub, add_comm, smul_sub]
          abel_nf
    _ = (alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n))
      + (1 - alg.α (n + 1)) • (T (alg.α n • alg.u +
        (1 - alg.α n) • T (alg.x n)) - T (alg.x n)) := by
          rw [smul_sub]
          simp
          rw [smul_sub]

-- ‖x(n+2)-x(n+1)‖≤μ*|λ(n+1)-λn|+(1-λ(n+1))‖x(n+1)-x(n)‖
lemma halpern_norm_diff_ineq
  {T : H → H}
  (alg : Halpern T)
  {D : Set H}
  (hT_nonexp : NonexpansiveOn T D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_diff_formula : ∀ n,
    alg.x (n + 2) - alg.x (n + 1) =
    (alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n)) +
    (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n)))
  (μ : ℝ)
  (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  : ∀ n,
      ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
      μ * |alg.α (n + 1) - alg.α n| +
      (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
  intro n
  rw [h_diff_formula n]
  calc
    ‖(alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n))
      + (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n))‖
      ≤ ‖(alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n))‖
        + ‖(1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n))‖ := by
          apply norm_add_le
    _ = |alg.α (n + 1) - alg.α n| * ‖alg.u - T (alg.x n)‖
        + |1 - alg.α (n + 1)| * ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by
          rw [norm_smul, norm_smul]
          norm_cast
    _ = |alg.α (n + 1) - alg.α n| * ‖alg.u - T (alg.x n)‖
        + (1 - alg.α (n + 1)) * ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by
          have h1_minus_α_pos : 0 < 1 - alg.α (n + 1) := by
            have := h_α_range (n + 1)
            simp [Set.mem_Ioo] at this
            linarith
          rw [abs_of_pos h1_minus_α_pos]
    _ ≤ |alg.α (n + 1) - alg.α n| * μ
        + (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
          gcongr
          · exact hμ_Tx_bound n
          · have h_range := h_α_range (n + 1)
            simp [Set.mem_Ioo] at h_range
            linarith
          have hT_nonexp' := hT_nonexp (halg_x_in_D (n + 1)) (halg_x_in_D n)
          rw [edist_dist, edist_dist] at hT_nonexp'
          rw [dist_eq_norm, dist_eq_norm] at hT_nonexp'
          have h_nonneg : 0 ≤ ‖alg.x (n + 1) - alg.x n‖ := norm_nonneg _
          simp at hT_nonexp'
          apply (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp
          simp
          exact hT_nonexp'
    _ = μ * |alg.α (n + 1) - alg.α n| +
        (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
          rw [mul_comm]

-- ‖x(n+2)-x(n+1)‖≤μ* Σ|λ(n+1)-λn| +μ *∏‖x(n+1)-x(n)‖
lemma halpern_telescoping_ineq
  {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (μ : ℝ)
  (hμ_pos : μ > 0)
  (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n,
    ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
    μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  : ∀ n m, m ≤ n →
      ‖alg.x (n+2) - alg.x (n+1)‖ ≤
        μ * (∑ k ∈ Finset.Icc m n, |alg.α (k+1) - alg.α k|)
          + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))) := by
    intro n m hmn
    have hμ_nonneg : 0 ≤ μ := le_of_lt hμ_pos
    calc
      ‖alg.x (n+2) - alg.x (n+1)‖
          ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k+1) - alg.α k|)
            + ‖alg.x (m+1) - alg.x m‖ *
              (∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))) := by
            apply halpern_telescoping_bound hμ_nonneg h_α_range h_norm_diff_ineq
            exact hmn
      _ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k+1) - alg.α k|)
          + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))) := by
          have hμ_x_diff_bound := hμ_x_bound m
          have h_norm_diff_nonneg : 0 ≤ ‖alg.x (m + 1) - alg.x m‖ := norm_nonneg _
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_right
          · exact hμ_x_diff_bound
          · apply Finset.prod_nonneg
            intro k hk
            have h_range := h_α_range (k + 1)
            simp [Set.mem_Ioo] at h_range
            linarith

-- lim ‖x(n+2)-x(n+1)‖≤μ* Σ|λ(n+1)-λn| +μ *∏‖x(n+1)-x(n)‖
lemma halpern_telescoping_limit
  {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (μ : ℝ)
  (hμ_pos : μ > 0)
  (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n,
    ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
    μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  : ∀ᶠ n in atTop, ∀ᶠ m in atTop, m ≤ n →
      ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
        μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) +
        μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
  have hμ_nonneg : 0 ≤ μ := le_of_lt hμ_pos
  have h_telescoping := halpern_telescoping_ineq
    alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq
  apply eventually_atTop.2
  use 0
  intro n hn
  apply eventually_atTop.2
  use 0
  intro m hm
  intro hmn
  calc
    ‖alg.x (n + 2) - alg.x (n + 1)‖
        ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) +
          ‖alg.x (m + 1) - alg.x m‖ *
            (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
            exact halpern_telescoping_bound hμ_nonneg h_α_range h_norm_diff_ineq n m hmn
    _ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) +
          μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
          have hμ_x_diff_bound := hμ_x_bound m
          have h_norm_diff_nonneg : 0 ≤ ‖alg.x (m + 1) - alg.x m‖ := norm_nonneg _
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_right
          · exact hμ_x_diff_bound
          · apply Finset.prod_nonneg
            intro k hk
            have h_range := h_α_range (k + 1)
            simp [Set.mem_Ioo] at h_range
            linarith

-- ∑k∈ Finset.Icc m n, fk +∑'k,f(k+n+1)=∑'k,f(k+m)
lemma sum_icc_add_tsum_eq_tsum_add
  {f : ℕ → ℝ}
  (hf : Summable f)
  (m n : ℕ)
  (hmn : m ≤ n) :
  ∑ k ∈ Finset.Icc m n, f k + ∑' k, f (k + n + 1) = ∑' k, f (k + m) := by
  -- 首先，分解 ∑' k, f (k + m) 为三部分
  have h_decomp : ∑' k, f (k + m) =
      ∑ k ∈ Finset.Icc m n, f k + ∑' k, f (k + n + 1) := by
    have h_split : ∑' k : ℕ, f (k + m) =
        ∑ k ∈ Finset.range (n - m + 1), f (k + m) + ∑' k : ℕ, f (k + n + 1) := by
      have hf_shift : Summable (fun k => f (k + m)) := by
        apply hf.comp_injective
        intro a b hab
        linarith
      rw [← Summable.sum_add_tsum_nat_add]
      · congr
        ext k
        ring_nf
        congr 1
        rw [Nat.Simproc.add_eq_add_le (1 + k + (n - m)) (1 + k) hmn]
      · assumption
    have h_finset_eq : ∑ k ∈ Finset.range (n - m + 1), f (k + m) =
        ∑ k ∈ Finset.Icc m n, f k := by
      trans ∑ i ∈ Finset.Icc m n, f i
      · -- 转换求和指标：k ∈ range(n-m+1) ↔ k+m ∈ Icc m n
        rw [Finset.sum_bij (fun k _ => k + m)]
        · intro k hk
          simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
          omega
        · intro k₁ k₂ _ _ heq
          omega
        · intro k hk
          use k - m
          simp
          constructor
          · simp at hk
            omega
          · simp at hk
            omega
        · intro i hi
          rfl
      simp
    rw [h_split, h_finset_eq]
  rw [h_decomp]

-- lim_m n → ∞, μ * ∑ k∈Finset.Icc m n,|λ(k+1)-λk| =0
lemma halpern_sum_tail_tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  (μ : ℝ)
  (hμ_pos : μ > 0)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop,
      m ≤ n → μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) < ε := by
  intros ε ε_pos
  let f := fun n => |alg.α (n + 1) - alg.α n|
  have hf : Summable f := h_α_diff_finite
  have h_sum_tail : Tendsto (fun m => ∑' k : ℕ, f (k + m)) atTop (𝓝 0) := by
    exact tendsto_sum_nat_add f
  have h_eventually_tail : ∀ᶠ m in atTop, ∑' k : ℕ, f (k + m) < ε / μ := by
    apply (tendsto_order.1 h_sum_tail).2 (ε / μ) (by positivity)
  have : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * ∑ k ∈ Finset.Icc m n, f k < ε := by
    filter_upwards [h_eventually_tail] with m hm
    apply eventually_atTop.2
    use m
    intro n hmn hmn'
    have h_le : ∑ k ∈ Finset.Icc m n, f k ≤ ∑' k : ℕ, f (k + m) := by
      calc
        ∑ k ∈ Finset.Icc m n, f k
            ≤ ∑ k ∈ Finset.Icc m n, f k + ∑' (k : ℕ), f (k + n + 1) := by
              simp
              simp [f]
              apply tsum_nonneg
              intro k
              exact abs_nonneg _
          _ = ∑' (k : ℕ), f (k + m) := by
              exact sum_icc_add_tsum_eq_tsum_add h_α_diff_finite m n hmn
    -- 应用到目标
    calc
      μ * ∑ k ∈ Finset.Icc m n, f k
          ≤ μ * ∑' k : ℕ, f (k + m) := by apply mul_le_mul_of_nonneg_left h_le (le_of_lt hμ_pos)
        _ < μ * (ε / μ) := mul_lt_mul_of_pos_left hm hμ_pos
        _ = ε := by field_simp [ne_of_gt hμ_pos]
  exact this

-- lim_n → ∞, μ * ∏ k∈Finset.Icc m n,(1-λ(k+1))=0
lemma halpern_prod_tail_tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  (μ : ℝ)
  (hμ_pos : μ > 0)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  : ∀ ε > 0, ∀ m : ℕ, ∀ᶠ n in atTop, m ≤ n →
      μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
  intros ε hε m

  -- 第一步：建立函数相等性
  have h_reindex : (fun n ↦ ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)))
      = (fun n ↦ ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k)) := by
    ext n
    by_cases hn : n ≥ m
    · -- 当 n ≥ m 时
      let g := fun k => k + 1
      let s := Finset.Icc m n
      let f := fun k => 1 - alg.α k
      have hf : Set.InjOn g ↑s := by
        intros x hx y hy hxy
        exact Nat.succ_inj.mp hxy
      rw [← Finset.prod_image (s := s) (f := f) (g := g) hf]
      congr
      ext k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨x, hx, rfl⟩
        constructor
        · simp [g, s] at *
          rcases hx with ⟨hxm, hxn⟩
          linarith
        · simp [g, s] at *
          rcases hx with ⟨hxm, hxn⟩
          linarith
      · intro hk
        use k - 1
        constructor
        · rcases hk with ⟨hk1, hk2⟩
          simp [s, g] at *
          constructor
          · exact Nat.le_sub_one_of_lt hk1
          · linarith
        rcases hk with ⟨hk1, hk2⟩
        simp [s, g] at *
        refine Nat.sub_add_cancel ?_
        have : 1 ≤ k := by
          calc 1 ≤ m + 1 := by linarith
          _ ≤ k := hk1
        linarith
    · -- 当 n < m 时，两边都是 1
      have h_empty1 : Finset.Icc m n = ∅ := by
        ext x
        simp [Finset.mem_Icc]
        simp at *
        intro hx
        linarith
      have h_empty2 : Finset.Icc (m + 1) (n + 1) = ∅ := by
        ext x
        simp [Finset.mem_Icc]
        simp at *
        intro hx
        linarith
      rw [h_empty1, Finset.prod_empty]
      rw [h_empty2, Finset.prod_empty]

  -- 第二步：证明乘积趋于零
  have h_prod_tendsto : Tendsto (fun n => ∏ k ∈ Finset.Icc
    (m + 1) (n + 1), (1 - alg.α k)) atTop (𝓝 0) := by
    let f : ℕ → ℝ := fun n => ∏ k ∈ Finset.Icc (m + 1) n, (1 - alg.α k)
    have h_f_tendsto : Tendsto f atTop (𝓝 0) :=
      infinite_prod_zero alg h_α_range h_α_sum_inf (m + 1)
    apply h_f_tendsto.comp
    exact tendsto_add_atTop_nat 1

  -- 第三步：提取 ε-δ 条件
  have h_eventually : ∀ᶠ n in atTop, ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k) < ε / μ := by
    rw [Metric.tendsto_atTop] at h_prod_tendsto
    obtain ⟨N, hN⟩ := h_prod_tendsto (ε / μ) (by positivity)
    rw [eventually_atTop]
    use N
    intro n hn
    have := hN n hn
    rw [Real.dist_eq] at this
    simp at this
    exact lt_of_abs_lt this

  -- 第四步：将条件转化为目标形式
  rw [eventually_atTop]
  obtain ⟨N, hN⟩ := (eventually_atTop).mp h_eventually
  use max m N
  intro n hn hmn
  have hn_N : n ≥ N := le_of_max_le_right hn
  calc
    μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))
        = μ * ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k) := by
          congr 1
          exact congrFun h_reindex n
      _ < μ * (ε / μ) := mul_lt_mul_of_pos_left (hN n hn_N) hμ_pos
      _ = ε := by field_simp [ne_of_gt hμ_pos]

-- 从范数收敛到向量收敛
lemma norm_diff_tendsto_zero_iff_diff_tendsto_zero
  {f : ℕ → H} :
  Tendsto (fun n => ‖f (n + 2) - f (n + 1)‖) atTop (𝓝 0) ↔
  Tendsto (fun n => (f (n + 2) - f (n + 1))) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop] at h ⊢
    intros ε ε_pos
    obtain ⟨N, hN⟩ := h ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq] at hN
    simp at hN
    rw [dist_eq_norm]
    simp
    exact hN
  · intro h
    rw [Metric.tendsto_atTop] at h ⊢
    intros ε ε_pos
    obtain ⟨N, hN⟩ := h ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN
    simp at hN
    rw [Real.dist_eq]
    simp
    exact hN

-- 相邻差序列收敛到零
lemma adjacent_diff_from_shifted
  {f : ℕ → H} :
  Tendsto (fun n => (f (n + 2) - f (n + 1))) atTop (𝓝 0) →
  Tendsto (fun n => (f (n + 1) - f n)) atTop (𝓝 0) := by
  intro h
  have : (fun n ↦ f (n + 1) - f n) ∘ (fun n ↦ n + 1) =
    (fun n ↦ f (n + 2) - f (n + 1)) := by
    funext n
    simp only [Function.comp_apply]
  rw [← this] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

-- 让 n 和 m 趋于 +∞，得到 lim xn+1−xn → 0
lemma halpern_diff_limit
  {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (μ : ℝ)
  (hμ_pos : μ > 0)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n,
    ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
    μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  (h_telescoping : ∀ n m, m ≤ n →
    ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
      μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) +
      μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)))) :
  Tendsto (fun n => (alg.x (n + 1) - alg.x n)) atTop (𝓝 0) := by
  have hμ_nonneg : 0 ≤ μ := le_of_lt hμ_pos
  have sq_lim_le := halpern_telescoping_limit alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq
  -- 让 n 和 m 趋于 +∞，得到 lim μ ∏ (1 - λₖ₊₁) = 0
  have sq_lim2 := halpern_prod_tail_tendsto_zero alg μ hμ_pos h_α_range h_α_sum_inf
  have sq_lim3: ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n →
    μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
    intro ε ε_pos
    exact Eventually.mono sq_lim_le fun x a ↦ sq_lim2 ε ε_pos x
  have sq_lim1 := halpern_sum_tail_tendsto_zero alg μ hμ_pos h_α_diff_finite
  have sq_lim4 : ∀ ε > 0, ∀ᶠ (m : ℕ) (n : ℕ) in atTop, m ≤ n →
    μ * ∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k| +
    μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
    intros ε ε_pos
    have h1 := sq_lim1 (ε/2) (by linarith)
    have h2 := sq_lim3 (ε/2) (by linarith)
    filter_upwards [h1, h2] with N1 h11 h22
    filter_upwards [h11, h22] with N2 h111 h222
    intro hN1N2
    calc
        _ < ε/2 + ε/2 := by
          apply add_lt_add
          · exact h111 hN1N2
          · exact h222 hN1N2
        _ = ε := by ring
  have sq_lim5 : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n →
    ‖alg.x (n + 2) - alg.x (n + 1)‖ < ε := by
    intro ε ε_pos
    filter_upwards [sq_lim4 ε ε_pos] with N1 h1
    filter_upwards [h1] with N2 h2
    intro hN1N2
    calc
      ‖alg.x (N2 + 2) - alg.x (N2 + 1)‖
          ≤ μ * ∑ k ∈ Finset.Icc N1 N2, |alg.α (k + 1) - alg.α k| +
            μ * ∏ k ∈ Finset.Icc N1 N2, (1 - alg.α (k + 1)) := by
            apply h_telescoping N2 N1 hN1N2
        _ < ε := h2 hN1N2
  have sq_lim5' : ∀ ε > 0, ∀ᶠ n in atTop, ‖alg.x (n + 2) - alg.x (n + 1)‖ < ε := by
    intro ε ε_pos
    have h_eventually := sq_lim5 ε ε_pos
    rw [eventually_atTop] at h_eventually
    obtain ⟨N, hN⟩ := h_eventually
    specialize hN N (le_refl N)
    rw [eventually_atTop] at hN
    rw [eventually_atTop]
    rcases hN with ⟨a, ha⟩
    use max N a
    intro n hn
    apply ha
    · exact le_of_max_le_right hn
    · exact le_of_max_le_left hn
  have sq_lim6 : Tendsto (fun n => ‖alg.x (n + 2) - alg.x (n + 1)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intros ε ε_pos
    obtain ⟨N, hN⟩ := (eventually_atTop).mp (sq_lim5' ε ε_pos)
    use N
    intro n hn
    rw [Real.dist_eq]
    simp
    exact hN n hn
  have sq_lim7 : Tendsto (fun n => (alg.x (n + 2) - alg.x (n + 1))) atTop (𝓝 0) :=
    (norm_diff_tendsto_zero_iff_diff_tendsto_zero.1 sq_lim6)
  exact adjacent_diff_from_shifted sq_lim7

-- 由Nonexpansive 得到 lim T(xn+1)−T(xn) → 0
lemma T_preserves_diff_tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  {D : Set H}
  (hT_nonexp : NonexpansiveOn T D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_diff_limit : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (𝓝 0))
  : Tendsto (fun n ↦ T (alg.x (n + 1)) - T (alg.x n)) atTop (𝓝 0) := by
  -- 利用非扩张映射的性质：dist(Tx, Ty) ≤ dist(x, y)
  have hT_lip : ∀ n, ‖T (alg.x (n + 1)) - T (alg.x n)‖ ≤ ‖alg.x (n + 1) - alg.x n‖ := by
    intro n
    rw [← dist_eq_norm, ← dist_eq_norm]
    specialize hT_nonexp (halg_x_in_D (n + 1)) (halg_x_in_D n)
    simp at hT_nonexp
    rw [edist_dist, edist_dist] at hT_nonexp
    have h_nonneg : 0 ≤ dist (alg.x (n + 1)) (alg.x n) := dist_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp hT_nonexp
  -- 由于 ‖alg.x (n + 1) - alg.x n‖ → 0，而 T 是非扩张的
  -- 所以 ‖T (alg.x (n + 1)) - T (alg.x n)‖ → 0
  rw [Metric.tendsto_atTop]
  intro ε ε_pos
  rw [Metric.tendsto_atTop] at h_diff_limit
  obtain ⟨N, hN⟩ := h_diff_limit ε ε_pos
  use N
  intro n hn
  specialize hN n hn
  rw [dist_eq_norm] at hN ⊢
  simp at hN ⊢
  calc
    ‖T (alg.x (n + 1)) - T (alg.x n)‖
        ≤ ‖alg.x (n + 1) - alg.x n‖ := by apply hT_lip n
      _ < ε := hN

-- lim ‖(xn+1-Txn+1)-(xn-Txn)‖ = 0
lemma x_sub_Tx_diff_Tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  (h_diff_limit : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (𝓝 0))
  (h_T_diff_limit : Tendsto (fun n ↦ T (alg.x (n + 1)) - T (alg.x n)) atTop (𝓝 0))
  : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ‖(alg.x (n + 1) - T (alg.x (n + 1))) -
        (alg.x n - T (alg.x n))‖ < ε := by
  intro ε ε_pos
  rw [Metric.tendsto_atTop] at h_diff_limit h_T_diff_limit
  obtain ⟨N1, hN1⟩ := h_diff_limit (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := h_T_diff_limit (ε / 2) (by linarith)
  use max N1 N2
  intro n hn
  have hn_N1 : n ≥ max N1 N2 := hn
  have hn_N1' : n ≥ N1 := le_of_max_le_left hn_N1
  have hn_N2' : n ≥ N2 := le_of_max_le_right hn_N1
  have step1 : ‖alg.x (n + 1) - alg.x n‖ < ε / 2 := by
    have h := hN1 n (by omega)
    rw [dist_eq_norm] at h
    simp at h
    linarith
  have step2 : ‖T (alg.x (n + 1)) - T (alg.x n)‖ < ε / 2 := by
    have h := hN2 n (by omega)
    rw [dist_eq_norm] at h
    simp at h
    linarith
  calc
    ‖(alg.x (n + 1) - T (alg.x (n + 1))) - (alg.x n - T (alg.x n))‖
        = ‖(alg.x (n + 1) - alg.x n) - (T (alg.x (n + 1)) - T (alg.x n))‖ := by
          congr 1; abel
      _ ≤ ‖alg.x (n + 1) - alg.x n‖ + ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by
          apply norm_sub_le
      _ < ε / 2 + ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by
        gcongr
      _ < ε := by linarith

-- 从存在量化形式得到 Tendsto 形式
lemma tendsto_of_forall_eps_exists_N_le
  {f : ℕ → H}
  (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖f n‖ < ε) :
  Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε ε_pos
  obtain ⟨N, hN⟩ := h ε ε_pos
  use N
  intro n hn
  rw [dist_eq_norm]
  simp
  exact hN n hn

-- lim ‖(xn+k-Txn+k)-(xn-Txn)‖ = 0
lemma sum_x_sub_Tx_diff_Tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  (h_diff_limit : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (𝓝 0))
  (h_T_diff_limit : Tendsto (fun n ↦ T (alg.x (n + 1)) - T (alg.x n)) atTop (𝓝 0))
  : ∀ k : ℕ, Tendsto (fun n ↦ (alg.x (n + k) - T (alg.x (n + k))) -
    (alg.x n - T (alg.x n))) atTop (𝓝 0) := by
  intro k
  induction k with
  | zero =>
    -- 基础情况：k = 0
    simp only [add_zero, sub_self]
    exact tendsto_const_nhds
  | succ k ih =>
    -- 归纳步：从 k 推到 k+1
    -- 关键思想：(xₙ₊ₖ₊₁ - Txₙ₊ₖ₊₁) - (xₙ - Txₙ)
    --         = [(xₙ₊ₖ₊₁ - Txₙ₊ₖ₊₁) - (xₙ₊ₖ - Txₙ₊ₖ)] + [(xₙ₊ₖ - Txₙ₊ₖ) - (xₙ - Txₙ)]
    have h_decomp : ∀ n,
      (alg.x (n + (k + 1)) - T (alg.x (n + (k + 1)))) - (alg.x n - T (alg.x n)) =
      ((alg.x (n + (k + 1)) - T (alg.x (n + (k + 1)))) - (alg.x (n + k) - T (alg.x (n + k)))) +
      ((alg.x (n + k) - T (alg.x (n + k))) - (alg.x n - T (alg.x n))) := by
      intro n
      abel

    -- 第一部分：固定 m = n+k，让 n 趋于无穷
    have h_part1 : Tendsto (fun n ↦ (alg.x (n + (k + 1)) - T (alg.x (n + (k + 1)))) -
      (alg.x (n + k) - T (alg.x (n + k)))) atTop (𝓝 0) := by
      -- 从 x_sub_Tx_diff_Tendsto_zero 得到存在量化形式
      have h_base_eps_N : ∀ ε > 0, ∃ N, ∀ n ≥ N,
        ‖(alg.x (n + 1) - T (alg.x (n + 1))) - (alg.x n - T (alg.x n))‖ < ε :=by
        exact fun ε a ↦ x_sub_Tx_diff_Tendsto_zero alg h_diff_limit h_T_diff_limit ε a

      -- 转换为 Tendsto 形式
      have h_base : Tendsto (fun n ↦ (alg.x (n + 1) - T (alg.x (n + 1))) -
        (alg.x n - T (alg.x n))) atTop (𝓝 0) := by
        exact tendsto_of_forall_eps_exists_N_le h_base_eps_N

      -- 现在可以使用组合和移位
      have h_shift : (fun n ↦ (alg.x (n + (k + 1)) - T (alg.x (n + (k + 1)))) -
        (alg.x (n + k) - T (alg.x (n + k)))) =
          (fun m ↦ (alg.x (m + 1) - T (alg.x (m + 1))) -
            (alg.x m - T (alg.x m))) ∘ (· + k) := by
              funext n
              simp only [Function.comp_apply, add_assoc]
      rw [h_shift]
      exact h_base.comp (tendsto_add_atTop_nat k)

    -- 第二部分：由归纳假设
    have h_part2 := ih

    -- 合并两部分
    have h_combined : Tendsto (fun n ↦
      ((alg.x (n + (k + 1)) - T (alg.x (n + (k + 1)))) - (alg.x (n + k) - T (alg.x (n + k)))) +
        ((alg.x (n + k) - T (alg.x (n + k))) - (alg.x n - T (alg.x n)))) atTop (𝓝 (0 + 0)) := by
          apply Tendsto.add h_part1 h_part2
    convert h_combined using 1
    · funext n
      exact h_decomp n
    · simp

-- lim (xₙ - Txₙ) → 0
lemma halpern_x_sub_Tx_tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (μ : ℝ)
  (hμ_pos : μ > 0)
  (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  (h_diff_limit : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (𝓝 0))
  : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (𝓝 0) := by
  -- 步骤1：建立关键等式
  have eq1 : ∀ n, alg.x (n + 1) - alg.x n =
      alg.α n • (alg.u - T (alg.x n)) + (T (alg.x n) - alg.x n) := by
    intro n
    rw [alg.update]
    calc
      alg.α n • alg.u + (1 - alg.α n) • T (alg.x n) - alg.x n
          = alg.α n • alg.u + (1 - alg.α n) • T (alg.x n) -
            (alg.α n • alg.x n + (1 - alg.α n) • alg.x n) := by
            congr 1
            simp [sub_smul]
        _ = alg.α n • (alg.u - alg.x n) + (1 - alg.α n) • (T (alg.x n) - alg.x n) := by
            simp [smul_sub, sub_smul]
            abel
        _ = alg.α n • (alg.u - T (alg.x n)) + alg.α n • (T (alg.x n) - alg.x n) +
            (1 - alg.α n) • (T (alg.x n) - alg.x n) := by
            simp [smul_sub, sub_smul]
        _ = alg.α n • (alg.u - T (alg.x n)) +
            (alg.α n + (1 - alg.α n)) • (T (alg.x n) - alg.x n) := by
            simp [smul_sub, sub_smul]
            abel
        _ = alg.α n • (alg.u - T (alg.x n)) + (T (alg.x n) - alg.x n) := by
            simp [add_sub_cancel]

  -- 步骤2：证明 α_n * ‖u - T(x_n)‖ → 0
  have h1 : Tendsto (fun n ↦ alg.α n * ‖alg.u - T (alg.x n)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h_α_limit
    obtain ⟨N, hN⟩ := h_α_limit (ε / μ) (by positivity)
    use N
    intro n hn
    rw [Real.dist_eq]
    simp only [sub_zero]
    have h_α_small : |alg.α n| < ε / μ := by
      have := hN n hn
      rw [Real.dist_eq] at this
      simp at this
      exact this
    have h_α_nonneg : 0 ≤ alg.α n := by
      have := h_α_range n
      simp [Set.mem_Ioo] at this
      rcases this with ⟨h1, h2⟩
      linarith
    rw [abs_of_nonneg h_α_nonneg] at h_α_small
    calc
      |alg.α n * ‖alg.u - T (alg.x n)‖|
          = alg.α n * ‖alg.u - T (alg.x n)‖ := by
            simp [abs_mul, abs_of_nonneg h_α_nonneg]
        _ ≤ alg.α n * μ := by
            gcongr
            exact hμ_Tx_bound n
        _ < (ε / μ) * μ := by
            apply mul_lt_mul_of_pos_right h_α_small
            exact hμ_pos
        _ = ε := by field_simp [ne_of_gt hμ_pos]

  -- 步骤3：证明 α_n • (u - T(x_n)) → 0
  have h2 : Tendsto (fun n ↦ alg.α n • (alg.u - T (alg.x n))) atTop (𝓝 0) := by
    -- 我们需要证明 ‖alg.α n • (alg.u - T (alg.x n))‖ → 0
    have h_norm_bound : Tendsto (fun n ↦ ‖alg.α n • (alg.u - T (alg.x n))‖) atTop (𝓝 0) := by
      have : Tendsto (fun n ↦ |alg.α n| * ‖alg.u - T (alg.x n)‖) atTop (𝓝 0) := by
        convert h1 using 1
        ext n; congr; simp
        have := h_α_range n
        simp [Set.mem_Ioo] at this
        rcases this with ⟨h1, h2⟩
        exact le_of_lt h1
      apply Metric.tendsto_atTop.mpr
      apply Metric.tendsto_atTop.mp
      convert this using 1
      funext n
      rw [norm_smul]
      simp

    -- 从范数的收敛性推出向量的收敛性
    rw [Metric.tendsto_atTop] at h_norm_bound
    rw [Metric.tendsto_atTop]
    intros ε ε_pos
    obtain ⟨N, hN⟩ := h_norm_bound ε ε_pos
    use N
    intros n hn
    specialize hN n hn
    rw [dist_eq_norm]
    simp at hN
    simp
    exact hN

  -- 步骤4：合并结果
  have h3 : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (𝓝 0) := h_diff_limit

  have h_key : ∀ n, alg.x n - T (alg.x n) =
      alg.α n • (alg.u - T (alg.x n)) - (alg.x (n + 1) - alg.x n) := by
    intro n
    have := eq1 n
    rw [this]
    simp
  convert Tendsto.sub h2 h3 using 1
  · funext n
    exact h_key n
  simp

#check norm_eq_iInf_iff_real_inner_le_zero
#check exists_norm_eq_iInf_of_complete_convex

-- Lemma 2.45: 有界序列存在弱收敛子序列
lemma bounded_seq_weakly_convergent_subsequence
  (x : ℕ → H)
  (h_bounded : ∃ M, ∀ n, ‖x n‖ ≤ M) :
  ∃ (φ : ℕ → ℕ) (p : H),
    (∀ m n, m < n → φ m < φ n) ∧  -- φ 是严格递增的
    WeakConverge (x ∘ φ) p := by
  -- 从 ∃ M, ∀ n, ‖x n‖ ≤ M 构造 BddAbove
  obtain ⟨M, hM⟩ := h_bounded
  have h_bdd_above : BddAbove (Set.range (fun n => ‖x n‖)) := by
    use M
    intro y hy
    simp [Set.range] at hy
    obtain ⟨n, rfl⟩ := hy
    exact hM n
  -- 应用已证明的定理
  obtain ⟨a, φ, h_strict_mono, h_weak_conv⟩ :=
    bounded_seq_has_weakly_converge_subseq x h_bdd_above
  -- 展开 StrictMono φ 为显式形式
  have h_phi_explicit : ∀ m n, m < n → φ m < φ n := by
    exact fun m n a ↦ h_strict_mono a
  exact ⟨φ, a, h_phi_explicit, h_weak_conv⟩



theorem existence_of_projection_point (C : Set H) (hC1 : C.Nonempty) (hC2 : Convex ℝ C)
  (hC3 : IsClosed C) (x : H) : ∃ u ∈ C, ‖x - u‖ = ⨅ w : C, ‖x - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hC1 (IsClosed.isComplete hC3) hC2 x

theorem proj_pt_inner_le_zero (x PxC : H) (C : Set H) (hC2 : Convex ℝ C)
  (hPxC : PxC ∈ C) (hP : ‖x - PxC‖ = ⨅ w : C, ‖x - w‖) :
  ∀ w ∈ C, inner ℝ (x - PxC) (w - PxC) ≤ 0 := (norm_eq_iInf_iff_real_inner_le_zero hC2 hPxC).1 hP


lemma StrictMono.nat_id_le {φ : ℕ → ℕ} (h_strict : ∀ i j, i < j → φ i < φ j) :
  ∀ k, φ k ≥ k := by
  intro k
  induction k with
  | zero =>
    -- φ 0 ≥ 0 显然成立
    exact Nat.zero_le (φ 0)
  | succ k' ih =>
    -- 假设 φ k' ≥ k'
    -- 由于 φ (k' + 1) > φ k'，所以 φ (k' + 1) ≥ φ k' + 1 ≥ k' + 1
    have h_strict_at_succ : φ (k' + 1) > φ k' := h_strict k' (k' + 1) (by omega)
    omega



-- 下确界的特征性质
#check csInf_le  -- 下确界是下界
#check csInf_lt_iff  -- L < a ↔ ∃ b ∈ S, b < a (当S非空有下界)



theorem lim_subsequence_eq_limsup
  (x : ℕ → ℝ)
  (hx_bdd : ∃ M : ℝ ,∀ k : ℕ, |x k| ≤ M) :
  ∃ (φ : ℕ → ℕ) (L : ℝ),
    (∀ m n, m < n → φ m < φ n) ∧
    (L = limsup x atTop) ∧
    (Tendsto (x ∘ φ) atTop (𝓝 L)) := by
  classical
  -- 步骤1：定义 L := limsup x atTop
  set L := limsup x atTop with hL_def

  -- 步骤2：从 limsup 的定义提取逼近性质
  have h_limsup_spec : ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, x n ≥ L - ε := by
    intro ε hε N
    by_contra! h_contra
    have h_le: ∀ n ≥ N, x n ≤ L - ε := by
      intro n hn
      specialize h_contra n hn
      linarith

    have h_eventually : ∀ᶠ n in atTop, x n ≤ L - ε := by
      rw [eventually_atTop]
      exact ⟨N, h_le⟩

    -- limsup 不能小于所有足够大项的上界
    have h_limsup_le : limsup x atTop ≤ L - ε := by
      rw [Filter.limsup_le_iff ?_ ?_]
      · intro y hy
        filter_upwards [h_eventually] with n hn
        linarith
      · rcases hx_bdd with ⟨M, hM⟩
        apply Filter.IsCoboundedUnder.of_frequently_ge ?_
        · exact -M
        · rw [@frequently_atTop]
          intro a
          use a + 1
          simp
          specialize hM (a + 1)
          apply abs_le.1 at hM
          rcases hM with ⟨hM1, hM2⟩
          assumption
      · simp [IsBoundedUnder, IsBounded]
        use (L - ε)
        use N
    linarith

  have h_limsup_spec' : ∀ ε > 0, ∀ᶠ n in atTop, x n ≤ L + ε := by
    intro ε hε
    rw [Filter.eventually_atTop]
    simp [limsup, limsSup] at hL_def
    -- 首先需要证明集合非空和有下界
    rcases hx_bdd with ⟨M, hM⟩
    have h_set_nonempty : {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → x b ≤ a}.Nonempty := by
      -- limsup 本身就是这个集合中的元素
      use M
      simp
      use 0
      simp
      intro n
      have := hM n
      apply abs_le.1 at this
      exact this.2
    have h_set_bdd_below : BddBelow {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → x b ≤ a} := by
      -- 集合中所有元素都是上界，所以存在下界（比如 -∞ 或某个具体数）
      use -M - 1
      intro y hy
      -- 任何是上界的元素都 ≥ -M - 1
      simp at hy
      by_contra! h_contra
      rcases hy with ⟨a, ha⟩
      specialize ha (a + 1)
      simp at ha
      have contra: x (a + 1) < -M - 1 := by linarith
      specialize hM (a + 1)
      apply abs_le.1 at hM
      rcases hM with ⟨hM1, hM2⟩
      linarith
    -- 现在可以使用 csInf_lt_iff
    have h2 : L < L + ε := by linarith
    nth_rewrite 1 [hL_def] at h2
    have h3 : ∃ b ∈ {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → x b ≤ a}, b < L + ε := by
      apply (csInf_lt_iff h_set_bdd_below h_set_nonempty).mp h2

    -- 从存在量化得到 eventually
    obtain ⟨b, ⟨N, hN_bound⟩, hb_lt⟩ := h3
    use N
    intro n hn
    specialize hN_bound n hn
    have h_bound : x n ≤ b := by
      simp at hN_bound
      exact hN_bound
    linarith

  -- 步骤3：递归构造严格递增子序列 φ
  have h_exists_subseq : ∃ φ : ℕ → ℕ,
      (∀ m n, m < n → φ m < φ n) ∧
      (∀ k, x (φ k) ≥ L - 1 / (k + 1)) := by
    let find_next (N : ℕ) (ε : ℝ) (hε_pos : 0 < ε) : ℕ :=
      (h_limsup_spec ε hε_pos N).choose

    -- 验证 find_next 的性质
    have h_find_next_ge : ∀ N ε (hε : 0 < ε),
      find_next N ε hε ≥ N := fun N ε _ =>
      (h_limsup_spec ε (by positivity) N).choose_spec.1

    have h_find_next_value : ∀ N ε (hε : 0 < ε),
      x (find_next N ε hε) ≥ L - ε := fun N ε _ =>
      (h_limsup_spec ε (by positivity) N).choose_spec.2

    -- 递归构造序列 φ
    let φ : ℕ → ℕ := fun k =>
      Nat.recOn k
        (find_next 0 1 (by positivity))  -- φ(0)：从 N=0, ε=1 找起
        (fun k' φk' =>
          find_next (φk' + 1) (1 / (k' + 2)) (by positivity))
    use φ
    constructor
    · -- 证明 φ 严格递增
      intro m n hmn
      induction n with
      | zero => omega  -- m < 0 不可能
      | succ n' ih =>
        by_cases hm : m < n'
        · have h_ih := ih hm
          calc φ m < φ n' := h_ih
            _ < φ (n' + 1) := by
              unfold φ
              apply h_find_next_ge
              positivity
        · push_neg at hm
          have : m = n' := by omega
          rw [this]
          unfold φ
          have : find_next (φ n' + 1) (1 / (n' + 2)) (by positivity) ≥ φ n' + 1 := by
            apply h_find_next_ge
            positivity
          exact this
    · -- 证明 x (φ k) ≥ L - 1 / (k + 1)
      intro k
      induction k with
      | zero =>
        unfold φ
        have h1 : (0 : ℝ) < 1 := by norm_num
        simp
        exact
          (OrderedSub.tsub_le_iff_right L 1
                (x
                  (find_next 0 1
                    (Mathlib.Meta.Positivity.pos_of_isNat
                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                      (Eq.refl (Nat.ble 1 1)))))).mp
            (h_find_next_value 0 1 h1)
      | succ k' ih =>
        have hε_pos : (0 : ℝ) < 1 / (k' + 2) := by positivity
        have h_value := h_find_next_value
          (φ (Nat.recOn k' (find_next 0 1 (by norm_num : 0 < (1 : ℝ)))
            (fun k'' φk'' => find_next (φk'' + 1) (1 / (k'' + 2)) (by positivity))) + 1)
          (1 / (k' + 2)) hε_pos
        calc
          _ ≥ L - 1 / (k' + 2) := by
            exact
              h_find_next_value
                (Nat.rec
                    (find_next 0 1
                      (Mathlib.Meta.Positivity.pos_of_isNat
                        (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl (Nat.ble 1 1))))
                    (fun k' φk' ↦find_next (φk' + 1) (1 / (↑k' + 2))
                      (div_pos
                        (Mathlib.Meta.Positivity.pos_of_isNat
                          (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                          (Eq.refl (Nat.ble 1 1)))
                        (Right.add_pos_of_nonneg_of_pos (Nat.cast_nonneg' k')
                          (Mathlib.Meta.Positivity.pos_of_isNat
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))
                            (Eq.refl (Nat.ble 1 2))))))
                    k' +1) (1 / (↑k' + 2)) hε_pos
          _ = L - 1 / (↑(k' + 1) + 1) := by norm_num; ring
  obtain ⟨φ, ⟨hφ_mono, h_φ_lower⟩⟩ := h_exists_subseq
  -- 步骤4：证明子列收敛到 L：下界来自 h_φ_lower，上界来自 limsup ≤ L
  use φ, L, hφ_mono, rfl
  rw [Metric.tendsto_atTop]
  intro ε ε_pos
  obtain ⟨N_up, hN_up⟩ := (eventually_atTop).mp (h_limsup_spec' (ε / 2) (by linarith))

  have h_one_div : ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → 1 / (↑k + 1) < ε := by
    use Nat.ceil (1 / ε)
    intro k hk
    have hk' : (1 : ℝ) / ε ≤ k := by
      have h_ceil_nonneg : 0 ≤ Nat.ceil (1 / ε) := by simp
      calc
        1 / ε ≤ Nat.ceil (1 / ε) := by
          exact Nat.le_ceil (1 / ε)
        _ ≤ k := by
          norm_cast
    have : 1 / ε > 0 := by exact one_div_pos.mpr ε_pos
    have hk_plus_one : (1 : ℝ) / ε < k + 1 := by linarith
    have : (1 : ℝ) / (k + 1) < ε := by
      have h_pos_k : 0 < (k : ℝ) + 1 := by
        norm_cast
        omega
      exact (one_div_lt ε_pos h_pos_k).mp hk_plus_one
    assumption
  obtain ⟨k₀, hk₀⟩ := h_one_div

  have h_phi_ge : ∀ k, φ k ≥ k := StrictMono.nat_id_le hφ_mono

  use max N_up k₀
  intro k hk
  have hk_up : k ≥ N_up := le_of_max_le_left hk
  have hk_k₀ : k ≥ k₀ := le_of_max_le_right hk
  have h_upper : x (φ k) ≤ L + ε / 2 := by
    specialize hN_up (φ k) ?_
    · exact Nat.le_trans hk_up (h_phi_ge k)
    · exact hN_up

  have h_lower : x (φ k) ≥ L - 1 / (↑k + 1) := h_φ_lower k

  have h_one_div_small : 1 / (↑k + 1) < ε := hk₀ k hk_k₀
  rw [dist_eq_norm]
  simp only [Function.comp_apply]
  simp
  apply abs_lt.2
  constructor
  · linarith
  · linarith



-- 引理 30.15：提取子列的弱收敛性和内积序列的收敛性
lemma halpern_subsequence_weak_convergence
  {D : Set H}
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  {T : H → H}
  {C : Set H}
  (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty)
  (alg : Halpern T)
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_C_closed_convex : IsClosed C ∧ Convex ℝ C)
  (h_xn_bounded : ∃ M, ∀ n, ‖alg.x n‖ ≤ M)
  (h_Txn_bounded : ∃ M, ∀ (n : ℕ), ‖T (alg.x n)‖ ≤ M)
  :
  ∃ (n : ℕ → ℕ) (z : H) (m : H) (q : ℕ → ℝ),
    -- n 是严格递增的子列索引
    (∀ i j, i < j → n i < n j) ∧
    -- z 是子列的弱极限
    (z ∈ D ∧ WeakConverge (alg.x ∘ n) z) ∧
    -- m 是 alg.u 在 C 上的投影
    (m ∈ C ∧ ‖alg.u - m‖ = ⨅ w : C, ‖alg.u - w‖) ∧
    -- q_n = ⟪T(x_n) - m, alg.u - m⟫
    (q = fun n => ⟪T (alg.x n) - m, alg.u - m⟫) ∧
    -- 子列满足收敛性
    (Tendsto (q ∘ n) atTop (𝓝 (limsup q atTop))) := by

  -- 第一步：C 的闭凸性
  have h_C_closed : IsClosed C := h_C_closed_convex.1
  have h_C_convex : Convex ℝ C := h_C_closed_convex.2

  -- 第二步：存在投影点 m ∈ C 使得 m 是 alg.u 在 C 上的投影
  obtain ⟨m, hm_in_C, hm_proj⟩ :=
    existence_of_projection_point C hT_fixpoint h_C_convex h_C_closed alg.u

  -- 第三步：定义数列 q_n = ⟪T(x_n) - m, alg.u - m⟫
  let q : ℕ → ℝ := fun n => ⟪T (alg.x n) - m, alg.u - m⟫
  rcases h_Txn_bounded with ⟨M_Tx, hM_Tx⟩
  have hq_bdd : ∃ M : ℝ, ∀ k : ℕ, |q k| ≤ M := by
    use (M_Tx + ‖m‖) * ‖alg.u - m‖
    intro k
    calc
      |q k| = |⟪T (alg.x k) - m, alg.u - m⟫| := rfl
      _ = max (⟪T (alg.x k) - m, alg.u - m⟫) (-⟪T (alg.x k) - m, alg.u - m⟫) := by
        exact rfl
      _ = max (⟪T (alg.x k) - m, alg.u - m⟫) (⟪-(T (alg.x k) - m), alg.u - m⟫) := by
        congr
        exact Eq.symm (inner_neg_left (T (alg.x k) - m) (alg.u - m))
      _ ≤ ‖T (alg.x k) - m‖ * ‖alg.u - m‖ := by
        apply max_le
        · exact real_inner_le_norm (T (alg.x k) - m) (alg.u - m)
        · calc
            _ ≤ ‖-(T (alg.x k) - m)‖ * ‖alg.u - m‖ := by
              exact real_inner_le_norm (-(T (alg.x k) - m)) (alg.u - m)
            _ = ‖T (alg.x k) - m‖ * ‖alg.u - m‖ := by
              rw [norm_neg]
      _ ≤ (‖T (alg.x k)‖ + ‖m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact norm_sub_le (T (alg.x k)) m
        · exact norm_nonneg _
      _ ≤ (M_Tx + ‖m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul_of_nonneg_right
        · simp
          exact hM_Tx k
        · exact norm_nonneg _
  -- 第四步：证明存在子列 q_k_n 使得 lim q_k_n → limsup q_n
  have h_subseq_q : ∃ (k : ℕ → ℕ), StrictMono k ∧ Tendsto (q ∘ k) atTop (𝓝 (limsup q atTop)) := by
    obtain ⟨φ, L, h_strict_mono, h_L_eq, h_tendsto⟩ := lim_subsequence_eq_limsup q hq_bdd
    exact ⟨φ, h_strict_mono, by rwa [← h_L_eq]⟩
  obtain ⟨k, h_k_strict_mono, h_k_tendsto⟩ := h_subseq_q

  -- 第五步：在子列 x(k_n) 中提取弱收敛子列
  -- 首先证明子列 x(k_n) 有界
  have h_xk_bounded : ∃ M, ∀ j, ‖alg.x (k j)‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_xn_bounded
    exact ⟨M, fun j => hM (k j)⟩
  -- 由有界性，存在进一步的子列 x(k(l_n)) 弱收敛到某点 z
  obtain ⟨l, z, h_l_strict_mono, h_weak_xkl_to_z⟩ :=
    bounded_seq_weakly_convergent_subsequence (alg.x ∘ k) h_xk_bounded

  -- 第六步：验证 z ∈ D（由 D 的闭性和弱收敛性）
  have h_z_in_D : z ∈ D := by
    have h_x_in_D : ∀ j, alg.x (k (l j)) ∈ D := fun j => halg_x_in_D _
    have h_D_weakly_closed : IsWeaklyClosed D := by
      apply closed_is_weakly_closed
      · exact hD_convex
      · exact hD_closed
    have h_D_weakly_seq_closed : IsWeaklySeqClosed D := by
      apply weakly_closed_seq_closed
      exact h_D_weakly_closed
    simp only [IsWeaklySeqClosed] at h_D_weakly_seq_closed
    apply h_D_weakly_seq_closed
    · exact h_x_in_D
    · exact h_weak_xkl_to_z

  -- 第七步：定义复合子列索引
  let n : ℕ → ℕ := k ∘ l
  have h_n_strict_mono : ∀ i j, i < j → n i < n j := by
    intros i j hij
    unfold n
    simp only [Function.comp_apply]
    exact h_k_strict_mono (h_l_strict_mono i j hij)

  -- 第八步：证明内积序列的收敛性
  have h_n_tendsto : Tendsto (q ∘ n) atTop (𝓝 (limsup q atTop)) := by
    have h_comp : (q ∘ n) = (q ∘ k) ∘ l := by
      funext j
      simp only [Function.comp_apply, n]
    rw [h_comp]
    apply h_k_tendsto.comp
    exact StrictMono.tendsto_atTop h_l_strict_mono

  -- 返回所有构造
  exact ⟨n, z, m, q, h_n_strict_mono, ⟨h_z_in_D, h_weak_xkl_to_z⟩,
         ⟨hm_in_C, hm_proj⟩, rfl, h_n_tendsto⟩

-- 引理：子列满足误差趋零条件
lemma halpern_subseq_x_sub_Tx_tendsto_zero
  {T : H → H}
  (alg : Halpern T)
  (n : ℕ → ℕ)
  (h_n_strict_mono : ∀ i j, i < j → n i < n j)
  (h_x_Tx_limit : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (𝓝 0))
  : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (𝓝 0) := by
  -- 首先证明严格递增函数满足 n k ≥ k
  have h_n_k_ge_k : ∀ k, n k ≥ k := by
    intro k
    induction k with
    | zero =>
      have := h_n_strict_mono 0 1 (by norm_num)
      omega
    | succ k' ih =>
      have : n (k' + 1) > n k' := h_n_strict_mono k' (k' + 1) (by omega)
      omega
  -- 证明子列也满足误差趋零条件
  rw [Metric.tendsto_atTop]
  intro ε ε_pos
  rw [Metric.tendsto_atTop] at h_x_Tx_limit
  obtain ⟨N, hN⟩ := h_x_Tx_limit ε ε_pos
  use N
  intro k hk
  specialize hN (n k) ?_
  · exact Nat.le_trans hk (h_n_k_ge_k k)
  · rw [dist_eq_norm] at hN ⊢
    exact hN

-- 引理：子列的固定点性质
lemma halpern_subseq_fixed_point
  {D : Set H}
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  (hD_nonempty : D.Nonempty)
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D)
  (alg : Halpern T)
  (n : ℕ → ℕ)
  (z : H)
  (h_z_in_D : z ∈ D)
  (h_z_weak_limit : WeakConverge (alg.x ∘ n) z)
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (𝓝 0))
  : z ∈ Fix T := by
  apply corollary_4_28 hD_closed hD_convex hD_nonempty hT_nonexp
    (alg.x ∘ n) (fun k => halg_x_in_D (n k)) z h_z_in_D
    h_z_weak_limit h_subseq_x_Tx_limit

-- 引理 30.16：子列内积序列的上极限不等式
lemma halpern_limsup_inner_le_zero
  {D : Set H}
  {T : H → H}
  {C : Set H}
  (hC : C = Fix T ∩ D)
  (hC_closed_convex : IsClosed C ∧ Convex ℝ C)
  (alg : Halpern T)
  (n : ℕ → ℕ)
  (z : H)
  (h_z_in_C : z ∈ C)
  (h_weak_xn_to_z : WeakConverge (alg.x ∘ n) z)
  (m : H)
  (hm_in_C : m ∈ C)
  (hm_proj : ‖alg.u - m‖ = ⨅ w : C, ‖alg.u - w‖)
  (h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (𝓝 0))
  (h_n_tendsto : Tendsto (fun k => ⟪T (alg.x (n k)) - m, alg.u - m⟫) atTop
    (𝓝 (limsup (fun n => ⟪T (alg.x n) - m, alg.u - m⟫) atTop)))
  : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0 := by

  -- lim ⟨T xkn − xkn , x − PCx⟩ → 0
  have h_subseq_inner_limit1 : Tendsto
    (fun k => ⟪T (alg.x (n k)) - alg.x (n k), alg.u - m⟫) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε ε_pos
      let R := ‖alg.u - m‖
      rw [Metric.tendsto_atTop] at h_subseq_x_Tx_limit
      by_cases hR : R = 0
      · use 0
        intro k hk
        rw [Real.dist_eq]
        simp only [sub_zero]
        have h_vec_zero : alg.u - m = 0 := norm_eq_zero.mp hR
        simp [inner_zero_right, h_vec_zero]
        linarith
      · have hR_pos : 0 < R := by
          simp only [R]
          exact norm_pos_iff.mpr (by
            intro h_eq
            have : alg.u - m = 0 := h_eq
            have : ‖alg.u - m‖ = 0 := by simp [this]
            exact hR this)
        obtain ⟨N, hN⟩ := h_subseq_x_Tx_limit (ε / R) (by positivity)
        use N
        intro k hk
        specialize hN k hk
        rw [dist_eq_norm] at hN
        simp at hN
        rw [Real.dist_eq]
        simp only [sub_zero]
        calc
          _ ≤ ‖T (alg.x (n k)) - alg.x (n k)‖ * ‖alg.u - m‖ := by
            apply abs_real_inner_le_norm
          _ = ‖alg.x (n k) - T (alg.x (n k))‖ * ‖alg.u - m‖ := by
            congr 1
            rw [norm_sub_rev]
          _ < (ε / R) * R := by
            apply mul_lt_mul_of_pos_right
            · exact hN
            · exact hR_pos
          _ = ε := by field_simp [ne_of_gt hR_pos]

  -- lim ⟨xkn, x − PCx⟩ → ⟨ z , x − PCx⟩
  have h_subseq_inner_limit2 : Tendsto (fun k => ⟪alg.x (n k), alg.u - m⟫)
    atTop (𝓝 ⟪z , alg.u - m⟫) := by
    rw [tendsto_iff_weakConverge] at h_weak_xn_to_z
    apply h_weak_xn_to_z (alg.u - m)

  -- lim ⟨xkn - PCx, x − PCx⟩ → ⟨ z - PCx, x − PCx⟩
  have h_subseq_inner_limit3 : Tendsto (fun k => ⟪alg.x (n k) - m, alg.u - m⟫)
    atTop (𝓝 ⟪z - m, alg.u - m⟫) := by
      by_cases h_eq : alg.u = m
      · simp [h_eq]
      · rw [Metric.tendsto_atTop]
        intro ε ε_pos
        rw [Metric.tendsto_atTop] at h_subseq_inner_limit2
        obtain ⟨N, hN⟩ := h_subseq_inner_limit2 ε (by positivity)
        use N
        intro k hk
        specialize hN k hk
        rw [Real.dist_eq] at hN ⊢
        calc
          _ = |⟪alg.x (n k), alg.u - m⟫- ⟪z, alg.u - m⟫| := by
            congr 1
            rw [inner_sub_left, inner_sub_left]
            ring
          _ < ε := by exact hN

  -- 利用投影性质得到不等式
  have h_proj_ineq : ⟪alg.u - m, z - m⟫ ≤ 0 := by
    have hm_in_D : m ∈ D := by
      rw [hC] at hm_in_C
      exact Set.mem_of_mem_inter_right hm_in_C
    have h_proj_apply : ∀ w ∈ C, ⟪alg.u - m, w - m⟫ ≤ 0 := by
      apply proj_pt_inner_le_zero alg.u m C ?_ hm_in_C ?_
      · exact hC_closed_convex.2
      · exact hm_proj
    exact h_proj_apply z h_z_in_C

  -- 子列内积的收敛性
  have h_subseq_inner_limit4 : Tendsto (fun k => ⟪ T (alg.x (n k)) - m, alg.u - m⟫)
    atTop (𝓝 ⟪z - m, alg.u - m⟫) := by
      have h_inner_diff : ∀ k,
          ⟪ T (alg.x (n k)) - m, alg.u - m⟫ =
          ⟪ T (alg.x (n k)) - alg.x (n k), alg.u - m⟫ +
          ⟪ alg.x (n k) - m, alg.u - m⟫ := by
        intro k
        rw [inner_sub_left, inner_sub_left, inner_sub_left]
        ring
      convert Tendsto.add h_subseq_inner_limit1 h_subseq_inner_limit3 using 1
      funext k
      · exact h_inner_diff k
      · simp

  -- 上极限等于子列的极限
  have h_limsup_eq : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop
    = ⟪z - m, alg.u - m⟫ := by
    have h1 := h_n_tendsto
    have h2 := h_subseq_inner_limit4
    exact tendsto_nhds_unique h1 h2

  -- 最终结论
  calc
    _ = ⟪z - m, alg.u - m⟫ := h_limsup_eq
    _ = ⟪alg.u - m, z - m⟫ := by exact real_inner_comm (alg.u - m) (z - m)
    _ ≤ 0 := h_proj_ineq


-- 引理：从上极限和步长条件提取存在量化形式
lemma halpern_eps_exists_of_limsup_and_alpha
  {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {T : H → H}
  (alg : Halpern T)
  (m : H)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k,
      ⟪T (alg.x n) - m, alg.u - m⟫ ≤ ε ∧
        alg.α n * ‖alg.u - m‖^2 ≤ ε := by
  intro ε hε
  have h_norm_um : 0 ≤ ‖alg.u - m‖ := norm_nonneg _
  by_cases h_um_zero : ‖alg.u - m‖ = 0
  · have h_u_eq_m : alg.u = m := by
      exact eq_of_norm_sub_eq_zero h_um_zero
    rw [h_u_eq_m]
    simp
    use 0
    intro n hn
    · linarith
  · -- 若 ‖u-m‖ ≠ 0
    have h_um_pos : 0 < ‖alg.u - m‖ := by
      exact norm_pos_iff.mpr (fun h => h_um_zero (by
        have : alg.u - m = 0 := h
        simp [this]))
    have h_um_sq_pos : 0 < ‖alg.u - m‖^2 := by positivity

    -- 从 h_α_limit 得到 ∃k₁ 使得 λₙ < ε/‖u-m‖²
    rw [Metric.tendsto_atTop] at h_α_limit
    obtain ⟨k₁, hk₁⟩ := h_α_limit (ε / ‖alg.u - m‖^2) (by positivity)

    have h_limsup_half : ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ ε / 2 := by
      have h_eventually : ∀ᶠ n in atTop,
          ⟪T (alg.x n) - m, alg.u - m⟫ < ε / 2 := by
        have : (0 : ℝ) < ε / 2 := by linarith
        have h_gap : limsup (fun k => ⟪T (alg.x k) - m, alg.u - m⟫) atTop < ε / 2 := by
          linarith [h_limsup_neg]
        apply Filter.eventually_lt_of_limsup_lt
        · exact h_gap
        · exact h_inner_bounded
      filter_upwards [h_eventually] with n hn
      exact le_of_lt hn

    rw [eventually_atTop] at h_limsup_half
    obtain ⟨k₂, hk₂⟩ := h_limsup_half
    use max k₁ k₂
    intro n hn
    have hn_k₁ : n ≥ k₁ := le_of_max_le_left hn
    have hn_k₂ : n ≥ k₂ := le_of_max_le_right hn
    constructor
    · exact le_trans (hk₂ n hn_k₂) (by linarith)
    · have h_α_small : ‖alg.α n - 0‖ < ε / ‖alg.u - m‖^2 := hk₁ n hn_k₁
      rw [sub_zero] at h_α_small
      have h_α_nonneg : 0 ≤ alg.α n := by
        have := h_α_range n
        simp [Set.mem_Ioo] at this
        linarith
      have h_alpha_abs : |alg.α n| = alg.α n := abs_of_nonneg h_α_nonneg
      rw [← h_alpha_abs] at h_α_small
      · calc
          alg.α n * ‖alg.u - m‖^2
              ≤ (ε / ‖alg.u - m‖^2) * ‖alg.u - m‖^2 := by
                apply mul_le_mul_of_nonneg_right
                · simp [h_alpha_abs] at h_α_small
                  linarith
                · exact h_um_sq_pos.le
          _ = ε := by field_simp [ne_of_gt h_um_sq_pos]

-- 30.18：投影距离的上界
lemma halpern_xn_sub_PCx_upbd
  {T : H → H}
  {C : Set H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n,
    ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧
    ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k,
      ‖alg.x (n+1) - m‖ ^ 2 ≤ alg.α n * ε + (1 - alg.α n) *
        ‖alg.x n - m‖ ^ 2 + 2 * alg.α n * ε := by
  intro ε hε
  have h_inner_bound := halpern_eps_exists_of_limsup_and_alpha alg m h_α_limit h_α_range
    h_limsup_neg h_inner_bounded
  specialize h_inner_bound ε hε
  rcases h_inner_bound with ⟨k, h_control⟩
  use k
  intro n hn
  have h_αn0 : 0 < alg.α n := (h_α_range n).1
  have h_αn1 : alg.α n < 1 := (h_α_range n).2
  specialize h_control n hn
  rcases h_control with ⟨h_inner_control, h_mul_control⟩
  calc
    ‖alg.x (n+1) - m‖ ^ 2
        = ‖alg.α n • (alg.u - m) + (1 - alg.α n) • (T (alg.x n) - m)‖ ^ 2 := by
          rw [alg.update]
          congr
          simp [smul_sub, sub_smul, ← add_sub_assoc, add_comm]
      _ = ‖alg.α n • (alg.u - m)‖ ^ 2 +
          ‖(1 - alg.α n) • (T (alg.x n) - m)‖ ^ 2 + 2 * ⟪alg.α n • (alg.u - m),
            (1 - alg.α n) • (T (alg.x n) - m)⟫ := by
              rw [← real_inner_self_eq_norm_sq]
              rw [inner_add_left, inner_add_right, inner_add_right]
              ring_nf
              rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
              simp [real_inner_comm, mul_two]
              ring
      _ ≤ alg.α n * ε + (1 - alg.α n) * ‖alg.x n - m‖ ^ 2 + 2 * alg.α n * ε := by
        apply add_le_add
        · apply add_le_add
          · -- 第一项：‖α_n • (u - m)‖² ≤ α_n * ε
            rw [norm_smul]
            calc
              (|alg.α n| * ‖alg.u - m‖) ^ 2
                  = (alg.α n)^2 * ‖alg.u - m‖^2 := by
                    rw [mul_pow, sq_abs]
                _ = alg.α n * (alg.α n * ‖alg.u - m‖^2) := by
                  ring
                _ ≤ alg.α n * ε := by
                  apply mul_le_mul
                  · simp
                  · exact h_mul_control
                  · apply mul_nonneg
                    · have h_α_nonneg : 0 ≤ alg.α n := by linarith
                      exact h_α_nonneg
                    · exact sq_nonneg ‖alg.u - m‖
                  · linarith
          · -- 第二项：‖(1-α_n) • (Tx_n - m)‖² ≤ (1-α_n) * ‖x_n - m‖²
            rw [norm_smul]
            calc
              (|1 - alg.α n| * ‖T (alg.x n) - m‖) ^ 2
                  = (1 - alg.α n) ^ 2 * ‖T (alg.x n) - m‖^2 := by
                    rw [mul_pow, sq_abs]
                _ ≤ (1 - alg.α n)^2 * ‖alg.x n - m‖^2 := by
                  apply mul_le_mul
                  · simp
                  · gcongr
                    apply (h_induction m hm_in_C n).1
                  · apply sq_nonneg
                  · exact sq_nonneg (1 - alg.α n)
                _ = (1 - alg.α n) * ((1 - alg.α n) * ‖alg.x n - m‖^2) := by
                  ring
                _ ≤ (1 - alg.α n) * ‖alg.x n - m‖^2 := by
                  apply mul_le_mul
                  · simp
                  · nth_rewrite 2 [← one_mul (‖alg.x n - m‖ ^ 2)]
                    apply mul_le_mul
                    · linarith
                    · simp
                    · exact sq_nonneg ‖alg.x n - m‖
                    · simp
                  · apply mul_nonneg
                    · linarith
                    · exact sq_nonneg ‖alg.x n - m‖
                  · apply le_of_lt; linarith
        · -- 第三项：2 * ⟪α_n • (u - m), (1-α_n) • (Tx_n - m)⟫ ≤ 2 * α_n * ε
          calc
            2 * ⟪alg.α n • (alg.u - m), (1 - alg.α n) • (T (alg.x n) - m)⟫
                = 2 * alg.α n * (1 - alg.α n) * ⟪alg.u - m, T (alg.x n) - m⟫ := by
                  simp [real_inner_smul_left, real_inner_smul_right]
                  ring
              _ ≤ 2 * alg.α n * (1 - alg.α n) * ε := by
                gcongr
                · apply mul_nonneg
                  · linarith
                  · linarith
                · rw [real_inner_comm]; exact h_inner_control
              _ ≤ 2 * alg.α n * ε := by
                have h1_minus_α : 1 - alg.α n ≤ 1 := by linarith
                calc
                  2 * alg.α n * (1 - alg.α n) * ε
                      ≤ 2 * alg.α n * 1 * ε := by
                        apply mul_le_mul_of_nonneg_right
                        · apply mul_le_mul_of_nonneg_left h1_minus_α
                          · apply mul_nonneg
                            · norm_num
                            exact (h_α_range n).1.le
                        exact le_of_lt hε
                    _ = 2 * alg.α n * ε := by ring

-- 引理 30.19：归纳得到乘积形式
lemma halpern_xn_sub_PCx_prod
  {T : H → H}
  {C : Set H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n,
    ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧
    ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n k : ℕ, n ≥ N → k ≥ N → n ≥ k →
      ‖alg.x (n + 1) - m‖ ^ 2 ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 *
        (∏ l ∈ Finset.Icc k n, (1 - alg.α l)) := by

  -- 首先应用 30.18 获得逐步不等式
  have h_dist_bound := halpern_xn_sub_PCx_upbd
    alg h_α_range h_α_limit m hm_in_C h_induction h_limsup_neg
    h_inner_bounded
  intro ε hε
  obtain ⟨N, hN⟩ := h_dist_bound ε hε
  use N
  intro n k hn hk hnk
  -- 通过对 n - k 的长度进行归纳
  obtain ⟨len, rfl⟩ := exists_add_of_le hnk

  -- 对 len 进行归纳
  induction len with
  | zero =>
    -- 基础情况：n = k
    simp only [add_zero, Finset.Icc_self, Finset.prod_singleton]
    have h_step_case := hN k (by linarith)
    calc
      _ ≤ alg.α k * ε + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 + 2 * alg.α k * ε := by
        exact h_step_case
      _ = 3 * alg.α k * ε + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 := by ring
      _ ≤ 3 * ε * alg.α k + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 := by linarith
      _ ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 * (1 - alg.α k) := by
        have h1_minus_α : 0 ≤ 1 - alg.α k := by
          have := h_α_range k
          simp [Set.mem_Ioo] at this
          linarith
        have hε_pos : 0 ≤ ε := le_of_lt hε
        nlinarith [sq_nonneg (‖alg.x k - m‖)]
  | succ len' ih =>
    -- 归纳步：从 len' 推到 len' + 1
    have hnk' : N ≤ k + len' := by linarith
    have h_ih := ih hnk'

    -- 更新的不等式
    calc
      _ = ‖alg.x (k + len' + 1 + 1) - m‖ ^ 2 := by ring_nf
      _ ≤ alg.α (k + len' + 1) * ε +
        (1 - alg.α (k + len' + 1)) * ‖alg.x (k + len' + 1) - m‖ ^ 2 +
          2 * alg.α (k + len' + 1) * ε := by
            apply hN (k + len' + 1)
            linarith

      _ ≤ alg.α (k + len' + 1) * ε +
          (1 - alg.α (k + len' + 1)) * (3 * ε + ‖alg.x k - m‖ ^ 2 *
            ∏ l ∈ Finset.Icc k (k + len'), (1 - alg.α l))
              + 2 * alg.α (k + len' + 1) * ε := by
                have : k + len' ≥ k := by linarith
                simp
                apply mul_le_mul
                · simp
                · exact h_ih this
                · exact sq_nonneg ‖alg.x (k + len' + 1) - m‖
                · have h1_minus_α : 0 ≤ 1 - alg.α (k + len' + 1) := by
                    have := h_α_range (k + len' + 1)
                    simp [Set.mem_Ioo] at this
                    linarith
                  linarith

      _ = 3 * ε + ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k (k + (len' + 1)), (1 - alg.α l) := by
        have :-(alg.α (1 + k + len') * ‖alg.x k - m‖ ^ 2 *
          ∏ x ∈ Finset.Icc k (k + len'), (1 - alg.α x)) +
            ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (k + len'), (1 - alg.α x) =
              ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (1 + k + len'), (1 - alg.α x) := by
                simp [add_comm]; simp [← add_assoc]; simp [← Nat.succ_eq_add_one]
                rw [Finset.prod_Icc_succ_top]
                · ring_nf; simp; left; congr 1; ring_nf
                · linarith
        rw [mul_add]
        ring_nf
        rw [add_comm (-(alg.α (1 + k + len') * ‖alg.x k - m‖ ^ 2 *
          ∏ x ∈ Finset.Icc k (k + len'), (1 - alg.α x))) (ε * 3)]
        rw [add_assoc, add_eq_add_iff_eq_and_eq]
        · simp
          exact this
        · simp
        · linarith


-- 引理：从上极限有界得到序列有界
lemma halpern_inner_bounded_of_limsup
  {T : H → H}
  (alg : Halpern T)
  (m : H)
  (μ : ℝ)
  (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  (h_limsup_neg : limsup (fun k ↦ inner ℝ (T (alg.x k) - m) (alg.u - m)) atTop ≤ 0)
  : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M := by
  have : ∃ N, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ < N := by
    have h_limsup_neg' : limsup (fun k ↦ inner ℝ (T (alg.x k) - m) (alg.u - m)) atTop < 1 := by
      linarith
    use 1
    apply Filter.eventually_lt_of_limsup_lt
    · exact h_limsup_neg'
    · simp [autoParam, IsBoundedUnder, IsBounded]
      use (μ + ‖alg.u - m‖) * ‖alg.u - m‖
      use 0
      intro b; simp
      calc
        _ ≤ ‖T (alg.x b) - m‖ * ‖alg.u - m‖ := by
          exact real_inner_le_norm (T (alg.x b) - m) (alg.u - m)
        _ = ‖(T (alg.x b) - alg.u) + (alg.u - m)‖ * ‖alg.u - m‖ := by
          simp
        _ ≤ (‖T (alg.x b) - alg.u‖ + ‖alg.u - m‖) * ‖alg.u - m‖ := by
          apply mul_le_mul
          · exact norm_add_le (T (alg.x b) - alg.u) (alg.u - m)
          · simp
          · exact norm_nonneg (alg.u - m)
          · rw [← zero_add 0]
            apply add_le_add
            · exact norm_nonneg (T (alg.x b) - alg.u)
            · exact norm_nonneg (alg.u - m)
        _ ≤ (μ + ‖alg.u - m‖) * ‖alg.u - m‖ := by
          apply mul_le_mul
          · simp
            specialize hμ_Tx_bound b
            calc
              _ = ‖alg.u - T (alg.x b)‖ := by
                rw [norm_sub_rev]
              _ ≤ μ := hμ_Tx_bound
          · simp
          · simp
          · have : μ ≥ 0 := by
              specialize hμ_Tx_bound b
              have :‖alg.u - T (alg.x b)‖ ≥ 0 := norm_nonneg _
              linarith
            rw [← zero_add 0]
            apply add_le_add
            · exact this
            · apply norm_nonneg
  rcases this with ⟨N, hN⟩
  use N
  filter_upwards [hN] with n hn
  linarith





-- 引理：由(30.19)和步长条件得到 limsup 的上界
lemma halpern_limsup_bound_from_prod
  {T : H → H} {C : Set H} (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (m : H) (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n,
    ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧
    ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  (y : H) (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M)
  : ∀ ε > 0, ∃ N : ℕ, ∀ (n k : ℕ), n ≥ k → n ≥ N → k ≥ N →
      limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≤ 3 * ε := by
  have h_α_le_one : ∀ n, 1 - alg.α n ≤ 1 := by
    intro n
    have := h_α_range n
    simp [Set.mem_Ioo] at this
    linarith
  have h_nonneg_one_sub_α : ∀ n, 0 ≤ 1 - alg.α n := by
    intro n
    have := h_α_range n
    simp [Set.mem_Ioo] at this
    linarith
  intro ε hε
  obtain ⟨N, hN⟩ := halpern_xn_sub_PCx_prod
    alg h_α_range h_α_limit m hm_in_C h_induction h_limsup_neg
    h_inner_bounded ε hε

  have h_pointwise : ∀ n ≥ N, ∀ k ≥ N, n ≥ k →
      ‖alg.x (n + 1) - m‖ ^ 2 ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 *
        (∏ l ∈ Finset.Icc k n, (1 - alg.α l)) := by
    intros n hn k hk hnk
    exact hN n k hn hk hnk

  have h_prod_zero : ∀ k ≥ N,
    limsup (fun n => (∏ l ∈ Finset.Icc k n, (1 - alg.α l))) atTop = 0 := by
    intro k hk
    have h_prod_tendsto : Tendsto (fun n => ∏ l ∈ Finset.Icc k n, (1 - alg.α l))
      atTop (𝓝 0) :=
      infinite_prod_zero alg h_α_range h_α_sum_inf k
    have h_limsup_eq : limsup (fun n => ∏ l ∈ Finset.Icc k n, (1 - alg.α l)) atTop = 0 := by
      exact Tendsto.limsup_eq h_prod_tendsto
    exact h_limsup_eq

  use N
  intro n k hnk hnN hkN

  have h_xn_sub_m_bdd : ∃ M : ℝ, ∀ n : ℕ, ‖alg.x n - m‖ ^ 2 ≤ M := by
    obtain ⟨K, hK⟩ := h_seq_bounded
    have h_K_nonneg : 0 ≤ K := by
      have hK_nonneg : ∀ n, 0 ≤ ‖alg.x n - y‖ := by
        intro n
        exact norm_nonneg _
      exact Std.le_trans (hK_nonneg N) (hK N)
    use (‖y - m‖ + K) ^ 2
    intro n
    calc
      _ = ‖(alg.x n - y) + (y - m)‖ ^ 2 := by
        congr 1
        congr
        abel
      _ = ‖alg.x n - y‖ ^ 2 + ‖y - m‖ ^ 2 +
          2 * ⟪alg.x n - y, y - m⟫ := by
            rw [← real_inner_self_eq_norm_sq]
            rw [inner_add_left, inner_add_right, inner_add_right]
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
            simp [real_inner_comm]
            ring
      _ ≤ K ^ 2 + ‖y - m‖ ^ 2 +
          2 * ‖alg.x n - y‖ * ‖y - m‖ := by
            apply add_le_add
            · apply add_le_add
              · apply sq_le_sq.2
                · simp
                  convert hK n
                  simp
                  assumption
              · simp
            · rw [mul_assoc]
              apply mul_le_mul_of_nonneg_left
              · exact real_inner_le_norm (alg.x n - y) (y - m)
              · norm_num
      _ ≤ (‖y - m‖ + K) ^ 2 := by
        rw [pow_two (‖y - m‖ + K), mul_add, add_mul, add_mul]
        ring_nf
        simp
        rw [add_comm]
        simp
        rw[mul_comm]
        apply mul_le_mul
        · convert hK n
        · simp
        · exact norm_nonneg (y - m)
        · assumption

  calc
    _ ≤ limsup (fun n => 3 * ε + ‖alg.x k - m‖ ^ 2 *
      (∏ l ∈ Finset.Icc k n, (1 - alg.α l))) atTop := by
        apply limsup_le_limsup
        · apply eventually_atTop.2
          use k
          intro p hp
          apply h_pointwise
          · linarith
          · linarith
          · assumption
        · simp [autoParam, IsCoboundedUnder, IsCobounded]
          rcases h_xn_sub_m_bdd with ⟨M, hM⟩
          use 0
          intro a p q
          specialize q (p + 1) (by linarith)
          have h_norm_sq_nonneg : 0 ≤ ‖alg.x (p + 1 + 1) - m‖ ^ 2 := by
            apply sq_nonneg
          linarith
        · simp [autoParam, IsBoundedUnder, IsBounded]
          rcases h_xn_sub_m_bdd with ⟨M, hM⟩
          use (3 * ε + M)
          use 0
          intro b
          simp
          calc
            _ ≤ M * ∏ l ∈ Finset.Icc k b, (1 - alg.α l) := by
              apply mul_le_mul
              · convert hM k
              · simp
              · apply Finset.prod_nonneg
                intro i hi
                exact h_nonneg_one_sub_α i
              · have h_norm_sq_nonneg : 0 ≤ ‖alg.x b - m‖ ^ 2 := by
                  apply sq_nonneg
                have := hM b
                linarith
            _ ≤ M := by
              nth_rewrite 2 [← mul_one M]
              apply mul_le_mul_of_nonneg_left
              · exact Finset.prod_le_one (fun i a ↦ h_nonneg_one_sub_α i) fun i a ↦ h_α_le_one i
              · have h_norm_sq_nonneg : 0 ≤ ‖alg.x b - m‖ ^ 2 := by
                  apply sq_nonneg
                have := hM b
                linarith
    _ = limsup (fun n ↦ ‖alg.x k - m‖ ^ 2 *
      ∏ l ∈ Finset.Icc k n, (1 - alg.α l) + 3 * ε) atTop := by
      apply congr
      · ext n
        ring_nf
      · simp
    _ ≤ limsup (fun n => ‖alg.x k - m‖ ^ 2) atTop *
      limsup (fun n => (∏ l ∈ Finset.Icc k n, (1 - alg.α l))) atTop + 3 * ε := by
      rw [limsup_add_const]
      · simp
        apply limsup_mul_le
        · simp
          exact atTop_neBot
        · exact isBoundedUnder_const
        · apply eventually_atTop.2
          use k
          intro n hn
          simp
          exact Finset.prod_nonneg fun i a ↦ h_nonneg_one_sub_α i
        · simp [IsBoundedUnder, IsBounded]
          use 1
          use k
          intro n hn
          apply Finset.prod_le_one
          · intro i hi
            exact h_nonneg_one_sub_α i
          · intro i hi
            exact h_α_le_one i
      · simp [IsBoundedUnder, IsBounded]
        obtain ⟨M, hM⟩ := h_xn_sub_m_bdd
        have h_M_nonneg : 0 ≤ M := by
          by_contra h
          push_neg at h
          have := hM 1
          have h_contradiction : ‖alg.x 1 - m‖ ^ 2 < 0 := by
            linarith
          have := sq_nonneg (‖alg.x 1 - m‖)
          linarith
        use M
        use k
        intro n hn
        rw [← mul_one M]
        apply mul_le_mul
        · convert hM k
        · apply Finset.prod_le_one
          · intro i hi
            exact h_nonneg_one_sub_α i
          · intro i hi
            exact h_α_le_one i
        · apply Finset.prod_nonneg
          intro i hi
          exact h_nonneg_one_sub_α i
        · exact h_M_nonneg
      · --‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k n, (1 - alg.α l)有界
        simp [IsCoboundedUnder, IsCobounded]
        use 0
        intro a p q
        specialize q (p + 1) (by linarith)
        have : ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k (p + 1), (1 - alg.α l) ≥ 0 := by
          apply mul_nonneg
          · apply sq_nonneg
          · exact Finset.prod_nonneg fun i a ↦ h_nonneg_one_sub_α i
        linarith
    _ = limsup (fun n ↦ ‖alg.x k - m‖ ^ 2) atTop * 0 + 3 * ε := by
      congr
      · rw [h_prod_zero k]
        assumption
    _ = 3 * ε := by
      rw [mul_zero]
      simp

-- x n收敛到PCx
lemma halpern_convergence_aux
  {T : H → H}
  {C : Set H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n,
    ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧
    ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  (z : H)
  (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M)
  : Tendsto alg.x atTop (𝓝 m) := by
  -- limsup上界被ε控制
  have h_limsup_upbd : ∀ ε > 0,
      limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≤ 3 * ε := by
    intro ε hε
    have h_seq_bound_z : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M := by
      obtain ⟨M, hM⟩ := h_seq_bounded
      exact ⟨M + ‖z - z‖, fun n => by
        calc ‖alg.x n - z‖ = ‖(alg.x n - z) + (z - z)‖ := by simp
          _ ≤ ‖alg.x n - z‖ + ‖z - z‖ := norm_add_le _ _
          _ ≤ M + ‖z - z‖ := by linarith [hM n]⟩
    obtain ⟨N, hN⟩ := halpern_limsup_bound_from_prod alg
      h_α_range h_α_limit h_α_sum_inf m hm_in_C h_induction
      h_limsup_neg h_inner_bounded z h_seq_bound_z ε hε
    exact hN N N (le_refl N) (le_refl N) (le_refl N)

  -- limsup下界被0控制
  have h_limsup_udbd : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≥ 0 := by
    have h0 : limsup (fun (n : ℕ) => (0 : ℝ)) atTop = (0 : ℝ) := by
      exact limsup_const 0
    rw [← h0]
    apply limsup_le_limsup
    · apply eventually_atTop.2
      use 0
      intro n hn
      simp
    · simp [autoParam]
      apply Filter.IsCoboundedUnder.of_frequently_ge
      exact frequently_const.mpr h_limsup_neg
    · simp [autoParam, IsBoundedUnder, IsBounded]
      have h_seq_bounded' : ∃ M, ∀ (n : ℕ), ‖alg.x (n + 1) - z‖ ≤ M := by
        rcases h_seq_bounded with ⟨M,hM⟩
        use M
        intro n
        exact hM (n + 1)
      rcases h_seq_bounded' with ⟨M,hM⟩
      use (M + ‖z - m‖)^2
      use 0
      intro n; simp
      calc
        _ = ‖alg.x (n + 1) - z + z - m‖ ^ 2 := by
          simp
        _ ≤ (‖alg.x (n + 1) - z‖ + ‖z - m‖) ^ 2 := by
          apply sq_le_sq.mpr
          simp
          have : ‖alg.x (n + 1) - z‖ + ‖z - m‖ ≥ 0 := add_nonneg (norm_nonneg _) (norm_nonneg _)
          rw [abs_of_nonneg this]
          exact norm_sub_le_norm_sub_add_norm_sub (alg.x (n + 1)) z m
        _ ≤ (M + ‖z - m‖) ^ 2 := by
          apply sq_le_sq.mpr
          simp [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
          rw [abs_of_nonneg]
          · exact add_le_add_right (hM n) ‖z - m‖
          · apply add_nonneg
            · specialize hM 0
              have : ‖alg.x (0 + 1) - z‖ ≥ 0 := norm_nonneg _
              linarith
            · exact norm_nonneg _

  -- 结合上下界得到极限为0
  have h_limsup_zero : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop = 0 := by
    by_contra h_ne_zero
    push_neg at h_ne_zero
    have h_pos : 0 < limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop :=
      lt_of_le_of_ne h_limsup_udbd (Ne.symm h_ne_zero)
    let L := limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop
    have h_all_eps : ∀ ε > 0, L ≤ 3 * ε := fun ε hε => h_limsup_upbd ε hε
    have h_sixth : 0 < L / 6 := by linarith
    have h_bound := h_all_eps (L / 6) h_sixth
    have h_contradiction : L ≤ L / 2 := by linarith
    linarith

  -- 从 limsup = 0 推出平方范数趋于零
  have h_norm_sq_tendsto_zero : Tendsto (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop (𝓝 0) := by
    rw [← h_limsup_zero]
    have h_nonneg : ∀ n, 0 ≤ ‖alg.x (n + 1) - m‖ ^ 2 := fun n => sq_nonneg _
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    have h_eventually : ∀ᶠ n in atTop, ‖alg.x (n + 1) - m‖ ^ 2 < ε := by
      have h_limsup_lt : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop < ε := by
        rw [h_limsup_zero]
        exact ε_pos
      apply Filter.eventually_lt_of_limsup_lt
      · exact h_limsup_lt
      · simp [autoParam, IsBoundedUnder, IsBounded]
        have h_seq_bounded' : ∃ M, ∀ (n : ℕ), ‖alg.x (n + 1) - z‖ ≤ M := by
          rcases h_seq_bounded with ⟨M,hM⟩
          use M
          intro n
          exact hM (n + 1)
        rcases h_seq_bounded' with ⟨M,hM⟩
        use (M + ‖z - m‖)^2
        use 0
        intro n; simp
        calc
          _ ≤ (‖alg.x (n + 1) - z‖ + ‖z - m‖) ^ 2 := by
            apply sq_le_sq.mpr
            simp [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
            exact norm_sub_le_norm_sub_add_norm_sub (alg.x (n + 1)) z m

          _ ≤ (M + ‖z - m‖) ^ 2 := by
            apply sq_le_sq.mpr
            simp [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
            rw [abs_of_nonneg]
            · exact add_le_add_right (hM n) ‖z - m‖
            · apply add_nonneg
              · specialize hM 1
                have : ‖alg.x (1 + 1) - z‖ ≥ 0 := norm_nonneg _
                linarith
              · apply norm_nonneg
    obtain ⟨N, hN⟩ := (eventually_atTop).mp h_eventually
    use N
    intro n hn
    rw [Real.dist_eq, h_limsup_zero]
    simp only [sub_zero]
    simp
    exact abs_of_nonneg (h_nonneg n) ▸ hN n hn

  -- 从平方范数趋于零推出范数趋于零
  have h_norm_tendsto_zero : Tendsto (fun n => ‖alg.x (n + 1) - m‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h_norm_sq_tendsto_zero
    obtain ⟨N, hN⟩ := h_norm_sq_tendsto_zero (ε ^ 2) (by positivity)
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq] at hN ⊢
    simp only [sub_zero] at hN ⊢
    have h_sq : ‖alg.x (n + 1) - m‖ ^ 2 < ε ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)] at hN
      exact hN
    simp
    apply sq_lt_sq.mp at h_sq
    simp at h_sq
    convert h_sq
    exact Eq.symm (abs_of_pos ε_pos)

  -- 从范数趋于零推出向量趋于零
  have h_diff_tendsto_zero : Tendsto (fun n => alg.x (n + 1) - m) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h_norm_tendsto_zero
    obtain ⟨N, hN⟩ := h_norm_tendsto_zero ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN ⊢
    simp at hN ⊢
    exact hN

  -- 从相邻差趋于零推出原序列收敛
  have h_shifted : Tendsto (fun n => alg.x (n + 1)) atTop (𝓝 m) := by
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h_diff_tendsto_zero
    obtain ⟨N, hN⟩ := h_diff_tendsto_zero ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN ⊢
    simp at hN ⊢
    exact hN
  exact (tendsto_add_atTop_iff_nat 1).mp h_shifted

#check Filter.eventually_lt_of_limsup_lt
#check norm_eq_iInf_iff_real_inner_le_zero--投影的形式

-- x 0 = u
lemma halpern_convergence_point_same
  {D : Set H}
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  (hD_nonempty : D.Nonempty)
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D)
  {C : Set H}
  (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty)
  (alg : Halpern T)
  (halg_x0 : alg.x0 ∈ D) --  初始点在 D 中
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N,
    alg.α n) atTop atTop) -- λ求和发散
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1)
    - alg.α n|)) -- 差值级数收敛
  (coincidence : alg.u = alg.x0)
  : ∃ (p : H), p ∈ C ∧
      Tendsto alg.x atTop (𝓝 p) ∧
      (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  have hT_quasinonexp := nonexpansive_leadsto_quasinonexpansive hT_nonexp
  have hC_closed_convex := by
    apply quasinonexpansive_fixedPoint_closed_convex
      hD_closed hD_convex hD_nonempty hT_quasinonexp
  obtain ⟨y, hy_in_C⟩ := hT_fixpoint
  have h_induction :=
    halpern_distance_monotone
      hT_nonexp hC alg halg_x0 halg_x_in_D h_α_range coincidence

  -- 证明序列有界 (30.6)
  have h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M := by
    use ‖alg.x0 - y‖
    intro n
    apply (h_induction y hy_in_C n).2

  have h_xn_bounded : ∃ M, ∀ n, ‖alg.x n‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_seq_bounded
    let M2 := ‖y‖
    use M1 + M2
    intro n
    calc
      ‖alg.x n‖ = ‖(alg.x n - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖alg.x n - y‖ + ‖y‖ := by apply norm_add_le
      _ ≤ M1 + M2 := by linarith [hM1 n]

  -- 证明 (Txₙ)ₙ∈ℕ 有界 (30.7)
  have h_Tseq_bounded : ∃ M, ∀ n, ‖T (alg.x n) - y‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_seq_bounded
    use M
    intro n
    calc
      _ ≤ ‖alg.x n - y‖ := (h_induction y hy_in_C n).1
      _ ≤ M := hM n
  have h_Txn_bounded : ∃ M, ∀ n, ‖T (alg.x n)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_Tseq_bounded
    let M2 := ‖y‖
    use M1 + M2
    intro n
    calc
      ‖T (alg.x n)‖ = ‖(T (alg.x n) - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖T (alg.x n) - y‖ + ‖y‖ := by apply norm_add_le
      _ ≤ M1 + M2 := by linarith [hM1 n]

  -- 证明 (xₙ₊₁ - Txₙ)ₙ∈ℕ 有界 (30.8)
  have h_diff_bounded : ∃ M, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_seq_bounded
    obtain ⟨M2, hM2⟩ := h_Tseq_bounded
    use M1 + M2
    intro n
    calc
      ‖alg.x (n + 1) - T (alg.x n)‖ = ‖(alg.x (n + 1) - y) - (T (alg.x n) - y)‖ := by
        congr 1
        rw [sub_sub_sub_cancel_right]
      ‖(alg.x (n + 1) - y) - (T (alg.x n) - y)‖
        ≤ ‖alg.x (n + 1) - y‖ + ‖T (alg.x n) - y‖ := by
          apply norm_sub_le
      _ ≤ M1 + M2 := by
          linarith [hM1 (n + 1), hM2 n]

  -- 由 (30.6) 和 (30.7)，定义 μ = sup max{‖xₙ₊₁ - xₙ‖, ‖x - Txₙ‖} < +∞ (30.9)
  have h_mu_bound : ∃ μ : ℝ, μ > 0 ∧
      (∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ) ∧
      (∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ) := by
    apply halpern_mu_bound alg
    · exact h_diff_bounded
    · exact h_Tseq_bounded
    · exact h_seq_bounded
  obtain ⟨μ, hμ_pos, hμ_x_bound, hμ_Tx_bound⟩ := h_mu_bound

  -- 证明 xₙ₊₂ - xₙ₊₁ = (λₙ₊₁ - λₙ)(x - Txₙ) + (1 - λₙ₊₁)(Txₙ₊₁ - Txₙ) (30.10)
  let h_diff_formula := halpern_diff_formula alg

  -- 使用提取出来的范数差分不等式引理(30.11)
  have h_norm_diff_ineq := halpern_norm_diff_ineq alg hT_nonexp halg_x_in_D h_α_range
    h_diff_formula μ hμ_Tx_bound
  have hμ_nonneg : 0 ≤ μ := by exact le_of_lt hμ_pos

  -- 对于 n ≥ m，通过归纳证明 (30.12)
  have h_telescoping := halpern_telescoping_ineq
    alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq

  -- 让 n 和 m 趋于 +∞，得到 lim xn+1 − xn → 0
  have h_diff_limit := halpern_diff_limit alg h_α_range μ hμ_pos
    h_α_diff_finite h_α_sum_inf hμ_x_bound h_norm_diff_ineq h_telescoping

  -- 由Nonexpansive 得到(30.13)
  have h_T_diff_limit : Tendsto (fun n ↦ T (alg.x (n + 1)) - T (alg.x n)) atTop (𝓝 0) := by
    exact T_preserves_diff_tendsto_zero alg hT_nonexp halg_x_in_D h_diff_limit

  -- 结合(30.8)与(30.13)得到(30.14)
  have h_x_Tx_limit : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (𝓝 0) :=
    halpern_x_sub_Tx_tendsto_zero alg h_α_range h_α_limit μ hμ_pos hμ_Tx_bound h_diff_limit

  -- 得到(30.15)
  obtain ⟨p, z, m, q, h_n_strict_mono, ⟨h_z_in_D, h_weak_xn_to_z⟩,
    ⟨hm_in_C, hm_proj⟩, hq_def, h_n_tendsto⟩ := by
      apply halpern_subsequence_weak_convergence hD_closed hD_convex hC ?_ alg halg_x_in_D
      · rw [hC]
        exact hC_closed_convex
      · exact h_xn_bounded
      · exact h_Txn_bounded
      · apply Set.nonempty_of_mem hy_in_C

  -- xn-z有界
  have h_seq_bound_z : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_seq_bounded
    exact ⟨M + ‖y - z‖, fun n => by
      calc ‖alg.x n - z‖ = ‖(alg.x n - y) + (y - z)‖ := by simp
        _ ≤ ‖alg.x n - y‖ + ‖y - z‖ := norm_add_le _ _
        _ ≤ M + ‖y - z‖ := by linarith [hM n]⟩

  -- z∈C
  have h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (p k) - T (alg.x (p k))) atTop (𝓝 0) :=
    halpern_subseq_x_sub_Tx_tendsto_zero alg p h_n_strict_mono h_x_Tx_limit
  have h_z_fixed : z ∈ Fix T :=
    halpern_subseq_fixed_point hD_closed hD_convex hD_nonempty hT_nonexp
      alg p z h_z_in_D h_weak_xn_to_z halg_x_in_D h_subseq_x_Tx_limit
  have h_z_in_C : z ∈ C := by
    rw [hC]
    exact ⟨h_z_fixed, h_z_in_D⟩

  -- 得到(30.16)
  have h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0 := by
    apply halpern_limsup_inner_le_zero hC ?_ alg p z h_z_in_C
      h_weak_xn_to_z m hm_in_C hm_proj h_subseq_x_Tx_limit ?_
    · rw [hC]
      exact hC_closed_convex
    · rw [hq_def] at h_n_tendsto
      exact h_n_tendsto

  -- 由limsup有界得到lim有界
  have h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M := by
    apply halpern_inner_bounded_of_limsup alg m μ hμ_Tx_bound h_limsup_neg

  -- 得到(30.18)
  have h_xn_sub_PCx_upbd := halpern_xn_sub_PCx_upbd alg
    h_α_range h_α_limit m hm_in_C h_induction h_limsup_neg h_inner_bounded

  -- 得到(30.19)
  have h_xn_sub_PCx_prod := halpern_xn_sub_PCx_prod alg
    h_α_range h_α_limit m hm_in_C h_induction h_limsup_neg h_inner_bounded

  -- x n收敛到 m
  have h_x_conv : Tendsto alg.x atTop (𝓝 m) := by
    exact halpern_convergence_aux alg h_α_range h_α_limit h_α_sum_inf m hm_in_C
      h_induction h_limsup_neg h_inner_bounded y h_seq_bounded

  use m; use hm_in_C; use h_x_conv
  intro w hw_in_C
  apply proj_pt_inner_le_zero alg.u m C ?_ hm_in_C hm_proj w hw_in_C
  rw [hC]
  rcases hC_closed_convex with ⟨h1,h2⟩
  assumption

-- 结合两种情况的主定理
theorem halpern_convergence
  {D : Set H}
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  (hD_nonempty : D.Nonempty)
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D)
  {C : Set H}
  (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty)
  (hT_invariant : ∀ x ∈ D, T x ∈ D)
  (alg : Halpern T)
  (halg_x0 : alg.x0 ∈ D) --  初始点在 D 中
  (halg_u : alg.u ∈ D) -- 参考点在 D 中
  (halg_x_in_D : ∀ n, alg.x n ∈ D)
  -- 步长条件
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N,
    alg.α n) atTop atTop) -- λ求和发散
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1)
    - alg.α n|)) -- 差值级数收敛
  : ∃ (p : H), p ∈ C ∧
      Tendsto alg.x atTop (𝓝 p) ∧
      (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  by_cases h_coincidence : alg.u = alg.x0
  · exact halpern_convergence_point_same
      hD_closed hD_convex hD_nonempty hT_nonexp hC hT_fixpoint alg halg_x0
      halg_x_in_D h_α_range h_α_limit h_α_sum_inf h_α_diff_finite h_coincidence
  · have h_α_pos : ∀ n, 0 < alg.α n := by
      intro n
      exact (h_α_range n).1
    have h_α_lt_one : ∀ n, alg.α n < 1 := by
      intro n
      exact (h_α_range n).2
    -- 第一步：定义起始点
    let s0 := alg.u
    -- 第二步：定义新的迭代序列 s_n，满足相同的递推关系
    let s : ℕ → H := fun n =>
      Nat.recOn n alg.u fun k sk =>
        alg.α k • alg.u + (1 - alg.α k) • T sk
        -- 验证新序列的初值条件
    have h_s_init : s 0 = alg.u := by simp [s]

    have h_s_update : ∀ k, s (k + 1) = alg.α k • alg.u + (1 - alg.α k) • T (s k) := by
      intro k
      simp only [s]

    -- 验证新序列在 D 中
    have h_s_in_D : ∀ n, s n ∈ D := by
      intro n
      induction n with
      | zero => rw [h_s_init]; exact halg_u
      | succ k ih =>
        rw [h_s_update]
        have : alg.α k • alg.u + (1 - alg.α k) • T (s k) ∈ D := by
          apply hD_convex
          · exact halg_u
          · exact hT_invariant (s k) ih
          · linarith [h_α_pos k, h_α_lt_one k]
          · linarith [h_α_pos k, h_α_lt_one k]
          · simp
        exact this

    -- 应用情况(a)到新序列
    have h_s_convergence : ∃ (p : H), p ∈ C ∧
        Tendsto s atTop (𝓝 p) ∧
        (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
      apply halpern_convergence_point_same
        hD_closed hD_convex hD_nonempty hT_nonexp hC hT_fixpoint
        { x0 := alg.u
          u := alg.u
          x := s
          α := alg.α
          update := h_s_update
          initial_value := h_s_init }
        halg_u h_s_in_D
        h_α_range h_α_limit h_α_sum_inf h_α_diff_finite
        rfl  -- u = x0
    obtain ⟨p, hp_in_C, hp_s_conv, hp_inner⟩ := h_s_convergence

    have h_norm_bounded : ∀ n : ℕ, ‖alg.x (n + 1) - s (n + 1)‖
      ≤ ‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 n, (1 - alg.α k) := by
      intro n
      induction n with
      | zero =>
        simp [s, alg.update,← smul_sub]
        calc
          _ = (1 - alg.α 0) * ‖T (alg.x 0) - T alg.u‖ := by
            rw [norm_smul]
            simp; left; linarith [h_α_lt_one 0]
          _ ≤ (1 - alg.α 0) * ‖alg.x 0 - alg.u‖ := by
            apply mul_le_mul_of_nonneg_left
            · rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
              specialize hT_nonexp (halg_x_in_D 0) halg_u
              simp at hT_nonexp
              rw [edist_dist, edist_dist] at hT_nonexp
              simp at hT_nonexp
              rw[dist_eq_norm, dist_eq_norm] at hT_nonexp
              exact hT_nonexp
            · simp
              linarith [h_α_lt_one 0]
          _ = (1 - alg.α 0) * ‖alg.x 0 - s 0‖ := by
            rw [h_s_init]
          _ = ‖alg.x 0 - s 0‖ * (1 - alg.α 0) := by
            ring_nf

      | succ n ih =>
        calc
          _ = ‖(alg.α (n + 1) • alg.u + (1 - alg.α (n + 1)) • T (alg.x (n + 1)))
            - (alg.α (n + 1) • alg.u + (1 - alg.α (n + 1)) • T (s (n + 1)))‖ := by
            rw [alg.update, h_s_update]
          _ = ‖(1 - alg.α (n + 1)) • T (alg.x (n + 1))
            - (1 - alg.α (n + 1)) • T (s (n + 1))‖ := by
            simp
          _ =  ‖(1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (s (n + 1)))‖ := by
            rw [← smul_sub (1 - alg.α (n + 1)) (T (alg.x (n + 1))) (T (s (n + 1)))]
          _ = (1 - alg.α (n + 1)) * ‖T (alg.x (n + 1)) - T (s (n + 1))‖ := by
            rw [norm_smul]
            simp
            left
            linarith [h_α_lt_one (n + 1)]
          _ ≤ (1 - alg.α (n + 1)) * (‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) := by
            apply mul_le_mul_of_nonneg_left
            · rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
              specialize hT_nonexp (halg_x_in_D (n + 1)) (h_s_in_D (n + 1))
              simp at hT_nonexp
              rw [edist_dist, edist_dist] at hT_nonexp
              simp at hT_nonexp
              rw[dist_eq_norm, dist_eq_norm] at hT_nonexp
              exact Std.le_trans hT_nonexp ih
            · simp
              linarith [h_α_lt_one (n + 1)]
          _ = ‖alg.x 0 - s 0‖ * (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * (1 - alg.α (n + 1)) := by
            ring_nf
          _ = ‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 (n + 1), (1 - alg.α k) := by
            nth_rewrite 2 [← Nat.succ_eq_add_one]
            rw [Finset.prod_Icc_succ_top]
            · rw [← mul_assoc]
            · linarith

    have h_prod_tendsto_zero : Tendsto (fun n => (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k))
      * ‖alg.x 0 - s 0‖) atTop (𝓝 (0 * ‖alg.x 0 - s 0‖)) := by
        have h_prod := infinite_prod_zero alg h_α_range h_α_sum_inf 0
        apply Tendsto.mul_const
        exact h_prod

    have h_prod_tendsto_zero' : Tendsto (fun n => ((∏ k ∈ Finset.Icc 0 n, (1 - alg.α k))
      * ‖alg.x 0 - s 0‖)) atTop (𝓝 0) := by
        convert h_prod_tendsto_zero
        simp

    have h_diff_tendsto_zero : Tendsto (fun n => ‖alg.x (n + 1) - s (n + 1)‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε ε_pos
      rw [Metric.tendsto_atTop] at h_prod_tendsto_zero'
      obtain ⟨N, hN⟩ := h_prod_tendsto_zero' ε ε_pos
      use N
      intro n hn
      specialize hN n hn
      rw [Real.dist_eq] at hN ⊢
      simp only [sub_zero] at hN ⊢
      simp
      calc
        ‖alg.x (n + 1) - s (n + 1)‖ ≤ ‖alg.x 0 - s 0‖ * (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) := by
          exact h_norm_bounded n
        _ = |(∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * ‖alg.x 0 - s 0‖| := by
          rw [abs_of_nonneg]
          · ring_nf
          · apply mul_nonneg
            · apply Finset.prod_nonneg
              intro k hk
              simp
              linarith [h_α_lt_one k]
            · exact norm_nonneg _
        _ < ε := hN

    have h_diff_tendsto_zero' : Tendsto (fun n => alg.x n - s n) atTop (𝓝 0) := by
      have h_shifted : Tendsto (fun n => alg.x (n + 1) - s (n + 1)) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε ε_pos
        rw [Metric.tendsto_atTop] at h_diff_tendsto_zero
        obtain ⟨N, hN⟩ := h_diff_tendsto_zero ε ε_pos
        use N
        intro n hn
        specialize hN n hn
        rw [dist_eq_norm] at hN ⊢
        simp at hN ⊢
        exact hN
      exact (tendsto_add_atTop_iff_nat 1).mp h_shifted

    have h_x_tendsto_p : Tendsto alg.x atTop (𝓝 p) := by
      rw [Metric.tendsto_atTop]
      intro ε ε_pos
      rw [Metric.tendsto_atTop] at hp_s_conv h_diff_tendsto_zero'
      obtain ⟨N1, hN1⟩ := hp_s_conv (ε / 2) (by linarith)
      obtain ⟨N2, hN2⟩ := h_diff_tendsto_zero' (ε / 2) (by linarith)
      let N := max N1 N2
      use N
      intro n hn
      specialize hN1 n (le_of_max_le_left hn)
      specialize hN2 n (le_of_max_le_right hn)
      simp only [dist_eq_norm] at hN1 hN2 ⊢
      simp at hN2
      calc
        ‖alg.x n - p‖ = ‖(alg.x n - s n) + (s n - p)‖ := by
          congr
          simp
        _ ≤ ‖alg.x n - s n‖ + ‖s n - p‖ := by apply norm_add_le
        _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · exact hN2
          · exact hN1
        _ = ε := by ring

    use p
