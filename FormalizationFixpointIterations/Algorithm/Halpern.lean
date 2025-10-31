import FormalizationFixpointIterations.Nonexpansive.Definitions
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Fin

open Nonexpansive_operator Filter Topology BigOperators Function
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
  (m n : ℕ) (hmn : m ≤ n) :
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

lemma infinite_prod_zero {T : H → H}
  (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N,
    alg.α n) atTop atTop)
  (m n : ℕ) (hmn : m ≤ n) :
  Tendsto (fun n => ∏ k ∈ Finset.Icc m n, (1 - alg.α k)) atTop (𝓝 0) := by
  have h_prod_eq : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) =
      Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) := by
    intro n hn
    exact (prod_exp_sum alg h_α_range m n hn).1
  have h_exp_le : ∀ n ≥ m, Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) ≤
      Real.exp (∑ k ∈ Finset.Icc m n, -alg.α k) := by
    intro n hn
    exact (prod_exp_sum alg h_α_range m n hn).2
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

-- prop 4.23(i)
-- 拟非扩张映射的不动点集刻画
theorem quasinonexpansive_fixedPoint_characterization
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
    (x : H)
    (hx : x ∈ D) :
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
theorem quasinonexpansive_fixedPoint_closed_convex
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
    exact (intersection_set_is_closed_convex hD_closed hD_convex x hx).1
  · apply convex_iInter₂
    intro x hx
    exact (intersection_set_is_closed_convex hD_closed hD_convex x hx).2

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


def A {T : H → H} (alg : Halpern T) (m n : ℕ) := ∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))
noncomputable def B {T : H → H} (alg : Halpern T) (m n : ℕ) :=
  Real.exp (- ∑ k ∈ Finset.Icc m n, alg.α (k+1))


#check Fin.sum_Icc_succ





lemma sum_alpha_diff_tail_to_zero
  {T : H → H}
  (alg : Halpern T)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|)) :
  Tendsto (fun m => ∑' k : ℕ, |alg.α (k + m + 1) - alg.α (k + m)|) atTop (𝓝 0) := by
  sorry



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
  have hT_quasinonexp := nonexpansive_leadsto_quasinonexpansive hT_nonexp
  have hC_closed_convex := quasinonexpansive_fixedPoint_closed_convex
    hD_closed hD_convex hD_nonempty hT_quasinonexp
  by_cases coincidence : alg.u = alg.x0
  · obtain ⟨y, hy_in_C⟩ := hT_fixpoint
      -- 首先证明对于某个 n，如果 ‖xₙ - y‖ ⩽ ‖x - y‖，则归纳成立
    have h_induction : ∀ z ∈ C, ∀ n,
        ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖ := by
      intro z hz_C n
      induction n with
      | zero =>
        constructor
        · -- T 的非扩张性
          have hz_in_fixD : z ∈ Fix T ∩ D := by convert hz_C; exact hC.symm
          have ⟨hz_fix, hz_D⟩ := hz_in_fixD
          have hz_in_fix' : z ∈ Fix' T D := ⟨hz_D, hz_fix⟩
          rw [alg.initial_value]
          apply hT_quasinonexp
          apply halg_x0
          exact hz_in_fix'
        · rw [alg.initial_value]
      | succ k ih =>
        constructor
        · -- 第一部分：非扩张性
          have hz_in_fixD : z ∈ Fix T ∩ D := by convert hz_C; exact hC.symm
          have ⟨hz_fix, hz_D⟩ := hz_in_fixD
          have hz_in_fix' : z ∈ Fix' T D := ⟨hz_D, hz_fix⟩
          exact hT_quasinonexp (halg_x_in_D (k+1)) hz_in_fix'
        · -- 第二部分：使用归纳假设 ih.2
          rw [alg.update]
          calc
            ‖alg.α k • alg.u + (1 - alg.α k) • T (alg.x k) - z‖
              = ‖alg.α k • (alg.u - z) + (1 - alg.α k) • (T (alg.x k) - z)‖ := by
                congr 1; simp [smul_sub, sub_smul, add_sub, add_comm]
            _ ≤ alg.α k * ‖alg.u - z‖ + (1 - alg.α k) * ‖T (alg.x k) - z‖ := by
                apply norm_add_le_of_le
                · simp [norm_smul]
                  gcongr
                  have hα_pos : 0 < alg.α k := by
                    have := h_α_range k
                    simp [Set.mem_Ioo] at this
                    exact this.1
                  rw [abs_of_pos hα_pos]
                simp [norm_smul]
                gcongr
                have h1_minus_α_pos : 0 < 1 - alg.α k := by
                  have := h_α_range k
                  simp [Set.mem_Ioo] at this
                  linarith
                rw [abs_of_pos h1_minus_α_pos]
            _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x k - z‖ := by
                rw [← coincidence]
                gcongr
                · have := h_α_range k
                  simp [Set.mem_Ioo] at this
                  linarith
                · exact ih.1
            _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x0 - z‖ := by
                gcongr
                · have := h_α_range k
                  simp [Set.mem_Ioo] at this
                  linarith
                exact ih.2  -- 这里用归纳假设的第二部分
            _ = ‖alg.x0 - z‖ := by ring

    -- 证明序列有界 (30.6)
    have h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M := by
      use ‖alg.x0 - y‖
      intro n
      apply (h_induction y hy_in_C n).2

    -- 证明 (Txₙ)ₙ∈ℕ 有界 (30.7)
    have h_Tx_bounded : ∃ M, ∀ n, ‖T (alg.x n) - y‖ ≤ M := by
      obtain ⟨M, hM⟩ := h_seq_bounded
      use M
      intro n
      calc
        _ ≤ ‖alg.x n - y‖ := (h_induction y hy_in_C n).1
        _ ≤ M := hM n

    -- 证明 (xₙ₊₁ - Txₙ)ₙ∈ℕ 有界 (30.8)
    have h_diff_bounded : ∃ M, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M := by
      obtain ⟨M1, hM1⟩ := h_seq_bounded
      obtain ⟨M2, hM2⟩ := h_Tx_bounded
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
      obtain ⟨M1, hM1⟩ := h_diff_bounded
      obtain ⟨M2, hM2⟩ := h_Tx_bounded
      obtain ⟨M3, hM3⟩ := h_seq_bounded
      let μ := M1 + M2 + M3 + ‖alg.u - y‖ + 1
      use μ
      constructor
      · simp [μ]
        have hM1_nonneg : 0 ≤ M1 := by apply le_trans (norm_nonneg _) (hM1 0)
        have hM2_nonneg : 0 ≤ M2 := by apply le_trans (norm_nonneg _) (hM2 0)
        have hM3_nonneg : 0 ≤ M3 := by apply le_trans (norm_nonneg _) (hM3 0)
        have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _
        linarith
      constructor
      · intro n
        calc
          _ = ‖(alg.x (n + 1) - T (alg.x n)) + (T (alg.x n) - alg.x n)‖ := by
            abel_nf
          _ ≤ ‖alg.x (n + 1) - T (alg.x n)‖ + ‖T (alg.x n) - alg.x n‖ := by
            apply norm_add_le
          _ ≤ M1 + ‖T (alg.x n) - alg.x n‖ := by
            gcongr
            exact hM1 n
          _ = M1 + ‖(T (alg.x n) - y) + (y - alg.x n)‖ := by
            abel_nf
          _ ≤ M1 + (‖T (alg.x n) - y‖ + ‖y - alg.x n‖) := by
            apply add_le_add_left; apply norm_add_le
          _ ≤ M1 + (M2 + M3) := by
            gcongr
            · exact hM2 n
            · rw[norm_sub_rev]
              exact hM3 n
          _ ≤ μ := by
            simp [μ]
            rw[← add_assoc]
            have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _
            linarith
      · intro n
        calc
          ‖alg.u - T (alg.x n)‖ = ‖(alg.u - y) + (y - T (alg.x n))‖ := by
            abel_nf
          _ ≤ ‖alg.u - y‖ + ‖y - T (alg.x n)‖ := by
            apply norm_add_le
          _ ≤ ‖alg.u - y‖ + M2 := by
            gcongr
            rw[norm_sub_rev]
            exact hM2 n
          _ ≤ μ := by
            simp [μ]
            have hM1_nonneg : 0 ≤ M1 := by apply le_trans (norm_nonneg _) (hM1 0)
            have hM3_nonneg : 0 ≤ M3 := by apply le_trans (norm_nonneg _) (hM3 0)
            linarith

    obtain ⟨μ, hμ_pos, hμ_x_bound, hμ_Tx_bound⟩ := h_mu_bound
    -- 证明 xₙ₊₂ - xₙ₊₁ = (λₙ₊₁ - λₙ)(x - Txₙ) + (1 - λₙ₊₁)(Txₙ₊₁ - Txₙ) (30.10)
    have h_diff_formula : ∀ n,
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



    -- 证明 ‖xₙ₊₂ - xₙ₊₁‖ ≤ μ|λₙ₊₁ - λₙ| + (1 - λₙ₊₁)‖xₙ₊₁ - xₙ‖ (30.11)
    have h_norm_diff_ineq : ∀ n,
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

    -- 对于 n ≥ m，通过归纳证明 (30.12)
    have h_telescoping : ∀ n m, m ≤ n →
        ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤
        μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) +
        ‖alg.x (m + 1) - alg.x m‖ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
      intro n m hmn
      obtain ⟨k, rfl⟩ := exists_add_of_le hmn
      -- 对 k 做归纳
      induction k with
      | zero =>
        simp
        have := h_norm_diff_ineq m
        linarith
      | succ k ih =>
        calc
          ‖alg.x (m + (k + 1) + 2) - alg.x (m + (k + 1) + 1)‖
            ≤ μ * |alg.α (m + (k + 1) + 1) - alg.α (m + (k + 1))|
              + (1 - alg.α (m + (k + 1) + 1)) *
                ‖alg.x (m + (k + 1) + 1) - alg.x (m + (k + 1))‖ := by
                  exact h_norm_diff_ineq (m + (k + 1))
          _ ≤ μ * |alg.α (m + (k + 1) + 1) - alg.α (m + (k + 1))|
              + (1 - alg.α (m + (k + 1) + 1)) *
                (μ * (∑ l ∈ Finset.Icc m (m + k), |alg.α (l + 1) - alg.α l|) +
                  ‖alg.x (m + 1) - alg.x m‖ *
                    (∏ l ∈ Finset.Icc m (m + k), (1 - alg.α (l + 1)))) := by
                      gcongr
                      · have := h_α_range (m + (k + 1) + 1)
                        simp [Set.mem_Ioo] at this
                        linarith
                      have h_le : m ≤ m + k := by linarith
                      exact ih h_le
          _ = μ * |alg.α (m + (k + 1) + 1) - alg.α (m + (k + 1))|
              + (1 - alg.α (m + (k + 1) + 1)) * μ *
                (∑ l ∈ Finset.Icc m (m + k), |alg.α (l + 1) - alg.α l|) +
                  (1 - alg.α (m + (k + 1) + 1)) * ‖alg.x (m + 1) - alg.x m‖ *
                    (∏ l ∈ Finset.Icc m (m + k), (1 - alg.α (l + 1))) := by
                      ring
          _ ≤  μ * |alg.α (m + (k + 1) + 1) - alg.α (m + (k + 1))|
              + μ * (∑ l ∈ Finset.Icc m (m + k), |alg.α (l + 1) - alg.α l|) +
                (1 - alg.α (m + (k + 1) + 1)) * ‖alg.x (m + 1) - alg.x m‖ *
                  (∏ l ∈ Finset.Icc m (m + k), (1 - alg.α (l + 1))) := by
                    have h1_minus_α_pos : 0 < 1 - alg.α (m + (k + 1) + 1) := by
                      have := h_α_range (m + (k + 1) + 1)
                      simp [Set.mem_Ioo] at this
                      linarith
                    gcongr
                    · apply Finset.sum_nonneg
                      intro l _
                      exact abs_nonneg _
                    · nth_rewrite 2[← one_mul μ]
                      apply mul_le_mul_of_nonneg_right
                      · simp
                        have := h_α_range (m + (k + 1) + 1)
                        simp [Set.mem_Ioo] at this
                        linarith
                      linarith
          _ = μ * (∑ l ∈ Finset.Icc m (m + (k + 1)), |alg.α (l + 1) - alg.α l|) +
              ‖alg.x (m + 1) - alg.x m‖ *
                (∏ l ∈ Finset.Icc m (m + (k + 1)), (1 - alg.α (l + 1))) := by
                  rw [← add_assoc, ← Nat.succ_eq_add_one (m+k),
                    Finset.sum_Icc_succ_top, Finset.prod_Icc_succ_top, Nat.succ_eq_add_one]
                  ring_nf
                  · linarith
                  linarith







    -- 让 n 和 m 趋于 +∞，得到 lim ‖xₙ₊₂ - xₙ₊₁‖ ≤ 0 (30.12 的极限)
    have h_diff_to_zero : Tendsto (fun n => ‖alg.x (n + 1) - alg.x n‖) atTop (𝓝 0) := by
      sorry

    -- 因此 xₙ₊₁ - xₙ → 0，由非扩张性得 Txₙ₊₁ - Txₙ → 0 (30.13)
    have h_Tx_diff_to_zero : Tendsto (fun n => ‖T (alg.x (n + 1)) - T (alg.x n)‖) atTop (𝓝 0) := by
      sorry

    -- 从迭代公式得到 xₙ₊₁ - Txₙ = λₙ(x - Txₙ)
    have h_xn_Txn_relation : ∀ n,
        alg.x (n + 1) - T (alg.x n) = alg.α n • (alg.u - T (alg.x n)) := by
      intro n
      sorry

    -- 由于 λₙ → 0 且序列有界，得到 xₙ₊₁ - Txₙ → 0
    have h_xn_Txn_to_zero : Tendsto (fun n => ‖alg.x (n + 1) - T (alg.x n)‖) atTop (𝓝 0) := by
      sorry

    -- 结合 (30.13) 得到 xₙ₊₁ - Txₙ₊₁ → 0
    have h_fixed_point_convergence :
        Tendsto (fun n => ‖alg.x (n + 1) - T (alg.x (n + 1))‖) atTop (𝓝 0) := by
      sorry

    -- 由于 {xₙ} 有界，存在弱收敛子列
    have h_weak_cluster : ∃ p ∈ D, ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∀ d ∈ D, Tendsto (fun k => ⟪alg.x (φ k) - d, d⟫) atTop (𝓝 ⟪p - d, d⟫) := by
      sorry

    -- p 是 T 的不动点（由 demiclosedness 原理）
    have h_p_fixed : ∃ p ∈ C, ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (fun k => alg.x (φ k)) atTop (𝓝[Set.univ] p) := by
      sorry

    -- 证明整个序列收敛到 p（利用 Opial 引理或类似技巧）
    have h_full_convergence : ∃ p ∈ C, Tendsto alg.x atTop (𝓝 p) := by
      sorry

    -- 最后证明 p 是到 u 的变分不等式的解
    obtain ⟨p, hp_in_C, hp_conv⟩ := h_full_convergence

    use p, hp_in_C, hp_conv

    -- 证明 ⟪u - p, w - p⟫ ≤ 0 对所有 w ∈ C
    intro w hw_in_C
    sorry















  · sorry
