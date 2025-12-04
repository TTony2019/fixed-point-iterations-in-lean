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






open Nonexpansive_operator Filter Topology BigOperators Function TopologicalSpace

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

structure Halpern (T : H → H) where
  x0 : H
  u : H  -- 30.1中的x
  x : ℕ → H
  α : ℕ → ℝ
  update : ∀ k : ℕ, x (k + 1) = (α k) • u + (1 - α k) • (T (x k))
  initial_value : x 0 = x0

#check norm_eq_iInf_iff_real_inner_le_zero--投影的形式

/--
Lemma: For any `ξ ∈ (0,1)`, it holds that `ln(1 - ξ) ≤ -ξ`.
-/
lemma log_ineq
  (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 1) :
  Real.log (1 - ξ) ≤ -ξ := by
  have h1 : 1 - ξ > 0 := by simp [Set.mem_Ioo] at hξ; linarith
  have h2 : 1 - ξ < 1 := by simp [Set.mem_Ioo] at hξ; linarith
  have key := Real.log_le_sub_one_of_pos h1
  linarith

-- 1 - α > 0
lemma one_sub_pos_of_mem_Ioo
  {a : ℝ} (ha : a ∈ Set.Ioo 0 1) : 0 < 1 - a := sub_pos.mpr ha.2

-- 1 - α <1
lemma one_sub_lt_one_of_mem_Ioo
  {a : ℝ} (ha : a ∈ Set.Ioo 0 1) : 1 - a < 1 := by simp [Set.mem_Ioo] at ha; linarith

-- 连乘恒等式
lemma prod_exp_sum
  {T : H → H} (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (m n : ℕ) :
  ∏ x ∈ Finset.Icc m n, (1 - alg.α x) = Real.exp (∑ x ∈ Finset.Icc m n, Real.log (1 - alg.α x)) ∧
    Real.exp (∑ x ∈ Finset.Icc m n, Real.log (1 - alg.α x)) ≤
      Real.exp (∑ x ∈ Finset.Icc m n, -alg.α x) := by
  constructor
  · symm; rw [Real.exp_sum]; apply Finset.prod_congr
    · ext x; simp
    · intro x
      have hk : x ∈ Finset.Icc m n → 1 - alg.α x > 0 := by
        intro hk_mem
        have := h_α_range x
        simp [Set.mem_Ioo] at this; linarith
      intro hx; rw [Real.exp_log]; exact hk hx
  apply Real.exp_le_exp.mpr; apply Finset.sum_le_sum; intro x hx
  exact log_ineq (alg.α x) (h_α_range x)

-- 30.4
lemma infinite_prod_zero
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) (m : ℕ) :
  Tendsto (fun n => ∏ k ∈ Finset.Icc m n, (1 - alg.α k)) atTop (𝓝 0) := by
  have h_prod_eq : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) =
      Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) := by
    intro n hn; exact (prod_exp_sum alg h_α_range m n).1
  have h_exp_le : ∀ n ≥ m, Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) ≤
      Real.exp (∑ k ∈ Finset.Icc m n, -alg.α k) := by
    intro n hn; exact (prod_exp_sum alg h_α_range m n).2
  have h_prod_le : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) ≤
      Real.exp (- ∑ k ∈ Finset.Icc m n, alg.α k) := by
    intro n hn; rw [h_prod_eq n hn]; convert h_exp_le n hn using 2; simp [Finset.sum_neg_distrib]
  have h_sum_icc_inf : Tendsto (fun n => ∑ k ∈ Finset.Icc m n, alg.α k) atTop atTop := by
    have h_decomp : ∀ n ≥ m, ∑ k ∈ Finset.range (n + 1), alg.α k =
        (∑ k ∈ Finset.range m, alg.α k) + (∑ k ∈ Finset.Icc m n, alg.α k) := by
      intro n hn; rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_succ_of_le hn)]; congr 1
    let C := ∑ k ∈ Finset.range m, alg.α k
    have h_eq : ∀ n ≥ m, ∑ k ∈ Finset.Icc m n, alg.α k =
        (∑ k ∈ Finset.range (n + 1), alg.α k) - C := by
      intro n hn; have := h_decomp n hn; linarith
    -- 现在证明收敛性
    rw [tendsto_atTop_atTop]; intro b
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp h_α_sum_inf) (b + C)
    use max m N; intro n hn
    have hn_m : n ≥ m := le_of_max_le_left hn; have hn_N : n ≥ N := le_of_max_le_right hn
    rw [h_eq n hn_m]
    have : ∑ k ∈ Finset.range (n + 1), alg.α k ≥ b + C := by apply hN; omega
    linarith
  have h_neg_sum : Tendsto (fun n => -∑ k ∈ Finset.Icc m n, alg.α k) atTop atBot := by simpa
  have h_exp_to_zero : Tendsto (fun n => Real.exp
    (- ∑ k ∈ Finset.Icc m n, alg.α k)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h_neg_sum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_exp_to_zero ?_ ?_
  · intro n; apply Finset.prod_nonneg; intro k _
    have := h_α_range k
    simp [Set.mem_Ioo] at this; linarith
  · intro n
    by_cases hn : n ≥ m
    · exact h_prod_le n hn
    · simp [Finset.Icc_eq_empty_of_lt (Nat.not_le.mp hn)]

-- 4.23(i)
-- 拟非扩张映射的不动点集刻画
lemma quasinonexpansive_fixedPoint_characterization
  {D : Set H} (hD_nonempty : D.Nonempty) {T : H → H} (hT_quasi : QuasiNonexpansiveOn T D)
  : Fix T ∩ D = ⋂ x ∈ D, {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} := by
  ext y; constructor
  · intro ⟨hy_fix, hy_D⟩; simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro x hx
    constructor
    · exact hy_D
    · have h_fix : IsFixedPt T y := hy_fix
      have hy_in_fix' : y ∈ Fix' T D := ⟨hy_D, h_fix⟩
      have h_quasi := hT_quasi hx hy_in_fix'
      have h_norm_sq : ‖T x - y‖^2 ≤ ‖x - y‖^2 :=
        sq_le_sq' (by linarith [norm_nonneg (T x - y)]) h_quasi
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h_norm_sq
      have eq1 : inner ℝ (T x - y) (T x - y) = inner ℝ (T x - x) (T x - x) +
        2 * inner ℝ (T x - x) (x - y) + inner ℝ (x - y) (x - y) := by
        rw [← sub_add_sub_cancel (T x) y x]; simp [inner_sub_left, inner_sub_right, real_inner_comm]
        ring_nf
      rw [eq1] at h_norm_sq
      have eq2 : inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)
        + 2 * inner ℝ (T x - x) (T x - y) ≤ 0 := by calc
          _ = inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - y) := by
            simp [inner_sub_left, inner_sub_right, real_inner_comm]; ring_nf
          _ ≤ 0 := by linarith
      calc
        _ = -inner ℝ (y - T x) (T x - x) := by rw [inner_sub_right, inner_sub_right]; ring
        _ ≤ -(inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)) / 2 := by
          have h1 : inner ℝ (T x - x) (T x - y) = -inner ℝ (T x - x) (y - T x) := by
            simp only [inner_sub_right]; ring
          rw [real_inner_comm (T x - x) (y - T x), ← h1]
          nlinarith [eq2]
        _ = (1/2) * ‖T x - x‖^2 := by
          rw [real_inner_self_eq_norm_sq, mul_comm]
          have h_neg : inner ℝ (T x - x) (x - T x) = - inner ℝ (T x - x) (T x - x) := by
            simp [inner_sub_right]
          rw [h_neg]; simp; rw [real_inner_self_eq_norm_sq]; ring_nf
  · intro hy
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
    constructor
    · obtain ⟨x0, hx0⟩ := hD_nonempty; have hy_D := (hy x0 hx0).1; have h_y := (hy y hy_D).2
      have h_eq : inner ℝ (y - T y) (y - T y) = ‖y - T y‖ ^ 2 := real_inner_self_eq_norm_sq _
      have h_sym : ‖y - T y‖ ^ 2 = ‖T y - y‖ ^ 2 := by rw [norm_sub_rev]
      rw [h_eq, h_sym] at h_y
      have : (1/2) * ‖T y - y‖ ^ 2 ≤ 0 := by linarith
      have h_zero : ‖T y - y‖ ^ 2 = 0 := by
        have h_nonneg : 0 ≤ ‖T y - y‖ ^ 2 := sq_nonneg _; linarith
      exact eq_of_norm_sub_eq_zero (sq_eq_zero_iff.mp h_zero)
    · obtain ⟨x0, hx0⟩ := hD_nonempty
      exact (hy x0 hx0).1

-- 辅助引理1：半空间是闭集
lemma halfspace_is_closed
  (a b : H) (c : ℝ) : IsClosed {x : H | ⟪x - a, b⟫ ≤ c} := by
  have : {x : H | ⟪x - a, b⟫ ≤ c} = (fun x => ⟪x - a, b⟫) ⁻¹' Set.Iic c := by
    ext x; simp [Set.mem_Iic]
  rw [this]; apply IsClosed.preimage ?_ isClosed_Iic
  apply Continuous.inner (continuous_id.sub continuous_const) (continuous_const)

-- 辅助引理2：半空间是凸集
lemma halfspace_is_convex
  (a b : H) (c : ℝ) : Convex ℝ {x : H | ⟪x - a, b⟫ ≤ c} := by
  intro x hx y hy t1 t2 ht1 ht2 ht; simp at hx hy ⊢; calc
    _ = ⟪t1 • x + t2 • y - (t1 • a + t2 • a), b⟫ := by congr 1; rw [← add_smul]; simp [ht]
    _ = ⟪t1 • (x - a) + t2 • (y - a), b⟫ := by
      congr 1; simp [smul_sub, sub_add_eq_sub_sub, add_sub, add_comm]
    _ = t1 * ⟪x - a, b⟫ + t2 * ⟪y - a, b⟫ := by
      rw [inner_add_left, inner_smul_left, inner_smul_left]; norm_cast
    _ ≤ t1 * c + t2 * c := add_le_add
      (mul_le_mul_of_nonneg_left hx ht1) (mul_le_mul_of_nonneg_left hy (by linarith))
    _ = c := by rw [← add_mul]; simp [ht]

-- 主引理：交集中每个集合都是闭凸集
lemma intersection_set_is_closed_convex
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : H → H} (x : H) :
  IsClosed {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} ∧
  Convex ℝ {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} := by
  constructor
  · exact IsClosed.inter hD_closed (halfspace_is_closed (T x) (x - T x) ((1/2) * ‖T x - x‖^2))
  · exact Convex.inter hD_convex (halfspace_is_convex (T x) (x - T x) ((1/2) * ‖T x - x‖^2))

-- prop 4.23(ii)
-- 推论：不动点集的闭凸性
lemma quasinonexpansive_fixedPoint_closed_convex
  {C D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_quasi : QuasiNonexpansiveOn T D) (hC : C = Fix T ∩ D)
  : IsClosed C ∧ Convex ℝ C := by
  rw [hC, quasinonexpansive_fixedPoint_characterization hD_nonempty hT_quasi]
  constructor
  · exact isClosed_biInter fun x _ => (intersection_set_is_closed_convex hD_closed hD_convex x).1
  · exact convex_iInter₂ fun x _ => (intersection_set_is_closed_convex hD_closed hD_convex x).2

-- quasi可以推出nonexpansive
omit [InnerProductSpace ℝ H] in
lemma nonexpansive_leadsto_quasinonexpansive
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D) :
    QuasiNonexpansiveOn T D := by
  intro x hx y hy
  rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp; rw [Fix'] at hy; rcases hy with ⟨hyD,hyFix⟩
  have h_edist := hT_nonexp hx hyD; simp only [ENNReal.coe_one, one_mul] at h_edist
  rw [hyFix, edist_dist, edist_dist] at h_edist
  have h_dist : dist (T x) y ≤ dist x y := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h_edist
  rw [dist_eq_norm, dist_eq_norm] at h_dist
  exact h_dist

-- ln ∏ ≤ - Σ
lemma log_prod_one_sub_le_neg_sum
  {α : ℕ → ℝ} (m n : ℕ) (hα : ∀ k, α k ∈ Set.Ioo 0 1) :
    Real.log (∏ k ∈ Finset.Icc m n, (1 - α (k + 1))) ≤ - ∑ k ∈ Finset.Icc m n, α (k + 1) := by
  have hpos : ∀ k ∈ Finset.Icc m n, 0 < (1 - α (k + 1)) := by
    intro k hk; exact one_sub_pos_of_mem_Ioo (hα (k + 1))
  have hlog : Real.log (∏ k ∈ Finset.Icc m n, (1 - α (k + 1)))
    = ∑ k ∈ Finset.Icc m n, Real.log (1 - α (k + 1)) := by
      apply Real.log_prod _ _; intro k hk; exact Ne.symm (ne_of_lt (hpos k hk))
  have hterm : ∀ k ∈ Finset.Icc m n, Real.log (1 - α (k + 1)) ≤ - α (k + 1) := by
    intro k hk; exact log_ineq (α (k+1)) (hα (k+1))
  simpa [hlog] using Finset.sum_le_sum hterm

-- ∀ z ∈ C, ‖T(x n) - z‖ ≤ ‖x n - z‖ ∧ ‖x n - z‖ ≤ ‖x0 - z‖
lemma halpern_distance_monotone
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (alg : Halpern T) (halg_x0 : alg.x0 ∈ D) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (coincidence : alg.u = alg.x0) :
  ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖ := by
  have hT_quasinonexp := nonexpansive_leadsto_quasinonexpansive hT_nonexp
  intro z hzC n
  induction n with
  | zero =>
    constructor
    · have ⟨hz_fix, hz_D⟩ : z ∈ Fix T ∩ D := by convert hzC; exact hC.symm
      have hz_in_fix' : z ∈ Fix' T D := ⟨hz_D, hz_fix⟩
      rw [alg.initial_value]
      exact hT_quasinonexp halg_x0 hz_in_fix'
    · rw [alg.initial_value]
  | succ k ih =>
    constructor
    · have ⟨hz_fix, hz_D⟩ :z ∈ Fix T ∩ D := by convert hzC; exact hC.symm
      have hz_in_fix' : z ∈ Fix' T D := ⟨hz_D, hz_fix⟩
      exact hT_quasinonexp (halg_x_in_D (k+1)) hz_in_fix'
    · rw [alg.update]; calc
        _ = ‖alg.α k • (alg.u - z) + (1 - alg.α k) • (T (alg.x k) - z)‖ := by
              congr 1; simp [smul_sub, sub_smul, add_sub, add_comm]
        _ ≤ alg.α k * ‖alg.u - z‖ + (1 - alg.α k) * ‖T (alg.x k) - z‖ := by
              apply norm_add_le_of_le
              · simp [norm_smul]; gcongr; rw [abs_of_pos (h_α_range k).1]
              · simp [norm_smul]; gcongr; rw [abs_of_pos (one_sub_pos_of_mem_Ioo (h_α_range k))]
        _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x k - z‖ := by
              rw [← coincidence]; gcongr
              · linarith [one_sub_pos_of_mem_Ioo (h_α_range k)]
              · exact ih.1
        _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x0 - z‖ := by
              gcongr
              · linarith [one_sub_pos_of_mem_Ioo (h_α_range k)]
              · exact ih.2
        _ = ‖alg.x0 - z‖ := by ring

-- μ is bounded
lemma halpern_mu_bound
  {T : H → H} (alg : Halpern T) {y : H}
  -- 三个前提：差分、Tx 偏差、序列均有统一上界
  (h_diff_bounded : ∃ M1, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M1)
  (h_Tx_bounded : ∃ M2, ∀ n, ‖T (alg.x n) - y‖ ≤ M2)
  (h_seq_bounded : ∃ M3, ∀ n, ‖alg.x n - y‖ ≤ M3) :
  ∃ μ : ℝ, μ > 0 ∧ (∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ) ∧ (∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ) := by
  -- 取各自的上界
  obtain ⟨M1, hM1⟩ := h_diff_bounded
  obtain ⟨M2, hM2⟩ := h_Tx_bounded
  obtain ⟨M3, hM3⟩ := h_seq_bounded
  -- 统一的 μ
  let μ := M1 + M2 + M3 + ‖alg.u - y‖ + 1; refine ⟨μ, ?hpos, ?hstep, ?huTx⟩
  -- 证明 μ > 0
  · simp [μ]; have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _
    linarith [(le_trans (norm_nonneg _) (hM1 0)), (le_trans (norm_nonneg _) (hM2 0)),
      (le_trans (norm_nonneg _) (hM3 0))]
  -- 证明 ‖x_{n+1} - x_n‖ ≤ μ
  · intro n; calc
      _ = ‖(alg.x (n + 1) - T (alg.x n)) + (T (alg.x n) - alg.x n)‖ := by abel_nf
      _ ≤ ‖alg.x (n + 1) - T (alg.x n)‖ + ‖T (alg.x n) - alg.x n‖ := by
        apply norm_add_le
      _ ≤ M1 + ‖T (alg.x n) - alg.x n‖ := by gcongr; exact hM1 n
      _ = M1 + ‖(T (alg.x n) - y) + (y - alg.x n)‖ := by abel_nf
      _ ≤ M1 + (‖T (alg.x n) - y‖ + ‖y - alg.x n‖) := by apply add_le_add_left; apply norm_add_le
      _ ≤ M1 + (M2 + M3) := by
        gcongr
        · exact hM2 n
        · rw [norm_sub_rev]; exact hM3 n
      _ ≤ μ := by
        simp [μ]; rw [← add_assoc]; have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _; linarith
  -- 证明 ‖u - T x_n‖ ≤ μ
  · intro n; calc
      _ = ‖(alg.u - y) + (y - T (alg.x n))‖ := by abel_nf
      _ ≤ ‖alg.u - y‖ + ‖y - T (alg.x n)‖ := by  apply norm_add_le
      _ ≤ ‖alg.u - y‖ + M2 := by gcongr; rw [norm_sub_rev]; exact hM2 n
      _ ≤ μ := by
        simp [μ]
        linarith [μ, (le_trans (norm_nonneg _) (hM1 0)), (le_trans (norm_nonneg _) (hM3 0))]

-- ‖x(n+2)-x(n+1)‖≤μ* Σ|λ(n+1)-λn| +(1-λ(n+1))*∏‖x(n+1)-x(n)‖
omit [InnerProductSpace ℝ H] in
lemma halpern_telescoping_bound
  {x : ℕ → H} {α : ℕ → ℝ} {μ : ℝ} (hμ_nonneg : 0 ≤ μ)
  (hα_range : ∀ n, α n ∈ Set.Ioo 0 1)
  (h_norm_diff_ineq : ∀ n, ‖x (n + 2) - x (n + 1)‖ ≤ μ *
    |α (n + 1) - α n| + (1 - α (n + 1)) * ‖x (n + 1) - x n‖)
  : ∀ n m, m ≤ n → ‖x (n + 2) - x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n,
    |α (k + 1) - α k|) + ‖x (m + 1) - x m‖ * (∏ k ∈ Finset.Icc m n, (1 - α (k + 1))) := by
  intro n m hmn; obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  -- Induction on the length k of the segment [m, m+k].
  induction k with
  | zero =>
    simp; linarith [h_norm_diff_ineq m]
  | succ k ih => calc
      ‖x (m + (k + 1) + 2) - x (m + (k + 1) + 1)‖ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))|
        + (1 - α (m + (k + 1) + 1)) * ‖x (m + (k + 1) + 1) - x (m + (k + 1))‖ :=
          h_norm_diff_ineq (m + (k + 1))
      _ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))| + (1 - α (m + (k + 1) + 1)) *
        (μ * (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|) + ‖x (m + 1) - x m‖ *
          (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1)))) := by
            gcongr
            · linarith [one_sub_pos_of_mem_Ioo (hα_range (m + (k + 1) + 1))]
            · exact ih (by linarith)
      _ = μ * |α (m + (k + 1) + 1) - α (m + (k + 1))| + (1 - α (m + (k + 1) + 1)) * μ *
        (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|) + (1 - α (m + (k + 1) + 1)) *
          ‖x (m + 1) - x m‖ * (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1))) := by ring
      _ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))| + μ * (∑ l ∈ Finset.Icc m (m + k),
        |α (l + 1) - α l|) + (1 - α (m + (k + 1) + 1)) * ‖x (m + 1) - x m‖ *
          (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1))) := by
            gcongr
            · apply Finset.sum_nonneg; intro l _; exact abs_nonneg _
            · nth_rewrite 2[← one_mul μ]; apply mul_le_mul_of_nonneg_right
              · simp; linarith [(hα_range (m + (k + 1) + 1)).1]
              · exact hμ_nonneg
      _ = μ * (∑ l ∈ Finset.Icc m (m + (k + 1)), |α (l + 1) - α l|) + ‖x (m + 1) - x m‖
        * (∏ l ∈ Finset.Icc m (m + (k + 1)), (1 - α (l + 1))) := by
          rw [← add_assoc, ← Nat.succ_eq_add_one (m+k), Finset.sum_Icc_succ_top,
            Finset.prod_Icc_succ_top, Nat.succ_eq_add_one]
          · ring_nf
          repeat linarith

-- x(n+2)-x(n+1)=λ(n+1)-λn)•(u-T xn)+(1-λ(n+1))•(T x(n+1)-T xn)
lemma halpern_diff_formula
  {T : H → H} (alg : Halpern T)
  : ∀ n, alg.x (n + 2) - alg.x (n + 1) = (alg.α (n + 1) - alg.α n) •
    (alg.u - T (alg.x n)) + (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n)) := by
  intro n; simp [alg.update]; calc
    _ = (alg.α (n + 1) • alg.u - alg.α n • alg.u) + ((1 - alg.α (n + 1)) •
      T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n)) - (1 - alg.α n) • T (alg.x n)) := by abel
    _ = (alg.α (n + 1) - alg.α n) • alg.u + ((1 - alg.α (n + 1)) • T (alg.α n • alg.u +
      (1 - alg.α n) • T (alg.x n)) - (1 - alg.α n) • T (alg.x n)) := by simp [sub_smul]
    _ = (alg.α (n + 1) - alg.α n) • alg.u - (alg.α (n + 1) - alg.α n) • T (alg.x n) +
      (1 - alg.α (n + 1)) • (T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n)) - T (alg.x n)) := by
        simp [sub_smul, add_sub, add_comm, smul_sub]; abel_nf
    _ = (alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n)) + (1 - alg.α (n + 1)) •
      (T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n)) - T (alg.x n)) := by simp [smul_sub]

-- ‖x(n+2)-x(n+1)‖≤μ*|λ(n+1)-λn|+(1-λ(n+1))‖x(n+1)-x(n)‖
lemma halpern_norm_diff_ineq
  {T : H → H} (alg : Halpern T) {D : Set H} (hT_nonexp : NonexpansiveOn T D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_diff_formula : ∀ n, alg.x (n + 2) - alg.x (n + 1) = (alg.α (n + 1) - alg.α n) •
    (alg.u - T (alg.x n)) + (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n)))
  (μ : ℝ) (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| + (1 - alg.α (n + 1)) *
    ‖alg.x (n + 1) - alg.x n‖ := by
  intro n; rw [h_diff_formula n]; calc
    _ ≤ ‖(alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n))‖
      + ‖(1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n))‖ := by apply norm_add_le
    _ = |alg.α (n + 1) - alg.α n| * ‖alg.u - T (alg.x n)‖
      + |1 - alg.α (n + 1)| * ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by simp [norm_smul]
    _ = |alg.α (n + 1) - alg.α n| * ‖alg.u - T (alg.x n)‖
      + (1 - alg.α (n + 1)) * ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by
          rw [abs_of_pos (one_sub_pos_of_mem_Ioo (h_α_range (n + 1)))]
    _ ≤ |alg.α (n + 1) - alg.α n| * μ + (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
      gcongr
      · exact hμ_Tx_bound n
      · linarith [(h_α_range (n + 1)).2]
      have hT_nonexp' := hT_nonexp (halg_x_in_D (n + 1)) (halg_x_in_D n)
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm] at hT_nonexp'
      have h_nonneg : 0 ≤ ‖alg.x (n + 1) - alg.x n‖ := norm_nonneg _
      simp at hT_nonexp'; apply (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp; simp; exact hT_nonexp'
    _ = μ * |alg.α (n + 1) - alg.α n| + (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
      rw [mul_comm]

-- ‖x(n+2)-x(n+1)‖≤μ* Σ|λ(n+1)-λn| +μ *∏‖x(n+1)-x(n)‖
lemma halpern_telescoping_ineq
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (μ : ℝ) (hμ_pos : μ > 0) (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  : ∀ n m, m ≤ n → ‖alg.x (n+2) - alg.x (n+1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n,
    |alg.α (k+1) - alg.α k|) + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))) := by
    intro n m hmn; have hμ_nonneg : 0 ≤ μ := le_of_lt hμ_pos; calc
      _ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k+1) - alg.α k|) + ‖alg.x (m+1) - alg.x m‖ *
        (∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))) := by
          apply halpern_telescoping_bound hμ_nonneg h_α_range h_norm_diff_ineq; exact hmn
      _ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k+1) - alg.α k|) + μ *
        (∏ k ∈ Finset.Icc m n, (1 - alg.α (k+1))) := by
          apply add_le_add_left; apply mul_le_mul_of_nonneg_right
          · exact hμ_x_bound m
          · apply Finset.prod_nonneg; intro k hk
            linarith [one_sub_pos_of_mem_Ioo (h_α_range (k+1))]

-- lim ‖x(n+2)-x(n+1)‖≤μ* Σ|λ(n+1)-λn| +μ *∏‖x(n+1)-x(n)‖
lemma halpern_telescoping_limit
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (μ : ℝ)
  (hμ_pos : μ > 0) (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  : ∀ᶠ n in atTop, ∀ᶠ m in atTop, m ≤ n →
    ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|)
      + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
  have hμ_nonneg := le_of_lt hμ_pos
  apply eventually_atTop.2; use 0; intro n hn; apply eventually_atTop.2; use 0; intro m hm hmn
  exact halpern_telescoping_ineq alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq n m hmn

-- ∑k∈ Finset.Icc m n, fk +∑'k,f(k+n+1)=∑'k,f(k+m)
lemma sum_icc_add_tsum_eq_tsum_add
  {f : ℕ → ℝ} (hf : Summable f) (m n : ℕ) (hmn : m ≤ n) :
  ∑ k ∈ Finset.Icc m n, f k + ∑' k, f (k + n + 1) = ∑' k, f (k + m) := by
  -- 首先，分解 ∑' k, f (k + m) 为三部分
  have h_decomp : ∑' k, f (k + m) = ∑ k ∈ Finset.Icc m n, f k + ∑' k, f (k + n + 1) := by
    have h_split : ∑' k : ℕ, f (k + m) =
        ∑ k ∈ Finset.range (n - m + 1), f (k + m) + ∑' k : ℕ, f (k + n + 1) := by
      have hf_shift : Summable (fun k => f (k + m)) := by
        apply hf.comp_injective; intro a b hab; linarith
      rw [← Summable.sum_add_tsum_nat_add]
      · congr; ext k; ring_nf; congr 1; rw [Nat.Simproc.add_eq_add_le (1 + k + (n - m)) (1 + k) hmn]
      · assumption
    have h_finset_eq : ∑ k ∈ Finset.range (n - m + 1), f (k + m) = ∑ k ∈ Finset.Icc m n, f k := by
      trans ∑ i ∈ Finset.Icc m n, f i
      · rw [Finset.sum_bij (fun k _ => k + m)]
        · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
        · intro k₁ k₂ _ _ heq; omega
        · intro k hk; use k - m; simp; constructor; repeat simp at hk; omega
        · simp
      · simp
    rw [h_split, h_finset_eq]
  rw [h_decomp]

-- lim_m n → ∞, μ * ∑ k∈Finset.Icc m n,|λ(k+1)-λk| =0
lemma halpern_sum_tail_tendsto_zero
  {T : H → H} (alg : Halpern T) (μ : ℝ) (hμ_pos : μ > 0)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * (∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k|) < ε := by
  intros ε ε_pos; let f := fun n => |alg.α (n + 1) - alg.α n|
  have hf := h_α_diff_finite
  have h_sum_tail : Tendsto (fun m => ∑' k : ℕ, f (k + m)) atTop (𝓝 0) := by
    exact tendsto_sum_nat_add f
  have h_eventually_tail : ∀ᶠ m in atTop, ∑' k : ℕ, f (k + m) < ε / μ := by
    apply (tendsto_order.1 h_sum_tail).2 (ε / μ) (by positivity)
  have : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * ∑ k ∈ Finset.Icc m n, f k < ε := by
    filter_upwards [h_eventually_tail] with m hm; apply eventually_atTop.2; use m
    intro n hmn hmn'
    have h_le : ∑ k ∈ Finset.Icc m n, f k ≤ ∑' k : ℕ, f (k + m) := by calc
        _ ≤ ∑ k ∈ Finset.Icc m n, f k + ∑' (k : ℕ), f (k + n + 1) := by
          simp [f]; apply tsum_nonneg; intro k; exact abs_nonneg _
        _ = ∑' (k : ℕ), f (k + m) := sum_icc_add_tsum_eq_tsum_add h_α_diff_finite m n hmn
    calc
      _ ≤ μ * ∑' k : ℕ, f (k + m) := by apply mul_le_mul_of_nonneg_left h_le (le_of_lt hμ_pos)
      _ < μ * (ε / μ) := mul_lt_mul_of_pos_left hm hμ_pos
      _ = ε := by field_simp [ne_of_gt hμ_pos]
  exact this

-- ∏ k ∈ Finset.Icc m n, (1 - α (k + 1)) = ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - α k)
lemma h_reindex
  {T : H → H} (alg : Halpern T) :∀ m : ℕ, (fun n ↦ ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)))
      = (fun n ↦ ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k)) := by
    intro m; ext n; by_cases hn : n ≥ m
    · let g := fun k => k + 1; let s := Finset.Icc m n; let f := fun k => 1 - alg.α k
      have hf : Set.InjOn g ↑s := by
        intros x hx y hy hxy; exact Nat.succ_inj.mp hxy
      rw [← Finset.prod_image (s := s) (f := f) (g := g) hf]; congr 1; ext k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨x, hx, rfl⟩; constructor
        repeat simp [g, s] at *; rcases hx with ⟨hxm, hxn⟩; linarith
      · intro hk; use k - 1; constructor
        · rcases hk with ⟨hk1, hk2⟩; simp [s, g] at *
          constructor
          · exact Nat.le_sub_one_of_lt hk1
          · linarith
        rcases hk with ⟨hk1, hk2⟩; simp [s, g] at *; refine Nat.sub_add_cancel ?_; linarith
    · have h_empty1 : Finset.Icc m n = ∅ := by
        ext x; simp [Finset.mem_Icc]; simp at *; intro hx; linarith
      have h_empty2 : Finset.Icc (m + 1) (n + 1) = ∅ := by
        ext x; simp [Finset.mem_Icc]; simp at *; intro hx; linarith
      simp [h_empty1, h_empty2, Finset.prod_empty]

-- lim_n → ∞, μ * ∏ k∈Finset.Icc m n,(1-λ(k+1))=0
lemma halpern_prod_tail_tendsto_zero
  {T : H → H} (alg : Halpern T) (μ : ℝ) (hμ_pos : μ > 0) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) : ∀ ε > 0, ∀ m : ℕ,
    ∀ᶠ n in atTop, m ≤ n → μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
  intros ε hε m
  have h_prod_tendsto : Tendsto (fun n => ∏ k ∈ Finset.Icc
    (m + 1) (n + 1), (1 - alg.α k)) atTop (𝓝 0) := by
    let f : ℕ → ℝ := fun n => ∏ k ∈ Finset.Icc (m + 1) n, (1 - alg.α k)
    have h_f_tendsto : Tendsto f atTop (𝓝 0) := infinite_prod_zero alg h_α_range h_α_sum_inf (m + 1)
    apply h_f_tendsto.comp; exact tendsto_add_atTop_nat 1

  have h_eventually : ∀ᶠ n in atTop, ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k) < ε / μ := by
    rw [Metric.tendsto_atTop] at h_prod_tendsto
    obtain ⟨N, hN⟩ := h_prod_tendsto (ε / μ) (by positivity)
    rw [eventually_atTop]; use N; intro n hn
    have := hN n hn; rw [Real.dist_eq] at this; simp at this; exact lt_of_abs_lt this

  rw [eventually_atTop]; obtain ⟨N, hN⟩ := (eventually_atTop).mp h_eventually
  use max m N; intro n hn hmn; have hn_N : n ≥ N := le_of_max_le_right hn; calc
    _ = μ * ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k) := by
      congr 1; exact congrFun (h_reindex alg m) n
    _ < μ * (ε / μ) := mul_lt_mul_of_pos_left (hN n hn_N) hμ_pos
    _ = ε := by field_simp [ne_of_gt hμ_pos]

-- 相邻差序列收敛到零
omit [InnerProductSpace ℝ H] in
lemma adjacent_diff_from_shifted
  {f : ℕ → H} : Tendsto (fun n => (f (n + 2) - f (n + 1))) atTop (𝓝 0) →
  Tendsto (fun n => (f (n + 1) - f n)) atTop (𝓝 0) := by
  intro h
  have : (fun n ↦ f (n + 1) - f n) ∘ (fun n ↦ n + 1) = (fun n ↦ f (n + 2) - f (n + 1)) := by
    funext n; simp only [Function.comp_apply]
  rw [← this] at h; exact (tendsto_add_atTop_iff_nat 1).mp h

-- 让 n 和 m 趋于 +∞，得到 lim xn+1−xn → 0
lemma halpern_diff_limit
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (μ : ℝ)
  (hμ_pos : μ > 0) (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  (h_telescoping : ∀ n m, m ≤ n → ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k|) + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))))
  : Tendsto (fun n => (alg.x (n + 1) - alg.x n)) atTop (𝓝 0) := by
  have sq_lim_le := halpern_telescoping_limit alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq
  -- 让 n 和 m 趋于 +∞，得到 lim μ ∏ (1 - λₖ₊₁) = 0
  have sq_lim2 := halpern_prod_tail_tendsto_zero alg μ hμ_pos h_α_range h_α_sum_inf
  have sq_lim3: ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * ∏ k ∈ Finset.Icc m n,
    (1 - alg.α (k + 1)) < ε := by
    intro ε ε_pos; exact Eventually.mono sq_lim_le fun x a ↦ sq_lim2 ε ε_pos x
  have sq_lim1 := halpern_sum_tail_tendsto_zero alg μ hμ_pos h_α_diff_finite
  have sq_lim4 : ∀ ε > 0, ∀ᶠ (m : ℕ) (n : ℕ) in atTop, m ≤ n → μ * ∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k| + μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
    intros ε ε_pos
    have h1 := sq_lim1 (ε/2) (by linarith); have h2 := sq_lim3 (ε/2) (by linarith)
    filter_upwards [h1, h2] with N1 h11 h22; filter_upwards [h11, h22] with N2 h111 h222
    intro hN1N2; calc
        _ < ε/2 + ε/2 := add_lt_add (h111 hN1N2) (h222 hN1N2)
        _ = ε := by ring
  have sq_lim5 : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n →
    ‖alg.x (n + 2) - alg.x (n + 1)‖ < ε := by
    intro ε ε_pos
    filter_upwards [sq_lim4 ε ε_pos] with N1 h1; filter_upwards [h1] with N2 h2; intro hN1N2; calc
      _ ≤ μ * ∑ k ∈ Finset.Icc N1 N2, |alg.α (k + 1) - alg.α k| +
        μ * ∏ k ∈ Finset.Icc N1 N2, (1 - alg.α (k + 1)) := by apply h_telescoping N2 N1 hN1N2
      _ < ε := h2 hN1N2
  have sq_lim5' : ∀ ε > 0, ∀ᶠ n in atTop, ‖alg.x (n + 2) - alg.x (n + 1)‖ < ε := by
    intro ε ε_pos; have h_eventually := sq_lim5 ε ε_pos; rw [eventually_atTop] at h_eventually
    obtain ⟨N, hN⟩ := h_eventually; specialize hN N (le_refl N); rw [eventually_atTop] at hN ⊢
    rcases hN with ⟨a, ha⟩; use max N a; intro n hn
    apply (ha n (le_of_max_le_right hn) (le_of_max_le_left hn))
  have sq_lim6 : Tendsto (fun n => ‖alg.x (n + 2) - alg.x (n + 1)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]; intros ε ε_pos
    obtain ⟨N, hN⟩ := (eventually_atTop).mp (sq_lim5' ε ε_pos); use N; intro n hn
    rw [Real.dist_eq]; simp; exact hN n hn
  have sq_lim7 : Tendsto (fun n => (alg.x (n + 2) - alg.x (n + 1))) atTop (𝓝 0) :=
    ((Iff.symm tendsto_zero_iff_norm_tendsto_zero).1 sq_lim6)
  exact adjacent_diff_from_shifted sq_lim7

-- lim (xₙ - Txₙ) → 0
lemma halpern_x_sub_Tx_tendsto_zero
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0)) (μ : ℝ) (hμ_pos : μ > 0)
  (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  (h_diff_limit : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (𝓝 0))
  : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (𝓝 0) := by
  -- 步骤1：建立关键等式
  have eq1 : ∀ n, alg.x (n + 1) - alg.x n = alg.α n • (alg.u - T (alg.x n)) +
    (T (alg.x n) - alg.x n) := by intro n; rw [alg.update]; simp [smul_sub, sub_smul]; abel

  -- 步骤2：证明 α_n * ‖u - T(x_n)‖ → 0
  have h1 : Tendsto (fun n ↦ alg.α n * ‖alg.u - T (alg.x n)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at ⊢ h_α_limit; intro ε ε_pos
    obtain ⟨N, hN⟩ := h_α_limit (ε / μ) (by positivity); use N; intro n hn; rw [Real.dist_eq]
    simp only [sub_zero]
    have h_α_small : |alg.α n| < ε / μ := by
      have := hN n hn; rw [Real.dist_eq] at this; simp at this; exact this
    have h_α_nonneg : 0 ≤ alg.α n := by linarith [(h_α_range n).1]
    rw [abs_of_nonneg h_α_nonneg] at h_α_small; calc
      _ = alg.α n * ‖alg.u - T (alg.x n)‖ := by simp [abs_mul, abs_of_nonneg h_α_nonneg]
      _ ≤ alg.α n * μ := by gcongr; exact hμ_Tx_bound n
      _ < (ε / μ) * μ := mul_lt_mul_of_pos_right h_α_small hμ_pos
      _ = ε := by field_simp [ne_of_gt hμ_pos]

  -- 步骤3：证明 α_n • (u - T(x_n)) → 0
  have h2 : Tendsto (fun n ↦ alg.α n • (alg.u - T (alg.x n))) atTop (𝓝 0) := by
    have h_norm_bound : Tendsto (fun n ↦ ‖alg.α n • (alg.u - T (alg.x n))‖) atTop (𝓝 0) := by
      have : Tendsto (fun n ↦ |alg.α n| * ‖alg.u - T (alg.x n)‖) atTop (𝓝 0) := by
        convert h1 using 1; ext n; congr; simp; linarith [(h_α_range n).1]
      convert this using 1; funext n; rw [norm_smul]; simp
    rw [Metric.tendsto_atTop] at h_norm_bound ⊢
    intros ε ε_pos; obtain ⟨N, hN⟩ := h_norm_bound ε ε_pos; use N; intros n hn
    specialize hN n hn; rw [dist_eq_norm]; simp at hN; simp; exact hN
  have h_key : ∀ n, alg.x n - T (alg.x n) = alg.α n • (alg.u - T (alg.x n)) - (alg.x (n + 1)
    - alg.x n) := by intro n; simp [eq1 n]
  convert Tendsto.sub h2 h_diff_limit using 1
  · funext n; exact h_key n
  · simp

#check norm_eq_iInf_iff_real_inner_le_zero
#check exists_norm_eq_iInf_of_complete_convex
#check TopologicalSpace.SeparableSpace

-- Lemma 2.45: 有界序列存在弱收敛子序列
lemma bounded_seq_weakly_convergent_subsequence [SeparableSpace H] [CompleteSpace H]
  (x : ℕ → H) (h_bounded : ∃ M, ∀ n, ‖x n‖ ≤ M) :
  ∃ (φ : ℕ → ℕ) (p : H), (∀ m n, m < n → φ m < φ n) ∧ WeakConverge (x ∘ φ) p := by
  -- 从 ∃ M, ∀ n, ‖x n‖ ≤ M 构造 IsBounded
  obtain ⟨M, hM⟩ := h_bounded
  have h_is_bounded : Bornology.IsBounded (Set.range fun n => ‖x n‖) := by
    rw [Bornology.IsBounded]; use 2 * M; intro m hm n hn; simp at *
    rcases hm with ⟨k, rfl⟩; rcases hn with ⟨l, rfl⟩
    calc
      _ ≤ ‖x k‖ + ‖x l‖ :=
        abs_sub_le_of_nonneg_of_le (norm_nonneg _) (by simp) (norm_nonneg _) (by simp)
      _ ≤ M + M := add_le_add (hM k) (hM l)
      _ = 2 * M := by ring
  obtain ⟨a, φ, h_strict_mono, h_weak_conv⟩ :=
    bounded_seq_has_weakly_converge_subseq_separable x h_is_bounded
  have h_phi_explicit : ∀ m n, m < n → φ m < φ n := fun m n a ↦ h_strict_mono a
  exact ⟨φ, a, h_phi_explicit, h_weak_conv⟩

-- 投影点定义
theorem existence_of_projection_point [CompleteSpace H]
  (C : Set H) (hC1 : C.Nonempty) (hC2 : Convex ℝ C) (hC3 : IsClosed C) (x : H) :
  ∃ u ∈ C, ‖x - u‖ = ⨅ w : C, ‖x - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hC1 (IsClosed.isComplete hC3) hC2 x

-- 投影点性质
theorem proj_pt_inner_le_zero
  (x PxC : H) (C : Set H) (hC2 : Convex ℝ C) (hPxC : PxC ∈ C) (hP : ‖x - PxC‖ = ⨅ w : C, ‖x - w‖) :
  ∀ w ∈ C, inner ℝ (x - PxC) (w - PxC) ≤ 0 := (norm_eq_iInf_iff_real_inner_le_zero hC2 hPxC).1 hP

-- 引理 30.15：提取子列的弱收敛性和内积序列的收敛性
lemma halpern_subsequence_weak_convergence [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : H → H} {C : Set H}
  (hT_fixpoint : C.Nonempty) (alg : Halpern T)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (h_C_closed_convex : IsClosed C ∧ Convex ℝ C)
  (h_xn_bounded : ∃ M, ∀ n, ‖alg.x n‖ ≤ M) (h_Txn_bounded : ∃ M, ∀ (n : ℕ), ‖T (alg.x n)‖ ≤ M) :
  ∃ (n : ℕ → ℕ) (z : H) (m : H) (q : ℕ → ℝ), (∀ i j, i < j → n i < n j) ∧
    (z ∈ D ∧ WeakConverge (alg.x ∘ n) z) ∧ (m ∈ C ∧ ‖alg.u - m‖ = ⨅ w : C, ‖alg.u - w‖) ∧
      (q = fun n => ⟪T (alg.x n) - m, alg.u - m⟫) ∧
        (Tendsto (q ∘ n) atTop (𝓝 (limsup q atTop))) := by
  have h_C_closed : IsClosed C := h_C_closed_convex.1
  have h_C_convex : Convex ℝ C := h_C_closed_convex.2
  obtain ⟨m, hm_in_C, hm_proj⟩ :=
    existence_of_projection_point C hT_fixpoint h_C_convex h_C_closed alg.u

  let q : ℕ → ℝ := fun n => ⟪T (alg.x n) - m, alg.u - m⟫; rcases h_Txn_bounded with ⟨M_Tx, hM_Tx⟩
  have hq_bdd : ∃ M : ℝ, ∀ k : ℕ, |q k| ≤ M := by
    use (M_Tx + ‖m‖) * ‖alg.u - m‖; intro k; calc
      _ = |⟪T (alg.x k) - m, alg.u - m⟫| := rfl
      _ = max (⟪T (alg.x k) - m, alg.u - m⟫) (-⟪T (alg.x k) - m, alg.u - m⟫) := rfl
      _ = max (⟪T (alg.x k) - m, alg.u - m⟫) (⟪-(T (alg.x k) - m), alg.u - m⟫) := by
        congr; exact Eq.symm (inner_neg_left (T (alg.x k) - m) (alg.u - m))
      _ ≤ ‖T (alg.x k) - m‖ * ‖alg.u - m‖ := by
        apply max_le (real_inner_le_norm (T (alg.x k) - m) (alg.u - m)) ?_
        · calc
          _ ≤ ‖-(T (alg.x k) - m)‖ * ‖alg.u - m‖ :=
            real_inner_le_norm (-(T (alg.x k) - m)) (alg.u - m)
          _ = ‖T (alg.x k) - m‖ * ‖alg.u - m‖ := by rw [norm_neg]
      _ ≤ (‖T (alg.x k)‖ + ‖m‖) * ‖alg.u - m‖ := mul_le_mul_of_nonneg_right
        (norm_sub_le (T (alg.x k)) m) (norm_nonneg _)
      _ ≤ (M_Tx + ‖m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); simp; exact hM_Tx k

  have h_subseq_q : ∃ (k : ℕ → ℕ), StrictMono k ∧ Tendsto (q ∘ k) atTop (𝓝 (limsup q atTop)) := by
    obtain ⟨φ, L, h_strict_mono, h_L_eq, h_tendsto⟩ := lim_subsequence_eq_limsup q hq_bdd
    exact ⟨φ, h_strict_mono, by rwa [← h_L_eq]⟩
  obtain ⟨k, h_k_strict_mono, h_k_tendsto⟩ := h_subseq_q
  have h_xk_bounded : ∃ M, ∀ j, ‖alg.x (k j)‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_xn_bounded; exact ⟨M, fun j => hM (k j)⟩
  obtain ⟨l, z, h_l_strict_mono, h_weak_xkl_to_z⟩ :=
    bounded_seq_weakly_convergent_subsequence (alg.x ∘ k) h_xk_bounded

  have h_z_in_D : z ∈ D := by
    have h_x_in_D : ∀ j, alg.x (k (l j)) ∈ D := fun j => halg_x_in_D _
    have h_D_weakly_closed : IsWeaklyClosed D := by
      apply closed_is_weakly_closed
      · exact hD_convex
      · exact hD_closed
    have h_D_weakly_seq_closed : IsWeaklySeqClosed D := by
      apply weakly_closed_seq_closed; exact h_D_weakly_closed
    simp only [IsWeaklySeqClosed] at h_D_weakly_seq_closed
    apply h_D_weakly_seq_closed h_x_in_D h_weak_xkl_to_z
  let n : ℕ → ℕ := k ∘ l
  have h_n_strict_mono : ∀ i j, i < j → n i < n j := by
    intro i j hij; unfold n; simp only [Function.comp_apply]
    exact h_k_strict_mono (h_l_strict_mono i j hij)

  have h_n_tendsto : Tendsto (q ∘ n) atTop (𝓝 (limsup q atTop)) := by
    have h_comp : (q ∘ n) = (q ∘ k) ∘ l := by funext j; simp only [Function.comp_apply, n]
    rw [h_comp]; apply h_k_tendsto.comp; exact StrictMono.tendsto_atTop h_l_strict_mono
  exact ⟨n, z, m, q, h_n_strict_mono, ⟨h_z_in_D, h_weak_xkl_to_z⟩,
    ⟨hm_in_C, hm_proj⟩, rfl, h_n_tendsto⟩

-- 引理：子列满足误差趋零条件
lemma halpern_subseq_x_sub_Tx_tendsto_zero
  {T : H → H} (alg : Halpern T) (n : ℕ → ℕ) (h_n_strict_mono : ∀ i j, i < j → n i < n j)
  (h_x_Tx_limit : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (𝓝 0))
  : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (𝓝 0) := by
  have h_n_k_ge_k : ∀ k, n k ≥ k := by apply StrictMono.nat_id_le h_n_strict_mono
  rw [Metric.tendsto_atTop] at h_x_Tx_limit ⊢; intro ε ε_pos; obtain ⟨N, hN⟩ := h_x_Tx_limit ε ε_pos
  use N; intro k hk; specialize hN (n k) (Nat.le_trans hk (h_n_k_ge_k k))
  rw [dist_eq_norm] at hN ⊢; exact hN

-- 引理：子列的固定点性质
lemma halpern_subseq_fixed_point [CompleteSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) (alg : Halpern T) (n : ℕ → ℕ) (z : H)
  (h_z_in_D : z ∈ D) (h_z_weak_limit : WeakConverge (alg.x ∘ n) z) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (𝓝 0))
  : z ∈ Fix T := by
  apply corollary_4_28 hD_closed hD_convex hD_nonempty hT_nonexp (alg.x ∘ n)
    (fun k => halg_x_in_D (n k)) z h_z_in_D h_z_weak_limit h_subseq_x_Tx_limit

-- 引理 30.16：子列内积序列的上极限不等式
lemma halpern_limsup_inner_le_zero [CompleteSpace H]
  {D : Set H} {T : H → H} {C : Set H} (hC : C = Fix T ∩ D)
  (hC_closed_convex : IsClosed C ∧ Convex ℝ C) (alg : Halpern T) (n : ℕ → ℕ) (z : H)
  (h_z_in_C : z ∈ C) (h_weak_xn_to_z : WeakConverge (alg.x ∘ n) z) (m : H) (hm_in_C : m ∈ C)
  (hm_proj : ‖alg.u - m‖ = ⨅ w : C, ‖alg.u - w‖)
  (h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (𝓝 0))
  (h_n_tendsto : Tendsto (fun k => ⟪T (alg.x (n k)) - m, alg.u - m⟫) atTop
  (𝓝 (limsup (fun n => ⟪T (alg.x n) - m, alg.u - m⟫) atTop)))
  : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0 := by
  have h_subseq_inner_limit1 : Tendsto
    (fun k => ⟪T (alg.x (n k)) - alg.x (n k), alg.u - m⟫) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop] at h_subseq_x_Tx_limit ⊢; intro ε ε_pos; let R := ‖alg.u - m‖
      by_cases hR : R = 0
      · use 0; intro k hk; rw [Real.dist_eq]; simp only [sub_zero]
        have h_vec_zero : alg.u - m = 0 := norm_eq_zero.mp hR
        simp [inner_zero_right, h_vec_zero]; linarith
      · have hR_pos : 0 < R := by
          simp only [R]
          exact norm_pos_iff.mpr (by
            intro h_eq; have : ‖alg.u - m‖ = 0 := by simp [h_eq]
            exact hR this)
        obtain ⟨N, hN⟩ := h_subseq_x_Tx_limit (ε / R) (by positivity); use N; intro k hk
        specialize hN k hk; simp [dist_eq_norm] at hN; rw [Real.dist_eq]; simp only [sub_zero]; calc
          _ ≤ ‖T (alg.x (n k)) - alg.x (n k)‖ * ‖alg.u - m‖ := by apply abs_real_inner_le_norm
          _ = ‖alg.x (n k) - T (alg.x (n k))‖ * ‖alg.u - m‖ := by congr 1; rw [norm_sub_rev]
          _ < (ε / R) * R := mul_lt_mul_of_pos_right hN hR_pos
          _ = ε := by field_simp [ne_of_gt hR_pos]

  have h_subseq_inner_limit2 : Tendsto (fun k => ⟪alg.x (n k), alg.u - m⟫) atTop (𝓝 ⟪z , alg.u - m⟫)
    := by rw [tendsto_iff_weakConverge] at h_weak_xn_to_z; apply h_weak_xn_to_z (alg.u - m)

  have h_subseq_inner_limit3 : Tendsto (fun k => ⟪alg.x (n k) - m, alg.u - m⟫) atTop
    (𝓝 ⟪z - m, alg.u - m⟫) := by
      by_cases h_eq : alg.u = m
      · simp [h_eq]
      · rw [Metric.tendsto_atTop]at h_subseq_inner_limit2 ⊢; intro ε ε_pos
        obtain ⟨N, hN⟩ := h_subseq_inner_limit2 ε (by positivity); use N; intro k hk
        specialize hN k hk; rw [Real.dist_eq] at hN ⊢; calc
          _ = |⟪alg.x (n k), alg.u - m⟫- ⟪z, alg.u - m⟫| := by
            congr 1; simp [inner_sub_left, inner_sub_left]
          _ < ε := hN

  have h_proj_ineq : ⟪alg.u - m, z - m⟫ ≤ 0 := by
    have hm_in_D : m ∈ D := by rw [hC] at hm_in_C; exact Set.mem_of_mem_inter_right hm_in_C
    have h_proj_apply : ∀ w ∈ C, ⟪alg.u - m, w - m⟫ ≤ 0 :=
      proj_pt_inner_le_zero alg.u m C hC_closed_convex.2 hm_in_C hm_proj
    exact h_proj_apply z h_z_in_C

  have h_subseq_inner_limit4 : Tendsto (fun k => ⟪ T (alg.x (n k)) - m, alg.u - m⟫) atTop
    (𝓝 ⟪z - m, alg.u - m⟫) := by
      have h_inner_diff : ∀ k, ⟪ T (alg.x (n k)) - m, alg.u - m⟫ = ⟪ T (alg.x (n k)) -
        alg.x (n k), alg.u - m⟫ + ⟪ alg.x (n k) - m, alg.u - m⟫ := by
        intro k; simp [inner_sub_left, inner_sub_left, inner_sub_left]
      convert Tendsto.add h_subseq_inner_limit1 h_subseq_inner_limit3 using 1
      · funext k; exact h_inner_diff k
      · simp

  have h_limsup_eq : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop
    = ⟪z - m, alg.u - m⟫ := tendsto_nhds_unique h_n_tendsto h_subseq_inner_limit4
  calc
    _ = ⟪z - m, alg.u - m⟫ := h_limsup_eq
    _ = ⟪alg.u - m, z - m⟫ := real_inner_comm (alg.u - m) (z - m)
    _ ≤ 0 := h_proj_ineq

-- 引理：从上极限和步长条件提取存在量化形式
lemma halpern_eps_exists_of_limsup_and_alpha
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {T : H → H}
  (alg : Halpern T) (m : H) (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ ε ∧
    alg.α n * ‖alg.u - m‖^2 ≤ ε := by
  intro ε hε; by_cases h_um_zero : ‖alg.u - m‖ = 0
  · have h_u_eq_m : alg.u = m := eq_of_norm_sub_eq_zero h_um_zero
    rw [h_u_eq_m]; simp; use 0; intro n hn; linarith
  · have h_um_pos : 0 < ‖alg.u - m‖ := norm_pos_iff.mpr (fun h => h_um_zero (by
        have : alg.u - m = 0 := h
        simp [this]))
    have h_um_sq_pos : 0 < ‖alg.u - m‖^2 := by positivity
    -- 从 h_α_limit 得到 ∃k₁ 使得 λₙ < ε/‖u-m‖²
    rw [Metric.tendsto_atTop] at h_α_limit
    obtain ⟨k₁, hk₁⟩ := h_α_limit (ε / ‖alg.u - m‖^2) (by positivity)

    have h_limsup_half : ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ ε / 2 := by
      have h_eventually : ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ < ε / 2 := by
        have : (0 : ℝ) < ε / 2 := by linarith
        have h_gap : limsup (fun k => ⟪T (alg.x k) - m, alg.u - m⟫) atTop < ε / 2 := by
          linarith [h_limsup_neg]
        apply Filter.eventually_lt_of_limsup_lt h_gap h_inner_bounded
      filter_upwards [h_eventually] with n hn; exact le_of_lt hn

    rw [eventually_atTop] at h_limsup_half; obtain ⟨k₂, hk₂⟩ := h_limsup_half; use max k₁ k₂
    intro n hn; have hn_k₁ := le_of_max_le_left hn; have hn_k₂ := le_of_max_le_right hn
    constructor
    · exact le_trans (hk₂ n hn_k₂) (by linarith)
    · have h_α_small : ‖alg.α n - 0‖ < ε / ‖alg.u - m‖^2 := hk₁ n hn_k₁; rw [sub_zero] at h_α_small
      have h_alpha_abs : |alg.α n| = alg.α n := abs_of_nonneg (le_of_lt (h_α_range n).1)
      rw [← h_alpha_abs] at h_α_small
      · calc
          _ ≤ (ε / ‖alg.u - m‖^2) * ‖alg.u - m‖^2 := by
            apply mul_le_mul_of_nonneg_right ?_ h_um_sq_pos.le
            · simp [h_alpha_abs] at h_α_small; linarith
          _ = ε := by field_simp [ne_of_gt h_um_sq_pos]

-- 30.18：投影距离的上界
lemma halpern_xn_sub_PCx_upbd [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0)) (m : H) (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, ‖alg.x (n+1) - m‖ ^ 2 ≤ alg.α n * ε + (1 - alg.α n) *
    ‖alg.x n - m‖ ^ 2 + 2 * alg.α n * ε := by
  intro ε hε
  have h_inner_bound := halpern_eps_exists_of_limsup_and_alpha alg m h_α_limit h_α_range
    h_limsup_neg h_inner_bounded
  specialize h_inner_bound ε hε; rcases h_inner_bound with ⟨k, h_control⟩; use k; intro n hn
  have h_αn0 : 0 < alg.α n := (h_α_range n).1; have h_αn1 : alg.α n < 1 := (h_α_range n).2
  specialize h_control n hn; rcases h_control with ⟨h_inner_control, h_mul_control⟩; calc
    _ = ‖alg.α n • (alg.u - m) + (1 - alg.α n) • (T (alg.x n) - m)‖ ^ 2 := by
      rw [alg.update]; congr; simp [smul_sub, sub_smul, ← add_sub_assoc, add_comm]
    _ = ‖alg.α n • (alg.u - m)‖ ^ 2 + ‖(1 - alg.α n) • (T (alg.x n) - m)‖ ^ 2 + 2 *
      ⟪alg.α n • (alg.u - m), (1 - alg.α n) • (T (alg.x n) - m)⟫ := by
        rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]; ring_nf
        simp [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm]; ring
      _ ≤ alg.α n * ε + (1 - alg.α n) * ‖alg.x n - m‖ ^ 2 + 2 * alg.α n * ε := by
        apply add_le_add
        · apply add_le_add
          · rw [norm_smul]; calc
              _ = (alg.α n)^2 * ‖alg.u - m‖^2 := by simp; rw [mul_pow, sq_abs]
              _ = alg.α n * (alg.α n * ‖alg.u - m‖^2) := by ring
              _ ≤ alg.α n * ε :=  mul_le_mul (by linarith) h_mul_control (mul_nonneg (by linarith)
                  (sq_nonneg ‖alg.u - m‖)) (by linarith)
          · -- 第二项：‖(1-α_n) • (Tx_n - m)‖² ≤ (1-α_n) * ‖x_n - m‖²
            rw [norm_smul]; calc
              _ = (1 - alg.α n) ^ 2 * ‖T (alg.x n) - m‖^2 := by simp; rw [mul_pow, sq_abs]
              _ ≤ (1 - alg.α n)^2 * ‖alg.x n - m‖^2 := by
                apply mul_le_mul (by simp) ?_ (by apply sq_nonneg) (sq_nonneg (1 - alg.α n))
                gcongr; apply (h_induction m hm_in_C n).1
              _ = (1 - alg.α n) * ((1 - alg.α n) * ‖alg.x n - m‖^2) := by ring
              _ ≤ (1 - alg.α n) * ‖alg.x n - m‖^2 := by
                apply mul_le_mul (by simp)
                · nth_rewrite 2 [← one_mul (‖alg.x n - m‖ ^ 2)]
                  apply mul_le_mul (by linarith) (by simp) (sq_nonneg ‖alg.x n - m‖) (by simp)
                · apply mul_nonneg (by linarith) (sq_nonneg ‖alg.x n - m‖)
                · apply le_of_lt; linarith
        · -- 第三项：2 * ⟪α_n • (u - m), (1-α_n) • (Tx_n - m)⟫ ≤ 2 * α_n * ε
          calc
            _ = 2 * alg.α n * (1 - alg.α n) * ⟪alg.u - m, T (alg.x n) - m⟫ := by
              simp [real_inner_smul_left, real_inner_smul_right]; ring
            _ ≤ 2 * alg.α n * (1 - alg.α n) * ε := by
              gcongr
              · apply mul_nonneg (by linarith) (by linarith)
              · rw [real_inner_comm]; exact h_inner_control
            _ ≤ 2 * alg.α n * ε := by calc
                _ ≤ 2 * alg.α n * 1 * ε := by
                  apply mul_le_mul_of_nonneg_right ?_ (le_of_lt hε)
                  apply mul_le_mul_of_nonneg_left (by linarith)
                  apply mul_nonneg (by norm_num) ((h_α_range n).1.le)
                _ = 2 * alg.α n * ε := by ring

-- 引理 30.19：归纳得到乘积形式
lemma halpern_xn_sub_PCx_prod [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0)) (m : H) (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n k : ℕ, n ≥ N → k ≥ N → n ≥ k → ‖alg.x (n + 1) - m‖ ^ 2
    ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 * (∏ l ∈ Finset.Icc k n, (1 - alg.α l)) := by
  -- 首先应用 30.18 获得逐步不等式
  have h_dist_bound := halpern_xn_sub_PCx_upbd alg h_α_range h_α_limit m
    hm_in_C h_induction h_limsup_neg h_inner_bounded
  intro ε hε; obtain ⟨N, hN⟩ := h_dist_bound ε hε; use N; intro n k hn hk hnk
  -- 通过对 n - k 的长度进行归纳
  obtain ⟨len, rfl⟩ := exists_add_of_le hnk; induction len with
  | zero =>
    -- 基础情况：n = k
    simp only [add_zero, Finset.Icc_self, Finset.prod_singleton]
    have h_step_case := hN k (by linarith); calc
      _ ≤ alg.α k * ε + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 + 2 * alg.α k * ε := h_step_case
      _ = 3 * alg.α k * ε + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 := by ring
      _ ≤ 3 * ε * alg.α k + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 := by linarith
      _ ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 * (1 - alg.α k) := by
        have h1_minus_α : 0 ≤ 1 - alg.α k := by linarith [one_sub_pos_of_mem_Ioo (h_α_range k)]
        have hε_pos : 0 ≤ ε := le_of_lt hε; nlinarith [sq_nonneg (‖alg.x k - m‖)]
  | succ len' ih =>
    -- 归纳步：从 len' 推到 len' + 1
    have hnk' : N ≤ k + len' := by linarith
    have h_ih := ih hnk'; calc
      _ = ‖alg.x (k + len' + 1 + 1) - m‖ ^ 2 := by ring_nf
      _ ≤ alg.α (k + len' + 1) * ε + (1 - alg.α (k + len' + 1)) * ‖alg.x (k + len' + 1) - m‖ ^ 2 +
        2 * alg.α (k + len' + 1) * ε := by apply hN (k + len' + 1); linarith

      _ ≤ alg.α (k + len' + 1) * ε + (1 - alg.α (k + len' + 1)) * (3 * ε + ‖alg.x k - m‖ ^ 2 *
          ∏ l ∈ Finset.Icc k (k + len'), (1 - alg.α l)) + 2 * alg.α (k + len' + 1) * ε := by
            have : k + len' ≥ k := by linarith
            simp; apply mul_le_mul (by simp) (h_ih this) (sq_nonneg ‖alg.x (k + len' + 1) - m‖)
            linarith [one_sub_pos_of_mem_Ioo (h_α_range (k + len' + 1))]

      _ = 3 * ε + ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k (k + (len' + 1)), (1 - alg.α l) := by
        have :- (alg.α (1 + k + len') * ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (k + len'),
          (1 - alg.α x)) + ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (k + len'), (1 - alg.α x) =
            ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (1 + k + len'), (1 - alg.α x) := by
              simp [add_comm]; simp [← add_assoc]; simp [← Nat.succ_eq_add_one]
              rw [Finset.prod_Icc_succ_top]
              · ring_nf; simp; left; congr 1; ring_nf
              · linarith
        rw [mul_add]; ring_nf
        rw [add_comm (-(alg.α (1 + k + len') * ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc
          k (k + len'), (1 - alg.α x))) (ε * 3), add_assoc, add_eq_add_iff_eq_and_eq]
        · simp; exact this
        · simp
        · linarith

-- 引理：从上极限有界得到序列有界
lemma halpern_inner_bounded_of_limsup
  {T : H → H} (alg : Halpern T) (m : H) (μ : ℝ) (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  (h_limsup_neg : limsup (fun k ↦ inner ℝ (T (alg.x k) - m) (alg.u - m)) atTop ≤ 0)
  : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M := by
  have : ∃ N, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ < N := by
    have h_limsup_neg' : limsup (fun k ↦ inner ℝ (T (alg.x k) - m) (alg.u - m)) atTop < 1 := by
      linarith
    use 1; apply Filter.eventually_lt_of_limsup_lt h_limsup_neg' ?_
    simp [IsBoundedUnder, IsBounded]; use (μ + ‖alg.u - m‖) * ‖alg.u - m‖; use 0; intro b hb; calc
      _ ≤ ‖T (alg.x b) - m‖ * ‖alg.u - m‖ := real_inner_le_norm (T (alg.x b) - m) (alg.u - m)
      _ = ‖(T (alg.x b) - alg.u) + (alg.u - m)‖ * ‖alg.u - m‖ := by simp
      _ ≤ (‖T (alg.x b) - alg.u‖ + ‖alg.u - m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul (norm_add_le (T (alg.x b) - alg.u) (alg.u - m)) (by simp)
          (norm_nonneg (alg.u - m)); rw [← zero_add 0]
        apply add_le_add (norm_nonneg (T (alg.x b) - alg.u)) (norm_nonneg (alg.u - m))
      _ ≤ (μ + ‖alg.u - m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul ?_ (by simp) (by simp) ?_
        · simp; specialize hμ_Tx_bound b; calc
            _ = ‖alg.u - T (alg.x b)‖ := by rw [norm_sub_rev]
            _ ≤ μ := hμ_Tx_bound
        · have : μ ≥ 0 := by specialize hμ_Tx_bound b; linarith [norm_nonneg (alg.u - T (alg.x b))]
          rw [← zero_add 0]; apply add_le_add this (norm_nonneg (alg.u - m))
  rcases this with ⟨N, hN⟩; use N; filter_upwards [hN] with n hn; linarith

-- 引理：由(30.19)和步长条件得到 limsup 的上界
lemma halpern_limsup_bound_from_prod [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M) (y : H)
  (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M)
  : ∀ ε > 0, ∃ N : ℕ, ∀ (n k : ℕ), n ≥ k → n ≥ N → k ≥ N →
      limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≤ 3 * ε := by
  have h_α_le_one : ∀ n, 1 - alg.α n ≤ 1 := by
    intro n; linarith [one_sub_lt_one_of_mem_Ioo (h_α_range n)]
  have h_nonneg_one_sub_α : ∀ n, 0 ≤ 1 - alg.α n := by
    intro n; linarith [one_sub_pos_of_mem_Ioo (h_α_range n)]
  intro ε hε
  obtain ⟨N, hN⟩ := halpern_xn_sub_PCx_prod alg h_α_range h_α_limit m hm_in_C h_induction
    h_limsup_neg h_inner_bounded ε hε
  have h_pointwise : ∀ n ≥ N, ∀ k ≥ N, n ≥ k → ‖alg.x (n + 1) - m‖ ^ 2 ≤ 3 * ε +
    ‖alg.x k - m‖ ^ 2 * (∏ l ∈ Finset.Icc k n, (1 - alg.α l)) := by
    intros n hn k hk hnk; exact hN n k hn hk hnk
  have h_prod_zero : ∀ k ≥ N, limsup (fun n => (∏ l ∈ Finset.Icc k n, (1 - alg.α l)))
    atTop = 0 := by
    intro k hk; have h_prod_tendsto := infinite_prod_zero alg h_α_range h_α_sum_inf k
    exact Tendsto.limsup_eq h_prod_tendsto
  use N; intro n k hnk hnN hkN
  have ⟨M, hM⟩ : ∃ M : ℝ, ∀ n : ℕ, ‖alg.x n - m‖ ^ 2 ≤ M := by
    obtain ⟨K, hK⟩ := h_seq_bounded
    have h_K_nonneg : 0 ≤ K := by
      have hK_nonneg : ∀ n, 0 ≤ ‖alg.x n - y‖ := by
        intro n; exact norm_nonneg _
      exact Std.le_trans (hK_nonneg N) (hK N)
    use (‖y - m‖ + K) ^ 2; intro n; calc
      _ = ‖(alg.x n - y) + (y - m)‖ ^ 2 := by congr; abel
      _ = ‖alg.x n - y‖ ^ 2 + ‖y - m‖ ^ 2 + 2 * ⟪alg.x n - y, y - m⟫ := by
        rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]; simp [real_inner_comm]; ring
      _ ≤ K ^ 2 + ‖y - m‖ ^ 2 + 2 * ‖alg.x n - y‖ * ‖y - m‖ := by
        apply add_le_add
        · apply add_le_add ?_ (by simp)
          · apply sq_le_sq.2; simp; convert hK n; simp; assumption
        rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (real_inner_le_norm (alg.x n - y) (y - m))
        norm_num
      _ ≤ (‖y - m‖ + K) ^ 2 := by
        rw [pow_two (‖y - m‖ + K), mul_add, add_mul, add_mul]; ring_nf; simp; rw [add_comm]; simp
        rw [mul_comm]; apply mul_le_mul (by convert hK n) (by simp)
          (norm_nonneg (y - m)) (by assumption)
  calc
    _ ≤ limsup (fun n => 3 * ε + ‖alg.x k - m‖ ^ 2 * (∏ l ∈ Finset.Icc k n, (1 - alg.α l)))
      atTop := by
        apply limsup_le_limsup
        · apply eventually_atTop.2; use k; intro p hp; apply h_pointwise
          · linarith
          · assumption
          · assumption
        · simp [autoParam, IsCoboundedUnder, IsCobounded]; use 0; intro a p q
          specialize q (p + 1) (by linarith)
          have h_norm_sq_nonneg : 0 ≤ ‖alg.x (p + 1 + 1) - m‖ ^ 2 := by apply sq_nonneg
          linarith
        · simp [autoParam, IsBoundedUnder, IsBounded]
          use (3 * ε + M), 0; intro b; simp; calc
            _ ≤ M * ∏ l ∈ Finset.Icc k b, (1 - alg.α l) := by
              apply mul_le_mul (by convert hM k) (by simp) ?_ ?_
              · apply Finset.prod_nonneg; intro i hi; exact h_nonneg_one_sub_α i
              · have h_norm_sq_nonneg : 0 ≤ ‖alg.x b - m‖ ^ 2 := by apply sq_nonneg
                linarith [hM b]
            _ ≤ M := by
              nth_rewrite 2 [← mul_one M]; apply mul_le_mul_of_nonneg_left
              · exact Finset.prod_le_one (fun i a ↦ h_nonneg_one_sub_α i) fun i a ↦ h_α_le_one i
              · have h_norm_sq_nonneg : 0 ≤ ‖alg.x b - m‖ ^ 2 := by apply sq_nonneg
                linarith [hM b]
    _ = limsup (fun n ↦ ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k n, (1 - alg.α l) + 3 * ε) atTop := by
      apply congr ?_ (by simp); ext n; ring_nf
    _ ≤ limsup (fun n => ‖alg.x k - m‖ ^ 2) atTop *
      limsup (fun n => (∏ l ∈ Finset.Icc k n, (1 - alg.α l))) atTop + 3 * ε := by
      rw [limsup_add_const]
      · simp; apply limsup_mul_le (by simp; exact atTop_neBot) (isBoundedUnder_const) ?_ ?_
        · apply eventually_atTop.2; use k; intro n hn; simp
          exact Finset.prod_nonneg fun i a ↦ h_nonneg_one_sub_α i
        · simp [IsBoundedUnder, IsBounded]; use 1, k; intro n hn; apply Finset.prod_le_one
          · intro i hi; exact h_nonneg_one_sub_α i
          · intro i hi; exact h_α_le_one i
      · simp [IsBoundedUnder, IsBounded]
        have h_M_nonneg : 0 ≤ M := by
          by_contra h; push_neg at h; have := hM 1
          have h_contradiction : ‖alg.x 1 - m‖ ^ 2 < 0 := by linarith
          linarith [sq_nonneg (‖alg.x 1 - m‖)]
        use M, k; intro n hn; rw [← mul_one M]; apply mul_le_mul (by convert hM k) ?_ ?_ h_M_nonneg
        · apply Finset.prod_le_one
          · intro i hi; exact h_nonneg_one_sub_α i
          · intro i hi; exact h_α_le_one i
        · apply Finset.prod_nonneg; intro i hi; exact h_nonneg_one_sub_α i
      · --‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k n, (1 - alg.α l)有界
        simp [IsCoboundedUnder, IsCobounded]; use 0; intro a p q; specialize q (p + 1) (by linarith)
        have : ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k (p + 1), (1 - alg.α l) ≥ 0 := by
          apply mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i a ↦ h_nonneg_one_sub_α i)
        linarith
    _ = limsup (fun n ↦ ‖alg.x k - m‖ ^ 2) atTop * 0 + 3 * ε := by
      congr; rw [h_prod_zero k]; assumption
    _ = 3 * ε := by rw [mul_zero]; simp

-- 辅助引理：有界性的相互推导
lemma halpern_norm_sq_bounded
  {T : H → H} (alg : Halpern T) (z m : H) (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M)
  : ∃ M : ℝ, ∀ n : ℕ, ‖alg.x (n + 1) - m‖ ^ 2 ≤ M := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ (n : ℕ), ‖alg.x (n + 1) - z‖ ≤ M := by
    rcases h_seq_bounded with ⟨M,hM⟩; use M; intro n; exact hM (n + 1)
  use (M + ‖z - m‖) ^ 2; intro n; calc
    _ = ‖alg.x (n + 1) - z + z - m‖ ^ 2 := by simp
    _ ≤ (‖alg.x (n + 1) - z‖ + ‖z - m‖) ^ 2 := by
      apply sq_le_sq.mpr; simp
      have : ‖alg.x (n + 1) - z‖ + ‖z - m‖ ≥ 0 := add_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [abs_of_nonneg this]; exact norm_sub_le_norm_sub_add_norm_sub (alg.x (n + 1)) z m
    _ ≤ (M + ‖z - m‖) ^ 2 := by
      apply sq_le_sq.mpr; simp [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [abs_of_nonneg]
      · exact add_le_add_right (hM n) ‖z - m‖
      · apply add_nonneg ?_ (norm_nonneg _); specialize hM 0
        have : ‖alg.x (0 + 1) - z‖ ≥ 0 := norm_nonneg _; linarith

-- x n收敛到PCx
lemma halpern_convergence_aux [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M) (z : H)
  (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M)
  : Tendsto alg.x atTop (𝓝 m) := by
  -- limsup上界被ε控制
  have h_limsup_upbd : ∀ ε > 0, limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≤ 3 * ε := by
    intro ε hε; have h_seq_bound_z : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M := by
      obtain ⟨M, hM⟩ := h_seq_bounded
      exact ⟨M + ‖z - z‖, fun n => by
        calc ‖alg.x n - z‖ = ‖(alg.x n - z) + (z - z)‖ := by simp
          _ ≤ ‖alg.x n - z‖ + ‖z - z‖ := norm_add_le _ _
          _ ≤ M + ‖z - z‖ := by linarith [hM n]⟩
    obtain ⟨N, hN⟩ := halpern_limsup_bound_from_prod alg h_α_range h_α_limit h_α_sum_inf m
      hm_in_C h_induction h_limsup_neg h_inner_bounded z h_seq_bound_z ε hε
    exact hN N N (le_refl N) (le_refl N) (le_refl N)

  -- limsup下界被0控制
  have h_limsup_udbd : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≥ 0 := by
    have h0 : limsup (fun (n : ℕ) => (0 : ℝ)) atTop = (0 : ℝ) := by exact limsup_const 0
    rw [← h0]; apply limsup_le_limsup
    · apply eventually_atTop.2; use 0; intro n hn; simp
    · simp [autoParam]; apply Filter.IsCoboundedUnder.of_frequently_ge
      exact frequently_const.mpr h_limsup_neg
    · simp [autoParam, IsBoundedUnder, IsBounded]
      obtain ⟨M, hM⟩ := halpern_norm_sq_bounded alg z m h_seq_bounded
      use M, 0; intro n hn; exact hM n

  -- 结合上下界得到极限为0
  have h_limsup_zero : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop = 0 := by
    by_contra! h_ne_zero
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
    rw [← h_limsup_zero]; have h_nonneg : ∀ n, 0 ≤ ‖alg.x (n + 1) - m‖ ^ 2 := fun n => sq_nonneg _
    rw [Metric.tendsto_atTop]; intro ε ε_pos
    have h_eventually : ∀ᶠ n in atTop, ‖alg.x (n + 1) - m‖ ^ 2 < ε := by
      have h_limsup_lt : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop < ε := by
        rw [h_limsup_zero]; exact ε_pos
      apply Filter.eventually_lt_of_limsup_lt (h_limsup_lt) ?_; simp [IsBoundedUnder, IsBounded]
      obtain ⟨M, hM⟩ := halpern_norm_sq_bounded alg z m h_seq_bounded
      use M, 0; intro n hn; exact hM n
    obtain ⟨N, hN⟩ := (eventually_atTop).mp h_eventually; use N; intro n hn
    rw [Real.dist_eq, h_limsup_zero]; simp [sub_zero]; exact abs_of_nonneg (h_nonneg n) ▸ hN n hn

  -- 从平方范数趋于零直接推出序列收敛到 m
  have h_shifted : Tendsto (fun n => alg.x (n + 1)) atTop (𝓝 m) := by
    rw [Metric.tendsto_atTop] at h_norm_sq_tendsto_zero ⊢; intro ε ε_pos
    obtain ⟨N, hN⟩ := h_norm_sq_tendsto_zero (ε ^ 2) (by positivity); use N; intro n hn
    rw [dist_eq_norm]
    have h_sq : ‖alg.x (n + 1) - m‖ ^ 2 < ε ^ 2 := by simpa [Real.dist_eq] using hN n hn
    apply sq_lt_sq.1 at h_sq; simp at h_sq; rw [abs_of_pos ε_pos] at h_sq; assumption
  exact (tendsto_add_atTop_iff_nat 1).mp h_shifted

#check Filter.eventually_lt_of_limsup_lt
#check norm_eq_iInf_iff_real_inner_le_zero--投影的形式

-- x 0 = u
lemma halpern_convergence_point_same [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty) (alg : Halpern T) (halg_x0 : alg.x0 ∈ D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|)) (coincidence : alg.u = alg.x0)
  : ∃ (p : H), p ∈ C ∧ Tendsto alg.x atTop (𝓝 p) ∧ (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  have hT_quasinonexp := nonexpansive_leadsto_quasinonexpansive hT_nonexp
  have hC_closed_convex := quasinonexpansive_fixedPoint_closed_convex hD_closed hD_convex
    hD_nonempty hT_quasinonexp hC
  obtain ⟨y, hy_in_C⟩ := hT_fixpoint
  have h_induction := halpern_distance_monotone hT_nonexp hC alg halg_x0 halg_x_in_D h_α_range
    coincidence

  -- 证明序列有界 (30.6)
  have h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M := by
    use ‖alg.x0 - y‖; intro n; apply (h_induction y hy_in_C n).2

  have h_xn_bounded : ∃ M, ∀ n, ‖alg.x n‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_seq_bounded; let M2 := ‖y‖; use M1 + M2; intro n; calc
      _ = ‖(alg.x n - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖alg.x n - y‖ + ‖y‖ := by apply norm_add_le
      _ ≤ M1 + M2 := by linarith [hM1 n]

  -- 证明 (Txₙ)ₙ∈ℕ 有界 (30.7)
  have h_Tseq_bounded : ∃ M, ∀ n, ‖T (alg.x n) - y‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_seq_bounded; use M; intro n; calc
      _ ≤ ‖alg.x n - y‖ := (h_induction y hy_in_C n).1
      _ ≤ M := hM n
  have h_Txn_bounded : ∃ M, ∀ n, ‖T (alg.x n)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_Tseq_bounded; let M2 := ‖y‖; use M1 + M2; intro n; calc
      _ = ‖(T (alg.x n) - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖T (alg.x n) - y‖ + ‖y‖ := by apply norm_add_le
      _ ≤ M1 + M2 := by linarith [hM1 n]

  -- 证明 (xₙ₊₁ - Txₙ)ₙ∈ℕ 有界 (30.8)
  have h_diff_bounded : ∃ M, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_seq_bounded; obtain ⟨M2, hM2⟩ := h_Tseq_bounded
    use M1 + M2; intro n; calc
      _ = ‖(alg.x (n + 1) - y) - (T (alg.x n) - y)‖ := by congr 1; rw [sub_sub_sub_cancel_right]
      _ ≤ ‖alg.x (n + 1) - y‖ + ‖T (alg.x n) - y‖ := by apply norm_sub_le
      _ ≤ M1 + M2 := by linarith [hM1 (n + 1), hM2 n]

  -- 由 (30.6) 和 (30.7)，定义 μ = sup max{‖xₙ₊₁ - xₙ‖, ‖x - Txₙ‖} < +∞ (30.9)
  have ⟨μ, hμ_pos, hμ_x_bound, hμ_Tx_bound⟩ : ∃ μ : ℝ, μ > 0 ∧
    (∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ) ∧(∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
      := halpern_mu_bound alg h_diff_bounded h_Tseq_bounded h_seq_bounded


  -- 证明 xₙ₊₂ - xₙ₊₁ = (λₙ₊₁ - λₙ)(x - Txₙ) + (1 - λₙ₊₁)(Txₙ₊₁ - Txₙ) (30.10)
  let h_diff_formula := halpern_diff_formula alg

  -- 使用提取出来的范数差分不等式引理(30.11)
  have h_norm_diff_ineq := halpern_norm_diff_ineq alg hT_nonexp halg_x_in_D h_α_range
    h_diff_formula μ hμ_Tx_bound

  -- 对于 n ≥ m，通过归纳证明 (30.12)
  have h_telescoping := halpern_telescoping_ineq
    alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq

  -- 让 n 和 m 趋于 +∞，得到 lim xn+1 − xn → 0
  have h_diff_limit := halpern_diff_limit alg h_α_range μ hμ_pos
    h_α_diff_finite h_α_sum_inf hμ_x_bound h_norm_diff_ineq h_telescoping

  -- 结合(30.8)与(30.13)得到(30.14)
  have h_x_Tx_limit : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (𝓝 0) :=
    halpern_x_sub_Tx_tendsto_zero alg h_α_range h_α_limit μ hμ_pos hμ_Tx_bound h_diff_limit

  -- 得到(30.15)
  obtain ⟨p, z, m, q, h_n_strict_mono, ⟨h_z_in_D, h_weak_xn_to_z⟩, ⟨hm_in_C, hm_proj⟩, hq_def,
    h_n_tendsto⟩ := halpern_subsequence_weak_convergence hD_closed hD_convex (by use y)
      alg halg_x_in_D hC_closed_convex h_xn_bounded h_Txn_bounded

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
  have h_z_in_C : z ∈ C := by rw [hC]; exact ⟨h_z_fixed, h_z_in_D⟩

  -- 得到(30.16)
  have h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0 := by
    apply halpern_limsup_inner_le_zero hC hC_closed_convex alg p z h_z_in_C
      h_weak_xn_to_z m hm_in_C hm_proj h_subseq_x_Tx_limit
    rw [hq_def] at h_n_tendsto; exact h_n_tendsto

  -- 由limsup有界得到lim有界
  have h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M :=
    halpern_inner_bounded_of_limsup alg m μ hμ_Tx_bound h_limsup_neg

  -- x n收敛到 m
  have h_x_conv : Tendsto alg.x atTop (𝓝 m) := by
    exact halpern_convergence_aux alg h_α_range h_α_limit h_α_sum_inf m hm_in_C
      h_induction h_limsup_neg h_inner_bounded y h_seq_bounded
  use m; use hm_in_C; use h_x_conv; intro w hw_in_C
  apply proj_pt_inner_le_zero alg.u m C ?_ hm_in_C hm_proj w hw_in_C; rw [hC]
  rcases hC_closed_convex with ⟨h1,h2⟩; rw [← hC]; assumption

-- 结合两种情况的主定理
theorem halpern_convergence [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty) (hT_invariant : ∀ x ∈ D, T x ∈ D) (alg : Halpern T)
  (halg_x0 : alg.x0 ∈ D) (halg_u : alg.u ∈ D) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  : ∃ (p : H), p ∈ C ∧ Tendsto alg.x atTop (𝓝 p) ∧ (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  by_cases h_coincidence : alg.u = alg.x0
  · exact halpern_convergence_point_same hD_closed hD_convex hD_nonempty hT_nonexp hC hT_fixpoint
      alg halg_x0 halg_x_in_D h_α_range h_α_limit h_α_sum_inf h_α_diff_finite h_coincidence
  · have h_α_pos : ∀ n, 0 < alg.α n := by intro n; exact (h_α_range n).1
    have h_α_lt_one : ∀ n, alg.α n < 1 := by intro n; exact (h_α_range n).2
    let s0 := alg.u
    let s : ℕ → H := fun n => Nat.recOn n alg.u fun k sk => alg.α k • alg.u + (1 - alg.α k) • T sk
    have h_s_init : s 0 = alg.u := by simp [s]
    have h_s_update : ∀ k, s (k + 1) = alg.α k • alg.u + (1 - alg.α k) • T (s k) := by
      intro k; simp only [s]

    -- 验证新序列在 D 中
    have h_s_in_D : ∀ n, s n ∈ D := by
      intro n; induction n with
      | zero => rw [h_s_init]; exact halg_u
      | succ k ih =>
        rw [h_s_update]
        exact hD_convex halg_u (hT_invariant (s k) ih) (by linarith [h_α_pos k, h_α_lt_one k])
          (by linarith [h_α_pos k, h_α_lt_one k]) (by simp)

    -- 应用情况(a)到新序列
    have ⟨p, hp_in_C, hp_s_conv, hp_inner⟩ : ∃ (p : H), p ∈ C ∧ Tendsto s atTop (𝓝 p) ∧
      (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
      apply halpern_convergence_point_same
        hD_closed hD_convex hD_nonempty hT_nonexp hC hT_fixpoint
        { x0 := alg.u
          u := alg.u
          x := s
          α := alg.α
          update := h_s_update
          initial_value := h_s_init }
        halg_u h_s_in_D h_α_range h_α_limit h_α_sum_inf h_α_diff_finite
        rfl

    have h_norm_bounded : ∀ n : ℕ, ‖alg.x (n + 1) - s (n + 1)‖
      ≤ ‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 n, (1 - alg.α k) := by
      intro n; induction n with
      | zero =>
        simp [s, alg.update,← smul_sub]; calc
          _ = (1 - alg.α 0) * ‖T (alg.x 0) - T alg.u‖ := by
            rw [norm_smul]; simp; left; linarith [h_α_lt_one 0]
          _ ≤ (1 - alg.α 0) * ‖alg.x 0 - alg.u‖ := by
            apply mul_le_mul_of_nonneg_left
            · rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
              specialize hT_nonexp (halg_x_in_D 0) halg_u; simp at hT_nonexp
              rw [edist_dist, edist_dist] at hT_nonexp; simp at hT_nonexp
              rw[dist_eq_norm, dist_eq_norm] at hT_nonexp; exact hT_nonexp
            · simp; linarith [h_α_lt_one 0]
          _ = (1 - alg.α 0) * ‖alg.x 0 - s 0‖ := by rw [h_s_init]
          _ = ‖alg.x 0 - s 0‖ * (1 - alg.α 0) := by ring_nf
      | succ n ih =>
        calc
          _ = ‖(alg.α (n + 1) • alg.u + (1 - alg.α (n + 1)) • T (alg.x (n + 1)))
            - (alg.α (n + 1) • alg.u + (1 - alg.α (n + 1)) • T (s (n + 1)))‖ := by
            rw [alg.update, h_s_update]
          _ = ‖(1 - alg.α (n + 1)) • T (alg.x (n + 1))- (1 - alg.α (n + 1)) • T (s (n + 1))‖ := by
            simp
          _ =  ‖(1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (s (n + 1)))‖ := by
            rw [← smul_sub (1 - alg.α (n + 1)) (T (alg.x (n + 1))) (T (s (n + 1)))]
          _ = (1 - alg.α (n + 1)) * ‖T (alg.x (n + 1)) - T (s (n + 1))‖ := by
            rw [norm_smul]; simp; left; linarith [h_α_lt_one (n + 1)]
          _ ≤ (1 - alg.α (n + 1)) * (‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) := by
            apply mul_le_mul_of_nonneg_left
            · rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
              specialize hT_nonexp (halg_x_in_D (n + 1)) (h_s_in_D (n + 1)); simp at hT_nonexp
              rw [edist_dist, edist_dist] at hT_nonexp; simp at hT_nonexp
              rw[dist_eq_norm, dist_eq_norm] at hT_nonexp; exact Std.le_trans hT_nonexp ih
            · simp; linarith [h_α_lt_one (n + 1)]
          _ = ‖alg.x 0 - s 0‖ * (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * (1 - alg.α (n + 1)) := by
            ring_nf
          _ = ‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 (n + 1), (1 - alg.α k) := by
            nth_rewrite 2 [← Nat.succ_eq_add_one]; rw [Finset.prod_Icc_succ_top]
            · rw [← mul_assoc]
            · linarith

    have h_prod_tendsto_zero : Tendsto (fun n => (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k))
      * ‖alg.x 0 - s 0‖) atTop (𝓝 (0 * ‖alg.x 0 - s 0‖)) := by
        have h_prod := infinite_prod_zero alg h_α_range h_α_sum_inf 0
        apply Tendsto.mul_const; exact h_prod

    have h_prod_tendsto_zero' : Tendsto (fun n => ((∏ k ∈ Finset.Icc 0 n, (1 - alg.α k))
      * ‖alg.x 0 - s 0‖)) atTop (𝓝 0) := by convert h_prod_tendsto_zero; simp

    have h_diff_tendsto_zero : Tendsto (fun n => ‖alg.x (n + 1) - s (n + 1)‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop] at h_prod_tendsto_zero' ⊢
      intro ε ε_pos; obtain ⟨N, hN⟩ := h_prod_tendsto_zero' ε ε_pos; use N; intro n hn
      specialize hN n hn; rw [Real.dist_eq] at hN ⊢; simp only [sub_zero] at hN ⊢; simp; calc
        _ ≤ ‖alg.x 0 - s 0‖ * (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) := h_norm_bounded n
        _ = |(∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * ‖alg.x 0 - s 0‖| := by
          rw [abs_of_nonneg]
          · ring_nf
          · apply mul_nonneg ?_ (norm_nonneg _); apply Finset.prod_nonneg; intro k hk; simp
            linarith [h_α_lt_one k]
        _ < ε := hN

    have h_x_tendsto_p : Tendsto alg.x atTop (𝓝 p) := by
      rw [Metric.tendsto_atTop] at hp_s_conv ⊢
      intro ε ε_pos
      have h_diff_tendsto : Tendsto (fun n => alg.x n - s n) atTop (𝓝 0) :=
        ((tendsto_add_atTop_iff_nat 1).mp (Metric.tendsto_atTop.mpr fun ε hε => by
            rw [Metric.tendsto_atTop] at h_diff_tendsto_zero
            obtain ⟨N, hN⟩ := h_diff_tendsto_zero ε hε; use N; intro n hn; specialize hN n hn
            rw [dist_eq_norm] at hN ⊢; simp at hN ⊢; exact hN))
      rw [Metric.tendsto_atTop] at h_diff_tendsto
      obtain ⟨N1, hN1⟩ := hp_s_conv (ε / 2) (by linarith)
      obtain ⟨N2, hN2⟩ := h_diff_tendsto (ε / 2) (by linarith)
      use max N1 N2; intro n hn
      have h1 := hN1 n (le_of_max_le_left hn); have h2 := hN2 n (le_of_max_le_right hn)
      rw [dist_eq_norm] at h1 h2 ⊢; simp at h2; calc
        _ = ‖(alg.x n - s n) + (s n - p)‖ := by simp
        _ ≤ ‖alg.x n - s n‖ + ‖s n - p‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add h2 h1
        _ = ε := by ring
    use p
