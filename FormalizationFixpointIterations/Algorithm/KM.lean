import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.Nonexpansive.Definitions
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators

open Set Filter Topology
open BigOperators Finset Function
open Nonexpansive_operator  --命名空间

set_option linter.unusedSectionVars false
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Fejér 单调性的定义
def IsFejerMonotone (x : ℕ → H) (C : Set H) : Prop :=
  ∀ y ∈ C, ∀ n, ‖x (n + 1) - y‖ ≤ ‖x n - y‖

-- Krasnosel'skii-Mann 迭代结构
structure KM (D : Set H) (T : H → H) where
  x0 : H
  hx0 : x0 ∈ D
  stepsize : ℕ → ℝ
  hstepsize : ∀ n, stepsize n ∈ Set.Icc (0 : ℝ) 1
  hstepsize_sum : Tendsto (fun n => ∑ i ∈ range (n+1), stepsize i * (1 - stepsize i)) atTop atTop
  x : ℕ → H
  update : ∀ n, x (n + 1) = x n + stepsize n • (T (x n) - x n)
  initial_value : x 0 = x0
  fix_T_nonempty : (Fix' T D).Nonempty

-- 引理 2.15: for x,y ∈ H and α ∈ ℝ,
-- ‖α x + (1-α) y‖^2 + α(1-α)‖x - y‖^2 = α‖x‖^2 + (1-α)‖y‖^2
lemma Corollary_2_15 (x y : H) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 = α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  -- rewrite the squared norms as inner products
  rw [← real_inner_self_eq_norm_sq (α • x + (1 - α) • y), ← real_inner_self_eq_norm_sq (x - y),
    ← real_inner_self_eq_norm_sq x, ← real_inner_self_eq_norm_sq y]
  have h1 : inner ℝ (α • x + (1 - α) • y) (α • x + (1 - α) • y) =
      α ^ 2 * inner ℝ x x + 2 * α * (1 - α) * inner ℝ x y + (1 - α) ^ 2 * inner ℝ y y := by
    simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  have h2 : inner ℝ (x - y) (x - y) = inner ℝ x x - 2 * inner ℝ x y + inner ℝ y y := by
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  rw [h1, h2]
  ring

example (T : H → H) (D : Set H) (Fix_T_nonempty : (Fix' T D).Nonempty) :∃ y ∈ D,  T y =y:= by
  rcases Fix_T_nonempty with ⟨y, hy⟩
  dsimp [Fix'] at hy
  rcases hy with ⟨ hyD,hyFix⟩
  use y
  constructor
  · exact hyD
  · exact hyFix

--ε N 语言化 收敛性
lemma Converge_iff (u : ℕ → ℝ) (x0 : ℝ) :
Tendsto u atTop (𝓝 x0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x0 - ε) (x0 + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x0)]
  simp

-- 定理 5.15 的形式化
theorem groetsch_theorem {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    -- (i) Fejér 单调性
    IsFejerMonotone km.x (Fix' T D) ∧
    -- (ii) 强收敛到 0
    (Tendsto (λ n => ‖T (km.x n) - km.x n‖)  atTop (𝓝 0)) ∧
    -- (iii) 弱收敛到不动点
    ∃ x ∈ (Fix' T D),
      Tendsto km.x atTop (𝓝 x) := by

  have key_inequality : ∀ (y : H) (hy : y ∈ Fix' T D) (n : ℕ),
      ‖km.x (n + 1) - y‖^2 ≤ ‖km.x n - y‖^2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖^2 := by
 -- 证明 (i) Fejér 单调性
    intro y hy n
    rcases hy with ⟨-, hyfix⟩
    -- 先从 km.hstepsize n 得到 0 ≤ s 和 s ≤ 1
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have key_calc := by
      calc
        ‖km.x (n + 1) - y‖^2
            = ‖(1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y)‖^2 := by
              rw [km.update n]
              simp only [smul_sub, sub_smul, one_smul]
              abel_nf
        _ = (1 - km.stepsize n) * ‖km.x n - y‖^2
            + km.stepsize n * ‖T (km.x n) - y‖^2
            - km.stepsize n * (1 - km.stepsize n) * ‖(T (km.x n) - y) - ( km.x n - y)‖^2 := by
              -- apply Corollary_2_15 with arguments arranged to match this expression
              have h := Corollary_2_15 (T (km.x n) - y) (km.x n - y) (km.stepsize n)
              -- swap the summands inside the norm so the lemma matches exactly
              have add_comm_eq : (1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y) =
                km.stepsize n • (T (km.x n) - y) + (1 - km.stepsize n) • (km.x n - y) := by simp [add_comm]
              rw [add_comm_eq]
              rw[eq_sub_iff_add_eq , h]
              ring
        _ ≤ (1 - km.stepsize n) * ‖km.x n - y‖^2 + km.stepsize n * ‖km.x n - y‖^2 -km.stepsize n * (1 - km.stepsize n) *‖(T (km.x n)  -  km.x n )‖^2  := by

            have hT_le : ‖T (km.x n) - y‖ ≤ ‖km.x n - y‖ := by
              nth_rw 1 [← hyfix]
              exact hT_nonexpansive (km.x n) y
            simp
            apply mul_le_mul_of_nonneg_left _ hs_nonneg
            refine pow_le_pow_left₀ ?_ hT_le 2
            exact norm_nonneg _
        _ = ‖km.x n - y‖^2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖^2 := by
            ring
    exact key_calc
  -- 证明 (i) Fejér 单调性
  constructor
  · intro y hy n
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have calc1 :‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 := by
      calc
      ‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ ^ 2 := by
        exact key_inequality y hy n
      _≤ ‖km.x n - y‖ ^ 2 := by
        have h_nonneg : 0 ≤ km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - y - (km.x n - y)‖ ^ 2 := by
          apply mul_nonneg
          · apply mul_nonneg
            · exact hs_nonneg
            · exact sub_nonneg.mpr hs_le_one   -- 1 - s ≥ 0
          · exact pow_nonneg (norm_nonneg _) 2
        simp at h_nonneg
        linarith
      --‖ a ‖ ^2 ≤ ‖ b ‖ ^2 推出 ‖ a ‖ ≤ ‖ b ‖
    have := (sq_le_sq).mp calc1
    repeat rw[abs_of_nonneg (norm_nonneg _)] at this
    exact this
  -- 证明 (ii) 强收敛到 0
  constructor
  rcases km.fix_T_nonempty with ⟨y0, hy0⟩
  have sum_bound : ∀ N, ∑  i ∈ range (N), km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 - ‖km.x (N) - y0‖ ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hN := key_inequality y0 hy0 N
      simp [Finset.sum_range_succ]
      linarith

  have partial_le : ∀ N, ∑ i ∈ Finset.range N, km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 := by
      intro N
      refine (sum_bound N).trans ?_
      simp

  -- 定义 a_n 并证明其非增
  let a := fun n => ‖T (km.x n) - km.x n‖
  have a_noninc : ∀ n, a (n + 1) ≤ a n := by
    intro n
    rcases km.hstepsize n with ⟨hs0, hs1⟩
    -- x_{n+1} - x_n = s_n • (T x_n - x_n)
    have hx : km.x (n + 1) - km.x n = km.stepsize n • (T (km.x n) - km.x n) := by
      rw [km.update n]; simp [ smul_sub]
    have eq : T (km.x (n + 1)) - km.x (n + 1) = (T (km.x (n + 1)) - T (km.x n)) + (1 - km.stepsize n) • (T (km.x n) - km.x n) := by
      calc
        T (km.x (n + 1)) - km.x (n + 1) = T (km.x (n + 1)) - T (km.x n) + T (km.x n) - km.x (n + 1) := by simp
        _ = T (km.x (n + 1)) - T (km.x n) + (1 - km.stepsize n) • (T (km.x n) - km.x n) := by
          nth_rw 2 [km.update n]
          simp only [smul_sub, sub_smul, one_smul]
          abel_nf

    calc
      a (n + 1) = ‖T (km.x (n + 1)) - km.x (n + 1)‖ := rfl
      _ = ‖(T (km.x (n + 1)) - T (km.x n)) + (1 - km.stepsize n) • (T (km.x n) - km.x n)‖ := by rw [eq]
      _ ≤ ‖T (km.x (n + 1)) - T (km.x n)‖ + ‖(1 - km.stepsize n) • (T (km.x n) - km.x n)‖ := by apply norm_add_le
      _ ≤ ‖km.x (n + 1) - km.x n‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by
        apply add_le_add
        · exact (hT_nonexpansive (km.x (n + 1)) (km.x n))
        -- 从 stepsize ∈ Icc 0 1 拆出 0 ≤ s ≤ 1
        have h_nonneg : 0 ≤ 1 - km.stepsize n := by linarith
        -- 证明 ‖(1 - s) • v‖ ≤ (1 - s) * ‖v‖
        calc
          ‖(1 - km.stepsize n) • (T (km.x n) - km.x n)‖
              = ‖(1 - km.stepsize n)‖ * ‖T (km.x n) - km.x n‖ := by rw [norm_smul]
          _ = |1 - km.stepsize n| * ‖T (km.x n) - km.x n‖ := by rw [Real.norm_eq_abs]
          _ = (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [abs_of_nonneg h_nonneg]
        linarith
      _= ‖km.stepsize n • (T (km.x n) - km.x n)‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [hx]
      _= km.stepsize n * ‖T (km.x n) - km.x n‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hs0)]
      _= ‖T (km.x n) - km.x n‖ := by ring

  -- 反证：若 a 不收敛到 0，则存在 ε>0 使得对任意 N 都能找到 n ≥ N 使 a n ≥ ε
  rw [Converge_iff _ _]
  --rw[tendsto_atTop']
  by_contra hnot
  push_neg at hnot
  rcases hnot with ⟨ε, εpos, hε⟩

  -- 由 km.hstepsize_sum（偏和趋于 +∞）挑出 M 使得偏和大于 ‖x0-y0‖^2 / ε
  have tend := km.hstepsize_sum
  have tend_prop := (Filter.tendsto_atTop_atTop.mp tend) (‖km.x 0 - y0‖ ^ 2 / ε^2)
  rcases tend_prop with ⟨N0, hN0⟩
  -- 由 hε 在 N0 处选出 n ≥ N0 且 a n ≥ ε
  rcases (hε N0) with ⟨n0, hn0_ge, hn0_ge_eps⟩
  -- 对 n0 + 1 的偏和，利用单调性 a_i ≥ a_{n0}（i ≤ n0）得到下界
  have lower : ∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2 ≥
      ∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i)*ε ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have : i ≤ n0 := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have ai_ge : a i ≥ a n0 := by
      exact (antitone_nat_of_succ_le a_noninc) (by omega)
    have ai_ge_eps : ε ≤ a i := by
      have h : ε ≤ ‖T (km.x n0) - km.x n0‖ := by
        by_contra! H  -- H: ‖T (km.x n0) - km.x n0‖ < ε
        rw[← zero_add ε ] at H
        exact hn0_ge_eps ⟨by linarith [norm_nonneg (T (km.x n0) - km.x n0)], H⟩
      linarith
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (le_of_lt εpos) ai_ge_eps 2
    rcases km.hstepsize i with ⟨hs0, hs1⟩
    · apply mul_nonneg
      · exact hs0
      · exact sub_nonneg.mpr hs1

  -- 由 hN0（偏和下界从 N0 开始）得到 S ≥ ‖x0-y0‖^2 / ε^2，结合上面 lower 导出矛盾
  have S_ge : ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) ≥ ‖km.x 0 - y0‖ ^ 2 / ε^2:= by
    apply hN0
    exact le_trans (by linarith : N0 ≤ n0) (le_refl _)

  have lb: ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2 ≥ (‖km.x 0 - y0‖ ^ 2 ) := by
    calc
      ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2
          ≥ ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * ε ^ 2 := by
            exact lower
      _ = ε ^ 2 *(∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i))  := by
        have : (∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * ε ^ 2) =
            ∑ i ∈ range (n0 + 1), ε ^ 2 * (km.stepsize i * (1 - km.stepsize i) ) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [this]
        -- 把 ε^2 提到和式外面
        rw [← @Finset.mul_sum ℕ _ _ (range (n0 + 1))  (fun i => km.stepsize i * (1 - km.stepsize i)) (ε ^ 2)]
      _ ≥ ‖km.x 0 - y0‖ ^ 2 := by
        -- 应用 S_ge：先把目标改写为 ε^2 * (∑ ...) ≥ ε^2 * (‖x0-y0‖^2 / ε^2)，再用 mul_le_mul_of_nonneg_left
        have hpos : 0 ≤ ε ^ 2 := by exact pow_nonneg (le_of_lt εpos) 2
        calc
          ε ^ 2 * (∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i))
          _ ≥ ε ^ 2 * (‖km.x 0 - y0‖ ^ 2 / ε ^ 2) := by apply mul_le_mul_of_nonneg_left S_ge hpos
          _ = ‖km.x 0 - y0‖ ^ 2 := by
            -- 用 field_simp 消去除数 ε^2（ε > 0）
            field_simp [ne_of_gt εpos]

  have ub := partial_le (n0 + 1)
  linarith
