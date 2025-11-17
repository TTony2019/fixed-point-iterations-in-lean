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


-- 定理 5.15 的形式化
theorem groetsch_theorem {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    -- (i) Fejér 单调性
    IsFejerMonotone km.x (Fix' T D) ∧
    -- (ii) 强收敛到 0
    (Tendsto (λ n => T (km.x n) - km.x n) atTop (𝓝 0)) ∧
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
  · intro ε hε_pos
    -- 由 km.hstepsize_sum 可知 ∑ s_n (1 - s_n) 发散到 +∞
    have h_sum_diverge := km.hstepsize_sum
    -- 因为 ∑ s_n (1 - s_n) 发散到 +∞，所以存在 N 使得当 n ≥ N 时，∑_{i=0}^{n} s_i (1 - s_i) > ‖x0 - y‖^2 / ε
    rcases (tendsto_atTop_atTop.mp h_sum_diverge) (‖km.x 0 - (Classical.choose km.fix_T_nonempty)‖ ^ 2 / ε)
      (by linarith [norm_nonneg _]) with ⟨N, hN⟩
    use N
    intro n hn_ge_N
    -- 利用关键不等式估计 ‖T(x_n) - x_n‖
    have key_estimate : ‖T (km.x n) - km.x n‖ ^ 2 ≤
        (‖km.x 0 - (Classical.choose km.fix_T_nonempty)‖ ^ 2) /
        (∑ i ∈ range (n + 1), km.stepsize i * (1 - km.stepsize i)) := by
      -- 从关键不等式出发
      have calc1 := by
        calc
          0 ≤ ‖km.x 0 - (Classical.choose km.fix_T_nonempty)‖ ^ 2 -
              ∑ i ∈ range (n + 1), km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 := by
            -- 利用关键不等式对 ‖x_{i+1} - y‖^2 进行递推展开
            have h_rec : ∀ m ≤ n, ‖km.x (m + 1) - (Classical.choose km.fix_T_nonempty)‖ ^ 2 ≤
                ‖km.x 0 - (Classical.choose km.fix_T_nonempty)‖ ^ 2 -
                ∑ i ∈ range (m + 1), km.stepsize i * (1 -
