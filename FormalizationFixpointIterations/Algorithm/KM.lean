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
open BigOperators Finset
open Nonexpansive_operator  --命名空间
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Fejér 单调性的定义
def IsFejerMonotone (x : ℕ → H) (C : Set H) : Prop :=
  ∀ y ∈ C, ∀ n, ‖x (n + 1) - y‖ ≤ ‖x n - y‖

def FixIn (T : H → H) (D : Set H) : Set H := {x ∈ D | T x = x}

-- Krasnosel'skii-Mann 迭代结构
structure KM (D : Set H) (T : H → H) where
  x0 : H
  hx0 := x0 ∈ D
  stepsize : ℕ → ℝ
  hstepsize : ∀ n, stepsize n ∈ Set.Icc (0 : ℝ) 1
  hstepsize_sum : Tendsto (fun n => ∑ i ∈ range (n+1), stepsize i * (1 - stepsize i)) atTop atTop
  x : ℕ → H
  update : ∀ n, x (n + 1) = x n + stepsize n • (T (x n) - x n)
  initial_value : x 0 = x0
  Fix_T := FixIn T D
  Fix_T_nonempty := (Fix' T D).Nonempty

-- 引理 2.15: for x,y ∈ H and α ∈ ℝ,
-- ‖α x + (1-α) y‖^2 + α(1-α)‖x - y‖^2 = α‖x‖^2 + (1-α)‖y‖^2
lemma Corollary_2_15 (x y : H) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 = α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  -- move to inner product form and expand using bilinearity
  simp [norm_add_sq_real,norm_sub_sq_real,inner_smul_left,inner_smul_right]
  repeat rw[norm_smul]
  simp
  ‖α •x ‖ = ‖α‖ * ‖x‖ := by rw [norm_smul]
  -- have h1 : (α ^ 2=‖α‖ ^ 2) := by rw[Real.norm_eq_abs,sq_abs]
  -- ring_nf
  -- rw[h1]
  -- ring_nf

-- 定理 5.15 的形式化
theorem groetsch_theorem {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    -- (i) Fejér 单调性
    IsFejerMonotone km.x km.Fix_T ∧
    -- (ii) 强收敛到 0
    (Tendsto (λ n => T (km.x n) - km.x n) atTop (𝓝 0)) ∧
    -- (iii) 弱收敛到不动点
    ∃ x ∈ km.Fix_T,
      Tendsto km.x atTop (𝓝 x) := by
  constructor -- 证明 (i) Fejér 单调性
  · intro y hy n
    have key_calc := by
      calc
        ‖km.x (n + 1) - y‖^2
            = ‖(1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y)‖^2 := by
              rw [km.update n]
              simp only [smul_sub, sub_smul, add_smul,one_smul]
              abel_nf
        _ ≤
