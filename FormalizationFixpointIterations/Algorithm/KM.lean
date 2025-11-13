import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.Nonexpansive.Definitions

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- #check Fix'
structure KM (T : H → H) (D: Set H) where
  x0 : H
  x : ℕ → H
  stepsize : ℕ → ℝ
  update : ∀ k : ℕ, x (k + 1) = x k + (stepsize k) • (T (x k) - x k)
  intial_value : x 0 = x0
  fix : (Nonexpansive_operator.Fix' T D).Nonempty
