import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

open Filter

section WeakTopology

universe u1
variable {H : Type u1}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

abbrev W := WeakSpace ℝ H
#check W

def WeakConverge'' (x : ℕ → H) (p : H) :=
  Tendsto (x: ℕ → W) atTop (nhds p : Filter W)

def IsWeaklyClosed' (s : Set H) := IsClosed (s : Set W)

theorem weakConverge_iff_inner_converge (x : ℕ → H) (p : H) : WeakConverge'' x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫) := by
  sorry

noncomputable instance : Preorder (WeakSpace ℝ ℝ) := by
  exact specializationPreorder (WeakSpace ℝ ℝ)

theorem closed_is_weakly_closed' [CompleteSpace H] (s : Set H) (hs : Convex ℝ s) (hw : IsClosed s) :
  IsWeaklyClosed' s := by
  simp [IsWeaklyClosed']
  refine { isOpen_compl := ?_ }
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x xsc
  obtain ⟨f,u,fxu,fbu⟩ := geometric_hahn_banach_point_closed hs hw xsc
  let U := f⁻¹' (Set.Iio u)
  have hU: IsOpen U := by
    refine Continuous.isOpen_preimage ?_ (Set.Iio u) ?_
    exact ContinuousLinearMap.continuous f
    exact isOpen_Iio
  -- have hxinU : x ∈ U := fxu
  -- have hUinsc : U ⊆ sᶜ := by
  --   refine Disjoint.subset_compl_left ?_
  --   refine Set.disjoint_left.mpr ?_
  --   sorry
  let yf := (InnerProductSpace.toDual ℝ H).symm f
  have (x:H): ⟪yf,x⟫ = f x := by
    exact InnerProductSpace.toDual_symm_apply
  -- let WD := WeakDual ℝ H
  let f1 := WeakSpace.map f

  have (x : H): f1 x = f x := rfl
  let U' := f1⁻¹' (Set.Iio u)
  use U'
  have U'Open : IsOpen U' := by
    -- apply @isOpen_coinduced.mp


    have : WeakSpace ℝ ℝ = ℝ := rfl
    sorry

    -- apply isOpen_Iio
    -- apply?
  have hU'insc : U' ⊆ sᶜ := by sorry
  have hxinU' : x ∈ U' := sorry
  constructor
  · exact hU'insc
  constructor
  · sorry
  exact hxinU'


end WeakTopology
