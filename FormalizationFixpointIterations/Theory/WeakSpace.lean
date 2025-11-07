import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

open Filter WeakDual Metric

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


section WeaklyClosed

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def IsWeaklyClosed (s : Set H) := @IsClosed (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))


end WeaklyClosed


section T2Space

#check Topology.IsEmbedding.t2Space
#check ProperSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

-- instance : AddCommGroup (WeakSpace ℝ H) := by
--   exact WeakSpace.instAddCommGroup
-- instance : PseudoMetricSpace (WeakSpace ℝ H) := by
--   sorry
  -- apply?
  -- apply pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor
  -- dist := sorry
  -- dist_self := sorry
  -- dist_comm := sorry
  -- dist_triangle := sorry

-- #check WeakSpace.t2Space ℝ H

instance : HMul ℝ (WeakSpace ℝ H) (WeakSpace ℝ H) := by
  exact { hMul := fun a a ↦ a }

instance : HDiv (WeakSpace ℝ H) ℝ (WeakSpace ℝ H) := by
  exact { hDiv := fun a a_1 ↦ a }

instance : T2Space (WeakSpace ℝ H) where
  t2 := by
    simp [Pairwise]
    intro x y hxy
    let u := x - y
    let w := (x + y)/(2:ℝ)
    -- let U := {z : H | ⟪z-w,u⟫ > 0}

    sorry

  -- apply @Topology.IsEmbedding.t2Space (WeakSpace ℝ H) H

  -- apply WeakBilin.isEmbedding
  -- · sorry
  -- sorry
  -- apply (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space


end T2Space

section WeaklyCompact

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def IsWeaklyCompact (s : Set H) : Prop := @IsCompact (WeakSpace ℝ H) _ (s: Set (WeakSpace ℝ H))

/-
Lemma 1.12
-/
example (s : Set H) (h : IsWeaklyCompact s) : IsWeaklyClosed s := IsCompact.isClosed h
#check IsCompact.of_isClosed_subset

example (s : Set H) (h : IsCompact s) : IsWeaklyCompact s := by
  simp [IsWeaklyCompact]
  -- apply?
  simp [IsCompact]

  sorry
  -- exact h
  -- sorry

-- open
/-
Fact 2.34: Banach-Alaoglu Bourbaki
-/
theorem closed_unit_ball_is_weakly_compact : IsWeaklyCompact (Metric.closedBall (0:H) (1:ℝ)) := by
  sorry

lemma isCompact_closedBall'' (x' : StrongDual ℝ H) (r : ℝ) :
    IsCompact (toStrongDual ⁻¹' closedBall x' r) := by
      exact WeakDual.isCompact_closedBall ℝ x' r

#check WeakDual.isCompact_closedBall

#check IsSeqCompact

def IsWeaklySeqCompact (s : Set H) := @IsSeqCompact (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))

/-
Fact 2.37 Eberlein Smulian
-/
theorem weakly_compact_iff_weakly_seq_compact (C : Set H) (hC : IsWeaklyCompact C) :
  IsWeaklySeqCompact C := by
  sorry

instance : SeqCompactSpace (WeakSpace ℝ H) := sorry

/-
Lemma 2.45
-/
theorem bounded_seq_has_weakly_converge_subseq (x : ℕ → H)
  (hx : BddAbove (Set.range (fun n => ‖x n‖))) :
  IsWeaklySeqCompact (Set.range x) := sorry

-- theorem bounded_seq_has_weakly_converge_subseq' (x : ℕ → H)
--   (hx : BddAbove (Set.range (fun n => ‖x n‖))) :
--   IsWeaklySeqCompact (Set.range x) := by
--   simp [IsWeaklySeqCompact, IsSeqCompact]


end WeaklyCompact
