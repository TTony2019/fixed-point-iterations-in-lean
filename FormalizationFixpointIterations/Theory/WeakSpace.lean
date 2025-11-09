import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

open Filter WeakDual Metric WeakBilin

section WeakTopology

universe u1
variable {H : Type u1}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def WeakConverge'' (x : ℕ → H) (p : H) :=
  Tendsto (x: ℕ → WeakSpace ℝ H) atTop (nhds p : Filter (WeakSpace ℝ H))

#check tendsto_iff_forall_eval_tendsto
#check LinearMap.flip_inj
#check LinearMap.flip_apply

def va (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a : H) : H →L[ℝ] ℝ where
  toFun := fun x => ⟪x, a⟫
  map_add' := sorry
  map_smul' := sorry

#check inner_self_eq_zero
lemma topDualPairing_is_injective : Function.Injective ⇑(topDualPairing ℝ H).flip := by
  simp [Function.Injective]
  intro a b hab
  have h1: (topDualPairing ℝ H).flip a (va H a)= (topDualPairing ℝ H).flip b (va H a) := by
    rw [hab]
  simp [LinearMap.flip_apply, topDualPairing_apply, va] at h1
  have h2: (topDualPairing ℝ H).flip a (va H b)= (topDualPairing ℝ H).flip b (va H b) := by
    rw [hab]
  simp [LinearMap.flip_apply, topDualPairing_apply, va] at h2
  have : a - b = 0 := by
    have h1': ⟪a - b, a⟫ = 0 := sorry
    have h2': ⟪a - b, b⟫ = 0 := sorry
    apply (@inner_self_eq_zero ℝ H _ _ _ (a - b)).1
    calc
      _ = ⟪a - b, a⟫ - ⟪a - b, b⟫ := inner_sub_right (a - b) a b
      _ = 0 - 0 := by sorry
      _ = 0 := by simp
  calc
    _ = a - b + b := Eq.symm (sub_add_cancel a b)
    _ = 0 + b := by rw [this]
    _ = b := by simp

#check InnerProductSpace.toDual
theorem topDualPairing_eq (p : H) : ∀ y : H →L[ℝ] ℝ, (topDualPairing ℝ H).flip p y = y p := by
  simp [LinearMap.flip_apply, topDualPairing_apply]

theorem topDualPairing_strong_dual [CompleteSpace H] (p : H) : ∀ y : H →L[ℝ] ℝ,
  (topDualPairing ℝ H).flip p y = ⟪(InnerProductSpace.toDual ℝ H).symm y, p⟫  := by
  simp [LinearMap.flip_apply, topDualPairing_apply]

theorem topDualPairing_strong_dual_seq [CompleteSpace H] (x : ℕ → H) : ∀ y : H →L[ℝ] ℝ,
  (fun n ↦ ((topDualPairing ℝ H).flip (x n)) y) =
  fun n => ⟪(InnerProductSpace.toDual ℝ H).symm y, x n⟫ := by
  intro y; ext n
  exact topDualPairing_strong_dual (x n) y

theorem topDualPairing_strong_dual_seq' [CompleteSpace H] (x : ℕ → H) : ∀ y : H →L[ℝ] ℝ,
  (fun n ↦ ((topDualPairing ℝ H).flip (x n)) y) =
  fun n => ⟪(InnerProductSpace.toDual ℝ H).symm y, x n⟫ := by
  intro y; ext n
  exact topDualPairing_strong_dual (x n) y

theorem weakConverge_iff_inner_converge_pre (x : ℕ → H) (p : H) : WeakConverge'' x p ↔
  ∀ y : H →L[ℝ] ℝ, Tendsto (fun n ↦ (topDualPairing ℝ H).flip (x n) y)
    atTop (nhds ((topDualPairing ℝ H).flip p y)) := by
  simp [WeakConverge'']
  apply tendsto_iff_forall_eval_tendsto
  exact topDualPairing_is_injective

theorem weakConverge_iff_inner_converge [CompleteSpace H] (x : ℕ → H) (p : H) : WeakConverge'' x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫) := by
  constructor
  · intro h y
    rw [weakConverge_iff_inner_converge_pre] at h
    specialize h (va H y)
    have : (fun n ↦ ((topDualPairing ℝ H).flip (x n)) (va H y)) = fun n => ⟪x n, y⟫ := by
      ext n
      simp [topDualPairing_apply, va]
    rw [this] at h
    simp [topDualPairing_apply, va] at h
    exact h
  intro h
  rw [weakConverge_iff_inner_converge_pre]
  intro y
  let yf := (InnerProductSpace.toDual ℝ H).symm y
  rw [topDualPairing_strong_dual, topDualPairing_strong_dual_seq]
  have : (fun n ↦ inner ℝ ((InnerProductSpace.toDual ℝ H).symm y) (x n)) =
    (fun n ↦ inner ℝ  (x n) ((InnerProductSpace.toDual ℝ H).symm y)) := by
    ext n; rw [real_inner_comm]
  rw [real_inner_comm, this]
  apply h

def IsWeaklyClosed' (s : Set H) := @IsClosed (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))

theorem continuous_real_weakspace : Continuous (toWeakSpace ℝ ℝ).symm := by
  have heq (w : ℝ): (toWeakSpace ℝ ℝ).symm w = (topDualPairing ℝ ℝ).flip w 1 := by
    simp [topDualPairing_apply]
    rfl
  have heq' : (toWeakSpace ℝ ℝ).symm.toFun = fun w => (topDualPairing ℝ ℝ).flip w 1 := by
    ext w
    exact heq w
  change Continuous (toWeakSpace ℝ ℝ).symm.toFun
  rw [heq']
  exact eval_continuous (topDualPairing ℝ ℝ).flip 1

#check isOpenMap_toWeakSpace_symm
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
  let yf := (InnerProductSpace.toDual ℝ H).symm f
  have (x:H): ⟪yf,x⟫ = f x := by
    exact InnerProductSpace.toDual_symm_apply
  let f1 := WeakSpace.map f
  let f2 := (toWeakSpace ℝ ℝ).symm
  let f21 := f2 ∘ f1
  have feq (x : H): f21 x = f x := rfl
  let U' := f21⁻¹' (Set.Iio u)
  use U'
  have U'Open : IsOpen U' := by
    refine Continuous.isOpen_preimage ?_ (Set.Iio u) ?_
    · simp [f21]
      refine Continuous.comp ?_ ?_
      · simp [f2]
        exact continuous_real_weakspace
      exact ContinuousLinearMap.continuous f1
    exact isOpen_Iio
  have hU'insc : U' ⊆ sᶜ := by
    intro g hg
    simp; simp [U', feq g] at hg
    by_contra! hgs
    linarith [fbu g hgs]
  have hxinU' : x ∈ U' := by
    refine Set.mem_preimage.mpr ?_
    simp [feq x]; exact fxu
  constructor
  · exact hU'insc
  constructor
  · exact U'Open
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
