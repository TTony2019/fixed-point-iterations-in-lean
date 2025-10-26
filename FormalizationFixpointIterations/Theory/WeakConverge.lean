import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Adjoint
-- import Mathlib.Analysis.InnerProductSpace.OfNorm

open WeakBilin Filter

#check WeakDual
#check StrongDual
#check WeakBilin
-- #check tendsto_iff_forall_eval_tendsto
#check tendsto_iff_forall_eval_tendsto
#check inner
#check ClusterPt
#check mem_closure_iff_clusterPt
#check WeakBilin
#check geometric_hahn_banach_point_closed


section WeakTopology

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def innerBilinear1 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (x : H) : H →ₗ[ℝ] ℝ where
  toFun := fun y => @inner ℝ _ _ x y
  map_add' := fun x_2 y ↦ inner_add_right x x_2 y
  map_smul' := fun m x_2 ↦ inner_smul_right_eq_smul x x_2 m

def innerBilin (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : H →ₗ[ℝ] H →ₗ[ℝ] ℝ where
  toFun := fun x => (innerBilinear1 H x)
  map_add' := by
    simp [innerBilinear1]
    intro x y
    ext g; simp; exact InnerProductSpace.add_left x y g
  map_smul' := by
    simp [innerBilinear1]
    intro x y; ext g; simp; rw [inner_smul_left]; simp

-- weak topology Hilbert space
abbrev W (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  := WeakBilin (innerBilin H)

def WeakConverge (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : ℕ → H) (p : H) :=
  Tendsto (x: ℕ → W H) atTop (nhds p : Filter (W H))

def WeakClusterPt (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (p : H) (F : Filter H) := @ClusterPt (W H) _ (p : W H) (F : Filter (W H))


#check WeakClusterPt
#check ClusterPt.mem_closure_of_mem
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (p : H) (F : Filter H)
-- #check WeakClusterPt p F

-- omit [InnerProductSpace ℝ H] in
-- theorem WeakClusterPt.mem_closure_of_mem (h : WeakClusterPt H p F) :
--   ∀ s ∈ F, p ∈ closure s := by
--   apply ClusterPt.mem_closure_of_mem
--   simp [WeakClusterPt] at h
--   exact h

theorem innerBilinear1_add : ∀ x y : H,
  innerBilinear1 H (x + y) = innerBilinear1 H x + innerBilinear1 H y := by
  intro x y
  refine LinearMap.ext_iff.mpr ?_
  intro z
  simp [innerBilinear1]
  exact InnerProductSpace.add_left x y z

theorem innerBilinear1_sub : ∀ x y : H,
  innerBilinear1 H (x - y) = innerBilinear1 H x - innerBilinear1 H y := by
  intro x y
  refine LinearMap.ext_iff.mpr ?_
  intro z
  simp [innerBilinear1]
  exact inner_sub_left x y z

lemma tendsto_iff_weakConverge
  (x : ℕ → H) (p : H) : WeakConverge H x p ↔
  ∀ y : H, Tendsto (fun i ↦ (innerBilin H (x i)) y) atTop (nhds ((innerBilin H p) y)) := by
    simp only [WeakConverge]
    apply tendsto_iff_forall_eval_tendsto
    simp [Function.Injective]
    intro x y hxy
    simp [innerBilin] at hxy
    have h: innerBilinear1 H (x - y) = 0 := by
      rw [innerBilinear1_sub H x y]
      exact sub_eq_zero_of_eq hxy
    have h': innerBilinear1 H (x - y) (x - y) = 0 := by
      simp [h]
    have h''': x - y = (0:H) := by
      simp [innerBilinear1] at h'
      exact h'
    calc
      _ = x - y + y := Eq.symm (sub_add_cancel x y)
      _ = 0 + y := by rw [h''']
      _ = y := zero_add y

theorem weakConverge_iff_inner_converge (x : ℕ → H) (p : H) : WeakConverge H x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫) := tendsto_iff_weakConverge H x p

lemma tendsto_iff_sub_tendsto_zero (x : ℕ → H) (p : H) : Tendsto (fun n ↦ x n) atTop (nhds p)
  ↔ Tendsto (fun n ↦ x n - p) atTop (nhds 0) := by sorry

lemma tendsto_iff_sub_tendsto_zero_inner (x : ℕ → H) (p : H) (y : H) :
  Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫)
  ↔ Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  -- sorry
  have hfun (y : H): (fun n ↦ ⟪x n - p, y⟫) = (fun n ↦ ⟪x n, y⟫ - ⟪p, y⟫) := by sorry
  rw [hfun y]
  constructor
  · intro h
    sorry
    -- apply (tendsto_iff_sub_tendsto_zero H (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).1
    -- exact h
  intro h
  sorry
  -- apply (tendsto_iff_sub_tendsto_zero H (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).2
  -- exact h


theorem weakConverge_iff_inner_converge' (x : ℕ → H) (p : H) : WeakConverge H x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  constructor
  · intro h y
    refine (tendsto_iff_sub_tendsto_zero_inner H x p y).mp ?_
    apply (weakConverge_iff_inner_converge H x p).1 h
  intro h
  rw [weakConverge_iff_inner_converge]
  intro y
  specialize h y
  exact (tendsto_iff_sub_tendsto_zero_inner H x p y).mpr h

#check IsCompact
#check IsSeqCompact
#check IsSeqClosed

def IsWeaklyCompact (s : Set H) := @IsCompact (W H) _ (s : Set (W H))
def IsWeaklySeqClosed (s : Set H) := @IsSeqClosed (W H) _ (s : Set (W H))
def IsWeaklyClosed (s : Set H) := @IsClosed (W H) _ (s : Set (W H))

#check SequentialSpace
-- theorem IsWeaklyClosed_def (s : Set H) : IsWeaklyClosed H s ↔
--   ∀ ⦃x : ℕ → W H⦄ ⦃p : W H⦄,
--   (∀ (n : ℕ), x n ∈ s) → Tendsto x atTop (nhds p) → p ∈ s := by
--   constructor
--   · intro hs
--     exact IsClosed.isSeqClosed hs
--   simp [IsWeaklyClosed]
--   intro h
--   sorry

#check exists_orthonormalBasis

theorem seq_converge_iff_norm_converge (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔ Tendsto (fun n => ‖x n - p‖^2) atTop (nhds 0) := sorry

theorem tsum_tendsto_zero (w : Finset H) (f : {x//x ∈ w} → ℕ → ℝ)
  (h : ∀ i : {x//x ∈ w}, Tendsto (f i) atTop (nhds 0)):
  Tendsto (fun n => ∑ i : {x//x ∈ w}, f i n) atTop (nhds 0) := by sorry

theorem tendsto_norm_congr (x : ℕ → ℝ) (h : Tendsto x atTop (nhds 0)) :
  Tendsto (fun n => ‖x n‖^2) atTop (nhds 0) := by sorry

theorem finite_weak_converge_iff_converge [FiniteDimensional ℝ H] (x : ℕ → H) (p : H)
  (h : WeakConverge H x p) : Tendsto x atTop (nhds p) := by
    apply (seq_converge_iff_norm_converge H x p).2
    simp [WeakConverge] at h
    obtain ⟨w,b,hb⟩ := exists_orthonormalBasis ℝ H
    have (n:ℕ) := OrthonormalBasis.sum_sq_norm_inner_left b (x n - p)
    have hfuneq: (fun n ↦ ‖x n - p‖ ^ 2) = fun n => ∑ i : {x//x ∈ w},
      ‖inner ℝ (x n - p) (b i)‖ ^ 2 := by
      ext n; symm
      exact this n
    rw [hfuneq]
    apply tsum_tendsto_zero H w (fun i:{x//x ∈ w} => (fun n => ‖inner ℝ (x n - p) (b i)‖ ^ 2))
    intro i
    apply tendsto_norm_congr
    apply (weakConverge_iff_inner_converge' H x p).1
    exact h

theorem strong_converge_then_weak_converge (x : ℕ → H) (p : H)
  (h : Tendsto x atTop (nhds p)) : WeakConverge H x p := by
  apply (weakConverge_iff_inner_converge' H x p).2
  intro y
  have (n:ℕ): ⟪x n - p, y⟫ ≤ ‖x n - p‖ * ‖y‖ := by sorry
  sorry


#check limsup
#check LowerSemicontinuous
#check norm_inner_le_norm
#check Tendsto.norm

-- Left hand side in proof of Lemma 2.42
theorem lim_inner_seq_eq_norm (x : ℕ → H) (p : H) (h : WeakConverge H x p) :
  Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := by
  obtain hw := (weakConverge_iff_inner_converge' H x p).1 h p
  rw [← tendsto_iff_sub_tendsto_zero_inner] at hw
  rwa [real_inner_self_eq_norm_sq p] at hw

#check Real.sSup_le
#check Real.le_sSup_iff
-- #check le_of_tendsto_liminf
-- #check Tendsto.liminf_le
#check le_liminf_iff
#check le_of_forall_pos_le_add
-- #check le_sSup_of_mem
-- Tendsto.le_limsup

#check EReal.tendsto_coe.mp

-- Right hand side of Lemma 2.42
lemma EReal.limit_le_liminf (x y : ℕ → ℝ) (p : ℝ) (h : Tendsto x atTop (nhds p))
  (hxy : ∀ n, x n ≤ y n) : Real.toEReal p ≤ liminf (fun n => Real.toEReal (y n)) atTop := by

  simp [liminf, limsInf]
  let s : Set EReal := {a : EReal | ∃ N, ∀ (n : ℕ), N ≤ n → (a ≤ y n)}
  change p ≤ sSup s
  have h1 : ∀ (ε : ℝ) , ε > 0 → Real.toEReal (p - ε) ∈ s := by
    intro ε hε
    simp [s]
    sorry
  have h2 : ∀ (ε : ℝ) , ε > 0 → p - ε ≤ sSup s := by
    intro ε hε
    apply le_sSup
    exact h1 ε hε
  by_cases hs1 : sSup s = ⊤
  · simp [hs1]
  push_neg at hs1
  have hs2 : sSup s ≠ ⊥ := by
    by_contra!
    rw [this] at h2
    specialize h2 1 (by simp)
    rw [← EReal.coe_sub] at h2
    -- simp at h2
    have : Real.toEReal p = ⊥ := by
      simp at h2
      sorry
    simpa
  lift (sSup s) to ℝ using ⟨hs1,hs2⟩ with d
  rw [EReal.coe_le_coe_iff]
  have h2' : ∀ ε > 0, p - ε ≤ d := by
    intro ε hε
    specialize h2 ε hε
    rwa [← EReal.coe_sub, EReal.coe_le_coe_iff] at h2
  exact le_of_forall_sub_le h2'

-- Lemma 2.42
theorem norm_weakly_lsc (x : ℕ → H) (p : H) (h : WeakConverge H x p) :
  Real.toEReal ‖p‖ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := by
  let x' := fun (n:ℕ) => ⟪x n, p⟫
  let y' := fun (n:ℕ) => ‖x n‖
  apply EReal.limit_le_liminf x' y'
  · sorry
  sorry


-- Lemma 2.51 (i)
theorem weak_converge_limsup_le_iff_strong_converge (x : ℕ → H) (p : H) :
  WeakConverge H x p ∧ limsup (fun n => Real.toEReal ‖x n‖) atTop ≤ Real.toEReal ‖p‖ ↔
  Tendsto x atTop (nhds p) := by
  have : liminf (fun n => ‖x n‖) atTop ≤ limsup (fun n => ‖x n‖) atTop := by
    sorry
  sorry

-- Corollary 2.52
theorem strong_converge_iff_weak_norm_converge (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔
  WeakConverge H x p ∧ Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
  constructor
  · intro h
    constructor
    · exact strong_converge_then_weak_converge H x p h
    exact Tendsto.norm h
  intro ⟨h1,h2⟩
  sorry

/-- Theorem 3.34
Let `C` be a convex subset of `H`. The following statement are equivalent:
1. `C` is weakly sequentially closed.
2. `C` is sequentially closed.
3. `C` is closed.
4. `C` is weakly closed.
-/
-- Theorem 3.34 (i) → (ii)
theorem convex_weakly_seq_closed (s : Set H) (hw : IsWeaklySeqClosed H s) : IsSeqClosed s :=
  fun x p hxn hx => @hw x p hxn ((strong_converge_iff_weak_norm_converge H x p).1 hx).1

-- Theorem 3.34 (ii) ↔ (iii)
#check isSeqClosed_iff_isClosed

section WeakLift
variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
#check WeakBilin.continuous_of_continuous_eval
def WeakLiftmap [CompleteSpace E] [CompleteSpace F] (f : E →L[ℝ] F) : (W E) →L[ℝ] (W F) :=
  { f with
    cont := by
      apply WeakBilin.continuous_of_continuous_eval
      intro y
      simp
      let h2 := (fun a ↦ (innerBilin E a) (f.adjoint y))
      let h1 := fun a:W E ↦ (innerBilin F (f a)) y
      have : h2 = h1 := by
        ext a
        simp [h1,h2]
        simp [innerBilin, innerBilinear1]
        exact ContinuousLinearMap.adjoint_inner_right f a y
      change Continuous h1
      rw [← this]
      simp [h2]
      apply WeakBilin.eval_continuous
  }

noncomputable def toR : W ℝ →ₗ[ℝ] ℝ :=
{ toFun := fun w => w,
  map_add' := by intros a b; rfl,
  map_smul' := by intros r a; rfl }

lemma Cont_toR : Continuous toR := by
  have heq (w : ℝ): toR w = innerBilin ℝ w 1 := by
    simp [innerBilin, innerBilinear1]; rfl
  have : toR.toFun = fun w => innerBilin ℝ w 1 := by
    ext w; exact heq w
  change Continuous toR.toFun
  rw [this]; exact eval_continuous (innerBilin ℝ) 1

noncomputable def ofR : ℝ →ₗ[ℝ] W ℝ :=
{ toFun := fun r => r,
  map_add' := by intros a b; rfl,
  map_smul' := by intros r a; rfl }

noncomputable def weakSpaceLinearEquivR : W ℝ ≃ₗ[ℝ] ℝ :=
{ toLinearMap := toR
  invFun := ofR,
  left_inv := by intro w; cases w; rfl,
  right_inv := by intro r; rfl
}

end WeakLift
#check geometric_hahn_banach_point_closed
#check IsClosed
theorem closed_is_weakly_closed' [CompleteSpace H] (s : Set H) (hs : Convex ℝ s) (hw : IsClosed s) :
  IsWeaklyClosed H s := by
  simp [IsWeaklyClosed]
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
  let f1 : (W H) →L[ℝ] (W ℝ) := WeakLiftmap H ℝ f
  let f1' := weakSpaceLinearEquivR.toLinearMap
  let f2 := f1' ∘ f1
  have feq (x : H): f2 x = f x := rfl
  let U' := f2⁻¹' (Set.Iio u)
  use U'
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
  · refine Continuous.isOpen_preimage ?_ (Set.Iio u) ?_
    · refine Continuous.comp ?_ ?_
      · simp [f1', weakSpaceLinearEquivR]
        exact Cont_toR
      exact ContinuousLinearMap.continuous f1
    exact isOpen_Iio
  exact hxinU'


-- Theorem 3.34 (iv) → (i)
theorem weakly_closed_seq_closed (s : Set H) (hs : IsWeaklyClosed H s) :
   IsWeaklySeqClosed H s := by
  simp [IsWeaklyClosed] at hs
  simp [IsWeaklySeqClosed]
  exact IsClosed.isSeqClosed hs

variable {F : Type*}
-- variable [AddCommMonoid F][Module ℝ F][WeakBilin B F]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

-- local notation ⟪⟫
-- def B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ := fun x y => ⟪x, y⟫
end WeakTopology
