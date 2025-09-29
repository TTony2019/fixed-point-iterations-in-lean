import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2

open WeakBilin Filter

#check WeakDual
#check WeakBilin
-- #check tendsto_iff_forall_eval_tendsto
#check tendsto_iff_forall_eval_tendsto
#check inner
#check ClusterPt
#check mem_closure_iff_clusterPt


-- universe u1
-- variable {H : Type u1}
-- variable [NormedAddCommGroup H] [Module ℝ H] --[InnerProductSpace ℝ H]

-- #check  H →ₗ[ℝ] H →ₗ[ℝ] ℝ
-- #check H → H → ℝ

-- variable (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
-- -- variable (H : WeakBilin B)

-- example (H : WeakBilin B) (x : ℕ → (WeakBilin B)) (p : WeakBilin B) :
--   Filter.Tendsto x atTop (nhds p) ↔
--   ∀ y : WeakBilin B, Filter.Tendsto (fun i ↦ (B (x i)) y) atTop (nhds ((B p) y)) := by
--     apply tendsto_iff_forall_eval_tendsto
--     sorry

-- #check WeakBilin B

section WeakTopology
-- variable {𝕜 : Type*} [RCLike 𝕜]

universe u1
variable {H : Type u1}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def innerBilinear1 (x : H) : H →ₗ[ℝ] ℝ where
  toFun := fun y => @inner ℝ _ _ x y
  map_add' := fun x_2 y ↦ inner_add_right x x_2 y
  map_smul' := fun m x_2 ↦ inner_smul_right_eq_smul x x_2 m

def innerBilin : H →ₗ[ℝ] H →ₗ[ℝ] ℝ where
  toFun := fun x => (innerBilinear1 x)
  map_add' := by
    simp [innerBilinear1]
    intro x y
    ext g; simp; exact InnerProductSpace.add_left x y g
  map_smul' := by
    simp [innerBilinear1]
    intro x y; ext g; simp; rw [inner_smul_left]; simp

#check WeakBilin innerBilin


-- instance : T2Space (WeakBilin innerBilin) := by sorry

#check Function.Injective

-- theorem h : Function.Injective ⇑innerBilin := by sorry

def WeakConverge (x : ℕ → H) (p : H) :=
  Tendsto (x: ℕ → WeakBilin innerBilin) atTop (nhds p : Filter (WeakBilin innerBilin))


  -- ∀ y : H, Tendsto (fun i ↦ (innerBilin (x i)) y) atTop (nhds ((innerBilin p) y))

def WeakClusterPt (p : H) (F : Filter H) :=
  ClusterPt (p : WeakBilin innerBilin) (F : Filter (WeakBilin innerBilin))

-- def WeakClusterPt' (p : WeakBilin innerBilin) (F : Filter (WeakBilin innerBilin)) :=
--   ClusterPt (p : WeakBilin innerBilin) (F : Filter (WeakBilin innerBilin))

#check WeakClusterPt
#check ClusterPt.mem_closure_of_mem
variable (p : H) (F : Filter H)
-- #check WeakClusterPt p F

omit [InnerProductSpace ℝ H] in
theorem WeakClusterPt.mem_closure_of_mem (h : WeakClusterPt p F) :
  ∀ s ∈ F, p ∈ closure s := by
  apply ClusterPt.mem_closure_of_mem
  simp [WeakClusterPt] at h
  exact h

theorem innerBilinear1_add : ∀ x y : H,
  innerBilinear1 (x + y) = innerBilinear1 x + innerBilinear1 y := by
  intro x y
  refine LinearMap.ext_iff.mpr ?_
  intro z
  simp [innerBilinear1]
  exact InnerProductSpace.add_left x y z

theorem innerBilinear1_sub : ∀ x y : H,
  innerBilinear1 (x - y) = innerBilinear1 x - innerBilinear1 y := by
  intro x y
  refine LinearMap.ext_iff.mpr ?_
  intro z
  simp [innerBilinear1]
  exact inner_sub_left x y z

lemma tendsto_iff_weakConverge
  (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H, Tendsto (fun i ↦ (innerBilin (x i)) y) atTop (nhds ((innerBilin p) y)) := by
    simp only [WeakConverge]
    apply tendsto_iff_forall_eval_tendsto
    simp [Function.Injective]
    intro x y hxy
    simp [innerBilin] at hxy
    have h: innerBilinear1 (x - y) = 0 := by
      rw [innerBilinear1_sub x y]
      exact sub_eq_zero_of_eq hxy
    have h': innerBilinear1 (x - y) (x - y) = 0 := by
      simp [h]
    have h''': x - y = (0:H) := by
      simp [innerBilinear1] at h'
      exact h'
    calc
      _ = x - y + y := Eq.symm (sub_add_cancel x y)
      _ = 0 + y := by rw [h''']
      _ = y := zero_add y

theorem weakConverge_iff_inner_converge (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫) := tendsto_iff_weakConverge x p

lemma tendsto_iff_sub_tendsto_zero (x : ℕ → H) (p : H) : Tendsto (fun n ↦ x n) atTop (nhds p)
↔ Tendsto (fun n ↦ x n - p) atTop (nhds 0) := by sorry

theorem weakConverge_iff_inner_converge' (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  -- apply tendsto_iff_sub_tendsto_zero
  have hfun (y : H): (fun n ↦ ⟪x n - p, y⟫) = (fun n ↦ ⟪x n, y⟫ - ⟪p, y⟫) := by sorry
  constructor
  · intro h y
    rw [hfun y]
    apply (tendsto_iff_sub_tendsto_zero (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).1
    apply (weakConverge_iff_inner_converge x p).1 h
  intro h
  rw [weakConverge_iff_inner_converge]
  intro y
  specialize h y
  rwa [tendsto_iff_sub_tendsto_zero, ← hfun y]

#check IsCompact
#check IsSeqCompact
#check IsSeqClosed

def IsWeaklyCompact (s : Set H) := IsCompact (s : Set (WeakBilin innerBilin))
def IsWeaklySeqClosed (s : Set H) := IsSeqClosed (s : Set (WeakBilin innerBilin))


#check exists_orthonormalBasis

theorem seq_converge_iff_norm_converge (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔ Tendsto (fun n => ‖x n - p‖^2) atTop (nhds 0) := sorry

theorem tsum_tendsto_zero (w : Finset H) (f : {x//x ∈ w} → ℕ → ℝ)
  (h : ∀ i : {x//x ∈ w}, Tendsto (f i) atTop (nhds 0)):
  Tendsto (fun n => ∑ i : {x//x ∈ w}, f i n) atTop (nhds 0) := by sorry

theorem tendsto_norm_congr (x : ℕ → ℝ) (h : Tendsto x atTop (nhds 0)) :
  Tendsto (fun n => ‖x n‖^2) atTop (nhds 0) := by sorry

theorem finite_weak_converge_iff_converge [FiniteDimensional ℝ H] (x : ℕ → H) (p : H)
  (h : WeakConverge x p) : Tendsto x atTop (nhds p) := by
    apply (seq_converge_iff_norm_converge x p).2
    simp [WeakConverge] at h
    obtain ⟨w,b,hb⟩ := exists_orthonormalBasis ℝ H
    have (n:ℕ) := OrthonormalBasis.sum_sq_norm_inner_left b (x n - p)
    have hfuneq: (fun n ↦ ‖x n - p‖ ^ 2) = fun n => ∑ i : {x//x ∈ w},
      ‖inner ℝ (x n - p) (b i)‖ ^ 2 := by
      ext n; symm
      exact this n
    rw [hfuneq]
    apply tsum_tendsto_zero w (fun i:{x//x ∈ w} => (fun n => ‖inner ℝ (x n - p) (b i)‖ ^ 2))
    intro i
    apply tendsto_norm_congr
    apply (weakConverge_iff_inner_converge' x p).1
    exact h

variable {F : Type*}
-- variable [AddCommMonoid F][Module ℝ F][WeakBilin B F]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

-- local notation ⟪⟫
-- def B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ := fun x y => ⟪x, y⟫
end WeakTopology
