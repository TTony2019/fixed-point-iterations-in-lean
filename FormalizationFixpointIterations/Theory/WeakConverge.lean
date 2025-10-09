import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

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
#check closure
#check nhds
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

#check tendsto_sub_nhds_zero_iff




omit [InnerProductSpace ℝ H] in--意思是这里的证明没有用到内积的性质，所以在这里直接忽略内积也能证明
lemma tendsto_iff_sub_tendsto_zero (x : ℕ → H) (p : H) : Tendsto (fun n ↦ x n) atTop (nhds p)
  ↔ Tendsto (fun n ↦ x n - p) atTop (nhds 0) := by
  exact Iff.symm tendsto_sub_nhds_zero_iff







lemma tendsto_iff_sub_tendsto_zero_inner (x : ℕ → H) (p : H) (y : H) :
  Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫)
  ↔ Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  have hfun (y : H): (fun n ↦ ⟪x n - p, y⟫) = (fun n ↦ ⟪x n, y⟫ - ⟪p, y⟫) := by
    ext n
    simp [inner_sub_left]
  rw [hfun y]
  constructor
  · intro h
    apply (tendsto_iff_sub_tendsto_zero (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).1
    exact h
  intro h
  apply (tendsto_iff_sub_tendsto_zero (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).2
  exact h


theorem weakConverge_iff_inner_converge' (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  constructor
  · intro h y
    refine (tendsto_iff_sub_tendsto_zero_inner x p y).mp ?_
    apply (weakConverge_iff_inner_converge x p).1 h
  intro h
  rw [weakConverge_iff_inner_converge]
  intro y
  specialize h y
  exact (tendsto_iff_sub_tendsto_zero_inner x p y).mpr h

#check IsCompact
#check IsSeqCompact
#check IsSeqClosed

def IsWeaklyCompact (s : Set H) :=
  @IsCompact (WeakBilin innerBilin) _ (s : Set (WeakBilin innerBilin))
-- def IsWeaklySeqClosed (s : Set H) := IsSeqClosed (s : Set (WeakBilin innerBilin))
def IsWeaklySeqClosed (s : Set H) :=
  @IsSeqClosed (WeakBilin innerBilin) _ (s : Set (WeakBilin innerBilin))
def IsWeaklyClosed (s : Set H) :=
  @IsClosed (WeakBilin innerBilin) _ (s : Set (WeakBilin innerBilin))

#check exists_orthonormalBasis



omit [InnerProductSpace ℝ H] in
theorem seq_converge_iff_norm_converge (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔ Tendsto (fun n => ‖x n - p‖^2) atTop (nhds 0) := by
  constructor
  · intro h
    rw [tendsto_iff_sub_tendsto_zero] at h
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    use N
    intro n hn
    specialize hN n hn
    simp [dist] at *
    refine Real.sq_lt.mpr ?_
    constructor
    · have nonneg : 0 ≤ ‖x n - p‖ := by
        exact norm_nonneg (x n - p)
      have lt: -√ε < 0 := by linarith
      exact lt_of_le_of_lt' nonneg lt
    exact hN
  intro h
  rw [tendsto_iff_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
  use N
  intro n hn
  specialize hN n hn
  simp [dist] at *
  apply Real.sq_lt.mp at hN
  rcases hN with ⟨h1, h2⟩
  have:√(ε ^ 2) = ε := by
    rw [Real.sqrt_sq hε.le]
  rw [this] at h2
  exact h2




omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem tsum_tendsto_zero (w : Finset H) (f : {x//x ∈ w} → ℕ → ℝ)
  (h : ∀ i : {x//x ∈ w}, Tendsto (f i) atTop (nhds 0)):
  Tendsto (fun n => ∑ i : {x//x ∈ w}, f i n) atTop (nhds 0) := by
  have h_sum : Tendsto (fun n => ∑ i : {x//x ∈ w}, f i n) atTop
    (nhds (∑ i : {x//x ∈ w}, (0 : ℝ))) := by
    apply tendsto_finset_sum
    intro i _
    exact h i
  simp only [Finset.sum_const_zero] at h_sum
  exact h_sum




#check IsOpen



theorem tendsto_norm_congr (x : ℕ → ℝ) (h : Tendsto x atTop (nhds 0)) :
  Tendsto (fun n => ‖x n‖^2) atTop (nhds 0) := by
  convert (seq_converge_iff_norm_converge x 0).mp h
  simp

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

theorem strong_converge_then_weak_converge (x : ℕ → H) (p : H)
  (h : Tendsto x atTop (nhds p)) : WeakConverge x p := by
  rw [weakConverge_iff_inner_converge]
  intro y
  have hy : Tendsto (fun _ : ℕ => y) atTop (nhds y) := tendsto_const_nhds
  simpa using (Filter.Tendsto.inner (𝕜:=ℝ) (E:=H) h hy)




#check limsup
#check LowerSemicontinuous
#check norm_inner_le_norm
#check Tendsto.norm

-- Left hand side in proof of Lemma 2.42
theorem lim_inner_seq_eq_norm (x : ℕ → H) (p : H) (h : WeakConverge x p) :
  Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := by
  obtain hw := (weakConverge_iff_inner_converge' x p).1 h p
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
--此处Real.toEReal是把实数拓展到了包含无限的扩展实数上
lemma EReal.limit_le_liminf (x y : ℕ → ℝ) (p : ℝ) (h : Tendsto x atTop (nhds p))
  (hxy : ∀ n, x n ≤ y n) : Real.toEReal p ≤ liminf (fun n => Real.toEReal (y n)) atTop := by
  simp [liminf, limsInf]
  let s : Set EReal := {a : EReal | ∃ N, ∀ (n : ℕ), N ≤ n → (a ≤ y n)}
  change p ≤ sSup s
  have h1 : ∀ (ε : ℝ) , ε > 0 → Real.toEReal (p - ε) ∈ s := by
    intro ε hε
    simp [s]
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε  -- 从 Tendsto 得到 ε-N 条件
    use N
    intro n hn
    specialize hN n hn  -- hN: |x n - p| < ε
    rw [Real.dist_eq] at hN  -- |x n - p| < ε，即 p - ε < x n < p + ε
    have p_lt_xn : p - ε < x n := by
      exact sub_lt_of_abs_sub_lt_left hN
    have xn_lt_yn : x n ≤ y n := hxy n  -- 从假设 hxy: ∀ n, x n ≤ y n
    have : p - ε < y n := by linarith
    rw [← EReal.coe_lt_coe_iff] at this
    exact le_of_lt this
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
    simp at h2
    exact EReal.coe_ne_bot (p - 1) h2
  lift (sSup s) to ℝ using ⟨hs1,hs2⟩ with d
  rw [EReal.coe_le_coe_iff]
  have h2' : ∀ ε > 0, p - ε ≤ d := by
    intro ε hε
    specialize h2 ε hε
    rwa [← EReal.coe_sub, EReal.coe_le_coe_iff] at h2
  exact le_of_forall_sub_le h2'

-- Lemma 2.42
theorem norm_weakly_lsc (x : ℕ → H) (p : H) (h : WeakConverge x p) :
  Real.toEReal ‖p‖ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := by
  let x' := fun (n:ℕ) => ⟪x n, p⟫
  let y' := fun (n:ℕ) => ‖x n‖
  apply EReal.limit_le_liminf x' y'
  · sorry
  sorry


-- Lemma 2.51 (i)
theorem weak_converge_limsup_le_iff_strong_converge (x : ℕ → H) (p : H) :
  WeakConverge x p ∧ limsup (fun n => Real.toEReal ‖x n‖) atTop ≤ Real.toEReal ‖p‖ ↔
  Tendsto x atTop (nhds p) := by
  have : liminf (fun n => ‖x n‖) atTop ≤ limsup (fun n => ‖x n‖) atTop := by
    sorry
  sorry

-- Corollary 2.52
theorem strong_converge_iff_weak_norm_converge (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔
  WeakConverge x p ∧ Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
  constructor
  · intro h
    constructor
    · exact strong_converge_then_weak_converge x p h
    exact Tendsto.norm h
  intro ⟨h1,h2⟩
  sorry

-- Theorem 3.34 (i) → (ii)
theorem convex_weakly_seq_closed (s : Set H) (hw : IsWeaklySeqClosed s) : IsSeqClosed s :=
  fun x p hxn hx => @hw x p hxn ((strong_converge_iff_weak_norm_converge x p).1 hx).1

-- Theorem 3.34 (ii) ↔ (iii)
#check isSeqClosed_iff_isClosed

-- Theorem 3.34 (iii) → (iv), needs the definition of projection operator
theorem closed_is_weakly_closed (s : Set H) (hs : Convex ℝ s) (hw : IsClosed s) :
  IsWeaklyClosed s := by sorry

-- Theorem 3.34 (iv) → (i)
theorem weakly_closed_seq_closed (s : Set H) (hs : IsWeaklyClosed s) : IsWeaklySeqClosed s := by
  simp [IsWeaklyClosed] at hs
  simp [IsWeaklySeqClosed]
  exact IsClosed.isSeqClosed hs

variable {F : Type*}
-- variable [AddCommMonoid F][Module ℝ F][WeakBilin B F]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

-- local notation ⟪⟫
-- def B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ := fun x y => ⟪x, y⟫
end WeakTopology
