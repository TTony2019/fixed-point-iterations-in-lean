/-
Copyright (c) 2025 Yifan Bai, Yantao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yifan Bai, Yantao Li
-/
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import FormalizationFixpointIterations.Theory.InnerProductSpace.liminf

open Filter Metric Topology Function TopologicalSpace WeakBilin

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

section topDualPairing

/--
The inner product is left continuous.
-/
def cont_inner_left (a : H) : H →L[ℝ] ℝ where
  toFun := fun x => ⟪x, a⟫
  map_add' := by
    intro x y
    simp [inner_add_left]
  map_smul' := by
    intro c x
    simp [inner_smul_left]

/--
The flip of the topological dual pairing is injective.
-/
lemma topDualPairing_is_injective : Function.Injective ⇑(topDualPairing ℝ H).flip := by
  simp [Function.Injective]
  intro a b hab
  have h1 : ⟪a, a⟫ = ⟪b, a⟫ := by
    change cont_inner_left a a = cont_inner_left a b
    rw [← topDualPairing_apply, ← topDualPairing_apply, ← LinearMap.flip_apply]
    nth_rw 2 [← LinearMap.flip_apply]; rw [← hab]
  have h2 : ⟪a, b⟫ = ⟪b, b⟫ := by
    change cont_inner_left b a = cont_inner_left b b
    rw [← topDualPairing_apply, ← topDualPairing_apply, ← LinearMap.flip_apply]
    nth_rw 2 [← LinearMap.flip_apply]; rw [← hab]
  have : a - b = 0 := by
    have h1': ⟪a - b, a⟫ = 0 := calc
      _ = ⟪a ,a⟫ - ⟪b, a⟫ := by apply inner_sub_left a b a
      _ = ⟪a, a⟫ - ⟪a, a⟫ := by rw [h1]
      _ = 0 := by simp
    have h2': ⟪a - b, b⟫ = 0 := calc
      _ = ⟪a, b⟫ - ⟪b, b⟫ := by apply inner_sub_left a b b
      _ = ⟪a, b⟫ - ⟪a, b⟫ := by rw [h2]
      _ = 0 := by simp
    apply (@inner_self_eq_zero ℝ H _ _ _ (a - b)).1
    calc
      _ = ⟪a - b, a⟫ - ⟪a - b, b⟫ := inner_sub_right (a - b) a b
      _ = 0 - 0 := by rw [h1', h2']
      _ = 0 := by simp
  calc
    _ = a - b + b := Eq.symm (sub_add_cancel a b)
    _ = 0 + b := by rw [this]
    _ = b := by simp

theorem topDualPairing_eq (p : H) : ∀ y : H →L[ℝ] ℝ, (topDualPairing ℝ H).flip p y = y p := by
  simp [LinearMap.flip_apply, topDualPairing_apply]

theorem topDualPairing_strong_dual [CompleteSpace H] (p : H) : ∀ y : H →L[ℝ] ℝ,
  (topDualPairing ℝ H).flip p y = ⟪(InnerProductSpace.toDual ℝ H).symm y, p⟫ := by
  simp [LinearMap.flip_apply, topDualPairing_apply]

theorem topDualPairing_eq_inner [CompleteSpace H] (x y : H) :
  (topDualPairing ℝ H).flip x ((cont_inner_left y)) = ⟪x, y⟫ := by
  rw [topDualPairing_eq]; simp [cont_inner_left]

theorem topDualPairing_strong_dual_seq [CompleteSpace H] (x : ℕ → H) : ∀ y : H →L[ℝ] ℝ,
  (fun n ↦ ((topDualPairing ℝ H).flip (x n)) y) =
  fun n => ⟪(InnerProductSpace.toDual ℝ H).symm y, x n⟫ := by
  intro y; ext n
  exact topDualPairing_strong_dual (x n) y

end topDualPairing

section WeakConverge

/--
Definition: Weak convergence in an inner product space.
-/
def WeakConverge (x : ℕ → H) (p : H) :=
  Tendsto (x: ℕ → WeakSpace ℝ H) atTop (nhds p : Filter (WeakSpace ℝ H))

theorem h (x : ℕ → H) (p : H) : WeakConverge x p ↔
  Tendsto (toWeakSpace ℝ H ∘ x) atTop (nhds (toWeakSpace ℝ H p)) := by
  rfl

theorem weakConverge_iff_inner_converge_pre (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H →L[ℝ] ℝ, Tendsto (fun n ↦ (topDualPairing ℝ H).flip (x n) y)
    atTop (nhds ((topDualPairing ℝ H).flip p y)) := by
  simp [WeakConverge]
  apply tendsto_iff_forall_eval_tendsto
  exact topDualPairing_is_injective

theorem weakConverge_iff_inner_converge [CompleteSpace H] (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H, Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫) := by
  constructor
  · intro h y; rw [weakConverge_iff_inner_converge_pre] at h; specialize h (cont_inner_left y)
    simp [topDualPairing_apply, cont_inner_left] at h; exact h
  intro h; rw [weakConverge_iff_inner_converge_pre]; intro y
  let yf := (InnerProductSpace.toDual ℝ H).symm y
  rw [topDualPairing_strong_dual, topDualPairing_strong_dual_seq]
  have : (fun n ↦ inner ℝ ((InnerProductSpace.toDual ℝ H).symm y) (x n)) =
    (fun n ↦ inner ℝ  (x n) ((InnerProductSpace.toDual ℝ H).symm y)) := by
    ext n; rw [real_inner_comm]
  rw [real_inner_comm, this]; apply h

omit [InnerProductSpace ℝ H] in
lemma tendsto_iff_sub_tendsto_zero {G : Type*} [NormedAddCommGroup G]
  (x : ℕ → G) (p : G) : Tendsto x atTop (nhds p)
  ↔ Tendsto (fun n ↦ x n - p) atTop (nhds 0) := Iff.symm tendsto_sub_nhds_zero_iff

lemma tendsto_iff_sub_tendsto_zero_inner (x : ℕ → H) (p : H) (y : H) :
  Tendsto (fun n ↦ ⟪x n, y⟫) atTop (nhds ⟪p, y⟫)
  ↔ Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  have hfun (y : H): (fun n ↦ ⟪x n - p, y⟫) = (fun n ↦ ⟪x n, y⟫ - ⟪p, y⟫) := by
    ext n; simp [inner_sub_left]
  rw [hfun y]
  constructor
  · exact fun h => (tendsto_iff_sub_tendsto_zero (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).1 h
  exact fun h => (tendsto_iff_sub_tendsto_zero (fun n ↦ ⟪x n, y⟫) ⟪p, y⟫).2 h

theorem weakConverge_iff_inner_converge' [CompleteSpace H] (x : ℕ → H) (p : H) :
  WeakConverge x p ↔ ∀ y : H, Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  constructor
  · intro h y
    refine (tendsto_iff_sub_tendsto_zero_inner x p y).mp ?_
    apply (weakConverge_iff_inner_converge x p).1 h
  intro h; rw [weakConverge_iff_inner_converge]; intro y
  specialize h y; exact (tendsto_iff_sub_tendsto_zero_inner x p y).mpr h


-- Left hand side in proof of Lemma 2.42
theorem lim_inner_seq_eq_norm [CompleteSpace H] (x : ℕ → H) (p : H) (h : WeakConverge x p) :
  Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := by
  obtain hw := (weakConverge_iff_inner_converge' x p).1 h p
  rw [← tendsto_iff_sub_tendsto_zero_inner] at hw
  rwa [real_inner_self_eq_norm_sq p] at hw

end WeakConverge

section FiniteDimensional

omit [InnerProductSpace ℝ H] in
theorem seq_converge_iff_norm_converge {G : Type*} [NormedAddCommGroup G] (x : ℕ → G) (p : G) :
  Tendsto x atTop (nhds p) ↔ Tendsto (fun n => ‖x n - p‖^2) atTop (nhds 0) := by
  constructor
  · intro h; rw [tendsto_iff_sub_tendsto_zero] at h; rw [Metric.tendsto_atTop]
    intro ε hε; rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h (Real.sqrt ε) (Real.sqrt_pos.mpr hε); use N; intro n hn
    specialize hN n hn; simp [dist] at *; refine Real.sq_lt.mpr ?_
    constructor
    · have nonneg : 0 ≤ ‖x n - p‖ := norm_nonneg (x n - p)
      have lt: -√ε < 0 := by linarith
      exact lt_of_le_of_lt' nonneg lt
    exact hN
  intro h; rw [tendsto_iff_sub_tendsto_zero, Metric.tendsto_atTop]; intro ε hε
  rw [Metric.tendsto_atTop] at h; obtain ⟨N, hN⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
  use N; intro n hn; specialize hN n hn; simp [dist] at *; apply Real.sq_lt.mp at hN
  rcases hN with ⟨h1, h2⟩
  have:√(ε ^ 2) = ε := by rw [Real.sqrt_sq hε.le]
  rwa [this] at h2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem tsum_tendsto_zero (w : Finset H) (f : {x//x ∈ w} → ℕ → ℝ)
  (h : ∀ i : {x//x ∈ w}, Tendsto (f i) atTop (nhds 0)):
  Tendsto (fun n => ∑ i : {x//x ∈ w}, f i n) atTop (nhds 0) := by
  have h_sum : Tendsto (fun n => ∑ i : {x//x ∈ w}, f i n) atTop
    (nhds (∑ i : {x//x ∈ w}, (0 : ℝ))) := by
    apply tendsto_finset_sum; exact fun i a ↦ h i
  simp only [Finset.sum_const_zero] at h_sum; exact h_sum

theorem tendsto_norm_congr (x : ℕ → ℝ) (h : Tendsto x atTop (nhds 0)) :
  Tendsto (fun n => ‖x n‖^2) atTop (nhds 0) := by
  rw[← sub_zero x]; exact (seq_converge_iff_norm_converge x 0).mp h

theorem finite_weak_converge_iff_converge [FiniteDimensional ℝ H] (x : ℕ → H) (p : H)
  (h : WeakConverge x p) : Tendsto x atTop (nhds p) := by
  apply (seq_converge_iff_norm_converge x p).2
  simp [WeakConverge] at h
  obtain ⟨w,b,hb⟩ := exists_orthonormalBasis ℝ H
  have (n:ℕ) := OrthonormalBasis.sum_sq_norm_inner_left b (x n - p)
  have hfuneq: (fun n ↦ ‖x n - p‖ ^ 2) = fun n => ∑ i : {x//x ∈ w},
    ‖inner ℝ (x n - p) (b i)‖ ^ 2 := by
    ext n; symm; exact this n
  rw [hfuneq]
  apply tsum_tendsto_zero w (fun i:{x//x ∈ w} => (fun n => ‖inner ℝ (x n - p) (b i)‖ ^ 2))
  intro i; apply tendsto_norm_congr; apply (weakConverge_iff_inner_converge' x p).1; exact h

theorem strong_converge_then_weak_converge [CompleteSpace H] (x : ℕ → H) (p : H)
  (h : Tendsto x atTop (nhds p)) : WeakConverge x p := by
  rw [weakConverge_iff_inner_converge]
  intro y
  have hy : Tendsto (fun _ : ℕ => y) atTop (nhds y) := tendsto_const_nhds
  simpa using (Filter.Tendsto.inner (𝕜:=ℝ) (E:=H) h hy)

end FiniteDimensional


section WeakConvergeBounded

-- def fn_norm : ℕ → H →L[ℝ] ℝ := fun n =>
-- def xn_inner (p : H) : H →ₛₗ[ℝ] ℝ where
--   toFun := fun z => ⟪p, z⟫
--   map_add' := fun u v => inner_add_right p u v
--   map_smul' := fun c u => inner_smul_right p u c

/--
The norm of a weakly convergent sequence is bounded.
-/
theorem weakly_converge_norm_bounded [CompleteSpace H]
  (x : ℕ → H) (p : H) (h_wkconv_x : WeakConverge x p) : ∃ M, ∀ n, ‖x n‖ ≤ M := by
  let f : ℕ → H →L[ℝ] ℝ := fun n => LinearMap.mkContinuous
      { toFun := fun z => ⟪x n, z⟫
        map_add' := fun u v => inner_add_right (x n) u v
        map_smul' := fun c u => inner_smul_right (x n) u c} ‖x n‖
        fun z => by simp; exact abs_real_inner_le_norm (x n) z
  have h_f_n_y_upbd : ∀ y : H, ∃ N : ℕ, ∃ M : ℝ, ∀ n ≥ N, |f n y| ≤ M := by
    intro y; rw [weakConverge_iff_inner_converge] at h_wkconv_x
    specialize h_wkconv_x y; rw [Metric.tendsto_atTop] at h_wkconv_x
    specialize h_wkconv_x (1) (one_pos)
    obtain ⟨N, hN⟩ := h_wkconv_x; use N, |⟪p, y⟫| + 1
    intro n hn; specialize hN n hn; simp [f]
    rw [Real.dist_eq] at hN
    have : |inner ℝ (x n) y| - |inner ℝ p y| < 1 := by
      calc
        _ ≤ |inner ℝ (x n) y - inner ℝ p y| := by apply abs_sub_abs_le_abs_sub
        _ < 1 := hN
    linarith
  have h_f_n_y_pointwise_bounded : ∀ y : H, ∃ M : ℝ, ∀ n : ℕ, |f n y| ≤ M := by
    intro y; specialize h_f_n_y_upbd y; obtain ⟨N, hN⟩ := h_f_n_y_upbd
    by_cases N_zero : N = 0
    · rw [N_zero] at hN; rcases hN with ⟨M, hM⟩; use M; intro n; exact hM n (Nat.zero_le n)
    · let M0 := (Finset.range N).sup' ⟨0, Finset.mem_range.mpr
        (Nat.pos_of_ne_zero ‹N ≠ 0›)⟩ (fun n => |(f n) y|)
      have ha : ∀ a ∈ Finset.range N, |(f a) y| ≤ M0 := by
        intro a ha; simp [M0]; use a
        constructor
        · exact List.mem_range.mp ha
        · simp
      rcases hN with ⟨M1, hM1⟩; use max M0 M1; intro n
      by_cases hn : n < N
      · calc
          _ ≤ M0 := by apply ha n; exact Finset.mem_range.mpr hn
          _ ≤ max M0 M1 := by apply le_max_left
      · push_neg at hn
        calc
          _ ≤ M1 := by apply hM1; exact hn
          _ ≤ max M0 M1 := by apply le_max_right
  have h_norm_sup_t_n_y : ∀ y : H, ∃ M : ℝ, ⨆ n : ℕ, |f n y| ≤ M := by
    intro y; rcases h_f_n_y_pointwise_bounded y with ⟨M, hM⟩; use M; exact ciSup_le hM
  have h_f_bounded : ∃ C, ∀ n, ‖f n‖ ≤ C := by
    have h_pointwise : ∀ y, ∃ M, ∀ n, |f n y| ≤ M := by intro y; exact h_f_n_y_pointwise_bounded y
    exact banach_steinhaus h_pointwise
  obtain ⟨C, hC⟩ := h_f_bounded; use C; intro n
  have h_norm_eq : ‖f n‖ = ‖x n‖ := by
    refine ContinuousLinearMap.opNorm_eq_of_bounds (by simp) ?_ ?_
    · intro z; simp [f]; exact abs_real_inner_le_norm (x n) z
    · intro M hM h; simp [f] at h; specialize h (x n)
      rw [abs_of_nonneg] at h
      · rw [real_inner_self_eq_norm_sq, pow_two] at h
        have : ‖x n‖ ≥ 0 := norm_nonneg (x n)
        by_cases h1: ‖x n‖ = 0
        · rw [h1]; assumption
        · push_neg at h1
          have : ‖x n‖ > 0 := by
            apply lt_of_le_of_ne this ?_
            intro h2; rw [h2] at h1; contradiction
          exact le_of_mul_le_mul_right h this
      · exact real_inner_self_nonneg
  rw [← h_norm_eq]; exact hC n

end WeakConvergeBounded

/--
Lemma 2.42 : `‖p‖ ≤ liminf ‖x n‖` if `x n` weakly converges to `p`.
-/
theorem norm_weakly_lsc [CompleteSpace H] (x : ℕ → H) (p : H) (h : WeakConverge x p) :
  Real.toEReal ‖p‖ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := by
  let x' := fun ( n : ℕ ) => ⟪x n, p⟫
  let y' := fun ( n : ℕ ) => ‖x n‖ * ‖p‖
  have hxy : ∀ n, x' n ≤ y' n := by
    intro n; exact real_inner_le_norm (x n) p
  have h1 : Tendsto x' atTop (nhds (‖p‖ ^ 2)) := lim_inner_seq_eq_norm x p h
  have nonneg1 : Real.toEReal ‖p‖ ≥ 0 := EReal.coe_nonneg.mpr (norm_nonneg p)
  have nonneg2 : ∀ n, Real.toEReal ‖x n‖ ≥ 0 := fun n ↦ EReal.coe_nonneg.mpr (norm_nonneg (x n))
  by_cases hp1 : Real.toEReal ‖p‖ = 0
  · simp [hp1]
    calc
      _ = liminf (fun n ↦ (0 : EReal)) atTop := by
        symm; apply @Filter.liminf_const EReal ℕ _ atTop _ (Real.toEReal 0)
      _ ≤ liminf (fun n ↦ Real.toEReal ‖x n‖) atTop := by
        apply liminf_le_liminf
        · apply Eventually.of_forall; intro n; simp
        · simp [autoParam, IsBoundedUnder, IsBounded]; use 0; use 0; intro n; simp
        · simp [autoParam]
          apply Filter.IsBoundedUnder.isCoboundedUnder_ge; simp [IsBoundedUnder, IsBounded]
          have ⟨M, hM⟩ : ∃ M, ∀ n, ‖x n‖ ≤ M := weakly_converge_norm_bounded x p h
          use M, 0; intro b_1 _; simp; exact hM b_1
  · have hp2 : Real.toEReal ‖p‖ ≠ ⊥ := by simp
    have hp3 : Real.toEReal ‖p‖ ≠ ⊤ := by simp
    push_neg at hp1
    have h_lim : Real.toEReal (‖p‖ ^ 2) ≤ liminf (fun n => Real.toEReal (y' n)) atTop :=
      EReal.limit_le_liminf x' y' (‖p‖ ^ 2) h1 hxy
    simp [y'] at h_lim
    have h2 : liminf (fun n ↦ Real.toEReal ‖x n‖ * Real.toEReal ‖p‖) atTop
      = (liminf (fun n ↦ Real.toEReal ‖x n‖) atTop) * Real.toEReal ‖p‖ := by
      apply EReal.liminf_mul_const x p
    rw [h2] at h_lim
    have p_norm_eq : Real.toEReal (‖p‖ * ‖p‖)  = Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by
      rw [← EReal.coe_mul]
    have eq: ‖p‖^2 = ‖p‖ * ‖p‖ := by linarith
    have eq': Real.toEReal (‖p‖ ^ 2) = Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by rw [eq, p_norm_eq]
    have : Real.toEReal ‖p‖ * Real.toEReal ‖p‖
      ≤ liminf (fun n ↦ Real.toEReal ‖x n‖) atTop * Real.toEReal ‖p‖ := by
      calc
        _ = Real.toEReal (‖p‖ ^ 2) := by rw [eq']
        _ ≤ liminf (fun n => Real.toEReal (y' n)) atTop := by convert h_lim
        _ = liminf (fun n => Real.toEReal (‖x n‖ * ‖p‖)) atTop := by simp [y']
        _ = liminf (fun n => Real.toEReal ‖x n‖ * Real.toEReal ‖p‖ ) atTop := by congr
        _ = liminf (fun n ↦ Real.toEReal ‖x n‖) atTop * Real.toEReal ‖p‖ := by rw [← h2]
    calc
      _ = Real.toEReal ‖p‖ / Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by
        symm; apply EReal.div_mul_cancel hp2 hp3 hp1
      _ = Real.toEReal ‖p‖ * Real.toEReal ‖p‖ / Real.toEReal ‖p‖ := by apply EReal.mul_div_right
      _ ≤ liminf (fun n ↦ ↑‖x n‖) atTop * Real.toEReal ‖p‖ / Real.toEReal ‖p‖ := by
        apply EReal.div_le_div_right_of_nonneg nonneg1 this
      _ = liminf (fun n ↦ ↑‖x n‖) atTop / Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by
        symm; apply EReal.mul_div_right
      _ = liminf (fun n ↦ ↑‖x n‖) atTop := EReal.div_mul_cancel hp2 hp3 hp1

/--
Lemma 2.51 (i) : ``Tendsto x atTop (nhds p)`` if and only if `WeakConverge x p` and
`limsup ‖x n‖ ≤ ‖p‖`.
-/
theorem weak_converge_limsup_le_iff_strong_converge [CompleteSpace H] (x : ℕ → H) (p : H) :
  WeakConverge x p ∧ limsup (fun n => Real.toEReal ‖x n‖) atTop ≤ Real.toEReal ‖p‖ ↔
  Tendsto x atTop (nhds p) := by
  by_cases upper_bound : ¬ (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
  · push_neg at upper_bound
    constructor
    · rintro ⟨hweak, hlimsup⟩; exfalso
      have hlimsup_top : limsup (fun n => Real.toEReal ‖x n‖) atTop = ⊤ := by
        simp [limsup, limsSup]; intro a N hb; by_contra ha_ne_top; push_neg at ha_ne_top
        by_cases ha_ne_bot : a = ⊥
        · simp [ha_ne_bot] at hb; specialize hb N; simp at hb
        push_neg at ha_ne_bot; lift a to ℝ using ⟨ha_ne_top, ha_ne_bot⟩ with a0
        by_cases hN : N = 0
        · simp [hN] at hb
          obtain ⟨m, hm⟩ := upper_bound (a0 + 1)
          have : ‖x m‖ ≤ a0 := by
            specialize hb m; assumption
          linarith
        · push_neg at hN
          let M1 := Finset.sup' (Finset.range N) (by simp [hN]) (fun k => ‖x k‖)
          let M := max M1 a0
          have hall : ∀ n, ‖x n‖ ≤ M := by
            intro n; by_cases hn : n < N
            · have : ‖x n‖ ≤ M1 := by
                apply Finset.le_sup'_of_le
                · simp [Finset.mem_range]; exact hn
                · exact le_rfl
              exact le_trans this (le_max_left M1 a0)
            · push_neg at hn
              have : Real.toEReal ‖x n‖ ≤ Real.toEReal a0 := hb n hn
              rw [EReal.coe_le_coe_iff] at this; exact le_trans this (le_max_right M1 a0)
          obtain ⟨m, hm⟩ := upper_bound (M + 1); specialize hall m; linarith
      rw [hlimsup_top] at hlimsup; simp at hlimsup
    intro h
    constructor
    · exact strong_converge_then_weak_converge x p h
    rw[Metric.tendsto_atTop] at h; exfalso; specialize h 1 zero_lt_one
    obtain ⟨N, hN⟩ := h
    let x0 := Finset.sup' (Finset.range (N + 1)) (by simp) (fun n ↦ ‖x n‖)
    let M := max (x0 + 1) (‖p‖ + 1)
    obtain ⟨n, hn⟩ := upper_bound M
    have hn_ge : n ≥ N := by
      classical
      by_contra hlt
      have hx0_le : ‖x n‖ ≤ x0 := by
        have hmem : n ∈ Finset.range (N + 1) := by
          have : n < N + 1 := by
            apply Nat.lt_succ_of_lt; push_neg at hlt; exact hlt
          simpa [Finset.mem_range] using this
        exact Finset.le_sup'_of_le (fun k ↦ ‖x k‖) hmem (le_rfl)
      have hcontr : ‖x n‖ ≤ M := by
        calc
          _ ≤ x0 + 1 := by linarith
          _ ≤ M := by apply le_max_left
      exact not_lt_of_ge hcontr hn
    have hdist : dist (x n) p > 1 := by
      have hnorm : ‖x n‖ > ‖p‖ + 1 := lt_of_le_of_lt (le_max_right _ _) hn
      have hbound : ‖x n - p‖ ≥ ‖x n‖ - ‖p‖ := norm_sub_norm_le (x n) p
      have h1: ‖x n‖ - ‖p‖ > 1 := by linarith
      simp [dist_eq_norm]; exact lt_of_lt_of_le h1 hbound
    have hdist' : dist (x n) p ≥ 1 := hdist.le
    have : dist (x n) p < 1 := hN n hn_ge
    exact (not_lt_of_ge hdist') this
  have h: liminf (fun n => Real.toEReal ‖x n‖) atTop
    ≤ limsup (fun n => Real.toEReal ‖x n‖) atTop := by
    push_neg at upper_bound; apply liminf_le_limsup
    · obtain ⟨M, hM⟩ := upper_bound
      have hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
        refine ⟨M, ?_⟩
        have : ∀ᶠ n in atTop, ‖x n‖ ≤ M := by exact Eventually.of_forall hM
        simpa using this
      exact hbounded
    have hbounded : IsBoundedUnder (· ≥ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
      refine ⟨0, ?_⟩
      have : ∀ᶠ n in atTop, 0 ≤ ‖x n‖ := Eventually.of_forall (by intro n; exact norm_nonneg (x n))
      simp
    exact hbounded
  push_neg at upper_bound
  constructor
  · rintro ⟨hweak, hlimsup⟩
    have h' :Real.toEReal ‖p‖ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := by
      apply norm_weakly_lsc; exact hweak
    have eq: limsup (fun n ↦ Real.toEReal ‖x n‖) atTop =
      liminf (fun n ↦ Real.toEReal ‖x n‖) atTop:= by
      apply le_antisymm
      · calc
          _ ≤ Real.toEReal ‖p‖ := hlimsup
          _ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := h'
      · exact h
    have hlim : Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
      apply EReal.tendsto_coe.mp; apply tendsto_of_liminf_eq_limsup
      · rw [eq] at hlimsup
        apply le_antisymm hlimsup h'
      rw[← eq] at h'
      apply le_antisymm hlimsup h'
      · obtain ⟨M, hM⟩ := upper_bound
        have hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
          refine ⟨M, ?_⟩
          have : ∀ᶠ n in atTop, ‖x n‖ ≤ M := by exact Eventually.of_forall hM
          simpa using this
        exact hbounded
      have hbounded : IsBoundedUnder (· ≥ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
        refine ⟨0, ?_⟩
        have : ∀ᶠ n in atTop, 0 ≤ ‖x n‖ :=
          Eventually.of_forall (by intro n; exact norm_nonneg (x n))
        simp
      exact hbounded
    have hnorm : Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by simpa using hlim
    have hsub : Tendsto (fun n => x n - p) atTop (nhds 0) := by
      apply (tendsto_iff_sub_tendsto_zero x p).1
      apply (seq_converge_iff_norm_converge x p).2
      have eq2:∀ n, ‖x n - p‖ ^2 = ‖x n‖^2 - 2 * ⟪x n, p⟫ + ‖p‖^2 := by
        intro n; rw [← @norm_sub_sq_real]
      simp only [eq2]
      have h1 : Tendsto (fun n => ‖x n‖^2) atTop (nhds (‖p‖^2)) := by
        simpa [pow_two] using hnorm.mul hnorm
      have h2 : Tendsto (fun n => 2 * ⟪x n, p⟫) atTop (nhds (2 * ‖p‖^2)) := by
        have : Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := lim_inner_seq_eq_norm x p hweak
        simpa using (tendsto_const_nhds (x := (2:ℝ))).mul this
      have h3 : Tendsto (fun n => ‖p‖^2) atTop (nhds (‖p‖^2)) := tendsto_const_nhds (α := ℕ)
      convert h1.sub h2 |>.add h3 using 2; ring
    have hnorm_sq : Tendsto (fun n => ‖x n - p‖ ^ 2) atTop (nhds 0) := by
      have hnorm : Tendsto (fun n => ‖x n - p‖) atTop (nhds 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mp hsub
      simpa [pow_two] using hnorm.mul hnorm
    exact (seq_converge_iff_norm_converge x p).2 hnorm_sq
  intro h'
  constructor
  · exact strong_converge_then_weak_converge x p h'
  have hnorm : Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := Tendsto.norm h'
  have hnorm_ereal : Tendsto (fun n => Real.toEReal ‖x n‖) atTop (nhds (Real.toEReal ‖p‖)) := by
    exact EReal.tendsto_coe.mpr hnorm
  have hlimsup : limsup (fun n => Real.toEReal ‖x n‖) atTop = Real.toEReal ‖p‖ := by
    obtain ⟨M, hM⟩ := upper_bound
    have hbdd_above : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
      refine ⟨M, ((Eventually.of_forall hM).mono (by intro n hn; simpa))⟩
    have hbdd_below : IsBoundedUnder (· ≥ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
      refine ⟨0, ?_⟩; apply Eventually.of_forall (fun (n : ℕ) => ?_); simp
    apply Tendsto.limsup_eq; exact hnorm_ereal
  rw [hlimsup]

/--
Corollary 2.52 : `Tendsto x atTop (nhds p)` if and only if `WeakConverge x p` and
`Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖)`.
-/
theorem strong_converge_iff_weak_norm_converge [CompleteSpace H] (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔
  WeakConverge x p ∧ Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
  constructor
  · intro h
    constructor
    · exact strong_converge_then_weak_converge x p h
    exact Tendsto.norm h
  intro ⟨h1, h2⟩; apply (seq_converge_iff_norm_converge x p).2
  have norm_expand : ∀ n, ‖x n - p‖^2 = ‖x n‖^2 - 2 * ⟪x n, p⟫ + ‖p‖^2 := by
    intro n; rw [← @norm_sub_sq_real]
  simp only [norm_expand]
  have hnorm_sq : Tendsto (fun n => ‖x n‖^2) atTop (nhds (‖p‖^2)) := by
    simpa [pow_two] using h2.mul h2
  have hinner : Tendsto (fun n => 2 * ⟪x n, p⟫) atTop (nhds (2 * ‖p‖^2)) := by
    have : Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := lim_inner_seq_eq_norm x p h1
    simpa using (tendsto_const_nhds (x := (2:ℝ))).mul this
  have hconst : Tendsto (fun n => ‖p‖^2) atTop (nhds (‖p‖^2)) := tendsto_const_nhds (α := ℕ)
  convert hnorm_sq.sub hinner |>.add hconst using 2; ring

/--
For a weakly convergent sequence `x n` converging to `x_lim` and a strongly convergent
sequence `u n` converging to `u_lim`, the inner product sequence `inner ℝ (x n) (u n)`
converges to `inner ℝ x_lim u_lim`.
-/
lemma wkconv_conv_ledsto_conv [CompleteSpace H]
  {x : ℕ → H} {x_lim : H} {u : ℕ → H} {u_lim : H} {h_wkconv_x : WeakConverge x x_lim}
  {h_conv_u : Tendsto u atTop (𝓝 u_lim)}
  : Tendsto (fun n => inner ℝ (x n) (u n)) atTop (𝓝 (inner ℝ x_lim u_lim)) := by
  have eq : (fun n => inner ℝ (x n) (u n) - inner ℝ x_lim u_lim) =
    (fun n => inner ℝ (x n) (u n - u_lim)) + (fun n => inner ℝ (x n - x_lim) u_lim) := by
      funext n; simp [inner_sub_left, inner_sub_right]
  have ⟨M, hM⟩ : ∃ M, ∀ n, ‖x n‖ ≤ M :=
    weakly_converge_norm_bounded x x_lim h_wkconv_x

  have h1: Tendsto (fun n => inner ℝ (x n) (u n - u_lim)) atTop (𝓝 0) := by
    have h_u_diff : Tendsto (fun n => u n - u_lim) atTop (𝓝 0) :=
      (tendsto_iff_sub_tendsto_zero u u_lim).mp h_conv_u
    by_cases M_zero : M = 0
    · have h_xn_zero : ∀ n, x n = 0 := by
        intro n; specialize hM n
        have : ‖x n‖ ≤ 0 := by rw [M_zero] at hM; exact hM
        have h_norm_nonneg : ‖x n‖ ≥ 0 := norm_nonneg (x n)
        exact norm_le_zero_iff.mp this
      rw [Metric.tendsto_atTop]; intro ε ε_pos; use 0; intro n hn; rw [h_xn_zero n]; simpa
    · have h_M_pos : M > 0 := by
        specialize hM 0; push_neg at M_zero
        have h_M_nonneg : M ≥ 0 := by
          calc
            _ ≥ ‖x 0‖ := hM
            _ ≥ 0 := norm_nonneg (x 0)
        exact lt_of_le_of_ne h_M_nonneg (id (Ne.symm M_zero))
      have h_ε_pos_div : ∀ ε > 0, ε / M > 0 := by intros ε ε_pos; exact div_pos ε_pos h_M_pos
      rw [Metric.tendsto_atTop] at h_u_diff ⊢; intro ε ε_pos
      specialize h_u_diff (ε / M) (h_ε_pos_div ε ε_pos); obtain ⟨N, hN⟩ := h_u_diff
      use N; intro n hn; specialize hN n hn; rw [Real.dist_eq]; simp only [sub_zero]
      rw [dist_eq_norm, sub_zero] at hN
      calc
        _ ≤ ‖x n‖ * ‖u n - u_lim‖ := abs_real_inner_le_norm (x n) (u n - u_lim)
        _ ≤ M * ‖u n - u_lim‖ :=
          mul_le_mul (hM n) (by simp) (norm_nonneg (u n - u_lim)) (le_of_lt h_M_pos)
        _ < M * (ε / M) := mul_lt_mul_of_pos_left hN h_M_pos
        _ = ε := by field_simp [ne_of_gt h_M_pos]

  have h2: Tendsto (fun n => inner ℝ (x n - x_lim) u_lim) atTop (𝓝 0) := by
    rw [weakConverge_iff_inner_converge] at h_wkconv_x; specialize h_wkconv_x u_lim
    rw [tendsto_iff_sub_tendsto_zero_inner] at h_wkconv_x; exact h_wkconv_x

  rw [show Tendsto (fun n ↦ inner ℝ (x n) (u n)) atTop (𝓝 (inner ℝ x_lim u_lim))
    ↔ Tendsto (fun n ↦ inner ℝ (x n) (u n) - inner ℝ x_lim u_lim) atTop (𝓝 0) by
  constructor
  · intro h; convert Tendsto.sub h tendsto_const_nhds using 1; ext n; simp
  · intro h
    exact (tendsto_iff_sub_tendsto_zero (fun n ↦ inner ℝ (x n) (u n))
      (inner ℝ x_lim u_lim)).mpr h]
  rw [eq]
  have h_add : Tendsto (fun n => inner ℝ (x n) (u n - u_lim) + inner ℝ (x n - x_lim) u_lim)
    atTop (𝓝 (0 + 0)) := Tendsto.add h1 h2
  convert h_add; simp
