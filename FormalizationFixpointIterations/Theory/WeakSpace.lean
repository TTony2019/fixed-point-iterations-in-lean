import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Compactness.Compact
import FormalizationFixpointIterations.Nonexpansive.Definitions
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.UniformSpace.Ascoli


set_option linter.unusedSectionVars false


open Filter WeakDual Metric WeakBilin Nonexpansive_operator Topology BigOperators Function
open TopologicalSpace

section WeakTopology

-- universe u1
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def WeakConverge (x : ℕ → H) (p : H) :=
  Tendsto (x: ℕ → WeakSpace ℝ H) atTop (nhds p : Filter (WeakSpace ℝ H))

#check continuous_id_of_le
#check tendsto_iff_forall_eval_tendsto
#check LinearMap.flip_inj
#check LinearMap.flip_apply

def va (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a : H) : H →L[ℝ] ℝ where
  toFun := fun x => ⟪x, a⟫
  map_add' := by
    intro x y
    simp [inner_add_left]
  map_smul' := by
    intro c x
    simp [inner_smul_left]

theorem continuous_va (a : H) : Continuous (va H a) := by
  simp [va]
  apply Continuous.inner
  · apply continuous_id
  · apply continuous_const



theorem continuous_va_weak (a : H) :
  @Continuous (WeakSpace ℝ H) ℝ _ _ (va H a) := by
  have h1 : @Continuous (WeakSpace ℝ H) H _ _ (fun (t : WeakSpace ℝ H) => (t : H)) := by
    apply continuous_id_of_le
    sorry
  have h2 : Continuous (fun (x : H) => inner ℝ x a) := by
    apply Continuous.inner
    · apply continuous_id
    · apply continuous_const
  simp [va]
  exact Continuous.comp h2 h1



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
    have h1': ⟪a - b, a⟫ = 0 := by
      calc
        _ = ⟪a ,a⟫ - ⟪b, a⟫ := by apply inner_sub_left a b a
        _ = ⟪a, a⟫ - ⟪a, a⟫ := by rw [h1]
        _ = 0 := by simp
    have h2': ⟪a - b, b⟫ = 0 := by
      calc
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

#check InnerProductSpace.toDual
theorem topDualPairing_eq (p : H) : ∀ y : H →L[ℝ] ℝ, (topDualPairing ℝ H).flip p y = y p := by
  simp [LinearMap.flip_apply, topDualPairing_apply]

theorem topDualPairing_strong_dual [CompleteSpace H] (p : H) : ∀ y : H →L[ℝ] ℝ,
  (topDualPairing ℝ H).flip p y = ⟪(InnerProductSpace.toDual ℝ H).symm y, p⟫  := by
  simp [LinearMap.flip_apply, topDualPairing_apply]

theorem topDualPairing_eq_inner [CompleteSpace H] (x y : H) :
  (topDualPairing ℝ H).flip x ((va H y)) = ⟪x, y⟫  := by
  rw [topDualPairing_eq]
  simp [va]

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

theorem weakConverge_iff_inner_converge_pre (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H →L[ℝ] ℝ, Tendsto (fun n ↦ (topDualPairing ℝ H).flip (x n) y)
    atTop (nhds ((topDualPairing ℝ H).flip p y)) := by
  simp [WeakConverge]
  apply tendsto_iff_forall_eval_tendsto
  exact topDualPairing_is_injective

theorem weakConverge_iff_inner_converge [CompleteSpace H] (x : ℕ → H) (p : H) : WeakConverge x p ↔
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

omit [InnerProductSpace ℝ H] in
@[simp]
lemma tendsto_iff_sub_tendsto_zero {G : Type*} [NormedAddCommGroup G]
  (x : ℕ → G) (p : G) : Tendsto x atTop (nhds p)
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

theorem weakConverge_iff_inner_converge' [CompleteSpace H] (x : ℕ → H) (p : H) :
  WeakConverge x p ↔ ∀ y : H, Tendsto (fun n ↦ ⟪x n - p, y⟫) atTop (nhds 0) := by
  constructor
  · intro h y
    refine (tendsto_iff_sub_tendsto_zero_inner x p y).mp ?_
    apply (weakConverge_iff_inner_converge x p).1 h
  intro h
  rw [weakConverge_iff_inner_converge]
  intro y
  specialize h y
  exact (tendsto_iff_sub_tendsto_zero_inner x p y).mpr h

theorem tendsto_iff_weakConverge [CompleteSpace H]
  (x : ℕ → H) (p : H) : WeakConverge x p ↔
  ∀ y : H, Tendsto (fun i ↦ inner ℝ (x i) y) atTop (nhds (inner ℝ p y)) :=
    weakConverge_iff_inner_converge x p

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

theorem tendsto_norm_congr (x : ℕ → ℝ) (h : Tendsto x atTop (nhds 0)) :
  Tendsto (fun n => ‖x n‖^2) atTop (nhds 0) := by
  rw[← sub_zero x]
  exact (seq_converge_iff_norm_converge x 0).mp h

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

theorem strong_converge_then_weak_converge [CompleteSpace H] (x : ℕ → H) (p : H)
  (h : Tendsto x atTop (nhds p)) : WeakConverge x p := by
  rw [weakConverge_iff_inner_converge]
  intro y
  have hy : Tendsto (fun _ : ℕ => y) atTop (nhds y) := tendsto_const_nhds
  simpa using (Filter.Tendsto.inner (𝕜:=ℝ) (E:=H) h hy)


-- Left hand side in proof of Lemma 2.42
theorem lim_inner_seq_eq_norm [CompleteSpace H] (x : ℕ → H) (p : H) (h : WeakConverge x p) :
  Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := by
  obtain hw := (weakConverge_iff_inner_converge' x p).1 h p
  rw [← tendsto_iff_sub_tendsto_zero_inner] at hw
  rwa [real_inner_self_eq_norm_sq p] at hw

-- Right hand side of Lemma 2.42
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


lemma EReal.liminf_mul_const (x : ℕ → H) (p : H) :
  liminf (fun n ↦ Real.toEReal (‖x n‖ * ‖p‖)) atTop
  = (liminf (fun n ↦ Real.toEReal ‖x n‖) atTop) * Real.toEReal ‖p‖ := by
  by_cases hp : Real.toEReal ‖p‖ = 0
  · simp [hp]
  · apply le_antisymm
    · calc
        _ = liminf (fun n ↦ ((Real.toEReal ‖p‖) * (Real.toEReal ‖x n‖))) atTop := by
          simp [mul_comm]
        _ ≤ (limsup (fun n ↦ Real.toEReal ‖p‖) atTop) *
          liminf (fun n ↦ Real.toEReal ‖x n‖) atTop := by
          apply EReal.liminf_mul_le
          · apply Eventually.of_forall
            intro n
            simp
          · apply Eventually.of_forall
            intro n
            simp
          · left
            push_neg at hp
            simp at hp
            simpa
          · left
            simp
        _ = ↑‖p‖ * liminf (fun n ↦ ↑‖x n‖) atTop := by
          simp
        _ = _ := by rw [mul_comm]
    · simp
      calc
        _ = liminf (fun n ↦ Real.toEReal ‖x n‖) atTop *
          liminf (fun n ↦ Real.toEReal ‖p‖) atTop := by
          congr
          symm
          apply @Filter.liminf_const EReal ℕ _ atTop _ (Real.toEReal ‖p‖)
        _ ≤ liminf (fun n ↦ Real.toEReal ‖x n‖ * Real.toEReal ‖p‖) atTop := by
          apply le_liminf_mul
          · apply Eventually.of_forall
            intro n
            simp
          · apply Eventually.of_forall
            intro n
            simp








-- 引理：弱收敛序列的范数有界
lemma weakly_converge_norm_bounded [CompleteSpace H]
  (x : ℕ → H) (x_lim : H) (h_wkconv_x : WeakConverge x x_lim) :
    ∃ M, ∀ n, ‖x n‖ ≤ M := by
  -- f 为有界线性算子
  let f : ℕ → H →L[ℝ] ℝ := fun n =>
    LinearMap.mkContinuous
      { toFun := fun z => ⟪x n, z⟫
        map_add' := fun u v => inner_add_right (x n) u v
        map_smul' := fun c u => inner_smul_right (x n) u c}
      ‖x n‖
      fun z => by
        simp; exact abs_real_inner_le_norm (x n) z

  have h_f_n_y_upbd : ∀ y : H, ∃ N : ℕ, ∃ M : ℝ, ∀ n ≥ N, |f n y| ≤ M := by
    intro y
    rw [weakConverge_iff_inner_converge] at h_wkconv_x
    specialize h_wkconv_x y; rw [Metric.tendsto_atTop] at h_wkconv_x
    specialize h_wkconv_x (1) (one_pos)
    obtain ⟨N, hN⟩ := h_wkconv_x
    use N, |⟪x_lim, y⟫| + 1
    intro n hn; specialize hN n hn; simp [f]
    rw [Real.dist_eq] at hN
    have : |inner ℝ (x n) y| - |inner ℝ x_lim y| < 1 := by
      calc
        _ ≤ |inner ℝ (x n) y - inner ℝ x_lim y| := by apply abs_sub_abs_le_abs_sub
        _ < 1 := hN
    linarith

  have h_f_n_y_pointwise_bounded : ∀ y : H, ∃ M : ℝ, ∀ n : ℕ, |f n y| ≤ M := by
    intro y
    specialize h_f_n_y_upbd y
    obtain ⟨N, hN⟩ := h_f_n_y_upbd
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
          |f n y| ≤ M0 := by apply ha n; exact Finset.mem_range.mpr hn
          _ ≤ max M0 M1 := by apply le_max_left
      · push_neg at hn
        calc
          |f n y| ≤ M1 := by apply hM1; exact hn
          _ ≤ max M0 M1 := by apply le_max_right

  have h_norm_sup_t_n_y : ∀ y : H, ∃ M : ℝ, ⨆ n : ℕ, |f n y| ≤ M := by
    intro y; rcases h_f_n_y_pointwise_bounded y with ⟨M, hM⟩; use M; exact ciSup_le hM

  have h_f_bounded : ∃ C, ∀ n, ‖f n‖ ≤ C := by
    have h_pointwise : ∀ y, ∃ M, ∀ n, |f n y| ≤ M := by intro y; exact h_f_n_y_pointwise_bounded y
    exact banach_steinhaus h_pointwise

  obtain ⟨C, hC⟩ := h_f_bounded; use C; intro n
  have h_norm_eq : ‖f n‖ = ‖x n‖ := by
    refine ContinuousLinearMap.opNorm_eq_of_bounds ?_ ?_ ?_
    · simp
    · intro z; simp [f]; exact abs_real_inner_le_norm (x n) z
    · intro M hM h; simp [f] at h; specialize h (x n)
      rw [abs_of_nonneg] at h
      · rw [real_inner_self_eq_norm_sq, pow_two] at h
        have : ‖x n‖ ≥ 0 := norm_nonneg (x n)
        by_cases h1: ‖x n‖ = 0
        · rw [h1]; assumption
        · push_neg at h1
          have : ‖x n‖ > 0 := by
            apply lt_of_le_of_ne
            · exact this
            · intro h2; rw [h2] at h1; contradiction
          exact le_of_mul_le_mul_right h this
      · exact real_inner_self_nonneg
  rw [← h_norm_eq]; exact hC n



-- Lemma 2.42
theorem norm_weakly_lsc [CompleteSpace H] (x : ℕ → H) (p : H) (h : WeakConverge x p) :
  Real.toEReal ‖p‖ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := by
  let x' := fun ( n : ℕ ) => ⟪x n, p⟫
  let y' := fun ( n : ℕ ) => ‖x n‖ * ‖p‖
  have hxy : ∀ n, x' n ≤ y' n := by
    intro n
    exact real_inner_le_norm (x n) p
  have h1 : Tendsto x' atTop (nhds (‖p‖ ^ 2)) := by
    apply lim_inner_seq_eq_norm x p h
  have nonneg1 : Real.toEReal ‖p‖ ≥ 0 := by
    exact EReal.coe_nonneg.mpr (norm_nonneg p)
  have nonneg2 : ∀ n, Real.toEReal ‖x n‖ ≥ 0 := by
    refine fun n ↦ ?_
    exact EReal.coe_nonneg.mpr (norm_nonneg (x n))
  by_cases hp1 : Real.toEReal ‖p‖ = 0
  · simp [hp1]
    calc
      _ = liminf (fun n ↦ (0 : EReal)) atTop := by
        symm
        apply @Filter.liminf_const EReal ℕ _ atTop _ (Real.toEReal 0)
      _ ≤ liminf (fun n ↦ Real.toEReal ‖x n‖) atTop := by
        apply liminf_le_liminf
        · apply Eventually.of_forall
          intro n
          simp
        · simp [autoParam, IsBoundedUnder, IsBounded]
          use 0
          use 0
          intro n
          simp
        · simp [autoParam]
          apply Filter.IsBoundedUnder.isCoboundedUnder_ge
          simp [IsBoundedUnder, IsBounded]
          have h_norm_bounded : ∃ M, ∀ n, ‖x n‖ ≤ M :=
            weakly_converge_norm_bounded x p h
          obtain ⟨M, hM⟩ := h_norm_bounded
          use M, 0
          intro b_1 _
          simp
          exact hM b_1
  · have hp2 : Real.toEReal ‖p‖ ≠ ⊥ := by
      simp
    have hp3 : Real.toEReal ‖p‖ ≠ ⊤ := by
      simp
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
    have eq: ‖p‖^2 = ‖p‖ * ‖p‖ := by
      linarith
    have eq': Real.toEReal (‖p‖ ^ 2) = Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by
      rw [eq, p_norm_eq]
    have : Real.toEReal ‖p‖ * Real.toEReal ‖p‖
      ≤ liminf (fun n ↦ Real.toEReal ‖x n‖) atTop * Real.toEReal ‖p‖ := by calc
      Real.toEReal ‖p‖ * Real.toEReal ‖p‖ = Real.toEReal (‖p‖ ^ 2) := by rw [eq']
      _ ≤ liminf (fun n => Real.toEReal (y' n)) atTop := by convert h_lim
      _ = liminf (fun n => Real.toEReal (‖x n‖ * ‖p‖)) atTop := by simp [y']
      _ = liminf (fun n => Real.toEReal ‖x n‖ * Real.toEReal ‖p‖ ) atTop := by congr
      _ = liminf (fun n ↦ Real.toEReal ‖x n‖) atTop * Real.toEReal ‖p‖ := by rw [← h2]
    calc
      _ = Real.toEReal ‖p‖ / Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by
        symm
        apply EReal.div_mul_cancel
        · exact hp2
        · exact hp3
        exact hp1
      _ = Real.toEReal ‖p‖ * Real.toEReal ‖p‖ / Real.toEReal ‖p‖ := by apply EReal.mul_div_right
      _ ≤ liminf (fun n ↦ ↑‖x n‖) atTop * Real.toEReal ‖p‖ / Real.toEReal ‖p‖ := by
        apply EReal.div_le_div_right_of_nonneg
        · exact nonneg1
        exact this
      _ = liminf (fun n ↦ ↑‖x n‖) atTop / Real.toEReal ‖p‖ * Real.toEReal ‖p‖ := by
        symm
        apply EReal.mul_div_right
      _ = liminf (fun n ↦ ↑‖x n‖) atTop := by
        apply EReal.div_mul_cancel
        · exact hp2
        · exact hp3
        exact hp1


-- Lemma 2.51 (i)
theorem weak_converge_limsup_le_iff_strong_converge [CompleteSpace H] (x : ℕ → H) (p : H) :
  WeakConverge x p ∧ limsup (fun n => Real.toEReal ‖x n‖) atTop ≤ Real.toEReal ‖p‖ ↔
  Tendsto x atTop (nhds p) := by
  by_cases upper_bound : ¬ (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
  · push_neg at upper_bound
    constructor
    · rintro ⟨hweak, hlimsup⟩
      exfalso
      have hlimsup_top : limsup (fun n => Real.toEReal ‖x n‖) atTop = ⊤ := by
        simp [limsup, limsSup]
        intro a N hb
        by_contra ha_ne_top
        push_neg at ha_ne_top
        by_cases ha_ne_bot : a = ⊥
        · simp [ha_ne_bot] at hb
          specialize hb N
          simp at hb
        push_neg at ha_ne_bot
        lift a to ℝ using ⟨ha_ne_top, ha_ne_bot⟩ with a0
        by_cases hN : N = 0
        · simp [hN] at hb
          obtain ⟨m, hm⟩ := upper_bound (a0 + 1)
          have : ‖x m‖ ≤ a0 := by
            specialize hb m
            assumption
          linarith
        · -- N ≠ 0 时，可以定义 M1
          push_neg at hN
          let M1 := Finset.sup' (Finset.range N) (by simp [hN]) (fun k => ‖x k‖)
          let M := max M1 a0
          have hall : ∀ n, ‖x n‖ ≤ M := by
            intro n
            by_cases hn : n < N
            · have : ‖x n‖ ≤ M1 := by
                apply Finset.le_sup'_of_le
                · simp [Finset.mem_range]; exact hn
                · exact le_rfl
              exact le_trans this (le_max_left M1 a0)
            · push_neg at hn
              have : Real.toEReal ‖x n‖ ≤ Real.toEReal a0 := hb n hn
              rw [EReal.coe_le_coe_iff] at this
              exact le_trans this (le_max_right M1 a0)
          obtain ⟨m, hm⟩ := upper_bound (M + 1)
          specialize hall m
          linarith
      rw [hlimsup_top] at hlimsup
      simp at hlimsup
    intro h
    constructor
    · exact strong_converge_then_weak_converge x p h
    rw[Metric.tendsto_atTop] at h
    exfalso
    specialize h 1 zero_lt_one
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
            apply Nat.lt_succ_of_lt
            push_neg at hlt
            exact hlt
          simpa [Finset.mem_range] using this
        exact Finset.le_sup'_of_le (fun k ↦ ‖x k‖) hmem (le_rfl)
      have hcontr : ‖x n‖ ≤ M := by
        calc
          _ ≤ x0 + 1 := by linarith
          _ ≤ M := by apply le_max_left
      exact not_lt_of_ge hcontr hn
    have hdist : dist (x n) p > 1 := by
      have hnorm : ‖x n‖ > ‖p‖ + 1 := lt_of_le_of_lt (le_max_right _ _) hn
      have hbound : ‖x n - p‖ ≥ ‖x n‖ - ‖p‖ := by
        exact norm_sub_norm_le (x n) p
      have h1: ‖x n‖ - ‖p‖ > 1 := by linarith
      simp [dist_eq_norm]
      exact lt_of_lt_of_le h1 hbound
    have hdist' : dist (x n) p ≥ 1 := hdist.le
    have : dist (x n) p < 1 := hN n hn_ge
    exact (not_lt_of_ge hdist') this
  have h: liminf (fun n => Real.toEReal ‖x n‖) atTop
    ≤ limsup (fun n => Real.toEReal ‖x n‖) atTop := by
    push_neg at upper_bound
    apply liminf_le_limsup
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
  push_neg at upper_bound
  constructor
  · rintro ⟨hweak, hlimsup⟩
    have h' :Real.toEReal ‖p‖ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := by
      apply norm_weakly_lsc
      exact hweak
    have eq: limsup (fun n ↦ Real.toEReal ‖x n‖) atTop
      = liminf (fun n ↦ Real.toEReal ‖x n‖) atTop:= by
      apply le_antisymm
      · calc
          _ ≤ Real.toEReal ‖p‖ := hlimsup
          _ ≤ liminf (fun n => Real.toEReal ‖x n‖) atTop := h'
      exact h
    have hnorm_bounds :
        IsBoundedUnder (· ≤ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) ∧
        IsBoundedUnder (· ≥ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
      refine ⟨?_, ?_⟩
      · obtain ⟨M, hM⟩ := upper_bound
        exact ⟨M, (Eventually.of_forall hM).mono (by intro n hn; simpa)⟩
      · refine ⟨0, ?_⟩
        have hnonneg : ∀ n, 0 ≤ Real.toEReal ‖x n‖ := by
          intro n
          apply EReal.coe_nonneg.mpr (norm_nonneg (x n))
        apply Eventually.of_forall hnonneg
    have hlim : Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
      apply EReal.tendsto_coe.mp
      apply tendsto_of_liminf_eq_limsup
      · rw [eq] at hlimsup
        apply le_antisymm
        · exact hlimsup
        exact h'
      rw[← eq] at h'
      apply le_antisymm
      · exact hlimsup
      exact h'
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
    have hnorm : Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
      simpa using hlim
    have hsub : Tendsto (fun n => x n - p) atTop (nhds 0) := by
      apply (tendsto_iff_sub_tendsto_zero x p).1
      apply (seq_converge_iff_norm_converge x p).2
      have eq2:∀ n, ‖x n - p‖ ^2 = ‖x n‖^2 - 2 * ⟪x n, p⟫ + ‖p‖^2 := by
        intro n
        rw [← @norm_sub_sq_real]
      simp only [eq2]
      have h1 : Tendsto (fun n => ‖x n‖^2) atTop (nhds (‖p‖^2)) := by
        simpa [pow_two] using hnorm.mul hnorm
      have h2 : Tendsto (fun n => 2 * ⟪x n, p⟫) atTop (nhds (2 * ‖p‖^2)) := by
        have : Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := by
          exact lim_inner_seq_eq_norm x p hweak
        simpa using (tendsto_const_nhds (x := (2:ℝ))).mul this
      have h3 : Tendsto (fun n => ‖p‖^2) atTop (nhds (‖p‖^2)) := tendsto_const_nhds (α := ℕ)
      convert h1.sub h2 |>.add h3 using 2
      ring
    have hnorm_sq :
        Tendsto (fun n => ‖x n - p‖ ^ 2) atTop (nhds 0) := by
      have hnorm : Tendsto (fun n => ‖x n - p‖) atTop (nhds 0) := by
        exact tendsto_zero_iff_norm_tendsto_zero.mp hsub
      simpa [pow_two] using hnorm.mul hnorm
    exact (seq_converge_iff_norm_converge x p).2 hnorm_sq
  intro h'
  constructor
  · exact strong_converge_then_weak_converge x p h'
  have hnorm : Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := Tendsto.norm h'
  -- 将 Real 转成 EReal 的收敛
  have hnorm_ereal : Tendsto (fun n => Real.toEReal ‖x n‖) atTop (nhds (Real.toEReal ‖p‖)) := by
    exact EReal.tendsto_coe.mpr hnorm
  -- 当序列收敛时，limsup = liminf = 极限值
  have hlimsup : limsup (fun n => Real.toEReal ‖x n‖) atTop = Real.toEReal ‖p‖ := by
    obtain ⟨M, hM⟩ := upper_bound
    have hbdd_above : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
      refine ⟨M, ?_⟩
      exact (Eventually.of_forall hM).mono (by intro n hn; simpa)
    have hbdd_below : IsBoundedUnder (· ≥ ·) atTop (fun n ↦ Real.toEReal ‖x n‖) := by
      refine ⟨0, ?_⟩
      apply Eventually.of_forall (fun (n : ℕ) => ?_)
      simp
    apply Tendsto.limsup_eq
    exact hnorm_ereal
  rw [hlimsup]

-- Corollary 2.52
theorem strong_converge_iff_weak_norm_converge [CompleteSpace H] (x : ℕ → H) (p : H) :
  Tendsto x atTop (nhds p) ↔
  WeakConverge x p ∧ Tendsto (fun n => ‖x n‖) atTop (nhds ‖p‖) := by
  constructor
  · intro h
    constructor
    · exact strong_converge_then_weak_converge x p h
    exact Tendsto.norm h
  intro ⟨h1, h2⟩
  apply (seq_converge_iff_norm_converge x p).2
  have norm_expand : ∀ n, ‖x n - p‖^2 = ‖x n‖^2 - 2 * ⟪x n, p⟫ + ‖p‖^2 := by
    intro n
    rw [← @norm_sub_sq_real]
  simp only [norm_expand]
  have hnorm_sq : Tendsto (fun n => ‖x n‖^2) atTop (nhds (‖p‖^2)) := by
    simpa [pow_two] using h2.mul h2
  have hinner : Tendsto (fun n => 2 * ⟪x n, p⟫) atTop (nhds (2 * ‖p‖^2)) := by
    have : Tendsto (fun n => ⟪x n, p⟫) atTop (nhds (‖p‖^2)) := by
      exact lim_inner_seq_eq_norm x p h1
    simpa using (tendsto_const_nhds (x := (2:ℝ))).mul this
  have hconst : Tendsto (fun n => ‖p‖^2) atTop (nhds (‖p‖^2)) :=
    tendsto_const_nhds (α := ℕ)
  convert hnorm_sq.sub hinner |>.add hconst using 2
  ring

def IsWeaklyClosed (s : Set H) := @IsClosed (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))
def IsWeaklySeqClosed (s : Set H) := @IsSeqClosed (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))
/-- Theorem 3.34
Let `C` be a convex subset of `H`. The following statement are equivalent:
1. `C` is weakly sequentially closed.
2. `C` is sequentially closed.
3. `C` is closed.
4. `C` is weakly closed.
-/
-- Theorem 3.34 (i) → (ii)
theorem convex_weakly_seq_closed [CompleteSpace H] (s : Set H) (hw : IsWeaklySeqClosed s) :
  IsSeqClosed s :=
  fun x p hxn hx => @hw x p hxn ((strong_converge_iff_weak_norm_converge x p).1 hx).1

-- Theorem 3.34 (ii) ↔ (iii)
#check isSeqClosed_iff_isClosed

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

-- Theorem 3.34 (iii) → (iv)
theorem closed_is_weakly_closed [CompleteSpace H] (s : Set H)
  (hs : Convex ℝ s) (hw : IsClosed s) :
  IsWeaklyClosed s := by
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


-- Theorem 3.34 (iv) → (i)
theorem weakly_closed_seq_closed (s : Set H) (hs : IsWeaklyClosed s) :
   IsWeaklySeqClosed s := by
  simp [IsWeaklyClosed] at hs
  simp [IsWeaklySeqClosed]
  exact IsClosed.isSeqClosed hs


-- Theorem 3.34 (iii) → (i)
theorem closed_is_weakly_seq_closed [CompleteSpace H] (s : Set H)
  (hs : Convex ℝ s) (hc : IsClosed s) : IsWeaklySeqClosed s := by
  have hwkclosed := closed_is_weakly_closed s hs hc
  exact weakly_closed_seq_closed s hwkclosed








-- demiclosed 的定义
def DemiclosedAt (D : Set H) (T : H → H) (u : H) : Prop :=
  (h_D_nonempty : D.Nonempty) →
  (h_D_weakly_seq_closed : IsWeaklySeqClosed D) →
  ∀ (x : ℕ → H), (∀ n, x n ∈ D) →
  ∀ (x_lim : H), x_lim ∈ D →
  WeakConverge x x_lim →
  Tendsto (fun n => T (x n)) atTop (𝓝 u) →
  T x_lim = u

def Demiclosed (T : H → H) (D : Set H) : Prop :=
  ∀ u : H, DemiclosedAt D T u









--x n弱收敛到x_lim, u n强收敛到u_lim,lim ⟪x_n, u_n⟫ = ⟪x_lim, u_lim⟫
lemma wkconv_conv_ledsto_conv [CompleteSpace H]
  {x : ℕ → H} {x_lim : H} {u : ℕ → H} {u_lim : H} {h_wkconv_x : WeakConverge x x_lim}
  {h_conv_u : Tendsto u atTop (𝓝 u_lim)}
  : Tendsto (fun n => inner ℝ (x n) (u n)) atTop (𝓝 (inner ℝ x_lim u_lim)) := by
  have eq : (fun n => inner ℝ (x n) (u n) - inner ℝ x_lim u_lim) =
    (fun n => inner ℝ (x n) (u n - u_lim)) + (fun n => inner ℝ (x n - x_lim) u_lim) := by
      funext n; simp [inner_sub_left, inner_sub_right]
  have h_norm_x_n_bdd : ∃ M, ∀ n, ‖x n‖ ≤ M :=
    weakly_converge_norm_bounded x x_lim h_wkconv_x

  have h1: Tendsto (fun n => inner ℝ (x n) (u n - u_lim)) atTop (𝓝 0) := by
    obtain ⟨M, hM⟩ := h_norm_x_n_bdd
    have h_u_diff : Tendsto (fun n => u n - u_lim) atTop (𝓝 0) := by
      exact (tendsto_iff_sub_tendsto_zero u u_lim).mp h_conv_u
    by_cases M_zero : M = 0
    · -- M = 0 时，x n 恒为 0 向量
      have h_xn_zero : ∀ n, x n = 0 := by
        intro n; specialize hM n
        have : ‖x n‖ ≤ 0 := by rw [M_zero] at hM; exact hM
        have h_norm_nonneg : ‖x n‖ ≥ 0 := norm_nonneg (x n)
        exact norm_le_zero_iff.mp this
      rw [Metric.tendsto_atTop]; intro ε ε_pos; use 0; intro n hn; rw [h_xn_zero n]; simpa
    · have h_M_pos : M > 0 := by
        specialize hM 0; push_neg at M_zero
        have h_M_nonneg : M ≥ 0 := by
          calc
            M ≥ ‖x 0‖ := hM
            _ ≥ 0 := norm_nonneg (x 0)
        exact lt_of_le_of_ne h_M_nonneg (id (Ne.symm M_zero))
      have h_ε_pos_div : ∀ ε > 0, ε / M > 0 := by
        intros ε ε_pos; exact div_pos ε_pos h_M_pos
      rw [Metric.tendsto_atTop] at h_u_diff ⊢; intro ε ε_pos
      specialize h_u_diff (ε / M) (h_ε_pos_div ε ε_pos)
      obtain ⟨N, hN⟩ := h_u_diff
      use N; intro n hn; specialize hN n hn; rw [Real.dist_eq]; simp only [sub_zero]
      rw [dist_eq_norm, sub_zero] at hN
      calc
        |inner ℝ (x n) (u n - u_lim)|
            ≤ ‖x n‖ * ‖u n - u_lim‖ := by exact abs_real_inner_le_norm (x n) (u n - u_lim)
          _ ≤ M * ‖u n - u_lim‖ := by
              apply mul_le_mul
              · exact hM n
              · simp
              · exact norm_nonneg (u n - u_lim)
              · linarith
          _ < M * (ε / M) := by apply mul_lt_mul_of_pos_left hN h_M_pos
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



-- Theorem 4.27: Browder's demiclosedness principle
theorem browder_demiclosed_principle [CompleteSpace H]
  {D : Set H}
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D)
  : Demiclosed (id - T) D := by
  intro u
  intro h_D_nonempty h_D_weakly_seq_closed
  intro x hx_in_D x_lim hx_lim_in_D h_weak_conv h_diff_tendsto
  --取一个弱收敛到x_lim的列x n
  simp at h_diff_tendsto
  have h_norm_bound : ∀ n : ℕ, ‖x_lim - T x_lim - u‖ ^ 2 ≤
    ‖x n - T (x n) - u‖ ^ 2 + 2 * ⟪x n - T (x n) - u, T (x n) - T x_lim⟫
      - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by
        intro n
        calc
          _ = ‖(x_lim - x n) + (x n - T x_lim - u)‖ ^ 2 := by congr 1; abel_nf
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * ⟪x_lim - x n, x n - T x_lim - u⟫ := by
            rw [← real_inner_self_eq_norm_sq]
            simp [← real_inner_self_eq_norm_sq, inner_add_left,
              inner_add_right, real_inner_comm, two_mul]; ring_nf
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * ⟪x_lim - x n, (x n - x_lim) + (x_lim - T x_lim - u)⟫ := by congr 1; abel_nf
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * (⟪x_lim - x n, x n - x_lim⟫ + ⟪x_lim - x n, x_lim - T x_lim - u⟫) := by
              congr 1; rw [inner_add_right]
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * (-‖x_lim - x n‖ ^ 2 + ⟪x_lim - x n, x_lim - T x_lim - u⟫) := by
            congr 1; simp; rw [← real_inner_self_eq_norm_sq]
            have : (x n - x_lim) = - (x_lim - x n) := by abel
            rw [this]; rw [inner_neg_right]
          _ = ‖x n - T x_lim - u‖ ^ 2 - ‖x n - x_lim‖ ^ 2
              - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by
            simp [mul_add, ← add_assoc]; ring_nf; simp [add_sub, add_comm]
            congr 3
            · simp; exact norm_sub_rev x_lim (x n)
            · have : - (x n - x_lim) = (x_lim - x n) := by abel
              rw [← this]; rw [inner_neg_left]; ring_nf
          _ = ‖(x n - T (x n) - u) + (T (x n) - T x_lim)‖ ^ 2 - ‖x n - x_lim‖ ^ 2
              - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by congr 1; abel_nf
          _ = ‖x n - T (x n) - u‖ ^ 2 + ‖T (x n) - T x_lim‖ ^ 2 +
              2 * ⟪x n - T (x n) - u, T (x n) - T x_lim⟫ - ‖x n - x_lim‖ ^ 2
              - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by
            rw [← real_inner_self_eq_norm_sq]
            simp [← real_inner_self_eq_norm_sq, inner_add_left,
              inner_add_right, real_inner_comm, two_mul]; ring_nf
          _ ≤ _ := by
            have : ‖T (x n) - T x_lim‖ ^ 2 ≤ ‖x n - x_lim‖ ^ 2 := by
              apply sq_le_sq.2; simp
              rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
              have := hT_nonexp (hx_in_D n) hx_lim_in_D
              simp [edist_dist] at this; rw [dist_eq_norm, dist_eq_norm] at this; exact this
            linarith

  have h1 : Tendsto (fun n => ‖x n - T (x n) - u‖) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h_diff_tendsto
    obtain ⟨N, hN⟩ := h_diff_tendsto ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN ⊢
    simp at ⊢ hN
    exact hN

  have h2 : Tendsto (fun n => x n - T (x n) - u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h1
    obtain ⟨N, hN⟩ := h1 ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN ⊢
    simp at ⊢ hN
    exact hN

  have h3 : WeakConverge (fun n => x n - x_lim) 0 := by
    rw [weakConverge_iff_inner_converge']
    intro y
    have h4 : Tendsto (fun n => ⟪x n, y⟫) atTop (𝓝 ⟪x_lim, y⟫) := by
      apply (weakConverge_iff_inner_converge x x_lim).1 h_weak_conv
    have h5 : Tendsto (fun (n : ℕ) => ⟪x_lim, y⟫) atTop (𝓝 ⟪x_lim, y⟫) := tendsto_const_nhds
    have h_diff : Tendsto (fun n => ⟪x n, y⟫ - ⟪x_lim, y⟫) atTop (𝓝 (⟪x_lim, y⟫ - ⟪x_lim, y⟫)) :=
      Tendsto.sub h4 h5
    convert h_diff using 1
    ext n; simp; rw [inner_sub_left]; ring_nf

  have h4 : WeakConverge (fun n => x n - T (x n)) u := by
    rw [weakConverge_iff_inner_converge']
    intro y
    by_cases hy : y = 0
    · -- 情况1：y = 0
      simp [hy]
    · have h2' : Tendsto (fun n => (x n - T (x n)) - u) atTop (𝓝 0) := by
        convert h2 using 1
      -- 内积的连续性
      have h_inner : Tendsto (fun n => ⟪(x n - T (x n)) - u, y⟫) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε ε_pos
        rw [Metric.tendsto_atTop] at h2'
        obtain ⟨N, hN⟩ := h2' (ε / ‖y‖) (by positivity)
        use N
        intro n hn
        specialize hN n hn
        simp [dist_eq_norm] at hN ⊢
        by_cases hy : y = 0
        · simp [hy]; linarith
        · calc
            |⟪(x n - T (x n)) - u, y⟫|
                ≤ ‖(x n - T (x n)) - u‖ * ‖y‖ := by apply abs_real_inner_le_norm _ _
              _ < (ε / ‖y‖) * ‖y‖ := by gcongr
              _ = ε := by field_simp [ne_of_gt (norm_pos_iff.mpr hy)]
      exact h_inner

  have h4 : WeakConverge (fun n => T (x n) - x n) (- u) := by
    rw [weakConverge_iff_inner_converge'] at h4 ⊢
    intro y
    specialize h4 y
    have := Tendsto.neg h4
    convert this using 1
    · ext n; simp; rw [← inner_neg_left]; simp [inner_sub_left, inner_add_left]; ring_nf
    simp

  have h5 : WeakConverge (fun n => T (x n) - x n + (x n - x_lim)
    + (x_lim - T x_lim)) (x_lim - T x_lim - u) := by
    rw [weakConverge_iff_inner_converge]
    intro y
    -- 分解内积
    have h4_inner : Tendsto (fun n => ⟪T (x n) - x n, y⟫) atTop (𝓝 ⟪-u, y⟫) := by
      apply (weakConverge_iff_inner_converge _ _).1 h4
    have h3_inner : Tendsto (fun n => ⟪x n - x_lim, y⟫) atTop (𝓝 ⟪(0 : H), y⟫) := by
      apply (weakConverge_iff_inner_converge _ _).1 h3
    have h_const : Tendsto (fun n : ℕ  => ⟪x_lim - T x_lim, y⟫) atTop (𝓝 ⟪x_lim - T x_lim, y⟫) :=
      tendsto_const_nhds

    -- 利用内积的加法性
    have h_combined : Tendsto (fun n =>
      ⟪T (x n) - x n, y⟫ + ⟪x n - x_lim, y⟫ + ⟪x_lim - T x_lim, y⟫)
      atTop (𝓝 (⟪-u, y⟫ + ⟪(0 : H), y⟫ + ⟪x_lim - T x_lim, y⟫)) := by
      apply Tendsto.add
      · apply Tendsto.add h4_inner h3_inner
      · exact h_const

    -- 转换为目标形式
    convert h_combined using 1
    · ext n; simp only [inner_add_left]
    · congr 1; simp [inner_sub_left]; abel

  have h5 : WeakConverge (fun n => T (x n) - T x_lim) (x_lim - T x_lim - u) := by
    convert h5 using 1; ext n; abel_nf

  have h1' :  Tendsto (fun n ↦ ‖x n - T (x n) - u‖ ^ 2) atTop (𝓝 0) := by
    apply Tendsto.pow at h1; specialize h1 2; convert h1; simp

  have h6 : Tendsto (fun n ↦ 2 * inner ℝ (x n - x_lim) (x_lim - T x_lim - u)) atTop (𝓝 0) := by
    have := (weakConverge_iff_inner_converge (fun n => x n - x_lim) 0).1 h3 (x_lim - T x_lim - u)
    simp only [inner_zero_left] at this; apply Tendsto.const_mul 2 at this; convert this; simp

  have h7 : Tendsto (fun n ↦ inner ℝ (T (x n) - T x_lim) (x n - T (x n) - u))
    atTop (𝓝 (inner ℝ 0 (x_lim - T x_lim - u))) := by
    let a := fun n => x n - T (x n) - u; let b := fun n => T (x n) - T x_lim
    have h_a : Tendsto a atTop (𝓝 0) := h2
    have h_b : WeakConverge b (x_lim - T x_lim - u) := h5
    rw [real_inner_comm]; apply wkconv_conv_ledsto_conv
    · exact h_b
    · exact h_a

  have h7' : Tendsto (fun n ↦ inner ℝ (T (x n) - T x_lim) (x n - T (x n) - u)) atTop (𝓝 0) := by
    convert h7; simp

  have h8 : Tendsto (fun n ↦ ‖x n - T (x n) - u‖ ^ 2 + (2 * inner ℝ (T (x n) - T x_lim)
    (x n - T (x n) - u) - 2 * inner ℝ (x n - x_lim) (x_lim - T x_lim - u))) atTop (𝓝 (0 + (0 - 0)))
      := by
        apply Tendsto.add
        · exact h1'
        · apply Tendsto.sub
          · apply Tendsto.const_mul 2 at h7'; convert h7'; simp
          · exact h6

  have h8' : Tendsto (fun n ↦ ‖x n - T (x n) - u‖ ^ 2 + 2 * inner ℝ (x n - T (x n) - u)
    (T (x n) - T x_lim) - 2 * inner ℝ (x n - x_lim) (x_lim - T x_lim - u)) atTop (𝓝 0) := by
      convert h8 using 1
      · funext n; ring_nf; rw [add_sub]; rw [real_inner_comm]; ring
      · simp

  have h9 : ∀ ε > 0, ‖x_lim - T x_lim - u‖ ^ 2 < ε := by
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h8'
    obtain ⟨N, hN⟩ := h8' (ε) ε_pos
    specialize hN N (le_refl N)
    simp [dist_eq_norm] at hN
    specialize h_norm_bound N
    calc
      _ ≤ ‖x N - T (x N) - u‖ ^ 2 + 2 * ⟪x N - T (x N) - u, T (x N) - T x_lim⟫
          - 2 * ⟪x N - x_lim, x_lim - T x_lim - u⟫ := h_norm_bound
      _ < ε := by exact lt_of_abs_lt hN

  have h_final : ‖x_lim - T x_lim - u‖ ^ 2 ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε ε_pos
    specialize h9 ε ε_pos
    linarith
  have h_nonneg : 0 ≤ ‖x_lim - T x_lim - u‖ ^ 2 := by
    apply pow_two_nonneg
  have : ‖x_lim - T x_lim - u‖ ^ 2 = 0 := by
    apply le_antisymm h_final h_nonneg
  have : ‖x_lim - T x_lim - u‖ = 0 := by
    exact pow_eq_zero this
  have : x_lim - T x_lim - u = 0 := by
    exact norm_eq_zero.mp this
  rw [sub_eq_zero] at this
  exact this

-- Corollary 4.28: 弱收敛且误差趋零蕴含固定点
lemma corollary_4_28 [CompleteSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) (x : ℕ → H) (h_x_in_D : ∀ n, x n ∈ D)
  (p : H) (h_p_in_D : p ∈ D) (h_weak_conv : WeakConverge x p)
  (h_error_zero : Tendsto (fun n => x n - T (x n)) atTop (𝓝 0)) : p ∈ Fix T := by
  have h_wk_seq_closed : IsWeaklySeqClosed D := by
    apply closed_is_weakly_seq_closed; exact hD_convex; exact hD_closed
  have h_demiclosed := browder_demiclosed_principle hT_nonexp
  have h_p_minus_Tp_zero : p - T p = 0 := by
    apply h_demiclosed; exact hD_nonempty; exact h_wk_seq_closed; exact h_x_in_D
    exact h_p_in_D; exact h_weak_conv; exact h_error_zero
  simp [Fix, IsFixedPt]; simp [sub_eq_zero] at h_p_minus_Tp_zero
  exact id (Eq.symm h_p_minus_Tp_zero)







end WeakTopology



section T2Space

#check Topology.IsEmbedding.t2Space
#check ProperSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

#check topDualPairing_eq_inner
instance inst_WeakSpace_T2 : T2Space (WeakSpace ℝ H) where
  t2 := by
    simp [Pairwise]
    intro x y hxy
    let u := x - y
    let f1 := WeakSpace.map (va H u)
    let f2 := (toWeakSpace ℝ ℝ).symm
    let f := f2 ∘ f1
    have feq (t : H): f t = (va H u) t := rfl
    let c := (f x + f y)/2
    let U := {z : H | f z > c}
    let V := {z : H | f z < c}
    have Uopen : @IsOpen (WeakSpace ℝ H) _ U := by
      refine isOpen_lt ?_ ?_
      exact continuous_const
      simp [f]
      refine Continuous.comp ?_ ?_
      exact continuous_real_weakspace
      exact ContinuousLinearMap.continuous f1
    have Vopen : @IsOpen (WeakSpace ℝ H) _ V := by
      simp [V]
      refine isOpen_lt ?_ ?_
      · simp [f]
        refine Continuous.comp ?_ ?_
        exact continuous_real_weakspace
        exact ContinuousLinearMap.continuous f1
      exact continuous_const
    have xinUV : x ∈ U ∧ y ∈ V := by
      constructor
      simp [U]
      change f x > c
      simp [feq, va]
      · refine (Real.add_lt_add_iff_left ?_).mp ?_
        · exact c
        · refine (Real.add_lt_add_iff_left c).mpr ?_
          simp [c, f, f1, va, f2, toWeakSpace]
          rw [LinearEquiv.refl]
          simp [LinearMap.id, u]
          simp [inner_sub_right]
          let xH : H := (toWeakSpace ℝ H).symm x
          let yH : H := (toWeakSpace ℝ H).symm y
          simp [real_inner_comm]
          have h_ne : xH ≠ yH := by
            have h_inj : Function.Injective ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
              LinearEquiv.injective _
            intro heq
            have : x = y := h_inj (by simp; exact heq)
            exact hxy this
          have h_sub : xH - yH ≠ 0 := sub_ne_zero_of_ne h_ne
          have h_pos : 0 < ‖xH - yH‖ := norm_pos_iff.mpr h_sub
          have h1: ‖xH - yH‖ ^ 2 > 0 := sq_pos_of_pos h_pos
          rw [← real_inner_self_eq_norm_sq] at h1
          simp [inner_sub_right, real_inner_comm] at h1
          -- 关键：使用 xH 和 yH 而不是转换后的形式
          have h_calc : (⟪xH, xH⟫ - ⟪yH, yH⟫) / 2 < ⟪xH, xH⟫ - ⟪xH, yH⟫ := by
            nlinarith [h1, sq_nonneg (‖xH - yH‖)]
          -- 因为 x 和 y 就是通过 toWeakSpace 从 xH 和 yH 得到的
          have h_eq_x : (toWeakSpace ℝ H) xH = x := by simp [xH]
          have h_eq_y : (toWeakSpace ℝ H) yH = y := by simp [yH]
          -- 转换目标中的内积
          convert h_calc using 3
      simp [V]
      change f y < c
      simp [feq, va]
      · refine (Real.add_lt_add_iff_left ?_).mp ?_
        · exact c
        · refine (Real.add_lt_add_iff_left c).mpr ?_
          simp [c, f, f1, va, f2, toWeakSpace]
          rw [LinearEquiv.refl]
          simp [LinearMap.id, u]
          simp [inner_sub_right]
          let xH : H := (toWeakSpace ℝ H).symm x
          let yH : H := (toWeakSpace ℝ H).symm y
          simp [real_inner_comm]
          have h_ne : xH ≠ yH := by
            have h_inj : Function.Injective ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
              LinearEquiv.injective _
            intro heq
            have : x = y := h_inj (by simp; exact heq)
            exact hxy this
          have h_sub : xH - yH ≠ 0 := sub_ne_zero_of_ne h_ne
          have h_pos : 0 < ‖xH - yH‖ := norm_pos_iff.mpr h_sub
          have h1: ‖xH - yH‖ ^ 2 > 0 := sq_pos_of_pos h_pos
          rw [← real_inner_self_eq_norm_sq] at h1
          simp [inner_sub_right, real_inner_comm] at h1
          -- 关键：使用 xH 和 yH 而不是转换后的形式
          have h_calc : ⟪xH, yH⟫ - ⟪yH, yH⟫ < (⟪xH, xH⟫ - ⟪yH, yH⟫) / 2 := by
            nlinarith [h1, sq_nonneg (‖xH - yH‖)]
          -- 因为 x 和 y 就是通过 toWeakSpace 从 xH 和 yH 得到的
          have h_eq_x : (toWeakSpace ℝ H) xH = x := by simp [xH]
          have h_eq_y : (toWeakSpace ℝ H) yH = y := by simp [yH]
          -- 转换目标中的内积
          convert h_calc using 3
    have dUV : Disjoint U V := by
      simp [Disjoint]
      intro Z hU hV
      simp [U, V] at hU hV
      have h_contradiction : ∀ z ∈ Z, False := by
        intro z hz
        have h1 : c < f z := hU hz
        have h2 : f z < c := hV hz
        linarith
      exact Set.subset_eq_empty h_contradiction rfl
    exact ⟨U, Uopen, V, Vopen, xinUV.1, xinUV.2, dUV⟩

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

lemma WeakSpace.continuous_of_continuous_eval
    {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : X → WeakSpace ℝ E}
    (hf : ∀ ℓ : E →L[ℝ] ℝ, Continuous fun x => ℓ (f x)) :
    Continuous f := continuous_induced_rng.2 <| continuous_pi_iff.mpr <| fun y => hf y

noncomputable def weakToWeakDual [CompleteSpace H] : WeakSpace ℝ H ≃ₗ[ℝ] WeakDual ℝ H :=
  (InnerProductSpace.toDual ℝ H).toLinearEquiv

#check WeakSpace
#check WeakBilin.eval_continuous
#check InnerProductSpace.toDual_symm_apply
noncomputable def weakHomeomorph [CompleteSpace H] : WeakSpace ℝ H ≃ₜ WeakDual ℝ H where
  toFun := weakToWeakDual
  invFun := weakToWeakDual.symm
  left_inv := weakToWeakDual.left_inv
  right_inv := weakToWeakDual.right_inv
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro x
    have : (fun v : WeakSpace ℝ H => (weakToWeakDual v) x)
      = fun v => (InnerProductSpace.toDual ℝ H x) v := by
        ext v
        simp [weakToWeakDual, InnerProductSpace.toDual_apply]
        change (InnerProductSpace.toDual ℝ H v) x = ⟪x, v⟫
        simp
        exact real_inner_comm x v
    simp [this]
    simp only [← topDualPairing_eq_inner]
    have : (fun v ↦ ((topDualPairing ℝ H).flip x) (va H v)) =
      (fun v ↦ ((topDualPairing ℝ H).flip v) (va H x)) := by
      ext v
      rw [topDualPairing_eq_inner, topDualPairing_eq_inner]
      exact congrFun (id (Eq.symm this)) v
    rw [this]
    apply WeakBilin.eval_continuous
  continuous_invFun := by
    apply WeakSpace.continuous_of_continuous_eval
    intro y
    obtain ⟨x, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective y
    have : (fun φ : WeakDual ℝ H => (InnerProductSpace.toDual ℝ H x)
        (weakToWeakDual.symm φ))
        = fun φ => φ x := by
        ext φ
        simp [weakToWeakDual]
        change ⟪x, ((InnerProductSpace.toDual ℝ H).symm φ) ⟫  = φ x
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [this]
    exact WeakDual.eval_continuous x

#check weakHomeomorph.isCompact_image

lemma weakHom_image_eq [CompleteSpace H] {x : H} {r : ℝ} :
  weakHomeomorph '' ((closedBall x r) : Set H) =
  toStrongDual ⁻¹' closedBall ((InnerProductSpace.toDual ℝ H) x) r := by
  ext y
  constructor
  · rintro ⟨x', h1, h2⟩
    simp; rw [← h2]; simp [weakHomeomorph, weakToWeakDual]
    change dist ((InnerProductSpace.toDual ℝ H) x') ((InnerProductSpace.toDual ℝ H) x) ≤ r
    simpa
  intro hy
  simp at hy; simp [weakHomeomorph, weakToWeakDual]
  obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective y
  use v
  constructor
  · simp at hy; exact hy
  change (InnerProductSpace.toDual ℝ H) v = (InnerProductSpace.toDual ℝ H) v
  rfl

/-
Fact 2.34: Banach-Alaoglu Bourbaki
-/
theorem closed_unit_ball_is_weakly_compact [CompleteSpace H] (x : H) (r : ℝ) :
  IsWeaklyCompact (closedBall x r) := by
  let f := InnerProductSpace.toDual ℝ H x
  obtain h := isCompact_closedBall ℝ f r
  simp [IsWeaklyCompact]
  have ball_eq: closedBall f r = (InnerProductSpace.toDual ℝ H)'' (closedBall x r) := by simp [f]
  simp [ball_eq] at h
  rwa [← weakHomeomorph.isCompact_image, weakHom_image_eq]


#check WeakDual.isCompact_closedBall

#check IsSeqCompact

def IsWeaklySeqCompact (s : Set H) := @IsSeqCompact (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))

#check TopologicalSpace.MetrizableSpace
#check SequentialSpace
#check FirstCountableTopology
#check FrechetUrysohnSpace
-- #check SeqClusterPt
#check MapClusterPt
-- #check IsSeqClusterPt
def IsWeaklySeqClusterPt (p : H) (x : ℕ → H):= @MapClusterPt (WeakSpace ℝ H) _ ℕ p atTop x

-- instance : MetrizableSpace (WeakSpace ℝ H) := sorry

/-
Fact 2.37 Eberlein Smulian
-/
theorem weakly_compact_iff_weakly_seq_compact (C : Set H) (hC : IsWeaklyCompact C) :
  IsWeaklySeqCompact C := by
  simp [IsWeaklySeqCompact, IsWeaklyCompact, IsSeqCompact] at hC ⊢
  intro x hx
  let M : Submodule ℝ H := Submodule.topologicalClosure (Submodule.span ℝ (Set.range x))
  haveI : SeparableSpace M := by
    refine { exists_countable_dense := ?_ }
    sorry
  sorry

-- instance : SeqCompactSpace (WeakSpace ℝ H) where
--   isSeqCompact_univ := by
--     show IsWeaklySeqCompact Set.univ
--     sorry

#check MapClusterPt
#check TopologicalSpace.SeparableSpace
#check TopologicalSpace.exists_countable_dense
#check Set.Countable.exists_eq_range
#check IsBounded
#check tendsto_subseq_of_bounded
#check subseq_tendsto_of_neBot


#check ArzelaAscoli.isCompact_closure_of_isClosedEmbedding

-- structure dense_f

structure convergent_Subseq (x : ℕ → H) (f : ℕ → H) (m : ℕ) where
  φ : ℕ → ℕ
  monotone' : StrictMono φ
  lim : ℝ
  convergent : Tendsto (fun n => ⟪f m, x (φ n)⟫) atTop (𝓝 lim)

-- 有界实数序列有收敛子列
lemma extract_subseq' (x : ℕ → H) (hx : Bornology.IsBounded <| Set.range fun n => ‖x n‖)
    (f : ℕ → H) (m : ℕ) :
    Nonempty <| convergent_Subseq x f m := by
    sorry
  -- classical
  -- obtain ⟨R, hR0⟩ := hx.subset_closedBall (0 : ℝ)
  -- have hnorm : ∀ n, ‖x n‖ ≤ R := by
  --   intro n
  --   have hxmem : ‖x n‖ ∈ Set.range fun n => ‖x n‖ := ⟨n, rfl⟩
  --   have hclosed := hR hxmem
  --   have hdist := Metric.mem_closedBall.mp hclosed
  --   simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hdist
  -- set y : ℕ → ℝ := fun n => ⟪f m, x n⟫
  -- set B : ℝ := ‖f m‖ * R
  -- have hB0 : 0 ≤ B := mul_nonneg (norm_nonneg _) hR0
  -- have hy_bounds : ∀ n, |y n| ≤ B := by
  --   intro n
  --   have h₁ : |y n| ≤ ‖f m‖ * ‖x n‖ := by
  --     simpa [y] using abs_realInner_le_norm (f m) (x n)
  --   have h₂ : ‖f m‖ * ‖x n‖ ≤ B := by
  --     have := mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg _)
  --     simpa [B] using this
  --   exact h₁.trans h₂
  -- have hy_mem : ∀ n, y n ∈ Set.Icc (-B) B := by
  --   intro n
  --   have := abs_le.mp (hy_bounds n)
  --   simpa [Set.mem_Icc] using this
  -- obtain ⟨φ, hφmono, l, -, hlim⟩ :=
  --   (isCompact_Icc (-B) B).exists_seq_tendsto y hy_mem
  -- refine ⟨⟨φ, hφmono, l, ?_⟩⟩
  -- simpa [y] using hlim

-- 有界序列的子列也是有界序列
lemma bdd_subseq_bdd (x : ℕ → H) (hx : Bornology.IsBounded <| Set.range fun n => ‖x n‖)
  (φ : ℕ → ℕ) :
  Bornology.IsBounded <| Set.range fun n => ‖(x ∘ φ) n‖ := by
  refine hx.subset ?_
  intro y hy
  rcases hy with ⟨n, rfl⟩
  exact ⟨φ n, rfl⟩

-- 存放 x ∘ φ 和 φ
structure subseq_x (x : ℕ → H) where
  xφ : ℕ → H -- x ∘ φ1 ∘ φ2 ∘ ... φ m
  phi_comp : ℕ → ℕ -- φ1 ∘ φ2 ∘ ... φ m
  φ : ℕ → ℕ -- φ m
  hφ : StrictMono φ -- φ m strict mono
  hbb : Bornology.IsBounded <| Set.range (fun n => ‖xφ n‖) -- x ∘ φ1 ∘ φ2 ∘ ... φ m bdd
  lim : ℝ
  fm : H
  hlim : Tendsto (fun n => ⟪fm, xφ n⟫) atTop (𝓝 lim)

-- noncomputable def xφ (x : ℕ → H)
--   (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
--   (f : ℕ → H) : ℕ → subseq_x x
-- | 0       => ⟨x, id, id, by exact fun ⦃a b⦄ a ↦ a, hx⟩
-- | (m + 1) => by
--   -- let ⟨xφm, φm, phi_comp, hφm, hbb⟩ := xφ x hx f m
--   have he := extract_subseq' (xφ x hx f m).1 (xφ x hx f m).5 f (m+1)
--   let h := Classical.choice <| he
--   have bdd := bdd_subseq_bdd (xφ x hx f m).1 (xφ x hx f m).5 h.1 h.2
--   exact ⟨(xφ x hx f m).1 ∘ h.1, (xφ x hx f m).2 ∘ h.1, h.1, h.2, bdd⟩

noncomputable def xφ (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) : ℕ → subseq_x x
| 0       => by
  have he := extract_subseq' x hx f 0
  let h := Classical.choice <| he
  have bdd := bdd_subseq_bdd x hx h.1
  exact ⟨x ∘ h.1, h.1, h.1, h.2, bdd, h.3, f 0, h.4⟩
| (m + 1) => by
  have he := extract_subseq' (xφ x hx f m).1 (xφ x hx f m).5 f (m+1)
  let h := Classical.choice <| he
  have bdd := bdd_subseq_bdd (xφ x hx f m).1 (xφ x hx f m).5 h.1
  exact ⟨(xφ x hx f m).1 ∘ h.1, (xφ x hx f m).2 ∘ h.1, h.1, h.2, bdd, h.3, f (m+1), h.4⟩

-- lemma dense_weakly_converge [CompleteSpace H] (x : ℕ → H) (f : ℕ → H) (a : ℕ → ℝ)
--   (hf : Dense (Set.range f)) (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
--   (hf2 : ∀ m, Tendsto (fun n => ⟪f m, x n⟫) atTop (nhds (a m))) :
--   ∃ p : H, WeakConverge x p := by
--   simp [weakConverge_iff_inner_converge]
--   sorry

-- ∀ m, φ0 ∘ φ1 ∘ φ2 ∘ ⋯ ∘ φ(m+1) = (φ0 ∘ φ1 ∘ φ2 ∘ ⋯ ∘ φm) ∘ φ(m+1)
lemma phi_comp_eq (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  (xφ x hx f (m+1)).2 = ((xφ x hx f m).2) ∘ ((xφ x hx f (m+1)).3) :=
  match m with
  | 0 => rfl
  | (_ + 1) => rfl

-- lemma phi_comp_eq (x : ℕ → H)
--   (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
--   (f : ℕ → H) (m : ℕ) :
--   (xφ x hx f (m+1)).2 = ((xφ x hx f m).2) ∘ ((xφ x hx f (m+1)).3) :=
--   match m with
--   | 0 => rfl
--   | (_ + 1) => rfl

-- ∀ m, φm is StrictMono.
lemma phim_mono (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  StrictMono (xφ x hx f m).3 := (xφ x hx f m).4

-- diagonal argument (sub-sequence of x)
noncomputable def phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H)
  : ℕ → ℕ := fun (n:ℕ) => (xφ x hx f n).2 n

#check StrictMono.comp

-- ∀ m, φ0 ∘ φ1 ∘ φ2 ∘ ⋯ ∘ φm is StrictMono.
lemma StrictMono_phi_comp (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ)
  : StrictMono (xφ x hx f m).2 := by
  induction' m with k hk
  · exact (xφ x hx f 0).4
  rw [phi_comp_eq]
  apply StrictMono.comp hk <| phim_mono x hx f (k + 1)

lemma StrictMono_nge (x : ℕ → ℕ) (hx : StrictMono x) (n : ℕ) : n < x (n + 1) := by
  have hle : ∀ k, k ≤ x k := by
    intro k
    induction' k with k hk
    · exact Nat.zero_le _
    · have h₁ : k + 1 ≤ x k + 1 := Nat.succ_le_succ hk
      have h₂ : x k + 1 ≤ x (k + 1) :=
        Nat.succ_le_of_lt (hx (Nat.lt_succ_self k))
      exact h₁.trans h₂
  have hn1 : n + 1 ≤ x (n + 1) := hle (n + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn1

lemma StrictMono_phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H)
  : StrictMono <| phi_diag x hx f := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  simp [phi_diag]
  rw [phi_comp_eq x hx f n]
  have h : n < (xφ x hx f (n + 1)).φ (n + 1) := by
    refine StrictMono_nge (xφ x hx f (n + 1)).φ ?_ n
    exact phim_mono x hx f (n + 1)
  exact StrictMono_phi_comp x hx f n h

lemma bdd_iff_exist_bound (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) :
  ∃ M > 0, ∀ n, ‖x n‖ ≤ M := by
  obtain ⟨R, hR⟩ := hx.subset_closedBall 0
  refine ⟨max 1 R, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro n
    have hx_mem : ‖x n‖ ∈ Set.range fun n => ‖x n‖ := ⟨n, rfl⟩
    have hx_dist : dist (‖x n‖) 0 ≤ R := by
      simpa [Metric.closedBall] using hR hx_mem
    have hx_le : ‖x n‖ ≤ R := by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hx_dist
    exact hx_le.trans (le_max_right _ _)

lemma upperbdd_phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H)
  : ∃ M > 0, ∀ n, ‖(x ∘ (phi_diag x hx f)) n‖ ≤ M := by
  have h := bdd_subseq_bdd x hx (phi_diag x hx f)
  exact bdd_iff_exist_bound (x ∘ phi_diag x hx f) h

-- ∀ m : ℕ, Tendsto (fun n => ⟪f m, (x ∘ φ0 ∘ ⋯ ∘ φm) n⟫) atTop (nhds (a m))
lemma converge_inner_subseq_fm (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  Tendsto (fun n => ⟪f m, (xφ x hx f m).1 n⟫) atTop (𝓝 (xφ x hx f m).6) := by
  match m with
  | 0 => exact (xφ x hx f 0).8
  | k + 1 => exact (xφ x hx f (k + 1)).8

-- ∀ m : ℕ, Tendsto (fun n => ⟪f m, (x ∘ φ) n⟫) atTop (nhds (a m))
-- 用极限定义
lemma converge_inner_subseq_fm_phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  Tendsto (fun n => ⟪f m, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (xφ x hx f m).6) := by
  sorry

-- ∀ y:H, (fun n => ⟪y, (x ∘ φ) n⟫) converges
-- 用柯西列的定义
-- 要用dense的定义
lemma dense_f_forall (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) :
  ∀ y:H, CauchySeq (fun n => ⟪y, (x ∘ (phi_diag x hx f)) n⟫) := by
  intro y
  simp [Metric.cauchySeq_iff]
  intro ε hε
  sorry
  -- refine _root_.cauchySeq_iff.mpr ?_


#check cauchySeq_tendsto_of_complete

lemma dense_f_forall_exist_lim (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) :
  ∀ y : H, ∃ a : ℝ, Tendsto (fun n => ⟪y, (x ∘ (phi_diag x hx f)) n⟫) atTop (nhds a):= by
  intro y
  apply cauchySeq_tendsto_of_complete
  exact dense_f_forall x hx f hf y

-- 证明线性映射，这个比较好证
def y_linearmap (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) :
  IsLinearMap ℝ (fun y => Classical.choose <| dense_f_forall_exist_lim x hx f hf y) where
  map_add := by
    intro a b
    let lima := Classical.choose <| dense_f_forall_exist_lim x hx f hf a
    let limb := Classical.choose <| dense_f_forall_exist_lim x hx f hf b
    let limab := Classical.choose <| dense_f_forall_exist_lim x hx f hf (a+b)
    change limab = lima + limb
    have ha : Tendsto (fun n ↦ ⟪a, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (lima))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf a)
    have hb : Tendsto (fun n ↦ ⟪b, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limb))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf b)
    have hab : Tendsto (fun n ↦ ⟪a + b, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limab))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf (a + b))
    sorry
  map_smul := by
    intro c y
    let limy := Classical.choose <| dense_f_forall_exist_lim x hx f hf y
    let limcy := Classical.choose <| dense_f_forall_exist_lim x hx f hf (c • y)
    change limcy = c * limy
    have hy : Tendsto (fun n ↦ ⟪y, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limy))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf y)
    have hb : Tendsto (fun n ↦ ⟪c • y, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limcy))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf (c • y))
    sorry

lemma tendsto_upper_bdd (x : ℕ → H) (M : ℝ)
  (hx : ∀ n, ‖x n‖ ≤ M) (a : ℝ)
  (y : H) (hc : Tendsto (fun n => ⟪y, x n⟫) atTop (nhds a)) :
  |a| ≤ M * ‖y‖ := by
  have hbound : ∀ n, |⟪y, x n⟫| ≤ M * ‖y‖ := by
    intro n
    calc
      _ ≤ ‖y‖ * ‖x n‖ := abs_real_inner_le_norm y (x n)
      _ ≤ ‖y‖ * M := mul_le_mul_of_nonneg_left (hx n) (norm_nonneg _)
      _ = M * ‖y‖ := CommMonoid.mul_comm ‖y‖ M
  exact (isClosed_le continuous_abs continuous_const).mem_of_tendsto hc
    (Eventually.of_forall hbound)

noncomputable def y_StrongDual (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) : StrongDual ℝ H where
  toFun := fun y => Classical.choose <| dense_f_forall_exist_lim x hx f hf y
  map_add' := (y_linearmap x hx f hf).1
  map_smul' := (y_linearmap x hx f hf).2
  cont := by
    apply @IsBoundedLinearMap.continuous ℝ _ H
    refine { toIsLinearMap := ?_, bound := ?_ }
    · exact y_linearmap x hx f hf
    rcases (upperbdd_phi_diag x hx f) with ⟨M1,hM1,hxn⟩
    use M1, hM1
    intro y
    let limy := Classical.choose <| dense_f_forall_exist_lim x hx f hf y
    change |limy| ≤ M1 * ‖y‖
    have hy : Tendsto (fun n ↦ ⟪y, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limy))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf y)
    exact tendsto_upper_bdd (fun n ↦ (x ∘ (phi_diag x hx f)) n) M1 hxn limy y hy

/-
Lemma 2.45
可分的版本
-/
theorem bounded_seq_has_weakly_converge_subseq_separable [SeparableSpace H]
  [CompleteSpace H] (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) :
  ∃ φ, StrictMono φ ∧ (∃ (a : H), WeakConverge (x ∘ φ) a) := by
  rcases exists_countable_dense H with ⟨s, hs1, hs2⟩
  have hsn : s.Nonempty := Dense.nonempty hs2
  rcases Set.Countable.exists_eq_range hs1 hsn with ⟨f, hf⟩
  let φ := phi_diag x hx f
  have hdense : Dense (Set.range f) := by
    rwa [hf] at hs2
  let yh := dense_f_forall_exist_lim x hx f hdense
  choose fy hhh using yh
  obtain sφ := StrictMono_phi_diag x hx f
  obtain ⟨a, h⟩ := (InnerProductSpace.toDual ℝ H).surjective (y_StrongDual x hx f hdense)
  have hy (y : H) :
    (y_StrongDual x hx f hdense).toFun y = ((InnerProductSpace.toDual ℝ H) a) y := by
    exact
      congrFun
        (congrArg AddHom.toFun
          (congrArg LinearMap.toAddHom (congrArg ContinuousLinearMap.toLinearMap (id (Eq.symm h)))))
        y
  have hy2 (y : H): ⟪a,y⟫ = (y_StrongDual x hx f hdense).toFun y := by
    specialize hy y
    simp [InnerProductSpace.toDual_apply] at hy
    symm
    exact hy
  have xφc : WeakConverge (x ∘ φ) a := by
    refine (weakConverge_iff_inner_converge (x ∘ φ) a).mpr ?_
    intro y
    rw [hy2]
    simp only [real_inner_comm]
    exact Classical.choose_spec (dense_f_forall_exist_lim x hx f hdense y)
  exact ⟨φ, sφ, a, xφc⟩


lemma IsWeaklySeqCompact_mono {s t : Set H}
  (x : ℕ → H) (hx : ∀ n : ℕ, x n ∈ s):
  (IsWeaklySeqCompact t) → s ⊆ t → ∃ a, ∃ φ, StrictMono φ ∧ WeakConverge (x ∘ φ) a := by
  intro ht hsub
  simp [IsWeaklySeqCompact, IsSeqCompact] at ht ⊢
  have hx' : ∀ n : ℕ, x n ∈ t := fun n => hsub (hx n)
  have := ht hx'
  rcases this with ⟨a, ha_in_t, φ, hφ_strict, hφ_conv⟩
  use a, φ, hφ_strict, hφ_conv

/-
Lemma 2.45
-/
theorem bounded_seq_has_weakly_converge_subseq [CompleteSpace H]
  (x : ℕ → H)
  (hx : BddAbove (Set.range (fun n => ‖x n‖))) :
  ∃ (a : H), ∃ φ, StrictMono φ ∧ WeakConverge (x ∘ φ) a := by
  let M := sSup (Set.range (fun n => ‖x n‖))
  let ρ := M + 1
  have h_in_ball : Set.range x ⊆ closedBall 0 ρ := by
    intro y hy
    simp [Set.range] at hy
    obtain ⟨n, rfl⟩ := hy
    simp [closedBall, dist_zero_right]
    -- ‖x n‖ ≤ M ≤ ρ
    have : ‖x n‖ ≤ M := by
      simp [M]
      refine (Real.le_sSup_iff hx ?_).mpr ?_
      · exact Set.range_nonempty fun n ↦ ‖x n‖
      · intro ε hε
        use ‖x n‖
        constructor
        · simp
        · linarith
    simp [ρ]
    linarith
  -- 应用 Banach-Alaoglu：闭球是弱紧的
  have h_ball_compact : IsWeaklyCompact (closedBall (0 : H) ρ) := by
    apply closed_unit_ball_is_weakly_compact
  -- 应用 Eberlein-Šmulian：弱紧 ⟹ 弱序列紧
  have h_ball_seq_compact : IsWeaklySeqCompact (closedBall (0 : H) ρ) :=
    weakly_compact_iff_weakly_seq_compact _ h_ball_compact
  have hx_in : ∀ n : ℕ, x n ∈ Set.range x := by
    exact fun n ↦ Set.mem_range_self n
  apply IsWeaklySeqCompact_mono x hx_in h_ball_seq_compact h_in_ball

-- theorem bounded_seq_has_weakly_converge_subseq' (x : ℕ → H)
--   (hx : BddAbove (Set.range (fun n => ‖x n‖))) :
--   IsWeaklySeqCompact (Set.range x) := by
--   simp [IsWeaklySeqCompact, IsSeqCompact]

#check mem_closure_iff_clusterPt

end WeaklyCompact
