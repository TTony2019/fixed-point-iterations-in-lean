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
  sorry






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
    simp [liminf, limsInf, sSup]
    sorry
  have hp2 : Real.toEReal ‖p‖ ≠ ⊥ := by
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
theorem closed_is_weakly_closed [CompleteSpace H] (s : Set H) (hs : Convex ℝ s) (hw : IsClosed s) :
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
          sorry
      · sorry
    have dUV : Disjoint U V := by
      simp [Disjoint]
      sorry
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
theorem closed_unit_ball_is_weakly_compact : IsWeaklyCompact (closedBall (0:H) (1:ℝ)) := by
  obtain := isCompact_closedBall
  simp [IsWeaklyCompact]
  


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
