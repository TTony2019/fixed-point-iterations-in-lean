import FormalizationFixpointIterations.Algorithm.Halpern.Lemma
import FormalizationFixpointIterations.Algorithm.Halpern.Halpern
import FormalizationFixpointIterations.Nonexpansive.Definitions
import FormalizationFixpointIterations.Nonexpansive.Properties
import FormalizationFixpointIterations.Theory.InnerProductSpace.WeakConverge
import FormalizationFixpointIterations.Theory.InnerProductSpace.Closedness
import FormalizationFixpointIterations.Theory.InnerProductSpace.Compact

open Nonexpansive_operator Filter Topology TopologicalSpace


local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]


lemma halpern_xj_formula
  {T : H → H} (alg : Halpern T) (h_α_form : ∀ n, alg.α n = (1 / (n + 2) : ℝ))
  (h_u_eq_x0 : alg.u = alg.x 0) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
    alg.x j = (1 / ((j + 1) : ℝ)) • alg.x 0 + ((j / (j + 1)) : ℝ) • T (alg.x (j - 1)) := by
  intro j hj
  have xj_eq : alg.x j = (1 - alg.α (j - 1)) • T (alg.x (j - 1)) + alg.α (j - 1) • alg.u := by
    have eq : j - 1 + 1 = j := Nat.sub_add_cancel hj.left; nth_rewrite 1 [← eq]
    rw[alg.update, add_comm]
  rw [← h_u_eq_x0, add_comm]
  have eq1 : 1 - alg.α (j - 1) = j / (j + 1) := by
    rw [h_α_form (j - 1)]; norm_cast; field_simp [Nat.succ_eq_add_one]
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, mul_add, sub_mul, add_mul, one_mul,
      mul_one, add_comm]
    have eq2 : ↑(j - 1) = (j : ℝ) - 1 := Nat.cast_pred (by linarith)
    rw [eq2]; ring
  have eq2 : alg.α (j - 1) = 1 / (j + 1) := by
    rw [h_α_form (j - 1)]; norm_cast; field_simp [Nat.succ_eq_add_one]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have eq3 : ↑(j - 1) = (j : ℝ) - 1 := Nat.cast_pred (by linarith)
    rw [eq3]; ring_nf
  rw [eq1, eq2] at xj_eq; assumption

lemma halpern_Tx_formula
  {T : H → H} (alg : Halpern T) (h_α_form : ∀ n, alg.α n = 1 / (n + 2))
  (h_u_eq_x0 : alg.u = alg.x 0) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
    T (alg.x (j - 1)) = (((j + 1) / j) : ℝ) • alg.x j - (1 / j : ℝ) • alg.x 0 := by
  intro j hj; have xj_eq := halpern_xj_formula alg h_α_form h_u_eq_x0 j hj
  rw [xj_eq]; simp only [one_div, smul_add, smul_smul]
  have eq1 :  (((j : ℝ) + 1) / (j : ℝ) * ((j : ℝ) + 1)⁻¹) = ((j : ℝ))⁻¹ := by field_simp
  rw [eq1]; simp only [add_sub_cancel_left]
  have eq2 : ((j + 1: ℝ) / (j : ℝ) * ((j : ℝ) / ((j : ℝ) + 1))) = 1 := by
    field_simp; rw[div_self]; rcases hj.left with hj_pos2; by_contra hj_zero
    have : 1 ≤ (j : ℝ) := Nat.one_le_cast.mpr hj_pos2
    linarith
  rw [eq2]; simp only [one_smul]


lemma halpern_norm_bdd1 [CompleteSpace H] [SeparableSpace H]
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (alg : Halpern T) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  {k : ℕ} (x_star : H) (hx_star_in_C : x_star ∈ C)
  : ‖T (alg.x k) - x_star‖ ^ 2 ≤ ‖alg.x k - x_star‖ ^ 2 := by
  have x_star_in_D : x_star ∈ D := by rw [hC] at hx_star_in_C; exact hx_star_in_C.right
  have : x_star = T x_star := by
    have hx_star_in_FixT : x_star ∈ Fix T := by rw [hC] at hx_star_in_C; exact hx_star_in_C.left
    symm; exact hx_star_in_FixT
  nth_rewrite 1 [this]; apply sq_le_sq.2; simp only [abs_norm]
  simp only [NonexpansiveOn, LipschitzOnWith, ENNReal.coe_one, one_mul] at hT_nonexp
  specialize hT_nonexp (halg_x_in_D k) x_star_in_D
  simp only [edist_dist, dist_eq_norm, ofReal_norm] at hT_nonexp
  exact enorm_le_iff_norm_le.mp hT_nonexp


lemma halpern_norm_bdd2 [CompleteSpace H] [SeparableSpace H]
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D) (alg : Halpern T)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) {k : ℕ} : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
    ‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 ≤ ‖alg.x j - alg.x (j - 1)‖ ^ 2 := by
  intro j hj; apply sq_le_sq.2; simp only [abs_norm]
  simp only [NonexpansiveOn, LipschitzOnWith, ENNReal.coe_one, one_mul] at hT_nonexp
  specialize hT_nonexp (halg_x_in_D j) (halg_x_in_D (j - 1))
  simp only [edist_dist, dist_eq_norm, ofReal_norm] at hT_nonexp
  exact enorm_le_iff_norm_le.mp hT_nonexp


lemma halpern_ineq1 [CompleteSpace H] [SeparableSpace H]
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D)
  (alg : Halpern T) (halg_x_in_D : ∀ n, alg.x n ∈ D) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
    0 ≥ j * (j + 1) * (‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2
      - ‖alg.x j - alg.x (j - 1)‖ ^ 2) := by
  intro j hj
  apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by linarith)) ?_
  simp only [tsub_le_iff_right, zero_add]; apply sq_le_sq.2; simp only [abs_norm]
  specialize hT_nonexp (halg_x_in_D j) (halg_x_in_D (j - 1))
  simp only [edist_dist, dist_eq_norm, ofReal_norm, ENNReal.coe_one, one_mul] at hT_nonexp
  exact enorm_le_iff_norm_le.mp hT_nonexp

lemma halpern_ineq2 [CompleteSpace H] [SeparableSpace H]
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D)
  (alg : Halpern T) (halg_x_in_D : ∀ n, alg.x n ∈ D) {k : ℕ}
  : (0 : ℝ) ≥ ∑ j ∈ Finset.Ico 1 (k + 1), (j : ℝ) * ((j : ℝ) + 1) *
    (‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 - ‖alg.x j - alg.x (j - 1)‖ ^ 2) := by
  apply Finset.sum_nonpos; intro j hj; apply halpern_ineq1 hT_nonexp alg halg_x_in_D
  constructor
  · exact List.left_le_of_mem_range' hj
  · apply Nat.lt_succ_iff.mp
    · simp only [Nat.succ_eq_add_one]; simp only [Finset.mem_Ico] at hj; exact hj.right



lemma halpern_eq3 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) (h_α_form : ∀ n, alg.α n = 1 / (n + 2))
  (h_u_eq_x0 : alg.u = alg.x 0) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → (j : ℝ) * ((j : ℝ) + 1) *
    ‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 = (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - T (alg.x j)‖ ^ 2
      + 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ +
        ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x j - alg.x 0‖ ^ 2 := by
  intro j ⟨hj1, hj2⟩
  have eq1 := halpern_xj_formula alg h_α_form h_u_eq_x0 j ⟨hj1, hj2⟩
  have eq2 := halpern_Tx_formula alg h_α_form h_u_eq_x0 j ⟨hj1, hj2⟩
  calc
    _ = (j : ℝ) * ((j : ℝ) + 1) * ‖-(alg.x j - T (alg.x j) +
      (1 / (j : ℝ)) • (alg.x j - alg.x 0))‖ ^ 2 := by
      congr; rw [eq2, ← sub_add, neg_add, neg_sub, smul_sub, neg_sub]
      simp only [one_div, add_sub]
      have : ((j : ℝ) + 1) / (j : ℝ) = 1 + (1 / (j : ℝ)) := by
        refine same_add_div ?_; intro h_contra
        have : (j : ℝ) ≥ 1 := Nat.one_le_cast.mpr hj1
        linarith
      rw [this, add_smul, ← sub_sub]; simp [@sub_add_eq_add_sub]
    _ = (j : ℝ) * ((j : ℝ) + 1) * (‖alg.x j - T (alg.x j)‖ ^ 2
      + 2 * ⟪alg.x j - T (alg.x j), (1 / (j : ℝ)) • (alg.x j - alg.x 0)⟫
        + ‖(1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2) := by
      congr 1; rw [norm_neg]
      have h_norm_add : ‖(alg.x j - T (alg.x j)) + (1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2 =
        ‖alg.x j - T (alg.x j)‖ ^ 2 + 2 * RCLike.re (inner ℝ (alg.x j - T (alg.x j))
          ((1 / (j : ℝ)) • (alg.x j - alg.x 0))) + ‖(1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2 :=
            norm_add_sq (alg.x j - T (alg.x j)) ((1 / (j : ℝ)) • (alg.x j - alg.x 0))
      simp only [RCLike.re_to_real] at h_norm_add; rw [← h_norm_add]
    _ = (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - T (alg.x j)‖ ^ 2
      + 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫
        + ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x j - alg.x 0‖ ^ 2 := by
      have h_inner_smul : inner ℝ (alg.x j - T (alg.x j)) ((1 / (j : ℝ)) • (alg.x j - alg.x 0))
        = (1 / (j : ℝ)) * inner ℝ (alg.x j - T (alg.x j)) (alg.x j - alg.x 0) := by
        exact real_inner_smul_right (alg.x j - T (alg.x j)) (alg.x j - alg.x 0) (1 / ↑j)
      have h_norm_smul : ‖(1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2
        = (1 / (j : ℝ)) ^ 2 * ‖alg.x j - alg.x 0‖ ^ 2 := by rw [norm_smul, mul_pow]; simp
      rw [h_inner_smul, h_norm_smul]; field_simp


lemma halpern_eq4 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) (h_α_form : ∀ n, alg.α n = 1 / (n + 2))
  (h_u_eq_x0 : alg.u = alg.x 0) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → - (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - alg.x (j - 1)‖ ^ 2
    = - (j : ℝ) / ((j : ℝ) + 1) * ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 -
      2 * (j : ℝ) * ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ -
        (j : ℝ) * ((j : ℝ) + 1) * ‖T (alg.x (j - 1)) - alg.x (j - 1)‖ ^ 2 := by
  intro j ⟨hj1, hj2⟩; have eq1 := halpern_xj_formula alg h_α_form h_u_eq_x0 j ⟨hj1, hj2⟩
  calc
    _ = - (j : ℝ) * ((j : ℝ) + 1) * ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))) +
      (T (alg.x (j - 1)) - alg.x (j - 1))‖ ^ 2 := by
      congr; rw [eq1, ← add_sub]; simp only [one_div, add_sub, sub_left_inj]
      have : (j : ℝ) / ((j : ℝ) + 1) = 1 - (1 / ((j : ℝ) + 1)) := by
        field_simp; rw [sub_eq_add_neg]; simp
      simp only [smul_sub, add_comm, add_sub]; rw [this, sub_smul]; simp [add_sub]
    _ = _ := by
      have h_norm_add : ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))) +
        (T (alg.x (j - 1)) - alg.x (j - 1))‖ ^ 2 =
          ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1)))‖ ^ 2 + 2 *
            ⟪(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))), T (alg.x (j - 1)) - alg.x (j - 1)⟫
              + ‖T (alg.x (j - 1)) - alg.x (j - 1)‖ ^ 2 := by
        let a := (1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1)))
        let b := T (alg.x (j - 1)) - alg.x (j - 1)
        exact norm_add_pow_two_real a b
      have h_norm_smul : ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1)))‖ ^ 2 =
        (1 / ((j : ℝ) + 1)) ^ 2 * ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 := by
        rw [norm_smul, mul_pow]; simp
      have h_inner_smul : ⟪(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))),
        T (alg.x (j - 1)) - alg.x (j - 1)⟫ = (1 / ((j : ℝ) + 1)) * ⟪alg.x 0 - T (alg.x (j - 1)),
            T (alg.x (j - 1)) - alg.x (j - 1)⟫ := real_inner_smul_left (alg.x 0 - T (alg.x (j - 1)))
              (T (alg.x (j - 1)) - alg.x (j - 1)) (1 / ((j : ℝ) + 1))
      rw [h_norm_add, h_norm_smul, h_inner_smul]; field_simp; ring


lemma halpern_eq5 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) (h_α_form : ∀ n, alg.α n = 1 / (n + 2))
  (h_u_eq_x0 : alg.u = alg.x 0) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → - (j : ℝ) / ((j : ℝ) + 1) *
    ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 = - ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x 0 - alg.x j‖ ^ 2 := by
  intro j ⟨hj1, hj2⟩; have eq1 := halpern_xj_formula alg h_α_form h_u_eq_x0 j ⟨hj1, hj2⟩
  calc
    _ = - (j : ℝ) / ((j : ℝ) + 1) *
      ‖(((j : ℝ) + 1) / (j : ℝ)) • alg.x 0 - (((j : ℝ) + 1) / (j : ℝ)) • alg.x j‖ ^ 2 := by
      rw [eq1]; congr 1; refine (sq_eq_sq₀ (by simp) (by simp)).mpr ?_; congr 1
      have h_expand : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → (((j : ℝ) + 1) / (j : ℝ)) • alg.x 0 -
        (((j : ℝ) + 1) / (j : ℝ)) • ((1 / ((j : ℝ) + 1)) • alg.x 0 +
          ((j : ℝ) / ((j : ℝ) + 1)) • T (alg.x (j - 1))) = (((j : ℝ) + 1) / (j : ℝ)) • alg.x 0
            - (((j : ℝ) + 1) / (j : ℝ)) • (1 / ((j : ℝ) + 1)) • alg.x 0 -
              (((j : ℝ) + 1) / (j : ℝ)) • ((j : ℝ) / ((j : ℝ) + 1)) • T (alg.x (j - 1)) := by
                  intro j ⟨hj1, hj2⟩; rw [smul_add, ← sub_sub]
      rw [h_expand j ⟨hj1, hj2⟩]
      have h_cancel : ((↑j + 1) / ↑j) * (↑j / (↑j + 1 : ℝ)) = 1 := by field_simp
      simp [smul_smul, h_cancel, one_smul]; field_simp; ring_nf
      simp only [add_smul, add_sub_cancel_right]
      have : (j : ℝ) * (j : ℝ)⁻¹ = 1 := by field_simp
      rw [this]; simp
    _ = _ := by
      have h_norm_smul : ‖(((j : ℝ) + 1) / (j : ℝ)) • (alg.x 0 - alg.x j)‖ ^ 2 =
        (((j : ℝ) + 1) / (j : ℝ)) ^ 2 * ‖alg.x 0 - alg.x j‖ ^ 2 := by
        rw [norm_smul, mul_pow]; congr; simp; field_simp
        have : (j : ℝ) + 1 > 0 := by linarith
        simp; linarith
      rw [← smul_sub, h_norm_smul]; field_simp


lemma halpern_eq6 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) {k : ℕ} (hk : k ≥ 1)
  : - ∑ j ∈ Finset.Icc 1 k, (2 : ℝ) * j *
    ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = ∑ j ∈
      Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
        ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := by
  have h_reindex : ∑ j ∈ Finset.Icc 1 k, (2 : ℝ) * j *
    ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = ∑ j ∈
      Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
        ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ := by
    rw [Finset.sum_bij (fun j _ => j - 1)]
    · intro j hj; simp [Finset.mem_Icc] at hj ⊢; omega
    · intro j hj; simp [Finset.mem_Icc] at hj ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc, zero_le, true_and, exists_prop] at hj ⊢; use (j + 1)
      constructor
      · constructor
        · linarith
        · exact Nat.add_le_of_le_sub hk hj
      simp
    · intro j hj
      simp only [mul_eq_mul_right_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
      left; symm; calc
        _ = ((j - 1 + 1) : ℝ) := by
          refine (add_left_inj 1).mpr ?_; refine Nat.cast_pred ?_; simp [Finset.mem_Icc] at hj
          omega
        _ = (j : ℝ) := by simp
  rw [h_reindex]
  have h_inner_eq : ∀ j, j ∈ Finset.Icc 0 (k - 1) → ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ =
      - ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := by
    intro j _
    have h1 : T (alg.x j) - alg.x j = -(alg.x j - T (alg.x j)) := by simp
    rw [h1, inner_neg_right]
    have h2 : alg.x 0 - T (alg.x j) = -(T (alg.x j) - alg.x 0) := by simp
    rw [h2, inner_neg_left, inner_neg_right]
    simp only [neg_neg]; exact real_inner_comm (alg.x j - T (alg.x j)) (T (alg.x j) - alg.x 0)
  calc
    _ = -∑ j ∈ Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
      ⟪T (alg.x j) - alg.x j, alg.x 0 - T (alg.x j)⟫ := by
      simp only [neg_inj]; congr; ext j; congr 1
      exact real_inner_comm (T (alg.x j) - alg.x j) (alg.x 0 - T (alg.x j))
    _ = ∑ j ∈ Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
      - ⟪T (alg.x j) - alg.x j, alg.x 0 - T (alg.x j)⟫ := by simp
    _ = ∑ j ∈ Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
      ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := by
      apply Finset.sum_congr rfl; intro j hj; apply congr_arg; simp [← inner_neg_left]


lemma halpern_eq7 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) {k : ℕ} (hk : k ≥ 1)
  : ∑ j ∈ Finset.Icc 1 k, 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫
    = ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ +
      2 * ((k : ℝ) + 1) * ⟪alg.x k - T (alg.x k), alg.x k - alg.x 0⟫ := by
  by_cases hk_eq : k = 1
  · rw [hk_eq]; simp
  · have hk : k ≥ 2 := by
      have : k > 1 := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr fun a ↦ by omega)
        fun a ↦ hk_eq (id (Eq.symm a))
      linarith
    have : k = (k - 1) + 1 := by omega
    nth_rewrite 1 [this]
    rw [Finset.sum_Icc_succ_top]
    · simp [id (Eq.symm this)]
    · linarith

lemma halpern_eq8 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) {k : ℕ} (hk : k ≥ 1)
  : ∑ j ∈ Finset.Icc 1 k, 2 * (j : ℝ) *
    ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = - 2 *
      ‖alg.x 0 - T (alg.x 0)‖ ^ 2 + ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j + 1) : ℝ) *
        ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ := by
  by_cases hk_eq : k = 1
  · rw [hk_eq]; simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, mul_one, tsub_self,
    neg_mul, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero]
    have h1 : T (alg.x 0) - alg.x 0 = -(alg.x 0 - T (alg.x 0)) := by simp
    rw [h1, inner_neg_right]
    have h2 : ‖alg.x 0 - T (alg.x 0)‖ ^ 2 = ⟪(alg.x 0 - T (alg.x 0)), (alg.x 0 - T (alg.x 0))⟫
      := Eq.symm (real_inner_self_eq_norm_sq (alg.x 0 - T (alg.x 0)))
    rw [h2]; ring
  · calc
      _ = ∑ j ∈ Finset.Ico 1 (k + 1), 2 * (j : ℝ) *
        ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ := by congr
      _ = 2 * (1 : ℝ) * ⟪alg.x 0 - T (alg.x (1 - 1)), T (alg.x (1 - 1)) - alg.x (1 - 1)⟫ +
        ∑ j ∈ Finset.Ico 2 (k + 1), 2 * (j : ℝ) *
          ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ := by
        rw [Finset.sum_eq_sum_Ico_succ_bot]
        · simp
        linarith
      _ = - 2 * ‖alg.x 0 - T (alg.x 0)‖ ^ 2 + ∑ j ∈ Finset.Ico 2 (k + 1), 2 * (j : ℝ) *
        ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ := by
        have h1 : T (alg.x 0) - alg.x 0 = -(alg.x 0 - T (alg.x 0)) := by simp
        rw [h1, inner_neg_right]
        have h2 : ‖alg.x 0 - T (alg.x 0)‖ ^ 2 = ⟪(alg.x 0 - T (alg.x 0)), (alg.x 0 - T (alg.x 0))⟫
          := Eq.symm (real_inner_self_eq_norm_sq (alg.x 0 - T (alg.x 0)))
        rw [h2]; ring
      _ = - 2 * ‖alg.x 0 - T (alg.x 0)‖ ^ 2 + ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j + 1) : ℝ) *
        ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ := by
        have h_reindex : ∑ j ∈ Finset.Ico 2 (k + 1), 2 * (j : ℝ) *
          ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ =
            ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j + 1) : ℝ) *
              ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ := by
          rw [Finset.sum_bij (fun j _ => j - 1)]
          · intro j hj; simp [Finset.mem_Ico] at hj ⊢; omega
          · intro j hj; simp [Finset.mem_Ico] at hj ⊢; omega
          · intro j hj; simp only [Finset.mem_Icc, Finset.mem_Ico, exists_prop] at hj ⊢
            use (j + 1); omega
          · intro j hj; simp only [mul_eq_mul_right_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
            or_false]
            left; symm; calc
              _ = ((j - 1 + 1) : ℝ) := by
                refine (add_left_inj 1).mpr ?_; refine Nat.cast_pred ?_
                simp [Finset.mem_Ico] at hj; omega
              _ = (j : ℝ) := by simp only [sub_add_cancel]
        rw [h_reindex]

lemma halpern_eq9 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) {k : ℕ}
  : ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) *
    ⟪(alg.x j - T (alg.x j)), (alg.x j - T (alg.x j))⟫ =
      ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) *
        ⟪(alg.x j - T (alg.x j)), (alg.x j - alg.x 0)⟫ - ∑ j ∈ Finset.Icc 1 (k - 1),
          2 * ((j : ℝ) + 1) * ⟪(alg.x 0 - T (alg.x j)), (T (alg.x j) - alg.x j)⟫ := by
  symm; calc
    _ = ∑ j ∈ Finset.Icc 1 (k - 1), (2 * ((j : ℝ) + 1) *
      ⟪(alg.x j - T (alg.x j)), (alg.x j - alg.x 0)⟫ - 2 * ((j : ℝ) + 1) *
        ⟪(alg.x 0 - T (alg.x j)), (T (alg.x j) - alg.x j)⟫) :=
        Eq.symm (Finset.sum_sub_distrib
          (fun x ↦ 2 * (↑x + 1) * inner ℝ (alg.x x - T (alg.x x)) (alg.x x - alg.x 0)) fun x ↦
            2 * (↑x + 1) * inner ℝ (alg.x 0 - T (alg.x x)) (T (alg.x x) - alg.x x))
    _ = _ := by
      apply Finset.sum_congr rfl; intro j hj; field_simp
      have h_inner : ⟪(alg.x j - T (alg.x j)), (alg.x j - T (alg.x j))⟫ =
        ⟪(alg.x j - T (alg.x j)), (alg.x j - alg.x 0) + (alg.x 0 - T (alg.x j))⟫ := by
          congr; simp
      rw [h_inner, inner_add_right, sub_eq_add_neg]; congr
      simp only [real_inner_comm, ← inner_neg_left, neg_sub]


lemma halpern_eq10 [CompleteSpace H] [SeparableSpace H]
  {T : H → H} (alg : Halpern T) {k : ℕ} (hk : k ≥ 1)
  : 2 * ((k : ℝ) + 1) * ⟪alg.x k - T (alg.x k), alg.x k - alg.x 0⟫ +
    ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - T (alg.x j)⟫
      + 2 * ‖alg.x 0 - T (alg.x 0)‖ ^ 2 = ∑ j ∈ Finset.Icc 1 k, 2 * ((j : ℝ) + 1) *
        ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ - ∑ j ∈ Finset.Icc 1 k, 2 * (j : ℝ) *
          ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ := by
  have eq7 : ∑ j ∈ Finset.Icc 1 k, 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫
    = ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ +
      2 * ((k : ℝ) + 1) * ⟪alg.x k - T (alg.x k), alg.x k - alg.x 0⟫ := halpern_eq7 alg hk
  have eq8 : ∑ j ∈ Finset.Icc 1 k, 2 * (j : ℝ) *
    ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = - 2 *
      ‖alg.x 0 - T (alg.x 0)‖ ^ 2 + ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j + 1) : ℝ) *
        ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ := halpern_eq8 alg hk
  have eq9 : ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) *
    ⟪(alg.x j - T (alg.x j)), (alg.x j - T (alg.x j))⟫ =
      ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) *
        ⟪(alg.x j - T (alg.x j)), (alg.x j - alg.x 0)⟫ - ∑ j ∈ Finset.Icc 1 (k - 1),
          2 * ((j : ℝ) + 1) * ⟪(alg.x 0 - T (alg.x j)), (T (alg.x j) - alg.x j)⟫ := halpern_eq9 alg
  rw [eq7, eq8]; simp [add_comm, ← sub_sub, ← add_assoc]; rw [eq9]; simp [real_inner_comm, add_sub]
































/--
Theorem 2.1: Halpern's Algorithm Convergence Rate
Let x₀ ∈ H be arbitrary but fixed. If T has fixed points, i.e. Fix(T) ≠ ∅,
then the iterates defined in (1) satisfy:
  (1/2)‖xₖ - T(xₖ)‖ ≤ ‖x₀ - x*‖/(k + 1)  ∀k ∈ ℕ, ∀x* ∈ Fix(T)

This bound is tight.
-/
theorem halpern_convergence_rate [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty) (hT_invariant : ∀ x ∈ D, T x ∈ D)
  (alg : Halpern T) (halg_x0 : alg.x0 ∈ D) (halg_u : alg.u ∈ D) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (h_α_limit : Tendsto alg.α atTop (𝓝 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  (h_α_form : ∀ n, alg.α n = 1 / (n + 2)) (h_u_eq_x0 : alg.u = alg.x 0)
  : ∀ (x_star : H), x_star ∈ C → ∀ k : ℕ,
    (1 / 2 : ℝ) * ‖alg.x k - T (alg.x k)‖ ≤ ‖alg.x 0 - x_star‖ / (k + 1) := by
  intro x_star hx_star_in_C k
  have x_star_in_D : x_star ∈ D := by
    rw [hC] at hx_star_in_C; exact hx_star_in_C.right
  by_cases hk : k ≥ 1
  · have eq1 := halpern_xj_formula alg h_α_form h_u_eq_x0 (k := k)
    have eq2 := halpern_Tx_formula alg h_α_form h_u_eq_x0 (k := k)

    have norm_bdd1 : ‖T (alg.x k) - x_star‖ ^ 2 ≤ ‖alg.x k - x_star‖ ^ 2 :=
      halpern_norm_bdd1 hT_nonexp hC alg halg_x_in_D x_star hx_star_in_C

    have norm_bdd2 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
      ‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 ≤ ‖alg.x j - alg.x (j - 1)‖ ^ 2 :=
      halpern_norm_bdd2 hT_nonexp alg halg_x_in_D

    have ineq1 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
      0 ≥ j * (j + 1) * (‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2
        - ‖alg.x j - alg.x (j - 1)‖ ^ 2) :=
      halpern_ineq1 hT_nonexp alg halg_x_in_D

    have ineq2 : (0 : ℝ) ≥ ∑ j ∈ Finset.Ico 1 (k + 1), (j : ℝ) * ((j : ℝ) + 1) *
      (‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 - ‖alg.x j - alg.x (j - 1)‖ ^ 2) :=
      halpern_ineq2 hT_nonexp alg halg_x_in_D

    have eq3 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → (j : ℝ) * ((j : ℝ) + 1) *
      ‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 = (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - T (alg.x j)‖ ^ 2
        + 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ +
          ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x j - alg.x 0‖ ^ 2 :=
      halpern_eq3 alg h_α_form h_u_eq_x0

    have eq4 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → - (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - alg.x (j - 1)‖ ^ 2
      = - (j : ℝ) / ((j : ℝ) + 1) * ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 -
        2 * (j : ℝ) * ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ -
          (j : ℝ) * ((j : ℝ) + 1) * ‖T (alg.x (j - 1)) - alg.x (j - 1)‖ ^ 2 :=
      halpern_eq4 alg h_α_form h_u_eq_x0

    have eq5 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → - (j : ℝ) / ((j : ℝ) + 1) *
      ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 = - ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x 0 - alg.x j‖ ^ 2 :=
      halpern_eq5 alg h_α_form h_u_eq_x0

    have eq6 : - ∑ j ∈ Finset.Icc 1 k, (2 : ℝ) * j *
      ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = ∑ j ∈
        Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
          ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := halpern_eq6 alg hk

    have eq7 : 2 * ((k : ℝ) + 1) * ⟪alg.x k - T (alg.x k), alg.x k - alg.x 0⟫ +
      ∑ j ∈ Finset.Icc 1 (k - 1), 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - T (alg.x j)⟫
        + 2 * ‖alg.x 0 - T (alg.x 0)‖ ^ 2 = ∑ j ∈ Finset.Icc 1 k, 2 * ((j : ℝ) + 1) *
          ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ - ∑ j ∈ Finset.Icc 1 k, 2 * (j : ℝ) *
            ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ :=
      halpern_eq10 alg hk

    have eq8 : ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * ((j : ℝ) + 1) *
      ‖alg.x (j - 1) - T (alg.x (j - 1))‖ ^ 2 = ∑ j ∈ Finset.Icc 0 (k - 1), ((j : ℝ) + 1)
        * ((j : ℝ) + 2) * ‖alg.x j - T (alg.x j)‖ ^ 2 := by
      rw [Finset.sum_bij (fun j _ => j - 1)]
      · intro j hj; simp [Finset.mem_Icc] at hj ⊢; omega
      · intro j hj; simp [Finset.mem_Icc] at hj ⊢; omega
      · intro j hj; simp only [Finset.mem_Icc, zero_le, true_and, exists_prop] at hj ⊢; use (j + 1)
        constructor
        · constructor
          · linarith
          · exact Nat.add_le_of_le_sub hk hj
        simp
      · intro j hj; simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, norm_eq_zero]; left
        have h_j_pos : j ≥ 1 := by simp only [Finset.mem_Icc] at hj; exact hj.1
        have : (j - 1 : ℝ) + 1 = j := by simp
        have : (j - 1 : ℝ) + 2 = j + 1 := by ring
        simp [*]

    have eq9 : ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * ((j : ℝ) + 1) *
      ‖alg.x j - T (alg.x j)‖ ^ 2 -  ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * ((j : ℝ) + 1) *
      ‖alg.x (j - 1) - T (alg.x (j - 1))‖ ^ 2 =
        (k : ℝ) * ((k : ℝ) + 1) * ‖alg.x k - T (alg.x k)‖ ^ 2 - ∑ j ∈
          Finset.Icc 1 (k - 1), ((j : ℝ) + 1) * ((j : ℝ) + 2) * ‖alg.x j - T (alg.x j)‖ ^ 2 := by sorry































    sorry
  · have hk_eq : k = 0 := by exact Nat.eq_zero_of_not_pos hk
    rw [hk_eq]
    simp only [one_div, CharP.cast_eq_zero, zero_add, div_one, ge_iff_le]
    rw[mul_comm]
    apply mul_le_of_le_mul_inv₀ (by simp) (by simp)
    simp
    calc
      _ = ‖(alg.x 0 - x_star) - (T (alg.x 0) - x_star)‖ := by simp
      _ ≤ ‖alg.x 0 - x_star‖ + ‖T (alg.x 0) - x_star‖ := norm_sub_le _ _
      _ ≤ ‖alg.x 0 - x_star‖ + ‖alg.x 0 - x_star‖ := by
        have : x_star = T x_star := by
          have hx_star_in_FixT : x_star ∈ Fix T := by
            rw [hC] at hx_star_in_C; exact hx_star_in_C.left
          simp only at hx_star_in_FixT
          symm; exact hx_star_in_FixT
        simp only [add_le_add_iff_left, ge_iff_le]
        nth_rewrite 1 [this]
        simp only [NonexpansiveOn, LipschitzOnWith, ENNReal.coe_one, one_mul] at hT_nonexp
        specialize hT_nonexp (halg_x_in_D 0) x_star_in_D
        simp only [edist_dist, dist_eq_norm, ofReal_norm] at hT_nonexp
        exact enorm_le_iff_norm_le.mp hT_nonexp
      _ = _ := by ring
