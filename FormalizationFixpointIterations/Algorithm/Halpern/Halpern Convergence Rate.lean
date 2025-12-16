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
    simp [mul_add, add_comm, add_mul, sub_mul]
    have eq2 : ↑(j - 1) = (j : ℝ) - 1 := Nat.cast_pred (by linarith)
    rw [eq2]; ring
  have eq2 : alg.α (j - 1) = 1 / (j + 1) := by
    rw [h_α_form (j - 1)]; norm_cast; field_simp [Nat.succ_eq_add_one]; simp
    have eq3 : ↑(j - 1) = (j : ℝ) - 1 := Nat.cast_pred (by linarith)
    rw [eq3]; ring_nf
  rw [eq1, eq2] at xj_eq; assumption

lemma halpern_Tx_formula
  {T : H → H} (alg : Halpern T) (h_α_form : ∀ n, alg.α n = 1 / (n + 2))
  (h_u_eq_x0 : alg.u = alg.x 0) {k : ℕ}
  : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
    T (alg.x (j - 1)) = (((j + 1) / j) : ℝ) • alg.x j - (1 / j : ℝ) • alg.x 0 := by
  intro j hj; have xj_eq := halpern_xj_formula alg h_α_form h_u_eq_x0 j hj
  rw [xj_eq]; simp [smul_add, smul_smul]
  have eq1 :  (((j : ℝ) + 1) / (j : ℝ) * ((j : ℝ) + 1)⁻¹) = ((j : ℝ))⁻¹ := by field_simp
  rw [eq1]; simp
  have eq2 : ((j + 1: ℝ) / (j : ℝ) * ((j : ℝ) / ((j : ℝ) + 1))) = 1 := by
    field_simp
    rw[div_self]
    rcases hj.left with hj_pos2
    by_contra hj_zero
    have : 1 ≤ (j : ℝ) := by
      exact Nat.one_le_cast.mpr hj_pos2
    linarith
  rw [eq2]; simp

































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
  · have eq1 := halpern_xj_formula alg h_α_form h_u_eq_x0 (k :=k)
    have eq2 := halpern_Tx_formula alg h_α_form h_u_eq_x0 (k :=k)

    have norm_bdd1 : ‖T (alg.x k) - x_star‖ ^ 2 ≤ ‖alg.x k - x_star‖ ^ 2 := by
      have : x_star = T x_star := by
        have hx_star_in_FixT : x_star ∈ Fix T := by
          rw [hC] at hx_star_in_C; exact hx_star_in_C.left
        simp [Fix, Function.IsFixedPt] at hx_star_in_FixT
        symm; exact hx_star_in_FixT
      nth_rewrite 1 [this]
      apply sq_le_sq.2
      simp
      simp [NonexpansiveOn,  LipschitzOnWith] at hT_nonexp
      specialize hT_nonexp (halg_x_in_D k) x_star_in_D
      simp [edist_dist, dist_eq_norm] at hT_nonexp
      exact enorm_le_iff_norm_le.mp hT_nonexp

    have norm_bdd2 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → ‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 ≤ ‖alg.x j - alg.x (j - 1)‖ ^ 2 := by
      intro j hj
      apply sq_le_sq.2
      simp
      simp [NonexpansiveOn,  LipschitzOnWith] at hT_nonexp
      specialize hT_nonexp (halg_x_in_D j) (halg_x_in_D (j - 1))
      simp [edist_dist, dist_eq_norm] at hT_nonexp
      exact enorm_le_iff_norm_le.mp hT_nonexp

    have ineq1 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k →
      0 ≥ j * (j + 1) * (‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2
        - ‖alg.x j - alg.x (j - 1)‖ ^ 2) := by
      intro j hj
      refine mul_nonpos_of_nonneg_of_nonpos ?_ ?_
      apply mul_nonneg (by linarith) (by linarith)
      simp
      apply sq_le_sq.2
      simp
      simp [NonexpansiveOn,  LipschitzOnWith] at hT_nonexp
      specialize hT_nonexp (halg_x_in_D j) (halg_x_in_D (j - 1))
      simp [edist_dist, dist_eq_norm] at hT_nonexp
      exact enorm_le_iff_norm_le.mp hT_nonexp

    have ineq2 : (0 : ℝ) ≥ ∑ j ∈ Finset.Ico 1 (k + 1), (j : ℝ) * ((j : ℝ) + 1) *
      (‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 - ‖alg.x j - alg.x (j - 1)‖ ^ 2) := by
      apply Finset.sum_nonpos
      intro j hj
      apply ineq1
      constructor
      · exact List.left_le_of_mem_range' hj
      · apply Nat.lt_succ_iff.mp
        simp
        simp [Finset.mem_Ico] at hj
        exact hj.right

    have eq3 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → (j : ℝ) * ((j : ℝ) + 1) *
      ‖T (alg.x j) - T (alg.x (j - 1))‖ ^ 2 = (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - T (alg.x j)‖ ^ 2
        + 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ +
          ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x j - alg.x 0‖ ^ 2 := by
      intro j ⟨hj1, hj2⟩
      calc
        _ = (j : ℝ) * ((j : ℝ) + 1) * ‖-(alg.x j - T (alg.x j) +
          (1 / (j : ℝ)) • (alg.x j - alg.x 0))‖ ^ 2 := by
          congr
          rw [eq2, ← sub_add, neg_add, neg_sub, smul_sub, neg_sub]
          simp [add_sub]
          have : ((j : ℝ) + 1) / (j : ℝ) = 1 + (1 / (j : ℝ)) := by
            refine same_add_div ?_
            intro h_contra
            have : (j : ℝ) ≥ 1 := by
              exact Nat.one_le_cast.mpr hj1
            linarith
          rw [this, add_smul, ← sub_sub]
          simp [@sub_add_eq_add_sub]
          exact ⟨hj1, hj2⟩
        _ = (j : ℝ) * ((j : ℝ) + 1) * (‖alg.x j - T (alg.x j)‖ ^ 2
          + 2 * ⟪alg.x j - T (alg.x j), (1 / (j : ℝ)) • (alg.x j - alg.x 0)⟫
            + ‖(1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2) := by
          congr 1
          rw [norm_neg]
          have h_norm_add : ‖(alg.x j - T (alg.x j)) + (1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2 =
            ‖alg.x j - T (alg.x j)‖ ^ 2 + 2 * RCLike.re (inner ℝ (alg.x j - T (alg.x j))
              ((1 / (j : ℝ)) • (alg.x j - alg.x 0))) + ‖(1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2 :=
                norm_add_sq (alg.x j - T (alg.x j)) ((1 / (j : ℝ)) • (alg.x j - alg.x 0))
          simp only [RCLike.re_to_real] at h_norm_add
          rw [← h_norm_add]
        _ = (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - T (alg.x j)‖ ^ 2
          + 2 * ((j : ℝ) + 1) * ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫
            + ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x j - alg.x 0‖ ^ 2 := by
          have h_inner_smul : inner ℝ (alg.x j - T (alg.x j)) ((1 / (j : ℝ)) • (alg.x j - alg.x 0))
            = (1 / (j : ℝ)) * inner ℝ (alg.x j - T (alg.x j)) (alg.x j - alg.x 0) := by
            exact real_inner_smul_right (alg.x j - T (alg.x j)) (alg.x j - alg.x 0) (1 / ↑j)
          have h_norm_smul : ‖(1 / (j : ℝ)) • (alg.x j - alg.x 0)‖ ^ 2
            = (1 / (j : ℝ)) ^ 2 * ‖alg.x j - alg.x 0‖ ^ 2 := by
            rw [norm_smul, mul_pow]
            simp
          rw [h_inner_smul, h_norm_smul]
          field_simp



    have eq4 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → - (j : ℝ) * ((j : ℝ) + 1) * ‖alg.x j - alg.x (j - 1)‖ ^ 2
      = - (j : ℝ) / ((j : ℝ) + 1) * ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 -
        2 * (j : ℝ) * ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ -
          (j : ℝ) * ((j : ℝ) + 1) * ‖T (alg.x (j - 1)) - alg.x (j - 1)‖ ^ 2 := by
      intro j ⟨hj1, hj2⟩
      calc
        _ = - (j : ℝ) * ((j : ℝ) + 1) * ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))) +
          (T (alg.x (j - 1)) - alg.x (j - 1))‖ ^ 2 := by
          congr
          rw [eq1, ← add_sub]
          simp [add_sub]
          have : (j : ℝ) / ((j : ℝ) + 1) = 1 - (1 / ((j : ℝ) + 1)) := by
            field_simp
            rw [sub_eq_add_neg]
            simp
          simp [smul_sub, add_comm, add_sub]
          rw [this, sub_smul]
          simp [add_sub]
          exact ⟨hj1, hj2⟩
        _ = _ := by
          have h_norm_add : ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))) +
            (T (alg.x (j - 1)) - alg.x (j - 1))‖ ^ 2 =
            ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1)))‖ ^ 2 +
            2 * ⟪(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))),
              T (alg.x (j - 1)) - alg.x (j - 1)⟫ +
            ‖T (alg.x (j - 1)) - alg.x (j - 1)‖ ^ 2 := by
            let a := (1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1)))
            let b := T (alg.x (j - 1)) - alg.x (j - 1)
            exact norm_add_pow_two_real a b
          have h_norm_smul : ‖(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1)))‖ ^ 2 =
            (1 / ((j : ℝ) + 1)) ^ 2 * ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 := by
            rw [norm_smul, mul_pow]
            simp
          have h_inner_smul : ⟪(1 / ((j : ℝ) + 1)) • (alg.x 0 - T (alg.x (j - 1))),
            T (alg.x (j - 1)) - alg.x (j - 1)⟫ =
            (1 / ((j : ℝ) + 1)) * ⟪alg.x 0 - T (alg.x (j - 1)),
              T (alg.x (j - 1)) - alg.x (j - 1)⟫ := by
            exact real_inner_smul_left (alg.x 0 - T (alg.x (j - 1)))
              (T (alg.x (j - 1)) - alg.x (j - 1)) (1 / ((j : ℝ) + 1))
          rw [h_norm_add, h_norm_smul, h_inner_smul]
          field_simp
          ring

    have eq5 : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → - (j : ℝ) / ((j : ℝ) + 1) *
      ‖alg.x 0 - T (alg.x (j - 1))‖ ^ 2 = - ((j : ℝ) + 1) / (j : ℝ) * ‖alg.x 0 - alg.x j‖ ^ 2 := by
      intro j ⟨hj1, hj2⟩
      calc
        _ = - (j : ℝ) / ((j : ℝ) + 1) *
          ‖(((j : ℝ) + 1) / (j : ℝ)) • alg.x 0 - (((j : ℝ) + 1) / (j : ℝ)) • alg.x j‖ ^ 2 := by
          rw [eq1 j ⟨hj1, hj2⟩]
          congr 1
          refine (sq_eq_sq₀ (by simp) (by simp)).mpr ?_
          congr 1
          have h_expand : ∀ j : ℕ, 1 ≤ j ∧ j ≤ k → (((j : ℝ) + 1) / (j : ℝ)) • alg.x 0 -
            (((j : ℝ) + 1) / (j : ℝ)) • ((1 / ((j : ℝ) + 1)) • alg.x 0 +
              ((j : ℝ) / ((j : ℝ) + 1)) • T (alg.x (j - 1))) = (((j : ℝ) + 1) / (j : ℝ)) • alg.x 0
                - (((j : ℝ) + 1) / (j : ℝ)) • (1 / ((j : ℝ) + 1)) • alg.x 0 -
                  (((j : ℝ) + 1) / (j : ℝ)) • ((j : ℝ) / ((j : ℝ) + 1)) • T (alg.x (j - 1)) := by
                  intro j ⟨hj1, hj2⟩
                  rw [smul_add, ← sub_sub]
          rw [h_expand j ⟨hj1, hj2⟩]
          have h_cancel1 : ((↑j + 1) / ↑j) * (1 / (↑j + 1 : ℝ)) = 1 / ↑j := by field_simp
          have h_cancel2 : ((↑j + 1) / ↑j) * (↑j / (↑j + 1 : ℝ)) = 1 := by field_simp
          simp only [smul_smul, h_cancel1, h_cancel2, one_smul]
          simp
          field_simp
          ring_nf
          simp [add_smul]
          have : (j : ℝ) * (j : ℝ)⁻¹ = 1 := by field_simp
          rw [this]; simp
        _ = _ := by
          have h_norm_smul : ‖(((j : ℝ) + 1) / (j : ℝ)) • (alg.x 0 - alg.x j)‖ ^ 2 =
            (((j : ℝ) + 1) / (j : ℝ)) ^ 2 * ‖alg.x 0 - alg.x j‖ ^ 2 := by
            rw [norm_smul, mul_pow]
            congr
            simp
            field_simp
            have : (j : ℝ) + 1 > 0 := by linarith
            simp
            linarith
          rw [← smul_sub, h_norm_smul]
          field_simp

    have eq6 : - ∑ j ∈ Finset.Icc 1 k, (2 : ℝ) * j *
      ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = ∑ j ∈
        Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
          ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := by
      have h_reindex : ∑ j ∈ Finset.Icc 1 k, (2 : ℝ) * j *
        ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ = ∑ j ∈
          Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
            ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ := by
        rw [Finset.sum_bij (fun j _ => j - 1)]
        · intro j hj
          simp [Finset.mem_Icc] at hj ⊢
          omega
        · intro j hj
          simp [Finset.mem_Icc] at hj ⊢
          omega
        · intro j hj
          simp [Finset.mem_Icc] at hj ⊢
          use (j + 1)
          omega
        · intro j hj
          simp
          left
          symm
          calc
            _ = ((j - 1 + 1) : ℝ) := by
              refine (add_left_inj 1).mpr ?_
              refine Nat.cast_pred ?_
              simp [Finset.mem_Icc] at hj
              omega
            _ = (j : ℝ) := by simp
      rw [h_reindex]
      have h_inner_eq : ∀ j, j ∈ Finset.Icc 0 (k - 1) →
        ⟪alg.x 0 - T (alg.x j), T (alg.x j) - alg.x j⟫ =
          - ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := by
        intro j _
        have h1 : T (alg.x j) - alg.x j = -(alg.x j - T (alg.x j)) := by simp
        rw [h1, inner_neg_right]
        have h2 : alg.x 0 - T (alg.x j) = -(T (alg.x j) - alg.x 0) := by simp
        rw [h2, inner_neg_left, inner_neg_right]
        simp
        exact real_inner_comm (alg.x j - T (alg.x j)) (T (alg.x j) - alg.x 0)
      calc
        _ = -∑ j ∈ Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
          ⟪T (alg.x j) - alg.x j, alg.x 0 - T (alg.x j)⟫ := by
          simp
          congr
          ext j
          congr 1
          exact real_inner_comm (T (alg.x j) - alg.x j) (alg.x 0 - T (alg.x j))
        _ = ∑ j ∈ Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
          - ⟪T (alg.x j) - alg.x j, alg.x 0 - T (alg.x j)⟫ := by
          simp
        _ = ∑ j ∈ Finset.Icc 0 (k - 1), (2 : ℝ) * (j + 1) *
          ⟪alg.x j - T (alg.x j), alg.x 0 - T (alg.x j)⟫ := by
          apply Finset.sum_congr rfl
          intro j hj
          apply congr_arg
          simp [← inner_neg_left]

    have eq7 : 2 * ((k : ℝ) + 1) * ⟪alg.x k - T (alg.x k), alg.x k - alg.x 0⟫ +
      2 * ∑ j ∈ Finset.Icc 1 (k - 1), ((j : ℝ) + 1) * (⟪alg.x j - T (alg.x j), alg.x j - T (alg.x j)⟫
        + 2 * ‖alg.x 0 - T (alg.x 0)‖ ^ 2) = ∑ j ∈ Finset.Icc 1 k, 2 * ((j : ℝ) + 1) *
          ⟪alg.x j - T (alg.x j), alg.x j - alg.x 0⟫ - ∑ j ∈ Finset.Icc 1 k, 2 * (j : ℝ) *
            ⟪alg.x 0 - T (alg.x (j - 1)), T (alg.x (j - 1)) - alg.x (j - 1)⟫ := by











    sorry
  · have hk_eq : k = 0 := by exact Nat.eq_zero_of_not_pos hk
    rw [hk_eq]
    simp
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
          simp [Fix, Function.IsFixedPt] at hx_star_in_FixT
          symm; exact hx_star_in_FixT
        simp
        nth_rewrite 1 [this]
        simp [NonexpansiveOn,  LipschitzOnWith] at hT_nonexp
        specialize hT_nonexp (halg_x_in_D 0) x_star_in_D
        simp [edist_dist, dist_eq_norm] at hT_nonexp
        exact enorm_le_iff_norm_le.mp hT_nonexp
      _ = _ := by ring
