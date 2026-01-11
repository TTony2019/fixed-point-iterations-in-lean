/-
Copyright (c) 2025 Jian Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jian Yu
-/
import FormalizationFixpointIterations.Algorithm.KM.Lemma
open Set Filter Topology TopologicalSpace Metric BigOperators Finset Function Nonexpansive_operator

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Krasnosel'skii-Mann iteration structure
-/
structure KM (D : Set H) (T : H → H) where
  x0 : H
  hx0 : x0 ∈ D
  stepsize : ℕ → ℝ
  hstepsize : ∀ n, stepsize n ∈ Set.Icc (0 : ℝ) 1
  hstepsize_sum : Tendsto (fun n => ∑ i ∈ range (n+1), stepsize i * (1 - stepsize i)) atTop atTop
  x : ℕ → H
  update : ∀ n, x (n + 1) = x n + stepsize n • (T (x n) - x n)
  initial_value : x 0 = x0
  fix_T_nonempty : (FixOn T D).Nonempty


-- The formalization of Groetsch's theorem for Krasnosel'skii-Mann iteration

/--
The important inequalities (5.16) in the proof process\
`‖x (n + 1) - y‖^2 ≤ ‖x n - y‖^2- λ n * (1 - λ n) * ‖T (x n) - x n‖^2`.
Here km.stepsize n corresponds to λ n in the paper.
-/
lemma key_inequality {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
(hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    ∀ (y : H) (hy : y ∈ FixOn T D) (n : ℕ),
      ‖km.x (n + 1) - y‖^2 ≤ ‖km.x n - y‖^2
      - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖^2 := by
    intro y hy n
    rcases hy with ⟨-, hyfix⟩
    --  obtain 0 ≤ s and s ≤ 1 from km.hstepsize n
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    calc
      ‖km.x (n + 1) - y‖^2
          = ‖(1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y)‖^2 := by
            rw [km.update n]
            simp only [smul_sub, sub_smul, one_smul]
            abel_nf
      _ = (1 - km.stepsize n) * ‖km.x n - y‖^2  + km.stepsize n * ‖T (km.x n) - y‖^2
          - km.stepsize n * (1 - km.stepsize n) * ‖(T (km.x n) - y) - ( km.x n - y)‖^2 := by
            -- apply Corollary_2_15 with arguments arranged to match this expression
            have h := convex_combination_norm_sq_identity (T (km.x n) - y) (km.x n - y) (km.stepsize n)
            -- swap the summands inside the norm so the lemma matches exactly
            have add_comm_eq : (1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y) =
            km.stepsize n • (T (km.x n) - y) + (1 - km.stepsize n) • (km.x n - y) := by simp [add_comm]
            rw [add_comm_eq]
            rw[eq_sub_iff_add_eq , h]
            ring
      _ ≤ (1 - km.stepsize n) * ‖km.x n - y‖^2 + km.stepsize n * ‖km.x n - y‖^2 -km.stepsize n * (1 - km.stepsize n) *‖(T (km.x n) - km.x n )‖^2  := by
          have hT_le : ‖T (km.x n) - y‖ ≤ ‖km.x n - y‖ := by
            nth_rw 1 [← hyfix]
            exact hT_nonexpansive (km.x n) y
          simp only [sub_sub_sub_cancel_right, tsub_le_iff_right, sub_add_cancel,
            add_le_add_iff_left, ge_iff_le]
          apply mul_le_mul_of_nonneg_left _ hs_nonneg
          refine pow_le_pow_left₀ ?_ hT_le 2
          exact norm_nonneg _
      _ = ‖km.x n - y‖^2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖^2 := by
          ring

/--
Sequence `x` in KM algorithm is Fejer monotone with respect to Fix T.
-/
lemma groetsch_theorem_i {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    IsFejerMonotone km.x (FixOn T D) := by
    intro y hy n
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have calc1 :‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 := by
      calc
      ‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ ^ 2 := by
        exact key_inequality T h_Im_T_in_D hT_nonexpansive km y hy n
      _≤ ‖km.x n - y‖ ^ 2 := by
        have h_nonneg : 0 ≤ km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - y - (km.x n - y)‖ ^ 2 := by
          apply mul_nonneg
          · apply mul_nonneg
            · exact hs_nonneg
            · exact sub_nonneg.mpr hs_le_one   -- 1 - s ≥ 0
          · exact pow_nonneg (norm_nonneg _) 2
        simp at h_nonneg
        linarith
    have := (sq_le_sq).mp calc1
    repeat rw[abs_of_nonneg (norm_nonneg _)] at this
    exact this

/--
Sequence `T (x n) - x n` in KM algorithm converges strongly to 0.
-/
lemma groetsch_theorem_ii {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    (Tendsto (fun n ↦ ‖T (km.x n) - km.x n‖)  atTop (𝓝 0)) := by
  rcases km.fix_T_nonempty with ⟨y0, hy0⟩
  have sum_bound : ∀ N, ∑  i ∈ range (N), km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 - ‖km.x (N) - y0‖ ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hN := key_inequality T h_Im_T_in_D hT_nonexpansive km y0 hy0 N
      simp [Finset.sum_range_succ]
      linarith
  have partial_le : ∀ N, ∑ i ∈ Finset.range N, km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 := by
      intro N
      refine (sum_bound N).trans ?_
      simp
  let a := fun n => ‖T (km.x n) - km.x n‖ -- define a_n = ‖T x_n - x_n‖
  have a_noninc : ∀ n, a (n + 1) ≤ a n := by
    intro n
    rcases km.hstepsize n with ⟨hs0, hs1⟩
    -- x_{n+1} - x_n = s_n • (T x_n - x_n)
    have hx : km.x (n + 1) - km.x n = km.stepsize n • (T (km.x n) - km.x n) := by
      rw [km.update n]; simp [ smul_sub]
    have eq : T (km.x (n + 1)) - km.x (n + 1) = (T (km.x (n + 1)) - T (km.x n)) + (1 - km.stepsize n) • (T (km.x n) - km.x n) := by
      calc
        T (km.x (n + 1)) - km.x (n + 1) = T (km.x (n + 1)) - T (km.x n) + T (km.x n) - km.x (n + 1) := by simp
        _ = T (km.x (n + 1)) - T (km.x n) + (1 - km.stepsize n) • (T (km.x n) - km.x n) := by
          nth_rw 2 [km.update n]
          simp only [smul_sub, sub_smul, one_smul]
          abel_nf
    calc
      a (n + 1) = ‖T (km.x (n + 1)) - km.x (n + 1)‖ := rfl
      _ = ‖(T (km.x (n + 1)) - T (km.x n)) + (1 - km.stepsize n) • (T (km.x n) - km.x n)‖ := by rw [eq]
      _ ≤ ‖T (km.x (n + 1)) - T (km.x n)‖ + ‖(1 - km.stepsize n) • (T (km.x n) - km.x n)‖ := by apply norm_add_le
      _ ≤ ‖km.x (n + 1) - km.x n‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by
        apply add_le_add
        · exact (hT_nonexpansive (km.x (n + 1)) (km.x n))
        have h_nonneg : 0 ≤ 1 - km.stepsize n := by linarith
        -- prove ‖(1 - s) • v‖ ≤ (1 - s) * ‖v‖
        calc
          ‖(1 - km.stepsize n) • (T (km.x n) - km.x n)‖
              = ‖(1 - km.stepsize n)‖ * ‖T (km.x n) - km.x n‖ := by rw [norm_smul]
          _ = |1 - km.stepsize n| * ‖T (km.x n) - km.x n‖ := by rw [Real.norm_eq_abs]
          _ = (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [abs_of_nonneg h_nonneg]
        linarith
      _= ‖km.stepsize n • (T (km.x n) - km.x n)‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [hx]
      _= km.stepsize n * ‖T (km.x n) - km.x n‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hs0)]
      _= ‖T (km.x n) - km.x n‖ := by ring
  rw [Converge_iff _ _]
  --Conduct a case-by-case analysis. If x0 = y0,trivial. Otherwise, use the method of contradiction.
  by_cases h_x0_eq_y0:  km.x 0 = y0
  · intro ε εpos
    use 0
    intro n hn
    rcases hy0 with ⟨-, hyfix⟩
    rw[← h_x0_eq_y0] at hyfix
    have fixed_point: T (km.x n) - km.x n = 0 := by
      induction n with
      | zero => rw[sub_eq_zero]; exact hyfix
      | succ i ih => rw [km.update i];simp [ih _]
    rw[fixed_point];simpa
  --x0 ≠ y0. Prove by contradiction: If a does not converge to 0, then there exists ε > 0 such that for any N, there is n ≥ N with a n ≥ ε
  by_contra! hnot
  rcases hnot with ⟨ε, εpos, hε⟩
  have tend := km.hstepsize_sum
  -- The partial sum S is greater than 2*‖x0 - y0‖^2 / ε^2 starting from some N0
  have tend_prop := (Filter.tendsto_atTop_atTop.mp tend) (2*‖km.x 0 - y0‖ ^ 2 / ε^2)
  rcases tend_prop with ⟨N0, hN0⟩
  -- pick n0 ≥ N0 and (a n0) ≥ ε
  rcases (hε N0) with ⟨n0, hn0_ge, hn0_ge_eps⟩
  -- For the partial sum up to n0 + 1, use the monotonicity a_i ≥ a_{n0} (for i ≤ n0) to obtain a lower bound
  have lower : ∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2 ≥
      ∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i)*ε ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have : i ≤ n0 := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have ai_ge : a i ≥ a n0 := by
      exact (antitone_nat_of_succ_le a_noninc) (by omega)
    have ai_ge_eps : ε ≤ a i := by
      have h : ε ≤ ‖T (km.x n0) - km.x n0‖ := by
        by_contra! H  -- H: ‖T (km.x n0) - km.x n0‖ < ε
        rw[← zero_add ε ] at H
        exact hn0_ge_eps ⟨by linarith [norm_nonneg (T (km.x n0) - km.x n0)], H⟩
      linarith
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (le_of_lt εpos) ai_ge_eps 2
    rcases km.hstepsize i with ⟨hs0, hs1⟩
    · apply mul_nonneg
      · exact hs0
      · exact sub_nonneg.mpr hs1
  -- S ≥ 2*‖x0-y0‖^2 / ε^2
  have S_ge : ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i)
  ≥ 2*‖km.x 0 - y0‖ ^ 2 / ε^2:= by
    apply hN0
    exact le_trans (by linarith : N0 ≤ n0) (le_refl _)
  -- combine the upper and lower bounds to get a contradiction
  have lb: ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2
  ≥ (2* ‖km.x 0 - y0‖ ^ 2 ) := by
    calc
      ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2
          ≥ ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * ε ^ 2 := by
            exact lower
      _ = ε ^ 2 *(∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i))  := by
        have : (∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * ε ^ 2) =
            ∑ i ∈ range (n0 + 1), ε ^ 2 * (km.stepsize i * (1 - km.stepsize i) ) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [this]
        -- Move ε^2 to the outside of the summation.
        rw [← @Finset.mul_sum ℕ _ _ (range (n0 + 1))
        (fun i => km.stepsize i * (1 - km.stepsize i)) (ε ^ 2)]
      _ ≥ 2*‖km.x 0 - y0‖ ^ 2 := by
        have hpos : 0 ≤ ε ^ 2 := by exact pow_nonneg (le_of_lt εpos) 2
        calc
          ε ^ 2 * (∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i))
          _ ≥ ε ^ 2 * (2* ‖km.x 0 - y0‖ ^ 2 / ε ^ 2) := by apply mul_le_mul_of_nonneg_left S_ge hpos
          _ = 2*‖km.x 0 - y0‖ ^ 2 := by
            field_simp [ne_of_gt εpos]
  have ub := partial_le (n0 + 1)
  have mid: 2 * ‖km.x 0 - y0‖ ^ 2 > ‖km.x 0 - y0‖ ^ 2 := by
    refine lt_two_mul_self ?_
    have h_sub_ne : km.x 0 - y0 ≠ 0 := by
      intro h
      apply h_x0_eq_y0
      rw[sub_eq_zero] at h
      exact h
    have h_norm_pos : 0 < ‖km.x 0 - y0‖ := by
      apply norm_pos_iff.mpr
      exact h_sub_ne
    have : 0 < ‖km.x 0 - y0‖ ^ 2 := pow_pos h_norm_pos (2)
    exact this
  linarith

/--
Sequence `x n` in KM algorithm converges weakly to a point `y0` in Fix T.
-/
lemma groetsch_theorem_iii [SeparableSpace H] [CompleteSpace H] {D : Set H}
(hD_convex : Convex ℝ D) (hD_closed : IsClosed D) (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
(hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (km : KM D T) :
    ∃ y0 ∈ (FixOn T D), WeakConverge km.x y0 := by
  have h_fejer := (groetsch_theorem_i hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km)
  have h_x : ∀ n, km.x n ∈ D := by  --The proposition that D is a convex set is only used in the third conclusion.
    intro n                          --That is, conclusions (i) and (ii) do not require that D be a convex closed set.
    induction n with
    | zero =>  rw [km.initial_value];exact km.hx0
    | succ n ih =>
    have eq : km.x (n + 1) = (1 - km.stepsize n) • km.x n + km.stepsize n • (T (km.x n)) := by
      rw [km.update n]
      simp [smul_sub, sub_smul, one_smul]
      abel_nf
    have h1 : T (km.x n) ∈ D := h_Im_T_in_D (km.x n) ih
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have combo_in : (1 - km.stepsize n) • km.x n + km.stepsize n • T (km.x n) ∈ D := by
      exact hD_convex (ih) h1 (sub_nonneg.mpr hs_le_one) (hs_nonneg) (sub_add_cancel _ _)
    rw [eq]
    exact combo_in
  --Prove that D is a sequentially weakly closed set --Theorem 3.34
  have h_D_seq_weak_closed : IsWeaklySeqClosed D := closed_is_weakly_seq_closed D hD_convex hD_closed
  have hT_nonexp : NonexpansiveOn T D := by
    intro x hx y hy
    simp only [edist_dist, ENNReal.coe_one, one_mul, dist_nonneg, ENNReal.ofReal_le_ofReal_iff]; rw [dist_eq_norm, dist_eq_norm]
    exact hT_nonexpansive x y
  have h_weak_cluster_in : ∀ p : H, HasWeakSubseq p km.x → p ∈ (FixOn T D)  := by
    intro p h_cluster
    rcases h_cluster with ⟨ φ, hφ , tend ⟩
    have p_in_D : p ∈ D := by
      have : ∀ n, (⇑(toWeakSpace ℝ H) ∘ fun k ↦ km.x (φ k)) n ∈ ⇑(toWeakSpace ℝ H) '' D := by
        intro n
        simp only [comp_apply, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
        exact Set.mem_preimage.mp (h_x (φ n))
      obtain h := h_D_seq_weak_closed this tend
      exact inter_singleton_nonempty.mp (h_D_seq_weak_closed this tend)
    -- Prove that p is a fixpoint of T.
    have h_error_zero : Tendsto (fun n ↦ km.x (φ n) - T (km.x (φ n))) atTop (𝓝 0):= by
      have h1 : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
      have h2 : Tendsto (fun n ↦ km.x n - T (km.x n)) atTop (𝓝 0) := by
        -- ‖T (km.x n) - km.x n‖ → 0
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have eq: Tendsto (fun n ↦ ‖km.x n - T (km.x n)‖) atTop (𝓝 0) ↔
          Tendsto (fun n ↦ ‖T (km.x n)- km.x n‖) atTop (𝓝 0) := by
          apply tendsto_congr
          intro n
          rw [norm_sub_rev]
        rw[eq]
        exact (groetsch_theorem_ii hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km)
      exact Tendsto.comp h2 h1
    have D_nonempty: (D).Nonempty := by
      exact ⟨ km.x0,km.hx0⟩
    have := corollary_4_28 hD_closed hD_convex D_nonempty hT_nonexp (fun n => km.x (φ n) ) (fun n => h_x (φ n) )
      p p_in_D tend h_error_zero
    exact ⟨ p_in_D, this ⟩
  apply WeakConv_of_Fejermonotone_of_clusterpt_in (FixOn T D) (km.fix_T_nonempty) km.x h_fejer h_weak_cluster_in

/--
Formalization of Groetsch's theorem for Krasnosel'skii-Mann iteration
-/
theorem groetsch_theorem [SeparableSpace H] [CompleteSpace H] {D : Set H}
    (hD_convex : Convex ℝ D) (hD_closed : IsClosed D) (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
    (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (km : KM D T) :
    -- (i) Fejér monotonicity
    IsFejerMonotone km.x (FixOn T D)
    -- (ii) converges strongly to 0
    ∧(Tendsto (fun n ↦ ‖T (km.x n) - km.x n‖)  atTop (𝓝 0))
    -- (iii) converges weakly to a fixpoint
    ∧∃ y0 ∈ (FixOn T D),WeakConverge km.x y0
    :=
      ⟨
        groetsch_theorem_i hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km,
        groetsch_theorem_ii hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km,
        groetsch_theorem_iii hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km
      ⟩
