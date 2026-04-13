/-
Copyright (c) 2025 Jian Yu, Yifan Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jian Yu, Yifan Bai
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
  α : ℕ → ℝ
  x : ℕ → H
  update : ∀ n, x (n + 1) = x n + α n • (T (x n) - x n)
  initial_value : x 0 = x0

lemma x0_in_D {D : Set H} {T : H → H} (km : KM D T) : km.x 0 ∈ D := by
  rw [km.initial_value]; exact km.hx0

lemma x_in_D {D : Set H} {T : H → H} (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (km : KM D T)
  (hx0 : km.x 0 ∈ D) (hD : Convex ℝ D) (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop)
  : ∀ n : ℕ, km.x n ∈ D := by
  intro n
  induction n with
  | zero => exact x0_in_D km
  | succ n ih =>
    simp only [Convex, StarConvex] at hD
    have : km.x (n + 1) =  km.α n • (T (km.x n)) + (1 - km.α n) • km.x n := by
      rw [km.update n, add_comm, smul_sub, ← add_sub_right_comm, add_sub_assoc, sub_smul, one_smul]
    rw [this]
    apply hD
    · exact h_Im_T_in_D (km.x n) ih
    · exact ih
    · have a1 : km.α n ≥ 0 := Set.mem_Icc.1 (hα1 n)|>.1
      linarith
    · have a2 : km.α n ≤ 1 := Set.mem_Icc.1 (hα1 n)|>.2
      linarith
    linarith

-- The formalization of Groetsch's theorem for Krasnosel'skii-Mann iteration

/--
The important inequalities (5.16) in the proof process\
`‖x (n + 1) - y‖^2 ≤ ‖x n - y‖^2- λ n * (1 - λ n) * ‖T (x n) - x n‖^2`.
Here km.α n corresponds to λ n in the paper.
-/
lemma key_inequality {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT : NonexpansiveOn T D) (km : KM D T) (hD : Convex ℝ D) (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop) :
    ∀ (y : H) (hy : y ∈ Fix T ∩ D) (n : ℕ), ‖km.x (n + 1) - y‖^2 ≤ ‖km.x n - y‖^2
      - km.α n * (1 - km.α n) * ‖T (km.x n) - km.x n‖^2 := by
    intro y hy n
    rcases hy with ⟨ht, hyfix⟩
    --  obtain 0 ≤ s and s ≤ 1 from km.hα1 n
    rcases hα1 n with ⟨hs_nonneg, hs_le_one⟩
    calc
      ‖km.x (n + 1) - y‖^2
          = ‖(1 - km.α n) • (km.x n - y) + km.α n • (T (km.x n) - y)‖^2 := by
            rw [km.update n]
            simp only [smul_sub, sub_smul, one_smul]
            abel_nf
      _ = (1 - km.α n) * ‖km.x n - y‖^2  + km.α n * ‖T (km.x n) - y‖^2
          - km.α n * (1 - km.α n) * ‖(T (km.x n) - y) - ( km.x n - y)‖^2 := by
            -- apply Corollary_2_15 with arguments arranged to match this expression
            have h := convex_combination_norm_sq_identity (T (km.x n) - y) (km.x n - y) (km.α n)
            -- swap the summands inside the norm so the lemma matches exactly
            have add_comm_eq : (1 - km.α n) • (km.x n - y) + km.α n • (T (km.x n) - y) =
            km.α n • (T (km.x n) - y) + (1 - km.α n) • (km.x n - y) := by simp [add_comm]
            rw [add_comm_eq]
            rw[eq_sub_iff_add_eq , h]
            ring
      _ ≤ (1 - km.α n) * ‖km.x n - y‖^2 + km.α n * ‖km.x n - y‖^2 -km.α n * (1 - km.α n) *‖(T (km.x n) - km.x n )‖^2  := by
          have hT_le : ‖T (km.x n) - y‖ ≤ ‖km.x n - y‖ := by
            nth_rw 1 [← ht]
            exact norm_le_mul_On hT (km.x n) y (x_in_D h_Im_T_in_D km (x0_in_D km) hD hα1 hα2 n) hyfix
          simp only [sub_sub_sub_cancel_right, tsub_le_iff_right, sub_add_cancel,
            add_le_add_iff_left, ge_iff_le]
          apply mul_le_mul_of_nonneg_left _ hs_nonneg
          refine pow_le_pow_left₀ ?_ hT_le 2
          exact norm_nonneg _
      _ = ‖km.x n - y‖^2 - km.α n * (1 - km.α n) * ‖T (km.x n) - km.x n‖^2 := by
          ring

/--
Sequence `x` in KM algorithm is Fejer monotone with respect to Fix T.
-/
lemma Groetsch_theorem_i {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT : NonexpansiveOn T D) (km : KM D T) (hD : Convex ℝ D) (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop) :
    IsFejerMonotone km.x (Fix T ∩ D) := by
    intro y hy n
    rcases hα1 n with ⟨hs_nonneg, hs_le_one⟩
    have calc1 :‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 := by
      calc
      ‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 - km.α n * (1 - km.α n) * ‖T (km.x n) - km.x n‖ ^ 2 := by
        exact key_inequality T h_Im_T_in_D hT km hD hα1 hα2 y hy n
      _≤ ‖km.x n - y‖ ^ 2 := by
        have h_nonneg : 0 ≤ km.α n * (1 - km.α n) * ‖T (km.x n) - y - (km.x n - y)‖ ^ 2 := by
          apply mul_nonneg
          · apply mul_nonneg
            · exact hs_nonneg
            · exact sub_nonneg.mpr hs_le_one   -- 1 - s ≥ 0
          · exact pow_nonneg (norm_nonneg _) 2
        simp at h_nonneg
        linarith
    have this:= (sq_le_sq).mp calc1
    repeat rw[abs_of_nonneg (norm_nonneg _)] at this
    exact this

/--
Sequence `T (x n) - x n` in KM algorithm converges strongly to 0.
-/
lemma Groetsch_theorem_ii {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT_nonexpansive : NonexpansiveOn T D) (km : KM D T) (hD : Convex ℝ D) (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop)
  (fix_T_nonempty : (Fix T ∩ D).Nonempty) :
  (Tendsto (fun n ↦ ‖T (km.x n) - km.x n‖) atTop (𝓝 0)) := by
  rcases fix_T_nonempty with ⟨y0, hy0⟩
  have sum_bound : ∀ N, ∑  i ∈ range (N), km.α i * (1 - km.α i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 - ‖km.x (N) - y0‖ ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hN := key_inequality T h_Im_T_in_D hT_nonexpansive km hD hα1 hα2 y0 hy0 N
      simp [Finset.sum_range_succ]
      linarith
  have partial_le : ∀ N, ∑ i ∈ Finset.range N, km.α i * (1 - km.α i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 := by
      intro N
      refine (sum_bound N).trans ?_
      simp
  let a := fun n => ‖T (km.x n) - km.x n‖ -- define a_n = ‖T x_n - x_n‖
  have a_noninc : ∀ n, a (n + 1) ≤ a n := by
    intro n
    rcases hα1 n with ⟨hs0, hs1⟩
    -- x_{n+1} - x_n = s_n • (T x_n - x_n)
    have hx : km.x (n + 1) - km.x n = km.α n • (T (km.x n) - km.x n) := by
      rw [km.update n]; simp [ smul_sub]
    have eq : T (km.x (n + 1)) - km.x (n + 1) = (T (km.x (n + 1)) - T (km.x n)) + (1 - km.α n) • (T (km.x n) - km.x n) := by
      calc
        T (km.x (n + 1)) - km.x (n + 1) = T (km.x (n + 1)) - T (km.x n) + T (km.x n) - km.x (n + 1) := by simp
        _ = T (km.x (n + 1)) - T (km.x n) + (1 - km.α n) • (T (km.x n) - km.x n) := by
          nth_rw 2 [km.update n]
          simp only [smul_sub, sub_smul, one_smul]
          abel_nf
    calc
      a (n + 1) = ‖T (km.x (n + 1)) - km.x (n + 1)‖ := rfl
      _ = ‖(T (km.x (n + 1)) - T (km.x n)) + (1 - km.α n) • (T (km.x n) - km.x n)‖ := by rw [eq]
      _ ≤ ‖T (km.x (n + 1)) - T (km.x n)‖ + ‖(1 - km.α n) • (T (km.x n) - km.x n)‖ := by apply norm_add_le
      _ ≤ ‖km.x (n + 1) - km.x n‖ + (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by
        apply add_le_add
        · apply norm_le_mul_On hT_nonexpansive (km.x (n + 1)) (km.x n)
          · exact x_in_D h_Im_T_in_D km (x0_in_D km) hD hα1 hα2 (n + 1)
          exact x_in_D h_Im_T_in_D km (x0_in_D km) hD hα1 hα2 n
        have h_nonneg : 0 ≤ 1 - km.α n := by linarith
        -- prove ‖(1 - s) • v‖ ≤ (1 - s) * ‖v‖
        calc
          ‖(1 - km.α n) • (T (km.x n) - km.x n)‖
              = ‖(1 - km.α n)‖ * ‖T (km.x n) - km.x n‖ := by rw [norm_smul]
          _ = |1 - km.α n| * ‖T (km.x n) - km.x n‖ := by rw [Real.norm_eq_abs]
          _ = (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by rw [abs_of_nonneg h_nonneg]
        linarith
      _= ‖km.α n • (T (km.x n) - km.x n)‖ + (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by rw [hx]
      _= km.α n * ‖T (km.x n) - km.x n‖ + (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hs0)]
      _= ‖T (km.x n) - km.x n‖ := by ring
  rw [Converge_iff _ _]
  --Conduct a case-by-case analysis. If x0 = y0,trivial. Otherwise, use the method of contradiction.
  by_cases h_x0_eq_y0:  km.x 0 = y0
  · intro ε εpos
    use 0
    intro n hn
    rcases hy0 with ⟨ht, hyfix⟩
    rw[← h_x0_eq_y0] at hyfix
    have fixed_point: T (km.x n) - km.x n = 0 := by
      induction n with
      | zero => rw[sub_eq_zero];
                simp [Nonexpansive_operator.Fix, IsFixedPt] at ht
                rwa [h_x0_eq_y0]
      | succ i ih => rw [km.update i];simp [ih _]
    rw[fixed_point];simpa
  --x0 ≠ y0. Prove by contradiction: If a does not converge to 0, then there exists ε > 0 such that for any N, there is n ≥ N with a n ≥ ε
  by_contra! hnot
  rcases hnot with ⟨ε, εpos, hε⟩
  have tend := hα2
  -- The partial sum S is greater than 2*‖x0 - y0‖^2 / ε^2 starting from some N0
  have tend_prop := (Filter.tendsto_atTop_atTop.mp tend) (2*‖km.x 0 - y0‖ ^ 2 / ε^2)
  rcases tend_prop with ⟨N0, hN0⟩
  -- pick n0 ≥ N0 and (a n0) ≥ ε
  rcases (hε N0) with ⟨n0, hn0_ge, hn0_ge_eps⟩
  -- For the partial sum up to n0 + 1, use the monotonicity a_i ≥ a_{n0} (for i ≤ n0) to obtain a lower bound
  have lower : ∑ i ∈ Finset.range (n0 + 1), km.α i * (1 - km.α i) * (a i) ^ 2 ≥
      ∑ i ∈ Finset.range (n0 + 1), km.α i * (1 - km.α i)*ε ^ 2 := by
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
    rcases hα1 i with ⟨hs0, hs1⟩
    · apply mul_nonneg
      · exact hs0
      · exact sub_nonneg.mpr hs1
  -- S ≥ 2*‖x0-y0‖^2 / ε^2
  have S_ge : ∑ i ∈ range (n0 + 1), km.α i * (1 - km.α i)
  ≥ 2*‖km.x 0 - y0‖ ^ 2 / ε^2:= by
    apply hN0
    exact le_trans (by linarith : N0 ≤ n0) (le_refl _)
  -- combine the upper and lower bounds to get a contradiction
  have lb: ∑ i ∈ range (n0 + 1), km.α i * (1 - km.α i) * (a i) ^ 2
  ≥ (2* ‖km.x 0 - y0‖ ^ 2 ) := by
    calc
      ∑ i ∈ range (n0 + 1), km.α i * (1 - km.α i) * (a i) ^ 2
          ≥ ∑ i ∈ range (n0 + 1), km.α i * (1 - km.α i) * ε ^ 2 := by
            exact lower
      _ = ε ^ 2 *(∑ i ∈ range (n0 + 1), km.α i * (1 - km.α i))  := by
        have : (∑ i ∈ range (n0 + 1), km.α i * (1 - km.α i) * ε ^ 2) =
            ∑ i ∈ range (n0 + 1), ε ^ 2 * (km.α i * (1 - km.α i) ) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [this]
        -- Move ε^2 to the outside of the summation.
        rw [← @Finset.mul_sum ℕ _ _ (range (n0 + 1))
        (fun i => km.α i * (1 - km.α i)) (ε ^ 2)]
      _ ≥ 2*‖km.x 0 - y0‖ ^ 2 := by
        have hpos : 0 ≤ ε ^ 2 := by exact pow_nonneg (le_of_lt εpos) 2
        calc
          ε ^ 2 * (∑ i ∈ Finset.range (n0 + 1), km.α i * (1 - km.α i))
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
lemma Groetsch_theorem_iii [SeparableSpace H] [CompleteSpace H] {D : Set H}
  (hD_convex : Convex ℝ D) (hD_closed : IsClosed D) (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT : NonexpansiveOn T D) (km : KM D T) (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop)
  (fix_T_nonempty : (Fix T ∩ D).Nonempty) :
  ∃ y0 ∈ (Fix T ∩ D), WeakConverge km.x y0 := by
  have h_fejer := Groetsch_theorem_i T h_Im_T_in_D hT km hD_convex
  have h_x : ∀ n, km.x n ∈ D := by  --The proposition that D is a convex set is only used in the third conclusion.
    intro n                          --That is, conclusions (i) and (ii) do not require that D be a convex closed set.
    induction n with
    | zero =>  rw [km.initial_value];exact km.hx0
    | succ n ih =>
    have eq : km.x (n + 1) = (1 - km.α n) • km.x n + km.α n • (T (km.x n)) := by
      rw [km.update n]
      simp [smul_sub, sub_smul, one_smul]
      abel_nf
    have h1 : T (km.x n) ∈ D := h_Im_T_in_D (km.x n) ih
    rcases hα1 n with ⟨hs_nonneg, hs_le_one⟩
    have combo_in : (1 - km.α n) • km.x n + km.α n • T (km.x n) ∈ D := by
      exact hD_convex (ih) h1 (sub_nonneg.mpr hs_le_one) (hs_nonneg) (sub_add_cancel _ _)
    rw [eq]
    exact combo_in
  --Prove that D is a sequentially weakly closed set --Theorem 3.34
  have h_D_seq_weak_closed : IsWeaklySeqClosed D := closed_is_weakly_seq_closed D hD_convex hD_closed
  have h_weak_cluster_in : ∀ p : H, WeakSubseqLimitPt p km.x → p ∈ (Fix T ∩ D)  := by
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
        exact Groetsch_theorem_ii T h_Im_T_in_D hT km hD_convex hα1 hα2 fix_T_nonempty
      exact Tendsto.comp h2 h1
    have D_nonempty: (D).Nonempty := by
      exact ⟨ km.x0,km.hx0⟩
    have := weakLimit_mem_fixedPoints_of_strongly_tendsto_sub hD_closed hD_convex D_nonempty hT (fun n => km.x (φ n) ) (fun n => h_x (φ n) )
      p p_in_D tend h_error_zero
    exact ⟨this, p_in_D⟩
  apply WeakConv_of_Fejermonotone_of_clusterpt_in (Fix T ∩ D) fix_T_nonempty km.x (h_fejer hα1 hα2) h_weak_cluster_in

/--
Formalization of Groetsch's theorem for Krasnosel'skii-Mann iteration
-/
theorem Groetsch_theorem [SeparableSpace H] [CompleteSpace H] {D : Set H}
  (hD1 : Convex ℝ D) (hD2 : IsClosed D) (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT : NonexpansiveOn T D) (km : KM D T) (fix_T_nonempty : (Fix T ∩ D).Nonempty)
  (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop) :
    -- (i) Fejér monotonicity
    IsFejerMonotone km.x (Fix T ∩ D)
    -- (ii) converges strongly to 0
    ∧ (Tendsto (fun n ↦ ‖T (km.x n) - km.x n‖) atTop (𝓝 0))
    -- (iii) converges weakly to a fixpoint
    ∧ ∃ y0 ∈ (Fix T ∩ D), WeakConverge km.x y0 :=
      ⟨
        Groetsch_theorem_i T h_Im_T_in_D hT km hD1 hα1 hα2,
        Groetsch_theorem_ii  T h_Im_T_in_D hT km hD1 hα1 hα2 fix_T_nonempty,
        Groetsch_theorem_iii hD1 hD2 T h_Im_T_in_D hT km hα1 hα2 fix_T_nonempty
      ⟩

/--
Build a `KM` structure from raw iteration data.
-/
def KM.ofData {D : Set H} {T : H → H}
  (x0 : H) (hx0 : x0 ∈ D) (α : ℕ → ℝ) (x : ℕ → H)
  (hupdate : ∀ n : ℕ, x (n + 1) = x n + α n • (T (x n) - x n))
  (hinit : x 0 = x0) : KM D T where
  x0 := x0
  hx0 := hx0
  α := α
  x := x
  update := hupdate
  initial_value := hinit

/--
`Groetsch_theorem` in a non-structure form: provide raw data `(x0, α, x)` and
the KM recursion, then apply the existing theorem via `KM.ofData`.
-/
theorem Groetsch_theorem_ofData [SeparableSpace H] [CompleteSpace H] {D : Set H}
  (hD1 : Convex ℝ D) (hD2 : IsClosed D) (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT : NonexpansiveOn T D)
  (x0 : H) (hx0 : x0 ∈ D) (α : ℕ → ℝ) (x : ℕ → H)
  (hupdate : ∀ n : ℕ, x (n + 1) = x n + α n • (T (x n) - x n))
  (hinit : x 0 = x0)
  (fix_T_nonempty : (Fix T ∩ D).Nonempty)
  (hα1 : ∀ n : ℕ, α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1), α i * (1 - α i)) atTop atTop) :
    IsFejerMonotone x (Fix T ∩ D)
    ∧ (Tendsto (fun n ↦ ‖T (x n) - x n‖) atTop (𝓝 0))
    ∧ ∃ y0 ∈ (Fix T ∩ D), WeakConverge x y0 := by
  simpa [KM.ofData] using
    (Groetsch_theorem hD1 hD2 T h_Im_T_in_D hT
      (KM.ofData x0 hx0 α x hupdate hinit) fix_T_nonempty hα1 hα2)

/--
Proposition 5.16 (global-space version): convergence of KM iteration for an `α`-averaged operator.
-/
theorem proposition_5_16 [SeparableSpace H] [CompleteSpace H]
  (T : H → H) (α : ℝ) (havg : Averaged T α) (hfix_nonempty : (Fix T).Nonempty)
  (lam : ℕ → ℝ)
  (hlam1 : ∀ n, lam n ∈ Set.Icc (0 : ℝ) (1 / α))
  (hlam2 : Tendsto (fun n => ∑ i ∈ range (n + 1), lam i * (1 - α * lam i)) atTop atTop)
  (x0 : H) (x : ℕ → H)
  (hupdate : ∀ n, x (n + 1) = x n + lam n • (T (x n) - x n))
  (hinit : x 0 = x0) :
    IsFejerMonotone x (Fix T)
    ∧ (Tendsto (fun n ↦ ‖T (x n) - x n‖) atTop (𝓝 0))
    ∧ ∃ y0 ∈ Fix T, WeakConverge x y0 := by
  rcases havg with ⟨hα_range, R, hR_nonexp, hrepr_on⟩
  have hα_pos : 0 < α := hα_range.1
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hrepr : ∀ z : H, T z = (1 - α) • z + α • R z := by
    intro z
    simpa using hrepr_on (x := z) (by simp)
  let μ : ℕ → ℝ := fun n => α * lam n
  have hdiff : ∀ n, T (x n) - x n = α • (R (x n) - x n) := by
    intro n
    rw [hrepr (x n)]
    simp [smul_sub, sub_smul, one_smul]
    abel_nf
  have hupdate_R : ∀ n, x (n + 1) = x n + μ n • (R (x n) - x n) := by
    intro n
    calc
      x (n + 1) = x n + lam n • (T (x n) - x n) := hupdate n
      _ = x n + lam n • (α • (R (x n) - x n)) := by rw [hdiff n]
      _ = x n + (lam n * α) • (R (x n) - x n) := by rw [smul_smul]
      _ = x n + (α * lam n) • (R (x n) - x n) := by
        congr 2
        ring
      _ = x n + μ n • (R (x n) - x n) := rfl
  have hμ1 : ∀ n, μ n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    rcases hlam1 n with ⟨hl0, hl1⟩
    refine ⟨mul_nonneg (le_of_lt hα_pos) hl0, ?_⟩
    have hmul : α * lam n ≤ α * (1 / α) :=
      mul_le_mul_of_nonneg_left hl1 (le_of_lt hα_pos)
    have hmul' : α * lam n ≤ (1 : ℝ) := by
      calc
        α * lam n ≤ α * (1 / α) := hmul
        _ = (1 : ℝ) := by field_simp [hα_ne]
    simpa [μ] using hmul'
  have hsum_mu : ∀ n,
      (∑ i ∈ range (n + 1), μ i * (1 - μ i)) =
        α * (∑ i ∈ range (n + 1), lam i * (1 - α * lam i)) := by
    intro n
    calc
      ∑ i ∈ range (n + 1), μ i * (1 - μ i)
          = ∑ i ∈ range (n + 1), α * (lam i * (1 - α * lam i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [μ]
              ring
      _ = α * (∑ i ∈ range (n + 1), lam i * (1 - α * lam i)) := by
            rw [← Finset.mul_sum]
  have hμ2_scaled :
      Tendsto (fun n => α * (∑ i ∈ range (n + 1), lam i * (1 - α * lam i))) atTop atTop :=
    tendsto_atTop_atTop_const_mul hα_pos hlam2
  have hμ2 : Tendsto (fun n => ∑ i ∈ range (n + 1), μ i * (1 - μ i)) atTop atTop := by
    refine Tendsto.congr' ?_ hμ2_scaled
    exact Filter.Eventually.of_forall (fun n => (hsum_mu n).symm)
  have hFix_eq : Fix T = Fix R := fix_eq_of_averaged_repr T R α hα_ne hrepr
  have hfixR_nonempty : (Fix R ∩ (Set.univ : Set H)).Nonempty := by
    rcases hfix_nonempty with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    constructor
    · simpa [hFix_eq] using hy
    · simp
  have hmain :=
    Groetsch_theorem_ofData (D := (Set.univ : Set H)) (T := R)
      (hD1 := convex_univ) (hD2 := isClosed_univ)
      (h_Im_T_in_D := by intro z hz; simp)
      (hT := hR_nonexp)
      (x0 := x0) (hx0 := by simp)
      (α := μ) (x := x) (hupdate := hupdate_R) (hinit := hinit)
      (fix_T_nonempty := hfixR_nonempty)
      (hα1 := hμ1) (hα2 := hμ2)
  rcases hmain with ⟨hfejerR, hstrongR, hweakR⟩
  have hfejerT : IsFejerMonotone x (Fix T) := by
    simpa [hFix_eq] using hfejerR
  have hnorm_eq : ∀ n, ‖T (x n) - x n‖ = α * ‖R (x n) - x n‖ := by
    intro n
    rw [hdiff n, norm_smul, Real.norm_eq_abs, abs_of_pos hα_pos]
  have hstrong_scaled : Tendsto (fun n ↦ α * ‖R (x n) - x n‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hstrongR)
  have hstrongT : Tendsto (fun n ↦ ‖T (x n) - x n‖) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hstrong_scaled
    exact Filter.Eventually.of_forall (fun n => (hnorm_eq n).symm)
  have hweakT : ∃ y0 ∈ Fix T, WeakConverge x y0 := by
    rcases hweakR with ⟨y0, hy0, hconv⟩
    refine ⟨y0, ?_, hconv⟩
    simpa [hFix_eq] using hy0.1
  exact ⟨hfejerT, hstrongT, hweakT⟩


/--
Corollary 5.17 (global-space version): apply Proposition 5.16 with `α = 1/2`
for firmly nonexpansive operators.
-/
theorem corollary_5_17 [SeparableSpace H] [CompleteSpace H]
  (T : H → H) (hfirm : Firmly_Nonexpansive T) (hfix_nonempty : (Fix T).Nonempty)
  (lam : ℕ → ℝ)
  (hlam1 : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
  (hlam2 : Tendsto (fun n => ∑ i ∈ range (n + 1), lam i * (2 - lam i)) atTop atTop)
  (x0 : H) (x : ℕ → H)
  (hupdate : ∀ n, x (n + 1) = x n + lam n • (T (x n) - x n))
  (hinit : x 0 = x0) :
    IsFejerMonotone x (Fix T)
    ∧ (Tendsto (fun n ↦ ‖T (x n) - x n‖) atTop (𝓝 0))
    ∧ ∃ y0 ∈ Fix T, WeakConverge x y0 := by
  have havg_half : Averaged T (1 / 2 : ℝ) :=
    (firmly_nonexpansive_iff_averaged_half T).1 hfirm
  have hlam1_half : ∀ n, lam n ∈ Set.Icc (0 : ℝ) (1 / (1 / 2 : ℝ)) := by
    intro n
    have htwo : (1 / (1 / 2 : ℝ)) = (2 : ℝ) := by norm_num
    simpa [htwo] using hlam1 n
  have hlam2_half :
      Tendsto (fun n => ∑ i ∈ range (n + 1), lam i * (1 - (1 / 2 : ℝ) * lam i)) atTop atTop := by
    have hscaled :
        Tendsto (fun n => (1 / 2 : ℝ) * (∑ i ∈ range (n + 1), lam i * (2 - lam i))) atTop atTop :=
      tendsto_atTop_atTop_const_mul (by norm_num) hlam2
    refine Tendsto.congr' ?_ hscaled
    refine Filter.Eventually.of_forall ?_
    intro n
    calc
      (1 / 2 : ℝ) * (∑ i ∈ range (n + 1), lam i * (2 - lam i))
          = ∑ i ∈ range (n + 1), (1 / 2 : ℝ) * (lam i * (2 - lam i)) := by
              rw [Finset.mul_sum]
      _ = ∑ i ∈ range (n + 1), lam i * (1 - (1 / 2 : ℝ) * lam i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
  simpa using
    proposition_5_16 T (1 / 2 : ℝ) havg_half hfix_nonempty lam hlam1_half hlam2_half
      x0 x hupdate hinit
