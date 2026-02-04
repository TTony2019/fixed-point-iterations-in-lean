/-
Copyright (c) 2025 Yantao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yantao Li
-/
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.CompleteField
import FormalizationFixpointIterations.Algorithm.Halpern.Lemma

open Nonexpansive_operator Filter Topology TopologicalSpace

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Lemma 30.9 : The boundedness of the
  sequence : `∃ μ > 0`, `‖x (n + 1) - x n‖ ≤ μ ∧ ‖x - T (x n)‖ ≤ μ`
-/
lemma halpern_mu_bound
  {T : H → H} (alg : Halpern T) {y : H}
  (h_diff_bounded : ∃ M1, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M1)
  (h_Tx_bounded : ∃ M2, ∀ n, ‖T (alg.x n) - y‖ ≤ M2)
  (h_seq_bounded : ∃ M3, ∀ n, ‖alg.x n - y‖ ≤ M3) :
  ∃ μ : ℝ, μ > 0 ∧ (∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ) ∧ (∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ) := by
  obtain ⟨M1, hM1⟩ := h_diff_bounded
  obtain ⟨M2, hM2⟩ := h_Tx_bounded
  obtain ⟨M3, hM3⟩ := h_seq_bounded
  let μ := M1 + M2 + M3 + ‖alg.u - y‖ + 1; refine ⟨μ, ?hpos, ?hstep, ?huTx⟩
  · simp [μ]; have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _
    linarith [(le_trans (norm_nonneg _) (hM1 0)), (le_trans (norm_nonneg _) (hM2 0)),
      (le_trans (norm_nonneg _) (hM3 0))]
  · intro n; calc
      _ = ‖(alg.x (n + 1) - T (alg.x n)) + (T (alg.x n) - alg.x n)‖ := by abel_nf
      _ ≤ ‖alg.x (n + 1) - T (alg.x n)‖ + ‖T (alg.x n) - alg.x n‖ := by
        apply norm_add_le
      _ ≤ M1 + ‖T (alg.x n) - alg.x n‖ := by gcongr; exact hM1 n
      _ = M1 + ‖(T (alg.x n) - y) + (y - alg.x n)‖ := by abel_nf
      _ ≤ M1 + (‖T (alg.x n) - y‖ + ‖y - alg.x n‖) := by
        apply add_le_add_right; apply norm_add_le
      _ ≤ M1 + (M2 + M3) := by
        gcongr
        · exact hM2 n
        · rw [norm_sub_rev]; exact hM3 n
      _ ≤ μ := by
        simp only [μ]; rw [← add_assoc]
        have h_diff_nonneg : 0 ≤ ‖alg.u - y‖ := norm_nonneg _; linarith
  · intro n; calc
      _ = ‖(alg.u - y) + (y - T (alg.x n))‖ := by abel_nf
      _ ≤ ‖alg.u - y‖ + ‖y - T (alg.x n)‖ := by  apply norm_add_le
      _ ≤ ‖alg.u - y‖ + M2 := by gcongr; rw [norm_sub_rev]; exact hM2 n
      _ ≤ μ := by
        simp [μ]
        linarith [μ, (le_trans (norm_nonneg _) (hM1 0)), (le_trans (norm_nonneg _) (hM3 0))]

omit [InnerProductSpace ℝ H] in
/--
Lemma 30.12.1 :The upbd of the norm of the difference : `‖x (n + 2) - x (n + 1)‖ ≤
  μ * Σ_m^n |λ (k + 1) - λ k| + ‖x (m + 1) - x m‖ * ∏_m^n (1 - λ (k + 1))`
-/
lemma halpern_telescoping_bound
  {x : ℕ → H} {α : ℕ → ℝ} {μ : ℝ} (hμ_nonneg : 0 ≤ μ) (hα_range : ∀ n, α n ∈ Set.Ioo 0 1)
  (h_norm_diff_ineq : ∀ n, ‖x (n + 2) - x (n + 1)‖ ≤ μ *
    |α (n + 1) - α n| + (1 - α (n + 1)) * ‖x (n + 1) - x n‖)
  : ∀ n m, m ≤ n → ‖x (n + 2) - x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n,
    |α (k + 1) - α k|) + ‖x (m + 1) - x m‖ * (∏ k ∈ Finset.Icc m n, (1 - α (k + 1))) := by
  intro n m hmn; obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  induction k with
  | zero => simp; linarith [h_norm_diff_ineq m]
  | succ k ih => calc
      ‖x (m + (k + 1) + 2) - x (m + (k + 1) + 1)‖ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))|
        + (1 - α (m + (k + 1) + 1)) * ‖x (m + (k + 1) + 1) - x (m + (k + 1))‖ :=
          h_norm_diff_ineq (m + (k + 1))
      _ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))| + (1 - α (m + (k + 1) + 1)) *
        (μ * (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|) + ‖x (m + 1) - x m‖ *
          (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1)))) := by
            gcongr
            · linarith [one_sub_pos_of_mem_Ioo (hα_range (m + (k + 1) + 1))]
            · exact ih (by linarith)
      _ = μ * |α (m + (k + 1) + 1) - α (m + (k + 1))| + (1 - α (m + (k + 1) + 1)) * μ *
        (∑ l ∈ Finset.Icc m (m + k), |α (l + 1) - α l|) + (1 - α (m + (k + 1) + 1)) *
          ‖x (m + 1) - x m‖ * (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1))) := by ring
      _ ≤ μ * |α (m + (k + 1) + 1) - α (m + (k + 1))| + μ * (∑ l ∈ Finset.Icc m (m + k),
        |α (l + 1) - α l|) + (1 - α (m + (k + 1) + 1)) * ‖x (m + 1) - x m‖ *
          (∏ l ∈ Finset.Icc m (m + k), (1 - α (l + 1))) := by
            gcongr; nth_rewrite 2 [← one_mul μ]
            apply mul_le_mul (by linarith [(hα_range (m + (k + 1) + 1)).1])
              (by simp only [le_refl]) hμ_nonneg (by linarith)
      _ = μ * (∑ l ∈ Finset.Icc m (m + (k + 1)), |α (l + 1) - α l|) + ‖x (m + 1) - x m‖
        * (∏ l ∈ Finset.Icc m (m + (k + 1)), (1 - α (l + 1))) := by
          rw [← add_assoc, ← Nat.succ_eq_add_one (m+k), Finset.sum_Icc_succ_top,
            Finset.prod_Icc_succ_top, Nat.succ_eq_add_one]
          · ring_nf
          repeat linarith

/--
Lemma 30.10: Equation of the difference : `x (n + 2) - x (n + 1) = λ (n + 1) - λ n) •
  (x - T (x n)) + (1 - λ (n + 1)) • (T (x (n + 1)) - T (x n))`
-/
lemma halpern_diff_formula
  {T : H → H} (alg : Halpern T)
  : ∀ n, alg.x (n + 2) - alg.x (n + 1) = (alg.α (n + 1) - alg.α n) •
    (alg.u - T (alg.x n)) + (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n)) := by
  intro n; simp only [alg.update]; calc
    _ = (alg.α (n + 1) • alg.u - alg.α n • alg.u) + ((1 - alg.α (n + 1)) •
      T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n)) - (1 - alg.α n) • T (alg.x n)) := by abel
    _ = (alg.α (n + 1) - alg.α n) • alg.u + ((1 - alg.α (n + 1)) • T (alg.α n • alg.u +
      (1 - alg.α n) • T (alg.x n)) - (1 - alg.α n) • T (alg.x n)) := by simp [sub_smul]
    _ = (alg.α (n + 1) - alg.α n) • alg.u - (alg.α (n + 1) - alg.α n) • T (alg.x n) +
      (1 - alg.α (n + 1)) • (T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n)) - T (alg.x n)) := by
        simp [sub_smul, add_sub, add_comm, smul_sub]; abel_nf
    _ = (alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n)) + (1 - alg.α (n + 1)) •
      (T (alg.α n • alg.u + (1 - alg.α n) • T (alg.x n)) - T (alg.x n)) := by simp [smul_sub]

/--
Lemma 30.11 : Boundedness of the norm of the difference : `‖x (n + 2) - x (n + 1)‖ ≤
  μ * |λ (n + 1) - λ n| + (1 - λ (n + 1)) * ‖x (n + 1) - x n‖`
-/
lemma halpern_norm_diff_ineq
  {T : H → H} (alg : Halpern T) {D : Set H} (hT_nonexp : NonexpansiveOn T D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_diff_formula : ∀ n, alg.x (n + 2) - alg.x (n + 1) = (alg.α (n + 1) - alg.α n) •
    (alg.u - T (alg.x n)) + (1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n)))
  (μ : ℝ) (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| + (1 - alg.α (n + 1)) *
    ‖alg.x (n + 1) - alg.x n‖ := by
  intro n; rw [h_diff_formula n]; calc
    _ ≤ ‖(alg.α (n + 1) - alg.α n) • (alg.u - T (alg.x n))‖
      + ‖(1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (alg.x n))‖ := by apply norm_add_le
    _ = |alg.α (n + 1) - alg.α n| * ‖alg.u - T (alg.x n)‖
      + |1 - alg.α (n + 1)| * ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by simp [norm_smul]
    _ = |alg.α (n + 1) - alg.α n| * ‖alg.u - T (alg.x n)‖
      + (1 - alg.α (n + 1)) * ‖T (alg.x (n + 1)) - T (alg.x n)‖ := by
          rw [abs_of_pos (one_sub_pos_of_mem_Ioo (h_α_range (n + 1)))]
    _ ≤ |alg.α (n + 1) - alg.α n| * μ + (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
      gcongr
      · exact hμ_Tx_bound n
      · linarith [(h_α_range (n + 1)).2]
      have hT_nonexp' := hT_nonexp (halg_x_in_D (n + 1)) (halg_x_in_D n)
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm] at hT_nonexp'
      have h_nonneg : 0 ≤ ‖alg.x (n + 1) - alg.x n‖ := norm_nonneg _
      simp only [ofReal_norm, ENNReal.coe_one, one_mul] at hT_nonexp'
      apply (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp; simp only [ofReal_norm]; exact hT_nonexp'
    _ = μ * |alg.α (n + 1) - alg.α n| + (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖ := by
      rw [mul_comm]

/--
Lemma 30.12.2: Boundedness of the norm of the difference : `‖x (n + 2) - x (n + 1)‖
  ≤ μ * Σ_m^n |λ (k + 1) - λ k| + μ * ∏_m^n (1 - λ (k + 1))`
-/
lemma halpern_telescoping_ineq
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (μ : ℝ) (hμ_pos : μ > 0) (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  : ∀ n m, m ≤ n → ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k|) + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
    intro n m hmn; have hμ_nonneg : 0 ≤ μ := le_of_lt hμ_pos; calc
      _ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) + ‖alg.x (m + 1) - alg.x m‖ *
        (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
          apply halpern_telescoping_bound hμ_nonneg h_α_range h_norm_diff_ineq; exact hmn
      _ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|) + μ *
        (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
        apply add_le_add_right; apply mul_le_mul_of_nonneg_right
        · exact hμ_x_bound m
        · apply Finset.prod_nonneg; intro k hk
          linarith [one_sub_pos_of_mem_Ioo (h_α_range (k + 1))]

/--
Lemma : The limit of the inequality in Lemma 30.12.2 : `lim m n → ∞, m ≤ n, ‖x (n + 2) - x (n + 1)‖
  ≤ μ * Σ_m^n |λ (k + 1) - λ k| + μ * ∏_m^n (1 - λ (k + 1))`
-/
lemma halpern_telescoping_limit
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (μ : ℝ)
  (hμ_pos : μ > 0) (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  : ∀ᶠ n in atTop, ∀ᶠ m in atTop, m ≤ n →
    ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n, |alg.α (k + 1) - alg.α k|)
      + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))) := by
  have hμ_nonneg := le_of_lt hμ_pos
  apply eventually_atTop.2; use 0; intro n hn; apply eventually_atTop.2; use 0; intro m hm hmn
  exact halpern_telescoping_ineq alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq n m hmn

omit [InnerProductSpace ℝ H] in
/--
Lemma : Index transform :
  `lim n → ∞`, `(f (n + 2) - f (n + 1)) = 0` → `lim n → ∞`, `f (n + 1) - f n = 0`
-/
lemma adjacent_diff_from_shifted
  {f : ℕ → H} : Tendsto (fun n => (f (n + 2) - f (n + 1))) atTop (nhds 0) →
  Tendsto (fun n => (f (n + 1) - f n)) atTop (nhds 0) := by
  intro h
  have : (fun n ↦ f (n + 1) - f n) ∘ (fun n ↦ n + 1) = (fun n ↦ f (n + 2) - f (n + 1)) := by
    funext n; simp only [Function.comp_apply]
  rw [← this] at h; exact (tendsto_add_atTop_iff_nat 1).mp h

/--
Lemma : The limit of the difference : `lim n → ∞`, `x (n + 1) - x n = 0`
-/
lemma halpern_diff_limit
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (μ : ℝ)
  (hμ_pos : μ > 0) (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (hμ_x_bound : ∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ)
  (h_norm_diff_ineq : ∀ n, ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * |alg.α (n + 1) - alg.α n| +
    (1 - alg.α (n + 1)) * ‖alg.x (n + 1) - alg.x n‖)
  (h_telescoping : ∀ n m, m ≤ n → ‖alg.x (n + 2) - alg.x (n + 1)‖ ≤ μ * (∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k|) + μ * (∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1))))
  : Tendsto (fun n => (alg.x (n + 1) - alg.x n)) atTop (nhds 0) := by
  have sq_lim_le := halpern_telescoping_limit alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq
  have sq_lim2 := halpern_prod_tail_tendsto_zero alg μ hμ_pos h_α_range h_α_sum_inf
  have sq_lim3: ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * ∏ k ∈ Finset.Icc m n,
    (1 - alg.α (k + 1)) < ε := by
    intro ε ε_pos; exact Eventually.mono sq_lim_le fun x a ↦ sq_lim2 ε ε_pos x
  have sq_lim1 := halpern_sum_tail_tendsto_zero alg μ hμ_pos h_α_diff_finite
  have sq_lim4 : ∀ ε > 0, ∀ᶠ (m : ℕ) (n : ℕ) in atTop, m ≤ n → μ * ∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k| + μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
    intros ε ε_pos
    have h1 := sq_lim1 (ε/2) (by linarith); have h2 := sq_lim3 (ε/2) (by linarith)
    filter_upwards [h1, h2] with N1 h11 h22; filter_upwards [h11, h22] with N2 h111 h222
    intro hN1N2; calc
      _ < ε/2 + ε/2 := add_lt_add (h111 hN1N2) (h222 hN1N2)
      _ = ε := by ring
  have sq_lim5 : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n →
    ‖alg.x (n + 2) - alg.x (n + 1)‖ < ε := by
    intro ε ε_pos
    filter_upwards [sq_lim4 ε ε_pos] with N1 h1; filter_upwards [h1] with N2 h2; intro hN1N2; calc
      _ ≤ μ * ∑ k ∈ Finset.Icc N1 N2, |alg.α (k + 1) - alg.α k| +
        μ * ∏ k ∈ Finset.Icc N1 N2, (1 - alg.α (k + 1)) := by apply h_telescoping N2 N1 hN1N2
      _ < ε := h2 hN1N2
  have sq_lim5' : ∀ ε > 0, ∀ᶠ n in atTop, ‖alg.x (n + 2) - alg.x (n + 1)‖ < ε := by
    intro ε ε_pos; have h_eventually := sq_lim5 ε ε_pos; rw [eventually_atTop] at h_eventually
    obtain ⟨N, hN⟩ := h_eventually; specialize hN N (le_refl N); rw [eventually_atTop] at hN ⊢
    rcases hN with ⟨a, ha⟩; use max N a; intro n hn
    apply (ha n (le_of_max_le_right hn) (le_of_max_le_left hn))
  have sq_lim6 : Tendsto (fun n => ‖alg.x (n + 2) - alg.x (n + 1)‖) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]; intros ε ε_pos
    obtain ⟨N, hN⟩ := (eventually_atTop).mp (sq_lim5' ε ε_pos); use N; intro n hn
    rw [Real.dist_eq]; simp only [sub_zero, abs_norm]; exact hN n hn
  have sq_lim7 : Tendsto (fun n => (alg.x (n + 2) - alg.x (n + 1))) atTop (nhds 0) :=
    ((Iff.symm tendsto_zero_iff_norm_tendsto_zero).1 sq_lim6)
  exact adjacent_diff_from_shifted sq_lim7

/--
Lemma 30.14 : The limit of `x n - T (x n)` : `lim n → ∞`, `x n - T (x n) = 0`
-/
lemma halpern_x_sub_Tx_tendsto_zero
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (nhds 0)) (μ : ℝ) (hμ_pos : μ > 0)
  (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  (h_diff_limit : Tendsto (fun n ↦ alg.x (n + 1) - alg.x n) atTop (nhds 0))
  : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (nhds 0) := by
  have eq1 : ∀ n, alg.x (n + 1) - alg.x n = alg.α n • (alg.u - T (alg.x n)) +
    (T (alg.x n) - alg.x n) := by intro n; rw [alg.update]; simp [smul_sub, sub_smul]; abel
  have h1 : Tendsto (fun n ↦ alg.α n * ‖alg.u - T (alg.x n)‖) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at ⊢ h_α_limit; intro ε ε_pos
    obtain ⟨N, hN⟩ := h_α_limit (ε / μ) (by positivity); use N; intro n hn; rw [Real.dist_eq]
    simp only [sub_zero]
    have h_α_small : |alg.α n| < ε / μ := by
      have := hN n hn; rw [Real.dist_eq] at this; simp only [sub_zero] at this; exact this
    have h_α_nonneg : 0 ≤ alg.α n := by linarith [(h_α_range n).1]
    rw [abs_of_nonneg h_α_nonneg] at h_α_small; calc
      _ = alg.α n * ‖alg.u - T (alg.x n)‖ := by simp [abs_mul, abs_of_nonneg h_α_nonneg]
      _ ≤ alg.α n * μ := by gcongr; exact hμ_Tx_bound n
      _ < (ε / μ) * μ := mul_lt_mul_of_pos_right h_α_small hμ_pos
      _ = ε := by field_simp [ne_of_gt hμ_pos]
  have h2 : Tendsto (fun n ↦ alg.α n • (alg.u - T (alg.x n))) atTop (nhds 0) := by
    have h_norm_bound : Tendsto (fun n ↦ ‖alg.α n • (alg.u - T (alg.x n))‖) atTop (nhds 0) := by
      have : Tendsto (fun n ↦ |alg.α n| * ‖alg.u - T (alg.x n)‖) atTop (nhds 0) := by
        convert h1 using 1; ext n; congr; simp; linarith [(h_α_range n).1]
      convert this using 1; funext n; rw [norm_smul]; simp
    rw [Metric.tendsto_atTop] at h_norm_bound ⊢
    intros ε ε_pos; obtain ⟨N, hN⟩ := h_norm_bound ε ε_pos; use N; intros n hn
    specialize hN n hn; rw [dist_eq_norm]; simp only [dist_zero_right, norm_norm] at hN ⊢
    simp only [sub_zero]; exact hN
  have h_key : ∀ n, alg.x n - T (alg.x n) = alg.α n • (alg.u - T (alg.x n)) - (alg.x (n + 1)
    - alg.x n) := by intro n; simp [eq1 n]
  convert Tendsto.sub h2 h_diff_limit using 1
  · funext n; exact h_key n
  · simp

/--
Lemma 30.17 : Upbd of the inner product and the norm : `∀ ε > 0, ∃ k, ∀ n ≥ k,
  ⟪T (x n) - PCx, x - PCx⟫ ≤ ε ∧ λ n * ‖x - PCx‖ ^ 2 ≤ ε`
-/
lemma halpern_eps_exists_of_limsup_and_alpha
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {T : H → H}
  (alg : Halpern T) (m : H) (h_α_limit : Tendsto alg.α atTop (nhds 0))
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ ε ∧
    alg.α n * ‖alg.u - m‖ ^ 2 ≤ ε := by
  intro ε hε; by_cases h_um_zero : ‖alg.u - m‖ = 0
  · have h_u_eq_m : alg.u = m := eq_of_norm_sub_eq_zero h_um_zero
    rw [h_u_eq_m]; simp only [ge_iff_le, sub_self, inner_zero_right, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, and_self]
    use 0; intro n hn; linarith
  · have h_um_pos : 0 < ‖alg.u - m‖ := norm_pos_iff.mpr (fun h => h_um_zero (by
      have : alg.u - m = 0 := h
      simp [this]))
    have h_um_sq_pos : 0 < ‖alg.u - m‖ ^ 2 := by positivity
    rw [Metric.tendsto_atTop] at h_α_limit
    obtain ⟨k₁, hk₁⟩ := h_α_limit (ε / ‖alg.u - m‖ ^ 2) (by positivity)
    have h_limsup_half : ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ ε / 2 := by
      have h_eventually : ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ < ε / 2 := by
        have : (0 : ℝ) < ε / 2 := by linarith
        have h_gap : limsup (fun k => ⟪T (alg.x k) - m, alg.u - m⟫) atTop < ε / 2 := by
          linarith [h_limsup_neg]
        apply Filter.eventually_lt_of_limsup_lt h_gap h_inner_bounded
      filter_upwards [h_eventually] with n hn; exact le_of_lt hn
    rw [eventually_atTop] at h_limsup_half; obtain ⟨k₂, hk₂⟩ := h_limsup_half; use max k₁ k₂
    intro n hn; have hn_k₁ := le_of_max_le_left hn; have hn_k₂ := le_of_max_le_right hn
    constructor
    · exact le_trans (hk₂ n hn_k₂) (by linarith)
    · have h_α_small : ‖alg.α n - 0‖ < ε / ‖alg.u - m‖^2 := hk₁ n hn_k₁; rw [sub_zero] at h_α_small
      have h_alpha_abs : |alg.α n| = alg.α n := abs_of_nonneg (le_of_lt (h_α_range n).1)
      rw [← h_alpha_abs] at h_α_small
      · calc
          _ ≤ (ε / ‖alg.u - m‖^2) * ‖alg.u - m‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right ?_ h_um_sq_pos.le
            · simp [h_alpha_abs] at h_α_small; linarith
          _ = ε := by field_simp [ne_of_gt h_um_sq_pos]

/--
Lemma 30.18 : The distance is upbounded by `ε` : `∀ ε > 0, ∃ k, ∀ n ≥ k,
  ‖x (n + 1) - PCx‖ ^ 2 ≤ λ n * ε + (1 - λ n) * ‖x n - PCx‖ ^ 2 + 2 * λ n * ε`
-/
lemma halpern_xn_sub_PCx_upbd [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (nhds 0)) (m : H) (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, ‖alg.x (n+1) - m‖ ^ 2 ≤ alg.α n * ε + (1 - alg.α n) *
    ‖alg.x n - m‖ ^ 2 + 2 * alg.α n * ε := by
  intro ε hε
  have h_inner_bound := halpern_eps_exists_of_limsup_and_alpha alg m h_α_limit h_α_range
    h_limsup_neg h_inner_bounded
  specialize h_inner_bound ε hε; rcases h_inner_bound with ⟨k, h_control⟩; use k; intro n hn
  have h_αn0 : 0 < alg.α n := (h_α_range n).1; have h_αn1 : alg.α n < 1 := (h_α_range n).2
  specialize h_control n hn; rcases h_control with ⟨h_inner_control, h_mul_control⟩; calc
    _ = ‖alg.α n • (alg.u - m) + (1 - alg.α n) • (T (alg.x n) - m)‖ ^ 2 := by
      rw [alg.update]; congr; simp [smul_sub, sub_smul, ← add_sub_assoc, add_comm]
    _ = ‖alg.α n • (alg.u - m)‖ ^ 2 + ‖(1 - alg.α n) • (T (alg.x n) - m)‖ ^ 2 + 2 *
      ⟪alg.α n • (alg.u - m), (1 - alg.α n) • (T (alg.x n) - m)⟫ := by
        rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]; ring_nf
        simp only [inner_self_eq_norm_sq_to_K, Real.ringHom_apply, real_inner_comm, add_left_inj]
        ring
      _ ≤ alg.α n * ε + (1 - alg.α n) * ‖alg.x n - m‖ ^ 2 + 2 * alg.α n * ε := by
        apply add_le_add
        · apply add_le_add
          · rw [norm_smul]; calc
              _ = (alg.α n)^2 * ‖alg.u - m‖^2 := by
                simp only [Real.norm_eq_abs]; rw [mul_pow, sq_abs]
              _ = alg.α n * (alg.α n * ‖alg.u - m‖^2) := by ring
              _ ≤ alg.α n * ε :=  mul_le_mul (by linarith) h_mul_control (mul_nonneg (by linarith)
                  (sq_nonneg ‖alg.u - m‖)) (by linarith)
          · rw [norm_smul]; calc
              _ = (1 - alg.α n) ^ 2 * ‖T (alg.x n) - m‖^2 := by
                simp only [Real.norm_eq_abs]; rw [mul_pow, sq_abs]
              _ ≤ (1 - alg.α n)^2 * ‖alg.x n - m‖^2 := by
                apply mul_le_mul (by simp) ?_ (by apply sq_nonneg) (sq_nonneg (1 - alg.α n))
                gcongr; apply (h_induction m hm_in_C n).1
              _ = (1 - alg.α n) * ((1 - alg.α n) * ‖alg.x n - m‖^2) := by ring
              _ ≤ (1 - alg.α n) * ‖alg.x n - m‖^2 := by
                apply mul_le_mul (by simp)
                · nth_rewrite 2 [← one_mul (‖alg.x n - m‖ ^ 2)]
                  apply mul_le_mul (by linarith) (by simp) (sq_nonneg ‖alg.x n - m‖) (by simp)
                · apply mul_nonneg (by linarith) (sq_nonneg ‖alg.x n - m‖)
                · apply le_of_lt; linarith
        · calc
            _ = 2 * alg.α n * (1 - alg.α n) * ⟪alg.u - m, T (alg.x n) - m⟫ := by
              simp [real_inner_smul_left, real_inner_smul_right]; ring
            _ ≤ 2 * alg.α n * (1 - alg.α n) * ε := by
              gcongr
              · apply mul_nonneg (by linarith) (by linarith)
              · rw [real_inner_comm]; exact h_inner_control
            _ ≤ 2 * alg.α n * ε := by calc
                _ ≤ 2 * alg.α n * 1 * ε := by
                  apply mul_le_mul_of_nonneg_right ?_ (le_of_lt hε)
                  apply mul_le_mul_of_nonneg_left (by linarith)
                  apply mul_nonneg (by norm_num) ((h_α_range n).1.le)
                _ = 2 * alg.α n * ε := by ring

/--
Lemma 30.19 : The distance is upbounded by `ε` : `∀ ε > 0, ∃ N, ∀ n k ≥ N, n ≥ k →
  ‖x (n + 1) - PCx‖ ^ 2 ≤ 3 * ε + ‖x k - PCx‖ ^ 2 * ∏_k^n (1 - λ l)`
-/
lemma halpern_xn_sub_PCx_prod [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (nhds 0)) (m : H) (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M)
  : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n k : ℕ, n ≥ N → k ≥ N → n ≥ k → ‖alg.x (n + 1) - m‖ ^ 2
    ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 * (∏ l ∈ Finset.Icc k n, (1 - alg.α l)) := by
  have h_dist_bound := halpern_xn_sub_PCx_upbd alg h_α_range h_α_limit m
    hm_in_C h_induction h_limsup_neg h_inner_bounded
  intro ε hε; obtain ⟨N, hN⟩ := h_dist_bound ε hε; use N; intro n k hn hk hnk
  obtain ⟨len, rfl⟩ := exists_add_of_le hnk; induction len with
  | zero =>
    simp only [add_zero, Finset.Icc_self, Finset.prod_singleton]
    have h_step_case := hN k (by linarith); calc
      _ ≤ alg.α k * ε + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 + 2 * alg.α k * ε := h_step_case
      _ = 3 * alg.α k * ε + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 := by ring
      _ ≤ 3 * ε * alg.α k + (1 - alg.α k) * ‖alg.x k - m‖ ^ 2 := by linarith
      _ ≤ 3 * ε + ‖alg.x k - m‖ ^ 2 * (1 - alg.α k) := by
        have h1_minus_α : 0 ≤ 1 - alg.α k := by linarith [one_sub_pos_of_mem_Ioo (h_α_range k)]
        have hε_pos : 0 ≤ ε := le_of_lt hε; nlinarith [sq_nonneg (‖alg.x k - m‖)]
  | succ len' ih =>
    have hnk' : N ≤ k + len' := by linarith
    have h_ih := ih hnk'; calc
      _ = ‖alg.x (k + len' + 1 + 1) - m‖ ^ 2 := by ring_nf
      _ ≤ alg.α (k + len' + 1) * ε + (1 - alg.α (k + len' + 1)) * ‖alg.x (k + len' + 1) - m‖ ^ 2 +
        2 * alg.α (k + len' + 1) * ε := by apply hN (k + len' + 1); linarith
      _ ≤ alg.α (k + len' + 1) * ε + (1 - alg.α (k + len' + 1)) * (3 * ε + ‖alg.x k - m‖ ^ 2 *
          ∏ l ∈ Finset.Icc k (k + len'), (1 - alg.α l)) + 2 * alg.α (k + len' + 1) * ε := by
            have : k + len' ≥ k := by linarith
            simp only [add_le_add_iff_right, add_le_add_iff_left, ge_iff_le]
            apply mul_le_mul (by simp) (h_ih this) (sq_nonneg ‖alg.x (k + len' + 1) - m‖)
            linarith [one_sub_pos_of_mem_Ioo (h_α_range (k + len' + 1))]
      _ = 3 * ε + ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k (k + (len' + 1)), (1 - alg.α l) := by
        have :- (alg.α (1 + k + len') * ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (k + len'),
          (1 - alg.α x)) + ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (k + len'), (1 - alg.α x) =
            ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc k (1 + k + len'), (1 - alg.α x) := by
              simp only [add_comm]; simp only [← add_assoc]; simp only [← Nat.succ_eq_add_one]
              rw [Finset.prod_Icc_succ_top]
              · ring_nf; simp only [Nat.succ_eq_add_one, sub_right_inj, mul_eq_mul_left_iff,
                mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
                norm_eq_zero]; left; congr 1; ring_nf
              · linarith
        rw [mul_add]; ring_nf
        rw [add_comm (-(alg.α (1 + k + len') * ‖alg.x k - m‖ ^ 2 * ∏ x ∈ Finset.Icc
          k (k + len'), (1 - alg.α x))) (ε * 3), add_assoc, add_eq_add_iff_eq_and_eq]
        · simp only [true_and]; exact this
        · simp
        · linarith

/--
Lemma : The distance is upbounded by `ε` : `∀ ε > 0, ∃ N, ∀ n k ≥ N, n ≥ k →
  limsup n → ∞, ‖x (n + 1) - PCx‖ ^ 2 ≤ 3 * ε`
-/
lemma halpern_limsup_bound_from_prod [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (nhds 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M) (y : H)
  (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M)
  : ∀ ε > 0, ∃ N : ℕ, ∀ (n k : ℕ), n ≥ k → n ≥ N → k ≥ N →
      limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≤ 3 * ε := by
  have h_α_le_one : ∀ n, 1 - alg.α n ≤ 1 := by
    intro n; linarith [one_sub_lt_one_of_mem_Ioo (h_α_range n)]
  have h_nonneg_one_sub_α : ∀ n, 0 ≤ 1 - alg.α n := by
    intro n; linarith [one_sub_pos_of_mem_Ioo (h_α_range n)]
  intro ε hε
  obtain ⟨N, hN⟩ := halpern_xn_sub_PCx_prod alg h_α_range h_α_limit m hm_in_C h_induction
    h_limsup_neg h_inner_bounded ε hε
  have h_pointwise : ∀ n ≥ N, ∀ k ≥ N, n ≥ k → ‖alg.x (n + 1) - m‖ ^ 2 ≤ 3 * ε +
    ‖alg.x k - m‖ ^ 2 * (∏ l ∈ Finset.Icc k n, (1 - alg.α l)) := by
    intros n hn k hk hnk; exact hN n k hn hk hnk
  have h_prod_zero : ∀ k ≥ N, limsup (fun n => (∏ l ∈ Finset.Icc k n, (1 - alg.α l)))
    atTop = 0 := by
    intro k hk; have h_prod_tendsto := infinite_prod_zero alg h_α_range h_α_sum_inf k
    exact Tendsto.limsup_eq h_prod_tendsto
  use N; intro n k hnk hnN hkN
  have ⟨M, hM⟩ : ∃ M : ℝ, ∀ n : ℕ, ‖alg.x n - m‖ ^ 2 ≤ M := by
    obtain ⟨K, hK⟩ := h_seq_bounded
    have h_K_nonneg : 0 ≤ K := by
      have hK_nonneg : ∀ n, 0 ≤ ‖alg.x n - y‖ := by
        intro n; exact norm_nonneg _
      exact Std.le_trans (hK_nonneg N) (hK N)
    use (‖y - m‖ + K) ^ 2; intro n; calc
      _ = ‖(alg.x n - y) + (y - m)‖ ^ 2 := by congr; abel
      _ = ‖alg.x n - y‖ ^ 2 + ‖y - m‖ ^ 2 + 2 * ⟪alg.x n - y, y - m⟫ := by
        rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]; simp [real_inner_comm]; ring
      _ ≤ K ^ 2 + ‖y - m‖ ^ 2 + 2 * ‖alg.x n - y‖ * ‖y - m‖ := by
        apply add_le_add
        · apply add_le_add ?_ (by simp)
          · apply sq_le_sq.2; simp only [abs_norm]; convert hK n; simp only [abs_eq_self]; linarith
        rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (real_inner_le_norm (alg.x n - y) (y - m))
        norm_num
      _ ≤ (‖y - m‖ + K) ^ 2 := by
        rw [pow_two (‖y - m‖ + K), mul_add, add_mul, add_mul]; ring_nf
        simp only [add_comm, add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_iff_left₀]
        rw [mul_comm]
        apply mul_le_mul (hK n) (by simp only [le_refl]) (norm_nonneg (y - m)) (by assumption)
  calc
    _ ≤ limsup (fun n => 3 * ε + ‖alg.x k - m‖ ^ 2 * (∏ l ∈ Finset.Icc k n, (1 - alg.α l)))
      atTop := by
        apply limsup_le_limsup
        · apply eventually_atTop.2; use k; intro p hp; apply h_pointwise
          · linarith
          · assumption
          · assumption
        · simp only [autoParam, IsCoboundedUnder, IsCobounded, eventually_map, eventually_atTop,
          ge_iff_le, forall_exists_index]; use 0; intro a p q
          specialize q (p + 1) (by linarith)
          have h_norm_sq_nonneg : 0 ≤ ‖alg.x (p + 1 + 1) - m‖ ^ 2 := by apply sq_nonneg
          linarith
        · simp only [autoParam, IsBoundedUnder, IsBounded, eventually_map, eventually_atTop,
          ge_iff_le]; use (3 * ε + M), 0; intro b
          simp only [zero_le, add_le_add_iff_left, forall_const]; calc
            _ ≤ M * ∏ l ∈ Finset.Icc k b, (1 - alg.α l) := by
              apply mul_le_mul (hM k) (by simp only [le_refl]) ?_ ?_
              · apply Finset.prod_nonneg; intro i hi; exact h_nonneg_one_sub_α i
              · have h_norm_sq_nonneg : 0 ≤ ‖alg.x b - m‖ ^ 2 := by apply sq_nonneg
                linarith [hM b]
            _ ≤ M := by
              nth_rewrite 2 [← mul_one M]; apply mul_le_mul_of_nonneg_left
              · exact Finset.prod_le_one (fun i a ↦ h_nonneg_one_sub_α i) fun i a ↦ h_α_le_one i
              · have h_norm_sq_nonneg : 0 ≤ ‖alg.x b - m‖ ^ 2 := by apply sq_nonneg
                linarith [hM b]
    _ = limsup (fun n ↦ ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k n, (1 - alg.α l) + 3 * ε) atTop := by
      apply congr ?_ (by simp); ext n; ring_nf
    _ ≤ limsup (fun n => ‖alg.x k - m‖ ^ 2) atTop *
      limsup (fun n => (∏ l ∈ Finset.Icc k n, (1 - alg.α l))) atTop + 3 * ε := by
      rw [limsup_add_const]
      · simp only [add_le_add_iff_right]
        apply limsup_mul_le
        · simp only [norm_nonneg, pow_succ_nonneg, frequently_true_iff_neBot]; exact atTop_neBot
        · apply isBoundedUnder_const
        · apply eventually_atTop.2; use k; intro n hn; simp only [Pi.zero_apply]
          exact Finset.prod_nonneg fun i a ↦ h_nonneg_one_sub_α i
        · simp only [IsBoundedUnder, IsBounded, eventually_map, eventually_atTop, ge_iff_le]
          use 1, k; intro n hn; apply Finset.prod_le_one
          · intro i hi; exact h_nonneg_one_sub_α i
          · intro i hi; exact h_α_le_one i
      · simp only [IsBoundedUnder, IsBounded, eventually_map, eventually_atTop, ge_iff_le]
        have h_M_nonneg : 0 ≤ M := by
          by_contra h; push_neg at h; have := hM 1
          have h_contradiction : ‖alg.x 1 - m‖ ^ 2 < 0 := by linarith
          linarith [sq_nonneg (‖alg.x 1 - m‖)]
        use M, k; intro n hn; rw [← mul_one M]; apply mul_le_mul (by convert hM k) ?_ ?_ h_M_nonneg
        · apply Finset.prod_le_one
          · intro i hi; exact h_nonneg_one_sub_α i
          · intro i hi; exact h_α_le_one i
        · apply Finset.prod_nonneg; intro i hi; exact h_nonneg_one_sub_α i
      · simp only [IsCoboundedUnder, IsCobounded, eventually_map, eventually_atTop, ge_iff_le,
        forall_exists_index]; use 0; intro a p q; specialize q (p + 1) (by linarith)
        have : ‖alg.x k - m‖ ^ 2 * ∏ l ∈ Finset.Icc k (p + 1), (1 - alg.α l) ≥ 0 := by
          apply mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i a ↦ h_nonneg_one_sub_α i)
        linarith
    _ = limsup (fun n ↦ ‖alg.x k - m‖ ^ 2) atTop * 0 + 3 * ε := by
      congr; rw [h_prod_zero k]; assumption
    _ = 3 * ε := by rw [mul_zero]; simp

/--
Lemma : The convergence of `x n` : `lim n → ∞, x n = PCx`
-/
lemma halpern_convergence_aux [CompleteSpace H]
  {T : H → H} {C : Set H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (nhds 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) (m : H)
  (hm_in_C : m ∈ C)
  (h_induction : ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖)
  (h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0)
  (h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M) (z : H)
  (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M)
  : Tendsto alg.x atTop (nhds m) := by
  have h_limsup_upbd : ∀ ε > 0, limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≤ 3 * ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := halpern_limsup_bound_from_prod alg h_α_range h_α_limit h_α_sum_inf m
      hm_in_C h_induction h_limsup_neg h_inner_bounded z h_seq_bounded ε hε
    exact hN N N (le_refl N) (le_refl N) (le_refl N)
  have h_limsup_udbd : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop ≥ 0 := by
    have h0 : limsup (fun (n : ℕ) => (0 : ℝ)) atTop = (0 : ℝ) := by exact limsup_const 0
    rw [← h0]; apply limsup_le_limsup
    · apply eventually_atTop.2; use 0; intro n hn; simp
    · simp only [autoParam]; apply Filter.IsCoboundedUnder.of_frequently_ge
      exact frequently_const.mpr h_limsup_neg
    · simp only [autoParam, IsBoundedUnder, IsBounded, eventually_map, eventually_atTop, ge_iff_le]
      obtain ⟨M, hM⟩ := halpern_norm_sq_bounded alg z m h_seq_bounded
      use M, 0; intro n hn; exact hM n
  have h_limsup_zero : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop = 0 := by
    by_contra! h_ne_zero
    have h_pos : 0 < limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop :=
      lt_of_le_of_ne h_limsup_udbd (Ne.symm h_ne_zero)
    let L := limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop
    have h_all_eps : ∀ ε > 0, L ≤ 3 * ε := fun ε hε => h_limsup_upbd ε hε
    have h_sixth : 0 < L / 6 := by linarith
    have h_bound := h_all_eps (L / 6) h_sixth
    have h_contradiction : L ≤ L / 2 := by linarith
    linarith
  have h_norm_sq_tendsto_zero : Tendsto (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop (nhds 0) := by
    rw [← h_limsup_zero]; have h_nonneg : ∀ n, 0 ≤ ‖alg.x (n + 1) - m‖ ^ 2 := fun n => sq_nonneg _
    rw [Metric.tendsto_atTop]; intro ε ε_pos
    have h_eventually : ∀ᶠ n in atTop, ‖alg.x (n + 1) - m‖ ^ 2 < ε := by
      have h_limsup_lt : limsup (fun n => ‖alg.x (n + 1) - m‖ ^ 2) atTop < ε := by
        rw [h_limsup_zero]; exact ε_pos
      apply Filter.eventually_lt_of_limsup_lt (h_limsup_lt) ?_
      simp only [IsBoundedUnder, IsBounded, eventually_map, eventually_atTop, ge_iff_le]
      obtain ⟨M, hM⟩ := halpern_norm_sq_bounded alg z m h_seq_bounded
      use M, 0; intro n hn; exact hM n
    obtain ⟨N, hN⟩ := (eventually_atTop).mp h_eventually; use N; intro n hn
    rw [Real.dist_eq, h_limsup_zero]; simp only [sub_zero, abs_pow, abs_norm]
    exact abs_of_nonneg (h_nonneg n) ▸ hN n hn
  have h_shifted : Tendsto (fun n => alg.x (n + 1)) atTop (nhds m) := by
    rw [Metric.tendsto_atTop] at h_norm_sq_tendsto_zero ⊢; intro ε ε_pos
    obtain ⟨N, hN⟩ := h_norm_sq_tendsto_zero (ε ^ 2) (by positivity); use N; intro n hn
    rw [dist_eq_norm]
    have h_sq : ‖alg.x (n + 1) - m‖ ^ 2 < ε ^ 2 := by simpa [Real.dist_eq] using hN n hn
    apply sq_lt_sq.1 at h_sq; simp only [abs_norm] at h_sq
    rw [abs_of_pos ε_pos] at h_sq; assumption
  exact (tendsto_add_atTop_iff_nat 1).mp h_shifted

/--
Situation under `x 0 = x`
-/
lemma halpern_convergence_point_same [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty) (alg : Halpern T) (halg_x0 : alg.x0 ∈ D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_limit : Tendsto alg.α atTop (nhds 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|)) (coincidence : alg.u = alg.x0)
  : ∃ (p : H), p ∈ C ∧ Tendsto alg.x atTop (𝓝 p) ∧ (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  have hT_quasinonexp := nonexpansive_quasinonexpansive hT_nonexp
  have hC_closed_convex := quasinonexpansive_fixedPoint_closed_convex hD_closed hD_convex
    hD_nonempty hT_quasinonexp hC
  obtain ⟨y, hy_in_C⟩ := hT_fixpoint
  have h_induction := halpern_distance_monotone hT_nonexp hC alg halg_x0 halg_x_in_D h_α_range
    coincidence
  have h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - y‖ ≤ M := by
    use ‖alg.x0 - y‖; intro n; apply (h_induction y hy_in_C n).2
  have h_xn_bounded : ∃ M, ∀ n, ‖alg.x n‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_seq_bounded; let M2 := ‖y‖; use M1 + M2; intro n; calc
      _ = ‖(alg.x n - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖alg.x n - y‖ + ‖y‖ := by apply norm_add_le
      _ ≤ M1 + M2 := by linarith [hM1 n]
  have h_Tseq_bounded : ∃ M, ∀ n, ‖T (alg.x n) - y‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_seq_bounded; use M; intro n; calc
      _ ≤ ‖alg.x n - y‖ := (h_induction y hy_in_C n).1
      _ ≤ M := hM n
  have h_Txn_bounded : ∃ M, ∀ n, ‖T (alg.x n)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_Tseq_bounded; let M2 := ‖y‖; use M1 + M2; intro n; calc
      _ = ‖(T (alg.x n) - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖T (alg.x n) - y‖ + ‖y‖ := by apply norm_add_le
      _ ≤ M1 + M2 := by linarith [hM1 n]
  have h_diff_bounded : ∃ M, ∀ n, ‖alg.x (n + 1) - T (alg.x n)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := h_seq_bounded; obtain ⟨M2, hM2⟩ := h_Tseq_bounded
    use M1 + M2; intro n; calc
      _ = ‖(alg.x (n + 1) - y) - (T (alg.x n) - y)‖ := by congr 1; rw [sub_sub_sub_cancel_right]
      _ ≤ ‖alg.x (n + 1) - y‖ + ‖T (alg.x n) - y‖ := by apply norm_sub_le
      _ ≤ M1 + M2 := by linarith [hM1 (n + 1), hM2 n]
  have ⟨μ, hμ_pos, hμ_x_bound, hμ_Tx_bound⟩ : ∃ μ : ℝ, μ > 0 ∧
    (∀ n, ‖alg.x (n + 1) - alg.x n‖ ≤ μ) ∧(∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
      := halpern_mu_bound alg h_diff_bounded h_Tseq_bounded h_seq_bounded
  let h_diff_formula := halpern_diff_formula alg
  have h_norm_diff_ineq := halpern_norm_diff_ineq alg hT_nonexp halg_x_in_D h_α_range
    h_diff_formula μ hμ_Tx_bound
  have h_telescoping := halpern_telescoping_ineq
    alg h_α_range μ hμ_pos hμ_x_bound h_norm_diff_ineq
  have h_diff_limit := halpern_diff_limit alg h_α_range μ hμ_pos
    h_α_diff_finite h_α_sum_inf hμ_x_bound h_norm_diff_ineq h_telescoping
  have h_x_Tx_limit : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (nhds 0) :=
    halpern_x_sub_Tx_tendsto_zero alg h_α_range h_α_limit μ hμ_pos hμ_Tx_bound h_diff_limit
  obtain ⟨p, z, m, q, h_n_strict_mono, ⟨h_z_in_D, h_weak_xn_to_z⟩, ⟨hm_in_C, hm_proj⟩, hq_def,
    h_n_tendsto⟩ := halpern_subsequence_weak_convergence hD_closed hD_convex (by use y)
      alg halg_x_in_D hC_closed_convex h_xn_bounded h_Txn_bounded
  have h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (p k) - T (alg.x (p k))) atTop (nhds 0) :=
    halpern_subseq_x_sub_Tx_tendsto_zero alg p h_n_strict_mono h_x_Tx_limit
  have h_z_fixed : z ∈ Fix T :=
    halpern_subseq_fixed_point hD_closed hD_convex hD_nonempty hT_nonexp
      alg p z h_z_in_D h_weak_xn_to_z halg_x_in_D h_subseq_x_Tx_limit
  have h_z_in_C : z ∈ C := by rw [hC]; exact ⟨h_z_fixed, h_z_in_D⟩
  have h_limsup_neg : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0 := by
    apply halpern_limsup_inner_le_zero hC hC_closed_convex alg p z h_z_in_C
      h_weak_xn_to_z m hm_in_C hm_proj h_subseq_x_Tx_limit
    rw [hq_def] at h_n_tendsto; exact h_n_tendsto
  have h_inner_bounded : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M :=
    halpern_inner_bounded_of_limsup alg m μ hμ_Tx_bound h_limsup_neg
  have h_x_conv : Tendsto alg.x atTop (nhds m) := by
    exact halpern_convergence_aux alg h_α_range h_α_limit h_α_sum_inf m hm_in_C
      h_induction h_limsup_neg h_inner_bounded y h_seq_bounded
  use m; use hm_in_C; use h_x_conv; intro w hw_in_C
  apply proj_pt_inner_le_zero alg.u m C ?_ hm_in_C hm_proj w hw_in_C; rw [hC]
  rcases hC_closed_convex with ⟨h1,h2⟩; rw [← hC]; assumption

/--
Lemma 30.20.1: The distance of the two sequences is upbounded :
  `‖x (n + 1) - y (n + 1)‖ ≤ ‖x 0 - y 0‖ * ∏_0^n (1 - λ k)`
-/
lemma halpern_norm_diff_bound
  {T : H → H} (alg : Halpern T) {D : Set H} (hT_nonexp : NonexpansiveOn T D)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (halg_u : alg.u ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (s : ℕ → H) (h_s_init : s 0 = alg.u) (h_s_in_D : ∀ n, s n ∈ D)
  (h_s_update : ∀ k, s (k + 1) = alg.α k • alg.u + (1 - alg.α k) • T (s k))
  : ∀ n : ℕ, ‖alg.x (n + 1) - s (n + 1)‖
    ≤ ‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 n, (1 - alg.α k) := by
  have h_α_lt_one : ∀ n, alg.α n < 1 := by intro n; exact (h_α_range n).2
  intro n; induction n with
  | zero =>
    simp only [zero_add, alg.update, h_s_update, add_sub_add_left_eq_sub, ← smul_sub,
      Finset.Icc_self, Finset.prod_singleton]; calc
      _ = (1 - alg.α 0) * ‖T (alg.x 0) - T alg.u‖ := by
        rw [norm_smul]; simp only [Real.norm_eq_abs]
        congr; apply abs_of_pos; linarith [h_α_lt_one 0]
      _ ≤ (1 - alg.α 0) * ‖alg.x 0 - alg.u‖ := by
        apply mul_le_mul_of_nonneg_left
        · rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
          specialize hT_nonexp (halg_x_in_D 0) halg_u
          simp only [ENNReal.coe_one, one_mul] at hT_nonexp
          rw [edist_dist, edist_dist] at hT_nonexp
          simp only [dist_nonneg, ENNReal.ofReal_le_ofReal_iff] at hT_nonexp
          rw[dist_eq_norm, dist_eq_norm] at hT_nonexp; exact hT_nonexp
        · simp only [sub_nonneg]; linarith [h_α_lt_one 0]
      _ = (1 - alg.α 0) * ‖alg.x 0 - s 0‖ := by rw [h_s_init]
      _ = ‖alg.x 0 - s 0‖ * (1 - alg.α 0) := by ring_nf
  | succ n ih => calc
      _ = ‖(alg.α (n + 1) • alg.u + (1 - alg.α (n + 1)) • T (alg.x (n + 1)))
        - (alg.α (n + 1) • alg.u + (1 - alg.α (n + 1)) • T (s (n + 1)))‖ := by
        rw [alg.update, h_s_update]
      _ =  ‖(1 - alg.α (n + 1)) • (T (alg.x (n + 1)) - T (s (n + 1)))‖ := by
        simp [← smul_sub (1 - alg.α (n + 1)) (T (alg.x (n + 1))) (T (s (n + 1)))]
      _ = (1 - alg.α (n + 1)) * ‖T (alg.x (n + 1)) - T (s (n + 1))‖ := by
        rw [norm_smul]; simp only [Real.norm_eq_abs, mul_eq_mul_right_iff, abs_eq_self, sub_nonneg,
          norm_eq_zero]; left; linarith [h_α_lt_one (n + 1)]
      _ ≤ (1 - alg.α (n + 1)) * (‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) := by
        apply mul_le_mul_of_nonneg_left
        · rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
          specialize hT_nonexp (halg_x_in_D (n + 1)) (h_s_in_D (n + 1))
          simp only [ENNReal.coe_one, one_mul] at hT_nonexp
          rw [edist_dist, edist_dist] at hT_nonexp
          simp only [dist_nonneg, ENNReal.ofReal_le_ofReal_iff] at hT_nonexp
          rw[dist_eq_norm, dist_eq_norm] at hT_nonexp; exact Std.le_trans hT_nonexp ih
        · simp only [sub_nonneg]; linarith [h_α_lt_one (n + 1)]
      _ = ‖alg.x 0 - s 0‖ * (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * (1 - alg.α (n + 1)) := by
        ring_nf
      _ = ‖alg.x 0 - s 0‖ * ∏ k ∈ Finset.Icc 0 (n + 1), (1 - alg.α k) := by
        nth_rewrite 2 [← Nat.succ_eq_add_one]; rw [Finset.prod_Icc_succ_top]
        · rw [← mul_assoc]
        · linarith

/--
Lemma 30.20.2: The limit of the product : `lim n → ∞, ∏_0^n (1 - λ k) * ‖x 0 - y 0‖ = 0`
-/
lemma halpern_prod_norm_diff_tendsto_zero
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (s : ℕ → H)
  : Tendsto (fun n => ((∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * ‖alg.x 0 - s 0‖))
    atTop (nhds 0) := by
  have h_prod_tendsto_zero : Tendsto (fun n => (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k))
    * ‖alg.x 0 - s 0‖) atTop (nhds (0 * ‖alg.x 0 - s 0‖)) := by
    have h_prod := infinite_prod_zero alg h_α_range h_α_sum_inf 0
    apply Tendsto.mul_const; exact h_prod
  convert h_prod_tendsto_zero; simp

/--
Situation under `x 0 ≠ u`
-/
lemma halpern_convergence_point_different [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty) (hT_invariant : ∀ x ∈ D, T x ∈ D) (alg : Halpern T)
  (halg_u : alg.u ∈ D) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (h_α_limit : Tendsto alg.α atTop (nhds 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  : ∃ (p : H), p ∈ C ∧ Tendsto alg.x atTop (nhds p) ∧ (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  have h_α_pos : ∀ n, 0 < alg.α n := by intro n; exact (h_α_range n).1
  have h_α_lt_one : ∀ n, alg.α n < 1 := by intro n; exact (h_α_range n).2
  let s0 := alg.u
  let s : ℕ → H := fun n => Nat.recOn n alg.u fun k sk => alg.α k • alg.u + (1 - alg.α k) • T sk
  have h_s_init : s 0 = alg.u := by simp [s]
  have h_s_update : ∀ k, s (k + 1) = alg.α k • alg.u + (1 - alg.α k) • T (s k) := by
    intro k; simp only [s]
  have h_s_in_D : ∀ n, s n ∈ D := by
    intro n; induction n with
    | zero => rw [h_s_init]; exact halg_u
    | succ k ih =>
      rw [h_s_update]
      exact hD_convex halg_u (hT_invariant (s k) ih) (by linarith [h_α_pos k, h_α_lt_one k])
        (by linarith [h_α_pos k, h_α_lt_one k]) (by simp)
  have ⟨p, hp_in_C, hp_s_conv, hp_inner⟩ : ∃ (p : H), p ∈ C ∧ Tendsto s atTop (nhds p) ∧
    (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
    apply halpern_convergence_point_same
      hD_closed hD_convex hD_nonempty hT_nonexp hC hT_fixpoint
      { x0 := alg.u
        u := alg.u
        x := s
        α := alg.α
        update := h_s_update
        initial_value := h_s_init }
      halg_u h_s_in_D h_α_range h_α_limit h_α_sum_inf h_α_diff_finite
      rfl
  have h_norm_bounded := halpern_norm_diff_bound alg hT_nonexp halg_x_in_D halg_u
    h_α_range s h_s_init h_s_in_D h_s_update
  have h_prod_tendsto_zero' :=
    halpern_prod_norm_diff_tendsto_zero alg h_α_range h_α_sum_inf s
  have h_diff_tendsto_zero : Tendsto (fun n => ‖alg.x (n + 1) - s (n + 1)‖) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at h_prod_tendsto_zero' ⊢
    intro ε ε_pos; obtain ⟨N, hN⟩ := h_prod_tendsto_zero' ε ε_pos; use N; intro n hn
    specialize hN n hn; rw [Real.dist_eq] at hN ⊢; simp only [sub_zero] at hN ⊢
    simp only [abs_norm]; calc
      _ ≤ ‖alg.x 0 - s 0‖ * (∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) := h_norm_bounded n
      _ = |(∏ k ∈ Finset.Icc 0 n, (1 - alg.α k)) * ‖alg.x 0 - s 0‖| := by
        rw [abs_of_nonneg]
        · ring_nf
        · apply mul_nonneg ?_ (norm_nonneg _); apply Finset.prod_nonneg; intro k hk; simp
          linarith [h_α_lt_one k]
      _ < ε := hN
  have h_x_tendsto_p : Tendsto alg.x atTop (nhds p) := by
    rw [Metric.tendsto_atTop] at hp_s_conv ⊢; intro ε ε_pos
    have h_diff_tendsto : Tendsto (fun n => alg.x n - s n) atTop (nhds 0) :=
      ((tendsto_add_atTop_iff_nat 1).mp (Metric.tendsto_atTop.mpr fun ε hε => by
          rw [Metric.tendsto_atTop] at h_diff_tendsto_zero
          obtain ⟨N, hN⟩ := h_diff_tendsto_zero ε hε; use N; intro n hn; specialize hN n hn
          rw [dist_eq_norm] at hN ⊢; simp only [sub_zero, norm_norm] at hN ⊢; exact hN))
    rw [Metric.tendsto_atTop] at h_diff_tendsto
    obtain ⟨N1, hN1⟩ := hp_s_conv (ε / 2) (by linarith)
    obtain ⟨N2, hN2⟩ := h_diff_tendsto (ε / 2) (by linarith)
    use max N1 N2; intro n hn
    have h1 := hN1 n (le_of_max_le_left hn); have h2 := hN2 n (le_of_max_le_right hn)
    rw [dist_eq_norm] at h1 h2 ⊢; simp only [sub_zero] at h2; calc
      _ = ‖(alg.x n - s n) + (s n - p)‖ := by simp
      _ ≤ ‖alg.x n - s n‖ + ‖s n - p‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h1
      _ = ε := by ring
  exact ⟨p, hp_in_C, h_x_tendsto_p, hp_inner⟩

/--
Theorem 30.1 Halpern's Algorithm
-/
theorem halpern_convergence' [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hT_fixpoint : C.Nonempty) (hT_invariant : ∀ x ∈ D, T x ∈ D) (alg : Halpern T)
  (halg_x0 : alg.x0 ∈ D) (halg_u : alg.u ∈ D) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (h_α_limit : Tendsto alg.α atTop (nhds 0))
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|)) :
  ∃ (p : H), p ∈ C ∧ Tendsto alg.x atTop (𝓝 p) ∧ (∀ w ∈ C, ⟪alg.u - p, w - p⟫ ≤ 0) := by
  by_cases h_coincidence : alg.u = alg.x0
  · -- Case: u = x0
    exact halpern_convergence_point_same hD_closed hD_convex hD_nonempty hT_nonexp hC hT_fixpoint
      alg halg_x0 halg_x_in_D h_α_range h_α_limit h_α_sum_inf h_α_diff_finite h_coincidence
  · -- Case: u ≠ x0
    exact halpern_convergence_point_different hD_closed hD_convex hD_nonempty hT_nonexp hC
      hT_fixpoint hT_invariant alg halg_u halg_x_in_D h_α_range h_α_limit h_α_sum_inf
      h_α_diff_finite

theorem halpern_convergence [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (hCn : C.Nonempty) (hT_inD : ∀ x ∈ D, T x ∈ D) (alg : Halpern T)
  (halg_x0 : alg.x0 ∈ D) (halg_u : alg.u ∈ D) (halg_xD : ∀ n, alg.x n ∈ D)
  (hα1 : ∀ n, alg.α n ∈ Set.Ioo 0 1) (hα2 : Tendsto alg.α atTop (nhds 0))
  (hα3 : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop)
  (hα4 : Summable (fun n => |alg.α (n + 1) - alg.α n|)) :
  ∃ (p : H), p ∈ C ∧ Tendsto alg.x atTop (𝓝 p) ∧ (‖alg.u - p‖ = ⨅ w : C, ‖alg.u - w‖) := by
    obtain ⟨p,hp1,hp2,hp3⟩ := halpern_convergence' hD_closed hD_convex
      hD_nonempty hT_nonexp hC hCn hT_inD alg halg_x0 halg_u halg_xD hα1 hα2 hα3 hα4
    use p,hp1,hp2
    have hCc: Convex ℝ C := by
      have hq : QuasiNonexpansiveOn T D := by
        exact nonexpansive_quasinonexpansive hT_nonexp
      exact (quasinonexpansive_fixedPoint_closed_convex hD_closed hD_convex hD_nonempty hq hC).2
    obtain hh:= (norm_eq_iInf_iff_real_inner_le_zero hCc hp1).2 hp3
    exact hh
