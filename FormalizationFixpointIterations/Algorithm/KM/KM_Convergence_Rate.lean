import FormalizationFixpointIterations.Algorithm.KM.Lemma
import FormalizationFixpointIterations.Algorithm.KM.KM
open Set Filter Topology TopologicalSpace Metric BigOperators Finset Function Nonexpansive_operator

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma KM_sum_bound {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT_nonexpansive : NonexpansiveOn T D) (km : KM D T) (hD : Convex ℝ D)
  (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop)
  (y0 : H) (hy0 : y0 ∈ Fix T ∩ D) :
  ∀ N, ∑ i ∈ range N, km.α i * (1 - km.α i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
    ‖km.x 0 - y0‖ ^ 2 - ‖km.x N - y0‖ ^ 2 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := key_inequality T h_Im_T_in_D hT_nonexpansive km hD hα1 hα2 y0 hy0 N
    simp [Finset.sum_range_succ]
    linarith

lemma KM_residual_nonincreasing {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT_nonexpansive : NonexpansiveOn T D) (km : KM D T) (hD : Convex ℝ D)
  (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop) :
  ∀ n, ‖T (km.x (n + 1)) - km.x (n + 1)‖ ≤ ‖T (km.x n) - km.x n‖ := by
  intro n
  rcases hα1 n with ⟨hs0, hs1⟩
  have hx : km.x (n + 1) - km.x n = km.α n • (T (km.x n) - km.x n) := by
    rw [km.update n]
    simp [smul_sub]
  have eq : T (km.x (n + 1)) - km.x (n + 1) =
      (T (km.x (n + 1)) - T (km.x n)) + (1 - km.α n) • (T (km.x n) - km.x n) := by
    calc
      T (km.x (n + 1)) - km.x (n + 1) = T (km.x (n + 1)) - T (km.x n) + T (km.x n) - km.x (n + 1) := by simp
      _ = T (km.x (n + 1)) - T (km.x n) + (1 - km.α n) • (T (km.x n) - km.x n) := by
        nth_rw 2 [km.update n]
        simp only [smul_sub, sub_smul, one_smul]
        abel_nf
  calc
    ‖T (km.x (n + 1)) - km.x (n + 1)‖
        = ‖(T (km.x (n + 1)) - T (km.x n)) + (1 - km.α n) • (T (km.x n) - km.x n)‖ := by rw [eq]
    _ ≤ ‖T (km.x (n + 1)) - T (km.x n)‖ + ‖(1 - km.α n) • (T (km.x n) - km.x n)‖ := by
      exact norm_add_le _ _
    _ ≤ ‖km.x (n + 1) - km.x n‖ + (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by
      apply add_le_add
      · apply norm_le_mul_On hT_nonexpansive (km.x (n + 1)) (km.x n)
        · exact x_in_D h_Im_T_in_D km (x0_in_D km) hD hα1 hα2 (n + 1)
        · exact x_in_D h_Im_T_in_D km (x0_in_D km) hD hα1 hα2 n
      · have h_nonneg : 0 ≤ 1 - km.α n := by linarith
        have hsmul_eq : ‖(1 - km.α n) • (T (km.x n) - km.x n)‖ =
            (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by
          calc
            ‖(1 - km.α n) • (T (km.x n) - km.x n)‖ = ‖(1 - km.α n)‖ * ‖T (km.x n) - km.x n‖ := by rw [norm_smul]
            _ = |1 - km.α n| * ‖T (km.x n) - km.x n‖ := by rw [Real.norm_eq_abs]
            _ = (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by rw [abs_of_nonneg h_nonneg]
        exact le_of_eq hsmul_eq
    _ = ‖km.α n • (T (km.x n) - km.x n)‖ + (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by rw [hx]
    _ = km.α n * ‖T (km.x n) - km.x n‖ + (1 - km.α n) * ‖T (km.x n) - km.x n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    _ = ‖T (km.x n) - km.x n‖ := by ring


/--
This theorem proves an O(1 / sqrt(n)) upper bound for the KM residual norm ‖T (km.x n) - km.x n‖.
-/
theorem KM_Conv_Rate {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D)
  (hT_nonexpansive : NonexpansiveOn T D) (km : KM D T) (hD : Convex ℝ D) (hα1 : ∀ n, km.α n ∈ Set.Icc (0 : ℝ) 1)
  (hα2 : Tendsto (fun n => ∑ i ∈ range (n + 1), km.α i * (1 - km.α i)) atTop atTop)
  (hα3 : ∃ α_inf : ℝ, 0 < α_inf ∧ ∀ n, α_inf ≤ km.α n)
  (hα4 : ∃ α_sup : ℝ, α_sup < 1 ∧ ∀ n, km.α n ≤ α_sup)
  (fix_T_nonempty : (Fix T ∩ D).Nonempty) : ∃ d_0: ℝ, ∃ τ_inf : ℝ, ∀ n,
  ‖T (km.x n) - km.x n‖ ≤ Real.sqrt (d_0^2 / (τ_inf * (n + 1 : ℝ))) := by
  rcases fix_T_nonempty with ⟨y0, hy0⟩
  rcases hα3 with ⟨α_inf, hα_inf_pos, hα_inf_le⟩
  rcases hα4 with ⟨α_sup, hα_sup_lt_one, hα_le_sup⟩
  let τ_inf : ℝ := α_inf * (1 - α_sup)
  have hτ_pos : 0 < τ_inf := by
    have h1 : 0 < 1 - α_sup := by linarith
    exact mul_pos hα_inf_pos h1
  have hτ_le : ∀ i, τ_inf ≤ km.α i * (1 - km.α i) := by
    intro i
    have h_left : α_inf * (1 - α_sup) ≤ α_inf * (1 - km.α i) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [hα_le_sup i]
      · exact le_of_lt hα_inf_pos
    have h_right : α_inf * (1 - km.α i) ≤ km.α i * (1 - km.α i) := by
      apply mul_le_mul_of_nonneg_right
      · exact hα_inf_le i
      · rcases hα1 i with ⟨_, hi_le_one⟩
        linarith
    exact le_trans h_left h_right
  have sum_bound : ∀ N, ∑ i ∈ range N, km.α i * (1 - km.α i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 - ‖km.x N - y0‖ ^ 2 :=
    KM_sum_bound T h_Im_T_in_D hT_nonexpansive km hD hα1 hα2 y0 hy0
  have partial_le : ∀ N, ∑ i ∈ Finset.range N, km.α i * (1 - km.α i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 := by
    intro N
    refine (sum_bound N).trans ?_
    simp
  let a := fun n => ‖T (km.x n) - km.x n‖
  have a_noninc : ∀ n, a (n + 1) ≤ a n := by
    intro n
    simpa [a] using KM_residual_nonincreasing T h_Im_T_in_D hT_nonexpansive km hD hα1 hα2 n
  use ‖km.x 0 - y0‖
  use τ_inf
  intro n
  have hpoint : ∀ i ∈ Finset.range (n + 1), τ_inf * (a n) ^ 2 ≤ km.α i * (1 - km.α i) * (a i) ^ 2 := by
    intro i hi
    have hi_le_n : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have han : a n ≤ a i := (antitone_nat_of_succ_le a_noninc) hi_le_n
    have han_sq : (a n) ^ 2 ≤ (a i) ^ 2 := by
      refine pow_le_pow_left₀ ?_ han 2
      exact norm_nonneg _
    have hcoef_nonneg : 0 ≤ km.α i * (1 - km.α i) := by
      rcases hα1 i with ⟨hi0, hi1⟩
      apply mul_nonneg
      · exact hi0
      · linarith
    calc
      τ_inf * (a n) ^ 2 ≤ (km.α i * (1 - km.α i)) * (a n) ^ 2 := by
        apply mul_le_mul_of_nonneg_right (hτ_le i)
        exact pow_nonneg (norm_nonneg _) 2
      _ ≤ (km.α i * (1 - km.α i)) * (a i) ^ 2 := by
        apply mul_le_mul_of_nonneg_left han_sq hcoef_nonneg
      _ = km.α i * (1 - km.α i) * (a i) ^ 2 := by ring
  have hsum_lower_aux : Finset.sum (Finset.range (n + 1)) (fun _ => τ_inf * (a n) ^ 2) ≤
      Finset.sum (Finset.range (n + 1)) (fun i => km.α i * (1 - km.α i) * (a i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i hi
  have hsum_lower : (n + 1 : ℝ) * (τ_inf * (a n) ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), km.α i * (1 - km.α i) * (a i) ^ 2 := by
    calc
      (n + 1 : ℝ) * (τ_inf * (a n) ^ 2) = Finset.sum (Finset.range (n + 1)) (fun _ => τ_inf * (a n) ^ 2) := by
        symm
        simp
      _ ≤ Finset.sum (Finset.range (n + 1)) (fun i => km.α i * (1 - km.α i) * (a i) ^ 2) := hsum_lower_aux
      _ = ∑ i ∈ Finset.range (n + 1), km.α i * (1 - km.α i) * (a i) ^ 2 := by simp
  have hmain : (n + 1 : ℝ) * (τ_inf * (a n) ^ 2) ≤ ‖km.x 0 - y0‖ ^ 2 := by
    exact le_trans hsum_lower (partial_le (n + 1))
  have hden_pos : 0 < τ_inf * (n + 1 : ℝ) := by
    have hnat : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    exact mul_pos hτ_pos hnat
  have han_sq_le : (a n) ^ 2 ≤ ‖km.x 0 - y0‖ ^ 2 / (τ_inf * (n + 1 : ℝ)) := by
    refine (le_div_iff₀ hden_pos).2 ?_
    have hmain' : (τ_inf * (n + 1 : ℝ)) * (a n) ^ 2 ≤ ‖km.x 0 - y0‖ ^ 2 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain'
  have hsqrt_den_pos : 0 < Real.sqrt (τ_inf * (n + 1 : ℝ)) := Real.sqrt_pos.mpr hden_pos
  have hrhs_nonneg : 0 ≤ ‖km.x 0 - y0‖ / Real.sqrt (τ_inf * (n + 1 : ℝ)) := by
    exact div_nonneg (norm_nonneg _) (le_of_lt hsqrt_den_pos)
  have hsq_rhs : (‖km.x 0 - y0‖ / Real.sqrt (τ_inf * (n + 1 : ℝ))) ^ 2
      = ‖km.x 0 - y0‖ ^ 2 / (τ_inf * (n + 1 : ℝ)) := by
    have hsqrt_sq : (Real.sqrt (τ_inf * (n + 1 : ℝ))) ^ 2 = τ_inf * (n + 1 : ℝ) := by
      exact Real.sq_sqrt (le_of_lt hden_pos)
    calc
      (‖km.x 0 - y0‖ / Real.sqrt (τ_inf * (n + 1 : ℝ))) ^ 2
          = ‖km.x 0 - y0‖ ^ 2 / (Real.sqrt (τ_inf * (n + 1 : ℝ))) ^ 2 := by ring
      _ = ‖km.x 0 - y0‖ ^ 2 / (τ_inf * (n + 1 : ℝ)) := by rw [hsqrt_sq]
  have hsq : (a n) ^ 2 ≤ (‖km.x 0 - y0‖ / Real.sqrt (τ_inf * (n + 1 : ℝ))) ^ 2 := by
    simpa [hsq_rhs] using han_sq_le
  have habs : |a n| ≤ |‖km.x 0 - y0‖ / Real.sqrt (τ_inf * (n + 1 : ℝ))| :=
    (sq_le_sq).1 hsq
  have han_nonneg : 0 ≤ a n := norm_nonneg _
  have hfinal : a n ≤ ‖km.x 0 - y0‖ / Real.sqrt (τ_inf * (n + 1 : ℝ)) := by
    simpa [abs_of_nonneg han_nonneg, abs_of_nonneg hrhs_nonneg] using habs
  simpa [a]
