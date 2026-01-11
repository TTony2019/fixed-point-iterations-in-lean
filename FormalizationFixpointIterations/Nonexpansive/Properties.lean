/-
Copyright (c) 2025 Yantao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yantao Li
-/
import FormalizationFixpointIterations.Nonexpansive.Definitions
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Function
namespace Nonexpansive_operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

/--
Proposition 4.23 (i) : If T if quasinonexpansive on D, then
  `Fix T ∩ D = ⋂ {x ∈ D} {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2}`
-/
theorem quasinonexpansive_fixedPoint_characterization {D : Set H} (hD_nonempty : D.Nonempty)
  {T : H → H} (hT : QuasiNonexpansiveOn T D) :
  Fix T ∩ D = ⋂ x ∈ D, {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} := by
  ext y; constructor
  · intro ⟨hy_fix, hy_D⟩; simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro x hx
    constructor
    · exact hy_D
    · have h_fix : IsFixedPt T y := hy_fix
      have hy_in_fix' : y ∈ FixOn T D := ⟨hy_D, h_fix⟩
      have h_quasi := hT hx hy_in_fix'
      have h_norm_sq : ‖T x - y‖^2 ≤ ‖x - y‖^2 :=
        sq_le_sq' (by linarith [norm_nonneg (T x - y)]) h_quasi
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h_norm_sq
      have eq1 : inner ℝ (T x - y) (T x - y) = inner ℝ (T x - x) (T x - x) +
        2 * inner ℝ (T x - x) (x - y) + inner ℝ (x - y) (x - y) := by
        calc
          _ = inner ℝ ((T x - x) + (x - y)) ((T x - x) + (x - y)) := by
            congr 1; repeat rw [sub_add_sub_cancel]
          _ = inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - y)
            + inner ℝ (x - y) (x - y) := by
            simp only [inner_add_left, inner_add_right,
              inner_sub_left, inner_sub_right, real_inner_comm]; ring_nf
      rw [eq1] at h_norm_sq
      have eq2 : inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)
        + 2 * inner ℝ (T x - x) (T x - y) ≤ 0 := by calc
          _ = inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - y) := by
            simp [inner_sub_left, inner_sub_right, real_inner_comm]; ring_nf
          _ ≤ 0 := by linarith
      calc
        _ = -inner ℝ (y - T x) (T x - x) := by rw [inner_sub_right, inner_sub_right]; ring
        _ ≤ -(inner ℝ (T x - x) (T x - x) + 2 * inner ℝ (T x - x) (x - T x)) / 2 := by
          have h1 : inner ℝ (T x - x) (T x - y) = -inner ℝ (T x - x) (y - T x) := by
            simp only [inner_sub_right]; ring
          rw [real_inner_comm (T x - x) (y - T x), ← h1]
          nlinarith [eq2]
        _ = (1/2) * ‖T x - x‖^2 := by
          rw [real_inner_self_eq_norm_sq, mul_comm]
          have h_neg : inner ℝ (T x - x) (x - T x) = - inner ℝ (T x - x) (T x - x) := by
            simp only [inner_sub_right]; ring
          rw [h_neg]; simp
          field_simp [norm_eq_zero]; linarith
  · intro hy; simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
    constructor
    · obtain ⟨x0, hx0⟩ := hD_nonempty; have hy_D := (hy x0 hx0).1; have h_y := (hy y hy_D).2
      have h_eq : inner ℝ (y - T y) (y - T y) = ‖y - T y‖ ^ 2 := real_inner_self_eq_norm_sq _
      have h_sym : ‖y - T y‖ ^ 2 = ‖T y - y‖ ^ 2 := by rw [norm_sub_rev]
      rw [h_eq, h_sym] at h_y
      have : (1/2) * ‖T y - y‖ ^ 2 ≤ 0 := by linarith
      have h_zero : ‖T y - y‖ ^ 2 = 0 := by
        have h_nonneg : 0 ≤ ‖T y - y‖ ^ 2 := sq_nonneg _; linarith
      exact eq_of_norm_sub_eq_zero (sq_eq_zero_iff.mp h_zero)
    · obtain ⟨x0, hx0⟩ := hD_nonempty
      exact (hy x0 hx0).1

/--
auxiliary lemma 1: `{x : H | ⟪x - a, b⟫ ≤ c}` is closed
-/
lemma halfspace_is_closed
  (a b : H) (c : ℝ) : IsClosed {x : H | ⟪x - a, b⟫ ≤ c} := by
  have : {x : H | ⟪x - a, b⟫ ≤ c} = (fun x => ⟪x - a, b⟫) ⁻¹' Set.Iic c := by
    ext x; simp [Set.mem_Iic]
  rw [this]; apply IsClosed.preimage ?_ isClosed_Iic
  apply Continuous.inner (continuous_id.sub continuous_const) (continuous_const)

/--
auxiliary lemma 2: `{x : H | ⟪x - a, b⟫ ≤ c}` is convex
-/
lemma halfspace_is_convex
  (a b : H) (c : ℝ) : Convex ℝ {x : H | ⟪x - a, b⟫ ≤ c} := by
  intro x hx y hy t1 t2 ht1 ht2 ht; simp only [Set.mem_setOf_eq] at hx hy ⊢; calc
    _ = ⟪t1 • x + t2 • y - (t1 • a + t2 • a), b⟫ := by congr 1; rw [← add_smul]; simp [ht]
    _ = ⟪t1 • (x - a) + t2 • (y - a), b⟫ := by
      congr 1; simp [smul_sub, sub_add_eq_sub_sub, add_sub, add_comm]
    _ = t1 * ⟪x - a, b⟫ + t2 * ⟪y - a, b⟫ := by
      rw [inner_add_left, inner_smul_left, inner_smul_left]; norm_cast
    _ ≤ t1 * c + t2 * c := add_le_add
      (mul_le_mul_of_nonneg_left hx ht1) (mul_le_mul_of_nonneg_left hy (by linarith))
    _ = c := by rw [← add_mul]; simp [ht]

/--
Lemma: `{x : H | ⟪x - a, b⟫ ≤ c}` is closed and convex
-/
lemma intersection_set_is_closed_convex
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : H → H} (x : H) :
  IsClosed {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} ∧
  Convex ℝ {y ∈ D | ⟪y - T x, x - T x⟫ ≤ (1/2) * ‖T x - x‖^2} := by
  constructor
  · exact IsClosed.inter hD_closed (halfspace_is_closed (T x) (x - T x) ((1/2) * ‖T x - x‖^2))
  · exact Convex.inter hD_convex (halfspace_is_convex (T x) (x - T x) ((1/2) * ‖T x - x‖^2))

/--
Proposition 4.23(ii) : If T is quasinonexpansive on D, then `Fix T ∩ D` is closed and convex
-/
theorem quasinonexpansive_fixedPoint_closed_convex
  {C D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT : QuasiNonexpansiveOn T D) (hC : C = Fix T ∩ D) : IsClosed C ∧ Convex ℝ C := by
  rw [hC, quasinonexpansive_fixedPoint_characterization hD_nonempty hT]
  constructor
  · exact isClosed_biInter fun x _ => (intersection_set_is_closed_convex hD_closed hD_convex x).1
  · exact convex_iInter₂ fun x _ => (intersection_set_is_closed_convex hD_closed hD_convex x).2

omit [InnerProductSpace ℝ H] in
/--
Lemma : T is nonexpansive on D → T is quasinonexpansive on D
-/
theorem nonexpansive_quasinonexpansive {D : Set H} {T : H → H}
  (hT_nonexp : NonexpansiveOn T D) : QuasiNonexpansiveOn T D := by
  intro x hx y hy
  rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp; rw [FixOn] at hy; rcases hy with ⟨hyD,hyFix⟩
  have h_edist := hT_nonexp hx hyD; simp only [ENNReal.coe_one, one_mul] at h_edist
  rw [hyFix, edist_dist, edist_dist] at h_edist
  have h_dist : dist (T x) y ≤ dist x y := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h_edist
  rw [dist_eq_norm, dist_eq_norm] at h_dist
  exact h_dist

end Nonexpansive_operator
