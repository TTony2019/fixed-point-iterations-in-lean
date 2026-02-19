import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.InnerProductSpace.WeakConverge
import FormalizationFixpointIterations.InnerProductSpace.Closedness

open WeakDual
-- open Filter WeakDual Metric WeakBilin Topology Function TopologicalSpace

section T2Space

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

lemma norm_sub_sq_eq_inner (a b : H) : ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * ⟪a,b⟫ := by
  calc
    _ = ⟪a - b, a - b⟫ := Eq.symm (real_inner_self_eq_norm_sq (a - b))
    _ = ⟪a, a⟫ + ⟪b, b⟫ - 2 * ⟪a,b⟫ := by
      rw [real_inner_sub_sub_self]
      rw [sub_add_eq_add_sub]
    _ = ‖a‖^2 + ‖b‖^2 - 2 * ⟪a,b⟫ := by
      repeat rw [← real_inner_self_eq_norm_sq]

instance inst_WeakSpace_T2 : T2Space (WeakSpace ℝ H) where
  t2 := by
    simp only [Pairwise, ne_eq, exists_and_left]
    intro x y hxy
    let u := x - y
    let f1 := WeakSpace.map (@cont_inner_left H _ _ u)
    let f2 := (toWeakSpace ℝ ℝ).symm
    let f := f2 ∘ f1
    have feq (t : H): f t = (@cont_inner_left H _ _ u) t := rfl
    let c := (f x + f y)/2
    let U := {z : H | f z > c}
    let V := {z : H | f z < c}
    have Uopen : @IsOpen (WeakSpace ℝ H) _ U := by
      refine isOpen_lt ?_ ?_
      · exact continuous_const
      simp only [f]
      refine Continuous.comp ?_ ?_
      · exact continuous_real_weakspace
      exact ContinuousLinearMap.continuous f1
    have Vopen : @IsOpen (WeakSpace ℝ H) _ V := by
      simp only [V]
      refine isOpen_lt ?_ ?_
      · simp only [f]
        refine Continuous.comp ?_ ?_
        · exact continuous_real_weakspace
        exact ContinuousLinearMap.continuous f1
      exact continuous_const
    have xinUV : x ∈ U ∧ y ∈ V := by
      constructor
      · simp only [gt_iff_lt, U]
        change f x > c
        simp only [feq, cont_inner_left, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
          AddHom.coe_mk, gt_iff_lt]
        refine (add_lt_add_iff_left ?_).mp ?_
        · exact c
        · refine (add_lt_add_iff_left c).mpr ?_
          simp only [toWeakSpace, LinearEquiv.refl_symm, cont_inner_left, WeakSpace.coe_map,
            ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, c, f,
            f2, f1]
          rw [LinearEquiv.refl]
          simp only [LinearMap.id, Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl,
            LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id_eq, u]
          simp only [inner_sub_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
          let xH : H := (toWeakSpace ℝ H).symm x
          let yH : H := (toWeakSpace ℝ H).symm y
          simp only [real_inner_comm, sub_add_sub_cancel, gt_iff_lt]
          have h_ne : xH ≠ yH := by
            have h_inj : Function.Injective ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
              LinearEquiv.injective _
            intro heq
            have : x = y := h_inj (by simp only [EmbeddingLike.apply_eq_iff_eq]; exact heq)
            exact hxy this
          have h_sub : xH - yH ≠ 0 := sub_ne_zero_of_ne h_ne
          have h_pos : 0 < ‖xH - yH‖ := norm_pos_iff.mpr h_sub
          have h1: ‖xH - yH‖ ^ 2 > 0 := sq_pos_of_pos h_pos
          rw [← real_inner_self_eq_norm_sq] at h1
          simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, gt_iff_lt] at h1
          -- Key point: Use xH and yH instead of the converted forms.
          have h_calc : (⟪xH, xH⟫ - ⟪yH, yH⟫) / 2 < ⟪xH, xH⟫ - ⟪xH, yH⟫ := by
            field_simp
            rw [norm_sub_sq_eq_inner] at h1
            simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
            linarith
          -- Because x and y are obtained from xH and yH through toWeakSpace.
          have h_eq_x : (toWeakSpace ℝ H) xH = x := by simp [xH]
          have h_eq_y : (toWeakSpace ℝ H) yH = y := by simp [yH]
          -- Transform the inner product in the target.
          convert h_calc using 3
          · exact Eq.symm (real_inner_self_eq_norm_sq xH)
          · exact Eq.symm (real_inner_self_eq_norm_sq yH)
          exact Eq.symm (real_inner_self_eq_norm_sq xH)
      simp only [V]
      change f y < c
      simp only [feq, cont_inner_left, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      · refine (add_lt_add_iff_left ?_).mp ?_
        · exact c
        · refine (add_lt_add_iff_left c).mpr ?_
          simp only [toWeakSpace, LinearEquiv.refl_symm, cont_inner_left, WeakSpace.coe_map,
            ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, c, f,
            f2, f1]
          rw [LinearEquiv.refl]
          simp only [LinearMap.id, Equiv.invFun_as_coe, Equiv.refl_symm, Equiv.coe_refl,
            LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id_eq, u]
          simp only [inner_sub_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
          let xH : H := (toWeakSpace ℝ H).symm x
          let yH : H := (toWeakSpace ℝ H).symm y
          simp only [real_inner_comm, sub_add_sub_cancel, gt_iff_lt]
          have h_ne : xH ≠ yH := by
            have h_inj : Function.Injective ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
              LinearEquiv.injective _
            intro heq
            have : x = y := h_inj (by simp only [EmbeddingLike.apply_eq_iff_eq]; exact heq)
            exact hxy this
          have h_sub : xH - yH ≠ 0 := sub_ne_zero_of_ne h_ne
          have h_pos : 0 < ‖xH - yH‖ := norm_pos_iff.mpr h_sub
          have h1: ‖xH - yH‖ ^ 2 > 0 := sq_pos_of_pos h_pos
          rw [← real_inner_self_eq_norm_sq] at h1
          simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, gt_iff_lt] at h1
          -- Key point: Use xH and yH instead of the converted forms.
          have h_calc : ⟪xH, yH⟫ - ⟪yH, yH⟫ < (⟪xH, xH⟫ - ⟪yH, yH⟫) / 2 := by
            field_simp
            rw [norm_sub_sq_eq_inner] at h1
            simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
            linarith
          have h_eq_x : (toWeakSpace ℝ H) xH = x := by simp [xH]
          have h_eq_y : (toWeakSpace ℝ H) yH = y := by simp [yH]
          convert h_calc using 3
          · exact Eq.symm (real_inner_self_eq_norm_sq yH)
          · exact Eq.symm (real_inner_self_eq_norm_sq xH)
          exact Eq.symm (real_inner_self_eq_norm_sq yH)
    have dUV : Disjoint U V := by
      simp only [Disjoint, Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
      intro Z hU hV
      simp only [gt_iff_lt, U, V] at hU hV
      have h_contradiction : ∀ z ∈ Z, False := by
        intro z hz
        have h1 : c < f z := hU hz
        have h2 : f z < c := hV hz
        linarith
      exact Set.subset_eq_empty h_contradiction rfl
    exact ⟨U, Uopen, V, Vopen, xinUV.1, xinUV.2, dUV⟩

end T2Space
