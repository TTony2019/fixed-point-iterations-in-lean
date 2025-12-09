import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.Theory.InnerProductSpace.WeakConverge
import FormalizationFixpointIterations.Theory.InnerProductSpace.Closedness

open WeakDual
-- open Filter WeakDual Metric WeakBilin Topology Function TopologicalSpace

section T2Space

#check Topology.IsEmbedding.t2Space
#check ProperSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂
instance inst_WeakSpace_T2 : T2Space (WeakSpace ℝ H) where
  t2 := by
    simp [Pairwise]
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
      simp [feq, cont_inner_left]
      · refine (Real.add_lt_add_iff_left ?_).mp ?_
        · exact c
        · refine (Real.add_lt_add_iff_left c).mpr ?_
          simp [c, f, f1, cont_inner_left, f2, toWeakSpace]
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
      simp [feq, cont_inner_left]
      · refine (Real.add_lt_add_iff_left ?_).mp ?_
        · exact c
        · refine (Real.add_lt_add_iff_left c).mpr ?_
          simp [c, f, f1, cont_inner_left, f2, toWeakSpace]
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
