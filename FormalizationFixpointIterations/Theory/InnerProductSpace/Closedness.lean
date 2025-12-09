import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Defs.Filter
-- import Mathlib.Logic.Function.Defs
import FormalizationFixpointIterations.Theory.InnerProductSpace.WeakConverge
import FormalizationFixpointIterations.Nonexpansive.Definitions

open WeakBilin Filter Topology Nonexpansive_operator Function

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

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

-- Theorem 3.34 (iii) → (iv)
theorem closed_is_weakly_closed [CompleteSpace H] (s : Set H)
  (hs : Convex ℝ s) (hw : IsClosed s) :
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


-- Theorem 3.34 (iii) → (i)
theorem closed_is_weakly_seq_closed [CompleteSpace H] (s : Set H)
  (hs : Convex ℝ s) (hc : IsClosed s) : IsWeaklySeqClosed s := by
  have hwkclosed := closed_is_weakly_closed s hs hc
  exact weakly_closed_seq_closed s hwkclosed


-- demiclosed 的定义
def DemiclosedAt (D : Set H) (T : H → H) (u : H) : Prop :=
  (h_D_nonempty : D.Nonempty) →
  (h_D_weakly_seq_closed : IsWeaklySeqClosed D) →
  ∀ (x : ℕ → H), (∀ n, x n ∈ D) →
  ∀ (x_lim : H), x_lim ∈ D →
  WeakConverge x x_lim →
  Tendsto (fun n => T (x n)) atTop (𝓝 u) →
  T x_lim = u

def Demiclosed (T : H → H) (D : Set H) : Prop :=
  ∀ u : H, DemiclosedAt D T u


-- Theorem 4.27: Browder's demiclosedness principle
theorem browder_demiclosed_principle [CompleteSpace H]
  {D : Set H}
  {T : H → H}
  (hT_nonexp : NonexpansiveOn T D)
  : Demiclosed (id - T) D := by
  intro u
  intro h_D_nonempty h_D_weakly_seq_closed
  intro x hx_in_D x_lim hx_lim_in_D h_weak_conv h_diff_tendsto
  --取一个弱收敛到x_lim的列x n
  simp at h_diff_tendsto
  have h_norm_bound : ∀ n : ℕ, ‖x_lim - T x_lim - u‖ ^ 2 ≤
    ‖x n - T (x n) - u‖ ^ 2 + 2 * ⟪x n - T (x n) - u, T (x n) - T x_lim⟫
      - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by
        intro n
        calc
          _ = ‖(x_lim - x n) + (x n - T x_lim - u)‖ ^ 2 := by congr 1; abel_nf
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * ⟪x_lim - x n, x n - T x_lim - u⟫ := by
            rw [← real_inner_self_eq_norm_sq]
            simp [← real_inner_self_eq_norm_sq, inner_add_left,
              inner_add_right, real_inner_comm, two_mul]; ring_nf
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * ⟪x_lim - x n, (x n - x_lim) + (x_lim - T x_lim - u)⟫ := by congr 1; abel_nf
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * (⟪x_lim - x n, x n - x_lim⟫ + ⟪x_lim - x n, x_lim - T x_lim - u⟫) := by
              congr 1; rw [inner_add_right]
          _ = ‖x_lim - x n‖ ^ 2 + ‖x n - T x_lim - u‖ ^ 2 +
              2 * (-‖x_lim - x n‖ ^ 2 + ⟪x_lim - x n, x_lim - T x_lim - u⟫) := by
            congr 1; simp; rw [← real_inner_self_eq_norm_sq]
            have : (x n - x_lim) = - (x_lim - x n) := by abel
            rw [this]; rw [inner_neg_right]
          _ = ‖x n - T x_lim - u‖ ^ 2 - ‖x n - x_lim‖ ^ 2
              - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by
            simp [mul_add, ← add_assoc]; ring_nf; simp [add_sub, add_comm]
            congr 3
            · simp; exact norm_sub_rev x_lim (x n)
            · have : - (x n - x_lim) = (x_lim - x n) := by abel
              rw [← this]; rw [inner_neg_left]; ring_nf
          _ = ‖(x n - T (x n) - u) + (T (x n) - T x_lim)‖ ^ 2 - ‖x n - x_lim‖ ^ 2
              - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by congr 1; abel_nf
          _ = ‖x n - T (x n) - u‖ ^ 2 + ‖T (x n) - T x_lim‖ ^ 2 +
              2 * ⟪x n - T (x n) - u, T (x n) - T x_lim⟫ - ‖x n - x_lim‖ ^ 2
              - 2 * ⟪x n - x_lim, x_lim - T x_lim - u⟫ := by
            rw [← real_inner_self_eq_norm_sq]
            simp [← real_inner_self_eq_norm_sq, inner_add_left,
              inner_add_right, real_inner_comm, two_mul]; ring_nf
          _ ≤ _ := by
            have : ‖T (x n) - T x_lim‖ ^ 2 ≤ ‖x n - x_lim‖ ^ 2 := by
              apply sq_le_sq.2; simp
              rw [NonexpansiveOn, LipschitzOnWith] at hT_nonexp
              have := hT_nonexp (hx_in_D n) hx_lim_in_D
              simp [edist_dist] at this; rw [dist_eq_norm, dist_eq_norm] at this; exact this
            linarith

  have h1 : Tendsto (fun n => ‖x n - T (x n) - u‖) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h_diff_tendsto
    obtain ⟨N, hN⟩ := h_diff_tendsto ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN ⊢
    simp at ⊢ hN
    exact hN

  have h2 : Tendsto (fun n => x n - T (x n) - u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h1
    obtain ⟨N, hN⟩ := h1 ε ε_pos
    use N
    intro n hn
    specialize hN n hn
    rw [dist_eq_norm] at hN ⊢
    simp at ⊢ hN
    exact hN

  have h3 : WeakConverge (fun n => x n - x_lim) 0 := by
    rw [weakConverge_iff_inner_converge']
    intro y
    have h4 : Tendsto (fun n => ⟪x n, y⟫) atTop (𝓝 ⟪x_lim, y⟫) := by
      apply (weakConverge_iff_inner_converge x x_lim).1 h_weak_conv
    have h5 : Tendsto (fun (n : ℕ) => ⟪x_lim, y⟫) atTop (𝓝 ⟪x_lim, y⟫) := tendsto_const_nhds
    have h_diff : Tendsto (fun n => ⟪x n, y⟫ - ⟪x_lim, y⟫) atTop (𝓝 (⟪x_lim, y⟫ - ⟪x_lim, y⟫)) :=
      Tendsto.sub h4 h5
    convert h_diff using 1
    ext n; simp; rw [inner_sub_left]; ring_nf

  have h4 : WeakConverge (fun n => x n - T (x n)) u := by
    rw [weakConverge_iff_inner_converge']
    intro y
    by_cases hy : y = 0
    · -- 情况1：y = 0
      simp [hy]
    · have h2' : Tendsto (fun n => (x n - T (x n)) - u) atTop (𝓝 0) := by
        convert h2 using 1
      -- 内积的连续性
      have h_inner : Tendsto (fun n => ⟪(x n - T (x n)) - u, y⟫) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε ε_pos
        rw [Metric.tendsto_atTop] at h2'
        obtain ⟨N, hN⟩ := h2' (ε / ‖y‖) (by positivity)
        use N
        intro n hn
        specialize hN n hn
        simp [dist_eq_norm] at hN ⊢
        by_cases hy : y = 0
        · simp [hy]; linarith
        · calc
            |⟪(x n - T (x n)) - u, y⟫|
                ≤ ‖(x n - T (x n)) - u‖ * ‖y‖ := by apply abs_real_inner_le_norm _ _
              _ < (ε / ‖y‖) * ‖y‖ := by gcongr
              _ = ε := by field_simp [ne_of_gt (norm_pos_iff.mpr hy)]
      exact h_inner

  have h4 : WeakConverge (fun n => T (x n) - x n) (- u) := by
    rw [weakConverge_iff_inner_converge'] at h4 ⊢
    intro y
    specialize h4 y
    have := Tendsto.neg h4
    convert this using 1
    · ext n; simp; rw [← inner_neg_left]; simp [inner_sub_left, inner_add_left]; ring_nf
    simp

  have h5 : WeakConverge (fun n => T (x n) - x n + (x n - x_lim)
    + (x_lim - T x_lim)) (x_lim - T x_lim - u) := by
    rw [weakConverge_iff_inner_converge]
    intro y
    -- 分解内积
    have h4_inner : Tendsto (fun n => ⟪T (x n) - x n, y⟫) atTop (𝓝 ⟪-u, y⟫) := by
      apply (weakConverge_iff_inner_converge _ _).1 h4
    have h3_inner : Tendsto (fun n => ⟪x n - x_lim, y⟫) atTop (𝓝 ⟪(0 : H), y⟫) := by
      apply (weakConverge_iff_inner_converge _ _).1 h3
    have h_const : Tendsto (fun n : ℕ  => ⟪x_lim - T x_lim, y⟫) atTop (𝓝 ⟪x_lim - T x_lim, y⟫) :=
      tendsto_const_nhds

    -- 利用内积的加法性
    have h_combined : Tendsto (fun n =>
      ⟪T (x n) - x n, y⟫ + ⟪x n - x_lim, y⟫ + ⟪x_lim - T x_lim, y⟫)
      atTop (𝓝 (⟪-u, y⟫ + ⟪(0 : H), y⟫ + ⟪x_lim - T x_lim, y⟫)) := by
      apply Tendsto.add
      · apply Tendsto.add h4_inner h3_inner
      · exact h_const

    -- 转换为目标形式
    convert h_combined using 1
    · ext n; simp only [inner_add_left]
    · congr 1; simp [inner_sub_left]; abel

  have h5 : WeakConverge (fun n => T (x n) - T x_lim) (x_lim - T x_lim - u) := by
    convert h5 using 1; ext n; abel_nf

  have h1' :  Tendsto (fun n ↦ ‖x n - T (x n) - u‖ ^ 2) atTop (𝓝 0) := by
    apply Tendsto.pow at h1; specialize h1 2; convert h1; simp

  have h6 : Tendsto (fun n ↦ 2 * inner ℝ (x n - x_lim) (x_lim - T x_lim - u)) atTop (𝓝 0) := by
    have := (weakConverge_iff_inner_converge (fun n => x n - x_lim) 0).1 h3 (x_lim - T x_lim - u)
    simp only [inner_zero_left] at this; apply Tendsto.const_mul 2 at this; convert this; simp

  have h7 : Tendsto (fun n ↦ inner ℝ (T (x n) - T x_lim) (x n - T (x n) - u))
    atTop (𝓝 (inner ℝ 0 (x_lim - T x_lim - u))) := by
    let a := fun n => x n - T (x n) - u; let b := fun n => T (x n) - T x_lim
    have h_a : Tendsto a atTop (𝓝 0) := h2
    have h_b : WeakConverge b (x_lim - T x_lim - u) := h5
    rw [real_inner_comm]; apply wkconv_conv_ledsto_conv
    · exact h_b
    · exact h_a

  have h7' : Tendsto (fun n ↦ inner ℝ (T (x n) - T x_lim) (x n - T (x n) - u)) atTop (𝓝 0) := by
    convert h7; simp

  have h8 : Tendsto (fun n ↦ ‖x n - T (x n) - u‖ ^ 2 + (2 * inner ℝ (T (x n) - T x_lim)
    (x n - T (x n) - u) - 2 * inner ℝ (x n - x_lim) (x_lim - T x_lim - u))) atTop (𝓝 (0 + (0 - 0)))
      := by
        apply Tendsto.add
        · exact h1'
        · apply Tendsto.sub
          · apply Tendsto.const_mul 2 at h7'; convert h7'; simp
          · exact h6

  have h8' : Tendsto (fun n ↦ ‖x n - T (x n) - u‖ ^ 2 + 2 * inner ℝ (x n - T (x n) - u)
    (T (x n) - T x_lim) - 2 * inner ℝ (x n - x_lim) (x_lim - T x_lim - u)) atTop (𝓝 0) := by
      convert h8 using 1
      · funext n; ring_nf; rw [add_sub]; rw [real_inner_comm]; ring
      · simp

  have h9 : ∀ ε > 0, ‖x_lim - T x_lim - u‖ ^ 2 < ε := by
    intro ε ε_pos
    rw [Metric.tendsto_atTop] at h8'
    obtain ⟨N, hN⟩ := h8' (ε) ε_pos
    specialize hN N (le_refl N)
    simp [dist_eq_norm] at hN
    specialize h_norm_bound N
    calc
      _ ≤ ‖x N - T (x N) - u‖ ^ 2 + 2 * ⟪x N - T (x N) - u, T (x N) - T x_lim⟫
          - 2 * ⟪x N - x_lim, x_lim - T x_lim - u⟫ := h_norm_bound
      _ < ε := by exact lt_of_abs_lt hN

  have h_final : ‖x_lim - T x_lim - u‖ ^ 2 ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε ε_pos
    specialize h9 ε ε_pos
    linarith
  have h_nonneg : 0 ≤ ‖x_lim - T x_lim - u‖ ^ 2 := by
    apply pow_two_nonneg
  have : ‖x_lim - T x_lim - u‖ ^ 2 = 0 := by
    apply le_antisymm h_final h_nonneg
  have : ‖x_lim - T x_lim - u‖ = 0 := by
    exact pow_eq_zero this
  have : x_lim - T x_lim - u = 0 := by
    exact norm_eq_zero.mp this
  rw [sub_eq_zero] at this
  exact this


-- Corollary 4.28: 弱收敛且误差趋零蕴含固定点
lemma corollary_4_28 [CompleteSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) (x : ℕ → H) (h_x_in_D : ∀ n, x n ∈ D)
  (p : H) (h_p_in_D : p ∈ D) (h_weak_conv : WeakConverge x p)
  (h_error_zero : Tendsto (fun n => x n - T (x n)) atTop (𝓝 0)) : p ∈ Fix T := by
  have h_wk_seq_closed : IsWeaklySeqClosed D := by
    apply closed_is_weakly_seq_closed; exact hD_convex; exact hD_closed
  have h_demiclosed := browder_demiclosed_principle hT_nonexp
  have h_p_minus_Tp_zero : p - T p = 0 := by
    apply h_demiclosed; exact hD_nonempty; exact h_wk_seq_closed; exact h_x_in_D
    exact h_p_in_D; exact h_weak_conv; exact h_error_zero
  simp [Fix, IsFixedPt]; simp [sub_eq_zero] at h_p_minus_Tp_zero
  exact id (Eq.symm h_p_minus_Tp_zero)
