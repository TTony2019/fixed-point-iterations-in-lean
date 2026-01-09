/-
Copyright (c) 2025 Jian Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jian Yu
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.Nonexpansive.Definitions
import FormalizationFixpointIterations.Theory.InnerProductSpace.Compact

open Set Filter Topology TopologicalSpace Metric BigOperators Finset Function Nonexpansive_operator

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
The definition of Fejér monotonicity. The sequence `x` is Fejér monotone with respect to the set `C` if
`∀ y ∈ C, ∀ n, ‖x (n + 1) - y‖ ≤ ‖x n - y‖`
-/
def IsFejerMonotone (x : ℕ → H) (C : Set H) : Prop :=
  ∀ y ∈ C, ∀ n, ‖x (n + 1) - y‖ ≤ ‖x n - y‖

/--
The definition of having a weakly convergent subsequence. A sequence `x` has a weakly convergent subsequence to `p` if
there exists a strictly monotone function `φ : ℕ → ℕ` such that `WeakConverge (fun n => (x (φ n))) p`.
-/
def HasWeakSubseq (p : H) (x : ℕ → H):=
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    WeakConverge (fun n => (x (φ n))) p

/--
Converts the definition of convergence of a real sequence `u` to `x0` into the ε-N form
-/
lemma Converge_iff (u : ℕ → ℝ) (x0 : ℝ) :
Tendsto u atTop (𝓝 x0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x0 - ε) (x0 + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x0)]
  simp

lemma HasWeakSubseq_of_WeakConverge (x : ℕ → H) (p : H) (hconv : WeakConverge x p) :
  HasWeakSubseq p x := by
  use id
  constructor
  · exact fun(x y hxy) => hxy
  exact hconv

/--
If ⟪x n, p⟫ converges, then ⟪x (φ n), p⟫ also converges.
-/
lemma WeakConverge_Subseq_inner {x : ℕ → H} {p : H} {φ : ℕ → ℕ} (hφ : StrictMono φ) (l : ℝ)
(hconv : Tendsto (fun n => ⟪x n, p⟫) atTop (𝓝 l)) :
  Tendsto (fun n =>⟪x (φ n), p⟫) atTop (𝓝 l) := by
  apply Filter.Tendsto.comp hconv
  exact StrictMono.tendsto_atTop hφ

/--
Corollary 2.15: for x,y ∈ H and α ∈ ℝ
 `‖αx + (1-α)y‖^2 + α(1-α)‖x - y‖^2 = α‖x‖^2 + (1-α)‖y‖^2`
-/
lemma convex_combination_norm_sq_identity
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (x y : H) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 = α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (α • x + (1 - α) • y), ← real_inner_self_eq_norm_sq (x - y),
    ← real_inner_self_eq_norm_sq x, ← real_inner_self_eq_norm_sq y]
  have h1 : inner ℝ (α • x + (1 - α) • y) (α • x + (1 - α) • y) =
      α ^ 2 * inner ℝ x x + 2 * α * (1 - α) * inner ℝ x y + (1 - α) ^ 2 * inner ℝ y y := by
    simp only [inner_add_left, inner_add_right, real_inner_comm]
    simp only [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp
    ring
  have h2 : inner ℝ (x - y) (x - y) = inner ℝ x x - 2 * inner ℝ x y + inner ℝ y y := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  rw [h1, h2]
  ring
alias Corollary_2_15 := convex_combination_norm_sq_identity

/--
Given a sequence `x : ℕ → H` and a set `U : Set H`, this lemma shows that if `x n ∉ U` occurs frequently (i.e., for infinitely many `n`), then there exists a strictly increasing subsequence of indices `l : ℕ → ℕ` such that for every `n`, `x (l n) ∉ U`.
This is useful for converting the "frequently" condition into the existence of a subsequence with the desired property, often used in proofs by contradiction or in constructing counterexamples.
-/
lemma frequently_subseq {x : ℕ → H} {U : Set H}
 (h_fre : ∃ᶠ (n : ℕ) in atTop, x n ∉ U) :
  ∃ (l : ℕ → ℕ), StrictMono l ∧ ∀ n, x (l n) ∉ U := by
  have h_freq : ∀ (N : ℕ), ∃ n ≥ N, x n ∉ U :=
    by rwa [frequently_atTop] at h_fre
  choose g hg_ge hg_not_mem using h_freq
  -- Recursive construction of a strictly increasing sequence l
  let l : ℕ → ℕ:=
    fun k =>
      Nat.recOn k
        (g 0) -- l 0 : pick n ≥ 0 with x n ∉ U
        (fun k' lk => g (lk + 1)) -- Given lk, select the next index greater than lk
  have hl_mono : StrictMono l := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    simp only [l]   --  l (n+1) = g (l n + 1)
    have h1 : l n < l n + 1 := Nat.lt_succ_self _
    have h2 : l n + 1 ≤ g (l n + 1) := hg_ge (l n + 1)
    exact lt_of_lt_of_le h1 h2
  have hl_not_mem : ∀ n, x (l n) ∉ U := by
    intro n
    induction n with
    | zero => simpa [l] using hg_not_mem 0
    | succ k hk => simpa [l, hk] using hg_not_mem (l k + 1)
  exact ⟨l, hl_mono, hl_not_mem⟩

/--
The conversion lemma between the `‖x_n‖ ≤ M` and `Bornology.IsBounded` conditions
-/
lemma bounded_to_IsBounded (x : ℕ → H) (h_bounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
: Bornology.IsBounded <| Set.range (fun n => ‖x n‖) := by
  rcases h_bounded with ⟨M, hM⟩
  rw [isBounded_iff_forall_norm_le]
  use M
  rintro y ⟨n, rfl⟩
  simpa using hM n

--An auxiliary process used to prove 2.46, show the limit of a convergent sequence within a closed set remains within the set.
lemma bounded_not_mem_subseq [SeparableSpace H] [CompleteSpace H] (x : ℕ → H) {V : Set H} (h_bounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
(hV_open : @IsOpen (WeakSpace ℝ H) _ V) (h_not_mem : ∀ (n : ℕ), x (n) ∉ V) :
∃ q0:H ,q0∈ Vᶜ∧ ∃ (φ : ℕ → ℕ), StrictMono φ ∧  WeakConverge (fun n => (x (φ n))) q0 := by
  have hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖) := bounded_to_IsBounded x h_bounded
  rcases h_bounded with ⟨M,h_bounded⟩
  have h_subseq :=bounded_seq_has_weakly_converge_subseq_separable x hx
  rcases h_subseq with ⟨q0, k, hk, h_k_conv⟩
  have hq0_notin_V : q0 ∈ Vᶜ := by
    have h1 : range (x∘k) ⊆ Vᶜ := by
      intro y hy
      simp only [Set.range] at hy
      obtain ⟨n, rfl⟩ := hy
      apply h_not_mem
    have h2 := isClosed_compl_iff.mpr hV_open --Note that here is weakly closed
    have h2_seqWeaklyClosed := h2.isSeqClosed
    -- refine (mem_compl_iff V q0).mpr ?_
    simp only [IsSeqClosed] at h2_seqWeaklyClosed
    refine h2_seqWeaklyClosed ?_ h_k_conv
    intro n
    apply h_not_mem
  exact ⟨q0, hq0_notin_V , k,hk,h_k_conv⟩

/--
Lemma 2.46
if sequence `x` is bounded and possesses at most one weak sequential cluster point, then `x` weakly converges to some point `p0` in `H`.
-/
lemma WeakConv_of_bounded_clusterptUnique [SeparableSpace H] [CompleteSpace H] (x : ℕ → H) (h_bounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
(h_atmost_one_cluster : ∀ p q : H,  HasWeakSubseq p x → HasWeakSubseq q x  → p = q) : ∃ p0 : H, WeakConverge x p0 := by
  have hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖) := bounded_to_IsBounded x h_bounded
  have  ⟨p0, k, hk, h_k_conv⟩ :=bounded_seq_has_weakly_converge_subseq_separable x hx
  use p0
  by_contra h_not_conv  --proof by contradiction
  simp only [WeakConverge] at h_not_conv
  rw [not_tendsto_iff_exists_frequently_notMem] at h_not_conv
  rcases h_not_conv with ⟨U, hU_nbds, h_fre⟩
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := (mem_nhds_iff.mp hU_nbds) --Obtain the weakly open set V from the neighborhood U
  have h_fre_V : ∃ᶠ n in atTop, x n ∉ V := h_fre.mono (by intro n hnU hV; exact hnU (hVsub hV))
  rcases frequently_subseq h_fre_V with ⟨l, hl_strict_mono, hl_not_mem⟩
  have h_bounded_l:∃ M, ∀ (n : ℕ), ‖(x ∘ l) n‖ ≤ M := by
    rcases h_bounded with ⟨M,h_bounded⟩
    exact ⟨ M, (fun n => h_bounded (l n))⟩
  have h1: ∃ q0:H , q0∈ Vᶜ∧  ∃ (φ : ℕ → ℕ), StrictMono φ ∧  WeakConverge (fun n => ((x∘ l) (φ n))) q0  :=
  bounded_not_mem_subseq (x ∘ l) h_bounded_l hVopen hl_not_mem --use the auxiliary proof above
  rcases h1 with ⟨q0,hq0, φ, hφ_strict_mono,h_conv_phi⟩
  let j:=l ∘ φ
  have hj_strict_mono :=StrictMono.comp hl_strict_mono hφ_strict_mono
  have h_sub_p0:HasWeakSubseq p0 x:= ⟨k, hk,h_k_conv⟩
  have h_sub_q0:HasWeakSubseq q0 x:= ⟨j, hj_strict_mono, h_conv_phi⟩
  have p0_eq_q0: p0=q0 := h_atmost_one_cluster p0 q0 h_sub_p0 h_sub_q0
  rw[p0_eq_q0] at hVmem
  exact hq0 hVmem
alias Lemma_2_46_backword := WeakConv_of_bounded_clusterptUnique

/--
equation (2.32):`2*⟪x n,p-q⟫ =‖x n - q‖^2-‖x n - p‖^2+‖p‖^2-‖q‖^2`
-/
lemma inner_sub_eq_norm_sub (x : ℕ → H) (p q : H) :
  ∀ n : ℕ, 2 * ⟪x n, p - q⟫ = ‖x n - q‖ ^ 2 - ‖x n - p‖ ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
  intro n
  symm
  calc
    ‖x n - q‖ ^ 2 - ‖x n - p‖ ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2
      = ⟪x n - q, x n - q⟫ - ⟪x n - p, x n - p⟫ + ⟪p, p⟫ - ⟪q, q⟫ := by
        rw [real_inner_self_eq_norm_sq (x n - q), real_inner_self_eq_norm_sq (x n - p),
          real_inner_self_eq_norm_sq p, real_inner_self_eq_norm_sq q]
    _ = 2 * ⟪x n, p - q⟫ := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
/--
Convert equation (2.32) to limit form and show limit ⟪x n,p-q⟫ exists.
-/
lemma inner_sub_lim_exists (x : ℕ → H) (p q : H) (lim_p lim_q : ℝ) (norm_p_2 : Tendsto (fun n ↦ ‖x n - p‖ ^ 2) atTop (𝓝 (lim_p ^ 2)))
(norm_q_2 : Tendsto (fun n ↦ ‖x n - q‖ ^ 2) atTop (𝓝 (lim_q ^ 2))) :
∃ l: ℝ ,Tendsto (fun n => ⟪x n,p-q⟫) atTop (𝓝 (l)) :=by
  use 1/2*((lim_q ^ 2)-(lim_p ^ 2)+‖p‖^2-‖q‖^2)
  have h2 : Tendsto (fun n => ‖x n -q‖ ^2-‖ x n -p‖ ^2+‖p‖^2-‖q‖^2) atTop
    (𝓝 ( (lim_q ^ 2)-(lim_p ^ 2)+‖p‖^2-‖q‖^2)) := by
    apply Tendsto.sub
    · apply Tendsto.add
      · apply Tendsto.sub
        · exact norm_q_2
        · exact norm_p_2
      · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have h1 : Tendsto (fun n => 2*⟪x n,p-q⟫) atTop (𝓝 ((lim_q ^ 2)-(lim_p ^ 2)+‖p‖^2-‖q‖^2)) :=by
    apply Tendsto.congr (fun n => (inner_sub_eq_norm_sub x p q n).symm) h2
  have :=h1.const_mul (1/2)
  simpa using this

/--
Lemma 2.47 : Suppose for every `a ∈ C`,  `‖x n - a‖` converges and that
every weak sequential cluster point of `x` belongs to `C`. Then `x` converges weakly to a point `p0` in `C`.
-/
lemma WeakConv_of_sub_norm_of_clusterpt_in [SeparableSpace H] [CompleteSpace H] (C : Set H) (h_C_nonempty : C.Nonempty) (x : ℕ → H)
(h_converge : ∀ a ∈ C, ∃ lim_A : ℝ, Tendsto (fun n ↦ ‖x n - a‖) atTop (𝓝 lim_A))
(h_weak_cluster_in : ∀ p : H,  HasWeakSubseq p x → p ∈ C) : ∃ p0 ∈ C, WeakConverge x p0 := by
  have h_bounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M := by
    rcases h_C_nonempty with ⟨y0 ,hy0⟩
    rcases h_converge y0 hy0 with ⟨lim_A, h_tendsto⟩
    rcases Filter.Tendsto.bddAbove_range h_tendsto with ⟨M0, hM0⟩
    let M := ‖y0‖ + M0
    use M
    intro n
    have h1 : ‖x n - y0‖ ≤ M0 := hM0 (Set.mem_range_self n)
    have h2 : ‖x n‖ ≤ ‖x n - y0‖ + ‖y0‖ := by
      apply norm_le_norm_sub_add
    linarith
  have h_atmost_one_cluster : ∀ p q : H,  HasWeakSubseq p x → HasWeakSubseq q x → p = q := by
    intro p q h_cluster_p h_cluster_q
    have hp_in_C : p ∈ C := h_weak_cluster_in p h_cluster_p
    have hq_in_C : q ∈ C := h_weak_cluster_in q h_cluster_q
    rcases h_converge p hp_in_C with ⟨lim_p, norm_tendsto_p⟩
    have norm_p_2:=norm_tendsto_p.pow 2  --‖x n - p‖^2 also converges
    rcases h_converge q hq_in_C with ⟨lim_q, norm_tendsto_q⟩
    have norm_q_2:=norm_tendsto_q.pow 2
    rcases h_cluster_p with ⟨k, hk, hconv_p⟩ --k and l are subsequence indices
    rcases h_cluster_q with ⟨l, hl, hconv_q⟩
    rw [weakConverge_iff_inner_converge (fun n ↦ x (k n)) p] at hconv_p
    rw [weakConverge_iff_inner_converge (fun n ↦ x (l n)) q] at hconv_q
    rcases inner_sub_lim_exists x p q lim_p lim_q norm_p_2 norm_q_2 with ⟨L, tendsto_L⟩ --用上面命题
    have hL1 :=WeakConverge_Subseq_inner hk L tendsto_L --subsequence also converges
    have hL2 :=WeakConverge_Subseq_inner hl L tendsto_L
    have h1:=tendsto_nhds_unique (hconv_p (p-q)) hL1 --Uniqueness of the limit
    have h2:=tendsto_nhds_unique (hconv_q (p-q)) hL2
    have h3 : inner ℝ (p - q) (p - q) = 0 := by
      rw [inner_sub_left, h1, h2, sub_self]
    rwa [inner_self_eq_zero,sub_eq_zero] at h3
  obtain ⟨p0, hp0 ⟩  := WeakConv_of_bounded_clusterptUnique x h_bounded h_atmost_one_cluster
  have hp0_in_C : p0 ∈ C := h_weak_cluster_in p0 (HasWeakSubseq_of_WeakConverge x p0 hp0)
  exact ⟨p0, hp0_in_C, hp0⟩
alias Lemma_2_47 := WeakConv_of_sub_norm_of_clusterpt_in

/--
If the sequence `x` is Fejér monotone with respect to a nonempty set `C`, then
(i) `x` is bounded.
(ii) For every point `a` in `C`, the sequence `‖x n - a‖` converges.
-/
lemma bounded_converge_of_Fejermonotone (C : Set H) (h_C_nonempty : C.Nonempty) (x : ℕ → H)
(h_fejer : IsFejerMonotone x C) :
(∃ M:ℝ , ∀ n, ‖x n‖ ≤ M)
∧ (∀ a ∈ C, ∃ lim_inf : ℝ, Tendsto (fun n ↦ ‖x n - a‖) atTop (𝓝 lim_inf)) := by
  rcases h_C_nonempty with ⟨y0, hy0⟩
  --Prove boundedness
  let M := ‖y0‖ + ‖x 0 - y0‖
  constructor
  · use M
    · intro n
      have h1 : ‖x n - y0‖ ≤ ‖x 0 - y0‖ := by
        induction n with
        | zero => simp
        | succ i hi => apply le_trans (h_fejer y0 hy0 i) hi
      have h2 : ‖x n‖ ≤ ‖x n - y0‖ + ‖y0‖ := by
        apply norm_le_norm_sub_add
      linarith
  --Prove the existence of the limit by using the Monotone Convergence Theorem
  intro a ha
  have h_decreasing : ∀ n, ‖x (n + 1) - a‖ ≤ ‖x n - a‖ := by
    intro n
    apply h_fejer a ha
  have h_bounded_below : ∀ n, 0 ≤ ‖x n - a‖ := by
    intro n
    apply norm_nonneg
  use ⨅ n, ‖x n - a‖
  have h_lub := IsGLB (Set.range (fun n ↦ ‖x n - a‖)) (⨅ n, ‖x n - a‖)
  apply tendsto_atTop_isGLB
  · apply antitone_nat_of_succ_le h_decreasing
  apply isGLB_ciInf
  use 0  --0 ∈ lowerBounds (Set.range fun n ↦ ‖x n - a‖)
  rintro y ⟨n, rfl⟩
  apply h_bounded_below n
alias Prop_5_04_i_ii := bounded_converge_of_Fejermonotone

/--
Theorem 5.5
If the sequence `x` is Fejér monotone with respect to a nonempty set `C`, and if every weak sequential cluster point of `x` belongs to `C`, then
`x` weakly converges to some point `p0` in `C`.
-/
theorem WeakConv_of_Fejermonotone_of_clusterpt_in [SeparableSpace H] [CompleteSpace H] (C : Set H) (h_C_nonempty : C.Nonempty) (x : ℕ → H)
(h_fejer : IsFejerMonotone x C) (h_weak_cluster_in : ∀ p : H, HasWeakSubseq p x → p ∈ C):
∃ p0 ∈ C, WeakConverge x p0 := by
  have h_converge := (bounded_converge_of_Fejermonotone C h_C_nonempty x h_fejer).2
  apply WeakConv_of_sub_norm_of_clusterpt_in C h_C_nonempty x h_converge h_weak_cluster_in
alias Theorem_5_05 := WeakConv_of_Fejermonotone_of_clusterpt_in
