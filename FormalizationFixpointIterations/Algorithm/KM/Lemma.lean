/-
Copyright (c) 2025 Jian Yu, Yifan Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jian Yu, Yifan Bai
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.Nonexpansive.Definitions
import FormalizationFixpointIterations.InnerProductSpace.Compact

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
def IsFejerMonotone (x : ℕ → H) (D : Set H) : Prop :=
  ∀ y ∈ D, ∀ n, ‖x (n + 1) - y‖ ≤ ‖x n - y‖

/--
Converts the definition of convergence of a real sequence `u` to `x0` into the ε-N form
-/
lemma Converge_iff (u : ℕ → ℝ) (x0 : ℝ) :
Tendsto u atTop (𝓝 x0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x0 - ε) (x0 + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x0)]
  simp

lemma HasWeakSubseq_of_WeakConverge (x : ℕ → H) (p : H) (hconv : WeakConverge x p) :
  WeakSubseqLimitPt p x := by
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
    simp only [IsSeqClosed] at h2_seqWeaklyClosed
    refine h2_seqWeaklyClosed ?_ h_k_conv
    intro n
    apply h_not_mem
  exact ⟨q0, hq0_notin_V , k,hk,h_k_conv⟩

/--
Lemma 2.46
if sequence `x` is bounded and possesses at most one weak sequential cluster point, then `x` weakly converges to some point `p0` in `H`.
-/
lemma WeakConv_of_bounded_clusterptUnique [SeparableSpace H] [CompleteSpace H] (x : ℕ → H) (hb : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
(hc : ∀ p q : H,  WeakSubseqLimitPt p x → WeakSubseqLimitPt q x  → p = q) : ∃ p0 : H, WeakConverge x p0 := by
  have hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖) := bounded_to_IsBounded x hb
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
    rcases hb with ⟨M,hb⟩
    exact ⟨ M, (fun n => hb (l n))⟩
  have h1: ∃ q0:H , q0∈ Vᶜ∧  ∃ (φ : ℕ → ℕ), StrictMono φ ∧  WeakConverge (fun n => ((x∘ l) (φ n))) q0  :=
  bounded_not_mem_subseq (x ∘ l) h_bounded_l hVopen hl_not_mem --use the auxiliary proof above
  rcases h1 with ⟨q0,hq0, φ, hφ_strict_mono,h_conv_phi⟩
  let j:=l ∘ φ
  have hj_strict_mono :=StrictMono.comp hl_strict_mono hφ_strict_mono
  have h_sub_p0:WeakSubseqLimitPt p0 x:= ⟨k, hk,h_k_conv⟩
  have h_sub_q0:WeakSubseqLimitPt q0 x:= ⟨j, hj_strict_mono, h_conv_phi⟩
  have p0_eq_q0: p0=q0 := hc p0 q0 h_sub_p0 h_sub_q0
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
(h_weak_cluster_in : ∀ p : H,  WeakSubseqLimitPt p x → p ∈ C) : ∃ p0 ∈ C, WeakConverge x p0 := by
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
  have h_atmost_one_cluster : ∀ p q : H,  WeakSubseqLimitPt p x → WeakSubseqLimitPt q x → p = q := by
    intro p q h_cluster_p h_cluster_q
    have hp_in_C : p ∈ C := h_weak_cluster_in p h_cluster_p
    have hq_in_C : q ∈ C := h_weak_cluster_in q h_cluster_q
    rcases h_converge p hp_in_C with ⟨lim_p, norm_tendsto_p⟩
    have norm_p_2:=norm_tendsto_p.pow 2  --‖x n - p‖^2 also converges
    rcases h_converge q hq_in_C with ⟨lim_q, norm_tendsto_q⟩
    have norm_q_2:=norm_tendsto_q.pow 2
    rcases h_cluster_p with ⟨k, hk, hconv_p⟩ --k and l are subsequence indices
    rcases h_cluster_q with ⟨l, hl, hconv_q⟩
    have heq1 : (fun n ↦ x (k n))  = x ∘ k := by
      ext n; simp
    have heq2 : (fun n ↦ x (l n))  = x ∘ l := by
      ext n; simp
    rw [← heq1, weakConverge_iff_inner_converge (fun n ↦ x (k n)) p] at hconv_p
    rw [← heq2, weakConverge_iff_inner_converge (fun n ↦ x (l n)) q] at hconv_q
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
Proposition 5.4.i
If the sequence `x` is Fejér monotone with respect to a nonempty set `C`, then (i) `x` is bounded.
-/
theorem Fejermono_bounded (D : Set H) (hD : D.Nonempty) (x : ℕ → H)
  (hx : IsFejerMonotone x D) : ∃ M:ℝ , ∀ n, ‖x n‖ ≤ M := by
  rcases hD with ⟨y0, hy0⟩
  --Prove boundedness
  let M := ‖y0‖ + ‖x 0 - y0‖
  use M; intro n
  have h1 : ‖x n - y0‖ ≤ ‖x 0 - y0‖ := by
    induction n with
    | zero => simp
    | succ i hi => apply le_trans (hx y0 hy0 i) hi
  have h2 : ‖x n‖ ≤ ‖x n - y0‖ + ‖y0‖ := by apply norm_le_norm_sub_add
  linarith
alias Prop_5_04_i := Fejermono_bounded

/--
Proposition 5.4.ii
If the sequence `x` is Fejér monotone with respect to a nonempty set `C`,
then for every point `a` in `C`, the sequence `‖x n - a‖` converges.
-/
theorem Fejermono_convergent (D : Set H) (x : ℕ → H) (h : IsFejerMonotone x D) :
  ∀ a ∈ D, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - a‖) atTop (𝓝 l) := by
  intro a ha
  have h_decreasing : ∀ n, ‖x (n + 1) - a‖ ≤ ‖x n - a‖ := by
    intro n
    apply h a ha
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
alias Prop_5_04_ii := Fejermono_convergent

/--
Theorem 5.5
If the sequence `x` is Fejér monotone with respect to a nonempty set `C`, and if every weak subsequential limit point of `x` belongs to `C`, then
`x` weakly converges to some point `p0` in `C`.
-/
theorem WeakConv_of_Fejermonotone_of_clusterpt_in [SeparableSpace H] [CompleteSpace H] (D : Set H) (hD : D.Nonempty) (x : ℕ → H)
(hx : IsFejerMonotone x D) (hw : ∀ p : H, WeakSubseqLimitPt p x → p ∈ D):
  ∃ p0 ∈ D, WeakConverge x p0 := by
  have h_converge : ∀ a ∈ D, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - a‖) atTop (𝓝 l) :=
    Fejermono_convergent D x hx
  exact WeakConv_of_sub_norm_of_clusterpt_in D hD x h_converge hw
alias Theorem_5_05 := WeakConv_of_Fejermonotone_of_clusterpt_in


/--
Definition 4.33 (set version): `T` is `α`-averaged on `D` if `α ∈ (0,1)` and
there exists a nonexpansive map `R` on `D` such that
`T x = (1 - α) x + α R x` for all `x ∈ D`.
-/
def AveragedOn (T : H → H) (D : Set H) (α : ℝ) : Prop :=
  α ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ R : H → H, NonexpansiveOn R D ∧
      ∀ ⦃x : H⦄, x ∈ D → T x = (1 - α) • x + α • R x

/--
Definition 4.33 (global version): `T` is `α`-averaged on the whole space.
-/
def Averaged (T : H → H) (α : ℝ) : Prop :=
  AveragedOn T Set.univ α

/--
If `u n → +∞` and `c > 0`, then `c * u n → +∞`.
-/
lemma tendsto_atTop_atTop_const_mul {u : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
  (hu : Tendsto u atTop atTop) :
  Tendsto (fun n => c * u n) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rcases (Filter.tendsto_atTop_atTop.mp hu) (b / c) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h1 : b / c ≤ u n := hN n hn
  have h2 : c * (b / c) ≤ c * u n := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
  have hb : b = c * (b / c) := by
    field_simp [hc.ne']
  linarith

/--
From the averaged representation with `α ≠ 0`, fixed points of `T` and `R` coincide.
-/
lemma fix_eq_of_averaged_repr (T R : H → H) (α : ℝ) (hα_ne : α ≠ 0)
  (hrepr : ∀ x : H, T x = (1 - α) • x + α • R x) :
  Fix T = Fix R := by
  ext x
  constructor
  · intro hxT
    have hxT' : T x = x := by
      simpa [Fix, IsFixedPt] using hxT
    have hdiff : T x - x = α • (R x - x) := by
      rw [hrepr x]
      simp [smul_sub, sub_smul, one_smul]
      abel_nf
    have hzero : α • (R x - x) = 0 := by
      rw [← hdiff, hxT']
      simp
    rcases smul_eq_zero.mp hzero with hα0 | hRx0
    · exact (hα_ne hα0).elim
    · have hxR' : R x = x := by
        simpa [sub_eq_zero] using hRx0
      simpa [Fix, IsFixedPt] using hxR'
  · intro hxR
    have hxR' : R x = x := by
      simpa [Fix, IsFixedPt] using hxR
    have hxT' : T x = x := by
      calc
        T x = (1 - α) • x + α • R x := hrepr x
        _ = (1 - α) • x + α • x := by simp [hxR']
        _ = ((1 - α) + α) • x := by rw [add_smul]
        _ = (1 : ℝ) • x := by
          congr 1
          ring
        _ = x := by simp
    simpa [Fix, IsFixedPt] using hxT'

/--
A global nonexpansive map is nonexpansive on `univ`.
-/
lemma nonexpansiveOn_univ_of_nonexpansive {T : H → H} (hT : Nonexpansive T) :
  NonexpansiveOn T (Set.univ : Set H) := by
  intro x hx y hy
  simpa using hT x y

/--
Lemma 2.17(ii)-style identity.
-/
lemma lemma_2_17_ii (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq x,
    ← real_inner_self_eq_norm_sq ((2 : ℝ) • y - x),
    ← real_inner_self_eq_norm_sq (x - y),
    ← real_inner_self_eq_norm_sq y]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, real_inner_comm]
  simp
  ring

/--
Proposition 4.4 (i)-(iii), global-space version.

`T` is firmly nonexpansive, `Id - T` is firmly nonexpansive, and `2T - Id`
is nonexpansive are equivalent characterizations.
-/
theorem proposition_4_4_i_ii_iii {T : H → H} :
    (Firmly_Nonexpansive T ↔ Firmly_Nonexpansive (fun x => x - T x)) ∧
    (Firmly_Nonexpansive T ↔ Nonexpansive (fun x => (2 : ℝ) • T x - x)) ∧
    (Firmly_Nonexpansive (fun x => x - T x) ↔
      Nonexpansive (fun x => (2 : ℝ) • T x - x)) := by
  let R : H → H := fun x => (2 : ℝ) • T x - x
  have h_i_ii : Firmly_Nonexpansive T ↔ Firmly_Nonexpansive (fun x => x - T x) := by
    constructor
    · intro h x y
      calc
        ‖(x - T x) - (y - T y)‖ ^ 2 + ‖(x - (x - T x)) - (y - (y - T y))‖ ^ 2
            = ‖(x - T x) - (y - T y)‖ ^ 2 + ‖T x - T y‖ ^ 2 := by
                congr 2
                abel_nf
        _ = ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 := by ring
        _ ≤ ‖x - y‖ ^ 2 := h x y
    · intro h x y
      have hxy := h x y
      calc
        ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2
            = ‖(x - T x) - (y - T y)‖ ^ 2 + ‖T x - T y‖ ^ 2 := by ring
        _ = ‖(x - T x) - (y - T y)‖ ^ 2 + ‖(x - (x - T x)) - (y - (y - T y))‖ ^ 2 := by
              congr 2
              abel_nf
        _ ≤ ‖x - y‖ ^ 2 := hxy
  have h_i_iii : Firmly_Nonexpansive T ↔ Nonexpansive R := by
    constructor
    · intro h x y
      let u : H := x - y
      let v : H := T x - T y
      have huv : u - v = (x - T x) - (y - T y) := by
        dsimp [u, v]
        abel_nf
      have h_le_uv : ‖v‖ ^ 2 + ‖u - v‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        calc
          ‖v‖ ^ 2 + ‖u - v‖ ^ 2 = ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 := by
            simp [u, v, huv]
          _ ≤ ‖x - y‖ ^ 2 := h x y
          _ = ‖u‖ ^ 2 := by simp [u]
      have h_nonneg_inside : 0 ≤ ‖u‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v‖ ^ 2 := by
        linarith [h_le_uv]
      have h217 : ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 =
          2 * (‖u‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v‖ ^ 2) := lemma_2_17_ii u v
      have h_nonneg_diff : 0 ≤ ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 := by
        linarith [h_nonneg_inside, h217]
      have h_sq : ‖(2 : ℝ) • v - u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        linarith [h_nonneg_diff]
      have h_norm_abs := (sq_le_sq).mp h_sq
      have h_norm : ‖(2 : ℝ) • v - u‖ ≤ ‖u‖ := by
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using h_norm_abs
      have h_rewrite : (2 : ℝ) • v - u = R x - R y := by
        dsimp [R, u, v]
        calc
          (2 : ℝ) • (T x - T y) - (x - y)
              = ((2 : ℝ) • T x - (2 : ℝ) • T y) - (x - y) := by rw [smul_sub]
          _ = ((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y) := by abel_nf
      have h_norm_R : ‖R x - R y‖ ≤ ‖x - y‖ := by
        calc
          ‖R x - R y‖ = ‖(2 : ℝ) • v - u‖ := by rw [h_rewrite]
          _ ≤ ‖u‖ := h_norm
          _ = ‖x - y‖ := by simp [u]
      have h_dist_R : dist (R x) (R y) ≤ dist x y := by
        simpa [dist_eq_norm] using h_norm_R
      have h_edist_R : edist (R x) (R y) ≤ edist x y := by
        rw [edist_dist, edist_dist]
        exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).2 h_dist_R
      simpa [ENNReal.coe_one, one_mul] using h_edist_R
    · intro h x y
      let u : H := x - y
      let v : H := T x - T y
      have h_rewrite : (2 : ℝ) • v - u = R x - R y := by
        dsimp [R, u, v]
        calc
          (2 : ℝ) • (T x - T y) - (x - y)
              = ((2 : ℝ) • T x - (2 : ℝ) • T y) - (x - y) := by rw [smul_sub]
          _ = ((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y) := by abel_nf
      have h_norm_R : ‖(2 : ℝ) • v - u‖ ≤ ‖u‖ := by
        calc
          ‖(2 : ℝ) • v - u‖ = ‖R x - R y‖ := by rw [h_rewrite]
          _ ≤ ‖x - y‖ := norm_le_mul R h x y
          _ = ‖u‖ := by simp [u]
      have h_sq : ‖(2 : ℝ) • v - u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        refine pow_le_pow_left₀ ?_ h_norm_R 2
        exact norm_nonneg _
      have h_nonneg_diff : 0 ≤ ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 := by
        linarith [h_sq]
      have h217 : ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 =
          2 * (‖u‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v‖ ^ 2) := lemma_2_17_ii u v
      have h_nonneg_inside : 0 ≤ ‖u‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v‖ ^ 2 := by
        have h_twice : 0 ≤ 2 * (‖u‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v‖ ^ 2) := by
          linarith [h_nonneg_diff, h217]
        linarith [h_twice]
      have h_le_uv : ‖v‖ ^ 2 + ‖u - v‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        linarith [h_nonneg_inside]
      have huv : u - v = (x - T x) - (y - T y) := by
        dsimp [u, v]
        abel_nf
      calc
        ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 = ‖v‖ ^ 2 + ‖u - v‖ ^ 2 := by
          simp [u, v, huv]
        _ ≤ ‖u‖ ^ 2 := h_le_uv
        _ = ‖x - y‖ ^ 2 := by simp [u]
  have h_ii_iii : Firmly_Nonexpansive (fun x => x - T x) ↔ Nonexpansive R :=
    h_i_ii.symm.trans h_i_iii
  exact ⟨h_i_ii, h_i_iii, by simpa [R] using h_ii_iii⟩

/--
`T` is firmly nonexpansive iff `T` is averaged with coefficient `1/2`.
-/
theorem firmly_nonexpansive_iff_averaged_half (T : H → H) :
    Firmly_Nonexpansive T ↔ Averaged T (1 / 2 : ℝ) := by
  constructor
  · intro hfirm
    let R : H → H := fun z => (2 : ℝ) • T z - z
    have hprop_4_4 := proposition_4_4_i_ii_iii (T := T)
    have hR_nonexp : Nonexpansive R := by
      simpa [R] using hprop_4_4.2.1.1 hfirm
    have hR_nonexp_on : NonexpansiveOn R (Set.univ : Set H) :=
      nonexpansiveOn_univ_of_nonexpansive hR_nonexp
    refine ⟨by norm_num, R, hR_nonexp_on, ?_⟩
    intro z hz
    have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
    have haux : (1 / 2 : ℝ) • ((2 : ℝ) • T z - z) = T z - (1 / 2 : ℝ) • z := by
      simp [smul_sub, smul_smul]
    rw [hhalf]
    change T z = (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • ((2 : ℝ) • T z - z)
    rw [haux]
    abel_nf
  · intro havg_half
    rcases havg_half with ⟨hhalf_range, R, hR_nonexp_on, hrepr_on⟩
    have hR_nonexp : Nonexpansive R := by
      intro x y
      exact hR_nonexp_on (x := x) (by simp) (y := y) (by simp)
    have hR_eq : ∀ z : H, R z = (2 : ℝ) • T z - z := by
      intro z
      have hz : T z = (1 - (1 / 2 : ℝ)) • z + (1 / 2 : ℝ) • R z := by
        simpa using hrepr_on (x := z) (by simp)
      have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
      rw [hhalf] at hz
      have hz2 : (2 : ℝ) • T z = z + R z := by
        calc
          (2 : ℝ) • T z = (2 : ℝ) • ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • R z) := by rw [hz]
          _ = (2 : ℝ) • ((1 / 2 : ℝ) • z) + (2 : ℝ) • ((1 / 2 : ℝ) • R z) := by rw [smul_add]
          _ = ((2 : ℝ) * (1 / 2 : ℝ)) • z + ((2 : ℝ) * (1 / 2 : ℝ)) • R z := by
                rw [smul_smul, smul_smul]
          _ = z + R z := by norm_num
      have hz3 : (2 : ℝ) • T z - z = R z := by
        calc
          (2 : ℝ) • T z - z = (z + R z) - z := by rw [hz2]
          _ = R z := by abel_nf
      exact hz3.symm
    have h_nonexp_2TminusId : Nonexpansive (fun z => (2 : ℝ) • T z - z) := by
      intro x y
      simpa [hR_eq x, hR_eq y] using hR_nonexp x y
    have hprop_4_4 := proposition_4_4_i_ii_iii (T := T)
    exact hprop_4_4.2.1.2 h_nonexp_2TminusId

