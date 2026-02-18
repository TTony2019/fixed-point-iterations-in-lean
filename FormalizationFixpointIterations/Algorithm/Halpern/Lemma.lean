import FormalizationFixpointIterations.Nonexpansive.Definitions
import FormalizationFixpointIterations.Nonexpansive.Properties
import FormalizationFixpointIterations.InnerProductSpace.WeakConverge
import FormalizationFixpointIterations.InnerProductSpace.Closedness
import FormalizationFixpointIterations.InnerProductSpace.Compact

open Nonexpansive_operator Filter Topology TopologicalSpace

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

structure Halpern (T : H → H) where
  x0 : H
  u : H  -- x in 30.1
  x : ℕ → H
  α : ℕ → ℝ
  update : ∀ k : ℕ, x (k + 1) = (α k) • u + (1 - α k) • (T (x k))
  initial_value : x 0 = x0

/--
Lemma 30.2: Properties of `ξ` : `∀ ξ ∈ (0,1)`, `ln (1 - ξ) ≤ -ξ`
-/
lemma log_ineq
  (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 1) :
  Real.log (1 - ξ) ≤ -ξ := by
  have h1 : 1 - ξ > 0 := by simp [Set.mem_Ioo] at hξ; linarith
  have h2 : 1 - ξ < 1 := by simp [Set.mem_Ioo] at hξ; linarith
  have key := Real.log_le_sub_one_of_pos h1
  linarith

/--
Lemma : Properties of `α` : `∀ α ∈ (0,1), 1 - α > 0`
-/
lemma one_sub_pos_of_mem_Ioo
  {a : ℝ} (ha : a ∈ Set.Ioo 0 1) : 0 < 1 - a := sub_pos.mpr ha.2

/--
Lemma : Properties of `α` : `∀ α ∈ (0,1), 1 - α < 1`
-/
lemma one_sub_lt_one_of_mem_Ioo
  {a : ℝ} (ha : a ∈ Set.Ioo 0 1) : 1 - a < 1 := by simp [Set.mem_Ioo] at ha; linarith

/--
Lemma 30.3 : Properties of `α` :
  `∀ n, α n ∈ (0,1) → ∏ (1 - α n) = exp Σ log(1 - α n)) ≤ exp (Σ -α n)`
-/
lemma prod_exp_sum
  {T : H → H} (alg : Halpern T)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (m n : ℕ) :
  ∏ x ∈ Finset.Icc m n, (1 - alg.α x) = Real.exp (∑ x ∈ Finset.Icc m n, Real.log (1 - alg.α x)) ∧
    Real.exp (∑ x ∈ Finset.Icc m n, Real.log (1 - alg.α x)) ≤
      Real.exp (∑ x ∈ Finset.Icc m n, -alg.α x) := by
  constructor
  · symm; rw [Real.exp_sum]; apply Finset.prod_congr
    · ext x; simp
    · intro x
      have hk : x ∈ Finset.Icc m n → 1 - alg.α x > 0 := by
        intro hk_mem
        have := h_α_range x
        simp [Set.mem_Ioo] at this; linarith
      intro hx; rw [Real.exp_log]; exact hk hx
  apply Real.exp_le_exp.mpr; apply Finset.sum_le_sum; intro x hx
  exact log_ineq (alg.α x) (h_α_range x)

/--
Lemma 30.4 : Limit of the infinite product of `(1 - α k)` :
  if `lim n→∞, Σ α n = ∞`, `lim n→∞ ∏_{k=m}^n (1 - α k) = 0`
-/
lemma infinite_prod_zero
  {T : H → H} (alg : Halpern T) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) (m : ℕ) :
  Tendsto (fun n => ∏ k ∈ Finset.Icc m n, (1 - alg.α k)) atTop (nhds 0) := by
  have h_prod_eq : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) =
      Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) := by
    intro n hn; exact (prod_exp_sum alg h_α_range m n).1
  have h_exp_le : ∀ n ≥ m, Real.exp (∑ k ∈ Finset.Icc m n, Real.log (1 - alg.α k)) ≤
      Real.exp (∑ k ∈ Finset.Icc m n, -alg.α k) := by
    intro n hn; exact (prod_exp_sum alg h_α_range m n).2
  have h_prod_le : ∀ n ≥ m, ∏ k ∈ Finset.Icc m n, (1 - alg.α k) ≤
      Real.exp (- ∑ k ∈ Finset.Icc m n, alg.α k) := by
    intro n hn; rw [h_prod_eq n hn]; convert h_exp_le n hn using 2; simp [Finset.sum_neg_distrib]
  have h_sum_icc_inf : Tendsto (fun n => ∑ k ∈ Finset.Icc m n, alg.α k) atTop atTop := by
    have h_decomp : ∀ n ≥ m, ∑ k ∈ Finset.range (n + 1), alg.α k =
        (∑ k ∈ Finset.range m, alg.α k) + (∑ k ∈ Finset.Icc m n, alg.α k) := by
      intro n hn; rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_succ_of_le hn)]; congr 1
    let C := ∑ k ∈ Finset.range m, alg.α k
    have h_eq : ∀ n ≥ m, ∑ k ∈ Finset.Icc m n, alg.α k =
        (∑ k ∈ Finset.range (n + 1), alg.α k) - C := by
      intro n hn; have := h_decomp n hn; linarith
    rw [tendsto_atTop_atTop]; intro b
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp h_α_sum_inf) (b + C)
    use max m N; intro n hn
    have hn_m : n ≥ m := le_of_max_le_left hn; have hn_N : n ≥ N := le_of_max_le_right hn
    rw [h_eq n hn_m]
    have : ∑ k ∈ Finset.range (n + 1), alg.α k ≥ b + C := by apply hN; omega
    linarith
  have h_neg_sum : Tendsto (fun n => -∑ k ∈ Finset.Icc m n, alg.α k) atTop atBot := by simpa
  have h_exp_to_zero : Tendsto (fun n => Real.exp
    (- ∑ k ∈ Finset.Icc m n, alg.α k)) atTop (nhds 0) := Real.tendsto_exp_atBot.comp h_neg_sum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_exp_to_zero ?_ ?_
  · intro n; apply Finset.prod_nonneg; intro k _
    have := h_α_range k
    simp [Set.mem_Ioo] at this; linarith
  · intro n
    by_cases hn : n ≥ m
    · exact h_prod_le n hn
    · simp [Finset.Icc_eq_empty_of_lt (Nat.not_le.mp hn)]

/--
Lemma : Inequalities by non-expansive :
  `∀ z ∈ C`, `‖T(x n) - z‖ ≤ ‖x n - z‖ ∧ ‖x n - z‖ ≤ ‖x0 - z‖`
-/
lemma halpern_distance_monotone
  {D : Set H} {T : H → H} (hT_nonexp : NonexpansiveOn T D) {C : Set H} (hC : C = Fix T ∩ D)
  (alg : Halpern T) (halg_x0 : alg.x0 ∈ D) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1) (coincidence : alg.u = alg.x0) :
  ∀ z ∈ C, ∀ n, ‖T (alg.x n) - z‖ ≤ ‖alg.x n - z‖ ∧ ‖alg.x n - z‖ ≤ ‖alg.x0 - z‖ := by
  have hT_quasinonexp := nonexpansive_quasinonexpansive hT_nonexp
  intro z hzC n
  induction n with
  | zero =>
    constructor
    · have ⟨hz_fix, hz_D⟩ : z ∈ Fix T ∩ D := by convert hzC; exact hC.symm
      rw [alg.initial_value]
      exact hT_quasinonexp halg_x0 ⟨hz_fix, hz_D⟩
    · rw [alg.initial_value]
  | succ k ih =>
    constructor
    · have ⟨hz_fix, hz_D⟩ :z ∈ Fix T ∩ D := by convert hzC; exact hC.symm
      exact hT_quasinonexp (halg_x_in_D (k+1)) ⟨hz_fix, hz_D⟩
    · rw [alg.update]; calc
        _ = ‖alg.α k • (alg.u - z) + (1 - alg.α k) • (T (alg.x k) - z)‖ := by
              congr 1; simp [smul_sub, sub_smul, add_sub, add_comm]
        _ ≤ alg.α k * ‖alg.u - z‖ + (1 - alg.α k) * ‖T (alg.x k) - z‖ := by
              apply norm_add_le_of_le
              · simp only [norm_smul]; gcongr; simp [abs_of_pos (h_α_range k).1]
              · simp only [norm_smul]; gcongr; simp only [Real.norm_eq_abs]
                rw [abs_of_pos (by linarith [(h_α_range k).2])]
        _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x k - z‖ := by
              rw [← coincidence]; gcongr
              · linarith [one_sub_pos_of_mem_Ioo (h_α_range k)]
              · exact ih.1
        _ ≤ alg.α k * ‖alg.x0 - z‖ + (1 - alg.α k) * ‖alg.x0 - z‖ := by
              gcongr
              · linarith [one_sub_pos_of_mem_Ioo (h_α_range k)]
              · exact ih.2
        _ = ‖alg.x0 - z‖ := by ring

/--
Lemma : Properties of sum : `∑_m^n f k + ∑_(n + 1)^∞ f k = ∑_m^∞ f k`
-/
lemma sum_icc_add_tsum_eq_tsum_add
  {f : ℕ → ℝ} (hf : Summable f) (m n : ℕ) (hmn : m ≤ n) :
  ∑ k ∈ Finset.Icc m n, f k + ∑' k, f (k + n + 1) = ∑' k, f (k + m) := by
  -- 首先，分解 ∑' k, f (k + m) 为三部分
  have h_decomp : ∑' k, f (k + m) = ∑ k ∈ Finset.Icc m n, f k + ∑' k, f (k + n + 1) := by
    have h_split : ∑' k : ℕ, f (k + m) =
        ∑ k ∈ Finset.range (n - m + 1), f (k + m) + ∑' k : ℕ, f (k + n + 1) := by
      have hf_shift : Summable (fun k => f (k + m)) := by
        apply hf.comp_injective; intro a b hab; linarith
      rw [← Summable.sum_add_tsum_nat_add]
      · congr; ext k; ring_nf; congr 1; rw [Nat.Simproc.add_eq_add_le (1 + k + (n - m)) (1 + k) hmn]
      · assumption
    have h_finset_eq : ∑ k ∈ Finset.range (n - m + 1), f (k + m) = ∑ k ∈ Finset.Icc m n, f k := by
      trans ∑ i ∈ Finset.Icc m n, f i
      · rw [Finset.sum_bij (fun k _ => k + m)]
        · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
        · intro k₁ k₂ _ _ heq; omega
        · intro k hk; use k - m; simp; constructor; repeat simp at hk; omega
        · simp
      · simp
    rw [h_split, h_finset_eq]
  rw [h_decomp]

/--
Lemma : Limit of the sum of difference ；`lim m n → ∞`, `μ * Σ_m^n |λ (k + 1) - λ k| = 0`
-/
lemma halpern_sum_tail_tendsto_zero
  {T : H → H} (alg : Halpern T) (μ : ℝ) (hμ_pos : μ > 0)
  (h_α_diff_finite : Summable (fun n => |alg.α (n + 1) - alg.α n|))
  : ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * (∑ k ∈ Finset.Icc m n,
    |alg.α (k + 1) - alg.α k|) < ε := by
  intros ε ε_pos; let f := fun n => |alg.α (n + 1) - alg.α n|
  have hf := h_α_diff_finite
  have h_sum_tail : Tendsto (fun m => ∑' k : ℕ, f (k + m)) atTop (nhds 0) := by
    exact tendsto_sum_nat_add f
  have h_eventually_tail : ∀ᶠ m in atTop, ∑' k : ℕ, f (k + m) < ε / μ := by
    apply (tendsto_order.1 h_sum_tail).2 (ε / μ) (by positivity)
  have : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → μ * ∑ k ∈ Finset.Icc m n, f k < ε := by
    filter_upwards [h_eventually_tail] with m hm; apply eventually_atTop.2; use m
    intro n hmn hmn'
    have h_le : ∑ k ∈ Finset.Icc m n, f k ≤ ∑' k : ℕ, f (k + m) := by calc
        _ ≤ ∑ k ∈ Finset.Icc m n, f k + ∑' (k : ℕ), f (k + n + 1) := by
          simp only [le_add_iff_nonneg_right]; apply tsum_nonneg; intro k; exact abs_nonneg _
        _ = ∑' (k : ℕ), f (k + m) := sum_icc_add_tsum_eq_tsum_add h_α_diff_finite m n hmn
    calc
      _ ≤ μ * ∑' k : ℕ, f (k + m) := by apply mul_le_mul_of_nonneg_left h_le (le_of_lt hμ_pos)
      _ < μ * (ε / μ) := mul_lt_mul_of_pos_left hm hμ_pos
      _ = ε := by field_simp [ne_of_gt hμ_pos]
  exact this

/--
Lemma : Properties of the product : `∏_m^n (1 - α (k + 1)) = ∏_(m + 1)^(n + 1) (1 - α k)`
-/
lemma h_reindex
  {T : H → H} (alg : Halpern T) :∀ m : ℕ, (fun n ↦ ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)))
      = (fun n ↦ ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k)) := by
    intro m; ext n; by_cases hn : n ≥ m
    · let g := fun k => k + 1; let s := Finset.Icc m n; let f := fun k => 1 - alg.α k
      have hf : Set.InjOn g ↑s := by
        intros x hx y hy hxy; exact Nat.succ_inj.mp hxy
      rw [← Finset.prod_image (s := s) (f := f) (g := g) hf]; congr 1; ext k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨x, hx, rfl⟩; constructor
        · simp only [ge_iff_le, Finset.coe_Icc, Nat.add_right_cancel_iff, implies_true,
          Set.injOn_of_eq_iff_eq, Finset.mem_Icc, add_le_add_iff_right, g, s] at *
          rcases hx with ⟨hxm, hxn⟩; linarith
        · simp only [g, s, Finset.mem_Icc] at *; linarith
      · intro hk; use k - 1; constructor
        · rcases hk with ⟨hk1, hk2⟩; simp only [g, s, Finset.mem_Icc, tsub_le_iff_right] at *
          constructor
          · exact Nat.le_sub_one_of_lt hk1
          · linarith
        rcases hk with ⟨hk1, hk2⟩; simp only [s, g] at *
        refine Nat.sub_add_cancel ?_; linarith
    · have h_empty1 : Finset.Icc m n = ∅ := by
        ext x; simp only [Finset.mem_Icc]
        simp only [ge_iff_le, not_le, Finset.notMem_empty, iff_false, not_and] at *
        intro hx; linarith
      have h_empty2 : Finset.Icc (m + 1) (n + 1) = ∅ := by
        ext x; simp only [Finset.mem_Icc]
        simp only [ge_iff_le, not_le, Finset.notMem_empty, iff_false, not_and] at *
        intro hx; linarith
      simp [h_empty1, h_empty2, Finset.prod_empty]

/--
Lemma : Limit of the product : `lim n → ∞, μ * ∏_m^n (1 - λ (k + 1)) = 0`
-/
lemma halpern_prod_tail_tendsto_zero
  {T : H → H} (alg : Halpern T) (μ : ℝ) (hμ_pos : μ > 0) (h_α_range : ∀ n, alg.α n ∈ Set.Ioo 0 1)
  (h_α_sum_inf : Tendsto (fun N => ∑ n ∈ Finset.range N, alg.α n) atTop atTop) : ∀ ε > 0, ∀ m : ℕ,
    ∀ᶠ n in atTop, m ≤ n → μ * ∏ k ∈ Finset.Icc m n, (1 - alg.α (k + 1)) < ε := by
  intros ε hε m
  have h_prod_tendsto : Tendsto (fun n => ∏ k ∈ Finset.Icc
    (m + 1) (n + 1), (1 - alg.α k)) atTop (nhds 0) := by
    let f : ℕ → ℝ := fun n => ∏ k ∈ Finset.Icc (m + 1) n, (1 - alg.α k)
    have h_f_tendsto : Tendsto f atTop (nhds 0) :=
      infinite_prod_zero alg h_α_range h_α_sum_inf (m + 1)
    apply h_f_tendsto.comp; exact tendsto_add_atTop_nat 1
  have h_eventually : ∀ᶠ n in atTop, ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k) < ε / μ := by
    rw [Metric.tendsto_atTop] at h_prod_tendsto
    obtain ⟨N, hN⟩ := h_prod_tendsto (ε / μ) (by positivity)
    rw [eventually_atTop]; use N; intro n hn
    have := hN n hn; rw [Real.dist_eq] at this
    simp only [sub_zero] at this; exact lt_of_abs_lt this
  rw [eventually_atTop]; obtain ⟨N, hN⟩ := (eventually_atTop).mp h_eventually
  use max m N; intro n hn hmn; have hn_N : n ≥ N := le_of_max_le_right hn; calc
    _ = μ * ∏ k ∈ Finset.Icc (m + 1) (n + 1), (1 - alg.α k) := by
      congr 1; exact congrFun (h_reindex alg m) n
    _ < μ * (ε / μ) := mul_lt_mul_of_pos_left (hN n hn_N) hμ_pos
    _ = ε := by field_simp [ne_of_gt hμ_pos]

/--
Lemma : Limit of the difference : `lim n → ∞`, `x (n k) - T (x (n k)) = 0`
-/
lemma halpern_subseq_x_sub_Tx_tendsto_zero
  {T : H → H} (alg : Halpern T) (n : ℕ → ℕ) (h_n_strict_mono : ∀ i j, i < j → n i < n j)
  (h_x_Tx_limit : Tendsto (fun n ↦ alg.x n - T (alg.x n)) atTop (nhds 0))
  : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (nhds 0) := by
  have h_n_k_ge_k : ∀ k, n k ≥ k := by apply StrictMono.nat_id_le h_n_strict_mono
  rw [Metric.tendsto_atTop] at h_x_Tx_limit ⊢; intro ε ε_pos; obtain ⟨N, hN⟩ := h_x_Tx_limit ε ε_pos
  use N; intro k hk; specialize hN (n k) (Nat.le_trans hk (h_n_k_ge_k k))
  rw [dist_eq_norm] at hN ⊢; exact hN

/--
Lemma : The subsequence weakly converges to a point in the fixed point set :
  `x n k ⇀ z` ∧ `lim n → ∞, x (n k) - T (x (n k)) = 0` → `z ∈ Fix T`
-/
lemma halpern_subseq_fixed_point [CompleteSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty)
  {T : H → H} (hT_nonexp : NonexpansiveOn T D) (alg : Halpern T) (n : ℕ → ℕ) (z : H)
  (h_z_in_D : z ∈ D) (h_z_weak_limit : WeakConverge (alg.x ∘ n) z) (halg_x_in_D : ∀ n, alg.x n ∈ D)
  (hs : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (nhds 0)) : z ∈ Fix T :=
  weakLimit_mem_fixedPoints_of_strongly_tendsto_sub hD_closed hD_convex hD_nonempty
    hT_nonexp (alg.x ∘ n) (fun k => halg_x_in_D (n k)) z h_z_in_D h_z_weak_limit hs

/--
Lemma 2.45 : Bounded sequence has a weakconvergent subsequence :
  `∀ n, ‖x n‖ ≤ M` → `∃ (φ : ℕ → ℕ) (p : H), (∀ m n, m < n → φ m < φ n) ∧ WeakConverge (x ∘ φ) p`
-/
lemma bounded_seq_weakly_convergent_subsequence [SeparableSpace H] [CompleteSpace H]
  (x : ℕ → H) (h_bounded : ∃ M, ∀ n, ‖x n‖ ≤ M) :
  ∃ (φ : ℕ → ℕ) (p : H), (∀ m n, m < n → φ m < φ n) ∧ WeakConverge (x ∘ φ) p := by
  obtain ⟨M, hM⟩ := h_bounded
  have h_is_bounded : Bornology.IsBounded (Set.range fun n => ‖x n‖) := by
    rw [Bornology.IsBounded]; use 2 * M; intro m hm n hn
    simp only [compl_compl, Set.mem_range] at *
    rcases hm with ⟨k, rfl⟩; rcases hn with ⟨l, rfl⟩
    calc
      _ ≤ ‖x k‖ + ‖x l‖ :=
        abs_sub_le_of_nonneg_of_le (norm_nonneg _) (by simp) (norm_nonneg _) (by simp)
      _ ≤ M + M := add_le_add (hM k) (hM l)
      _ = 2 * M := by ring
  obtain ⟨a, φ, h_strict_mono, h_weak_conv⟩ :=
    bounded_seq_has_weakly_converge_subseq_separable x h_is_bounded
  have h_phi_explicit : ∀ m n, m < n → φ m < φ n := fun m n a ↦ h_strict_mono a
  exact ⟨φ, a, h_phi_explicit, h_weak_conv⟩

/--
Definition of projection point : `∃ u ∈ C, ‖x - u‖ = inf_{w ∈ C} ‖x - w‖`
-/
theorem existence_of_projection_point [CompleteSpace H]
  (C : Set H) (hC1 : C.Nonempty) (hC2 : Convex ℝ C) (hC3 : IsClosed C) (x : H) :
  ∃ u ∈ C, ‖x - u‖ = ⨅ w : C, ‖x - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hC1 (IsClosed.isComplete hC3) hC2 x

/--
Proposition of projection point :
  `‖x - PCx‖ = inf_{w ∈ C} ‖x - w‖` → `∀ w ∈ C, ⟪x - PCx, w - PCx⟫ ≤ 0`
-/
theorem proj_pt_inner_le_zero
  (x PCx : H) (C : Set H) (hC2 : Convex ℝ C) (hPCx : PCx ∈ C) (hP : ‖x - PCx‖ = ⨅ w : C, ‖x - w‖) :
  ∀ w ∈ C, inner ℝ (x - PCx) (w - PCx) ≤ 0 := (norm_eq_iInf_iff_real_inner_le_zero hC2 hPCx).1 hP

/--
Lemma : Limit of the inner product is upbounded : `∃ M > 0, lim n → ∞, ⟪T (x n) - PCx, x - PCx⟫ ≤ M`
-/
lemma halpern_inner_bounded_of_limsup
  {T : H → H} (alg : Halpern T) (m : H) (μ : ℝ) (hμ_Tx_bound : ∀ n, ‖alg.u - T (alg.x n)‖ ≤ μ)
  (h_limsup_neg : limsup (fun k ↦ inner ℝ (T (alg.x k) - m) (alg.u - m)) atTop ≤ 0)
  : ∃ M, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ ≤ M := by
  have : ∃ N, ∀ᶠ n in atTop, ⟪T (alg.x n) - m, alg.u - m⟫ < N := by
    have h_limsup_neg' : limsup (fun k ↦ inner ℝ (T (alg.x k) - m) (alg.u - m)) atTop < 1 := by
      linarith
    use 1; apply Filter.eventually_lt_of_limsup_lt h_limsup_neg' ?_
    simp only [IsBoundedUnder, IsBounded, eventually_map, eventually_atTop, ge_iff_le]
    use (μ + ‖alg.u - m‖) * ‖alg.u - m‖; use 0; intro b hb; calc
      _ ≤ ‖T (alg.x b) - m‖ * ‖alg.u - m‖ := real_inner_le_norm (T (alg.x b) - m) (alg.u - m)
      _ = ‖(T (alg.x b) - alg.u) + (alg.u - m)‖ * ‖alg.u - m‖ := by simp
      _ ≤ (‖T (alg.x b) - alg.u‖ + ‖alg.u - m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul (norm_add_le (T (alg.x b) - alg.u) (alg.u - m)) (by simp)
          (norm_nonneg (alg.u - m)); rw [← zero_add 0]
        apply add_le_add (norm_nonneg (T (alg.x b) - alg.u)) (norm_nonneg (alg.u - m))
      _ ≤ (μ + ‖alg.u - m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul ?_ (by simp) (by simp) ?_
        · simp only [add_le_add_iff_right]; specialize hμ_Tx_bound b; calc
            _ = ‖alg.u - T (alg.x b)‖ := by rw [norm_sub_rev]
            _ ≤ μ := hμ_Tx_bound
        · have : μ ≥ 0 := by specialize hμ_Tx_bound b; linarith [norm_nonneg (alg.u - T (alg.x b))]
          rw [← zero_add 0]; apply add_le_add this (norm_nonneg (alg.u - m))
  rcases this with ⟨N, hN⟩; use N; filter_upwards [hN] with n hn; linarith

/--
Lemma : Upbounded leads to upbounded : `‖x n - z‖ ≤ M1` → `‖x (n + 1) - PCx‖ ^ 2 ≤ M2`
-/
lemma halpern_norm_sq_bounded
  {T : H → H} (alg : Halpern T) (z m : H) (h_seq_bounded : ∃ M, ∀ n, ‖alg.x n - z‖ ≤ M)
  : ∃ M : ℝ, ∀ n : ℕ, ‖alg.x (n + 1) - m‖ ^ 2 ≤ M := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ (n : ℕ), ‖alg.x (n + 1) - z‖ ≤ M := by
    rcases h_seq_bounded with ⟨M,hM⟩; use M; intro n; exact hM (n + 1)
  use (M + ‖z - m‖) ^ 2; intro n; calc
    _ = ‖alg.x (n + 1) - z + z - m‖ ^ 2 := by simp
    _ ≤ (‖alg.x (n + 1) - z‖ + ‖z - m‖) ^ 2 := by
      apply sq_le_sq.mpr; simp only [sub_add_cancel, abs_norm]
      have : ‖alg.x (n + 1) - z‖ + ‖z - m‖ ≥ 0 := add_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [abs_of_nonneg this]; exact norm_sub_le_norm_sub_add_norm_sub (alg.x (n + 1)) z m
    _ ≤ (M + ‖z - m‖) ^ 2 := by
      apply sq_le_sq.mpr; simp only [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [abs_of_nonneg]
      · exact add_le_add_left (hM n) ‖z - m‖
      · apply add_nonneg ?_ (norm_nonneg _); specialize hM 0
        have : ‖alg.x (0 + 1) - z‖ ≥ 0 := norm_nonneg _; linarith

/--
Lemma 30.15 : The sequence of the inner product has a subsequence which tends to limsup :
  `∃ (n : ℕ → ℕ) (z PCx : H) (q : ℕ → ℝ),
  (∀ i j, i < j → n i < n j) ∧ (z ∈ D ∧ WeakConverge (x ∘ n) z) ∧
  (PCx ∈ C ∧ ‖x - PCx‖ = inf_{w ∈ C} ‖x - w‖) ∧
  (q = fun n => ⟪T (x n) - PCx, x - PCx⟫) ∧
  (Tendsto (q ∘ n) atTop (nhds (limsup q atTop)))`
-/
lemma halpern_subsequence_weak_convergence [CompleteSpace H] [SeparableSpace H]
  {D : Set H} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : H → H} {C : Set H}
  (hT_fixpoint : C.Nonempty) (alg : Halpern T)
  (halg_x_in_D : ∀ n, alg.x n ∈ D) (h_C_closed_convex : IsClosed C ∧ Convex ℝ C)
  (h_xn_bounded : ∃ M, ∀ n, ‖alg.x n‖ ≤ M) (h_Txn_bounded : ∃ M, ∀ (n : ℕ), ‖T (alg.x n)‖ ≤ M) :
  ∃ (n : ℕ → ℕ) (z : H) (m : H) (q : ℕ → ℝ), (∀ i j, i < j → n i < n j) ∧
    (z ∈ D ∧ WeakConverge (alg.x ∘ n) z) ∧ (m ∈ C ∧ ‖alg.u - m‖ = ⨅ w : C, ‖alg.u - w‖) ∧
      (q = fun n => ⟪T (alg.x n) - m, alg.u - m⟫) ∧
        (Tendsto (q ∘ n) atTop (nhds (limsup q atTop))) := by
  have h_C_closed : IsClosed C := h_C_closed_convex.1
  have h_C_convex : Convex ℝ C := h_C_closed_convex.2
  obtain ⟨m, hm_in_C, hm_proj⟩ :=
    existence_of_projection_point C hT_fixpoint h_C_convex h_C_closed alg.u
  let q : ℕ → ℝ := fun n => ⟪T (alg.x n) - m, alg.u - m⟫; rcases h_Txn_bounded with ⟨M_Tx, hM_Tx⟩
  have hq_bdd : ∃ M : ℝ, ∀ k : ℕ, |q k| ≤ M := by
    use (M_Tx + ‖m‖) * ‖alg.u - m‖; intro k; calc
      _ = |⟪T (alg.x k) - m, alg.u - m⟫| := rfl
      _ = max (⟪T (alg.x k) - m, alg.u - m⟫) (-⟪T (alg.x k) - m, alg.u - m⟫) := rfl
      _ = max (⟪T (alg.x k) - m, alg.u - m⟫) (⟪-(T (alg.x k) - m), alg.u - m⟫) := by
        congr; exact Eq.symm (inner_neg_left (T (alg.x k) - m) (alg.u - m))
      _ ≤ ‖T (alg.x k) - m‖ * ‖alg.u - m‖ := by
        apply max_le (real_inner_le_norm (T (alg.x k) - m) (alg.u - m)) ?_
        calc
          _ ≤ ‖-(T (alg.x k) - m)‖ * ‖alg.u - m‖ :=
            real_inner_le_norm (-(T (alg.x k) - m)) (alg.u - m)
          _ = ‖T (alg.x k) - m‖ * ‖alg.u - m‖ := by rw [norm_neg]
      _ ≤ (‖T (alg.x k)‖ + ‖m‖) * ‖alg.u - m‖ := mul_le_mul_of_nonneg_right
        (norm_sub_le (T (alg.x k)) m) (norm_nonneg _)
      _ ≤ (M_Tx + ‖m‖) * ‖alg.u - m‖ := by
        apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simp only [add_le_add_iff_right]; exact hM_Tx k
  have h_subseq_q : ∃ (k : ℕ → ℕ), StrictMono k ∧
    Tendsto (q ∘ k) atTop (nhds (limsup q atTop)) := by
    obtain ⟨φ, L, h_strict_mono, h_L_eq, h_tendsto⟩ := lim_subsequence_eq_limsup q hq_bdd
    exact ⟨φ, h_strict_mono, by rwa [← h_L_eq]⟩
  obtain ⟨k, h_k_strict_mono, h_k_tendsto⟩ := h_subseq_q
  have h_xk_bounded : ∃ M, ∀ j, ‖alg.x (k j)‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_xn_bounded; exact ⟨M, fun j => hM (k j)⟩
  obtain ⟨l, z, h_l_strict_mono, h_weak_xkl_to_z⟩ :=
    bounded_seq_weakly_convergent_subsequence (alg.x ∘ k) h_xk_bounded
  have h_z_in_D : z ∈ D := by
    have h_x_in_D : ∀ j, alg.x (k (l j)) ∈ D := fun j => halg_x_in_D _
    have h_D_weakly_closed : IsWeaklyClosed D := by
      apply closed_is_weakly_closed
      · exact hD_convex
      · exact hD_closed
    have h_D_weakly_seq_closed : IsWeaklySeqClosed D := by
      apply weakly_closed_seq_closed; exact h_D_weakly_closed
    simp only [IsWeaklySeqClosed, IsSeqClosed] at h_D_weakly_seq_closed
    have h : (∀ (n : ℕ), (alg.x ∘ k ∘ l) n ∈ ⇑(toWeakSpace ℝ H) '' D) := by
      intro n
      exact Set.mem_image_of_mem (⇑(toWeakSpace ℝ H)) (halg_x_in_D ((k ∘ l) n))
      -- exact Set.mem_image_of_mem (⇑(toWeakSpace ℝ H))
    specialize @h_D_weakly_seq_closed (toWeakSpace ℝ H ∘ alg.x ∘ k ∘ l)
      (toWeakSpace ℝ H z) h h_weak_xkl_to_z
    exact Set.inter_singleton_nonempty.mp h_D_weakly_seq_closed
  let n : ℕ → ℕ := k ∘ l
  have h_n_strict_mono : ∀ i j, i < j → n i < n j := by
    intro i j hij; unfold n; simp only [Function.comp_apply]
    exact h_k_strict_mono (h_l_strict_mono i j hij)
  have h_n_tendsto : Tendsto (q ∘ n) atTop (nhds (limsup q atTop)) := by
    have h_comp : (q ∘ n) = (q ∘ k) ∘ l := by funext j; simp only [Function.comp_apply, n]
    rw [h_comp]; apply h_k_tendsto.comp; exact StrictMono.tendsto_atTop h_l_strict_mono
  exact ⟨n, z, m, q, h_n_strict_mono, ⟨h_z_in_D, h_weak_xkl_to_z⟩,
    ⟨hm_in_C, hm_proj⟩, rfl, h_n_tendsto⟩

/--
Lemma 30.16 : Limsup of the inner product nonpositive : `limsup n → ∞, ⟪T (x n) - PCx, x - PCx⟫ ≤ 0`
-/
lemma halpern_limsup_inner_le_zero [CompleteSpace H]
  {D : Set H} {T : H → H} {C : Set H} (hC : C = Fix T ∩ D)
  (hC_closed_convex : IsClosed C ∧ Convex ℝ C) (alg : Halpern T) (n : ℕ → ℕ) (z : H)
  (h_z_in_C : z ∈ C) (h_weak_xn_to_z : WeakConverge (alg.x ∘ n) z) (m : H) (hm_in_C : m ∈ C)
  (hm_proj : ‖alg.u - m‖ = ⨅ w : C, ‖alg.u - w‖)
  (h_subseq_x_Tx_limit : Tendsto (fun k => alg.x (n k) - T (alg.x (n k))) atTop (nhds 0))
  (h_n_tendsto : Tendsto (fun k => ⟪T (alg.x (n k)) - m, alg.u - m⟫) atTop
  (nhds (limsup (fun n => ⟪T (alg.x n) - m, alg.u - m⟫) atTop)))
  : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop ≤ 0 := by
  have h_subseq_inner_limit1 : Tendsto
    (fun k => ⟪T (alg.x (n k)) - alg.x (n k), alg.u - m⟫) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop] at h_subseq_x_Tx_limit ⊢; intro ε ε_pos; let R := ‖alg.u - m‖
      by_cases hR : R = 0
      · use 0; intro k hk; rw [Real.dist_eq]; simp only [sub_zero]
        have h_vec_zero : alg.u - m = 0 := norm_eq_zero.mp hR
        simp [inner_zero_right, h_vec_zero]; linarith
      · have hR_pos : 0 < R := by
          simp only [R]
          exact norm_pos_iff.mpr (by
            intro h_eq; have : ‖alg.u - m‖ = 0 := by simp [h_eq]
            exact hR this)
        obtain ⟨N, hN⟩ := h_subseq_x_Tx_limit (ε / R) (by positivity); use N; intro k hk
        specialize hN k hk; simp only [dist_eq_norm, sub_zero] at hN
        rw [Real.dist_eq]; simp only [sub_zero]; calc
          _ ≤ ‖T (alg.x (n k)) - alg.x (n k)‖ * ‖alg.u - m‖ := by apply abs_real_inner_le_norm
          _ = ‖alg.x (n k) - T (alg.x (n k))‖ * ‖alg.u - m‖ := by congr 1; rw [norm_sub_rev]
          _ < (ε / R) * R := mul_lt_mul_of_pos_right hN hR_pos
          _ = ε := by field_simp [ne_of_gt hR_pos]
  have h_subseq_inner_limit2 : Tendsto (fun k => ⟪alg.x (n k), alg.u - m⟫) atTop
    (nhds ⟪z , alg.u - m⟫) :=
    by rw [weakConverge_iff_inner_converge] at h_weak_xn_to_z; apply h_weak_xn_to_z (alg.u - m)
  have h_subseq_inner_limit3 : Tendsto (fun k => ⟪alg.x (n k) - m, alg.u - m⟫) atTop
    (nhds ⟪z - m, alg.u - m⟫) := by
      by_cases h_eq : alg.u = m
      · simp [h_eq]
      · rw [Metric.tendsto_atTop]at h_subseq_inner_limit2 ⊢; intro ε ε_pos
        obtain ⟨N, hN⟩ := h_subseq_inner_limit2 ε (by positivity); use N; intro k hk
        specialize hN k hk; rw [Real.dist_eq] at hN ⊢; calc
          _ = |⟪alg.x (n k), alg.u - m⟫- ⟪z, alg.u - m⟫| := by
            congr 1; simp [inner_sub_left, inner_sub_left]
          _ < ε := hN
  have h_proj_ineq : ⟪alg.u - m, z - m⟫ ≤ 0 := by
    have hm_in_D : m ∈ D := by rw [hC] at hm_in_C; exact Set.mem_of_mem_inter_right hm_in_C
    have h_proj_apply : ∀ w ∈ C, ⟪alg.u - m, w - m⟫ ≤ 0 :=
      proj_pt_inner_le_zero alg.u m C hC_closed_convex.2 hm_in_C hm_proj
    exact h_proj_apply z h_z_in_C
  have h_subseq_inner_limit4 : Tendsto (fun k => ⟪ T (alg.x (n k)) - m, alg.u - m⟫) atTop
    (nhds ⟪z - m, alg.u - m⟫) := by
      have h_inner_diff : ∀ k, ⟪ T (alg.x (n k)) - m, alg.u - m⟫ = ⟪ T (alg.x (n k)) -
        alg.x (n k), alg.u - m⟫ + ⟪ alg.x (n k) - m, alg.u - m⟫ := by
        intro k; simp [inner_sub_left, inner_sub_left, inner_sub_left]
      convert Tendsto.add h_subseq_inner_limit1 h_subseq_inner_limit3 using 1
      · funext k; exact h_inner_diff k
      · simp
  have h_limsup_eq : limsup (fun k => ⟪(T (alg.x k) - m), (alg.u - m)⟫) atTop
    = ⟪z - m, alg.u - m⟫ := tendsto_nhds_unique h_n_tendsto h_subseq_inner_limit4
  calc
    _ = ⟪z - m, alg.u - m⟫ := h_limsup_eq
    _ = ⟪alg.u - m, z - m⟫ := real_inner_comm (alg.u - m) (z - m)
    _ ≤ 0 := h_proj_ineq
