/-
Copyright (c) 2025 Yifan Bai, Yantao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yifan Bai, Yantao Li
-/
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Dual
import FormalizationFixpointIterations.InnerProductSpace.Closedness
import FormalizationFixpointIterations.InnerProductSpace.T2Space
import Mathlib
open Metric WeakDual Filter Topology TopologicalSpace
section WeaklyCompact

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

def IsWeaklyCompact (s : Set H) : Prop := IsCompact ((toWeakSpace ℝ H) '' s)
/-
Lemma 1.12
-/
example (s : Set H) (h : IsWeaklyCompact s) : IsWeaklyClosed s := IsCompact.isClosed h


lemma WeakSpace.continuous_of_continuous_eval
    {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : X → WeakSpace ℝ E}
    (hf : ∀ ℓ : E →L[ℝ] ℝ, Continuous fun x => ℓ (f x)) :
    Continuous f := continuous_induced_rng.2 <| continuous_pi_iff.mpr <| fun y => hf y

noncomputable def weakToWeakDual [CompleteSpace H] : WeakSpace ℝ H ≃ₗ[ℝ] WeakDual ℝ H :=
  (InnerProductSpace.toDual ℝ H).toLinearEquiv

noncomputable def weakHomeomorph [CompleteSpace H] : Homeomorph (WeakSpace ℝ H) (WeakDual ℝ H) where
  toFun := weakToWeakDual
  invFun := weakToWeakDual.symm
  left_inv := weakToWeakDual.left_inv
  right_inv := weakToWeakDual.right_inv
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro x
    have : (fun v : WeakSpace ℝ H => (weakToWeakDual v) x)
      = fun v => (InnerProductSpace.toDual ℝ H x) v := by
        ext v
        simp only [weakToWeakDual, InnerProductSpace.toDual_apply_apply]
        change (InnerProductSpace.toDual ℝ H v) x = ⟪x, v⟫
        simp only [InnerProductSpace.toDual_apply_apply]
        exact real_inner_comm x v
    simp only [this, InnerProductSpace.toDual_apply_apply]
    simp only [← topDualPairing_eq_inner]
    have : (fun v ↦ ((topDualPairing ℝ H).flip x) (@cont_inner_left H _ _ v)) =
      (fun v ↦ ((topDualPairing ℝ H).flip v) (@cont_inner_left H _ _ x)) := by
      ext v
      rw [topDualPairing_eq_inner, topDualPairing_eq_inner]
      exact congrFun (id (Eq.symm this)) v
    rw [this]
    apply WeakBilin.eval_continuous
  continuous_invFun := by
    apply WeakSpace.continuous_of_continuous_eval
    intro y
    obtain ⟨x, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective y
    have : (fun φ : WeakDual ℝ H => (InnerProductSpace.toDual ℝ H x)
        (weakToWeakDual.symm φ))
        = fun φ => φ x := by
        ext φ
        simp only [weakToWeakDual, InnerProductSpace.toDual_apply_apply]
        change ⟪x, ((InnerProductSpace.toDual ℝ H).symm φ) ⟫  = φ x
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [this]
    exact WeakDual.eval_continuous x

lemma weakHom_image_eq [CompleteSpace H] {x : H} {r : ℝ} :
  weakHomeomorph '' ((closedBall x r) : Set H) =
  toStrongDual ⁻¹' closedBall ((InnerProductSpace.toDual ℝ H) x) r := by
  ext y; constructor
  · rintro ⟨x', h1, h2⟩
    simp only [Set.mem_preimage, coe_toStrongDual, mem_closedBall];
    rw [← h2]; simp only [weakHomeomorph, weakToWeakDual, Homeomorph.homeomorph_mk_coe,
      Equiv.coe_fn_mk]
    change dist ((InnerProductSpace.toDual ℝ H) x') ((InnerProductSpace.toDual ℝ H) x) ≤ r
    simpa
  intro hy
  simp only [Set.mem_preimage, coe_toStrongDual, mem_closedBall] at hy;
  simp only [weakHomeomorph, weakToWeakDual, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    Set.mem_image, mem_closedBall]
  obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective y
  use v
  constructor
  · simp only [LinearIsometryEquiv.dist_map] at hy; exact hy
  change (InnerProductSpace.toDual ℝ H) v = (InnerProductSpace.toDual ℝ H) v
  rfl

/-
Fact 2.34: Banach-Alaoglu Bourbaki
-/
theorem closed_unit_ball_is_weakly_compact [CompleteSpace H] (x : H) (r : ℝ) :
  IsWeaklyCompact (closedBall x r) := by
  let f := InnerProductSpace.toDual ℝ H x
  obtain h := isCompact_closedBall ℝ f r
  simp only [IsWeaklyCompact]
  have ball_eq: closedBall f r = (InnerProductSpace.toDual ℝ H)'' (closedBall x r) := by simp [f]
  simp [ball_eq] at h
  obtain h' := @weakHom_image_eq _ _ _ _ x r
  rw [s_eq (closedBall x r)] at h'
  rwa [← weakHomeomorph.isCompact_image, h']

def IsWeaklySeqCompact (s : Set H) := @IsSeqCompact (WeakSpace ℝ H) _ (s : Set (WeakSpace ℝ H))

-- theorem closed_ball_is_weakly_seqcompact [SeparableSpace H] [CompleteSpace H] (x : H) (r : ℝ) :
--   IsWeaklySeqCompact (closedBall x r) := by
--   let f := InnerProductSpace.toDual ℝ H x
--   obtain h := WeakDual.isSeqCompact_closedBall ℝ H f r
--   simp [IsWeaklySeqCompact]
--   have ball_eq: closedBall f r = (InnerProductSpace.toDual ℝ H)'' (closedBall x r) := by simp [f]
--   simp [ball_eq] at h
--   obtain h' := @weakHom_image_eq _ _ _ _ x r
--   rw [s_eq (closedBall x r)] at h'
--   -- rwa [← weakHomeomorph.isCompact_image, h']
--   sorry



def IsWeaklySeqClusterPt (p : H) (x : ℕ → H):= @MapClusterPt (WeakSpace ℝ H) _ ℕ p atTop x

/--
Properties of strictly monotone functions from ℕ to ℕ
-/
lemma StrictMono.nat_id_le
  {φ : ℕ → ℕ} (h_strict : ∀ i j, i < j → φ i < φ j) : ∀ k, φ k ≥ k := by
  intro k; induction k with
  | zero => exact Nat.zero_le (φ 0)
  | succ k' ih =>
  have h_strict_at_succ : φ (k' + 1) > φ k' := h_strict k' (k' + 1) (by omega); omega

/--
Auxiliary lemma: limsup lower approximation inequality :
  `∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, x n ≥ limsup x atTop - ε`
-/
lemma limsup_spec_lower
  (x : ℕ → ℝ) (hx_bdd : ∃ M : ℝ, ∀ k : ℕ, |x k| ≤ M) :
  ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, x n ≥ limsup x atTop - ε := by
  intro ε hε N; by_contra! h_contra
  have h_le: ∀ n ≥ N, x n ≤ limsup x atTop - ε := by intro n hn; specialize h_contra n hn; linarith
  have h_eventually : ∀ᶠ n in atTop, x n ≤ limsup x atTop - ε := by
    rw [eventually_atTop]; exact ⟨N, h_le⟩
  have h_limsup_le : limsup x atTop ≤ limsup x atTop - ε := by
    rw [Filter.limsup_le_iff ?_ ?_]
    · intro y hy; filter_upwards [h_eventually] with n hn; linarith
    · rcases hx_bdd with ⟨M, hM⟩; apply Filter.IsCoboundedUnder.of_frequently_ge ?_
      · exact - M
      · rw [@frequently_atTop]; intro a; use a + 1; simp only [ge_iff_le, le_add_iff_nonneg_right,
        zero_le, true_and]; specialize hM (a + 1)
        apply abs_le.1 at hM; rcases hM with ⟨hM1, hM2⟩; assumption
    · simp only [IsBoundedUnder, IsBounded, eventually_map, eventually_atTop, ge_iff_le];
      use (limsup x atTop - ε); use N
  linarith

/--
Auxiliary lemma: limsup lower approximation inequality :
  `∀ ε > 0, ∀ᶠ n in atTop, x n ≤ limsup x atTop + ε`
-/
lemma limsup_spec_upper
  (x : ℕ → ℝ) (hx_bdd : ∃ M : ℝ, ∀ k : ℕ, |x k| ≤ M) :
  ∀ ε > 0, ∀ᶠ n in atTop, x n ≤ limsup x atTop + ε := by
    set L := limsup x atTop with hL_def
    intro ε hε; rw [Filter.eventually_atTop]; simp only [limsup, limsSup, eventually_map,
      eventually_atTop, ge_iff_le] at hL_def
    rcases hx_bdd with ⟨M, hM⟩
    have h_set_nonempty : {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → x b ≤ a}.Nonempty := by
      use M; simp only [Set.mem_setOf_eq]; use 0; simp only [zero_le, forall_const]; intro n;
      have := hM n; apply abs_le.1 at this; exact this.2
    have h_set_bdd_below : BddBelow {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → x b ≤ a} := by
      use -M - 1; intro y hy; simp only [Set.mem_setOf_eq] at hy;
      by_contra! h_contra; rcases hy with ⟨a, ha⟩
      specialize ha (a + 1); simp at ha
      have contra: x (a + 1) < -M - 1 := by linarith
      specialize hM (a + 1); apply abs_le.1 at hM; rcases hM with ⟨hM1, hM2⟩; linarith
    have h2 : L < L + ε := by linarith
    nth_rewrite 1 [hL_def] at h2
    have ⟨b, ⟨N, hN_bound⟩, hb_lt⟩ : ∃ b ∈ {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → x b ≤ a}, b < L + ε :=
      (csInf_lt_iff h_set_bdd_below h_set_nonempty).mp h2
    use N; intro n hn; specialize hN_bound n hn; linarith

/--
Auxiliary lemma: the reciprocal function tends to zero :
  `∀ ε > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, 1 / (k + 1) < ε`
-/
lemma one_div_tendsto_zero
  (ε : ℝ) (hε : ε > 0) : ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → 1 / (↑k + 1) < ε := by
  use Nat.ceil (1 / ε); intro k hk
  have hk' : (1 : ℝ) / ε ≤ k := by
    calc
      1 / ε ≤ Nat.ceil (1 / ε) := Nat.le_ceil (1 / ε)
      _ ≤ k := by norm_cast
  have hk_plus_one : (1 : ℝ) / ε < k + 1 := by linarith
  have h_pos_k : 0 < (k : ℝ) + 1 := by norm_cast; omega
  exact (one_div_lt hε h_pos_k).mp hk_plus_one

/--
lemma : Bounded real sequence has a subsequence converging to limsup :
  `∃ (φ : ℕ → ℕ) (L : ℝ), (∀ m n, m < n → φ m < φ n) ∧ (L = limsup x atTop) ∧
    (Tendsto (x ∘ φ) atTop (𝓝 L))`
-/
theorem lim_subsequence_eq_limsup
  (x : ℕ → ℝ) (hx_bdd : ∃ M : ℝ, ∀ k : ℕ, |x k| ≤ M) :
  ∃ (φ : ℕ → ℕ) (L : ℝ), (∀ m n, m < n → φ m < φ n) ∧ (L = limsup x atTop) ∧
    (Tendsto (x ∘ φ) atTop (𝓝 L)) := by
  set L := limsup x atTop with hL_def
  have h_limsup_spec := limsup_spec_lower x hx_bdd
  have h_limsup_spec' := limsup_spec_upper x hx_bdd
  -- 步骤3：递归构造严格递增子序列 φ
  have ⟨φ, ⟨hφ_mono, h_φ_lower⟩⟩ : ∃ φ : ℕ → ℕ, (∀ m n, m < n → φ m < φ n) ∧
    (∀ k, x (φ k) ≥ L - 1 / (k + 1)) := by
    let find_next (N : ℕ) (ε : ℝ) (hε_pos : 0 < ε) : ℕ := (h_limsup_spec ε hε_pos N).choose
    have h_find_next_ge : ∀ N ε (hε : 0 < ε), find_next N ε hε ≥ N := fun N ε _ =>
      (h_limsup_spec ε (by positivity) N).choose_spec.1
    have h_find_next_value : ∀ N ε (hε : 0 < ε), x (find_next N ε hε) ≥ L - ε := fun N ε _ =>
      (h_limsup_spec ε (by positivity) N).choose_spec.2
    -- 递归构造序列 φ
    let φ : ℕ → ℕ := fun k => Nat.recOn k (find_next 0 1 (by positivity))
      (fun k' φk' => find_next (φk' + 1) (1 / (k' + 2)) (by positivity))
    use φ
    constructor
    · intro m n hmn; induction n with
      | zero => omega
      | succ n' ih =>
        by_cases hm : m < n'
        · have h_ih := ih hm
          calc _ < φ n' := h_ih
            _ < φ (n' + 1) := by unfold φ; apply h_find_next_ge; positivity
        · push_neg at hm; have : m = n' := by omega
          rw [this]; unfold φ
          have : find_next (φ n' + 1) (1 / (n' + 2)) (by positivity) ≥ φ n' + 1 := by
            apply h_find_next_ge; positivity
          exact this
    · intro k; induction k with
      | zero =>
        unfold φ; have h1 : (0 : ℝ) < 1 := by norm_num
        simp only [one_div, Nat.rec_zero, CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero,
          not_false_eq_true, div_self, ge_iff_le, tsub_le_iff_right]
        exact (OrderedSub.tsub_le_iff_right L 1 (x (find_next 0 1
          (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
            (Eq.refl (Nat.ble 1 1)))))).mp (h_find_next_value 0 1 h1)
      | succ k' ih =>
        have hε_pos : (0 : ℝ) < 1 / (k' + 2) := by positivity
        have h_value := h_find_next_value (φ (Nat.recOn k' (find_next 0 1
          (by norm_num : 0 < (1 : ℝ))) (fun k'' φk'' => find_next (φk'' + 1)
            (1 / (k'' + 2)) (by positivity))) + 1) (1 / (k' + 2)) hε_pos
        calc
          _ ≥ L - 1 / (k' + 2) := by
            exact h_find_next_value (Nat.rec (find_next 0 1 (Mathlib.Meta.Positivity.pos_of_isNat
              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl (Nat.ble 1 1))))
                (fun k' φk' ↦find_next (φk' + 1) (1 / (↑k' + 2)) (div_pos
                  (Mathlib.Meta.Positivity.pos_of_isNat
                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl (Nat.ble 1 1)))
                        (Right.add_pos_of_nonneg_of_pos (Nat.cast_nonneg' k')
                          (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ
                            (Eq.refl 2)) (Eq.refl (Nat.ble 1 2)))))) k' +1) (1 / (↑k' + 2)) hε_pos
          _ = L - 1 / (↑(k' + 1) + 1) := by norm_num; ring
  use φ, L, hφ_mono, rfl; rw [Metric.tendsto_atTop]; intro ε ε_pos
  obtain ⟨N_up, hN_up⟩ := (eventually_atTop).mp (h_limsup_spec' (ε / 2) (by linarith))
  obtain ⟨k₀, hk₀⟩ := one_div_tendsto_zero ε ε_pos; have h_phi_ge := StrictMono.nat_id_le hφ_mono
  use max N_up k₀; intro k hk
  have hk_up := le_of_max_le_left hk; have hk_k₀ := le_of_max_le_right hk
  have h_upper := hN_up (φ k) (Nat.le_trans hk_up (h_phi_ge k))
  have h_lower := h_φ_lower k; have h_one_div_small := hk₀ k hk_k₀
  rw [dist_eq_norm]; simp only [Function.comp_apply, Real.norm_eq_abs, gt_iff_lt]
  apply abs_lt.2; constructor; repeat linarith

structure convergent_Subseq (x : ℕ → H) (f : ℕ → H) (m : ℕ) where
  φ : ℕ → ℕ
  monotone' : StrictMono φ
  lim : ℝ
  convergent : Tendsto (fun n => ⟪f m, x (φ n)⟫) atTop (𝓝 lim)

/--
Lemma : From a bounded sequence in H, we can extract a subsequence such that
  the inner products with a fixed vector converge : `Nonempty (convergent_Subseq x f m)`
-/
lemma extract_subseq' (x : ℕ → H) (hx : Bornology.IsBounded <| Set.range fun n => ‖x n‖)
    (f : ℕ → H) (m : ℕ) :
    Nonempty <| convergent_Subseq x f m := by
  obtain ⟨R, hR⟩ := hx.subset_closedBall 0
  have hnorm : ∀ n, ‖x n‖ ≤ R := by
    intro n; have hxmem : ‖x n‖ ∈ Set.range fun n => ‖x n‖ := ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using (hR hxmem)
  set y : ℕ → ℝ := fun n => ⟪f m, x n⟫; set B : ℝ := ‖f m‖ * R
  have hy_bounds : ∀ n, |y n| ≤ B := by
    intro n
    calc
      _ ≤ ‖f m‖ * ‖x n‖ := abs_real_inner_le_norm (f m) (x n)
      _ ≤ ‖f m‖ * R := mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg _)
      _ = B := rfl
  obtain ⟨φ, L, hφ_mono, _, h_tendsto⟩ := lim_subsequence_eq_limsup y ⟨B, hy_bounds⟩
  apply Nonempty.intro; exact ⟨φ, hφ_mono, L, h_tendsto⟩

omit [InnerProductSpace ℝ H] in
/--
Lemma : subsequence of a bounded sequence is still bounded :
  `Bornology.IsBounded (Set.range (fun n => ‖(x ∘ φ) n‖))`
-/
lemma bdd_subseq_bdd (x : ℕ → H) (hx : Bornology.IsBounded <| Set.range fun n => ‖x n‖)
  (φ : ℕ → ℕ) :
  Bornology.IsBounded <| Set.range fun n => ‖(x ∘ φ) n‖ := by
  refine hx.subset ?_; intro y hy; rcases hy with ⟨n, rfl⟩; exact ⟨φ n, rfl⟩

structure subseq_x (x : ℕ → H) where
  phi_comp : ℕ → ℕ     -- φ1 ∘ φ2 ∘ ... ∘ φm
  φ : ℕ → ℕ            -- φm
  hφ : StrictMono φ    -- φm strict mono
  hbb : Bornology.IsBounded <| Set.range (fun n => ‖(x ∘ phi_comp) n‖)  -- x ∘ phi_comp 有界
  lim : ℝ
  fm : H
  hlim : Tendsto (fun n => ⟪fm, (x ∘ phi_comp) n⟫) atTop (𝓝 lim)

def subseq_x.xφ (x : ℕ → H) (s : subseq_x x) : ℕ → H := x ∘ s.phi_comp

noncomputable def xφ (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) : ℕ → subseq_x x
| 0       => by
  have he := extract_subseq' x hx f 0
  let h := Classical.choice <| he
  have bdd := bdd_subseq_bdd x hx h.1
  exact ⟨h.1, h.1, h.2, bdd, h.3, f 0, h.4⟩
| (m + 1) => by
  have he := extract_subseq' ((xφ x hx f m).xφ) (xφ x hx f m).hbb f (m+1)
  let h := Classical.choice <| he
  have bdd := bdd_subseq_bdd ((xφ x hx f m).xφ) (xφ x hx f m).hbb h.1
  exact ⟨(xφ x hx f m).phi_comp ∘ h.1, h.1, h.2, bdd, h.3, f (m+1), h.4⟩


/--
Properties of ∘ : `∀ m, φ0 ∘ φ1 ∘ φ2 ∘ ⋯ ∘ φ(m+1) = (φ0 ∘ φ1 ∘ φ2 ∘ ⋯ ∘ φm) ∘ φ(m+1)`
-/
lemma phi_comp_eq (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  (xφ x hx f (m+1)).phi_comp = ((xφ x hx f m).phi_comp) ∘ ((xφ x hx f (m+1)).φ) :=
  match m with
  | 0 => rfl
  | (_ + 1) => rfl

/--
Properties of `φ` : `∀ m, φm is StrictMono.`
-/
lemma phim_mono (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  StrictMono (xφ x hx f m).φ := (xφ x hx f m).hφ

/--
The definition of the diagonal subsequence of x :
  `φ_diag = φ0 ∘ φ1 ∘ φ2 ∘ ⋯`
-/
noncomputable def phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H)
  : ℕ → ℕ := fun (n:ℕ) => (xφ x hx f n).phi_comp n

/--
The maintain of strictmono : `φ0 ∘ φ1 ∘ φ2 ∘ ⋯ ∘ φm is StrictMono`
-/
lemma StrictMono_phi_comp (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ)
  : StrictMono (xφ x hx f m).phi_comp := by
  induction' m with k hk
  · exact (xφ x hx f 0).hφ
  · rw [phi_comp_eq]; apply StrictMono.comp hk <| phim_mono x hx f (k + 1)

/--
Properties of strictmono function : `∀ n, n < φ (n + 1)`
-/
lemma StrictMono_nge (x : ℕ → ℕ) (hx : StrictMono x) (n : ℕ) : n < x (n + 1) := by
  have hle : ∀ k, k ≤ x k := by
    intro k
    induction' k with k hk
    · exact Nat.zero_le _
    · have h₁ : k + 1 ≤ x k + 1 := Nat.succ_le_succ hk
      have h₂ : x k + 1 ≤ x (k + 1) := Nat.succ_le_of_lt (hx (Nat.lt_succ_self k))
      exact h₁.trans h₂
  have hn1 : n + 1 ≤ x (n + 1) := hle (n + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn1

/--
Properties of strictmono function : `n, φ_diag n ≥ n`
-/
lemma StrictMono_phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H)
  : StrictMono <| phi_diag x hx f := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  simp only [phi_diag]
  rw [phi_comp_eq x hx f n]
  have h : n < (xφ x hx f (n + 1)).φ (n + 1) := by
    refine StrictMono_nge (xφ x hx f (n + 1)).φ ?_ n
    exact phim_mono x hx f (n + 1)
  exact StrictMono_phi_comp x hx f n h


omit [InnerProductSpace ℝ H] in
/--
Properties of bounded sequences : there exists an upper bound `M > 0` such that `∀ n, ‖x n‖ ≤ M`
-/
lemma bdd_iff_exist_bound (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) :
  ∃ M > 0, ∀ n, ‖x n‖ ≤ M := by
  obtain ⟨R, hR⟩ := hx.subset_closedBall 0
  refine ⟨max 1 R, (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro n; have hx_mem : ‖x n‖ ∈ Set.range fun n => ‖x n‖ := ⟨n, rfl⟩
  have hx_dist : dist (‖x n‖) 0 ≤ R := by simpa [Metric.closedBall] using hR hx_mem
  have hx_le : ‖x n‖ ≤ R := by simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hx_dist
  exact hx_le.trans (le_max_right _ _)

/--
Properties of bounded sequences : `∀ n, ‖(x ∘ φ_diag) n‖` is bounded
-/
lemma upperbdd_phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H)
  : ∃ M > 0, ∀ n, ‖(x ∘ (phi_diag x hx f)) n‖ ≤ M := by
  have h := bdd_subseq_bdd x hx (phi_diag x hx f)
  exact bdd_iff_exist_bound (x ∘ phi_diag x hx f) h

/--
Limit of the inner product between m-th line element and :
  `∀ m : ℕ, Tendsto (fun n => ⟪f m, (x ∘ φ0 ∘ ⋯ ∘ φm) n⟫) atTop (nhds (a m))`
-/
lemma converge_inner_subseq_fm (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  Tendsto (fun n => ⟪f m, ((xφ x hx f m).xφ) n⟫) atTop (𝓝 (xφ x hx f m).lim) := by
  match m with
  | 0 => exact (xφ x hx f 0).hlim
  | k + 1 => exact (xφ x hx f (k + 1)).hlim

/--
The elements in (m+1)-th subsequence are also in m-th subsequence :
  `∀ m : ℕ, Set.range (x ∘ φ0 ∘ ⋯ ∘ φ(m+1)) ⊆ Set.range (x ∘ φ0 ∘ ⋯ ∘ φm)`
-/
lemma xφ_succ_range_subset (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ) :
  Set.range (fun k => ((xφ x hx f (m + 1)).xφ) k) ⊆
  Set.range (fun k => ((xφ x hx f m).xφ) k) := by
  intro y hy; rcases hy with ⟨j, rj⟩; rw [← rj]; unfold subseq_x.xφ
  rw [phi_comp_eq x hx f m]
  simp only [Function.comp_apply]
  use ((xφ x hx f (m + 1)).φ) j

/--
The elements in n-th subsequence are also in m-th subsequence when n ≥ m :
  `∀ m : ℕ, Set.range (x ∘ φ0 ∘ ⋯ ∘ φ(n)) ⊆ Set.range (x ∘ φ0 ∘ ⋯ ∘ φm)`
-/
lemma xφ_range_subset (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ) :
  ∀ n ≥ m, Set.range (fun k => ((xφ x hx f n).xφ) k) ⊆
  Set.range (fun k => ((xφ x hx f m).xφ) k) := by
  intro n hn
  induction n, hn using Nat.le_induction with
    | base =>
      rfl
    | succ n' hn' ih =>
      have h_subset := xφ_succ_range_subset x hx f n'
      exact Set.Subset.trans h_subset ih

/--
The n_th elements in the diagonal subsequence are also in m-th subsequence when n ≥ m :
  `∀ n ≥ m, x (phi_diag x hx f n) ∈ Set.range (fun k => ((xφ x hx f m).xφ) k)`
-/
lemma phi_diag_in_xφ_image (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ) :
  ∀ n ≥ m, x (phi_diag x hx f n) ∈ Set.range (fun k => ((xφ x hx f m).xφ) k) := by
  intro n hn; unfold phi_diag
  have h_in_n_range : x ((xφ x hx f n).phi_comp n) ∈
    Set.range (fun k => ((xφ x hx f n).xφ) k) := by
    unfold subseq_x.xφ; use n; simp
  have h_subset := xφ_range_subset x hx f m n hn
  exact h_subset h_in_n_range

/--
Properties of indexes between successive subsequences :
  `∀ k, ∃ j ≥ k, ((xφ x hx f (m + 1)).xφ k = ((xφ x hx f m).xφ j)`
-/
lemma xφ_succ_indices_ge (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ) :
  ∀ k, ∃ j ≥ k, ((xφ x hx f (m + 1)).xφ) k = ((xφ x hx f m).xφ) j := by
  intro k; unfold subseq_x.xφ; rw [phi_comp_eq x hx f m]
  simp only [Function.comp_apply]
  have h_φ_ge : (xφ x hx f (m + 1)).φ k ≥ k := by
    have h_strict := phim_mono x hx f (m + 1)
    exact StrictMono.nat_id_le h_strict k
  use (xφ x hx f (m + 1)).φ k, h_φ_ge

/--
Properties of indexes between two subsequences :
  `∀ n ≥ m, ∀ k, ∃ j ≥ k, ((xφ x hx f n).xφ k = ((xφ x hx f m).xφ j)`
-/
lemma xφ_indices_ge (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) (f : ℕ → H) (m : ℕ) :
  ∀ n ≥ m, ∀ k, ∃ j ≥ k, ((xφ x hx f n).xφ) k = ((xφ x hx f m).xφ) j := by
  intro n hn; induction n, hn using Nat.le_induction with
  | base => intro k; use k, le_refl k
  | succ n' hn' ih =>
    intro k; obtain ⟨j', hj'_ge, hj'_eq⟩ := ih k
    obtain ⟨j'', hj''_ge, hj''_eq⟩ := xφ_succ_indices_ge x hx f n' j'
    have ⟨j'_0, hj'_0_ge, hj'_0_eq⟩ : ∃ j' ≥ k, ((xφ x hx f (n' + 1)).xφ) k
      = ((xφ x hx f n').xφ) j' := xφ_succ_indices_ge x hx f n' k
    obtain ⟨j''_0, hj''_0_ge, hj''_0_eq⟩ := ih j'_0; use j''_0
    constructor
    · linarith
    · calc
        _ = ((xφ x hx f n').xφ) j'_0 := hj'_0_eq
        _ = ((xφ x hx f m).xφ) j''_0 := hj''_0_eq

/--
The limit of the inner product between the element on the diagonal sequence and f m :
  `∀ m ≥ n, Tendsto (fun n => ⟪f m, (x ∘ φ) n⟫) atTop (nhds (a m))`
-/
lemma converge_inner_subseq_fm_phi_diag (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (m : ℕ) :
  Tendsto (fun n => ⟪f m, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (xφ x hx f m).lim) := by
  have h_in_range := phi_diag_in_xφ_image x hx f m
  -- 步骤2：因此存在 k_n 使得 x (phi_diag x hx f n) = ((xφ x hx f m).xφ) k_n
  have h_exists_k : ∀ n ≥ m, ∃ k ≥ n, x (phi_diag x hx f n) = ((xφ x hx f m).xφ) k := by
    intro n hn; unfold phi_diag
    have ⟨j, hj_ge, hj_eq⟩ := xφ_indices_ge x hx f m n hn n
    have h_xφ_def : ((xφ x hx f n).xφ) n = x ((xφ x hx f n).phi_comp n) := by
      unfold subseq_x.xφ
      simp
    use j, hj_ge
    rw [← h_xφ_def, hj_eq]
  -- 步骤3：定义一个子列索引函数 ψ
  let ψ : ℕ → ℕ := fun n => (h_exists_k (m + n) (by linarith)).choose
  have h_ψ_ge : ∀ n, ψ n ≥ n := by
    intro n
    have : ψ n ≥ m + n := by
      simp only [ge_iff_le] at h_exists_k
      exact (h_exists_k (m + n) (by linarith)).choose_spec.1
    linarith
  -- 步骤4：我们知道 ⟪f m, (x ∘ (phi_diag x hx f)) (m + n)⟫ = ⟪f m, ((xφ x hx f m).xφ) (ψ n)⟫
  have h_eq_xφ : ∀ n, ⟪f m, (x ∘ (phi_diag x hx f)) (m + n)⟫ =
    ⟪f m, ((xφ x hx f m).xφ) (ψ n)⟫ := by
    intro n
    have := (h_exists_k (m + n) (by linarith)).choose_spec
    simp only [ge_iff_le] at this
    exact congrArg (inner ℝ (f m)) this.2
  -- 步骤5：⟪f m, ((xφ x hx f m).xφ) (ψ n)⟫ 是 ⟪f m, ((xφ x hx f m).xφ) k⟫ 的子列
  -- 而 ⟪f m, ((xφ x hx f m).xφ) k⟫ 收敛到 (xφ x hx f m).lim
  have h_base_conv : Tendsto (fun k => ⟪f m, ((xφ x hx f m).xφ) k⟫) atTop
    (𝓝 (xφ x hx f m).lim) := converge_inner_subseq_fm x hx f m
  -- 步骤6：子列也收敛到相同的极限
  have h_subseq_conv : Tendsto (fun n => ⟪f m, ((xφ x hx f m).xφ) (ψ n)⟫) atTop
    (𝓝 (xφ x hx f m).lim) := by
    apply Tendsto.comp h_base_conv ?_
    rw [tendsto_atTop_atTop]
    intro S
    use S
    intro n hn
    specialize h_ψ_ge n
    linarith
  -- 步骤7：通过等式转换回原始序列（从 m 开始的平移）
  have h_shifted : Tendsto (fun n => ⟪f m, (x ∘ (phi_diag x hx f)) (m + n)⟫) atTop
    (𝓝 (xφ x hx f m).lim) := by
    convert h_subseq_conv using 1
    ext n
    exact h_eq_xφ n
  -- 步骤8：原始序列的收敛性等价于平移序列的收敛性
  have h_equiv : Tendsto (fun n => ⟪f m, (x ∘ (phi_diag x hx f)) n⟫) atTop
    (𝓝 (xφ x hx f m).lim) ↔
    Tendsto (fun n => ⟪f m, (x ∘ (phi_diag x hx f)) (m + n)⟫) atTop
    (𝓝 (xφ x hx f m).lim) := by
    constructor
    · intro h; exact h_shifted
    · intro h; rw [Metric.tendsto_atTop]; intro ε hε; rw [Metric.tendsto_atTop] at h_shifted
      obtain ⟨N, hN⟩ := h_shifted ε hε; use N + m; intro n hn; specialize hN (n - m)
      have h_n_ge_m : n ≥ m := by omega
      have : n - m + m = n := by omega
      rw [← this] at hN
      have hN_apply : (n - m) ≥ N := by omega
      simp only [ge_iff_le, Set.mem_range, Function.comp_apply, gt_iff_lt,
        add_tsub_cancel_right] at *
      convert hN hN_apply
      linarith
  exact h_equiv.mpr h_shifted

/--
For any point in the space the inner product is a Cauchy sequence :
  `∀ y : H, CauchySeq (fun n => ⟪y, (x ∘ φ_diag) n⟫)`
-/
lemma dense_f_forall (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) :
  ∀ y : H, CauchySeq (fun n => ⟪y, (x ∘ (phi_diag x hx f)) n⟫) := by
  intro y; simp only [Function.comp_apply, Metric.cauchySeq_iff, gt_iff_lt, ge_iff_le]; intro ε hε
  obtain ⟨M, hM_pos, hM⟩ := bdd_iff_exist_bound (x ∘ phi_diag x hx f)
    (bdd_subseq_bdd x hx (phi_diag x hx f))
  have h_eps_pos : 0 < ε / (3 * M + 1) := by positivity
  have ⟨fk, hfk_in_ball, hfk_in_f⟩ := Metric.dense_iff.mp hf y (ε / (3 * M + 1)) h_eps_pos
  have hfk_eq : ∃ k, fk = f k := by
    obtain ⟨k, hk⟩ := hfk_in_f; use k; rw [hk]
  obtain ⟨k, rfl⟩ := hfk_eq
  have h_fk_conv : Tendsto (fun n => ⟪f k, (x ∘ (phi_diag x hx f)) n⟫) atTop
    (𝓝 (xφ x hx f k).lim) := converge_inner_subseq_fm_phi_diag x hx f k
  have h_fk_cauchy : CauchySeq (fun n => ⟪f k, (x ∘ (phi_diag x hx f)) n⟫) :=
    Tendsto.cauchySeq h_fk_conv
  rw [Metric.cauchySeq_iff] at h_fk_cauchy
  obtain ⟨N, hN⟩ := h_fk_cauchy (ε / 3) (by linarith); use N; intro m hm n hn
  have h_tri : dist ⟪y, (x ∘ (phi_diag x hx f)) m⟫ ⟪y, (x ∘ (phi_diag x hx f)) n⟫
    ≤ dist ⟪y, (x ∘ (phi_diag x hx f)) m⟫ ⟪f k, (x ∘ (phi_diag x hx f)) m⟫
      + dist ⟪f k, (x ∘ (phi_diag x hx f)) m⟫ ⟪f k, (x ∘ (phi_diag x hx f)) n⟫
      + dist ⟪f k, (x ∘ (phi_diag x hx f)) n⟫ ⟪y, (x ∘ (phi_diag x hx f)) n⟫ :=
    by simp only [Function.comp_apply]; exact dist_triangle4 _ _ _ _
  -- 估计第一项：|⟪y - f k, x(φ m)⟫| < ε/3
  have h_term : ∀ m, dist ⟪y, (x ∘ (phi_diag x hx f)) m⟫
    ⟪f k, (x ∘ (phi_diag x hx f)) m⟫ < ε / 3 := by
    intro p; simp only [Function.comp_apply, dist_eq_norm]
    rw [show ⟪y, x (phi_diag x hx f p)⟫ - ⟪f k, x (phi_diag x hx f p)⟫ =
      ⟪y - f k, x (phi_diag x hx f p)⟫ by rw [← inner_sub_left]]
    calc
      _ ≤ ‖y - f k‖ * ‖x (phi_diag x hx f p)‖ := by apply abs_real_inner_le_norm
      _ ≤  (ε / (3 * M + 1)) * M := by
        apply mul_le_mul ?_ (hM p) (norm_nonneg (x (phi_diag x hx f p))) (by linarith)
        · simp only [ball, dist_eq_norm, ← norm_sub_rev, Set.mem_setOf_eq] at hfk_in_ball ⊢
          calc
            _ = ‖y - f k‖ := by rw [norm_sub_rev]
            _ ≤ ε / (3 * M + 1) := by linarith [hfk_in_ball]
      _ < ε / 3 := by
        rw [div_eq_mul_one_div]; nth_rewrite 2 [div_eq_mul_one_div]; rw [mul_assoc]
        apply mul_lt_mul_of_pos_left
        · field_simp
          linarith
        · exact hε
  have h_term1 := h_term m; have h_term1' := h_term n; rw [dist_comm] at h_term1'
  -- 估计第二项：|⟪f k, x(φ m)⟫ - ⟪f k, x(φ n)⟫| < ε/3
  have h_term2 : dist ⟪f k, (x ∘ (phi_diag x hx f)) m⟫
    ⟪f k, (x ∘ (phi_diag x hx f)) n⟫ < ε / 3 := by
    specialize hN m hm n hn;
    simp only [Function.comp_apply, dist_eq_norm, Real.norm_eq_abs] at hN; exact hN
  -- 综合三项
  calc dist ⟪y, (x ∘ (phi_diag x hx f)) m⟫ ⟪y, (x ∘ (phi_diag x hx f)) n⟫
      ≤ dist ⟪y, (x ∘ (phi_diag x hx f)) m⟫ ⟪f k, (x ∘ (phi_diag x hx f)) m⟫
        + dist ⟪f k, (x ∘ (phi_diag x hx f)) m⟫ ⟪f k, (x ∘ (phi_diag x hx f)) n⟫
        + dist ⟪f k, (x ∘ (phi_diag x hx f)) n⟫ ⟪y, (x ∘ (phi_diag x hx f)) n⟫ := h_tri
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/--
For any point in the space the inner product converges :
  `∀ y : H, ∃ a : ℝ, Tendsto (fun n => ⟪y, (x ∘ φ) n⟫) atTop (nhds a)`
-/
lemma dense_f_forall_exist_lim (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) :
  ∀ y : H, ∃ a : ℝ, Tendsto (fun n => ⟪y, (x ∘ (phi_diag x hx f)) n⟫) atTop (nhds a):= by
  intro y; apply cauchySeq_tendsto_of_complete; exact dense_f_forall x hx f hf y

/--
Definition of the linear map y_linearmap
-/
def y_linearmap (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) :
  IsLinearMap ℝ (fun y => Classical.choose <| dense_f_forall_exist_lim x hx f hf y) where
  map_add := by
    intro a b
    let lima := Classical.choose <| dense_f_forall_exist_lim x hx f hf a
    let limb := Classical.choose <| dense_f_forall_exist_lim x hx f hf b
    let limab := Classical.choose <| dense_f_forall_exist_lim x hx f hf (a+b)
    change limab = lima + limb
    have ha : Tendsto (fun n ↦ ⟪a, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (lima))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf a)
    have hb : Tendsto (fun n ↦ ⟪b, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limb))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf b)
    have hab : Tendsto (fun n ↦ ⟪a + b, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limab))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf (a + b))
    have h_add_inner : (fun n ↦ ⟪a + b, (x ∘ (phi_diag x hx f)) n⟫) =
      fun n ↦ ⟪a, (x ∘ (phi_diag x hx f)) n⟫ + ⟪b, (x ∘ (phi_diag x hx f)) n⟫ := by
      ext n; exact inner_add_left a b ((x ∘ (phi_diag x hx f)) n)
    rw [h_add_inner] at hab
    have h_tendsto_add : Tendsto
      (fun n ↦ ⟪a, (x ∘ (phi_diag x hx f)) n⟫ + ⟪b, (x ∘ (phi_diag x hx f)) n⟫)
      atTop (𝓝 (lima + limb)) := Tendsto.add ha hb
    exact tendsto_nhds_unique hab h_tendsto_add
  map_smul := by
    intro c y
    let limy := Classical.choose <| dense_f_forall_exist_lim x hx f hf y
    let limcy := Classical.choose <| dense_f_forall_exist_lim x hx f hf (c • y)
    change limcy = c * limy
    have hy : Tendsto (fun n ↦ ⟪y, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limy))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf y)
    have hb : Tendsto (fun n ↦ ⟪c • y, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limcy))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf (c • y))
    have h_smul_inner : (fun n ↦ ⟪c • y, (x ∘ (phi_diag x hx f)) n⟫) =
      fun n ↦ c * ⟪y, (x ∘ (phi_diag x hx f)) n⟫ := by
      ext n; exact real_inner_smul_left y ((x ∘ phi_diag x hx f) n) c
    rw [h_smul_inner] at hb
    have h_tendsto_smul : Tendsto
      (fun n ↦ c * ⟪y, (x ∘ (phi_diag x hx f)) n⟫)
      atTop (𝓝 (c * limy)) := by
      exact Tendsto.const_mul c hy
    exact tendsto_nhds_unique hb h_tendsto_smul

/--
The limit of the inner product is upper bounded :
  `|a| ≤ M * ‖y‖`
-/
lemma tendsto_upper_bdd (x : ℕ → H) (M : ℝ)
  (hx : ∀ n, ‖x n‖ ≤ M) (a : ℝ)
  (y : H) (hc : Tendsto (fun n => ⟪y, x n⟫) atTop (nhds a)) :
  |a| ≤ M * ‖y‖ := by
  have hbound : ∀ n, |⟪y, x n⟫| ≤ M * ‖y‖ := by
    intro n
    calc
      _ ≤ ‖y‖ * ‖x n‖ := abs_real_inner_le_norm y (x n)
      _ ≤ ‖y‖ * M := mul_le_mul_of_nonneg_left (hx n) (norm_nonneg _)
      _ = M * ‖y‖ := CommMonoid.mul_comm ‖y‖ M
  exact (isClosed_le continuous_abs continuous_const).mem_of_tendsto hc
    (Eventually.of_forall hbound)

/--
The definition of the strong dual element y_StrongDual
-/
noncomputable def y_StrongDual (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖))
  (f : ℕ → H) (hf : Dense (Set.range f)) : StrongDual ℝ H where
  toFun := fun y => Classical.choose <| dense_f_forall_exist_lim x hx f hf y
  map_add' := (y_linearmap x hx f hf).1
  map_smul' := (y_linearmap x hx f hf).2
  cont := by
    apply @IsBoundedLinearMap.continuous ℝ _ H
    refine { toIsLinearMap := ?_, bound := ?_ }
    · exact y_linearmap x hx f hf
    rcases (upperbdd_phi_diag x hx f) with ⟨M1,hM1,hxn⟩
    use M1, hM1
    intro y
    let limy := Classical.choose <| dense_f_forall_exist_lim x hx f hf y
    change |limy| ≤ M1 * ‖y‖
    have hy : Tendsto (fun n ↦ ⟪y, (x ∘ (phi_diag x hx f)) n⟫) atTop (𝓝 (limy))
      := Classical.choose_spec (dense_f_forall_exist_lim x hx f hf y)
    exact tendsto_upper_bdd (fun n ↦ (x ∘ (phi_diag x hx f)) n) M1 hxn limy y hy

/-
Lemma 2.45 : Any bounded sequence in a separable and
  complete inner product space has a weakly convergent subsequence.
-/
theorem bounded_seq_has_weakly_converge_subseq_separable [SeparableSpace H]
  [CompleteSpace H] (x : ℕ → H)
  (hx : Bornology.IsBounded <| Set.range (fun n => ‖x n‖)) :
  ∃ (a : H), ∃ φ, StrictMono φ ∧ WeakConverge (x ∘ φ) a := by
  rcases exists_countable_dense H with ⟨s, hs1, hs2⟩
  have hsn : s.Nonempty := Dense.nonempty hs2
  rcases Set.Countable.exists_eq_range hs1 hsn with ⟨f, hf⟩
  let φ := phi_diag x hx f
  have hdense : Dense (Set.range f) := by rwa [hf] at hs2
  let yh := dense_f_forall_exist_lim x hx f hdense
  choose fy hhh using yh; obtain sφ := StrictMono_phi_diag x hx f
  obtain ⟨a, h⟩ := (InnerProductSpace.toDual ℝ H).surjective (y_StrongDual x hx f hdense)
  have hy (y : H) : (y_StrongDual x hx f hdense).toFun y = ((InnerProductSpace.toDual ℝ H) a) y
    := by exact congrFun (congrArg AddHom.toFun (congrArg LinearMap.toAddHom
      (congrArg ContinuousLinearMap.toLinearMap (id (Eq.symm h))))) y
  have hy2 (y : H): ⟪a,y⟫ = (y_StrongDual x hx f hdense).toFun y := by
    specialize hy y
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe,
      InnerProductSpace.toDual_apply_apply] at hy
    symm
    exact hy
  have xφc : WeakConverge (x ∘ φ) a := by
    refine (weakConverge_iff_inner_converge (x ∘ φ) a).mpr ?_; intro y; rw [hy2]
    simp only [real_inner_comm]
    exact Classical.choose_spec (dense_f_forall_exist_lim x hx f hdense y)
  exact ⟨a, φ, sφ, xφc⟩

/--
Monotonicity of weak sequential compactness :
  `s ⊆ t` and `t` is weakly sequentially compact implies `s` is weakly sequentially compact
-/
lemma IsWeaklySeqCompact_mono {s t : Set H}
  (x : ℕ → H) (hx : ∀ n : ℕ, x n ∈ s):
  (IsWeaklySeqCompact t) → s ⊆ t → ∃ a, ∃ φ, StrictMono φ ∧ WeakConverge (x ∘ φ) a := by
  intro ht hsub
  simp only [IsWeaklySeqCompact, IsSeqCompact] at ht ⊢
  have hx' : ∀ n : ℕ, x n ∈ t := fun n => hsub (hx n)
  have := ht hx'
  rcases this with ⟨a, ha_in_t, φ, hφ_strict, hφ_conv⟩
  use a, φ, hφ_strict, hφ_conv

end WeaklyCompact
