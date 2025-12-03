import Mathlib.Analysis.InnerProductSpace.ProdL2
import FormalizationFixpointIterations.Nonexpansive.Definitions
import FormalizationFixpointIterations.Theory.WeakSpace
import Mathlib.Tactic
import Mathlib.Util.Delaborators

open Set Filter Topology
open BigOperators Finset Function
open Nonexpansive_operator  --命名空间

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Fejér 单调性的定义
def IsFejerMonotone (x : ℕ → H) (C : Set H) : Prop :=
  ∀ y ∈ C, ∀ n, ‖x (n + 1) - y‖ ≤ ‖x n - y‖

-- Krasnosel'skii-Mann 迭代结构
structure KM (D : Set H) (T : H → H) where
  x0 : H
  hx0 : x0 ∈ D
  stepsize : ℕ → ℝ
  hstepsize : ∀ n, stepsize n ∈ Set.Icc (0 : ℝ) 1
  hstepsize_sum : Tendsto (fun n => ∑ i ∈ range (n+1), stepsize i * (1 - stepsize i)) atTop atTop
  x : ℕ → H
  update : ∀ n, x (n + 1) = x n + stepsize n • (T (x n) - x n)
  initial_value : x 0 = x0
  fix_T_nonempty : (Fix' T D).Nonempty

-- 引理 2.15: for x,y ∈ H and α ∈ ℝ,
-- ‖α x + (1-α) y‖^2 + α(1-α)‖x - y‖^2 = α‖x‖^2 + (1-α)‖y‖^2
lemma Corollary_2_15 (x y : H) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 = α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  -- rewrite the squared norms as inner products
  rw [← real_inner_self_eq_norm_sq (α • x + (1 - α) • y), ← real_inner_self_eq_norm_sq (x - y),
    ← real_inner_self_eq_norm_sq x, ← real_inner_self_eq_norm_sq y]
  have h1 : inner ℝ (α • x + (1 - α) • y) (α • x + (1 - α) • y) =
      α ^ 2 * inner ℝ x x + 2 * α * (1 - α) * inner ℝ x y + (1 - α) ^ 2 * inner ℝ y y := by
    simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  have h2 : inner ℝ (x - y) (x - y) = inner ℝ x x - 2 * inner ℝ x y + inner ℝ y y := by
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  rw [h1, h2]
  ring

example (T : H → H) (D : Set H) (Fix_T_nonempty : (Fix' T D).Nonempty) :∃ y ∈ D,  T y =y:= by
  rcases Fix_T_nonempty with ⟨y, hy⟩
  dsimp [Fix'] at hy
  rcases hy with ⟨ hyD,hyFix⟩
  use y
  constructor
  · exact hyD
  · exact hyFix

--ε N 语言化 收敛性
lemma Converge_iff (u : ℕ → ℝ) (x0 : ℝ) :
Tendsto u atTop (𝓝 x0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x0 - ε) (x0 + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x0)]
  simp

def IsWeaklyClusterPoint (x : H) (F : Filter H) := @ClusterPt (WeakSpace ℝ H) _
 (x : (WeakSpace ℝ H)) (F:Filter (WeakSpace ℝ H))

#check id
def IsWeaklySeqClusterPt' (p : H) (x : ℕ → H):=
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    WeakConverge (fun n => (x (φ n))) p

#check weakConverge_iff_inner_converge

--引理:数列x与p的内积收敛,则子数列与p的内积也收敛
--Tendsto (fun n =>⟪x n, p⟫) atTop 𝓝 l,则 Tendsto (fun n =>⟪x (φ n), p⟫) atTop 𝓝 l
lemma weakConverge_subseq {x : ℕ → H} {p : H} {φ : ℕ → ℕ} (hφ : StrictMono φ) (l : ℝ)
(hconv : Tendsto (fun n => ⟪x n, p⟫) atTop (𝓝 l)) :
  Tendsto (fun n =>⟪x (φ n), p⟫) atTop (𝓝 l) := by
  apply Filter.Tendsto.comp hconv
  exact StrictMono.tendsto_atTop hφ

--引理: 数列x弱收敛至p, 则p为x的弱聚点
lemma WeakConverge_is_ClusterPt (x : ℕ → H) (p : H) (hconv : WeakConverge x p) :
  IsWeaklySeqClusterPt' p x := by
  use id
  constructor
  · exact fun(x y hxy) => hxy
  exact hconv


lemma Lemma_2_46_backword (x : ℕ → H) (h_bounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M)
(h_atmost_one_cluster : ∀ p q : H,  IsWeaklySeqClusterPt' p x → IsWeaklySeqClusterPt' q x → p = q) : ∃ p0 : H, WeakConverge x p0 := by
  sorry

--(2.32)等式
lemma prop_2_32 (x : ℕ → H) (p q : H) :
∀ n : ℕ ,2*⟪x n,p-q⟫ =‖ x n -q‖ ^2-‖ x n -p‖ ^2+‖p‖^2-‖q‖^2 :=by
  intro n
  symm
  calc
    ‖ x n -q‖ ^2-‖ x n -p‖ ^2+‖p‖^2-‖q‖^2=
      ⟪ x n -q, x n -q⟫ - ⟪ x n -p, x n -p⟫ + ⟪p, p⟫ - ⟪q, q⟫ := by
        rw [real_inner_self_eq_norm_sq (x n - q), real_inner_self_eq_norm_sq (x n - p),
          real_inner_self_eq_norm_sq p, real_inner_self_eq_norm_sq q]
    _= 2*⟪x n,p-q⟫ := by
      simp [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
--(2.32)转化为极限形式
lemma prop_2_32_lim (x : ℕ → H) (p q : H) (lim_p lim_q : ℝ) (norm_p_2 : Tendsto (fun n ↦ ‖x n - p‖ ^ 2) atTop (𝓝 (lim_p ^ 2)))
(norm_q_2 : Tendsto (fun n ↦ ‖x n - q‖ ^ 2) atTop (𝓝 (lim_q ^ 2))) :
∃ l: ℝ ,Tendsto (fun n => ⟪x n,p-q⟫) atTop (𝓝 (l)) :=by
  use 1/2*((lim_q ^ 2)-(lim_p ^ 2)+‖p‖^2-‖q‖^2)
  have h2 : Tendsto (fun n => ‖x n -q‖ ^2-‖ x n -p‖ ^2+‖p‖^2-‖q‖^2) atTop
    (𝓝 ( (lim_q ^ 2)-(lim_p ^ 2)+‖p‖^2-‖q‖^2)) := by
    apply Tendsto.sub
    · apply Tendsto.add
      apply Tendsto.sub
      · exact norm_q_2
      · exact norm_p_2
      · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have h1 : Tendsto (fun n => 2*⟪x n,p-q⟫) atTop (𝓝 ((lim_q ^ 2)-(lim_p ^ 2)+‖p‖^2-‖q‖^2)) :=by
    apply Tendsto.congr (fun n => (prop_2_32 x p q n).symm) h2
  have :=h1.const_mul (1/2)
  simpa using this


#check Filter.Tendsto.mul_const
lemma Lemma_2_47 (C : Set H) (h_C_nonempty : C.Nonempty) (x : ℕ → H)
(h_converge : ∀ a ∈ C, ∃ lim_A : ℝ, Tendsto (fun n ↦ ‖x n - a‖) atTop (𝓝 lim_A))
(h_weak_cluster_in : ∀ p : H,  IsWeaklySeqClusterPt' p x → p ∈ C) : ∃ p0 ∈ C, WeakConverge x p0 := by
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
  have h_atmost_one_cluster : ∀ p q : H,  IsWeaklySeqClusterPt' p x → IsWeaklySeqClusterPt' q x → p = q := by
    intro p q h_cluster_p h_cluster_q
    have hp_in_C : p ∈ C := h_weak_cluster_in p h_cluster_p
    have hq_in_C : q ∈ C := h_weak_cluster_in q h_cluster_q
    rcases h_converge p hp_in_C with ⟨lim_p, norm_tendsto_p⟩
    have norm_p_2:=norm_tendsto_p.pow 2  --范数平方也收敛
    rcases h_converge q hq_in_C with ⟨lim_q, norm_tendsto_q⟩
    have norm_q_2:=norm_tendsto_q.pow 2
    rcases h_cluster_p with ⟨k, hk, hconv_p⟩ --这里的k和l为子列下标函数
    rcases h_cluster_q with ⟨l, hl, hconv_q⟩
    rw [weakConverge_iff_inner_converge (fun n ↦ x (k n)) p] at hconv_p
    rw [weakConverge_iff_inner_converge (fun n ↦ x (l n)) q] at hconv_q
    rcases prop_2_32_lim x p q lim_p lim_q norm_p_2 norm_q_2 with ⟨L, tendsto_L⟩ --用上面命题
    have hL1 :=weakConverge_subseq hk L tendsto_L --两个子列也收敛到L
    have hL2 :=weakConverge_subseq hl L tendsto_L
    have h1:=tendsto_nhds_unique (hconv_p (p-q)) hL1 --极限唯一性
    have h2:=tendsto_nhds_unique (hconv_q (p-q)) hL2
    have h3 : inner ℝ (p - q) (p - q) = 0 := by
      rw [inner_sub_left, h1, h2, sub_self]
    rwa [inner_self_eq_zero,sub_eq_zero] at h3
  obtain ⟨p0, hp0 ⟩  := Lemma_2_46_backword x h_bounded h_atmost_one_cluster
  have hp0_in_C : p0 ∈ C := h_weak_cluster_in p0 (WeakConverge_is_ClusterPt x p0 hp0)
  exact ⟨p0, hp0_in_C, hp0⟩


#check isGLB_ciInf

--Proposition 5.4 (i)和(ii)的形式化
lemma Prop_5_04_i_ii (C : Set H) (h_C_nonempty : C.Nonempty) (x : ℕ → H)
(h_fejer : IsFejerMonotone x C) :
(∃ M:ℝ , ∀ n, ‖x n‖ ≤ M)
∧ (∀ a ∈ C, ∃ lim_inf : ℝ, Tendsto (fun n ↦ ‖x n - a‖) atTop (𝓝 lim_inf)) := by
  rcases h_C_nonempty with ⟨y0, hy0⟩
  --证明有界性
  let M := ‖y0‖ + ‖x 0 - y0‖
  constructor
  · use M
    · intro n
      have h1 : ‖x n - y0‖ ≤ ‖x 0 - y0‖ := by
        induction' n with i hi
        · simp
        · apply le_trans (h_fejer y0 hy0 i) hi
      have h2 : ‖x n‖ ≤ ‖x n - y0‖ + ‖y0‖ := by
        apply norm_le_norm_sub_add
      linarith
  --证明极限存在性  --单调有界
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
  use 0  --证明0 ∈ lowerBounds (Set.range fun n ↦ ‖x n - a‖) 可能有更好方法
  rintro y ⟨n, rfl⟩
  apply h_bounded_below n

variable {D : Set H} (hD_seq : IsWeaklySeqClosed D)
variable (u : ℕ → H) (hu : ∀ n, u n ∈ D) (p : H) (hconv : WeakConverge u p)
--这里如果hconv写 Tendsto (fun n ↦ H) atTop (𝓝 (p : WeakSpace ℝ H)) 就错了，不知道为什么
example : p ∈ D :=
  hD_seq hu hconv

--def IsWeaklySeqClusterPt (p : H) (x : ℕ → H):=
--  ∃ (φ : ℕ → ℕ), StrictMono φ ∧
--    Tendsto (fun n => (x (φ n) : WeakSpace ℝ H)) atTop (𝓝 (p : WeakSpace ℝ H))
variable (u : ℕ → H) (φ : ℕ → ℕ) (hu : ∀ n, u n ∈ D) (p : H) (hconv : WeakConverge (fun n => (u (φ n))) p)
example : p ∈ D :=
  hD_seq (fun n => hu (φ n)) hconv

--定理5.5的形式化
theorem theorem_5_05 (C : Set H) (h_C_nonempty : C.Nonempty) (x : ℕ → H)
(h_fejer : IsFejerMonotone x C) (h_weak_cluster_in : ∀ p : H, IsWeaklySeqClusterPt' p x → p ∈ C):
∃ p0 ∈ C, WeakConverge x p0 := by
  have h_converge := (Prop_5_04_i_ii C h_C_nonempty x h_fejer).2
  apply Lemma_2_47 C h_C_nonempty x h_converge h_weak_cluster_in

#check IsSeqClosed
-- 定理 5.15 的形式化

lemma key_inequality {D : Set H} (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    ∀ (y : H) (hy : y ∈ Fix' T D) (n : ℕ),
      ‖km.x (n + 1) - y‖^2 ≤ ‖km.x n - y‖^2
      - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖^2 := by
 -- 证明 (i) Fejér 单调性
    intro y hy n
    rcases hy with ⟨-, hyfix⟩
    -- 先从 km.hstepsize n 得到 0 ≤ s 和 s ≤ 1
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have key_calc := by
      calc
        ‖km.x (n + 1) - y‖^2
            = ‖(1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y)‖^2 := by
              rw [km.update n]
              simp only [smul_sub, sub_smul, one_smul]
              abel_nf
        _ = (1 - km.stepsize n) * ‖km.x n - y‖^2
            + km.stepsize n * ‖T (km.x n) - y‖^2
            - km.stepsize n * (1 - km.stepsize n) * ‖(T (km.x n) - y) - ( km.x n - y)‖^2 := by
              -- apply Corollary_2_15 with arguments arranged to match this expression
              have h := Corollary_2_15 (T (km.x n) - y) (km.x n - y) (km.stepsize n)
              -- swap the summands inside the norm so the lemma matches exactly
              have add_comm_eq : (1 - km.stepsize n) • (km.x n - y) + km.stepsize n • (T (km.x n) - y) =
              km.stepsize n • (T (km.x n) - y) + (1 - km.stepsize n) • (km.x n - y) := by simp [add_comm]
              rw [add_comm_eq]
              rw[eq_sub_iff_add_eq , h]
              ring
        _ ≤ (1 - km.stepsize n) * ‖km.x n - y‖^2 + km.stepsize n * ‖km.x n - y‖^2 -km.stepsize n * (1 - km.stepsize n) *‖(T (km.x n)  -  km.x n )‖^2  := by

            have hT_le : ‖T (km.x n) - y‖ ≤ ‖km.x n - y‖ := by
              nth_rw 1 [← hyfix]
              exact hT_nonexpansive (km.x n) y
            simp
            apply mul_le_mul_of_nonneg_left _ hs_nonneg
            refine pow_le_pow_left₀ ?_ hT_le 2
            exact norm_nonneg _
        _ = ‖km.x n - y‖^2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖^2 := by
            ring
    exact key_calc

lemma groetsch_theorem_i {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    -- (i) Fejér 单调性
    IsFejerMonotone km.x (Fix' T D) := by
    intro y hy n
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have calc1 :‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 := by
      calc
      ‖km.x (n + 1) - y‖ ^ 2 ≤ ‖km.x n - y‖ ^ 2 - km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ ^ 2 := by
        exact key_inequality T h_Im_T_in_D hT_nonexpansive km y hy n
      _≤ ‖km.x n - y‖ ^ 2 := by
        have h_nonneg : 0 ≤ km.stepsize n * (1 - km.stepsize n) * ‖T (km.x n) - y - (km.x n - y)‖ ^ 2 := by
          apply mul_nonneg
          · apply mul_nonneg
            · exact hs_nonneg
            · exact sub_nonneg.mpr hs_le_one   -- 1 - s ≥ 0
          · exact pow_nonneg (norm_nonneg _) 2
        simp at h_nonneg
        linarith
      --‖ a ‖ ^2 ≤ ‖ b ‖ ^2 推出 ‖ a ‖ ≤ ‖ b ‖
    have := (sq_le_sq).mp calc1
    repeat rw[abs_of_nonneg (norm_nonneg _)] at this
    exact this

lemma groetsch_theorem_ii {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    (Tendsto (fun n ↦ ‖T (km.x n) - km.x n‖)  atTop (𝓝 0)) := by
  rcases km.fix_T_nonempty with ⟨y0, hy0⟩
  have sum_bound : ∀ N, ∑  i ∈ range (N), km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 - ‖km.x (N) - y0‖ ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hN := key_inequality T h_Im_T_in_D hT_nonexpansive km y0 hy0 N
      simp [Finset.sum_range_succ]
      linarith

  have partial_le : ∀ N, ∑ i ∈ Finset.range N, km.stepsize i * (1 - km.stepsize i) * ‖T (km.x i) - km.x i‖ ^ 2 ≤
      ‖km.x 0 - y0‖ ^ 2 := by
      intro N
      refine (sum_bound N).trans ?_
      simp

  -- 定义 a_n 并证明其非增
  let a := fun n => ‖T (km.x n) - km.x n‖
  have a_noninc : ∀ n, a (n + 1) ≤ a n := by
    intro n
    rcases km.hstepsize n with ⟨hs0, hs1⟩
    -- x_{n+1} - x_n = s_n • (T x_n - x_n)
    have hx : km.x (n + 1) - km.x n = km.stepsize n • (T (km.x n) - km.x n) := by
      rw [km.update n]; simp [ smul_sub]
    have eq : T (km.x (n + 1)) - km.x (n + 1) = (T (km.x (n + 1)) - T (km.x n)) + (1 - km.stepsize n) • (T (km.x n) - km.x n) := by
      calc
        T (km.x (n + 1)) - km.x (n + 1) = T (km.x (n + 1)) - T (km.x n) + T (km.x n) - km.x (n + 1) := by simp
        _ = T (km.x (n + 1)) - T (km.x n) + (1 - km.stepsize n) • (T (km.x n) - km.x n) := by
          nth_rw 2 [km.update n]
          simp only [smul_sub, sub_smul, one_smul]
          abel_nf

    calc
      a (n + 1) = ‖T (km.x (n + 1)) - km.x (n + 1)‖ := rfl
      _ = ‖(T (km.x (n + 1)) - T (km.x n)) + (1 - km.stepsize n) • (T (km.x n) - km.x n)‖ := by rw [eq]
      _ ≤ ‖T (km.x (n + 1)) - T (km.x n)‖ + ‖(1 - km.stepsize n) • (T (km.x n) - km.x n)‖ := by apply norm_add_le
      _ ≤ ‖km.x (n + 1) - km.x n‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by
        apply add_le_add
        · exact (hT_nonexpansive (km.x (n + 1)) (km.x n))
        -- 从 stepsize ∈ Icc 0 1 拆出 0 ≤ s ≤ 1
        have h_nonneg : 0 ≤ 1 - km.stepsize n := by linarith
        -- 证明 ‖(1 - s) • v‖ ≤ (1 - s) * ‖v‖
        calc
          ‖(1 - km.stepsize n) • (T (km.x n) - km.x n)‖
              = ‖(1 - km.stepsize n)‖ * ‖T (km.x n) - km.x n‖ := by rw [norm_smul]
          _ = |1 - km.stepsize n| * ‖T (km.x n) - km.x n‖ := by rw [Real.norm_eq_abs]
          _ = (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [abs_of_nonneg h_nonneg]
        linarith
      _= ‖km.stepsize n • (T (km.x n) - km.x n)‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [hx]
      _= km.stepsize n * ‖T (km.x n) - km.x n‖ + (1 - km.stepsize n) * ‖T (km.x n) - km.x n‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hs0)]
      _= ‖T (km.x n) - km.x n‖ := by ring

  -- 反证：若 a 不收敛到 0，则存在 ε>0 使得对任意 N 都能找到 n ≥ N 使 a n ≥ ε
  rw [Converge_iff _ _]
  --rw[tendsto_atTop']

  --分类讨论，若 x0 = y0 则直接取 N=0，否则利用反证法
  by_cases h_x0_eq_y0:  km.x 0 = y0
  · intro ε εpos
    use 0
    intro n hn
    rcases hy0 with ⟨-, hyfix⟩
    rw[← h_x0_eq_y0] at hyfix
    have fixed_point: T (km.x n) - km.x n = 0 := by
      induction' n with n ih
      rw[sub_eq_zero]
      exact hyfix
      rw [km.update n]
      simp [ih _]
    rw[fixed_point]
    simpa
  --x0 ≠ y0
  by_contra! hnot
  rcases hnot with ⟨ε, εpos, hε⟩

  -- 由 km.hstepsize_sum（偏和趋于 +∞）挑出 M 使得偏和大于 ‖x0-y0‖^2 / ε
  have tend := km.hstepsize_sum
  have tend_prop := (Filter.tendsto_atTop_atTop.mp tend) (2*‖km.x 0 - y0‖ ^ 2 / ε^2)
  rcases tend_prop with ⟨N0, hN0⟩
  -- 由 hε 在 N0 处选出 n ≥ N0 且 a n ≥ ε
  rcases (hε N0) with ⟨n0, hn0_ge, hn0_ge_eps⟩
  -- 对 n0 + 1 的偏和，利用单调性 a_i ≥ a_{n0}（i ≤ n0）得到下界
  have lower : ∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2 ≥
      ∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i)*ε ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have : i ≤ n0 := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have ai_ge : a i ≥ a n0 := by
      exact (antitone_nat_of_succ_le a_noninc) (by omega)
    have ai_ge_eps : ε ≤ a i := by
      have h : ε ≤ ‖T (km.x n0) - km.x n0‖ := by
        by_contra! H  -- H: ‖T (km.x n0) - km.x n0‖ < ε
        rw[← zero_add ε ] at H
        exact hn0_ge_eps ⟨by linarith [norm_nonneg (T (km.x n0) - km.x n0)], H⟩
      linarith
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (le_of_lt εpos) ai_ge_eps 2
    rcases km.hstepsize i with ⟨hs0, hs1⟩
    · apply mul_nonneg
      · exact hs0
      · exact sub_nonneg.mpr hs1

  -- 由 hN0（偏和下界从 N0 开始）得到 S ≥ ‖x0-y0‖^2 / ε^2，结合上面 lower 导出矛盾
  have S_ge : ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i)
  ≥ 2*‖km.x 0 - y0‖ ^ 2 / ε^2:= by
    apply hN0
    exact le_trans (by linarith : N0 ≤ n0) (le_refl _)

  have lb: ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2
  ≥ (2* ‖km.x 0 - y0‖ ^ 2 ) := by
    calc
      ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * (a i) ^ 2
          ≥ ∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * ε ^ 2 := by
            exact lower
      _ = ε ^ 2 *(∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i))  := by
        have : (∑ i ∈ range (n0 + 1), km.stepsize i * (1 - km.stepsize i) * ε ^ 2) =
            ∑ i ∈ range (n0 + 1), ε ^ 2 * (km.stepsize i * (1 - km.stepsize i) ) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [this]
        -- 把 ε^2 提到和式外面
        rw [← @Finset.mul_sum ℕ _ _ (range (n0 + 1))
        (fun i => km.stepsize i * (1 - km.stepsize i)) (ε ^ 2)]
      _ ≥ 2*‖km.x 0 - y0‖ ^ 2 := by
        -- 应用 S_ge：先把目标改写为 ε^2 * (∑ ...) ≥ ε^2 * (2*‖x0-y0‖^2 / ε^2)，再用 mul_le_mul_of_nonneg_left
        have hpos : 0 ≤ ε ^ 2 := by exact pow_nonneg (le_of_lt εpos) 2
        calc
          ε ^ 2 * (∑ i ∈ Finset.range (n0 + 1), km.stepsize i * (1 - km.stepsize i))
          _ ≥ ε ^ 2 * (2* ‖km.x 0 - y0‖ ^ 2 / ε ^ 2) := by apply mul_le_mul_of_nonneg_left S_ge hpos
          _ = 2*‖km.x 0 - y0‖ ^ 2 := by
            -- 用 field_simp 消去除数 ε^2（ε > 0）
            field_simp [ne_of_gt εpos]

  have ub := partial_le (n0 + 1)
  have mid: 2 * ‖km.x 0 - y0‖ ^ 2 > ‖km.x 0 - y0‖ ^ 2 := by
    refine lt_two_mul_self ?_
    have h_sub_ne : km.x 0 - y0 ≠ 0 := by
      intro h
      apply h_x0_eq_y0
      rw[sub_eq_zero] at h
      exact h
    have h_norm_pos : 0 < ‖km.x 0 - y0‖ := by
      apply norm_pos_iff.mpr
      exact h_sub_ne
    have : 0 < ‖km.x 0 - y0‖ ^ 2 := pow_pos h_norm_pos (2)
    exact this
  linarith

lemma groetsch_theorem_iii {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    ∃ y0 ∈ (Fix' T D),
      WeakConverge km.x y0
    := by
  have h_fejer := (groetsch_theorem_i hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km)
  have h_x : ∀ n, km.x n ∈ D := by  --似乎这个命题只在第三个结论用到，即结论(i)(ii)不要求D是凸闭集
    intro n
    induction' n with n ih
    · rw [km.initial_value]
      exact km.hx0
    have eq : km.x (n + 1) = (1 - km.stepsize n) • km.x n + km.stepsize n • (T (km.x n)) := by
      rw [km.update n]
      simp [smul_sub, sub_smul, one_smul]
      abel_nf
    have h1 : T (km.x n) ∈ D := h_Im_T_in_D (km.x n) ih
      -- D 凸性推出凸组合仍在 D 中
    rcases km.hstepsize n with ⟨hs_nonneg, hs_le_one⟩
    have combo_in : (1 - km.stepsize n) • km.x n + km.stepsize n • T (km.x n) ∈ D := by
      -- 注意 Convex 的形式是：∀ x y ∈ D, ∀ t ∈ Icc (0:ℝ) 1, t • x + (1 - t) • y ∈ D
      -- 我们取 x := T (km.x n), y := km.x n, 并传入相应的证据
      exact hD_convex (ih) h1 (sub_nonneg.mpr hs_le_one) (hs_nonneg) (sub_add_cancel _ _)
    rw [eq]
    exact combo_in

  --证明D 是序列弱闭集--定理3.34
  have h_D_seq_weak_closed : IsWeaklySeqClosed D := closed_is_weakly_seq_closed D hD_convex hD_closed
  have hT_nonexp : NonexpansiveOn T D := by
    intro x hx y hy
    simp [edist_dist] ;rw [dist_eq_norm, dist_eq_norm]
    exact hT_nonexpansive x y

  have h_weak_cluster_in : ∀ p : H, IsWeaklySeqClusterPt' p km.x → p ∈ (Fix' T D)  := by
    intro p h_cluster
    rcases h_cluster with ⟨ φ, hφ , tend ⟩
    have p_in_D : p ∈ D := by
      apply h_D_seq_weak_closed (fun n => h_x (φ n) ) tend
    -- 证明 p 是 T 的不动点
    have h_error_zero : Tendsto (fun n ↦ km.x (φ n) - T (km.x (φ n))) atTop (𝓝 0):= by
      have h1 : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
      have h2 : Tendsto (fun n ↦ km.x n - T (km.x n)) atTop (𝓝 0) := by
        -- 由结论(ii)可知 ‖T (km.x n) - km.x n‖ → 0
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have eq: Tendsto (fun n ↦ ‖km.x n - T (km.x n)‖) atTop (𝓝 0) ↔
          Tendsto (fun n ↦ ‖T (km.x n)- km.x n‖) atTop (𝓝 0) := by
          apply tendsto_congr
          intro n
          rw [norm_sub_rev]
        rw[eq]
        exact (groetsch_theorem_ii hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km)
      exact Tendsto.comp h2 h1
    have D_nonempty: (D).Nonempty := by
      exact ⟨ km.x0,km.hx0⟩
    have := corollary_4_28 hD_closed hD_convex D_nonempty hT_nonexp (fun n => km.x (φ n) ) (fun n => h_x (φ n) )
      p p_in_D tend h_error_zero
    exact ⟨ p_in_D, this ⟩
  apply theorem_5_05 (Fix' T D) (km.fix_T_nonempty) km.x h_fejer h_weak_cluster_in

theorem groetsch_theorem {D : Set H} (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (T : H → H) (h_Im_T_in_D : ∀ x ∈ D, T x ∈ D) (hT_nonexpansive : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (km : KM D T) :
    -- (i) Fejér 单调性
    IsFejerMonotone km.x (Fix' T D)
    -- (ii) 强收敛到 0
    ∧(Tendsto (fun n ↦ ‖T (km.x n) - km.x n‖)  atTop (𝓝 0))
    -- (iii) 弱收敛到不动点
    ∧∃ y0 ∈ (Fix' T D),
      WeakConverge km.x y0
    :=
      ⟨
        groetsch_theorem_i hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km,
        groetsch_theorem_ii hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km,
        groetsch_theorem_iii hD_convex hD_closed T h_Im_T_in_D hT_nonexpansive km
      ⟩
