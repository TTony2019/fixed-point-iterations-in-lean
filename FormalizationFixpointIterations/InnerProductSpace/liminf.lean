/-
Copyright (c) 2025 Yifan Bai, Yantao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yifan Bai, Yantao Li
-/
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Normed.Group.Basic

open Filter

/--
Right hand side of Lemma 2.42 : If a sequence `x` converges to `p`, and `x n ≤ y n` for all `n`,
then `p ≤ liminf y n`.
-/
lemma EReal.limit_le_liminf (x y : ℕ → ℝ) (p : ℝ) (h : Tendsto x atTop (nhds p))
  (hxy : ∀ n, x n ≤ y n) : Real.toEReal p ≤ liminf (fun n => Real.toEReal (y n)) atTop := by
  simp only [liminf, limsInf, eventually_map, eventually_atTop, ge_iff_le]
  let s : Set EReal := {a : EReal | ∃ N, ∀ (n : ℕ), N ≤ n → (a ≤ y n)}
  change p ≤ sSup s
  have h1 : ∀ (ε : ℝ) , ε > 0 → Real.toEReal (p - ε) ∈ s := by
    intro ε hε
    simp only [coe_sub, Set.mem_setOf_eq, s]
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε  -- 从 Tendsto 得到 ε-N 条件
    use N
    intro n hn
    specialize hN n hn  -- hN: |x n - p| < ε
    rw [Real.dist_eq] at hN  -- |x n - p| < ε，即 p - ε < x n < p + ε
    have p_lt_xn : p - ε < x n := by
      exact sub_lt_of_abs_sub_lt_left hN
    have xn_lt_yn : x n ≤ y n := hxy n  -- 从假设 hxy: ∀ n, x n ≤ y n
    have : p - ε < y n := by linarith
    rw [← EReal.coe_lt_coe_iff] at this; exact le_of_lt this
  have h2 : ∀ (ε : ℝ) , ε > 0 → p - ε ≤ sSup s := by
    intro ε hε; apply le_sSup; exact h1 ε hε
  by_cases hs1 : sSup s = ⊤
  · simp [hs1]
  push_neg at hs1
  have hs2 : sSup s ≠ ⊥ := by
    by_contra!
    rw [this] at h2
    specialize h2 1 (by simp)
    rw [← EReal.coe_sub] at h2
    simp only [coe_sub, coe_one, le_bot_iff] at h2
    exact EReal.coe_ne_bot (p - 1) h2
  lift (sSup s) to ℝ using ⟨hs1,hs2⟩ with d; rw [EReal.coe_le_coe_iff]
  have h2' : ∀ ε > 0, p - ε ≤ d := by
    intro ε hε; specialize h2 ε hε; rwa [← EReal.coe_sub, EReal.coe_le_coe_iff] at h2
  exact le_of_forall_sub_le h2'

/--
Equality of liminf : `liminf (‖x n‖ * ‖p‖) = liminf ‖x n‖ * ‖p‖`.
-/
lemma EReal.liminf_mul_const {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (p : E) :
  liminf (fun n ↦ Real.toEReal (‖x n‖ * ‖p‖)) atTop
  = (liminf (fun n ↦ Real.toEReal ‖x n‖) atTop) * Real.toEReal ‖p‖ := by
  by_cases hp : Real.toEReal ‖p‖ = 0
  · simp [hp]
  apply le_antisymm
  · calc
      _ = liminf (fun n ↦ ((Real.toEReal ‖p‖) * (Real.toEReal ‖x n‖))) atTop := by simp [mul_comm]
      _ ≤ (limsup (fun n ↦ Real.toEReal ‖p‖) atTop) *
        liminf (fun n ↦ Real.toEReal ‖x n‖) atTop := by
        apply EReal.liminf_mul_le
        · apply Eventually.of_forall; simp
        · apply Eventually.of_forall; simp
        · left; push_neg at hp; simp at hp; simpa
        · left; simp
      _ = ↑‖p‖ * liminf (fun n ↦ ↑‖x n‖) atTop := by simp
      _ = _ := by rw [mul_comm]
  calc
    _ = liminf (fun n ↦ Real.toEReal ‖x n‖) atTop *
      liminf (fun n ↦ Real.toEReal ‖p‖) atTop := by
      congr; symm; apply @Filter.liminf_const EReal ℕ _ atTop _ (Real.toEReal ‖p‖)
    _ ≤ liminf (fun n ↦ Real.toEReal ‖x n‖ * Real.toEReal ‖p‖) atTop := by
      apply le_liminf_mul
      · apply Eventually.of_forall; simp
      · apply Eventually.of_forall; simp
