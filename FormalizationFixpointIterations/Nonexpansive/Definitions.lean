/-
Copyright (c) 2025 Yifan Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yifan Bai
-/
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Constructions

universe u v
variable {α : Type u} {β : Type v}

namespace Nonexpansive_operator

section defn_nonexpansive

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

def Nonexpansive (T : α → β) := LipschitzWith 1 T
def NonexpansiveOn (T : α → β) (s : Set α) := LipschitzOnWith 1 T s

def Strictly_Nonexpansive (T : α → β) := ∀ x y, x ≠ y → edist (T x) (T y) < edist x y
def Strictly_NonexpansiveOn (T : α → β) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (T x) (T y) ≤ edist x y

theorem edist_le_mul (T : α → β) (h : Nonexpansive T) (x y : α) :
  edist (T x) (T y) ≤ edist x y := by
    simpa [ENNReal.coe_one] using (h x y)

theorem firmly_edist_lt_mul (T : α → β) (h : Strictly_Nonexpansive T) (x y : α) (hxy : x ≠ y) :
  edist (T x) (T y) < edist x y := h x y hxy

end defn_nonexpansive

section defn_firmly_nonexpansive
open Function
variable [NormedAddCommGroup α]

def Fix (T : α → α) : Set α := {x | IsFixedPt T x}

def FixOn (T : α → α) (D : Set α) : Set α := {x | x ∈ D ∧ IsFixedPt T x}

def Firmly_Nonexpansive (T : α → α) :=
  ∀ x y, ‖T x - T y‖^2 + ‖(x - T x) - (y - T y)‖^2 < ‖x - y‖^2

def Firmly_NonexpansiveOn (T : α → α) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ‖T x - T y‖^2 + ‖(x - T x) - (y - T y)‖^2 < ‖x - y‖^2

def Firmly_QuasiNonexpansive (T : α → α) :=
  ∀ x y, y ∈ Fix T → ‖T x - y‖^2 + ‖T x - x‖^2 ≤ ‖x - y‖^2

def Firmly_QuasiNonexpansiveOn (T : α → α) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ FixOn T s → ‖T x - y‖^2 + ‖T x - x‖^2 ≤ ‖x - y‖^2

def QuasiNonexpansive (T : α → α) :=
  ∀ x y, y ∈ Fix T → ‖T x - y‖ ≤ ‖x - y‖

def QuasiNonexpansiveOn (T : α → α) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ Fix T ∩ s → ‖T x - y‖ ≤ ‖x - y‖

def Strictly_QuasiNonexpansive (T : α → α) :=
  ∀ x, ¬ IsFixedPt T x → ∀ y, IsFixedPt T y → ‖T x - y‖ < ‖x - y‖

def Strictly_QuasiNonexpansiveOn (T : α → α) (s : Set α) :=
  ∀ x, x ∈ s ∧ (¬ IsFixedPt T x) → ∀ y, y ∈ Fix T ∩ s → ‖T x - y‖ < ‖x - y‖

end defn_firmly_nonexpansive

section properties_PMetric
variable [PseudoMetricSpace α] [PseudoMetricSpace β]

theorem dist_le_mul (T : α → β) (h : Nonexpansive T) (x y : α) :
  dist (T x) (T y) ≤ dist x y := by
    simpa [ENNReal.coe_one] using ((lipschitzWith_iff_dist_le_mul).1 h x y)

theorem dist_le_mul_On {T : α → β} {D : Set α} (h : NonexpansiveOn T D) (x y : α)
  (hx : x ∈ D) (hy : y ∈ D) : dist (T x) (T y) ≤ dist x y := by
  simpa [ENNReal.coe_one] using ((lipschitzOnWith_iff_dist_le_mul).1 h x hx y hy)

theorem strictly_nonexpansive_iff_dist_lt_mul (T : α → β) :
  Strictly_Nonexpansive T ↔ ∀ x y, x ≠ y → dist (T x) (T y) < dist x y := by
  simp only [Strictly_Nonexpansive, edist_nndist]
  norm_cast

theorem strictly_dist_lt_mul (T : α → β) (h : Strictly_Nonexpansive T) (x y : α) (hxy : x ≠ y) :
  dist (T x) (T y) < dist x y := (strictly_nonexpansive_iff_dist_lt_mul T).1 h x y hxy

end properties_PMetric

section properties_Normed
open NormedAddGroup

variable [NormedAddCommGroup α] [NormedAddCommGroup β]

theorem norm_le_mul (T : α → β) (h : Nonexpansive T) (x y : α) :
  ‖T x - T y‖ ≤ ‖x - y‖ := by
    simpa [dist_eq] using dist_le_mul T h x y

theorem norm_le_mul_On {T : α → β} {D : Set α} (h : NonexpansiveOn T D) (x y : α)
  (hx : x ∈ D) (hy : y ∈ D) : ‖T x - T y‖ ≤ ‖x - y‖ := by
  simpa [dist_eq] using dist_le_mul_On h x y hx hy

theorem strictly_nonexpansive_iff_norm_lt_mul (T : α → β) :
  Strictly_Nonexpansive T ↔ ∀ x y, x ≠ y → ‖T x - T y‖ < ‖x - y‖ := by
    simpa [dist_eq] using strictly_nonexpansive_iff_dist_lt_mul T

theorem strictly_norm_lt_mul (T : α → β) (h : Strictly_Nonexpansive T) (x y : α) (hxy : x ≠ y) :
  ‖T x - T y‖ < ‖x - y‖ := (strictly_nonexpansive_iff_norm_lt_mul T).1 h x y hxy

theorem firmly_norm_le (T : α → α) (h : Firmly_Nonexpansive T) (x y : α) :
  ‖T x - T y‖^2 + ‖(x - T x) - (y - T y)‖^2 < ‖x - y‖^2 := h x y


end properties_Normed

end Nonexpansive_operator
