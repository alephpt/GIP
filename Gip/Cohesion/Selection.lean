/-!
# Cohesion and Type Selection Through Survival

This module formalizes the concept of Cohesion as a measure of a structure's
internal consistency, which in turn determines its survival through the cycle.

## Refactoring Note

Previously this file had custom axioms for distance:
- `axiom identity_distance` → Now uses Mathlib's `MetricSpace.dist`
- `axiom distance_nonneg` → Now `dist_nonneg` from Mathlib
- `axiom distance_eq_zero` → Now `dist_eq_zero` from Mathlib

All cohesion properties are now THEOREMS derived from Foundations.lean.
-/

import Gip.Foundations

namespace GIP.Cohesion

open GIP.Foundations

/-!
## Re-export Cohesion from Foundations

The core cohesion machinery is defined in Foundations.lean using Mathlib's MetricSpace.
We re-export it here for backwards compatibility.
-/

/-- Cohesion is a computable measure of a structure's internal consistency.
    Re-exported from Foundations. -/
noncomputable abbrev cohesion {α : Type*} [MetricSpace α] := GIP.Foundations.cohesion

/-- The threshold for a structure to survive the cycle. -/
abbrev survival_threshold := GIP.Foundations.survivalThreshold

/-- A predicate stating that a structure survives the cycle. -/
abbrev survives_cycle {α : Type*} [MetricSpace α] (x y : α) := GIP.Foundations.survives x y

/-!
## Cohesion Properties (All THEOREMS, not axioms)

These are re-exported from Foundations for API compatibility.
-/

/-- Cohesion is always positive - THEOREM -/
theorem cohesion_positive {α : Type*} [MetricSpace α] (x y : α) :
    0 < cohesion x y := cohesion_pos x y

/-- Cohesion is at most 1 - THEOREM -/
theorem cohesion_bounded {α : Type*} [MetricSpace α] (x y : α) :
    cohesion x y ≤ 1 := cohesion_le_one x y

/-- Cohesion equals 1 iff identical - THEOREM -/
theorem perfect_cohesion_iff_identical {α : Type*} [MetricSpace α] (x y : α) :
    cohesion x y = 1 ↔ x = y := cohesion_eq_one_iff x y

/-- Cohesion is symmetric - THEOREM -/
theorem cohesion_symmetric {α : Type*} [MetricSpace α] (x y : α) :
    cohesion x y = cohesion y x := cohesion_symm x y

/-!
## Cohesion and Survival

The core link between cohesion and survival is now a DEFINITION in Foundations.
-/

/-- Cohesion determines survival - THEOREM by definition -/
theorem cohesion_determines_survival {α : Type*} [MetricSpace α] (x y : α) :
    (cohesion x y > survival_threshold ↔ survives_cycle x y) := by
  rfl

/-- High cohesion implies survival - THEOREM -/
theorem high_cohesion_survives {α : Type*} [MetricSpace α] (x y : α)
    (h : cohesion x y > survival_threshold) : survives_cycle x y :=
  GIP.Foundations.high_cohesion_survives x y h

/-!
## Identity Space

A type for structures with a metric, allowing cohesion computation.
-/

/-- An identity space is any type with a metric structure -/
abbrev IdentitySpace := GIP.Foundations.IdentitySpace

/-!
## Inferred Types (Stable Structures)

An Inferred Type is a collection of structures that are stable enough
(i.e., cohesive enough) to survive the cycle.
-/

/-- An Inferred Type is a set of points with a reference, all surviving -/
structure InferredType (α : Type*) [MetricSpace α] where
  members : Set α
  reference : α  -- The reference point for cohesion measurement
  closure : ∀ x, x ∈ members → survives_cycle x reference
  nonempty : members.Nonempty

/-!
## Summary of Changes

| Old (Axiom) | New Status |
|-------------|------------|
| `axiom identity_distance` | Uses `MetricSpace.dist` from Mathlib |
| `axiom distance_nonneg` | `dist_nonneg` theorem from Mathlib |
| `axiom distance_eq_zero` | `dist_eq_zero` theorem from Mathlib |
| `axiom perfect_cohesion_is_perfect_reconstruction` | Follows from `cohesion_eq_one_iff` |

No axioms remain in this file. All properties are derived from Foundations.
-/

end GIP.Cohesion
