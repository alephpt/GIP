/-!
# Core GIP Types

This file re-exports the foundational types from `Foundations.lean`.

## Design Note

Previously this file contained "axioms" that were actually definitions:
- `axiom OriginType : Type` → Now `Obj` (defined inductively)
- `axiom the_origin` → Now `Obj.empty` (the initial object)
- `axiom manifest` → Now derived from `Obj` structure

All types are now DEFINED, not axiomatized.
-/

import Gip.Foundations

namespace GIP.CoreTypes

open GIP.Foundations

/-- The three aspects through which the origin manifests.
    This is re-exported from Foundations for backwards compatibility. -/
abbrev Aspect := Obj

/-- Backwards compatibility: Aspect.empty -/
abbrev Aspect.empty := Obj.empty

/-- Backwards compatibility: Aspect.identity -/
abbrev Aspect.identity := Obj.identity

/-- Backwards compatibility: Aspect.infinite -/
abbrev Aspect.infinite := Obj.infinite

/-- The "type" of the origin - this is just Unit (singleton).
    Previously axiomatized, now DEFINED. -/
def OriginType := Unit

/-- The unique origin - this is just the unit value.
    Previously axiomatized, now DEFINED. -/
def the_origin : OriginType := ()

/-- Any origin equals the_origin - THEOREM, not axiom.
    Follows immediately from OriginType being Unit. -/
theorem origin_is_unique (o : OriginType) : o = the_origin := by
  cases o
  rfl

/-- Manifestation of origin as an aspect.
    Previously axiomatized, now DEFINED as a type family.

    The "manifest" of an aspect is simply that aspect's type in our category.
    - manifest empty = the initial object type
    - manifest identity = the identity object type
    - manifest infinite = the terminal object type
-/
def manifest (_orig : OriginType) (a : Obj) : Type :=
  match a with
  | .empty => Unit      -- Initial: one canonical element
  | .unit => Unit       -- Proto-identity: one canonical element
  | .identity => Nat    -- Identity: natural numbers as example structure
  | .infinite => Unit   -- Terminal: one canonical element

/-- The empty aspect has a unique inhabitant -/
def manifest_empty : manifest the_origin .empty := ()

/-- The infinite aspect has a unique inhabitant -/
def manifest_infinite : manifest the_origin .infinite := ()

/-!
## Summary of Changes

| Old (Axiom) | New (Definition/Theorem) |
|-------------|-------------------------|
| `axiom OriginType : Type` | `def OriginType := Unit` |
| `axiom the_origin : OriginType` | `def the_origin : OriginType := ()` |
| `axiom origin_is_unique` | `theorem origin_is_unique` (proven) |
| `axiom manifest` | `def manifest` (defined) |

No axioms remain in this file.
-/

end GIP.CoreTypes
