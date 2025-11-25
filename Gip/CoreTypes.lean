import Gip.Foundations

/-!
# Core GIP Types

Re-exports the foundational types from `Foundations.lean`.

## The Zero Object Model

- **○** (Origin) is the zero object
- **○/○ = (∅ ≅ ∞)** produces isomorphic dual aspects
- **{N}** emerges as the universe of structures
-/

namespace GIP.CoreTypes

open GIP.Foundations

/-- The GIP objects, re-exported from Foundations -/
abbrev Aspect := Obj

/-- Origin ○ - the zero object -/
abbrev Origin := Obj.origin

/-- Empty aspect ∅ -/
abbrev AspectEmpty := Obj.aspect_empty

/-- Infinite aspect ∞ (isomorphic to ∅) -/
abbrev AspectInfinite := Obj.aspect_infinite

/-- Identity n - the hub -/
abbrev Identity := Obj.identity

/-- The "type" of the origin - this is the zero object itself -/
def OriginType := Unit

/-- The unique origin -/
def the_origin : OriginType := ()

/-- Any origin equals the_origin - THEOREM -/
theorem origin_is_unique (o : OriginType) : o = the_origin := by
  cases o; rfl

/-- The aspects are isomorphic -/
theorem aspects_iso : ∃ (f : Hom AspectEmpty AspectInfinite) (g : Hom AspectInfinite AspectEmpty),
    Hom.comp f g = Hom.id AspectEmpty ∧ Hom.comp g f = Hom.id AspectInfinite :=
  aspects_isomorphic

end GIP.CoreTypes
