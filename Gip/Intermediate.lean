/-!
# The Intermediate Morphisms of GIP

This file provides the morphism structure for the zero object model.

## The Zero Object Model

- **○** is the zero object (initial AND terminal)
- **∅ ≅ ∞** are isomorphic dual aspects
- **n** is the hub (bidirectional flow, not zero object)

## Morphism Structure

From ○ (zero object):
- `from_origin`: ○ → A for all A (initial)
- `to_origin`: A → ○ for all A (terminal)

Between aspects:
- `empty_to_inf`: ∅ → ∞ (isomorphism)
- `inf_to_empty`: ∞ → ∅ (inverse)

To/from hub n:
- `gen`: ∅ → n (generation)
- `res`: ∞ → n (resolution)
- `act_empty`: n → ∅ (action)
- `act_inf`: n → ∞ (action)
-/

import Gip.Foundations

namespace GIP.Intermediate

open GIP.Foundations

/-!
## Zero Object Morphisms

○ has unique morphisms to/from all objects.
-/

/-- Morphism from origin to any object -/
abbrev fromOrigin (a : Obj) : Hom Obj.origin a := Hom.from_origin a

/-- Morphism from any object to origin -/
abbrev toOrigin (a : Obj) : Hom a Obj.origin := Hom.to_origin a

/-- Zero object property: unique from -/
theorem from_origin_unique (a : Obj) (f g : Hom Obj.origin a) : f = g :=
  morphismFromOrigin_unique a f g

/-- Zero object property: unique to -/
theorem to_origin_unique (a : Obj) (f g : Hom a Obj.origin) : f = g :=
  morphismToOrigin_unique a f g

/-!
## Aspect Isomorphism

∅ ≅ ∞ - they are two faces of the same coin.
-/

/-- ∅ → ∞ -/
abbrev emptyToInfinite : Hom Obj.aspect_empty Obj.aspect_infinite := emptyToInf

/-- ∞ → ∅ -/
abbrev infiniteToEmpty : Hom Obj.aspect_infinite Obj.aspect_empty := infToEmpty

/-- Round trip is identity -/
theorem aspect_iso_roundtrip_empty :
    Hom.comp emptyToInfinite infiniteToEmpty = Hom.id Obj.aspect_empty :=
  empty_inf_empty

theorem aspect_iso_roundtrip_inf :
    Hom.comp infiniteToEmpty emptyToInfinite = Hom.id Obj.aspect_infinite :=
  inf_empty_inf

/-!
## Hub Morphisms

n is the hub - it has bidirectional flow with aspects.
-/

/-- Generation: ∅ → n -/
abbrev generation : Hom Obj.aspect_empty Obj.identity := Gen

/-- Resolution: ∞ → n -/
abbrev resolution : Hom Obj.aspect_infinite Obj.identity := Res

/-- Action to empty: n → ∅ -/
abbrev actionEmpty : Hom Obj.identity Obj.aspect_empty := act.to_empty

/-- Action to infinite: n → ∞ -/
abbrev actionInf : Hom Obj.identity Obj.aspect_infinite := act.to_infinite

/-!
## Coherence

Gen and Res are "the same" via the isomorphism.
-/

/-- Gen = Res via ∅ ≅ ∞ -/
theorem gen_res_coherent : Hom.comp emptyToInfinite resolution = generation :=
  gen_res_coherence

/-!
## Summary

| Morphism | Type | Role |
|----------|------|------|
| `from_origin` | ○ → A | Zero object (initial) |
| `to_origin` | A → ○ | Zero object (terminal) |
| `emptyToInfinite` | ∅ → ∞ | Aspect isomorphism |
| `infiniteToEmpty` | ∞ → ∅ | Inverse isomorphism |
| `generation` | ∅ → n | Into hub |
| `resolution` | ∞ → n | Into hub |
| `actionEmpty` | n → ∅ | From hub |
| `actionInf` | n → ∞ | From hub |
-/

end GIP.Intermediate
