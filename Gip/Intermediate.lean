import Gip.Foundations

/-!
# The Intermediate Morphisms of GIP

This file provides the morphism structure for the restricted origin model.

## The Restricted Origin Model

- **○** connects only to aspects (∅ and ∞)
- **∅ ≅ ∞** are isomorphic dual aspects
- **n** is the hub (bidirectional flow with aspects)

## Morphism Structure

From/To ○ (aspects only):
- `origin_to_empty`: ○ → ∅
- `origin_to_inf`: ○ → ∞
- `empty_to_origin`: ∅ → ○
- `inf_to_origin`: ∞ → ○

Between aspects:
- `empty_to_inf`: ∅ → ∞ (isomorphism)
- `inf_to_empty`: ∞ → ∅ (inverse)

To/from hub n:
- `gen`: ∅ → n (generation)
- `res`: ∞ → n (resolution)
- `act_empty`: n → ∅ (action)
- `act_inf`: n → ∞ (action)
-/

namespace GIP.Intermediate

open GIP.Foundations

/-!
## Origin Morphisms

○ connects only to aspects (∅ and ∞).
-/

/-- Morphism from origin to empty -/
abbrev originToEmpty : Hom Obj.origin Obj.aspect_empty := Hom.origin_to_empty

/-- Morphism from origin to infinite -/
abbrev originToInfinite : Hom Obj.origin Obj.aspect_infinite := Hom.origin_to_inf

/-- Morphism from ∅ to origin -/
abbrev emptyToOrigin : Hom Obj.aspect_empty Obj.origin := Hom.empty_to_origin

/-- Morphism from ∞ to origin -/
abbrev infiniteToOrigin : Hom Obj.aspect_infinite Obj.origin := Hom.inf_to_origin

/-- Unique ○ → ∅ -/
theorem origin_to_empty_unique (f g : Hom Obj.origin Obj.aspect_empty) : f = g :=
  morphismOriginToEmpty_unique f g

/-- Unique ○ → ∞ -/
theorem origin_to_inf_unique (f g : Hom Obj.origin Obj.aspect_infinite) : f = g :=
  morphismOriginToInf_unique f g

/-- Unique ∅ → ○ -/
theorem empty_to_origin_unique (f g : Hom Obj.aspect_empty Obj.origin) : f = g :=
  morphismEmptyToOrigin_unique f g

/-- Unique ∞ → ○ -/
theorem inf_to_origin_unique (f g : Hom Obj.aspect_infinite Obj.origin) : f = g :=
  morphismInfToOrigin_unique f g

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
| `originToEmpty` | ○ → ∅ | Bifurcation to empty |
| `originToInfinite` | ○ → ∞ | Bifurcation to infinite |
| `emptyToOrigin` | ∅ → ○ | Return to origin |
| `infiniteToOrigin` | ∞ → ○ | Return to origin |
| `emptyToInfinite` | ∅ → ∞ | Aspect isomorphism |
| `infiniteToEmpty` | ∞ → ∅ | Inverse isomorphism |
| `generation` | ∅ → n | Into hub |
| `resolution` | ∞ → n | Into hub |
| `actionEmpty` | n → ∅ | From hub |
| `actionInf` | n → ∞ | From hub |
-/

end GIP.Intermediate
