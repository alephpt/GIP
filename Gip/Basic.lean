import Gip.Foundations

/-!
# Basic GIP Definitions

Re-exports from the restricted origin model Foundations.

## The Model

- **○** connects only to aspects (∅ and ∞)
- **∅ ≅ ∞** are isomorphic dual aspects
- **n** is the hub (connects to aspects, not directly to ○)
-/

namespace GIP.Basic

open GIP.Foundations

-- Objects
abbrev GIPObj := Obj
abbrev Origin := Obj.origin
abbrev Empty := Obj.aspect_empty
abbrev Infinite := Obj.aspect_infinite
abbrev Identity := Obj.identity

-- Morphisms
abbrev GIPHom := Hom

-- Origin morphisms (○ ↔ aspects only)
abbrev originToEmpty := Hom.origin_to_empty
abbrev originToInf := Hom.origin_to_inf
abbrev emptyToOrigin := Hom.empty_to_origin
abbrev infToOrigin := Hom.inf_to_origin

-- Aspect isomorphism
abbrev emptyToInfinite := emptyToInf
abbrev infiniteToEmpty := infToEmpty

-- Hub morphisms
abbrev gen := Gen
abbrev res := Res

-- Origin properties (○ ↔ aspects uniqueness)
theorem origin_to_empty_unique (f g : Hom Origin Empty) : f = g :=
  morphismOriginToEmpty_unique f g

theorem origin_to_inf_unique (f g : Hom Origin Infinite) : f = g :=
  morphismOriginToInf_unique f g

theorem empty_to_origin_unique (f g : Hom Empty Obj.origin) : f = g :=
  morphismEmptyToOrigin_unique f g

theorem inf_to_origin_unique (f g : Hom Infinite Obj.origin) : f = g :=
  morphismInfToOrigin_unique f g

-- Aspect isomorphism
theorem aspects_iso : ∃ (f : Hom Empty Infinite) (g : Hom Infinite Empty),
    Hom.comp f g = Hom.id Empty ∧ Hom.comp g f = Hom.id Infinite :=
  aspects_isomorphic

end GIP.Basic
