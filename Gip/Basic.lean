/-!
# Basic GIP Definitions

Re-exports from the zero object model Foundations.

## The Model

- **○** is the zero object (initial AND terminal)
- **∅ ≅ ∞** are isomorphic dual aspects
- **n** is the hub
-/

import Gip.Foundations

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

-- Zero object morphisms
abbrev fromOrigin := Hom.from_origin
abbrev toOrigin := Hom.to_origin

-- Aspect isomorphism
abbrev emptyToInfinite := emptyToInf
abbrev infiniteToEmpty := infToEmpty

-- Hub morphisms
abbrev gen := Gen
abbrev res := Res

-- Zero object properties
theorem origin_initial (a : Obj) (f g : Hom Obj.origin a) : f = g :=
  morphismFromOrigin_unique a f g

theorem origin_terminal (a : Obj) (f g : Hom a Obj.origin) : f = g :=
  morphismToOrigin_unique a f g

-- Aspect isomorphism
theorem aspects_iso : ∃ (f : Hom Empty Infinite) (g : Hom Infinite Empty),
    Hom.comp f g = Hom.id Empty ∧ Hom.comp g f = Hom.id Infinite :=
  aspects_isomorphic

end GIP.Basic
