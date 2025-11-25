/-!
# Zero Object Theory

○ is THE zero object - both initial AND terminal.

## Properties of a Zero Object

A zero object Z satisfies:
1. ∀ A, ∃! f : Z → A (initial)
2. ∀ A, ∃! g : A → Z (terminal)
3. All paths through Z collapse (A → Z → B is unique)

In GIP, ○ is this zero object.
-/

import Gip.Foundations

namespace GIP.ZeroObject

open GIP.Foundations

/-!
## ○ is the Zero Object
-/

/-- ○ → A exists for all A -/
theorem zero_to_all (a : Obj) : ∃ f : Hom Obj.origin a, True :=
  ⟨Hom.from_origin a, trivial⟩

/-- A → ○ exists for all A -/
theorem all_to_zero (a : Obj) : ∃ f : Hom a Obj.origin, True :=
  ⟨Hom.to_origin a, trivial⟩

/-- ○ → A is unique -/
theorem zero_to_unique (a : Obj) (f g : Hom Obj.origin a) : f = g :=
  morphismFromOrigin_unique a f g

/-- A → ○ is unique -/
theorem to_zero_unique (a : Obj) (f g : Hom a Obj.origin) : f = g :=
  morphismToOrigin_unique a f g

/-- The zero object property: paths through ○ collapse -/
theorem zero_collapse (a b : Obj)
    (f₁ f₂ : Hom a Obj.origin) (g₁ g₂ : Hom Obj.origin b) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := to_zero_unique a f₁ f₂
  have hg : g₁ = g₂ := zero_to_unique b g₁ g₂
  rw [hf, hg]

/-!
## The Bifurcation: ○/○ = (∅ ≅ ∞)

The self-division of ○ produces isomorphic dual aspects.
-/

/-- ∅ and ∞ are isomorphic -/
theorem aspects_isomorphic :
    ∃ (f : Hom Obj.aspect_empty Obj.aspect_infinite)
      (g : Hom Obj.aspect_infinite Obj.aspect_empty),
      Hom.comp f g = Hom.id Obj.aspect_empty ∧
      Hom.comp g f = Hom.id Obj.aspect_infinite :=
  GIP.Foundations.aspects_isomorphic

/-- The bifurcation from ○ -/
structure Bifurcation where
  to_empty : Hom Obj.origin Obj.aspect_empty
  to_infinite : Hom Obj.origin Obj.aspect_infinite

/-- The canonical bifurcation -/
def bifurcation : Bifurcation where
  to_empty := Hom.from_origin Obj.aspect_empty
  to_infinite := Hom.from_origin Obj.aspect_infinite

/-!
## Summary

○ is the zero object:
- Unique morphisms to/from all objects
- All paths through ○ collapse
- ○/○ = (∅ ≅ ∞) : {N}
-/

end GIP.ZeroObject
