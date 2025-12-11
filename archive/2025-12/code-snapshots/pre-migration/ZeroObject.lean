import Gip.Foundations

/-!
# Origin Object Theory (Restricted Model)

○ connects only to aspects (∅ and ∞).

## Properties

The restricted origin ○ satisfies:
1. ∃! f : ○ → ∅ and ∃! g : ○ → ∞ (to aspects only)
2. ∃! f : ∅ → ○ and ∃! g : ∞ → ○ (from aspects only)
3. Paths through ○ between aspects collapse (unique)

This is NOT a zero object in the traditional sense (which would have
morphisms to/from ALL objects). Instead, ○ only connects to aspects.
-/

namespace GIP.ZeroObject

open GIP.Foundations

/-!
## ○ → Aspects
-/

/-- ○ → ∅ exists -/
theorem origin_to_empty : ∃ _ : Hom Obj.origin Obj.aspect_empty, True :=
  ⟨Hom.origin_to_empty, trivial⟩

/-- ○ → ∞ exists -/
theorem origin_to_inf : ∃ _ : Hom Obj.origin Obj.aspect_infinite, True :=
  ⟨Hom.origin_to_inf, trivial⟩

/-- ○ → ∅ is unique -/
theorem origin_to_empty_unique (f g : Hom Obj.origin Obj.aspect_empty) : f = g :=
  morphismOriginToEmpty_unique f g

/-- ○ → ∞ is unique -/
theorem origin_to_inf_unique (f g : Hom Obj.origin Obj.aspect_infinite) : f = g :=
  morphismOriginToInf_unique f g

/-!
## Aspects → ○
-/

/-- ∅ → ○ exists -/
theorem empty_to_origin : ∃ _ : Hom Obj.aspect_empty Obj.origin, True :=
  ⟨Hom.empty_to_origin, trivial⟩

/-- ∞ → ○ exists -/
theorem inf_to_origin : ∃ _ : Hom Obj.aspect_infinite Obj.origin, True :=
  ⟨Hom.inf_to_origin, trivial⟩

/-- ∅ → ○ is unique -/
theorem empty_to_origin_unique (f g : Hom Obj.aspect_empty Obj.origin) : f = g :=
  morphismEmptyToOrigin_unique f g

/-- ∞ → ○ is unique -/
theorem inf_to_origin_unique (f g : Hom Obj.aspect_infinite Obj.origin) : f = g :=
  morphismInfToOrigin_unique f g

/-!
## Path Collapse (Holographic Principle)
-/

/-- Paths ∅ → ○ → ∅ collapse -/
theorem empty_origin_empty_collapse
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := empty_to_origin_unique f₁ f₂
  have hg : g₁ = g₂ := origin_to_empty_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∅ → ○ → ∞ collapse -/
theorem empty_origin_inf_collapse
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := empty_to_origin_unique f₁ f₂
  have hg : g₁ = g₂ := origin_to_inf_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∞ → ○ → ∅ collapse -/
theorem inf_origin_empty_collapse
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := inf_to_origin_unique f₁ f₂
  have hg : g₁ = g₂ := origin_to_empty_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∞ → ○ → ∞ collapse -/
theorem inf_origin_inf_collapse
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := inf_to_origin_unique f₁ f₂
  have hg : g₁ = g₂ := origin_to_inf_unique g₁ g₂
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
  to_empty := Hom.origin_to_empty
  to_infinite := Hom.origin_to_inf

/-!
## Summary

○ in the restricted model:
- Unique morphisms TO aspects (∅ and ∞) only
- Unique morphisms FROM aspects only
- Paths through ○ between aspects collapse
- ○/○ = (∅ ≅ ∞) : {N}
-/

end GIP.ZeroObject
