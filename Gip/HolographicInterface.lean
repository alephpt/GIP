import Gip.Foundations
import Gip.Origin

/-!
# The Holographic Interface of the Origin

The holographic properties of GIP in the restricted origin model.

## The Restricted Origin Model

- **○** connects only to aspects (∅ and ∞)
- **∅ ≅ ∞** are isomorphic aspects
- **n** is the hub (bidirectional flow with aspects)
- All paths through ○ between aspects collapse (uniqueness)
-/

namespace GIP.HolographicInterface

open GIP.Foundations
open GIP.Origin

/-!
## Path Collapse Property

All paths through ○ between aspects are equal - this is the holographic principle.
-/

/-- Paths ∅ → ○ → ∅ collapse -/
theorem empty_paths_through_origin_empty_collapse
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  empty_origin_empty_collapse f₁ f₂ g₁ g₂

/-- Paths ∅ → ○ → ∞ collapse -/
theorem empty_paths_through_origin_inf_collapse
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  empty_origin_inf_collapse f₁ f₂ g₁ g₂

/-- Paths ∞ → ○ → ∅ collapse -/
theorem inf_paths_through_origin_empty_collapse
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  inf_origin_empty_collapse f₁ f₂ g₁ g₂

/-- Paths ∞ → ○ → ∞ collapse -/
theorem inf_paths_through_origin_inf_collapse
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  inf_origin_inf_collapse f₁ f₂ g₁ g₂

/-!
## Uniqueness Properties
-/

/-- Morphisms ○ → ∅ are unique -/
theorem origin_to_empty_unique (f g : Hom Obj.origin Obj.aspect_empty) : f = g :=
  morphismOriginToEmpty_unique f g

/-- Morphisms ○ → ∞ are unique -/
theorem origin_to_inf_unique (f g : Hom Obj.origin Obj.aspect_infinite) : f = g :=
  morphismOriginToInf_unique f g

/-- Morphisms ∅ → ○ are unique -/
theorem empty_to_origin_unique (f g : Hom Obj.aspect_empty Obj.origin) : f = g :=
  morphismEmptyToOrigin_unique f g

/-- Morphisms ∞ → ○ are unique -/
theorem inf_to_origin_unique (f g : Hom Obj.aspect_infinite Obj.origin) : f = g :=
  morphismInfToOrigin_unique f g

/-!
## The Aspect Isomorphism

∅ ≅ ∞ means Gen and Res are "the same" transformation.
-/

/-- ∅ and ∞ are isomorphic -/
theorem dual_aspects_isomorphic :
    ∃ (f : Hom Obj.aspect_empty Obj.aspect_infinite)
      (g : Hom Obj.aspect_infinite Obj.aspect_empty),
      Hom.comp f g = Hom.id Obj.aspect_empty ∧
      Hom.comp g f = Hom.id Obj.aspect_infinite :=
  aspects_isomorphic

/-- Gen = Res via the isomorphism -/
theorem generation_resolution_coherent :
    Hom.comp emptyToInf Hom.res = Hom.gen := by
  rfl

/-!
## Paths Through Aspects

Since ○ only connects to aspects, all paths between ○ and n go through ∅ or ∞.
-/

/-- Path from n to ○ via ∅ -/
def hubToOriginViaEmpty : Hom Obj.identity Obj.origin :=
  identityToOriginViaEmpty

/-- Path from n to ○ via ∞ -/
def hubToOriginViaInf : Hom Obj.identity Obj.origin :=
  identityToOriginViaInf

/-!
## The Holographic Principle

Information collapses when passing through ○.
-/

/-- The "holographic" property for ∅ → ○ → ∅: all paths collapse -/
theorem holographic_principle_empty_empty :
    ∀ (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty),
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  empty_paths_through_origin_empty_collapse

/-- The "holographic" property for ∅ → ○ → ∞: all paths collapse -/
theorem holographic_principle_empty_inf :
    ∀ (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite),
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  empty_paths_through_origin_inf_collapse

/-- The "holographic" property for ∞ → ○ → ∅: all paths collapse -/
theorem holographic_principle_inf_empty :
    ∀ (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty),
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  inf_paths_through_origin_empty_collapse

/-- The "holographic" property for ∞ → ○ → ∞: all paths collapse -/
theorem holographic_principle_inf_inf :
    ∀ (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite),
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ :=
  inf_paths_through_origin_inf_collapse

/-!
## Summary

### The Restricted Origin Model:
- ○ connects only to aspects (∅ and ∞)
- Paths through ○ between aspects collapse (holographic principle)
- ∅ ≅ ∞ (dual aspects are isomorphic)
- n is the hub where structure is realized
- n flows to ○ through aspects (n → ∅ → ○ or n → ∞ → ○)

### Key Theorems:
- `empty/inf_paths_through_origin_X_collapse`: Paths collapse through ○
- `dual_aspects_isomorphic`: ∅ ≅ ∞
- `generation_resolution_coherent`: Gen ≈ Res
- `holographic_principle_X_Y`: Information collapses through ○
-/

end GIP.HolographicInterface
