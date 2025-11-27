import Gip.Foundations

/-!
# Origin Theory: The Restricted Model

This module defines the higher-level transformations,
grounded in the restricted origin model:

- **○** connects only to aspects (∅ and ∞)
- **∅ ≅ ∞** are isomorphic dual aspects
- **n** is the hub (connects to aspects, not directly to ○)

## The Structure

```
        ○
       ↗ ↖
      ↙   ↘
     ∅  ≅  ∞
      ↓   ↓
   Gen   Res
      ↘ ↙
       n (hub)
      ↙ ↘
   Act   Act
      ↓   ↓
     ∅  ≅  ∞
      ↘   ↙
        ○
```
-/

namespace GIP.Origin

open GIP.Foundations

/-!
## The Three Transformations

All are categorically valid in the restricted model.
-/

-- Gen, Res are imported from Foundations (no local redefinition to avoid ambiguity)
-- Act is an alias to the Foundations instance
abbrev Act := act

/-!
## Path Properties

With ∅ ≅ ∞, Gen and Res are "the same transformation" viewed from different aspects.
-/

/-- Gen and Res are coherent via the isomorphism -/
theorem gen_res_via_isomorphism :
    Hom.comp emptyToInf Res = Gen := gen_res_coherence

/-- Symmetrically, Res = Gen via the inverse isomorphism -/
theorem res_gen_via_isomorphism :
    Hom.comp infToEmpty Gen = Res := by
  -- ∞ → ∅ → n should equal ∞ → n
  rfl

/-!
## Paths Through Aspects

Since ○ only connects to aspects, all paths between ○ and n go through ∅ or ∞.
-/

/-- From n back to ○ via ∅ (n has no direct morphism to origin) -/
def identityToOriginViaEmpty : Hom Obj.identity Obj.origin :=
  Hom.comp Act.to_empty emptyToOrigin

/-- From n back to ○ via ∞ -/
def identityToOriginViaInf : Hom Obj.identity Obj.origin :=
  Hom.comp Act.to_infinite infToOrigin

/-!
## Information Collapse

Paths from aspects through ○ collapse - uniqueness on both ends.
-/

/-- Paths ∅ → ○ → ∅ are unique -/
theorem empty_origin_empty_collapse
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∅ → ○ → ∞ are unique -/
theorem empty_origin_inf_collapse
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∞ → ○ → ∅ are unique -/
theorem inf_origin_empty_collapse
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∞ → ○ → ∞ are unique -/
theorem inf_origin_inf_collapse
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂
  rw [hf, hg]

/-!
## DualAspect Structure: Duality from Unity

The bifurcation ○/○ = (∅, ∞) produces dual initial objects.
BOTH ∅ and ∞ are initial objects simultaneously, isomorphic to each other.
-/

/-- DualAspect captures that ∅ and ∞ are isomorphic faces -/
structure DualAspect where
  empty_morphism : Hom Obj.origin Obj.aspect_empty
  infinite_morphism : Hom Obj.origin Obj.aspect_infinite
  isomorphism_witness : Hom.comp empty_morphism emptyToInf = infinite_morphism

/-- The canonical dual aspect from ○ -/
def bifurcate_dual : DualAspect where
  empty_morphism := Hom.origin_to_empty
  infinite_morphism := Hom.origin_to_inf
  isomorphism_witness := by unfold Hom.comp emptyToInf; rfl

/-- ∅ is initial: Gen is unique -/
theorem empty_initial : ∀ (f g : Hom Obj.aspect_empty Obj.identity), f = g := by
  intro f g
  cases f <;> cases g <;> rfl

/-- ∞ is initial: Res is unique -/
theorem infinite_initial : ∀ (f g : Hom Obj.aspect_infinite Obj.identity), f = g := by
  intro f g
  cases f <;> cases g <;> rfl

/-- The self-division ○/○ = (∅, ∞) produces dual initial objects -/
theorem origin_self_division_yields_dual_initials :
    (∀ f g : Hom Obj.aspect_empty Obj.identity, f = g) ∧
    (∀ f g : Hom Obj.aspect_infinite Obj.identity, f = g) :=
  ⟨empty_initial, infinite_initial⟩

/-!
## Summary

### Duality from Unity: ○/○ = (∅, ∞)
- The origin's self-division produces **dual initial objects**
- BOTH ∅ and ∞ are initial (unique morphisms to n)
- ∅ ≅ ∞ (isomorphic aspects)

### Valid (in restricted model):
- `Gen : ∅ → n` (generation from empty initial)
- `Res : ∞ → n` (resolution from infinite initial)
- `Act : n → (∅, ∞)` (action/mirror back to both initials)
- ○ ↔ aspects (unique morphisms)
- Gen ≈ Res via ∅ ≅ ∞

### The Key Insight:
○ connects only to aspects (∅ and ∞).
n connects only to aspects (∅ and ∞).
The aspects serve as the interface layer - both are initial objects
arising from ○'s self-division, providing dual sources for forward pathways.
-/

end GIP.Origin
