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

All are functionally valid in the restricted model.
Using the Phi (Φ)-based functions from Foundations.
-/

-- Gen, Res, and Act are imported from Foundations as functions
-- We create aliases for clarity in this module
noncomputable abbrev gen := Gen
noncomputable abbrev res := Res
noncomputable abbrev act := Act

/-!
## Path Properties

With ∅ ≅ ∞, Gen and Res are "the same transformation" viewed from different aspects.
Note: These are now functional properties, not categorical morphisms.
-/

/-- Gen and Res produce the same Phi (Φ) from isomorphic inputs -/
theorem gen_res_coherence_functional (e : manifest the_origin Aspect.empty) :
    Gen e = Res (aspect_iso.to_inf e) := by
  -- Unfold the definitions of Gen and Res
  unfold Gen Res
  -- Gen e = gamma.gen e, Res inf = epsilon.res inf
  -- By phi_coherence: gamma.gen e = epsilon.res (aspect_iso.to_inf e)
  rw [phi_coherence]

/-!
## Functional Paths

Since ○ only connects to aspects, all paths between ○ and n go through ∅ or ∞.
Using the functional Act which returns a pair.
-/

/-- Extract empty component from ActSplit -/
noncomputable def act_to_empty (n : manifest the_origin Aspect.identity) :
    manifest the_origin Aspect.empty :=
  (ActSplit n).1

/-- Extract infinite component from ActSplit -/
noncomputable def act_to_infinite (n : manifest the_origin Aspect.identity) :
    manifest the_origin Aspect.infinite :=
  (ActSplit n).2

/-!
## Categorical Compatibility Layer

For proofs that still need categorical morphisms, we use the Hom structure
from Foundations which provides a categorical view of the conduit model.
-/

/-- From n back to ○ via ∅ using categorical morphisms -/
def identityToOriginViaEmpty : Hom 𝕟 ○ :=
  Hom.n_to_origin_via_empty

/-- From n back to ○ via ∞ using categorical morphisms -/
def identityToOriginViaInf : Hom 𝕟 ○ :=
  Hom.n_to_origin_via_inf

/-- From ○ to n via ∅ using categorical morphisms -/
def originToIdentityViaEmpty : Hom ○ 𝕟 :=
  Hom.origin_to_n_via_empty

/-- From ○ to n via ∞ using categorical morphisms -/
def originToIdentityViaInf : Hom ○ 𝕟 :=
  Hom.origin_to_n_via_inf

/-!
## Information Collapse

Paths from aspects through ○ collapse - uniqueness on both ends.
Using the categorical layer for these proofs.
-/

/-- Paths ∅ → ○ → ∅ are unique -/
theorem empty_origin_empty_collapse
    (f₁ f₂ : Hom ∅ ○) (g₁ g₂ : Hom ○ ∅) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∅ → ○ → ∞ are unique -/
theorem empty_origin_inf_collapse
    (f₁ f₂ : Hom ∅ ○) (g₁ g₂ : Hom ○ ∞) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∞ → ○ → ∅ are unique -/
theorem inf_origin_empty_collapse
    (f₁ f₂ : Hom ∞ ○) (g₁ g₂ : Hom ○ ∅) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂
  rw [hf, hg]

/-- Paths ∞ → ○ → ∞ are unique -/
theorem inf_origin_inf_collapse
    (f₁ f₂ : Hom ∞ ○) (g₁ g₂ : Hom ○ ∞) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂
  rw [hf, hg]

/-!
## DualAspect Structure: Duality from Unity

The bifurcation ○/○ = (∅, ∞) produces dual initial objects.
BOTH ∅ and ∞ are initial objects simultaneously, isomorphic to each other.
Using the categorical compatibility layer.
-/

/-- DualAspect captures that ∅ and ∞ are isomorphic faces -/
structure DualAspect where
  empty_morphism : Hom ○ ∅
  infinite_morphism : Hom ○ ∞
  isomorphism_witness : Hom.comp empty_morphism emptyToInf = infinite_morphism

/-- The canonical dual aspect from ○ -/
def bifurcate_dual : DualAspect where
  empty_morphism := Hom.origin_to_empty
  infinite_morphism := Hom.origin_to_inf
  isomorphism_witness := by
    unfold Hom.comp emptyToInf
    -- This follows from the composition rules in Foundations
    rfl

/-- ∅ is initial: morphisms from ∅ to n are unique (Gen) -/
theorem empty_initial : ∀ (f g : Hom ∅ 𝕟), f = g := by
  intro f g
  cases f; cases g; rfl

/-- ∞ is initial: morphisms from ∞ to n are unique (Res) -/
theorem infinite_initial : ∀ (f g : Hom ∞ 𝕟), f = g := by
  intro f g
  cases f; cases g; rfl

/-- The self-division ○/○ = (∅, ∞) produces dual initial objects -/
theorem origin_self_division_yields_dual_initials :
    (∀ f g : Hom ∅ 𝕟, f = g) ∧
    (∀ f g : Hom ∞ 𝕟, f = g) :=
  ⟨empty_initial, infinite_initial⟩

/-!
## Functional Properties of Act

Act returns a pair (∅, ∞), demonstrating the mirror/split nature.
-/

/-- ActSplit produces both empty and infinite aspects -/
theorem act_produces_dual_aspects (n : manifest the_origin Aspect.identity) :
    ∃ (e : manifest the_origin Aspect.empty) (inf : manifest the_origin Aspect.infinite),
    ActSplit n = (e, inf) := by
  exact ⟨(ActSplit n).1, (ActSplit n).2, rfl⟩

/-- ActSplit is the functional mirror operator -/
theorem act_is_mirror :
    ∀ n : manifest the_origin Aspect.identity,
    act_to_empty n = (ActSplit n).1 ∧ act_to_infinite n = (ActSplit n).2 := by
  intro n
  constructor <;> rfl

/-!
## Summary

### Duality from Unity: ○/○ = (∅, ∞)
- The origin's self-division produces **dual initial objects**
- BOTH ∅ and ∞ are initial (unique morphisms to n)
- ∅ ≅ ∞ (isomorphic aspects)

### Valid (in restricted model):
- `Gen : ∅ → n` (generation from empty initial, through Phi (Φ))
- `Res : ∞ → n` (resolution from infinite initial, through Phi (Φ))
- `Act : n → (∅, ∞)` (action/mirror back to both initials as a pair)
- ○ ↔ aspects (unique morphisms in categorical view)
- Gen ≈ Res via ∅ ≅ ∞

### The Key Insight:
○ connects only to aspects (∅ and ∞).
n connects only to aspects (∅ and ∞).
The aspects serve as the interface layer - both are initial objects
arising from ○'s self-division, providing dual sources for forward pathways.
All transformations flow through Phi (Φ) as the convergence point.
-/

end GIP.Origin