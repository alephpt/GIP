/-!
# Origin Theory: Grounded in Category Theory

This module defines the higher-level transformations (Gen, Res, Act),
now properly grounded in Foundations.lean.

## Critical Design Issue

The refactoring revealed that the original "bidirectional conduit" model
contained **categorically invalid** axioms:

- `gamma.res : 𝟙 → ∅` cannot exist (initial objects only emit)
- `epsilon.res : ∞ → 𝟙` cannot exist (terminal objects only receive)

This means the old `dissolve : ∞ → ∅` pathway was not well-founded.

## Resolution

We have two options:

1. **Accept the asymmetry**: The cycle only goes one direction:
   ∅ → 𝟙 → n → 𝟙 → ∞ (no return from ∞ to ∅)

2. **Augment the category**: Add structure that allows "reverse" morphisms
   (e.g., adjunctions, duality, or a different categorical framework)

For now, we implement Option 1 and note where Option 2 would be needed.
-/

import Gip.Foundations

namespace GIP.Origin

open GIP.Foundations

/-!
## The Three Transformations (Valid Direction)

These transformations follow the categorical flow from initial to terminal.
-/

/-- **Gen**: Generation pathway ∅ → n
    Composition: γ;ι (gamma then iota)
    This is categorically valid. -/
def Gen : Hom Obj.empty Obj.identity := Hom.gamma_iota

/-- **Sat**: Saturation pathway n → ∞
    Composition: τ;ε (tau then epsilon)
    This is categorically valid. -/
def Sat : Hom Obj.identity Obj.infinite := Hom.tau_epsilon

/-- **FullPath**: Complete forward path ∅ → ∞
    Composition: γ;ε (through unit directly) or γ;ι;τ;ε (through identity)
    Both are valid and equal by uniqueness of morphisms to terminal. -/
def FullPath : Hom Obj.empty Obj.infinite := Hom.gamma_epsilon

/-- The two paths to ∞ are equal - THEOREM from terminal uniqueness -/
theorem paths_to_terminal_equal :
    Hom.comp Gen Sat = FullPath := by
  -- Both are morphisms ∅ → ∞, so equal by terminal uniqueness
  exact morphismToInfinite_unique Obj.empty (Hom.comp Gen Sat) FullPath

/-!
## The Problematic Reverse Direction

The old model had:
- `Res : ∞ → n` (resolution from infinite)
- `dissolve : ∞ → ∅` (dissolution)

These require morphisms FROM terminal and TO initial, which don't exist
in standard category theory.

### Option 2 Sketch: Adjoint Structure

If we wanted reverse morphisms, we could:
1. Posit that (Gen, Res) form an adjunction
2. Or work in a *-category with involution
3. Or use a traced monoidal category

This would require additional axioms WITH JUSTIFICATION.
-/

/-- Placeholder for reverse path - requires augmented structure -/
axiom reverse_structure_postulate :
  -- IF we add adjoint structure, THEN reverse morphisms exist
  -- This is the ONLY new postulate beyond Foundations
  ∃ (Res : Hom Obj.infinite Obj.identity),
    -- With some coherence condition
    True

/-!
## Duality and Bifurcation

The old model's "DualAspect" and "bifurcate" can be reformulated.
-/

/-- DualAspect: The complementary poles
    In proper categorical terms, this is the product ∅ × ∞
    (initial and terminal as a pair) -/
structure DualAspect where
  empty_witness : Hom Obj.empty Obj.empty  -- id on initial
  infinite_witness : Hom Obj.infinite Obj.infinite  -- id on terminal
  complementary : Obj.empty ≠ Obj.infinite  -- They're distinct

/-- The canonical dual aspect -/
def bifurcate : DualAspect where
  empty_witness := Hom.id Obj.empty
  infinite_witness := Hom.id Obj.infinite
  complementary := by decide  -- Obj.empty ≠ Obj.infinite by definition

/-- Convergence: Both aspects connect to identity
    From ∅: via Gen (γ;ι)
    From ∞: requires augmented structure -/
def converge_from_empty : Hom Obj.empty Obj.identity := Gen

/-!
## Information Loss (The Ouroboros)

The key insight: even without reverse morphisms, we can express information loss.
Any morphism ∅ → ∅ must be the identity (by initiality).
But if we HAD a cycle ∅ → n → ∞ → ∅, it would equal id_∅.
This means the cycle "forgets" which path was taken - information loss.
-/

/-- All morphisms ∅ → ∅ equal identity - THEOREM -/
theorem empty_endomorphism_unique (f : Hom Obj.empty Obj.empty) :
    f = Hom.id Obj.empty :=
  morphismFromEmpty_unique Obj.empty f (Hom.id Obj.empty)

/-- Information loss formulation:
    If a cycle existed, it would collapse all paths to id_∅ -/
theorem information_loss_principle :
    ∀ (f g : Hom Obj.empty Obj.empty), f = g :=
  fun f g => by
    rw [empty_endomorphism_unique f, empty_endomorphism_unique g]

/-!
## Legacy Compatibility (With Caveats)

These definitions maintain API compatibility but some are now `sorry`
because the old model was categorically invalid.
-/

/-- actualize = Gen (valid) -/
abbrev actualize := Gen

/-- saturate = Sat (valid) -/
abbrev saturate := Sat

/-- dissolve: Would require ∞ → ∅, which doesn't exist categorically -/
-- def dissolve : Hom Obj.infinite Obj.empty := sorry  -- INVALID

/-- circle_path: Would require going ∅ → n → ∅, but no n → ∅ exists -/
-- def circle_path : Hom Obj.empty Obj.empty := sorry  -- INVALID

/-!
## Summary

### Valid (Proven/Defined):
- `Gen : ∅ → n` (generation)
- `Sat : n → ∞` (saturation)
- `FullPath : ∅ → ∞` (complete forward path)
- `bifurcate : DualAspect` (the two poles)
- `information_loss_principle` (all ∅ → ∅ equal id)

### Invalid (Removed):
- `Res : ∞ → n` (no morphisms from terminal to non-terminal)
- `dissolve : ∞ → ∅` (no morphisms from terminal to initial)
- `circle_path` (no cycle without reverse morphisms)

### Requires Augmented Structure:
- `reverse_structure_postulate` (ONE additional postulate, if needed)

The old model conflated "bidirectional flow" with "categorical morphisms".
Proper category theory only has one-directional morphisms.
Bidirectionality requires additional structure (adjunctions, dualities).
-/

end GIP.Origin
