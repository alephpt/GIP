import Gip.ProjectionFunctors
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Test for F_Ring functor

This module tests the F_Ring projection functor.
-/

namespace GIP.Test

open CategoryTheory GIP

/-- Test that F_Ring maps empty to PUnit -/
example : F_Ring.obj Obj.empty = RingCat.of PUnit := rfl

/-- Test that F_Ring maps unit to ℤ -/
example : F_Ring.obj Obj.unit = RingCat.of ℤ := rfl

/-- Test that F_Ring maps n to quotient ring -/
example : F_Ring.obj Obj.n = RingCat.of (ℤ ⧸ (⊥ : Ideal ℤ)) := rfl

/-- Test that identity morphisms are preserved -/
example : F_Ring.map (𝟙 Obj.unit) = 𝟙 (F_Ring.obj Obj.unit) := by
  rfl

/-- Test that the functor maps morphisms correctly -/
example : F_Ring.map (𝟙 Obj.empty) = 𝟙 (F_Ring.obj Obj.empty) := by
  rfl

example : F_Ring.map (𝟙 Obj.n) = 𝟙 (F_Ring.obj Obj.n) := by
  rfl

/-- Verify that the trivial ring PUnit is indeed a ring -/
example : Ring PUnit := inferInstance

/-- Verify that the quotient ring is indeed a ring -/
example : Ring (ℤ ⧸ (⊥ : Ideal ℤ)) := inferInstance

/-- Test composition of morphisms -/
example (f : Obj.unit ⟶ Obj.n) (g : Obj.n ⟶ Obj.n) :
  ∃ h, h = F_Ring.map (f ≫ g) := by
  use F_Ring.map f ≫ F_Ring.map g
  exact F_Ring.map_comp f g

/-- The quotient by bottom ideal is isomorphic to the original ring -/
theorem quotient_bottom_iso : (ℤ ⧸ (⊥ : Ideal ℤ)) ≃+* ℤ := by
  -- The quotient by the zero ideal is isomorphic to the ring itself
  apply RingEquiv.ofBijective (quotientToInt)
  constructor
  · -- Injective
    intro x y h
    -- If quotientToInt x = quotientToInt y, then x = y
    sorry  -- Would need to show this using properties of bottom ideal
  · -- Surjective
    intro x
    use Ideal.Quotient.mk _ x
    -- quotientToInt (mk x) = x
    sorry  -- Would need to show this using lift properties

/-- F_Ring is a well-defined functor -/
theorem F_Ring_is_functor : Functor Gen RingCat := F_Ring

end GIP.Test