import Gip.Origin

/-!
# Test Suite: Origin Theory (Post-Refactor)

This test suite validates the refactored Origin theory based on the `converge` axiom
and the derived `actualize` function.

## Test Coverage

1.  **Duality and Convergence**: Verify the core `converge` mechanism.
2.  **Identity Genesis**: Test the `identity_from_both` axiom.
3.  **Derived Actualization**: Test the properties of the new `actualize` function,
    especially the `actualize_surjective` theorem.
4.  **Circle Integrity**: Verify the `circle_closes` axiom holds with the new components.
-/

namespace GIP.Origin.Tests

open GIP.Origin

-- Axiom assumptions for testing purposes
noncomputable instance : Nonempty (manifest the_origin Aspect.empty) := ⟨bifurcate.empty⟩
noncomputable instance : Nonempty (manifest the_origin Aspect.infinite) := ⟨bifurcate.infinite⟩

-- A sample empty element for testing
noncomputable def test_empty : manifest the_origin Aspect.empty := Classical.choice inferInstance

-- A sample infinite element for testing
noncomputable def test_infinite : manifest the_origin Aspect.infinite := Classical.choice inferInstance

/-!
## 1. Duality and Convergence Tests
-/

/-- TEST: The `bifurcate` axiom provides a valid DualAspect. -/
theorem test_bifurcate_properties :
  bifurcate.empty ≠ bifurcate.infinite → bifurcate.complementary = (by simp) := by
  intro
  simp [bifurcate]

/--
TEST: `converge` respects the `converge_depends_only_on_empty` axiom.
Two DualAspects with the same empty component should produce the same identity.
-/
theorem test_converge_dependency (d1 d2 : DualAspect) (h : d1.empty = d2.empty) :
  converge d1 = converge d2 := by
  exact converge_depends_only_on_empty d1 d2 h

/--
TEST: We can create different `DualAspect`s that should converge to the same identity.
-/
example : ∃ (d1 d2 : DualAspect), d1.empty = d2.empty ∧ d1.infinite ≠ d2.infinite → converge d1 = converge d2 := by
  -- Assume there are at least two different infinite manifestations
  let assumption : ∃ i1 i2, i1 ≠ i2 := ⟨bifurcate.infinite, saturate (actualize test_empty)⟩ -- This is a bit of a hack
  by_cases h_inf_exists : ∃ i1 i2 : manifest the_origin Aspect.infinite, i1 ≠ i2
  · obtain ⟨inf1, inf2, h_inf_neq⟩ := h_inf_exists
    let d1 : DualAspect := { empty := test_empty, infinite := inf1, complementary := by simp, inseparable := trivial }
    let d2 : DualAspect := { empty := test_empty, infinite := inf2, complementary := by simp, inseparable := trivial }
    use d1, d2
    constructor
    · simp
    · intro
      exact converge_depends_only_on_empty d1 d2 (by simp)
  · simp at h_inf_exists
    -- If all infinite manifestations are equal, the premise `d1.infinite ≠ d2.infinite` is false, so the implication is true.
    let d1 : DualAspect := { empty := test_empty, infinite := test_infinite, complementary := by simp, inseparable := trivial }
    use d1, d1
    constructor
    · rfl
    · intro h_false
      contradiction

/-!
## 2. Identity Genesis Tests
-/

/-- TEST: Any given identity must arise from a DualAspect. -/
theorem test_identity_requires_duality (i : manifest the_origin Aspect.identity) :
  ∃ (d : DualAspect), i = converge d := by
  obtain ⟨e, inf, dual, he, hinf, hi⟩ := identity_from_both i
  use dual
  exact hi

/-!
## 3. Derived Actualization Tests
-/

/--
TEST: The `actualize` function is well-defined and produces an identity.
-/
example (e : manifest the_origin Aspect.empty) :
  ∃ (i : manifest the_origin Aspect.identity), i = actualize e := by
  use actualize e

/--
TEST: The `actualize_surjective` theorem holds.
This is a critical validation of the refactored logic.
-/
theorem test_actualize_is_surjective :
  Function.Surjective actualize := by
  -- This test simply confirms that the proof in the main file is accepted.
  exact actualize_surjective

/--
TEST: For any identity, a preimage under `actualize` can be found.
-/
theorem test_preimage_exists_for_identity (i : manifest the_origin Aspect.identity) :
  ∃ (e : manifest the_origin Aspect.empty), actualize e = i := by
  -- This is the definition of surjectivity, which we just proved.
  exact actualize_surjective i

/-!
## 4. Circle Integrity Tests
-/

/--
TEST: The `circle_path` function is well-defined.
-/
example (e : manifest the_origin Aspect.empty) :
  ∃ (e' : manifest the_origin Aspect.empty), e' = circle_path e := by
  use circle_path e

/--
TEST: The `circle_closes` axiom holds for the `circle_path`.
This confirms the fundamental cycle is intact after the refactor.
-/
theorem test_circle_closure (e : manifest the_origin Aspect.empty) :
  circle_path e = e := by
  exact circle_closes e

/--
TEST: The information loss theorem still holds.
The proof should be valid with the new `actualize` definition.
-/
theorem test_circle_is_not_injective :
  ¬(Function.Injective (fun e => saturate (actualize e))) := by
  exact circle_not_injective

end GIP.Origin.Tests