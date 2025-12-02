import Gip.Axioms
import Gip.Foundations
import Mathlib.CategoryTheory.Category.Basic

/-!
# GIP Core Theorems

This module provides a central library of fundamental theorems derived from the
GIP axioms.

By proving these essential facts here, we avoid re-proving them in multiple
other modules, adhering to the DRY (Don't Repeat Yourself) principle. This
makes the entire codebase cleaner and more robust.
-/

namespace GIP.Core

open GIP.Foundations
open GIP.Axioms
open CategoryTheory

/-!
## Section 1: Core Isomorphism Theorems
-/

/--

**Theorem: The Dual Aspects are Isomorphic.**



This theorem provides a canonical proof that the empty aspect (`∅`) and the

infinite aspect (`∞`) are isomorphic in the categorical sense. This is a

foundational principle of GIP's "Duality from Unity".



The proof constructs an `iso` structure, which requires providing the forward

morphism (`hom`), the backward morphism (`inv`), and proofs that composing

them in both directions results in the identity morphism.

-/

theorem aspects_are_isomorphic : ∅ ≅ ∞ := by

  -- Construct the isomorphism structure

  refine {

    hom := Hom.empty_to_inf,

    inv := Hom.inf_to_empty,

    -- Proof for hom ≫ inv = 𝟙 ∅

    hom_inv_id := by {

      unfold CategoryStruct.comp

      unfold Hom.comp

      -- This composition is defined as `id ∅` in Foundations.lean

      rfl

    },

    -- Proof for inv ≫ hom = 𝟙 ∞

    inv_hom_id := by {

      unfold CategoryStruct.comp

      unfold Hom.comp

      -- This composition is defined as `id ∞` in Foundations.lean

      rfl

    }

  }





/-!

## Section 2: Core Theorems about the Origin (○)

-/



/--

The `AspectObj` inductive type defines the subcategory of GIP that contains

only the Origin and its two dual aspects.

-/

inductive AspectObj : Type where

  | origin : AspectObj

  | empty : AspectObj

  | infinite : AspectObj

deriving DecidableEq



/-- A mapping from the `AspectObj` subcategory to the full `GIP.Obj` type. -/

def AspectObj.toObj : AspectObj → Obj

  | .origin => ○

  | .empty => ∅

  | .infinite => ∞



/--

**Theorem: The Origin is an initial object for the Aspect Subcategory.**



This theorem proves that for every object `A` in the `{○, ∅, ∞}` subcategory,

there exists a unique morphism from `○` to `A`.

-/

theorem origin_is_initial_for_aspects :

  ∀ (A : AspectObj), Nonempty (Unique (○ ⟶ A.toObj)) := by

  intro A

  cases A

  -- Case 1: A = ○

  case origin =>

    fconstructor

    -- Proof that a morphism ○ → ○ exists

    exact ⟨𝟙 ○, by {

      intro g

      cases g; rfl

    }⟩

  -- Case 2: A = ∅

  case empty =>

    fconstructor

    -- Proof that a morphism ○ → ∅ exists

    exact ⟨Hom.origin_to_empty, by {

      intro g; cases g; rfl

    }⟩

  -- Case 3: A = ∞

  case infinite =>

    fconstructor

    -- Proof that a morphism ○ → ∞ exists

    exact ⟨Hom.origin_to_inf, by {

      intro g; cases g; rfl

    }⟩



/--

**Theorem: The Origin is a terminal object for the Aspect Subcategory.**



This theorem proves that for every object `A` in the `{○, ∅, ∞}` subcategory,

there exists a unique morphism from `A` to `○`.

-/

theorem origin_is_terminal_for_aspects :

  ∀ (A : AspectObj), Nonempty (Unique (A.toObj ⟶ ○)) := by

  intro A

  cases A

  -- Case 1: A = ○

  case origin =>

    fconstructor

    exact ⟨𝟙 ○, by {

      intro g; cases g; rfl

    }⟩

  -- Case 2: A = ∅

  case empty =>

    fconstructor

    exact ⟨Hom.empty_to_origin, by {

      intro g; cases g; rfl

    }⟩

  -- Case 3: A = ∞

  case infinite =>

    fconstructor

    exact ⟨Hom.inf_to_origin, by {

      intro g; cases g; rfl

    }⟩



/--



**Theorem: The Origin is a Zero Object for the Aspect Subcategory.**







A zero object is an object that is both initial and terminal. This theorem



combines the previous two proofs to establish that `○` is a zero object



within the restricted context of its aspects. This formalizes a key claim



in the GIP book outline.



-/



theorem origin_is_restricted_zero :



  (∀ (A : AspectObj), Nonempty (Unique (○ ⟶ A.toObj))) ∧



  (∀ (A : AspectObj), Nonempty (Unique (A.toObj ⟶ ○))) :=



by



  constructor



  . exact origin_is_initial_for_aspects



  . exact origin_is_terminal_for_aspects











/-!



## Section 3: The Holographic Principle



-/







/--



**Path Collapse (∅ → ○ → ∅):** Any two paths from the empty aspect to itself



that pass through the Origin are equal.



-/



theorem paths_empty_origin_empty_collapse



    (f₁ f₂ : ∅ ⟶ ○) (g₁ g₂ : ○ ⟶ ∅) :



    f₁ ≫ g₁ = f₂ ≫ g₂ := by



  -- The proof follows from the fact that the individual morphisms are unique.



  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂



  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂



  rw [hf, hg]







/--



**Path Collapse (∅ → ○ → ∞):** Any two paths from the empty aspect to the



infinite aspect that pass through the Origin are equal.



-/



theorem paths_empty_origin_inf_collapse



    (f₁ f₂ : ∅ ⟶ ○) (g₁ g₂ : ○ ⟶ ∞) :



    f₁ ≫ g₁ = f₂ ≫ g₂ := by



  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂



  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂



  rw [hf, hg]







/--



**Path Collapse (∞ → ○ → ∅):** Any two paths from the infinite aspect to the



empty aspect that pass through the Origin are equal.



-/



theorem paths_inf_origin_empty_collapse



    (f₁ f₂ : ∞ ⟶ ○) (g₁ g₂ : ○ ⟶ ∅) :



    f₁ ≫ g₁ = f₂ ≫ g₂ := by



  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂



  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂



  rw [hf, hg]







/--



**Path Collapse (∞ → ○ → ∞):** Any two paths from the infinite aspect to



itself that pass through the Origin are equal.



-/



theorem paths_inf_origin_inf_collapse



    (f₁ f₂ : ∞ ⟶ ○) (g₁ g₂ : ○ ⟶ ∞) :



    f₁ ≫ g₁ = f₂ ≫ g₂ := by



  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂



  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂



  rw [hf, hg]







/--



**Theorem: The Holographic Principle.**







This theorem states that information collapses when passing through the



Origin. Any path between the two aspects that is routed through the Origin



is unique. This is a direct consequence of the Origin being a restricted



zero object for the aspects.



-/



theorem holographic_principle :



  (∀ (f₁ f₂ : ∅ ⟶ ○) (g₁ g₂ : ○ ⟶ ∅), f₁ ≫ g₁ = f₂ ≫ g₂) ∧



  (∀ (f₁ f₂ : ∅ ⟶ ○) (g₁ g₂ : ○ ⟶ ∞), f₁ ≫ g₁ = f₂ ≫ g₂) ∧



  (∀ (f₁ f₂ : ∞ ⟶ ○) (g₁ g₂ : ○ ⟶ ∅), f₁ ≫ g₁ = f₂ ≫ g₂) ∧



  (∀ (f₁ f₂ : ∞ ⟶ ○) (g₁ g₂ : ○ ⟶ ∞), f₁ ≫ g₁ = f₂ ≫ g₂) :=



by



  constructor



  . exact paths_empty_origin_empty_collapse



  . constructor



    . exact paths_empty_origin_inf_collapse



    . constructor



      . exact paths_inf_origin_empty_collapse



      . exact paths_inf_origin_inf_collapse







end GIP.Core




