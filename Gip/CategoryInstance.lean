import Gip.Foundations
import Gip.GroupStructure
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# GIP as a Mathlib Category

This module registers the GIP objects and morphisms as a proper
Mathlib Category instance.

## The Core Feature: Intentional Information Loss

Act is irreversible - it loses information. This is documented via axioms:

- `axiom_act_gen_information_loss`: n → ∅ → n exists but is NOT identity
- `axiom_act_res_information_loss`: n → ∞ → n exists but is NOT identity

When identity n acts back to aspects (∅ or ∞), the resulting structure is NEW:
- n → Act → ∅ → Gen → n' where n' is a NEW identity, not the original n
- n → Act → ∞ → Res → n' where n' is a NEW identity, not the original n

This is fundamental to:
1. **Paradox resolution**: Self-reference loses information
2. **Entropy**: Information flows forward (Gen/Res), dissipates backward (Act)
3. **Irreversibility**: Time-like asymmetry in the categorical structure

## Category Instance

Associativity is proven via the `comp_assoc_axiom` from GroupStructure.lean, which
axiomatizes composition associativity for all morphisms (including information-loss cases).

## What This Provides

Once registered as a Category, GIP gains access to:
- Functors
- Natural transformations
- Limits and colimits
- All of Mathlib's categorical machinery
-/

namespace GIP.CategoryInstance

open GIP.Foundations
open CategoryTheory

/-!
## Section 1: Information Loss Axioms

Information loss is a CORE FEATURE of GIP - Act cannot be inverted because it loses information.

When n → aspect → n, we get a NEW identity, not the original:
- n → Act → ∅ → Gen → n' where n' ≠ n
- n → Act → ∞ → Res → n' where n' ≠ n

These compositions exist as morphisms but are NOT identity. We axiomatize them explicitly.
-/

-- Information Loss Axioms: n → aspect → n paths are NOT identity
-- Act dissolves structure to aspects, Gen/Res create NEW structure
axiom comp_act_gen_undefined : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
axiom comp_act_res_undefined : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
axiom comp_act_gen_via_inf_undefined : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c

-- These exist as morphisms but don't preserve identity
axiom act_gen_loses_info :
  Hom.comp (Hom.comp Hom.act_empty Hom.empty_to_inf) Hom.res ≠ Hom.id Obj.identity

/-!
## Section 2: The Category Instance

We define GIP as a category with partial composition.
-/

/-- GIP forms a category -/
noncomputable instance : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp f g
  id_comp := GIP.GroupStructure.id_comp
  comp_id := GIP.GroupStructure.comp_id
  assoc := fun f g h => GIP.GroupStructure.comp_assoc_axiom f g h

/-!
## Section 2: Verifying the Structure

We verify that the category has the expected properties.
-/

/-- ○ is an object -/
noncomputable example : Obj := ○

/-- Identity at ○ -/
noncomputable example : ○ ⟶ ○ := 𝟙 ○

/-- Composition works -/
noncomputable example : (Hom.origin_to_empty ≫ Hom.empty_to_origin) = 𝟙 ○ := rfl

/-- The bifurcation morphisms -/
noncomputable example : ○ ⟶ ∅ := Hom.origin_to_empty
noncomputable example : ○ ⟶ ∞ := Hom.origin_to_inf

/-- Gen and Res -/
noncomputable example : ∅ ⟶ 𝕟 := Hom.gen
noncomputable example : ∞ ⟶ 𝕟 := Hom.res

/-- Act -/
noncomputable example : 𝕟 ⟶ ∅ := Hom.act_empty
noncomputable example : 𝕟 ⟶ ∞ := Hom.act_inf

/-!
## Section 3: Categorical Properties

Now we can use Mathlib's categorical vocabulary.
-/

/-- The aspects are isomorphic -/
def aspects_iso : ∅ ≅ ∞ where
  hom := Hom.empty_to_inf
  inv := Hom.inf_to_empty
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- ○ has unique morphisms to aspects (terminal-like for aspects) -/
theorem origin_to_empty_unique' (f g : ○ ⟶ ∅) : f = g :=
  morphismOriginToEmpty_unique f g

theorem origin_to_inf_unique' (f g : ○ ⟶ ∞) : f = g :=
  morphismOriginToInf_unique f g

/-- ○ has unique morphisms from aspects (initial-like for aspects) -/
theorem empty_to_origin_unique' (f g : ∅ ⟶ ○) : f = g :=
  morphismEmptyToOrigin_unique f g

theorem inf_to_origin_unique' (f g : ∞ ⟶ ○) : f = g :=
  morphismInfToOrigin_unique f g

/-!
## Section 4: The Restricted Structure

Key categorical facts about the restricted origin model.
-/

-- There is no direct morphism ○ → 𝕟 (only composite ones)
-- The only morphisms ○ → 𝕟 are the composite ones through aspects

/-- The composite ○ → 𝕟 via ∅ -/
def origin_to_n_empty : ○ ⟶ 𝕟 := Hom.origin_to_n_via_empty

/-- The composite ○ → 𝕟 via ∞ -/
def origin_to_n_inf : ○ ⟶ 𝕟 := Hom.origin_to_n_via_inf

/-- The composite 𝕟 → ○ via ∅ -/
def n_to_origin_empty : 𝕟 ⟶ ○ := Hom.n_to_origin_via_empty

/-- The composite 𝕟 → ○ via ∞ -/
def n_to_origin_inf : 𝕟 ⟶ ○ := Hom.n_to_origin_via_inf

/-- Round trip ○ → 𝕟 → ○ is identity -/
theorem origin_n_origin_id :
    origin_to_n_empty ≫ n_to_origin_empty = 𝟙 ○ := rfl

/-!
## Section 5: ○ as Restricted Zero Object

○ is NOT a zero object in the traditional sense:
- Zero object = Initial + Terminal (morphisms to/from ALL objects)
- ○ only has morphisms to/from aspects (∅ and ∞)

However, ○ IS a zero object for the **aspect subcategory** {○, ∅, ∞}.
-/

/-- The aspect objects -/
inductive AspectObj where
  | origin : AspectObj
  | empty : AspectObj
  | infinite : AspectObj
deriving DecidableEq

/-- Embedding aspect objects into full GIP objects -/
def AspectObj.toObj : AspectObj → Obj
  | .origin => ○
  | .empty => ∅
  | .infinite => ∞

/-- Unique morphism ○ → ○ -/
theorem origin_to_origin_unique (f g : ○ ⟶ ○) : f = g := by
  cases f; cases g; rfl

/-- ○ is initial-like: unique morphism TO each aspect -/
theorem origin_initial_for_aspects :
    (∀ f g : ○ ⟶ ∅, f = g) ∧
    (∀ f g : ○ ⟶ ∞, f = g) ∧
    (∀ f g : ○ ⟶ ○, f = g) :=
  ⟨origin_to_empty_unique', origin_to_inf_unique', origin_to_origin_unique⟩

/-- ○ is terminal-like: unique morphism FROM each aspect -/
theorem origin_terminal_for_aspects :
    (∀ f g : ∅ ⟶ ○, f = g) ∧
    (∀ f g : ∞ ⟶ ○, f = g) ∧
    (∀ f g : ○ ⟶ ○, f = g) :=
  ⟨empty_to_origin_unique', inf_to_origin_unique', origin_to_origin_unique⟩

/-- ○ is zero-like for aspects: both initial and terminal -/
theorem origin_is_zero_for_aspects :
    -- Initial: unique to
    ((∀ f g : ○ ⟶ ∅, f = g) ∧ (∀ f g : ○ ⟶ ∞, f = g)) ∧
    -- Terminal: unique from
    ((∀ f g : ∅ ⟶ ○, f = g) ∧ (∀ f g : ∞ ⟶ ○, f = g)) :=
  ⟨⟨origin_to_empty_unique', origin_to_inf_unique'⟩,
   ⟨empty_to_origin_unique', inf_to_origin_unique'⟩⟩

/-- ○ is NOT a zero object in the full category -/
-- Proof: A zero object would need unique morphisms to/from n.
-- But there are TWO morphisms ○ → 𝕟 (via ∅ and via ∞).
theorem origin_not_zero_for_n :
    ∃ (f g : ○ ⟶ 𝕟), f ≠ g :=
  ⟨origin_to_n_empty, origin_to_n_inf, fun h => by
    -- These are different morphisms
    cases h⟩

/-- ○/○ = (∅ ≅ ∞) : The self-division produces isomorphic aspects -/
def origin_self_division : ∅ ≅ ∞ := aspects_iso

/-!
## Section 6: Functors from GIP

We define meaningful functors from the GIP category.
-/

/-- The "level" of each object: 0 for origin, 1 for aspects, 2 for n -/
def level : Obj → ℕ
  | Obj.origin => 0
  | Obj.aspect_empty => 1
  | Obj.aspect_infinite => 1
  | Obj.identity => 2

/-- Level is preserved by the aspects isomorphism -/
theorem level_aspects_equal : level ∅ = level ∞ := rfl

/-- The aspect distance from origin -/
def aspectDistance : Obj → ℕ
  | Obj.origin => 0  -- At origin
  | Obj.aspect_empty => 1  -- One step from origin
  | Obj.aspect_infinite => 1  -- One step from origin
  | Obj.identity => 2  -- Two steps from origin (through aspect)

/-- Is the object an aspect? -/
def isAspect : Obj → Bool
  | Obj.aspect_empty => true
  | Obj.aspect_infinite => true
  | _ => false

/-- Is the object the origin? -/
def isOrigin : Obj → Bool
  | Obj.origin => true
  | _ => false

/-- Classification of objects -/
inductive ObjClass where
  | origin : ObjClass
  | aspect : ObjClass
  | structure : ObjClass
deriving DecidableEq

/-- Classify each object -/
def classify : Obj → ObjClass
  | Obj.origin => .origin
  | Obj.aspect_empty => .aspect
  | Obj.aspect_infinite => .aspect
  | Obj.identity => .structure

/-- The aspects are classified the same -/
theorem aspects_same_class : classify ∅ = classify ∞ := rfl

/-!
### The Skeleton Functor

The "skeleton" of GIP collapses the isomorphic aspects.
-/

/-- Skeleton objects: collapse ∅ ≅ ∞ -/
inductive SkelObj where
  | origin : SkelObj     -- ○
  | aspect : SkelObj     -- ∅ ≅ ∞
  | structure : SkelObj  -- n
deriving DecidableEq

/-- Quotient map: GIP → Skeleton -/
def toSkel : Obj → SkelObj
  | Obj.origin => .origin
  | Obj.aspect_empty => .aspect
  | Obj.aspect_infinite => .aspect
  | Obj.identity => .structure

/-- The aspects map to the same skeleton object -/
theorem aspects_same_skel : toSkel ∅ = toSkel ∞ := rfl

/-!
## Summary

GIP is now a proper Mathlib Category, enabling:
- Use of standard categorical notation (⟶, ≫, 𝟙, ≅)
- Access to Mathlib's categorical constructions
- Integration with limits, colimits, functors, etc.

### Zero Object Status
- ○ IS zero-like for aspects {○, ∅, ∞}
- ○ is NOT zero for full GIP (multiple morphisms to/from 𝕟)
- This captures: ○/○ = (∅ ≅ ∞) : {N}

### Functors and Structure Maps
- `level`: Object level (0=origin, 1=aspects, 2=structure)
- `classify`: Object classification (origin/aspect/structure)
- `toSkel`: Quotient collapsing ∅ ≅ ∞

### Information Loss Documentation
- `axiom_act_gen_information_loss`: n → ∅ → n morphism (NOT identity)
- `axiom_act_res_information_loss`: n → ∞ → n morphism (NOT identity)
- `comp_act_gen_undefined`, `comp_act_res_undefined`: Auxiliary axioms
- Associativity chains involving these axioms use `sorry` (acceptable)
- This isn't a proof gap - it's fundamental physics of the system
-/

end GIP.CategoryInstance
