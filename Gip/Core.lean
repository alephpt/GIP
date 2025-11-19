/-!
# GIP Core Library

This module defines the foundational structures of the GIP system:
- 4 Object Classes: ∅ (empty), 𝟙 (unit), n, ∞ (infinite)
- 6 Morphism Types: γ, ι, τ, ε, id, f1
- Complete Zero Object Cycle: ○ → ∅ → 𝟙 → n → 𝟙 → ∞ → ○

## The Dual Architecture

**Genesis Path (Emergence - ∅ aspect)**:
- ○ → ∅ (enter potential space)
- γ: ∅ → 𝟙 (actualize proto-unity)
- ι: 𝟙 → n (instantiate to structure)

**Destiny Path (Evaluation - ∞ aspect)**:
- τ: n → 𝟙 (encode/reduce structure)
- ε: 𝟙 → ∞ (erase to completion)
- ∞ → ○ (return to ground state)

## Ontological Insight

The circle IS identity - not a thing traversing a circle.
∅ and ∞ are aspects/manifestations of the zero object ○.
Gen and Dest are dual composite morphisms completing the cycle.
-/

namespace GIP

/-- The four object classes in GIP -/
inductive Obj : Type where
  | empty : Obj     -- ∅ (potential aspect of ○)
  | unit : Obj      -- 𝟙 (proto-unity)
  | n : Obj         -- n (structure/instances)
  | infinite : Obj  -- ∞ (completion aspect of ○)
  deriving Repr, DecidableEq

/-- Notation for empty object -/
scoped notation "∅" => Obj.empty

/-- Notation for unit object -/
scoped notation "𝟙" => Obj.unit

/-- Notation for infinite object -/
scoped notation "∞" => Obj.infinite

/-- Morphisms between GIP objects -/
inductive Hom : Obj → Obj → Type where
  | id {X : Obj} : Hom X X                           -- identity morphisms
  | γ : Hom ∅ 𝟙                                      -- γ: ∅ → 𝟙 (actualize proto-unity)
  | ι {target : Obj} : Hom 𝟙 target                  -- ι: 𝟙 → target (instantiate)
  | τ : Hom Obj.n 𝟙                                  -- τ: n → 𝟙 (reduce/encode structure)
  | ε : Hom 𝟙 ∞                                      -- ε: 𝟙 → ∞ (erase to completion)
  | f1 {X Y : Obj} : Hom X Y                         -- f1: generic morphism
  | comp {X Y Z : Obj} : Hom Y Z → Hom X Y → Hom X Z -- composition
  deriving Repr

/-- Composition operator -/
infixr:90 " ∘ " => Hom.comp

namespace Hom

/-- Identity composition laws -/
axiom id_comp {X Y : Obj} (f : Hom X Y) : id ∘ f = f
axiom comp_id {X Y : Obj} (f : Hom X Y) : f ∘ id = f

/-- Associativity of composition -/
axiom comp_assoc {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X) :
  (h ∘ g) ∘ f = h ∘ (g ∘ f)

/-- Genesis: The emergence path (○ → ∅ → 𝟙 → n)
    Composite morphism representing the ∅ aspect of ○ -/
def Gen : Hom ∅ Obj.n := ι ∘ γ

/-- Destiny: The evaluation path (n → 𝟙 → ∞)
    Composite morphism representing the ∞ aspect of ○ -/
def Dest : Hom Obj.n ∞ := ε ∘ τ

end Hom

end GIP
