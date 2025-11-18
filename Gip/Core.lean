/-!
# GIP Core Library

This module defines the foundational structures of the GIP system:
- 3 Object Classes: ∅ (empty), 𝟙 (unit), n
- 4 Morphism Types: γ, ι, id, f1
-/

namespace GIP

/-- The three object classes in GIP -/
inductive Obj : Type where
  | empty : Obj  -- ∅
  | unit : Obj   -- 𝟙
  | n : Obj      -- n
  deriving Repr, DecidableEq

/-- Notation for empty object -/
scoped notation "∅" => Obj.empty

/-- Notation for unit object -/
scoped notation "𝟙" => Obj.unit

/-- Morphisms between GIP objects -/
inductive Hom : Obj → Obj → Type where
  | id {X : Obj} : Hom X X                           -- identity morphisms
  | γ : Hom ∅ 𝟙                                      -- γ: ∅ → 𝟙
  | ι {target : Obj} : Hom 𝟙 target                  -- ι: 𝟙 → target
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

end Hom

end GIP
