/-
Morphism definitions for the Gen category
Based on categorical/definitions/gen_category_axioms_v2.md Section 2.2
-/

import Gen.Basic

namespace Gen

-- Morphisms in Gen category
-- We define when morphisms exist between objects
-- From gen_category_axioms_v2.md Section 2.2
inductive GenMorphism : GenObj → GenObj → Type where
  -- Identity morphisms (Category axiom requirement)
  | id_empty : GenMorphism ∅ ∅
  | id_unit : GenMorphism 𝟙 𝟙
  | id_nat (n : Nat) : GenMorphism (GenObj.nat n) (GenObj.nat n)

  -- Genesis morphism: ∅ → 𝟙 (register1_unit_v2.md Section 1.2)
  | genesis : GenMorphism ∅ 𝟙

  -- Instantiation morphisms: 𝟙 → n (register1_unit_v2.md Section 3.1)
  | instantiation (n : Nat) : GenMorphism 𝟙 (GenObj.nat n)

  -- Divisibility morphisms: n → m when n | m (register2_numeric_v2.md Section 3)
  | divisibility (n m : Nat) (h : ∃ k, m = n * k) :
      GenMorphism (GenObj.nat n) (GenObj.nat m)

  -- Composition of morphisms
  | comp {X Y Z : GenObj} :
      GenMorphism X Y → GenMorphism Y Z → GenMorphism X Z

-- Notation for common morphisms
notation "γ" => GenMorphism.genesis
notation "ι" => GenMorphism.instantiation

-- Helper function to get identity morphism for any object
def idMorph (X : GenObj) : GenMorphism X X :=
  match X with
  | .empty => GenMorphism.id_empty
  | .unit => GenMorphism.id_unit
  | .nat n => GenMorphism.id_nat n

-- Composition notation
infixr:80 " ∘ " => GenMorphism.comp

-- Helper: Check if a natural number divides another
def divides (n m : Nat) : Prop := ∃ k, m = n * k

-- Decision procedure for divisibility
instance (n m : Nat) : Decidable (divides n m) := by
  unfold divides
  sorry -- TODO: implement divisibility decision procedure

-- φ notation for divisibility morphisms
notation "φ[" n "," m "]" => GenMorphism.divisibility n m

end Gen