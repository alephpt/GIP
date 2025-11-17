/-
Basic definitions for the Gen category
Based on categorical/definitions/*_v2.md
-/

universe u

namespace Gen

-- The Gen category has three types of objects
-- From register0_empty_v2.md, register1_unit_v2.md, register2_numeric_v2.md
inductive GenObj : Type where
  | empty : GenObj                    -- Register 0: ∅
  | unit : GenObj                     -- Register 1: 𝟙
  | nat : Nat → GenObj                 -- Register 2: n for each n ∈ ℕ

-- Notation for convenience
notation "∅" => GenObj.empty
notation "𝟙" => GenObj.unit

-- Helper to create numeric objects
def num (n : Nat) : GenObj := GenObj.nat n

-- Decidable equality for GenObj
instance : DecidableEq GenObj := fun a b =>
  match a, b with
  | .empty, .empty => isTrue rfl
  | .unit, .unit => isTrue rfl
  | .nat n, .nat m =>
    if h : n = m then
      isTrue (by rw [h])
    else
      isFalse (by intro heq; cases heq; exact h rfl)
  | .empty, .unit => isFalse GenObj.noConfusion
  | .empty, .nat _ => isFalse GenObj.noConfusion
  | .unit, .empty => isFalse GenObj.noConfusion
  | .unit, .nat _ => isFalse GenObj.noConfusion
  | .nat _, .empty => isFalse GenObj.noConfusion
  | .nat _, .unit => isFalse GenObj.noConfusion

end Gen