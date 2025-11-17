/-
PURE GIP Basic definitions - Phase 0 Refactoring
Only Register 0 (∅) and Register 1 (𝟙) - numbers emerge via projection

This is the CORRECT GIP foundation as specified.
-/

universe u

namespace Gen

/- ## Pure GIP Objects

GIP Foundation has exactly TWO objects:
- ∅ (Register 0): Pre-mathematical potential
- 𝟙 (Register 1): Proto-unity, mediation point

Natural numbers are NOT objects in Gen. They emerge via:
  F_R: Gen → CommRing, then project to ℕ

This separation is ESSENTIAL for:
1. Non-circular foundation (no arithmetic assumptions in Gen)
2. Ontological purity (∅ and 𝟙 are pre-mathematical)
3. Proper projection theory (structure emerges, not assumed)
-/

inductive GenObj : Type where
  | empty : GenObj                    -- Register 0: ∅ (pure potential)
  | unit : GenObj                     -- Register 1: 𝟙 (proto-unity)

-- Notation for convenience
notation "∅" => GenObj.empty
notation "𝟙" => GenObj.unit

-- Decidable equality for GenObj (trivial with only 2 objects)
instance : DecidableEq GenObj := fun a b =>
  match a, b with
  | .empty, .empty => isTrue rfl
  | .unit, .unit => isTrue rfl
  | .empty, .unit => isFalse GenObj.noConfusion
  | .unit, .empty => isFalse GenObj.noConfusion

/- ## Register Classification

While GenObj only has ∅ and 𝟙, we define register levels conceptually:
- Register 0: ∅ (potential)
- Register 1: 𝟙 (unity)
- Register 2: Emerges via F_R projection (not in Gen itself)
-/

inductive RegisterLevel : Type where
  | zero : RegisterLevel    -- Pre-mathematical potential
  | one : RegisterLevel     -- Proto-unity
  deriving DecidableEq

def register : GenObj → RegisterLevel
  | .empty => .zero
  | .unit => .one

/- ## Ontological Properties

These properties capture the ontological structure of GIP:
- ∅ has no internal structure (potential)
- 𝟙 emerges from ∅ via genesis γ
- All structure emerges from 𝟙 via projections
-/

-- GenMorphism is defined in Morphisms.lean
-- empty_is_initial and genesis_unique are proven in Register0.lean, Register1.lean,
-- and ModalTopology.CategoricalUniqueness using standard categorical axioms

end Gen
