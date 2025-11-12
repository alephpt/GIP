/-
Working proofs that demonstrate what we can prove with the current structure
-/

import Gen.Basic
import Gen.Morphisms

namespace Gen

-- Basic distinctness proofs for objects
theorem empty_ne_unit : GenObj.empty ≠ GenObj.unit := by
  intro h
  cases h

theorem nat_ne_empty (n : Nat) : GenObj.nat n ≠ GenObj.empty := by
  intro h
  cases h

theorem nat_ne_unit (n : Nat) : GenObj.nat n ≠ GenObj.unit := by
  intro h
  cases h

theorem nat_injective (n m : Nat) : GenObj.nat n = GenObj.nat m → n = m := by
  intro h
  injection h

-- Trivial identity proofs
theorem id_empty_is_id : GenMorphism.id_empty = GenMorphism.id_empty := rfl
theorem id_unit_is_id : GenMorphism.id_unit = GenMorphism.id_unit := rfl
theorem genesis_is_genesis : GenMorphism.genesis = GenMorphism.genesis := rfl

-- Proof that we can construct compositions
theorem comp_exists {X Y Z : GenObj} (f : GenMorphism X Y) (g : GenMorphism Y Z) :
    ∃ h : GenMorphism X Z, True := by
  exists GenMorphism.comp f g

-- Proof that identity morphisms exist
theorem id_exists_empty : ∃ f : GenMorphism GenObj.empty GenObj.empty, True := by
  exists GenMorphism.id_empty

theorem id_exists_unit : ∃ f : GenMorphism GenObj.unit GenObj.unit, True := by
  exists GenMorphism.id_unit

theorem id_exists_nat (n : Nat) : ∃ f : GenMorphism (GenObj.nat n) (GenObj.nat n), True := by
  exists GenMorphism.id_nat n

-- Proof that genesis exists
theorem genesis_exists : ∃ f : GenMorphism GenObj.empty GenObj.unit, True := by
  exists GenMorphism.genesis

-- Proof that instantiation exists
theorem instantiation_exists (n : Nat) :
    ∃ f : GenMorphism GenObj.unit (GenObj.nat n), True := by
  exists GenMorphism.instantiation n

end Gen