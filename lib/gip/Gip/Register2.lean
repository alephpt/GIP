/-
Register 2: The Numeric Objects n
Based on categorical/definitions/register2_numeric_v2.md

STUB: This module contains axioms for now. Full proofs to be completed later.
-/

import Gip.Basic
import Gip.Morphisms
import Gip.Register0
import Gip.Register1

namespace Gen
namespace Register2

-- Theorem 2.1: Unique morphism from unit
theorem unique_morphism_from_unit (n : Nat) :
  ∀ (f : GenMorphism 𝟙 (GenObj.nat n)), f = ι n := by
  exact Register1.unique_morphism_to_nat n

-- Theorem 2.2: Universal factorization from empty
theorem morphism_from_empty (n : Nat) :
  ∀ (f : GenMorphism ∅ (GenObj.nat n)), f = GenMorphism.comp γ (ι n) := by
  exact Register1.universal_factorization n

-- Theorem 2.3: No morphisms to previous registers
theorem no_morphisms_to_previous_registers (n : Nat) :
  (∀ (f : GenMorphism (GenObj.nat n) ∅), False) ∧
  (∀ (f : GenMorphism (GenObj.nat n) 𝟙), False) := by
  constructor
  · intro f
    sorry
  · exact Register1.no_morphisms_from_nat_to_unit n

-- Helper: divisibility
def dvd (n m : Nat) : Prop := ∃ k, m = n * k

-- Reflexivity
theorem divisibility_reflexive (n : Nat) : dvd n n := by
  unfold dvd
  exact ⟨1, (Nat.mul_one n).symm⟩

-- Transitivity
theorem divisibility_transitive (n m k : Nat) :
  dvd n m → dvd m k → dvd n k := by
  intro ⟨a, ha⟩ ⟨b, hb⟩
  unfold dvd
  refine ⟨a * b, ?_⟩
  calc k = m * b := hb
       _ = (n * a) * b := by rw [← ha]
       _ = n * (a * b) := Nat.mul_assoc n a b

-- One divides all
theorem one_dvd_n (n : Nat) : dvd 1 n := by
  unfold dvd
  exact ⟨n, (Nat.one_mul n).symm⟩

-- Axioms for divisibility morphisms (TODO: prove these)
axiom divisibility_morphism_criterion : ∀ (n m : Nat),
  Nonempty (GenMorphism (GenObj.nat n) (GenObj.nat m)) ↔ dvd n m

axiom divisibility_morphism_unique : ∀ (n m : Nat) (h : dvd n m),
  ∀ (f : GenMorphism (GenObj.nat n) (GenObj.nat m)),
    f = GenMorphism.divisibility n m h

axiom identity_as_divisibility : ∀ (n : Nat),
  GenMorphism.id_nat n = GenMorphism.divisibility n n (divisibility_reflexive n)

axiom divisibility_composition : ∀ (n m k : Nat) (hnm : dvd n m) (hmk : dvd m k),
  GenMorphism.comp (GenMorphism.divisibility n m hnm) (GenMorphism.divisibility m k hmk) =
  GenMorphism.divisibility n k (divisibility_transitive n m k hnm hmk)

axiom critical_identity : ∀ (n m : Nat) (h : dvd n m),
  GenMorphism.comp (ι n) (GenMorphism.divisibility n m h) = ι m

axiom instantiation_factors_through_one : ∀ (n : Nat) (h : dvd 1 n),
  ι n = GenMorphism.comp (ι 1) (GenMorphism.divisibility 1 n h)

end Register2
end Gen
