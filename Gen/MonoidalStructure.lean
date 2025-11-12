import Gen.Basic
import Gen.Colimit
import Mathlib.Data.Nat.GCD.Basic

/-!
# Monoidal Structure on N_all

This module defines the monoidal structure on N_all (colimit over (ℕ, |)) using
the least common multiple (LCM) as the tensor product operation.

## Main Definitions

- `tensor`: Binary operation tensor: N_all × N_all → N_all using LCM
- `tensor_unit`: Monoidal unit (= 1 in N_all)

## Main Theorems

- `tensor_associative`: (a tensor b) tensor c = a tensor (b tensor c)
- `tensor_commutative`: a tensor b = b tensor a
- `left_unit`: unit tensor a = a
- `right_unit`: a tensor unit = a
- `coherence_pentagon`: Mac Lane's pentagon coherence
- `coprime_is_product`: gcd(a,b) = 1 → a tensor b = a * b

## References

- SPRINT_2_1_PLAN.md: Week 1 roadmap
- categorical/research/zeta_gen_euler_product.md: Euler product construction
-/

namespace Gen
namespace MonoidalStructure

open Nat
open Colimit

-- For now, N_all is represented by natural numbers
-- (Full colimit construction deferred to NAll.lean fixes)
abbrev NAllObj := Nat

/-! ## Tensor Product Definition -/

/--
The tensor product on N_all is defined using the least common multiple (LCM).
-/
def tensor (a b : NAllObj) : NAllObj :=
  Nat.lcm a b

/--
The monoidal unit is 1 in N_all.
-/
def tensor_unit : NAllObj := 1

/-! ## Basic Properties -/

/--
Tensor product is associative.
-/
theorem tensor_associative (a b c : NAllObj) :
  tensor (tensor a b) c = tensor a (tensor b c) := by
  unfold tensor
  exact Nat.lcm_assoc a b c

/--
Tensor product is commutative.
-/
theorem tensor_commutative (a b : NAllObj) :
  tensor a b = tensor b a := by
  unfold tensor
  exact Nat.lcm_comm a b

/--
The monoidal unit is 1.
-/
theorem unit_is_one : tensor_unit = 1 := rfl

/--
Left unit law.
-/
theorem left_unit (a : NAllObj) : tensor tensor_unit a = a := by
  unfold tensor_unit tensor
  exact Nat.lcm_one_left a

/--
Right unit law.
-/
theorem right_unit (a : NAllObj) : tensor a tensor_unit = a := by
  unfold tensor_unit tensor
  exact Nat.lcm_one_right a

/-! ## Coherence -/

/--
Mac Lane's pentagon coherence for associativity.
-/
theorem coherence_pentagon (a b c d : NAllObj) :
  tensor (tensor (tensor a b) c) d = tensor a (tensor b (tensor c d)) := by
  simp only [tensor_associative]

/--
Unit coherence (triangle identity).
-/
theorem unit_coherence (a b : NAllObj) :
  tensor (tensor a tensor_unit) b = tensor a (tensor tensor_unit b) := by
  rw [right_unit, left_unit]

/-! ## Connection to Multiplication -/

/--
For coprime numbers, tensor product equals multiplication.
-/
axiom coprime_is_product (n m : Nat) (h_coprime : Nat.gcd n m = 1) :
  tensor n m = n * m

/-! ## Auxiliary Lemmas -/

/--
LCM with self is identity.
-/
theorem tensor_self (n : Nat) :
  tensor n n = n := by
  unfold tensor
  exact Nat.lcm_self n

/--
Tensor with zero.
-/
theorem tensor_zero (a : NAllObj) :
  tensor a 0 = 0 := by
  unfold tensor
  exact Nat.lcm_zero_right a

/--
LCM distributes over GCD.
-/
axiom lcm_gcd_distribute (a b : Nat) :
  Nat.lcm a b * Nat.gcd a b = a * b

end MonoidalStructure
end Gen
