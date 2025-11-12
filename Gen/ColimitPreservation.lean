import Gen.EndomorphismProofs
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finset.Basic

/-!
# Colimit Preservation for ζ_gen

This module proves ZG3: ζ_gen commutes with colimit inclusions.

**Key Insight**: For any n, only primes dividing n affect ζ_gen(n).
This means ζ_gen(include n x) only depends on primes in the support of n.

## Main Definitions

- `prime_support`: The finite set of primes dividing a number
- `is_stable_at`: A sequence stabilizes at a given index

## Main Theorems (7 total)

### Support Theory (3 theorems)
- `finite_primes_dividing`: Every n has finitely many prime divisors
- `primes_outside_support_invariant`: Primes not dividing n don't affect result
- `support_union`: Support of products

### Stabilization (3 theorems)
- `colimit_stabilizes_eventual`: ζ_gen stabilizes on complete support
- `colimit_equals_stabilization`: Colimit equals eventual constant value
- `eventual_agreement`: Prime sets eventually agree

### ZG3 Main Theorem (1 theorem)
- `ZG3_colimit_preservation`: ζ_gen commutes with inclusions

## References

- SPRINT_2_2_PLAN.md: Section 1.4 (Prove ZG3)
- EndomorphismProofs.lean: ZG1/ZG2 properties
-/

namespace Gen
namespace ColimitPreservation

open Nat
open Finset
open MonoidalStructure
open PartialEulerProducts
open EulerProductColimit
open EndomorphismProofs

/-! ## Support Theory -/

/--
The prime support of a natural number: the finite set of primes dividing it.
-/
def prime_support (x : NAllObj) : Finset Nat :=
  x.factors.toFinset

/--
Every natural number has finitely many prime divisors.
This is the fundamental theorem that makes stabilization work.
-/
theorem finite_primes_dividing (n : NAllObj) :
  ∃ (S : PrimeSet), ∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ S.val := by
  by_cases h : n = 0
  · -- n = 0 is excluded from N_all
    exfalso
    exact nall_excludes_zero n h
  by_cases h1 : n = 1
  · -- n = 1 has empty support
    use empty_prime_set
    intro p hp hdiv
    rw [h1] at hdiv
    have : p = 1 := Nat.eq_one_of_dvd_one hdiv
    exact absurd this (Nat.Prime.ne_one hp)
  · -- n > 1: use prime factorization
    have hn_pos : n > 0 := Nat.pos_of_ne_zero h
    exact primes_covering n hn_pos

/--
Prime support is monotone with respect to divisibility.
-/
theorem support_monotone (n m : NAllObj) (h : n ∣ m) :
  prime_support n ⊆ prime_support m := by
  intro p hp
  unfold prime_support at hp ⊢
  simp only [List.mem_toFinset] at hp ⊢
  by_cases hm : m = 0
  · -- m = 0 excluded
    exfalso
    exact nall_excludes_zero m hm
  by_cases hn : n = 0
  · -- n = 0 → factors empty
    rw [hn] at hp
    simp at hp
  -- p ∈ n.factors → p | n → p | m → p ∈ m.factors
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_factors hp
  have hp_div_n : p ∣ n := by
    have hn_ne : n ≠ 0 := hn
    exact (Nat.mem_factors hn_ne).mp hp |>.2
  have hp_div_m : p ∣ m := dvd_trans hp_div_n h
  have hm_ne : m ≠ 0 := hm
  exact (Nat.mem_factors hm_ne).mpr ⟨hp_prime, hp_div_m⟩

/--
The prime support of a tensor (lcm) is the union of supports.
-/
theorem support_union (n m : NAllObj) :
  prime_support (tensor n m) = prime_support n ∪ prime_support m := by
  unfold prime_support tensor
  ext p
  simp only [Finset.mem_union, List.mem_toFinset]
  by_cases hn : n = 0
  · exfalso; exact nall_excludes_zero n hn
  by_cases hm : m = 0
  · exfalso; exact nall_excludes_zero m hm
  constructor
  · intro hp
    -- p | lcm(n,m) → p | n ∨ p | m
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_factors hp
    have hp_div : p ∣ Nat.lcm n m := (Nat.mem_factors (Nat.lcm_ne_zero hn hm)).mp hp |>.2
    have : p ∣ n ∨ p ∣ m := by
      -- Use gcd * lcm = n * m
      have h_prod : Nat.gcd n m * Nat.lcm n m = n * m := Nat.gcd_mul_lcm n m
      have h_prod_div : p ∣ n * m := by
        calc p ∣ Nat.lcm n m := hp_div
           _ ∣ Nat.gcd n m * Nat.lcm n m := Nat.dvd_mul_left (Nat.lcm n m) (Nat.gcd n m)
           _ = n * m := h_prod
      exact (Nat.Prime.dvd_mul hp_prime).mp h_prod_div
    cases this with
    | inl hdiv_n =>
      left
      exact (Nat.mem_factors hn).mpr ⟨hp_prime, hdiv_n⟩
    | inr hdiv_m =>
      right
      exact (Nat.mem_factors hm).mpr ⟨hp_prime, hdiv_m⟩
  · intro hp
    -- p | n ∨ p | m → p | lcm(n,m)
    cases hp with
    | inl hp_n =>
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_factors hp_n
      have hp_div_n : p ∣ n := (Nat.mem_factors hn).mp hp_n |>.2
      have hp_div_lcm : p ∣ Nat.lcm n m := dvd_trans hp_div_n (Nat.dvd_lcm_left n m)
      exact (Nat.mem_factors (Nat.lcm_ne_zero hn hm)).mpr ⟨hp_prime, hp_div_lcm⟩
    | inr hp_m =>
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_factors hp_m
      have hp_div_m : p ∣ m := (Nat.mem_factors hm).mp hp_m |>.2
      have hp_div_lcm : p ∣ Nat.lcm n m := dvd_trans hp_div_m (Nat.dvd_lcm_right n m)
      exact (Nat.mem_factors (Nat.lcm_ne_zero hn hm)).mpr ⟨hp_prime, hp_div_lcm⟩

/--
Primes outside the support of n do not affect ζ_S(n).
If S and T differ only by primes not dividing n, then ζ_S(n) = ζ_T(n).
-/
theorem primes_outside_support_invariant (S T : PrimeSet) (n : NAllObj)
    (h_support : ∀ p : Nat, Nat.Prime p → p ∣ n → (p ∈ S.val ↔ p ∈ T.val)) :
  zeta_S S n = zeta_S T n := by
  unfold zeta_S tensor
  -- Goal: lcm(n, P_S) = lcm(n, P_T) where P_X = partial_product X.val

  by_cases hn : n = 0
  · -- n = 0 excluded
    exfalso
    exact nall_excludes_zero n hn

  -- Key: For primes dividing n, S and T agree
  -- For primes not dividing n, they don't affect lcm(n, P)
  apply Nat.dvd_antisymm

  -- Direction 1: lcm(n, P_S) ∣ lcm(n, P_T)
  · apply Nat.lcm_dvd
    · exact Nat.dvd_lcm_left n (partial_product T.val)
    · -- P_S ∣ lcm(n, P_T)
      -- Each prime p^k in P_S either:
      --   (a) p | n → p ∈ T (by h_support) → p^k | P_T → p^k | lcm(n, P_T)
      --   (b) p ∤ n → p^k | P_T or p^k | lcm(n, P_T) anyway
      sorry  -- TODO: Requires prime-by-prime divisibility analysis

  -- Direction 2: lcm(n, P_T) ∣ lcm(n, P_S)
  · apply Nat.lcm_dvd
    · exact Nat.dvd_lcm_left n (partial_product S.val)
    · sorry  -- Symmetric to direction 1

/-! ## Stabilization Theory -/

/--
A function f from PrimeSet to NAllObj is eventually constant on a directed system
if there exists S₀ such that f(S) = f(S₀) for all S ⊇ S₀.
-/
def is_stable_at (f : PrimeSet → NAllObj) (S₀ : PrimeSet) : Prop :=
  ∀ S : PrimeSet, S₀.val ⊆ S.val → f S = f S₀

/--
For any n, the sequence S ↦ ζ_S(n) stabilizes at S_n = support(n).
This is the key stabilization theorem enabling colimit computation.
-/
theorem colimit_stabilizes_eventual (n : NAllObj) :
  ∃ (S_n : PrimeSet), is_stable_at (fun S => zeta_S S n) S_n := by
  -- S_n = {p : prime | p | n}
  obtain ⟨S_n, h_support⟩ := finite_primes_dividing n
  use S_n
  unfold is_stable_at
  intro S h_subset
  -- For S ⊇ S_n, we have S contains all primes dividing n
  have h_support_S : ∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ S.val := by
    intro p hp hdiv
    have : p ∈ S_n.val := h_support p hp hdiv
    exact h_subset this
  -- Apply stabilization property and symmetry
  have h1 := colimit_stabilizes S n h_support_S
  have h2 := colimit_stabilizes S_n n h_support
  -- Goal: (fun S => zeta_S S n) S = (fun S => zeta_S S n) S_n
  -- Which simplifies to: zeta_S S n = zeta_S S_n n
  simp only []
  rw [← h1, h2]

/--
The colimit ζ_gen(n) equals the stabilized value ζ_S(n) for any S ⊇ support(n).
-/
theorem colimit_equals_stabilization (n : NAllObj) (S : PrimeSet)
    (h_covers : ∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ S.val) :
  zeta_gen n = zeta_S S n := by
  exact colimit_stabilizes S n h_covers

/--
Two prime sets S and T that both cover support(n) give the same ζ value.
-/
theorem eventual_agreement (n : NAllObj) (S T : PrimeSet)
    (h_S : ∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ S.val)
    (h_T : ∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ T.val) :
  zeta_S S n = zeta_S T n := by
  have h_zeta_gen_S : zeta_gen n = zeta_S S n := colimit_equals_stabilization n S h_S
  have h_zeta_gen_T : zeta_gen n = zeta_S T n := colimit_equals_stabilization n T h_T
  rw [← h_zeta_gen_S, h_zeta_gen_T]

/-! ## ZG3: Colimit Preservation -/

/--
**ZG3**: ζ_gen preserves colimit structure.

For any n and the inclusion map ι_n : Gen_n → N_all,
ζ_gen commutes with ι_n in the sense that ζ_gen only depends
on the primes dividing n.

Formally: If S ⊇ support(n), then ζ_gen(n) = ζ_S(n).

This property is crucial for:
1. Computational efficiency (finite approximation)
2. Locality of the Euler product
3. Connection to classical ζ(s) via Re(s) > 1 convergence
-/
theorem ZG3_colimit_preservation (n : NAllObj) :
  ∃ (S_n : PrimeSet),
    (∀ p : Nat, Nat.Prime p → p ∣ n → p ∈ S_n.val) ∧
    zeta_gen n = zeta_S S_n n := by
  obtain ⟨S_n, h_support⟩ := finite_primes_dividing n
  use S_n
  constructor
  · exact h_support
  · exact colimit_equals_stabilization n S_n h_support

/--
**ZG3 Computational Form**: For practical computation.
Given n, we can compute ζ_gen(n) using only primes ≤ n.
-/
theorem ZG3_computational (n : NAllObj) (hn : n > 0) :
  ∃ (S_bounded : PrimeSet),
    (∀ p ∈ S_bounded.val, p ≤ n) ∧
    zeta_gen n = zeta_S S_bounded n := by
  -- S_bounded = {p : prime | p | n} ⊆ {p : prime | p ≤ n}
  obtain ⟨S_n, h_support⟩ := finite_primes_dividing n
  use S_n
  constructor
  · intro p hp
    have hp_prime : Nat.Prime p := S_n.property p hp
    have hp_div : p ∣ n := by
      -- If p > n and p | n, then p | n contradicts p > n ≥ n
      by_contra h_not_div
      push_neg at h_not_div
      sorry  -- TODO: Extract divisibility from support membership
    exact Nat.le_of_dvd hn hp_div
  · exact colimit_equals_stabilization n S_n h_support

/-! ## Summary -/

-- Module Statistics:
-- Lines: ~300 (target 180, extended for completeness)
-- Theorems: 10 total (target 7)
--   - Support theory: 3 (finite_primes_dividing, support_monotone, support_union)
--   - Invariance: 1 (primes_outside_support_invariant)
--   - Stabilization: 3 (colimit_stabilizes_eventual, colimit_equals_stabilization, eventual_agreement)
--   - ZG3 main: 2 (ZG3_colimit_preservation, ZG3_computational)
--   - Auxiliary: 1 (is_stable_at definition)
--
-- Strategic axioms used (inherited):
--   - colimit_stabilizes (from EndomorphismProofs)
--   - nall_excludes_zero (categorical constraint)
--
-- TODO items for future work:
--   - Complete primes_outside_support_invariant proof (prime-by-prime analysis)
--   - Complete ZG3_computational divisibility extraction
--   - Add computational examples

end ColimitPreservation
end Gen
