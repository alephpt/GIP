import Gen.ZetaEvaluation
import Gen.PrimeGeneration
import Gen.MonoidalStructure

/-!
# Examples and Validation

Comprehensive examples demonstrating ζ_gen computation and validating ZG1-ZG4 properties.

This module provides:
1. Concrete computations for n ≤ 100
2. Property validation (ZG1 multiplicativity, ZG3 locality)
3. Pattern analysis and documentation
4. Regression tests for known values

## Organization

- **Small Examples** (n ≤ 10): Basic cases, primes and composites
- **Medium Examples** (10 < n ≤ 30): More complex patterns
- **Large Examples** (30 < n ≤ 100): Stress testing
- **Property Validation**: ZG1-ZG4 computational verification
- **Edge Cases**: Boundary conditions and special values

## Expected Patterns

For small n:
- ζ_gen(1) = 1 (unit)
- ζ_gen(prime p) involves primes up to p
- ζ_gen(composite n) involves more primes

## Usage

Uncomment #eval lines to see actual computations.
Use these examples for:
- Verifying correctness
- Understanding ζ_gen behavior
- Debugging computational issues
- Performance benchmarking

-/

namespace Gen
namespace Examples

open ZetaEvaluation
open PrimeGeneration
open MonoidalStructure

/-! ## Small Examples (n ≤ 10) -/

section SmallExamples

-- Unit element
#eval compute_zeta_gen 1  -- Expected: 1

-- Small primes
#eval compute_zeta_gen 2  -- Primes ≤ 2: [2]
#eval compute_zeta_gen 3  -- Primes ≤ 3: [2, 3]
#eval compute_zeta_gen 5  -- Primes ≤ 5: [2, 3, 5]
#eval compute_zeta_gen 7  -- Primes ≤ 7: [2, 3, 5, 7]

-- Powers of 2
#eval compute_zeta_gen 4  -- 2²
#eval compute_zeta_gen 8  -- 2³

-- Composite numbers
#eval compute_zeta_gen 6   -- 2 × 3
#eval compute_zeta_gen 9   -- 3²
#eval compute_zeta_gen 10  -- 2 × 5

end SmallExamples

/-! ## Medium Examples (10 < n ≤ 30) -/

section MediumExamples

-- Primes
#eval compute_zeta_gen 11
#eval compute_zeta_gen 13
#eval compute_zeta_gen 17
#eval compute_zeta_gen 19
#eval compute_zeta_gen 23
#eval compute_zeta_gen 29

-- Powers of 2
#eval compute_zeta_gen 16  -- 2⁴
#eval compute_zeta_gen 32  -- 2⁵ (exceeds range but included for completeness)

-- Highly composite numbers
#eval compute_zeta_gen 12  -- 2² × 3
#eval compute_zeta_gen 18  -- 2 × 3²
#eval compute_zeta_gen 20  -- 2² × 5
#eval compute_zeta_gen 24  -- 2³ × 3
#eval compute_zeta_gen 30  -- 2 × 3 × 5

-- Other composites
#eval compute_zeta_gen 14  -- 2 × 7
#eval compute_zeta_gen 15  -- 3 × 5
#eval compute_zeta_gen 21  -- 3 × 7
#eval compute_zeta_gen 22  -- 2 × 11
#eval compute_zeta_gen 25  -- 5²
#eval compute_zeta_gen 26  -- 2 × 13
#eval compute_zeta_gen 27  -- 3³
#eval compute_zeta_gen 28  -- 2² × 7

end MediumExamples

/-! ## Large Examples (30 < n ≤ 100) -/

section LargeExamples

-- Benchmark values
#eval compute_zeta_gen 50
#eval compute_zeta_gen 60
#eval compute_zeta_gen 70
#eval compute_zeta_gen 80
#eval compute_zeta_gen 90
#eval compute_zeta_gen 100

-- Powers
#eval compute_zeta_gen 64   -- 2⁶
#eval compute_zeta_gen 81   -- 3⁴
#eval compute_zeta_gen 49   -- 7²

-- Highly composite
#eval compute_zeta_gen 36   -- 2² × 3²
#eval compute_zeta_gen 48   -- 2⁴ × 3
#eval compute_zeta_gen 72   -- 2³ × 3²
#eval compute_zeta_gen 96   -- 2⁵ × 3

-- Primes in range
#eval compute_zeta_gen 31
#eval compute_zeta_gen 37
#eval compute_zeta_gen 41
#eval compute_zeta_gen 43
#eval compute_zeta_gen 47
#eval compute_zeta_gen 53
#eval compute_zeta_gen 59
#eval compute_zeta_gen 61
#eval compute_zeta_gen 67
#eval compute_zeta_gen 71
#eval compute_zeta_gen 73
#eval compute_zeta_gen 79
#eval compute_zeta_gen 83
#eval compute_zeta_gen 89
#eval compute_zeta_gen 97

end LargeExamples

/-! ## Property Validation: ZG1 Multiplicativity -/

section ZG1Multiplicativity

/-
ZG1: For coprime n, m: ζ_gen(n ⊗ m) = ζ_gen(n) ⊗ ζ_gen(m)
In computational terms: ζ_gen(n * m) = lcm(ζ_gen(n), ζ_gen(m))
-/

-- Validate for small coprime pairs
def check_multiplicativity (n m : Nat) : Bool :=
  if Nat.gcd n m = 1 then
    compute_zeta_gen (n * m) = Nat.lcm (compute_zeta_gen n) (compute_zeta_gen m)
  else
    true  -- Skip non-coprime pairs

#eval check_multiplicativity 2 3   -- 2 and 3 are coprime
#eval check_multiplicativity 2 5   -- 2 and 5 are coprime
#eval check_multiplicativity 3 5   -- 3 and 5 are coprime
#eval check_multiplicativity 2 7   -- 2 and 7 are coprime
#eval check_multiplicativity 3 7   -- 3 and 7 are coprime
#eval check_multiplicativity 5 7   -- 5 and 7 are coprime

-- More complex coprime pairs
#eval check_multiplicativity 4 9   -- 2² and 3² are coprime
#eval check_multiplicativity 8 9   -- 2³ and 3² are coprime
#eval check_multiplicativity 4 25  -- 2² and 5² are coprime

-- Examples with explicit computation
example : Nat.gcd 2 3 = 1 := by native_decide
#eval compute_zeta_gen 6
#eval Nat.lcm (compute_zeta_gen 2) (compute_zeta_gen 3)

example : Nat.gcd 2 5 = 1 := by native_decide
#eval compute_zeta_gen 10
#eval Nat.lcm (compute_zeta_gen 2) (compute_zeta_gen 5)

end ZG1Multiplicativity

/-! ## Property Validation: ZG3 Locality -/

section ZG3Locality

/-
ZG3: Only primes p ≤ n contribute to ζ_gen(n)
Computational check: ζ_gen(n) = ζ_S(n) where S = primes_up_to(n)
-/

def check_locality (n : Nat) : Bool :=
  let primes := primes_up_to n
  compute_zeta_gen n = compute_zeta_S primes n

-- Validate for various n
#eval check_locality 5
#eval check_locality 10
#eval check_locality 15
#eval check_locality 20
#eval check_locality 30
#eval check_locality 50
#eval check_locality 100

-- Explicit demonstrations
#eval compute_zeta_gen 10
#eval primes_up_to 10
#eval compute_zeta_S (primes_up_to 10) 10

#eval compute_zeta_gen 30
#eval primes_up_to 30
#eval compute_zeta_S (primes_up_to 30) 30

end ZG3Locality

/-! ## Property Validation: Prime Behavior -/

section PrimeBehavior

/-
For prime p, ζ_gen(p) should include contributions from all primes ≤ p.
-/

def analyze_prime (p : Nat) : (Nat × List Nat × Nat) :=
  (p, primes_up_to p, compute_zeta_gen p)

#eval analyze_prime 2
#eval analyze_prime 3
#eval analyze_prime 5
#eval analyze_prime 7
#eval analyze_prime 11
#eval analyze_prime 13
#eval analyze_prime 17
#eval analyze_prime 19
#eval analyze_prime 23
#eval analyze_prime 29
#eval analyze_prime 31

end PrimeBehavior

/-! ## Edge Cases and Special Values -/

section EdgeCases

-- Boundary values
#eval compute_zeta_gen 0   -- Should be 1 (unit)
#eval compute_zeta_gen 1   -- Should be 1 (identity)

-- Powers of primes
#eval compute_zeta_gen 2   -- 2¹
#eval compute_zeta_gen 4   -- 2²
#eval compute_zeta_gen 8   -- 2³
#eval compute_zeta_gen 16  -- 2⁴
#eval compute_zeta_gen 32  -- 2⁵

#eval compute_zeta_gen 3   -- 3¹
#eval compute_zeta_gen 9   -- 3²
#eval compute_zeta_gen 27  -- 3³

#eval compute_zeta_gen 5   -- 5¹
#eval compute_zeta_gen 25  -- 5²

end EdgeCases

/-! ## Pattern Analysis -/

section PatternAnalysis

/-
Analyze growth patterns and relationships.
-/

-- Compare ζ_gen(n) vs n for various n
def analyze_growth (n : Nat) : (Nat × Nat × Nat) :=
  let zeta := compute_zeta_gen n
  let ratio := if n = 0 then 0 else zeta / n  -- Integer division
  (n, zeta, ratio)

-- Sample points
#eval List.map analyze_growth [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval List.map analyze_growth [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]

-- Prime counting in results
def count_prime_factors (n : Nat) : Nat :=
  (primes_up_to n).length

#eval List.map (fun n => (n, count_prime_factors n, compute_zeta_gen n))
  [10, 20, 30, 40, 50]

end PatternAnalysis

/-! ## Regression Tests -/

section RegressionTests

/-
Known values for regression testing.
These should remain stable across refactorings.
-/

-- Basic invariants
example : compute_zeta_gen 0 = 1 := by native_decide
example : compute_zeta_gen 1 = 1 := by native_decide

-- Small values (can be verified by hand)
-- Note: Actual expected values depend on the algorithm implementation
-- These examples serve as regression tests

def test_suite : List (Nat × Bool) :=
  [ (1, compute_zeta_gen 1 = 1)
  , (2, compute_zeta_gen 2 = 2)
  , (3, compute_zeta_gen 3 = 3)
  , (4, compute_zeta_gen 4 = 4)
  ]

#eval test_suite

end RegressionTests

/-! ## Summary Statistics -/

section Summary

-- Test coverage
def tested_values : List Nat :=
  List.range 101  -- 0 to 100

def test_all : Bool :=
  tested_values.all (fun n => compute_zeta_gen n > 0)

#eval test_all  -- Should be true

-- Prime count at 100
#eval prime_count 100  -- Should be 25

-- Sample of results
def sample_results : List (Nat × Nat) :=
  [1, 2, 5, 10, 20, 30, 50, 100].map (fun n => (n, compute_zeta_gen n))

#eval sample_results

end Summary

end Examples
end Gen
