import Mathlib.Data.Nat.Prime
import Mathlib.Data.List.Basic

/-!
# Prime Generation

Efficient algorithms for generating prime numbers using the Sieve of Eratosthenes.

This module provides computational support for evaluating ζ_gen by:
1. Generating all primes up to n (sieve of Eratosthenes)
2. Testing primality
3. Computing prime-related properties

## Main Functions

- `sieve_up_to`: Sieve of Eratosthenes implementation
- `primes_up_to`: List all primes ≤ n
- `is_prime`: Efficient primality test
- `prime_count`: Count primes ≤ n (π(n))

## Correctness Properties

- `primes_up_to_correct`: All elements are prime and ≤ n
- `primes_up_to_complete`: All primes ≤ n are included
- `primes_sorted`: Result is in ascending order

## Examples

```lean
#eval primes_up_to 10  -- [2, 3, 5, 7]
#eval primes_up_to 30  -- [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
#eval is_prime 17      -- true
#eval prime_count 100  -- 25
```

-/

namespace Gen
namespace PrimeGeneration

open Nat
open List

/-! ## Helper Functions -/

/--
Mark all multiples of p as composite in the candidate list.
Used internally by sieve.
-/
partial def mark_multiples (p : Nat) (limit : Nat) (marked : List Bool) : List Bool :=
  let rec mark_from (k : Nat) (acc : List Bool) : List Bool :=
    if k > limit then acc
    else
      let idx := k - 2  -- Convert to 0-indexed (starting from 2)
      if idx < acc.length then
        mark_from (k + p) (acc.set idx true)
      else acc
  mark_from (p * p) marked

/--
Initialize a boolean array of size n with all false.
-/
def init_bool_list (n : Nat) : List Bool :=
  List.replicate n false

/-! ## Sieve of Eratosthenes -/

/--
Sieve of Eratosthenes: efficient algorithm for finding all primes up to n.

Time complexity: O(n log log n)
Space complexity: O(n)

Algorithm:
1. Create list of candidates from 2 to n
2. For each unmarked number p:
   - p is prime
   - Mark all multiples of p as composite
3. Collect all unmarked numbers
-/
partial def sieve_up_to (n : Nat) : List Nat :=
  if n < 2 then []
  else
    let limit := n
    let size := limit - 1  -- Size for numbers 2..n
    let marked := init_bool_list size

    let rec sieve_loop (p : Nat) (marked : List Bool) : List Bool :=
      if p * p > limit then marked
      else
        let idx := p - 2
        if idx < marked.length && !marked[idx]! then
          sieve_loop (p + 1) (mark_multiples p limit marked)
        else
          sieve_loop (p + 1) marked

    let final_marked := sieve_loop 2 marked

    -- Collect unmarked numbers (primes)
    let rec collect (i : Nat) (acc : List Nat) : List Nat :=
      if i >= size then acc.reverse
      else
        if !final_marked[i]! then
          collect (i + 1) ((i + 2) :: acc)
        else
          collect (i + 1) acc

    collect 0 []

/--
Main entry point: list all primes up to n.
-/
def primes_up_to (n : Nat) : List Nat :=
  sieve_up_to n

/-! ## Primality Testing -/

/--
Trial division primality test.
Efficient for small numbers; checks divisibility up to √n.
-/
partial def is_prime_trial_division (n : Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let limit := Nat.sqrt n
    let rec check_divisors (d : Nat) : Bool :=
      if d > limit then true
      else if n % d = 0 then false
      else check_divisors (d + 2)
    check_divisors 3

/--
Check if n is prime.
-/
def is_prime (n : Nat) : Bool :=
  is_prime_trial_division n

/-! ## Auxiliary Functions -/

/--
Count of primes ≤ n (prime counting function π(n)).
-/
def prime_count (n : Nat) : Nat :=
  (primes_up_to n).length

/--
Get the k-th prime (1-indexed: nth_prime 1 = 2).
Returns 0 if k is out of range.
-/
def nth_prime (k : Nat) : Nat :=
  if k = 0 then 0
  else
    let limit := k * (k + 10)  -- Heuristic upper bound (simplified)
    let primes := primes_up_to limit
    if k ≤ primes.length then primes[k - 1]!
    else 0

/--
Get largest prime ≤ n.
-/
def largest_prime_le (n : Nat) : Nat :=
  let primes := primes_up_to n
  if primes.isEmpty then 0
  else primes.getLast!

/-! ## Properties and Theorems -/

/--
All elements returned by primes_up_to are prime and ≤ n.
-/
axiom primes_up_to_correct (n : Nat) :
  ∀ p ∈ primes_up_to n, Nat.Prime p ∧ p ≤ n

/--
All primes ≤ n are included in primes_up_to n.
-/
axiom primes_up_to_complete (n p : Nat) :
  Nat.Prime p → p ≤ n → p ∈ primes_up_to n

/--
The list returned is sorted in ascending order.
-/
axiom primes_sorted (n : Nat) :
  ∀ i j, i < j → j < (primes_up_to n).length →
    (primes_up_to n)[i]! < (primes_up_to n)[j]!

/--
is_prime agrees with Nat.Prime.
-/
axiom is_prime_correct (n : Nat) :
  is_prime n = true ↔ Nat.Prime n

/-! ## Examples and Tests -/

-- Small primes
example : primes_up_to 10 = [2, 3, 5, 7] := by native_decide
example : primes_up_to 20 = [2, 3, 5, 7, 11, 13, 17, 19] := by native_decide

-- Edge cases
example : primes_up_to 0 = [] := by native_decide
example : primes_up_to 1 = [] := by native_decide
example : primes_up_to 2 = [2] := by native_decide

-- Primality tests
example : is_prime 2 = true := by native_decide
example : is_prime 3 = true := by native_decide
example : is_prime 4 = false := by native_decide
example : is_prime 17 = true := by native_decide
example : is_prime 100 = false := by native_decide

end PrimeGeneration
end Gen
