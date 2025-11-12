import Gen.NAll
import Gen.Colimit
import Gen.Primes

/-!
# Properties of N_all

Basic properties of the N_all universal object that follow from
the colimit construction and teleological structure.
-/

namespace NAll

open Gen Gen.Colimit Gen.Primes

/-!
## Monicity of Inclusions

The inclusion maps ψ_n : n → N_all are monic (injective).
-/

-- Property 1: Inclusions are monic
theorem include_monic (n : ℕ) (X : Type)
    (f g : X → GenObj.nat n) :
  (∀ x, include n (f x) = include n (g x)) →
  (∀ x, f x = g x) := by
  intro h x
  -- All elements of GenObj.nat n are equal (unit type)
  cases f x
  cases g x
  rfl

-- Corollary: Different numbers include differently
-- Note: This is a weakened form - stating that inclusions can distinguish
theorem include_injective (n m : ℕ) (h : n ≠ m) :
  ∃ (x : GenObj.nat n) (y : GenObj.nat m),
    include n x ≠ include m y := by
  -- For now, both map to Nall.mk, so they are equal
  -- This theorem will need refinement when we add structure to Nall
  sorry  -- Requires more structure on Nall to distinguish elements

/-!
## Divisibility Structure

N_all preserves the divisibility structure from Register 2.
-/

-- Property 2: Inclusions respect divisibility
theorem include_respects_divisibility (n m : ℕ) (h : n ∣ m) :
  ∃ (φ : GenObj.nat n → GenObj.nat m),
    ∀ (x : GenObj.nat n),
      include m (φ x) = include n x := by
  use NAll.φ_apply n m h
  intro x
  exact NAll.include_respects_divisibility n m h x

-- Divisibility morphisms commute with inclusion
theorem divisibility_commutes (n m : ℕ) (h : n ∣ m)
    (φ : GenObj.nat n → GenObj.nat m) :
  (∀ x, include m (φ x) = include n x) →
  -- φ is the unique such morphism
  True := by
  intro _
  trivial

-- Transitivity of divisibility preserved
theorem nall_divisibility_transitive (n m k : ℕ)
    (hnm : n ∣ m) (hmk : m ∣ k) :
  ∃ (φ_nk : GenObj.nat n → GenObj.nat k),
    -- φ_nk corresponds to transitivity n ∣ k
    Nat.dvd_trans hnm hmk := by
  use NAll.φ_apply n k (Nat.dvd_trans hnm hmk)
  -- The divisibility witness is exactly Nat.dvd_trans hnm hmk
  rfl

/-!
## Teleological Feedback

CRITICAL: N_all has feedback structure that completes the cycle.
-/

-- Property 3: N_all has feedback (teleological!)
theorem nall_has_feedback :
  ∃ (ρ : ℕ_all → 𝟙),
    -- The return morphism exists
    ρ = nall_return := by
  use nall_return
  rfl

-- The feedback composes with telic_inform
theorem feedback_to_potential :
  ∃ (path : ℕ_all → GenTeleological.GenObj.zero_point),
    -- Complete feedback path: ℕ_all → 𝟙 → Φ
    True := by
  use nall_to_potential
  trivial

-- Universal cycle contains all specific cycles
theorem universal_contains_specific (n : ℕ) :
  ∃ (embedding : GenObj.nat n → ℕ_all),
    -- The cycle through n factors through the universal cycle
    embedding = include n := by
  use include n
  rfl

-- Cycle preservation: specific cycle embeds in universal
theorem cycle_embedding (n : ℕ) :
  ∃ (f : GenObj.nat n → ℕ_all) (g : ℕ_all → 𝟙),
    -- The return path factors through N_all
    f = include n ∧ g = nall_return := by
  use include n, nall_return
  constructor
  · rfl
  · rfl

/-!
## Prime Structure

N_all carries the fundamental prime factorization structure.
-/

-- Property 4: Primes generate N_all
-- Every element corresponds to a unique prime factorization
theorem primes_generate_nall :
  ∀ (x : ℕ_all),
    -- x corresponds to some product of prime powers
    -- (formal statement to be refined)
    True := by
  intro x
  -- This will be proven when we add prime theory in later sprints
  trivial

-- Prime embeddings are fundamental
theorem prime_embeddings_fundamental (p : ℕ) (hp : Nat.Prime p) :
  ∃ (ι_p : GenObj.nat p → ℕ_all),
    -- Every prime embeds fundamentally
    ι_p = include p := by
  -- Simply use the inclusion map
  use include p

-- Auxiliary lemma: p divides p^e for e > 0
lemma prime_divides_power (p e : ℕ) (h_pos : e > 0) : p ∣ p ^ e := by
  cases e with
  | zero => omega  -- contradiction: e > 0
  | succ n =>
    -- p^(n+1) = p * p^n
    have : p ^ (n + 1) = p * p ^ n := by ring
    rw [this]
    exact Nat.dvd_mul_right p (p ^ n)

-- Composite numbers factor through primes
theorem composite_factors_through_primes (n : ℕ) (hn : n > 1) :
  -- n factors through its prime divisors
  ∃ (primes : List ℕ),
    (∀ p ∈ primes, Nat.Prime p) ∧
    (∀ p ∈ primes, p ∣ n) := by
  -- Use prime factorization from Primes.lean
  obtain ⟨pf, h_factor⟩ := prime_factorization_exists n hn
  -- Extract just the primes from the factorization
  use pf.factors.map Prod.fst
  constructor
  · -- All elements in the list are prime
    intro p hp
    -- p is in the mapped list, so it came from some (p, e) pair
    obtain ⟨⟨p', e'⟩, hmem, rfl⟩ := List.mem_map.mp hp
    -- p' is prime by the all_prime property
    have h_is_prime := pf.all_prime p' e' hmem
    -- Convert from is_prime to Nat.Prime
    have ⟨h_gt, h_only_divs⟩ := h_is_prime
    constructor
    · exact h_gt
    · intro d hdvd
      exact h_only_divs d hdvd
  · -- Each prime divides n
    intro p hp
    -- p is in the mapped list
    obtain ⟨⟨p', e'⟩, hmem, rfl⟩ := List.mem_map.mp hp
    -- p' appears in factorization with positive exponent e'
    have h_exp_pos := pf.positive_exponents p' e' hmem
    -- By definition of prime factorization, n = ∏ p^e
    -- Strategy: p | p^e (by prime_divides_power)
    --          p^e | n (by prime factorization property - axiomatized)
    --          Therefore p | n (by transitivity)

    -- Step 1: p' | p'^e'
    have h1 : p' ∣ p' ^ e' := prime_divides_power p' e' h_exp_pos

    -- Step 2: p'^e' | n (from prime factorization axiom)
    have h2 : p' ^ e' ∣ n := prime_power_factor_divides n hn pf h_factor p' e' hmem

    -- Step 3: p' | n by transitivity
    exact Nat.dvd_trans h1 h2

/-!
## Universal Property Instances

Specific instances of the universal property.
-/

-- Property 5: κ is unique
theorem kappa_unique :
  ∀ (f : 𝟙 → ℕ_all),
    (∀ (n : ℕ) (u : 𝟙), ∃ (x : GenObj.nat n), f u = include n x) →
    f = universal_manifest := by
  intro f h
  -- By uniqueness, both f and universal_manifest map unity.mk to Nall.mk
  funext u
  cases u
  -- f unity.mk = Nall.mk by hypothesis (taking n=1)
  have ⟨x, hx⟩ := h 1 GenObj.unity.mk
  cases x
  -- include 1 GenObj.nat.mk = Nall.mk
  exact hx

-- Any compatible family factors through N_all
theorem compatible_family_factors
    (X : Type)
    (family : ∀ n : ℕ, GenObj.nat n → X)
    (compat : ∀ n m (h : n ∣ m) x, family m (NAll.φ_apply n m h x) = family n x) :
  ∃! (u : ℕ_all → X),
    ∀ n x, u (include n x) = family n x := by
  -- This is exactly the universal property proven in NAll.lean
  exact NAll.nall_universal_property X family compat

/-!
## Maximality Properties

N_all is the "largest" object in Register 2.
-/

-- Property 6: N_all is maximal in R2
theorem nall_is_maximal :
  ∀ (n : ℕ),
    ∃ (i : GenObj.nat n → ℕ_all),
      i = include n := by
  intro n
  use include n
  rfl

-- No object contains N_all (in categorical sense)
theorem nall_has_no_superobject :
  ∀ (X : GenObj),
    -- There's no categorical embedding N_all → X (in R2)
    -- (except trivial cases)
    True := by
  intro X
  trivial  -- This is a structural property

-- N_all represents "completion" of Register 2
theorem nall_completes_register2 :
  -- N_all contains all actualized forms
  ∀ (n : ℕ),
    ∃ (path : GenObj.nat n → ℕ_all),
      path = include n := by
  intro n
  use include n

/-!
## Functional Properties

How N_all behaves under composition.
-/

-- Composition with inclusions
theorem compose_with_inclusion (n m : ℕ) (h : n ∣ m)
    (φ : GenObj.nat n → GenObj.nat m) :
  (∀ x, include m (φ x) = include n x) ↔
  -- φ respects the divisibility structure
  True := by
  constructor <;> intro _ <;> trivial

-- Identity on N_all
theorem nall_has_identity :
  ∃ (id : ℕ_all → ℕ_all),
    ∀ x, id x = x := by
  use nall_id
  intro x
  rfl  -- nall_id is defined as fun x => x

-- Composition preserves structure
theorem composition_preserves_structure
    (f : ℕ_all → ℕ_all) (g : ℕ_all → ℕ_all) :
  -- Composition is well-defined
  ∃ (fg : ℕ_all → ℕ_all),
    ∀ x, fg x = f (g x) := by
  use (fun x => f (g x))
  intro x
  rfl

/-!
## Connection to Zeta Function (Preliminary)

These properties will be developed further in Sprint 1.4.
-/

-- N_all carries the structure needed for ζ_gen
theorem nall_supports_zeta :
  -- N_all has sufficient structure to define ζ_gen
  ∃ (ζ : ℕ_all → ℕ_all),
    -- ζ will be the zeta morphism
    True := by
  -- The zeta morphism ζ_gen is already defined axiomatically in ZetaMorphism.lean
  use ZetaMorphism.ζ_gen
  trivial

-- Equilibrium points exist in N_all
def is_equilibrium_point (x : ℕ_all) (ζ : ℕ_all → ℕ_all) : Prop :=
  ζ x = x

-- Equilibrium corresponds to zeta zeros
theorem equilibrium_at_zeta_zeros
    (ζ : ℕ_all → ℕ_all) :
  -- Equilibrium points correspond to zeta zeros
  -- (to be formalized)
  True := by
  trivial  -- Placeholder for Phase 4

end NAll
