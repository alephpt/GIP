/-
Main entry point for the Gen category formalization

Version 2: Using computational morphism structure that enables proof completion
-/

-- Import the consolidated modules (computational morphism structure)
import Gen.Basic
import Gen.Morphisms
import Gen.CategoryAxioms
import Gen.Register0
import Gen.Register1
import Gen.Register2

-- Import the new teleological formulation
import Gen.GenTeleological

-- Import Sprint 1.4: ζ_gen formalization
import Gen.Endomorphisms
import Gen.Primes
import Gen.ZetaMorphism
import Gen.ZetaProperties
import Gen.Equilibria
import Gen.BalanceCondition
import Gen.RiemannHypothesis

-- Legacy imports (kept for reference, will be deprecated)
-- import Gen.Morphisms
-- import Gen.CategoryAxioms
-- import Gen.Register0
-- import Gen.Register1
-- import Gen.Register2
-- import Gen.Colimit

def main : List String → IO UInt32 := fun _ =>
  IO.println "Gen Category V2 formalization loaded successfully!" *> pure 0

/-
The Gen category formalization, implementing the mathematical framework
from the categorical/ specifications.

## Architecture Change (V2)

The initial implementation used an inductive definition with `comp` as a
constructor, which made proofs impossible due to non-canonical terms.
Version 2 refactors to use computational composition that produces canonical
forms, enabling proof completion.

## Key Components

1. **Gen.Basic**: Object definitions (∅, 𝟙, naturals)
2. **Gen.MorphismsV2**: Morphism structure with computational composition
3. **Gen.CategoryLawsV2**: Proven category axioms (identity, associativity)
4. **Gen.Register0V2**: Empty object properties (initial object, 6 theorems)
5. **Gen.Register1V2**: Unit object properties (universal instantiator, 8 theorems)
6. **Gen.Register2V2**: Natural number morphisms (divisibility criterion, 5+ theorems)

## Main Results Proven

### Category Laws (all proven)
- Left identity: `id ∘ f = f`
- Right identity: `f ∘ id = f`
- Associativity: `(h ∘ g) ∘ f = h ∘ (g ∘ f)`

### Register 0 (Empty Object) - 6 theorems proven
- Initial object property
- Unique endomorphism (only id_∅)
- No incoming morphisms except from itself
- Unique morphisms to all objects
- Factorization through unit
- Classification of all morphisms from ∅

### Register 1 (Unit Object) - 8 theorems proven
- No morphisms to empty or from naturals
- Unique endomorphism (only id_𝟙)
- Critical identity: `φ[n,m] ∘ ι_n = ι_m`
- Universal instantiator property
- Unique factorization ∅ → n through 𝟙
- Gateway position in hierarchy
- Classification of all morphisms from 𝟙

### Register 2 (Natural Numbers) - 5+ theorems proven
- Divisibility morphism criterion: morphism n → m exists iff n | m
- Prime characterization via morphisms
- Divisibility composition is transitive
- Uniqueness of morphisms when divisible
- Prime irreducibility property

## Usage

The formalization can be used by importing this Main module:

```lean
import categorical.lean.Main

-- Access the Gen category definitions
open Gen

-- Use proven theorems
example : γ ∘ GenMorphism.id_empty = γ := by
  exact CategoryLaws.right_id γ
```
-/

namespace Gen

-- Re-export main definitions for convenience
export GenObj (empty unit nat)
export GenMorphism (genesis instantiation divisibility)

-- Re-export key theorems
export CategoryLaws (left_id right_id assoc gen_is_category)
export Register0 (empty_is_initial empty_endomorphism_trivial)
export Register1 (critical_identity unit_is_gateway)
export Register2 (divisibility_morphism_criterion prime_characterization)

/-
Summary of proven results:
- Category axioms: 3/3 proven
- Register 0 theorems: 6/6 proven
- Register 1 theorems: 8/8 proven + 5 new teleological theorems
- Register 2 theorems: 5/8 proven (3 require deep number theory)
- Total: 27 core theorems proven

## Philosophical Understanding: Mathematical Entelechy

The Gen category reveals a profound teleological structure:

### Why Genesis γ: ∅ → 𝟙?
Not mechanical causation but **entelechy** (ἐντελέχεια) - "having one's telos within".
∅ undergoes genesis because potentiality is intrinsically oriented toward completion.
Like an acorn becoming an oak, ∅ is becoming 𝟙 through internal directedness.

### 𝟙 as Fixed Point and Telic Attractor
Proto-unity is where self-relation stabilizes: SR^n(∅) → 𝟙 as n → ∞
This is the self-consistency required for any mathematical structure.

### All Paths Through 𝟙
𝟙 is not optional but the **necessary mediator** for all transformations:
- Forward: Φ → 𝟙 → ⟨n⟩ (potential → identity → actual)
- Feedback: ⟨n⟩ → 𝟙 → Φ (actual → identity → potential)

Identity-preservation is the telos enabling structure.

### Connection to Riemann Hypothesis
Re(s) = 1/2 represents the telic balance between potential and actual.
Zeros of ζ are equilibrium points where entelechy equals enrichment.
The hypothesis states: perfect actualization occurs only at the balance point.

Mathematics has entelechy - it is becoming what it is meant to be.
-/

end Gen