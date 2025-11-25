-- Foundation (must be first)
import Gip.Foundations

-- Core structure
import Gip.Basic
import Gip.CoreTypes
import Gip.Intermediate
import Gip.ZeroObject
import Gip.UniversalFactorization

-- Transformations
import Gip.Origin

-- Cohesion
import Gip.Cohesion
import Gip.Cohesion.Selection

-- Integration
import Gip.HolographicInterface
import Gip.GrandUnifiedProof
import Gip.ProcessIdentity

-- Extended modules (these may have their own issues to address)
import Gip.Factorization
import Gip.ModalTopology
import Gip.Examples
import Gip.ParadoxIsomorphism
import Gip.ComplexityStratification
import Gip.InfinitePotential
import Gip.CognitiveLimits
import Gip.MonadStructure
import Gip.SelfReference
import Gip.BayesianCore
import Gip.Universe.Generation

/-!
# GIP: Properly Grounded Implementation

A Lean 4 library implementing the Genesis-Infinity Point (GIP) theory,
properly grounded in established mathematics via Mathlib.

## The Zero Object Model

- **○** (Origin) is the zero object (initial AND terminal)
- **○/○ = (∅ ≅ ∞)** self-division produces isomorphic dual aspects
- **{N}** emerges as structures that survive
- **n** is the hub (bidirectional flow, not a zero object)

## Core Architecture

### Foundations (Gip/Foundations.lean)
The proper mathematical foundation:
- `Obj`: Four objects (○, ∅, ∞, n)
- `Hom`: Morphisms with explicit composition
- `MetricSpace`-based cohesion

### Object Structure
- **○** (origin): Zero object - both source and sink
- **∅** (aspect_empty): Empty aspect
- **∞** (aspect_infinite): Infinite aspect (∅ ≅ ∞)
- **n** (identity): Realized structure (hub)

### Morphism Structure
- **from_origin**: ○ → A (initial property)
- **to_origin**: A → ○ (terminal property)
- **empty_to_inf/inf_to_empty**: ∅ ≅ ∞ isomorphism
- **gen**: ∅ → n (generation)
- **res**: ∞ → n (resolution)
- **act_empty/act_inf**: n → ∅/∞ (action)

### Key Properties (All PROVEN)
- ○ is zero object (initial AND terminal)
- ∅ ≅ ∞ (isomorphic aspects)
- n is hub (bidirectional flow)
- Cohesion ∈ (0, 1] (from MetricSpace)

## The Circle Closes

```
○/○ = (∅ ≅ ∞) : {N}

        ○ (zero object)
        ↓ bifurcation
     (∅ ≅ ∞)
      ↓   ↓
   Gen   Res
      ↘ ↙
       n (hub)
      ↙ ↘
   Act   Act
      ↓   ↓
     (∅ ≅ ∞)
        ↓
        ○
```

⭕ = ○
-/
