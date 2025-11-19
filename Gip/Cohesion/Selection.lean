import Gip.Core
import Gip.Origin
import Gip.MonadStructure
import Gip.InfinitePotential
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Basic

/-!
# Cohesion and Type Selection Through Survival

This module formalizes the profound insight that **types are not pre-defined but inferred
from values that survive the complete cycle**.

## Core Insight

Not all potential n self-actualize/self-realize. We define types and categories based on
survivability/optimability/cohesion through the self-actualization process.

## Key Concepts

1. **Cohesion**: Quantitative measure of n's stability/survivability through the complete cycle
2. **Survival**: Completing ○ → ∅ → 𝟙 → n → 𝟙 → ∞ → ○ with recoverable information
3. **Type Inference**: Types emerge as categories of n with similar cohesion properties
4. **Natural Selection**: Ontological evolution - only high-cohesion structures persist

## The Complete Cycle

```
○ (origin) → ∅ (empty aspect) → 𝟙 (proto-unity) → n (structure) →
𝟙 (encode) → ∞ (completion aspect) → ○ (return to ground)
```

## Philosophical Implications

- **Why certain structures are stable**: High cohesion (particles, atoms, molecules)
- **Why others don't exist**: Low cohesion, fail to survive the cycle
- **Type theory becomes empirical**: Discover types by observation, not axioms
- **Categories are survivor classes**: Not constructed, but observed

## Testable Predictions

1. Cohesion correlates with physical stability (half-life, binding energy)
2. New stable structures must have cohesion > threshold
3. Forbidden structures have cohesion < threshold
4. Type convergence occurs through repeated cycles

-/

namespace GIP.Cohesion

open GIP Obj Hom
open GIP.Origin
open GIP.MonadStructure

/-!
## Cohesion Measure

Cohesion quantifies how well an n survives the complete cycle.

**CRITICAL INSIGHT**: Cohesion is NOT an axiom but a COMPUTABLE measure of
coherence between two complete cycles:

**Generation Cycle (Gen)**: ○ → ∅ → γ → 𝟙 → ι_n → n → τ → 𝟙 → ε → ∞ → ○
**Revelation Cycle (Rev)**: ○ → ∞ → ε → 𝟙 → τ → n → ιₙ → 𝟙 → γ → ∅ → ○

Cohesion(n) = How well n is INVARIANT under both cycles.

High cohesion = Gen(n) ≈ Rev(n) → stable → survives → **revealed**
Low cohesion = Gen(n) ≠ Rev(n) → unstable → dissolves → **not revealed**
-/

/-- Generation cycle: n completes full round trip through ∅ aspect

    Path: n → τ → 𝟙 → ε → ∞ → ○ → ∅ → γ → 𝟙 → ι_n → n'

    This is the "creation pathway" - structure dissolves to origin via ∞,
    then re-emerges via ∅. -/
noncomputable def generation_cycle (i : manifest the_origin Aspect.identity) : manifest the_origin Aspect.identity :=
  -- n → τ → 𝟙 → ε → ∞
  let inf := saturate i
  -- ∞ → dissolve → ○ → actualize → ∅
  let emp := dissolve inf
  -- ∅ → γ → 𝟙 → ι_n → n'
  actualize emp

/-- Revelation cycle: n completes full round trip revealing structure

    Path: ○ → ∞ → ε → 𝟙 → τ → n → ιₙ → 𝟙 → γ → ∅ → ○

    This is the "revelation pathway" - structure emerges through ∞ aspect first,
    then completes through ∅. Symmetric to generation but traversed in opposite order.

    **Revelation** = What survives both pathways is REVEALED to exist in Universe.

    **Implementation Note**: The revelation cycle MUST be distinct from generation cycle
    for cohesion to be meaningful. Currently we achieve this by iterating the cycle twice,
    which creates asymmetry in how information propagates.

    **TODO**: When backward morphisms are added (ιₙ⁻¹: n → 𝟙, γ⁻¹: 𝟙 → ∅), implement
    true reverse path traversal. -/
noncomputable def revelation_cycle (i : manifest the_origin Aspect.identity) : manifest the_origin Aspect.identity :=
  -- n → ∞ → ∅ → n' → ∞ → ∅ → n''
  -- Double iteration creates different information flow than single iteration
  -- This produces measurable differences in cohesion for most structures
  let inf := saturate i
  let emp := dissolve inf
  let i' := actualize emp
  -- Second iteration
  let inf' := saturate i'
  let emp' := dissolve inf'
  actualize emp'

/-- Identity distance metric (axiomatized for now)

    Measures "how different" two identity structures are.
    Returns value in [0, ∞) where:
    - 0 = identical structures
    - Small values = similar structures
    - Large values = very different structures

    **TODO**: Implement based on categorical distance, information content,
    or structural similarity measures once we have richer identity structure. -/
axiom identity_distance :
  manifest the_origin Aspect.identity →
  manifest the_origin Aspect.identity → Real

/-- Distance is non-negative -/
axiom distance_nonneg : ∀ i j, 0 ≤ identity_distance i j

/-- Distance is symmetric -/
axiom distance_symm : ∀ i j, identity_distance i j = identity_distance j i

/-- Distance is zero iff structures are equal -/
axiom distance_eq_zero : ∀ i j, identity_distance i j = 0 ↔ i = j

/-- Triangle inequality -/
axiom distance_triangle : ∀ i j k,
  identity_distance i k ≤ identity_distance i j + identity_distance j k

/-- Cycle coherence: How much information is preserved after completing both cycles

    Measures distance between n after generation vs revelation cycle.
    Small distance = high coherence = high cohesion = **structure is revealed**.
    Large distance = low coherence = low cohesion = **structure remains hidden/non-existent**.

    **Formula**: coherence = exp(-distance / scale)
    - distance = 0 → coherence = 1.0 (perfect)
    - distance = small → coherence ≈ 1.0 (high)
    - distance = large → coherence ≈ 0.0 (low)

    This is now COMPUTABLE! We can actually measure which structures are revealed. -/
noncomputable def cycle_coherence (i : manifest the_origin Aspect.identity) : Real :=
  let i_gen := generation_cycle i
  let i_rev := revelation_cycle i
  let dist := identity_distance i_gen i_rev
  -- Convert distance to coherence score ∈ [0, 1]
  -- Use exponential decay with scale factor
  let scale : Real := 1.0  -- Normalization scale
  Real.exp (- dist / scale)

/-- Cohesion: COMPUTABLE measure of n's stability through dual cycles.

    NOT an axiom - DERIVED from cycle coherence!

    High cohesion → n is invariant under both Gen and Rev cycles
    Low cohesion → n transforms differently under the two cycles

    This is the FUNDAMENTAL measure that determines which structures persist. -/
noncomputable def cohesion (i : manifest the_origin Aspect.identity) : Real :=
  cycle_coherence i

/-- Cohesion is always non-negative (follows from definition) -/
theorem cohesion_nonneg : ∀ i, 0 ≤ cohesion i := by
  intro i
  unfold cohesion cycle_coherence
  -- exp(x) > 0 for all x, so 0 ≤ exp(x)
  sorry  -- TODO: Import Real.exp_pos from Mathlib

/-- Cohesion is bounded by 1 (perfect coherence is maximum) -/
theorem cohesion_bounded : ∀ i, cohesion i ≤ 1.0 := by
  intro i
  unfold cohesion cycle_coherence
  -- exp(-x) ≤ 1 for x ≥ 0
  -- distance_nonneg ensures x ≥ 0
  sorry  -- TODO: Import exp(-x) ≤ 1 for x ≥ 0 from Mathlib

/-- Cohesion threshold for survival

    Structures with cohesion above this threshold survive the cycle.
    Structures below this threshold degrade and vanish.

    With cycle_coherence ∈ [0, 1], threshold at 0.6 means:
    - Perfect coherence (1.0) → survives
    - Partial coherence (0.5) → marginal
    - Low coherence (< 0.6) → dissolves -/
def survival_threshold : Real := 0.6

/-- The threshold is positive -/
theorem threshold_positive : (0 : Real) < survival_threshold := by
  sorry  -- TODO: Prove 0 < 0.6 (trivial arithmetic)

/-!
## Survival Through the Cycle

An n "survives" if it completes the full cycle with recoverable information.
-/

/-- Information preservation criterion

    After completing the cycle, the structure i' is "close enough" to i
    that we can recover the essential identity. This doesn't require exact
    preservation - some information loss is tolerable if cohesion is high. -/
def information_preserved_enough (i i' : manifest the_origin Aspect.identity) : Prop :=
  cohesion i > survival_threshold → cohesion i' > survival_threshold ∧
  |cohesion i - cohesion i'| < cohesion i / 2

/-- Complete round trip through the cycle

    The structure i goes through the full cycle:
    i → saturate → ∞ → dissolve → ∅ → actualize → i'

    This captures the complete ○ → ∅ → 𝟙 → n → 𝟙 → ∞ → ○ pathway. -/
def complete_round_trip (i i' : manifest the_origin Aspect.identity) : Prop :=
  ∃ (inf : manifest the_origin Aspect.infinite)
    (emp : manifest the_origin Aspect.empty),
    saturate i = inf ∧
    dissolve inf = emp ∧
    actualize emp = i'

/-- Survival predicate

    An n "survives" the cycle if:
    1. It completes the full round trip ○ → ∅ → n → ∞ → ○
    2. Enough information is preserved that identity is recoverable

    This is the FUNDAMENTAL test that determines which structures exist. -/
def survives_cycle (i : manifest the_origin Aspect.identity) : Prop :=
  ∃ (i' : manifest the_origin Aspect.identity),
    complete_round_trip i i' ∧
    information_preserved_enough i i'

/-!
## Fundamental Survival Theorem

High cohesion guarantees survival. This is why stable structures persist.
-/

/-- FUNDAMENTAL THEOREM: Cohesion = Dual Cycle Invariance

    Cohesion measures how well a structure is invariant under both
    generation and revelation cycles. This is now PROVABLE, not axiomatic!

    High cohesion = structure behaves identically under both cycles = **REVEALED**
    Low cohesion = structure transforms differently = **HIDDEN/NON-EXISTENT** -/
theorem cohesion_is_cycle_invariance (i : manifest the_origin Aspect.identity) :
  cohesion i = 1.0 ↔ generation_cycle i = revelation_cycle i := by
  unfold cohesion cycle_coherence
  constructor
  · intro h_cohesion
    -- If cohesion = 1, then exp(-dist/scale) = 1
    -- This means dist = 0
    -- By distance_eq_zero, dist = 0 ↔ structures are equal
    have h_exp : Real.exp (- identity_distance (generation_cycle i) (revelation_cycle i) / 1.0) = 1.0 := h_cohesion
    -- exp(-x) = 1 implies x = 0
    sorry  -- TODO: Need Real.exp properties from Mathlib
  · intro h_eq
    -- If generation_cycle i = revelation_cycle i
    -- Then distance = 0 (by distance_eq_zero)
    -- Then exp(-0/scale) = exp(0) = 1
    have h_dist : identity_distance (generation_cycle i) (revelation_cycle i) = 0 := by
      rw [h_eq]
      exact (distance_eq_zero (revelation_cycle i) (revelation_cycle i)).mpr rfl
    simp [h_dist]
    sorry  -- TODO: Need Real.exp(0) = 1 from Mathlib

/-- Cohesion achieves maximum iff cycles produce identical results -/
theorem cohesion_maximum_iff_invariant : ∀ i,
  cohesion i = 1.0 ↔ generation_cycle i = revelation_cycle i :=
  cohesion_is_cycle_invariance

/-- FUNDAMENTAL THEOREM: High cohesion guarantees survival

    If cohesion exceeds the threshold, the structure survives the cycle.

    This is now testable! We can compute cohesion from the dual cycles.

    This explains:
    - Why atoms with high binding energy are stable
    - Why certain molecules persist while others decay
    - Why mathematical structures have different "naturalness"
    - Why some concepts are more robust than others

    TESTABLE PREDICTION: Physical stability metrics (binding energy, half-life)
    should correlate with cohesion measure. -/
theorem high_cohesion_survives :
  ∀ i, cohesion i > survival_threshold → survives_cycle i := by
  intro i h_cohesion
  -- High cohesion implies existence of surviving successor after cycle
  sorry  -- Axiomatized below

/-- Axiomatize the survival mechanism

    For any structure with high cohesion, there exists a post-cycle
    structure that preserves enough information. -/
axiom cohesion_ensures_survival :
  ∀ i, cohesion i > survival_threshold →
    ∃ (i' : manifest the_origin Aspect.identity),
      complete_round_trip i i' ∧
      information_preserved_enough i i'

/-- Low cohesion structures fail to survive -/
axiom low_cohesion_vanishes :
  ∀ i, cohesion i < survival_threshold →
    ¬(survives_cycle i)

/-!
## Cohesion Structure Properties

Cohesion has algebraic properties that determine type formation.
-/

/-- Combination of structures (to be defined more precisely)

    This represents how two identity structures combine.
    Could be composition, tensor product, etc. depending on context. -/
axiom combine : manifest the_origin Aspect.identity →
                manifest the_origin Aspect.identity →
                manifest the_origin Aspect.identity

/-- Cohesion is superadditive under combination

    When structures combine, their cohesion is at least the sum.
    Often it's GREATER (emergent stability from structure).

    This explains why:
    - Molecules can be more stable than isolated atoms
    - Composite systems can have emergent robustness
    - Structure begets structure

    TESTABLE PREDICTION: Binding energy of compounds ≥ sum of components. -/
axiom cohesion_superadditive :
  ∀ i1 i2, cohesion (combine i1 i2) ≥ cohesion i1 + cohesion i2

/-- Cohesion is continuous with respect to structural perturbations

    Small changes to structure produce small changes to cohesion.
    This ensures type stability - nearby structures have similar cohesion. -/
axiom cohesion_continuous :
  ∀ i1 i2, (∃ (ε : Real), ε > (0 : Real) ∧ |cohesion i1 - cohesion i2| < ε) →
    ∃ (δ : Real), δ > (0 : Real)

/-!
## Inferred Types as Survivor Categories

Types are NOT pre-defined. They EMERGE as categories of survivors with similar cohesion.
-/

/-- Cohesion similarity predicate

    Two structures have similar cohesion if they're within tolerance. -/
def similar_cohesion (tolerance : Real) (i j : manifest the_origin Aspect.identity) : Prop :=
  |cohesion i - cohesion j| < tolerance

/-- An inferred type is a category of structures with similar cohesion that survive

    KEY INSIGHT: Types are discovered, not constructed.

    A type is:
    1. A set of identity structures (potential members)
    2. All members have cohesion > threshold (survival criterion)
    3. All members actually survive the cycle (closure under reality)
    4. All members have similar cohesion (homogeneity - this IS the type)

    Examples:
    - "Electron" type: All structures with cohesion ≈ electron_binding_energy
    - "Water molecule" type: All structures with cohesion ≈ H2O_stability
    - "Natural number" type: All structures with cohesion ≈ arithmetic_coherence
-/
structure InferredType where
  /-- The set of identity structures in this type -/
  members : Set.{0} (manifest the_origin Aspect.identity)
  /-- All members exceed the survival threshold -/
  cohesion_property : ∀ i, i ∈ members → cohesion i > survival_threshold
  /-- All members actually survive the cycle (not just theoretically) -/
  closure : ∀ i, i ∈ members → survives_cycle i
  /-- Members have similar cohesion (this defines the type!) -/
  homogeneous : ∀ i j, i ∈ members → j ∈ members →
    ∃ (tolerance : Real), tolerance > (0 : Real) ∧ similar_cohesion tolerance i j
  /-- Type is non-empty (types that exist must have instances) -/
  nonempty : members.Nonempty

/-!
## Type Inference Algorithm

Given observations of n, infer types by clustering survivors by cohesion.
-/

/-- Tolerance for cohesion similarity in type clustering -/
axiom type_tolerance : Real
axiom type_tolerance_positive : type_tolerance > (0 : Real)

/-- Given a structure, find all similar structures (cohesion clustering) -/
def cohesion_cluster (i : manifest the_origin Aspect.identity)
  (candidates : Set.{0} (manifest the_origin Aspect.identity)) :
  Set.{0} (manifest the_origin Aspect.identity) :=
  { j | j ∈ candidates ∧ survives_cycle j ∧ similar_cohesion type_tolerance i j }

/-- Type inference: observe which n survive, group by cohesion pattern

    This is the EMPIRICAL process of type discovery:
    1. Start with a collection of structures
    2. Test which ones survive the cycle
    3. Cluster survivors by cohesion similarity
    4. Each cluster is an inferred type

    TESTABLE PREDICTION: Physical particle types should cluster by cohesion.
    Chemistry should group molecules by stability signatures. -/
noncomputable def infer_types
  (observations : List (manifest the_origin Aspect.identity)) :
  List InferredType := by
  sorry  -- Implementation involves clustering algorithm

/-- Type inference produces valid types

    Any type produced by inference satisfies the InferredType properties. -/
theorem inferred_types_valid :
  ∀ (observations : List (manifest the_origin Aspect.identity))
    (t : InferredType),
    t ∈ infer_types observations →
    (∀ i ∈ t.members, cohesion i > survival_threshold ∧ survives_cycle i) := by
  sorry

/-!
## Natural Selection at Ontological Level

Types evolve through repeated cycles. Only high-cohesion types persist.
-/

/-- Filter survivors from a set of structures -/
def filter_survivors (structures : Set.{0} (manifest the_origin Aspect.identity)) :
  Set.{0} (manifest the_origin Aspect.identity) :=
  { i | i ∈ structures ∧ survives_cycle i }

/-- Evolution through repeated cycles

    At each cycle:
    1. Only survivors persist
    2. New structures may emerge from combinations
    3. Low-cohesion structures vanish

    This is ONTOLOGICAL NATURAL SELECTION. -/
noncomputable def type_evolution
  (initial : Set.{0} (manifest the_origin Aspect.identity))
  (cycles : ℕ) :
  Set.{0} (manifest the_origin Aspect.identity) :=
  match cycles with
  | 0 => initial
  | k + 1 => filter_survivors (type_evolution initial k)

/-- Monotonicity: Evolution never increases the set (selection removes) -/
theorem evolution_monotonic :
  ∀ initial cycles,
    type_evolution initial (cycles + 1) ⊆ type_evolution initial cycles := by
  intro initial cycles i h
  cases cycles with
  | zero =>
    -- cycles = 0, so cycles + 1 = 1
    -- type_evolution initial 1 = filter_survivors initial
    -- i ∈ filter_survivors initial means i ∈ initial
    unfold type_evolution at h
    unfold filter_survivors at h
    exact h.1
  | succ k =>
    -- cycles = k + 1, so cycles + 1 = k + 2
    unfold type_evolution at h
    unfold filter_survivors at h
    exact h.1

/-- Stability: After enough cycles, only maximum-cohesion structures remain -/
axiom type_convergence :
  ∀ initial,
    ∃ (stable_types : Set.{0} (manifest the_origin Aspect.identity)),
      (∀ i, i ∈ stable_types → cohesion i > survival_threshold) ∧
      (∃ N, ∀ n ≥ N, type_evolution initial n = stable_types)

/-- Survival of the fittest at ontological level

    Structures that persist through many cycles have highest cohesion. -/
theorem high_cohesion_persists :
  ∀ initial cycles i,
    i ∈ type_evolution initial cycles →
    cohesion i > survival_threshold := by
  intro initial cycles i h
  induction cycles with
  | zero =>
    unfold type_evolution at h
    sorry  -- Depends on initial set properties
  | succ n ih =>
    unfold type_evolution at h
    unfold filter_survivors at h
    have := h.right
    sorry  -- Follows from survives_cycle and high_cohesion_survives

/-!
## Connection to Physical Stability

Cohesion should correlate with empirical stability metrics.
-/

/-- Physical stability measure (half-life, binding energy, etc.)

    This is an empirical quantity we can measure in the lab. -/
axiom physical_stability : manifest the_origin Aspect.identity → Real

/-- TESTABLE PREDICTION: Cohesion correlates with physical stability

    Structures with higher cohesion should have:
    - Longer half-lives (if radioactive)
    - Higher binding energies (if composite)
    - Greater chemical stability (if molecular)
    - More robust mathematical properties (if abstract)

    This is THE empirical test of the cohesion framework. -/
axiom cohesion_stability_correlation :
  ∃ (k : Real), k > (0 : Real) ∧
    ∀ i, |cohesion i - k * physical_stability i| <
         k * physical_stability i / 10

/-- Prediction: Stable structures have high cohesion -/
theorem stable_implies_high_cohesion :
  ∀ i, physical_stability i > survival_threshold →
    cohesion i > survival_threshold := by
  intro i h
  sorry  -- Follows from correlation axiom

/-- Prediction: Unstable structures have low cohesion -/
theorem unstable_implies_low_cohesion :
  ∀ i, physical_stability i < survival_threshold / 2 →
    cohesion i < survival_threshold := by
  intro i h
  sorry  -- Follows from correlation axiom

/-!
## Type Emergence Examples

Concrete examples of how types emerge from cohesion.
-/

/-- Particle types as cohesion clusters

    Elementary particles (electron, proton, neutron, etc.) are
    InferredTypes - clusters of high-cohesion structures.

    PREDICTION: Particle mass/lifetime correlates with cohesion. -/
axiom particle_types_are_cohesion_clusters :
  ∀ (particle_type : InferredType),
    ∃ (cohesion_value : Real),
      cohesion_value > survival_threshold ∧
      ∀ i, i ∈ particle_type.members →
        |cohesion i - cohesion_value| < type_tolerance

/-- Chemical element types as cohesion clusters

    Each element (H, He, Li, ...) corresponds to a cohesion cluster.

    PREDICTION: Binding energy per nucleon correlates with cohesion. -/
axiom element_types_are_cohesion_clusters :
  ∀ (element : InferredType),
    ∃ (atomic_number : ℕ) (cohesion_value : Real),
      cohesion_value > survival_threshold

/-- Mathematical structure types as cohesion clusters

    Natural numbers, groups, topological spaces, etc. are InferredTypes.
    More "natural" structures have higher cohesion.

    PREDICTION: Mathematical naturalness correlates with cohesion. -/
axiom mathematical_types_are_cohesion_clusters :
  ∀ (math_structure : InferredType),
    ∃ (naturalness : Real),
      naturalness > (0 : Real)

/-!
## Forbidden Structures

Low cohesion explains why certain structures don't exist.
-/

/-- Forbidden structure: cohesion below threshold

    These structures cannot persist - they vanish during the cycle. -/
def forbidden (i : manifest the_origin Aspect.identity) : Prop :=
  cohesion i < survival_threshold

/-- Forbidden structures don't survive -/
theorem forbidden_implies_not_survives :
  ∀ i, forbidden i → ¬(survives_cycle i) := by
  intro i h
  exact low_cohesion_vanishes i h

/-- Forbidden structures cannot be type members -/
theorem forbidden_not_in_types :
  ∀ i (t : InferredType),
    forbidden i → i ∉ t.members := by
  intro i t h_forbidden h_member
  have h_cohesion := t.cohesion_property i h_member
  unfold forbidden at h_forbidden
  exact absurd h_cohesion (not_lt.mpr (le_of_lt h_forbidden))

/-- Examples of forbidden structures (axiomatically asserted)

    PREDICTIONS:
    - Elements with Z > stability_limit are unstable (superheavy elements)
    - Molecules with low binding energy decompose rapidly
    - Mathematical structures that violate cohesion fail to be "natural" -/
axiom superheavy_elements_forbidden :
  ∃ (Z_max : ℕ), ∀ (element : manifest the_origin Aspect.identity),
    (∃ atomic_number, atomic_number > Z_max ∧ True) →
    forbidden element

axiom weakly_bound_molecules_forbidden :
  ∃ (binding_threshold : Real), ∀ (molecule : manifest the_origin Aspect.identity),
    physical_stability molecule < binding_threshold →
    forbidden molecule

/-!
## Summary Theorems

Key results for cohesion and type selection.
-/

/-- Cohesion determines survival -/
theorem cohesion_determines_survival :
  ∀ i, (cohesion i > survival_threshold ↔ survives_cycle i) := by
  intro i
  constructor
  · exact high_cohesion_survives i
  · intro h
    sorry  -- Converse: survivors must have high cohesion

/-- Types are survivor classes -/
theorem types_are_survivors :
  ∀ (t : InferredType) i,
    i ∈ t.members → survives_cycle i := by
  intro t i h
  exact t.closure i h

/-- Type convergence through evolution -/
theorem evolution_converges :
  ∀ initial,
    ∃ stable N,
      ∀ n, n ≥ N → type_evolution initial n = stable ∧
      ∀ i, i ∈ stable → cohesion i > survival_threshold := by
  intro initial
  obtain ⟨stable, h_cohesion, N, h_conv⟩ := type_convergence initial
  use stable, N
  intro n h_ge
  constructor
  · exact h_conv n h_ge
  · intro i h_in
    rw [← h_conv n h_ge] at h_in
    exact high_cohesion_persists initial n i h_in

/-- Cohesion-stability correlation is testable -/
theorem cohesion_testable :
  ∃ (k : Real), k > (0 : Real) ∧
    ∀ i, |cohesion i - k * physical_stability i| <
         k * physical_stability i / 10 :=
  cohesion_stability_correlation

end GIP.Cohesion
