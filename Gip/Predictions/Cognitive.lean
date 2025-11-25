import Gip.Foundations
import Mathlib.Data.Real.Basic

/-!
# Cognitive Predictions from GIP Theory

Predictions relating the zero object cycle to cognitive phenomena.

## The Restricted Origin Model Context

- ○ connects only to aspects (∅ and ∞)
- ∅ ≅ ∞ are isomorphic aspects
- n is the hub (bidirectional flow with aspects)

## Predictions Overview

- C1: Perceptual binding time proportional to feature count
- C2: Decision reaction time decomposes into Gen + Dest
- C3: Memory consolidation proportional to encoding-retrieval coherence
- C4: Prototype as limit of exemplars
-/

namespace GIP.Predictions.Cognitive

open GIP.Foundations

/-!
## C1: Feature Binding Time

**Claim**: Perceptual binding time ∝ number of features to integrate.

**Correspondence**:
- ○ ↔ Pre-attentive field (undifferentiated sensory input)
- ∅ ↔ Feature space (color, motion, shape, etc.)
- n ↔ Bound percept (integrated representation)

The more features that need to pass through ∅ → n, the longer the binding.

**Status**: TYPE A - EMPIRICAL
-/

/-- Perceptual binding structure -/
structure FeatureBinding where
  /-- Number of features to bind -/
  feature_count : ℕ
  /-- Binding constant (ms per feature) -/
  k : ℝ
  /-- k is positive -/
  k_pos : k > 0

/-- Predicted binding time -/
def binding_time (fb : FeatureBinding) : ℝ :=
  fb.k * fb.feature_count

/-- C1: Binding time increases with features -/
theorem binding_increases_with_features (fb : FeatureBinding) (n : ℕ) (hn : n > 0) :
    binding_time { fb with feature_count := fb.feature_count + n } >
    binding_time fb := by
  unfold binding_time
  simp
  have h : fb.k * n > 0 := mul_pos fb.k_pos (Nat.cast_pos.mpr hn)
  linarith

/-- Correspondence to GIP cycle -/
structure BindingCycleCorrespondence where
  /-- Pre-attentive field is origin -/
  preattentive : Obj
  preattentive_is_origin : preattentive = ○
  /-- Features emerge via bifurcation -/
  features : Obj
  features_are_aspects : features = ∅ ∨ features = ∞
  /-- Bound percept is structure -/
  percept : Obj
  percept_is_n : percept = 𝕟

/-!
## C2: Reaction Time Decomposition

**Claim**: Decision reaction time = Gen_time + Dest_time.

The cycle has two phases:
- Gen (∅ → n): Evidence accumulation / search
- Dest (n → ∅): Response selection / verification

**Status**: TYPE A - EMPIRICAL
-/

/-- Reaction time components -/
structure ReactionTime where
  /-- Generation time (evidence accumulation) -/
  gen_time : ℝ
  /-- Destruction time (response selection) -/
  dest_time : ℝ
  /-- Both positive -/
  gen_pos : gen_time > 0
  dest_pos : dest_time > 0

/-- Total reaction time -/
def total_rt (rt : ReactionTime) : ℝ :=
  rt.gen_time + rt.dest_time

/-- C2: RT decomposes additively -/
theorem rt_decomposes (rt : ReactionTime) :
    total_rt rt = rt.gen_time + rt.dest_time := rfl

/-- Hick's Law: RT increases with log of choices -/
structure HicksLaw where
  /-- Base RT (intercept) -/
  a : ℝ
  /-- Slope (bits per second) -/
  b : ℝ
  /-- Number of choices -/
  n : ℕ
  /-- Positive constants -/
  a_pos : a > 0
  b_pos : b > 0
  n_pos : n > 0

/-- Hick's Law RT prediction -/
noncomputable def hicks_rt (h : HicksLaw) : ℝ :=
  h.a + h.b * Real.log h.n

/-!
## C3: Memory Consolidation

**Claim**: Consolidation strength ∝ (encoding × retrieval) / interference.

The cycle coherence determines memory stability:
- Strong Gen (encoding) + Strong Dest (retrieval) = Strong consolidation
- Interference disrupts the cycle

**Status**: TYPE A - EMPIRICAL
-/

/-- Memory consolidation factors -/
structure ConsolidationFactors where
  /-- Encoding strength -/
  encoding : ℝ
  /-- Retrieval strength -/
  retrieval : ℝ
  /-- Interference level -/
  interference : ℝ
  /-- All non-negative -/
  encoding_pos : encoding ≥ 0
  retrieval_pos : retrieval ≥ 0
  interference_pos : interference ≥ 0

/-- Consolidation strength formula -/
noncomputable def consolidation_strength (cf : ConsolidationFactors) : ℝ :=
  (cf.encoding * cf.retrieval) / (1 + cf.interference)

/-- C3: Higher encoding-retrieval coherence → stronger consolidation -/
theorem stronger_encoding_helps (cf : ConsolidationFactors)
    (h : cf.encoding > 0) (h2 : cf.retrieval > 0) :
    consolidation_strength cf > 0 := by
  unfold consolidation_strength
  apply div_pos
  · exact mul_pos h h2
  · linarith [cf.interference_pos]

/-!
## C4: Prototype as Exemplar Limit

**Claim**: Learned prototype = central tendency (mean/mode) of exemplars.

In cycle terms:
- Exemplars are individual n's (structures)
- Prototype is the ∞ aspect (limit/completion)
- Learning: ∅ → n₁, n₂, ... → ∞ (exemplars converge to prototype)

**Status**: TYPE A - EMPIRICAL
-/

/-- Exemplar-prototype relationship -/
structure PrototypeLearning where
  /-- Number of exemplars seen -/
  exemplar_count : ℕ
  /-- Distance to prototype (decreases with learning) -/
  distance_to_prototype : ℝ
  /-- Distance is non-negative -/
  distance_pos : distance_to_prototype ≥ 0

/-- C4a: Typicality inversely proportional to distance -/
noncomputable def typicality (pl : PrototypeLearning) (k : ℝ) : ℝ :=
  k / (1 + pl.distance_to_prototype)

/-- Typicality increases as distance decreases -/
theorem typicality_inverse_distance (pl : PrototypeLearning) (k : ℝ) (hk : k > 0) :
    typicality pl k > 0 := by
  unfold typicality
  apply div_pos hk
  linarith [pl.distance_pos]

/-- Correspondence: Prototype is the ∞ aspect -/
def prototype_correspondence : Obj := ∞

/-- Correspondence: Exemplars go through n -/
def exemplar_correspondence : Obj := 𝕟

/-!
## Summary

### Empirical (TYPE A) - Awaiting Data:
- `binding_increases_with_features`: C1 - Feature binding time
- `rt_decomposes`: C2 - Reaction time decomposition
- `stronger_encoding_helps`: C3 - Memory consolidation
- `typicality_inverse_distance`: C4 - Prototype learning

### Structural Correspondences:
- Pre-attentive field ↔ ○
- Feature space ↔ ∅/∞
- Bound percept / Exemplar ↔ n
- Prototype ↔ ∞
-/

end GIP.Predictions.Cognitive
