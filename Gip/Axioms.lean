import Gip.Origin
import Gip.Intermediate

/-!
# GIP Axiomatic Foundation (Refactored)

Complete registry of all axioms used in the new formalization based on
`CoreTypes` and `Intermediate` morphisms.
-/

namespace GIP.Axioms

open GIP.CoreTypes
open GIP.Intermediate
open GIP.Origin

/-!
## Summary of Axiom Categories

1.  **Core Types** (3 axioms): The foundational types of the system.
2.  **Intermediate Morphisms** (8 axioms): The fundamental building blocks of the cycles.
3.  **Genesis & Duality** (3 axioms): Higher-level principles of emergence.
-/

section CoreTypes

/-!
### 1. Core Type Axioms
From `Gip/CoreTypes.lean`
-/

-- Axiom 1: `the_origin`
#check (@the_origin : OriginType)

-- Axiom 2: `origin_is_unique`
#check (@origin_is_unique : ∀ o : OriginType, o = the_origin)

-- Axiom 3: `manifest`
#check (@manifest : OriginType → Aspect → Type)

end CoreTypes

section IntermediateMorphisms

/-!
### 2. Intermediate Morphism Axioms
From `Gip/Intermediate.lean`
-/

-- Axiom 4: `ProtoIdentity` exists
#check (@proto_identity_exists : Nonempty ProtoIdentity)

-- Axiom 5: `gamma_gen` (∅ → 1)
#check (@gamma_gen : manifest the_origin Aspect.empty → ProtoIdentity)

-- Axiom 6: `gamma_res` (1 → ∅)
#check (@gamma_res : ProtoIdentity → manifest the_origin Aspect.empty)

-- Axiom 7: `iota_gen` (1 → n)
#check (@iota_gen : ProtoIdentity → manifest the_origin Aspect.identity)

-- Axiom 8: `iota_res` (n → 1)
#check (@iota_res : manifest the_origin Aspect.identity → ProtoIdentity)

-- Axiom 9: `tau_gen` (n → 1)
#check (@tau_gen : manifest the_origin Aspect.identity → ProtoIdentity)

-- Axiom 10: `tau_res` (1 → n)
#check (@tau_res : ProtoIdentity → manifest the_origin Aspect.identity)

-- Axiom 11: `epsilon_gen` (1 → ∞)
#check (@epsilon_gen : ProtoIdentity → manifest the_origin Aspect.infinite)

-- Axiom 12: `epsilon_res` (∞ → 1)
#check (@epsilon_res : manifest the_origin Aspect.infinite → ProtoIdentity)

end IntermediateMorphisms

section GenesisAndDuality

/-!
### 3. Genesis & Duality Axioms
From `Gip/Origin.lean`
-/

-- Axiom 13: `bifurcate`
#check (@bifurcate : DualAspect)

-- Axiom 14: `converge`
#check (@converge : DualAspect → manifest the_origin Aspect.identity)

-- Axiom 15: `identity_from_both`
#check (@identity_from_both : ∀ (i : manifest the_origin Aspect.identity),
  ∃ (e : manifest the_origin Aspect.empty)
    (inf : manifest the_origin Aspect.infinite)
    (dual : DualAspect),
    dual.empty = e ∧ dual.infinite = inf ∧ i = converge dual)

end GenesisAndDuality

end GIP.Axioms
