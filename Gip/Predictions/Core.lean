import Gip.Predictions.Mathematical
import Gip.Predictions.Physics
import Gip.Predictions.Cognitive

/-!
# GIP Predictions - Core Module

This module re-exports all prediction domains.

## Domains

- **Mathematical**: Proof complexity, NP structure, induction, incompleteness
- **Physics**: Quantum measurement, thermodynamics, black holes, phase transitions
- **Cognitive**: Feature binding, reaction time, memory, prototype learning

## Status Summary

### Proven (no sorry):
- M1: Complexity decomposition (trivial)
- M3: Gödel at n-level
- P2: Carnot efficiency bound
- C1: Binding time increases with features
- C3: Consolidation strength positive
- C4: Typicality positive

### Mathematical (provable, TODO):
- M1a: NP verification structure
- M3a: Completeness condition

### Empirical (awaiting data):
- P1: Quantum measurement cycle
- P3: Black hole information conservation
- P4: Critical exponents
- C2: RT decomposition
- M2: Induction-cycle isomorphism
-/

namespace GIP.Predictions.Core

-- Re-export all prediction modules
open GIP.Predictions.Mathematical
open GIP.Predictions.Physics
open GIP.Predictions.Cognitive

end GIP.Predictions.Core
