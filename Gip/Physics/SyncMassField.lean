/-
Copyright (c) 2025 Neotec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/

import Gip.Physics.SyncMassField.Foundations
import Gip.Physics.SyncMassField.DiracStructure
import Gip.Physics.SyncMassField.ChiralSymmetry
import Gip.Physics.SyncMassField.FieldEquation
import Gip.Physics.SyncMassField.Symmetries
import Gip.Physics.SyncMassField.VacuumStructure
import Gip.Physics.SyncMassField.Lagrangian

/-!
# Synchronization Mass Field Theory

This module provides the main interface to the SMFT formalization,
re-exporting all completed phases:

## Phase 1: Foundations (Weeks 1-2)
- `Foundations` - Basic types, fields, and potentials
- `DiracStructure` - Clifford algebra, gamma matrices, and spinors

## Phase 2: Chiral Symmetry (Week 3)
- `ChiralSymmetry` - Chiral matrix γ^5, projectors, exponential e^(iθγ^5)

## Phase 3: Field Equation (Week 4)
- `FieldEquation` - The fundamental SMFT equation (i∂̸ - M)ψ = 0

## Phase 5: Symmetries & Vacuum (Weeks 5-6)
- `Symmetries` - U(1) symmetry and chiral transformations
- `VacuumStructure` - Symmetry breaking, critical mass scaling m² ∝ (K - Kc)

## Phase 6: Lagrangian (Week 7)
- `Lagrangian` - Variational formulation, action principle δS = 0 ⟹ SMFT equation

## Next: Phase 7 (Weeks 8-9) - GIP Correspondence
The critical phase proving SMFT IS the physical proof of GIP:
- GIP convergence ↔ SMFT variational principle
- ProtoIdentity optimization ↔ Action minimization
- Synchronization = Mass generation (proved both ways)

## Usage

```lean
import Gip.Physics.SyncMassField

open GIP.Physics.SyncMassField
```
-/