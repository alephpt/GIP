/-
GIP (Generative Identity Principle) Core Framework
Provides the foundational three-register ontological structure
-/

import Gip.Basic
import Gip.Register0
import Gip.Register1
import Gip.Register2
import Gip.Morphisms
import Gip.Projection
-- Deprecated circular approaches (kept for historical reference):
-- import Gip.ModalTopology.MetricSpace          -- Circular: constraintViolation privileges genesis
-- import Gip.ModalTopology.CoherenceOperator    -- Circular: operator defined to return genesis
-- import Gip.ModalTopology.GenesisUniqueness    -- Circular: uses above circular definitions

-- Non-circular categorical approach (current):
import Gip.ModalTopology.CategoricalUniqueness  -- Uses standard categorical initial object axiom

-- Universal Projection Functors (Phase 2):
import Gip.Projections.Topos                     -- F_T: Gen → Topos (logical structure)
import Gip.Projections.Set                       -- F_S: Gen → FinSet (membership structure)
