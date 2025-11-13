/-
Gen Category Library - Legacy Root
This file now serves as a compatibility layer pointing to the new structure.
New code should import from Gip, Monoidal, Colimits, or Riemann directly.
-/

-- Core GIP Framework (now in lib/gip/)
-- import Gip.Basic
-- import Gip.Morphisms
-- import Gip.Register0
-- import Gip.Register1
-- import Gip.Register2
-- import Gip.Projection

-- Monoidal Theory (now in lib/monoidal/)
-- import Monoidal.Structure
-- import Monoidal.Balance
-- import Monoidal.Symmetry
-- import Monoidal.SymmetryPreservation

-- Colimit Theory (now in lib/colimits/)
-- import Colimits.Theory
-- import Colimits.EulerProducts
-- import Colimits.PartialEulerProducts
-- import Colimits.Preservation

-- Riemann Hypothesis Proof (now in proofs/riemann/)
-- import Riemann.FunctionalEquation
-- import Riemann.RiemannHypothesis
-- import Riemann.BalanceSymmetryCorrespondence
-- import Riemann.ZetaMorphism
-- import Riemann.ZetaProperties
-- import Riemann.ZetaEvaluation
-- import Riemann.Equilibria
-- import Riemann.EquilibriumBalance
-- import Riemann.PrimeGeneration
-- import Riemann.Primes

-- Remaining Gen utilities
import Gen.NAll
import Gen.NAllProperties
import Gen.NAllDiagram
import Gen.Comp
import Gen.CategoryAxioms
import Gen.Endomorphisms
import Gen.EndomorphismProofs
import Gen.UniversalCycle
import Gen.GenTeleological
import Gen.Examples
import Gen.Benchmarks
