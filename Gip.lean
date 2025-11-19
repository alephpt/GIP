import Gip.Basic
import Gip.Core
import Gip.Factorization
import Gip.ModalTopology
import Gip.Examples
import Gip.ParadoxIsomorphism
import Gip.G2Derivation
import Gip.ComplexityStratification
import Gip.InfinitePotential
import Gip.CognitiveLimits
-- import Gip.Origin  -- Has build errors, commented out

/-!
# GIP: Native Implementation

A native Lean 4 library implementing the GIP system with:
- 3 Object Classes: ∅, 𝟙, n
- 4 Morphism Types: γ, ι, id, f1
- Universal Factorization Law: id_n = (ι_n ∘ γ) ∘ ε_n
- Modal Topology: Genesis uniqueness via coherence constraints
- Infinite Potential: ∅ as pre-structural potential, not empty set

## Modules
- `GIP.Core`: Fundamental object classes and morphism types
- `GIP.Factorization`: Universal factorization theorems
- `GIP.ModalTopology`: Coherence constraints, operator, and uniqueness proofs
- `GIP.ParadoxIsomorphism`: Categorical isomorphism between fundamental paradoxes
- `GIP.G2Derivation`: Conceptual framework for G₂ connection via triality
- `GIP.ComplexityStratification`: Phase transitions at register boundaries
- `GIP.InfinitePotential`: ∅ as infinite pre-structural potential with limitation mechanism
- `GIP.CognitiveLimits`: Unknowability theorems for ∅ and ∞, knowability of n
- `GIP.Origin`: Pre-structural origin with triadic manifestation (∅, n, ∞) and circle structure
-/
