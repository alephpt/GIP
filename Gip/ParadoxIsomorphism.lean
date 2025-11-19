/-
# Paradox Isomorphism Formalization

This module re-exports the paradox isomorphism formalizations from the split sub-modules.

The content has been organized into:
- `Gip.Paradox.Core`: Shared definitions and base isomorphism structure (Russell ≅ 0/0)
- `Gip.Paradox.Classical`: Classical paradoxes (Russell, Liar, ZeroDiv)
- `Gip.Paradox.Formal`: Formal system paradoxes (Gödel, Halting)

All paradoxes share the same categorical structure as attempts at impossible
self-reference (○/○) with structure present. See the individual modules for details.
-/

import Gip.Paradox.Core
import Gip.Paradox.Classical
import Gip.Paradox.Formal

-- Re-export the namespace for backwards compatibility
namespace Gip.ParadoxIsomorphism
end Gip.ParadoxIsomorphism