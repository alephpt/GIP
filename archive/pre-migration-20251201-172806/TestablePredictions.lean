/-
# Testable Predictions Across Domains

This module re-exports the testable predictions from the split sub-modules.

The content has been organized into:
- `Gip.Predictions.Core`: Prediction framework and base structures
- `Gip.Predictions.Physics`: 4 physics predictions (quantum, thermo, black holes, phase)
- `Gip.Predictions.Cognitive`: 4 cognition predictions (perception, decision, memory, concepts)
- `Gip.Predictions.Mathematical`: 3 mathematics predictions (proof, induction, Gödel)

## Total Predictions: 12 (3 from BayesianIsomorphism + 9 new)

All predictions are empirically testable and falsifiable.
If experiments contradict these predictions, GIP theory is falsified.
-/

import Gip.Predictions.Core
import Gip.Predictions.Physics
import Gip.Predictions.Cognitive
import Gip.Predictions.Mathematical

-- Re-export the namespace for backwards compatibility
namespace GIP.TestablePredictions
end GIP.TestablePredictions