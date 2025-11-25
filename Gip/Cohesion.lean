/-!
# Cohesion

Re-exports cohesion from Foundations.

Cohesion measures structural integrity: `cohesion(x,y) = exp(-dist(x,y))`
Structures with cohesion > threshold survive and form {N}.
-/

import Gip.Cohesion.Selection

namespace GIP.Cohesion

-- All exports from Selection.lean

end GIP.Cohesion
