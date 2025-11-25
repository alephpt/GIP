/-!
# Cohesion

This file re-exports cohesion functionality from the properly grounded implementation.

## Design Note

Cohesion is now defined in Foundations.lean using Mathlib's MetricSpace.
The Selection submodule provides the full API.

## What Cohesion Means

Cohesion measures how well a structure maintains its identity through transformation.
Mathematically: `cohesion(x, y) = exp(-dist(x, y))`

- Cohesion = 1: Perfect preservation (x = y)
- Cohesion > threshold: Structure survives
- Cohesion → 0: Structure dissolves

This replaces the old axiomatic approach with proven properties from Mathlib.
-/

import Gip.Cohesion.Selection

namespace GIP.Cohesion

-- All exports come from Selection.lean which imports Foundations.lean

end GIP.Cohesion
