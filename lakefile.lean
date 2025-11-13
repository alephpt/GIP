import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

package gen where
  -- add package configuration options here

-- Core GIP Framework
lean_lib Gip where
  srcDir := "lib/gip"
  roots := #[`Gip]

lean_lib Monoidal where
  srcDir := "lib/monoidal"
  roots := #[`Monoidal]

lean_lib Colimits where
  srcDir := "lib/colimits"
  roots := #[`Colimits]

-- Riemann Hypothesis Proof
lean_lib Riemann where
  srcDir := "proofs/riemann"
  roots := #[`Riemann]

-- Legacy Gen namespace (for remaining files in Gen/)
lean_lib Gen where
  srcDir := "Gen"
  roots := #[`Gen]

-- Tests
lean_lib test where
  srcDir := "test"
  roots := #[`Test]
