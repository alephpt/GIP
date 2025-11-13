import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

package gen where
  -- add package configuration options here

lean_lib Gen where
  -- add library configuration options here

lean_lib test where
  -- test library configuration
