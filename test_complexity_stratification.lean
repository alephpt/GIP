import Gip.ComplexityStratification

/-!
# Test Suite for Complexity Stratification

This file tests the functionality of the ComplexityStratification module.
-/

open GIP

-- Test boundary detection
#eval crossesRegister 256        -- Expected: true (2^8)
#eval crossesRegister 257        -- Expected: false
#eval crossesRegister 65536      -- Expected: true (2^16)
#eval crossesRegister 65537      -- Expected: false

-- Test stratum classification
#eval complexityStratum 255      -- Expected: ⟨0, _⟩ (8-bit stratum)
#eval complexityStratum 256      -- Expected: ⟨1, _⟩ (16-bit stratum)
#eval complexityStratum 65535    -- Expected: ⟨1, _⟩ (16-bit stratum)
#eval complexityStratum 65536    -- Expected: ⟨2, _⟩ (32-bit stratum)

-- Test required level
#eval requiredLevel 100          -- Expected: .bit8
#eval requiredLevel 1000         -- Expected: .bit16
#eval requiredLevel 100000       -- Expected: .bit32

-- Test threshold values
#eval threshold .bit8            -- Expected: 256
#eval threshold .bit16           -- Expected: 65536
#eval threshold .bit32           -- Expected: 4294967296

-- Test phase transition detection
example : phaseTransitionAt 256 := by
  simp [phaseTransitionAt]

example : phaseTransitionAt 65536 := by
  simp [phaseTransitionAt]

example : ¬phaseTransitionAt 257 := by
  simp only [phaseTransitionAt]; decide

-- Test threshold ordering
example : threshold .bit8 < threshold .bit16 := threshold_8_lt_16
example : threshold .bit16 < threshold .bit32 := threshold_16_lt_32
example : threshold .bit32 < threshold .bit64 := threshold_32_lt_64

-- Test register hierarchy
example : registerHierarchy.length = 4 := by rfl

-- Test that all hierarchy elements are transitions
example : ∀ n ∈ registerHierarchy, phaseTransitionAt n := hierarchy_all_transitions

#check phase_transition_at_boundaries
#check phase_transition_at_boundaries_prop
#check unique_level_for_threshold
#check threshold_chain
#check crosses_iff_phase_transition
#check complexity_stratum_deterministic

-- Demonstrate computable boundary detection
def testValue : Nat := 1000

#eval if crossesRegister testValue
      then s!"Value {testValue} is at a register boundary"
      else s!"Value {testValue} is not at a register boundary"

#eval s!"Value {testValue} requires register level: {repr (requiredLevel testValue)}"
#eval s!"Value {testValue} is in complexity stratum: {complexityStratum testValue}"
