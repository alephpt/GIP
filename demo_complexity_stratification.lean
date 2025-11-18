import Gip.ComplexityStratification

/-!
# Complexity Stratification Demo

Quick demonstration of key features.
-/

open GIP

-- Demo 1: Boundary detection at each register level
section BoundaryDetection
  #eval crossesRegister (2^8)   -- true: 256 is at 8-bit boundary
  #eval crossesRegister (2^16)  -- true: 65536 is at 16-bit boundary
  #eval crossesRegister (2^32)  -- true: 4294967296 is at 32-bit boundary

  -- Non-boundaries
  #eval crossesRegister 255     -- false
  #eval crossesRegister 257     -- false
end BoundaryDetection

-- Demo 2: Stratum classification
section StratumClassification
  #eval complexityStratum 100      -- ⟨0, _⟩ (8-bit)
  #eval complexityStratum 1000     -- ⟨1, _⟩ (16-bit)
  #eval complexityStratum 100000   -- ⟨2, _⟩ (32-bit)

  #eval requiredLevel 100          -- .bit8
  #eval requiredLevel 1000         -- .bit16
  #eval requiredLevel 100000       -- .bit32
end StratumClassification

-- Demo 3: Threshold mapping
section ThresholdMapping
  #eval threshold .bit8            -- 256
  #eval threshold .bit16           -- 65536
  #eval threshold .bit32           -- 4294967296

  #eval thresholdToLevel? 256      -- some .bit8
  #eval thresholdToLevel? 257      -- none (not a boundary)
end ThresholdMapping

-- Demo 4: Phase transition theorems
section Theorems
  -- All thresholds are phase transitions
  example : phaseTransitionAt 256 := phase_transition_at_boundaries_prop .bit8
  example : phaseTransitionAt 65536 := phase_transition_at_boundaries_prop .bit16

  -- Thresholds are ordered
  example : 256 < 65536 := threshold_8_lt_16
  example : 65536 < 4294967296 := threshold_16_lt_32

  -- Complete chain
  example : 256 < 65536 ∧ 65536 < 4294967296 ∧ 4294967296 < 2^64 :=
    threshold_chain
end Theorems

-- Demo 5: Practical analysis function
def analyzeNumber (n : Nat) : String :=
  if crossesRegister n then
    s!"{n} is a phase transition point (register boundary)"
  else
    let level := requiredLevel n
    let stratum := complexityStratum n
    s!"{n} requires {repr level}, complexity stratum {stratum}"

#eval analyzeNumber 256
#eval analyzeNumber 1000
#eval analyzeNumber 65536
#eval analyzeNumber 100000

-- Demo 6: Boundary testing range
def testRange (center : Nat) (radius : Nat := 2) : List (Nat × Bool) :=
  List.range (2 * radius + 1)
    |>.map (fun i => center - radius + i)
    |>.map (fun n => (n, crossesRegister n))

#eval testRange 256    -- Test around 8-bit boundary
#eval testRange 65536  -- Test around 16-bit boundary

-- Demo 7: Verify key property - deterministic stratum assignment
example (n : Nat) : complexityStratum n = complexityStratum n :=
  complexity_stratum_deterministic n

-- Demo 8: Register hierarchy
#eval registerHierarchy
#eval registerHierarchy.length  -- 4 boundaries

-- Verify all are transitions
example : ∀ n ∈ registerHierarchy, phaseTransitionAt n :=
  hierarchy_all_transitions

#check empirical_hypothesis_phase_behavior

/-!
## Key Takeaways

1. **Four register boundaries**: 2^8, 2^16, 2^32, 2^64
2. **Phase transitions detected**: Use `crossesRegister` or `phaseTransitionAt`
3. **Stratum classification**: Use `complexityStratum` or `requiredLevel`
4. **Proven theorems**: 15 theorems, no sorry statements
5. **Empirically testable**: Framework supports measurement and validation

This formalization connects computational reality (register sizes) with
mathematical rigor (formalized theorems) and empirical science (testable predictions).
-/
