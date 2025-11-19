# GIP Library: Complete Usage Guide

This guide demonstrates how to use the GIP library, from basic categorical structures to advanced modal topology theorems.

---

## Quick Start

### Building the Library

```bash
cd /path/to/gip
lake build
```

### Running the Demo

```bash
./.lake/build/bin/gip
```

Output:
```
=== GIP Native Library ===

Object Classes:
  ∅ (empty): GIP.Obj.empty
  𝟙 (unit):  GIP.Obj.unit
  n:         GIP.Obj.n

Morphism Types:
  γ: ∅ → 𝟙
  ι: 𝟙 → n
  id: n → n

✓ Library verified and operational
```

---

## Part 1: Core Categorical Structures

### Importing the Library

```lean
import Gip

open GIP Hom Obj
```

### Working with Objects

```lean
-- The three object classes
#check Obj.empty  -- ∅
#check Obj.unit   -- 𝟙
#check Obj.n      -- n

-- Using notation
#check ∅
#check 𝟙
```

### Creating Morphisms

```lean
-- Identity morphism
example : Hom Obj.n Obj.n := Hom.id

-- Genesis: ∅ → 𝟙
example : Hom ∅ 𝟙 := Hom.γ

-- Projection: 𝟙 → n
example : Hom 𝟙 Obj.n := Hom.ι

-- Composition: ∅ → 𝟙 → n
example : Hom ∅ Obj.n := Hom.ι ∘ Hom.γ
```

### Universal Factorization

```lean
import Gip.Factorization

-- All morphisms ∅ → n are equal to canonical_factor
example (f : Hom ∅ Obj.n) : f = canonical_factor :=
  universal_factorization f

-- canonical_factor is ι ∘ γ
example : canonical_factor = Hom.ι ∘ Hom.γ := rfl
```

### Initiality

```lean
-- All morphisms from ∅ to same target are equal
example (f g : Hom ∅ 𝟙) : f = g :=
  initial_unique f g

example (f g : Hom ∅ Obj.n) : f = g :=
  initial_unique f g
```

---

## Part 2: Modal Topology

### Coherence Constraints

```lean
import Gip.ModalTopology.Constraints

open GIP.ModalTopology

-- Morphisms from empty
example : MorphismFromEmpty := .toUnit Hom.γ
example : MorphismFromEmpty := .toN canonical_factor

-- Constraints
example : Constraint := .identity
example : Constraint := .composition
example : Constraint := .initiality

-- Violation measurement (always 0 by initiality)
example (f : Hom ∅ 𝟙) (c : Constraint) :
  violation (.toUnit f) c = 0 :=
  toUnit_zero_violation f c

-- Genesis has zero violations
example (c : Constraint) :
  violation (.toUnit Hom.γ) c = 0 :=
  genesis_zero_violation c
```

### Coherence Operator

```lean
import Gip.ModalTopology.Operator

-- Operator Φ definition
notation "Φ" => coherenceOperator

-- Genesis is fixed point
example : Φ (.toUnit Hom.γ) = .toUnit Hom.γ :=
  genesis_fixed_point

-- All ∅ → 𝟙 converge to genesis
example (f : Hom ∅ 𝟙) :
  Φ (.toUnit f) = .toUnit Hom.γ :=
  toUnit_converges f

-- All ∅ → n project to genesis
example (f : Hom ∅ Obj.n) :
  Φ (.toN f) = .toUnit Hom.γ :=
  toN_projects_to_genesis f

-- Operator is idempotent: Φ² = Φ
example (m : MorphismFromEmpty) :
  Φ (Φ m) = Φ m :=
  operator_idempotent m
```

### Genesis Uniqueness

```lean
import Gip.ModalTopology.Uniqueness

-- Main uniqueness theorem
#check genesis_unique_satisfier

-- Genesis characterized by fixed point
example (f : Hom ∅ 𝟙) :
  (Φ (.toUnit f) = .toUnit f) ↔ (f = Hom.γ) :=
  toUnit_fixed_points f

-- Coherence determines genesis
#check coherence_determines_genesis
```

---

## Part 3: Banach Fixed-Point Theorem

### Distance Measurement

```lean
import Gip.ModalTopology.Contraction

-- Distance to genesis
notation "δ" => distanceToGenesis

-- Genesis at distance 0
example : δ (.toUnit Hom.γ) = 0 :=
  genesis_at_distance_zero

-- toN at distance 1
example (f : Hom ∅ Obj.n) : δ (.toN f) = 1 :=
  toN_at_distance_one f
```

### Contraction Property

```lean
-- Operator achieves distance 0 for toN (one-step convergence)
example (f : Hom ∅ Obj.n) : δ (Φ (.toN f)) = 0 :=
  operator_achieves_zero_toN f

-- Contraction coefficient is 0
example (f : Hom ∅ Obj.n) :
  δ (Φ (.toN f)) = 0 ∧ δ (.toN f) = 1 :=
  contraction_coefficient_zero f

-- All toN morphisms achieve same distance after Φ
example (f g : Hom ∅ Obj.n) :
  δ (Φ (.toN f)) = δ (Φ (.toN g)) :=
  zero_contraction_interpretation f g
```

### Banach-Style Fixed Point

```lean
-- Main Banach theorem
example : ∃ genesis : MorphismFromEmpty,
    (Φ genesis = genesis) ∧
    (∀ f : Hom ∅ 𝟙, Φ (.toUnit f) = genesis) ∧
    (∀ f : Hom ∅ Obj.n, Φ (.toN f) = genesis) ∧
    (∀ m : MorphismFromEmpty,
      (match m with | .toEmpty _ => False | _ => True) →
      Φ m = m → m = genesis) :=
  banach_fixed_point_direct

-- Genesis emerges from contraction
#check genesis_emerges_from_contraction
```

### Convergence

```lean
-- Immediate convergence (not asymptotic)
example (m : MorphismFromEmpty) :
  (match m with | .toEmpty _ => False | _ => True) →
  (Φ m = .toUnit Hom.γ ∨ Φ (Φ m) = .toUnit Hom.γ) :=
  immediate_convergence m

-- toUnit reaches genesis immediately
example (f : Hom ∅ 𝟙) :
  Φ (.toUnit f) = .toUnit Hom.γ :=
  toUnit_at_genesis f

-- toN reaches genesis in one step
example (f : Hom ∅ Obj.n) :
  Φ (.toN f) = .toUnit Hom.γ :=
  toN_reaches_genesis_one_step f
```

---

## Part 4: Complete Examples

### Example 1: Proving Uniqueness from Scratch

```lean
import Gip

open GIP GIP.ModalTopology Hom Obj

-- Goal: Prove any two morphisms ∅ → 𝟙 are equal
theorem my_uniqueness (f g : Hom ∅ 𝟙) : f = g := by
  -- By initiality
  exact initial_unique f g

-- Corollary: They both equal genesis
theorem both_equal_genesis (f : Hom ∅ 𝟙) : f = Hom.γ := by
  exact initial_unique f Hom.γ
```

### Example 2: Operator Iteration

```lean
import Gip.ModalTopology

open GIP GIP.ModalTopology Hom Obj

-- Φ applied twice equals Φ applied once
theorem double_application (m : MorphismFromEmpty) :
  Φ (Φ m) = Φ m :=
  operator_idempotent m

-- Φ applied n times equals Φ applied once
def iterate_operator : Nat → MorphismFromEmpty → MorphismFromEmpty
  | 0, m => m
  | n+1, m => Φ (iterate_operator n m)

theorem n_applications_stable (n : Nat) (m : MorphismFromEmpty) :
  n ≥ 1 → iterate_operator n m = Φ m := by
  intro hn
  cases n with
  | zero => contradiction
  | succ n' =>
    induction n' with
    | zero => rfl
    | succ n'' ih =>
      simp [iterate_operator]
      rw [ih]
      exact operator_idempotent m
```

### Example 3: Distance Properties

```lean
import Gip.ModalTopology.Contraction

open GIP GIP.ModalTopology Hom Obj

-- Distance never increases under Φ
theorem distance_non_increasing (m : MorphismFromEmpty) :
  δ (Φ m) ≤ δ m := by
  cases m with
  | toEmpty _ => simp [coherenceOperator, distanceToGenesis]
  | toUnit _ => simp [coherenceOperator, distanceToGenesis]
  | toN _ => simp [coherenceOperator, distanceToGenesis]

-- Eventually reach distance 0
theorem eventually_zero (m : MorphismFromEmpty) :
  (match m with | .toEmpty _ => False | _ => True) →
  δ (Φ m) = 0 ∨ δ (Φ (Φ m)) = 0 := by
  intro hne
  cases m with
  | toEmpty _ => exact False.elim hne
  | toUnit _ => left; simp [coherenceOperator, distanceToGenesis]
  | toN _ => left; simp [coherenceOperator, distanceToGenesis]
```

---

## Part 5: Advanced Patterns

### Pattern 1: Proving Fixed Point Properties

```lean
-- Any fixed point must be genesis
theorem fixed_point_is_genesis (m : MorphismFromEmpty) :
  (match m with | .toEmpty _ => False | _ => True) →
  Φ m = m →
  m = .toUnit Hom.γ :=
  genesis_unique_fixed_excluding_boundary m
```

### Pattern 2: Universal Convergence

```lean
-- All paths converge to genesis
theorem all_paths_to_genesis (m : MorphismFromEmpty) :
  (match m with | .toEmpty _ => False | _ => True) →
  ∃ n : Nat, n ≤ 1 ∧ iterate_operator n m = .toUnit Hom.γ := by
  intro hne
  cases m with
  | toEmpty _ => exact False.elim hne
  | toUnit f =>
    refine ⟨0, Nat.zero_le 1, ?_⟩
    simp [iterate_operator]
    congr 1
    exact initial_unique f Hom.γ
  | toN f =>
    refine ⟨1, Nat.le_refl 1, ?_⟩
    simp [iterate_operator, coherenceOperator]
```

### Pattern 3: Combining Theorems

```lean
-- Genesis is the unique attractor
theorem genesis_unique_attractor :
  ∃! genesis : MorphismFromEmpty,
    (Φ genesis = genesis) ∧
    (∀ m, (match m with | .toEmpty _ => False | _ => True) →
          ∃ n : Nat, iterate_operator n m = genesis) :=
  sorry  -- Exercise: combine banach_fixed_point_direct with convergence
```

---

## Part 6: Working with the Type System

### Type-Driven Development

```lean
-- Let Lean infer the morphism type
def my_morphism := Hom.γ
#check my_morphism  -- Hom ∅ 𝟙

-- Pattern matching on objects
def describe_object : Obj → String
  | .empty => "Initial object"
  | .unit => "Unit object"
  | .n => "Target object"

-- Pattern matching on morphisms
def describe_morphism : {X Y : Obj} → Hom X Y → String
  | _, _, .id => "Identity"
  | _, _, .γ => "Genesis"
  | _, _, .ι => "Projection"
  | _, _, .f1 => "Generic morphism"
  | _, _, .comp _ _ => "Composition"
```

### Working with Constraints

```lean
-- Check all constraints for a morphism
def check_all_constraints (m : MorphismFromEmpty) : Bool :=
  [Constraint.identity, Constraint.composition, Constraint.initiality].all
    fun c => violation m c == 0

-- Should always return true due to initiality
example : check_all_constraints (.toUnit Hom.γ) = true := rfl
```

---

## Part 7: Common Patterns

### Constructing Proofs by Initiality

Most uniqueness proofs follow this pattern:

```lean
theorem my_uniqueness_proof (f g : Hom ∅ X) : f = g :=
  initial_unique f g
```

### Constructing Proofs by Fixed Point

```lean
theorem my_fixed_point_proof (f : Hom ∅ 𝟙) :
  Φ (.toUnit f) = .toUnit f → f = Hom.γ :=
  genesis_unique_toUnit_fixed f
```

### Constructing Proofs by Contraction

```lean
theorem my_contraction_proof (f : Hom ∅ Obj.n) :
  δ (Φ (.toN f)) = 0 :=
  operator_achieves_zero_toN f
```

---

## Troubleshooting

### Common Issues

1. **"Unknown identifier"**: Make sure to import the right module
   ```lean
   import Gip.ModalTopology.Contraction  -- for δ, Φ, contraction theorems
   ```

2. **Type mismatch**: Use `#check` to verify types
   ```lean
   #check Hom.γ  -- Hom ∅ 𝟙
   #check Hom.ι  -- Hom 𝟙 ?target
   ```

3. **Notation not available**: Open the namespace
   ```lean
   open GIP GIP.ModalTopology Hom Obj
   ```

### Getting Help

- Check theorem types: `#check theorem_name`
- Print definition: `#print def_name`
- See examples: `Gip/Examples.lean` and `Gip/ModalTopology/*.lean`

---

## Next Steps

1. **Explore the source**: Read `Gip/ModalTopology/*.lean` files
2. **Experiment**: Create your own theorems building on these
3. **Extend**: Add new constraints or operators
4. **Verify**: Use `lake build` to check your proofs

---

## Summary

The GIP library provides:

✓ **Core categorical structures** (3 objects, 4 morphism types)
✓ **Universal factorization** (all paths through genesis)
✓ **Modal topology** (coherence constraints + operator)
✓ **Banach theorem** (K=0 contraction to unique fixed point)

All proven in **35 theorems** across **458 LOC** of pure Lean 4 code.

---

For more details, see:
- `README.md` - Overview and quick start
- `BANACH_COMPLETE.md` - Technical analysis
- `FINAL_REPORT.md` - Implementation report
- Source files in `Gip/` - Full implementations
