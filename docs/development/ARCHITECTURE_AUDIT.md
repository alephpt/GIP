# Architecture Audit: GIP-Core vs RH-Application

**Date**: 2025-11-17
**Purpose**: Detailed audit of all code to identify what belongs where
**Goal**: Establish clear migration plan for Phase 0 refactoring

---

## Current File Structure Analysis

### lib/gip/ - Should be PURE GIP Foundation

#### ✅ CORRECT (Keep in lib/gip/)

| File | Status | Reason |
|------|--------|--------|
| `Gip/Register0.lean` | ✅ KEEP | Defines ∅ (pure potential) |
| `Gip/Register1.lean` | ✅ KEEP | Defines 𝟙 (proto-unity) |
| `Gip/Basic.lean` | ⚠️ FIX | Core but has nat - needs purification |
| `Gip/Morphisms.lean` | ⚠️ FIX | Core but has RH morphisms - needs cleaning |

#### ❌ WRONG (Move OUT of lib/gip/)

| File | Current Location | Target Location | Reason |
|------|-----------------|-----------------|--------|
| `Gip/Register2.lean` | `lib/gip/` | DELETE | Numbers emerge via projection, not in Gen |
| `Gip/Projection.lean` | `lib/gip/` | REFACTOR | Split into proper Projections/ |

#### ⚠️ INCOMPLETE (Must Implement)

| File | Status | Priority | Action |
|------|--------|----------|--------|
| `Gip/Projections/Topos.lean` | STUB/MISSING | HIGH | Implement F_T: Gen → Topos |
| `Gip/Projections/Set.lean` | PARTIAL | HIGH | Complete F_S: Gen → Set |
| `Gip/Projections/Ring.lean` | BYPASSED | HIGH | Fix F_R to target CommRing not Comp |
| `Gip/Projections/Comp.lean` | RH-SPECIFIC | HIGH | Move to proofs/riemann/ |

---

## Detailed Code Audit

### File: lib/gip/Gip/Basic.lean

**Current State**:
```lean
inductive GenObj : Type where
  | empty : GenObj      -- ✅ KEEP (Register 0)
  | unit : GenObj       -- ✅ KEEP (Register 1)
  | nat : Nat → GenObj  -- ❌ REMOVE (violates GIP)
```

**Target State**:
```lean
inductive GenObj : Type where
  | empty : GenObj      -- ∅ (pure potential)
  | unit : GenObj       -- 𝟙 (proto-unity)
  -- Natural numbers emerge via F_R: Gen → CommRing → ℕ
```

**Migration Impact**: HIGH
- All references to `GenObj.nat n` must be refactored
- Tests using nat must be updated
- Proofs using nat must move to proofs/riemann/

---

### File: lib/gip/Gip/Morphisms.lean

**Current State** (8 morphism types):
```lean
inductive GenMorphism : GenObj → GenObj → Type where
  | id_empty : GenMorphism .empty .empty           -- ✅ KEEP
  | id_unit : GenMorphism .unit .unit              -- ✅ KEEP
  | id_nat (n : Nat) : GenMorphism (.nat n) (.nat n)  -- ❌ REMOVE (no nat)
  | genesis : GenMorphism .empty .unit             -- ✅ KEEP (THE morphism)
  | instantiation (n : Nat) : GenMorphism .unit (.nat n)  -- ❌ REMOVE (no nat)
  | divisibility (n m : Nat) (h : m ∣ n) : GenMorphism (.nat n) (.nat m)  -- ❌ MOVE to RH
  | gamma_prime (p : Prime) : GenMorphism .unit (.nat p)  -- ❌ MOVE to RH
  | comp : GenMorphism A B → GenMorphism B C → GenMorphism A C  -- ✅ KEEP
```

**Target State** (3 morphism types):
```lean
inductive GenMorphism : GenObj → GenObj → Type where
  | id_empty : GenMorphism .empty .empty
  | id_unit : GenMorphism .unit .unit
  | genesis : GenMorphism .empty .unit   -- γ: ∅ → 𝟙 (ontological necessity)
  | comp : GenMorphism A B → GenMorphism B C → GenMorphism A C
```

**Where RH morphisms go**:
- `divisibility` → `proofs/riemann/ArithmeticStructure.lean` (via F_R projection)
- `gamma_prime` → `proofs/riemann/EulerFactors.lean` (prime-specific)
- `instantiation` → `proofs/riemann/Instantiation.lean` (via F_R)

**Migration Impact**: VERY HIGH
- Entire RH proof depends on these morphisms
- Must redefine them as projected structures
- All proofs using them must be rewritten

---

### File: lib/gip/Gip/Register2.lean

**Current State**: Defines numeric register within Gen

**Problem**: Register 2 (numbers) should NOT be in Gen itself. Numbers emerge via projection.

**Action**: DELETE this file

**Target**: Numbers defined via:
```lean
-- In proofs/riemann/ArithmeticStructure.lean
def ℕ_via_F_R : Type := Image (F_R GenObj.unit)
-- Natural numbers as the image of 𝟙 under F_R projection
```

**Migration Impact**: MEDIUM
- Remove all imports of Register2
- Redefine numeric structures via projections
- Update tests

---

### File: lib/gip/Gip/Projections/Topos.lean

**Current State**: MISSING or STUB

**GIP Requirement**: ESSENTIAL - F_T: Gen → Topos must exist

**Must Implement**:
```lean
-- Target: Topos category (for logical structure)
inductive ToposObj where
  | empty_type : ToposObj       -- ⊥ (false proposition)
  | unit_type : ToposObj        -- ⊤ (true proposition)
  | prop_type : ToposObj        -- Prop (propositions)

-- Functor: F_T: Gen → Topos
def F_T_obj : GenObj → ToposObj
  | .empty => .empty_type       -- ∅ → ⊥
  | .unit => .unit_type         -- 𝟙 → ⊤

-- Prove: F_T preserves structure
theorem F_T_preserves_genesis :
  F_T_morphism genesis = (false_implies_true : ⊥ → ⊤)
```

**Priority**: HIGH - Without this, cannot claim Gen grounds logic

---

### File: lib/gip/Gip/Projections/Set.lean

**Current State**: PARTIAL - some structure defined but incomplete

**GIP Requirement**: ESSENTIAL - F_S: Gen → Set must be complete

**Current Issues**:
- Missing morphism mappings
- Incomplete functoriality proofs
- Edge cases not handled

**Must Complete**:
```lean
-- Complete all morphism cases
def F_S_morphism : {A B : GenObj} → GenMorphism A B → SetMorphism (F_S_obj A) (F_S_obj B)
  | .empty, .unit, .genesis => empty_to_singleton  -- ✅ EXISTS
  | _, _, .id_empty => id_empty_set                 -- ✅ EXISTS
  | _, _, .id_unit => id_singleton                  -- ✅ EXISTS
  | _, _, .comp f g => comp (F_S_morphism f) (F_S_morphism g)  -- ⚠️ VERIFY

-- Prove all functoriality
theorem F_S_preserves_composition : ...  -- ⚠️ CURRENTLY SORRY
```

**Priority**: HIGH - Needed for claiming Gen grounds membership

---

### File: lib/gip/Gip/Projections/Ring.lean

**Current State**: IMPLEMENTED but BYPASSES CommRing, goes directly to Comp

**Problem**: Should be F_R: Gen → CommRing, not F_R: Gen → Comp

**Current (WRONG)**:
```lean
def F_R_obj : GenObj → RingObj
  | .empty => .zero           -- ✅ OK
  | .unit => .integers        -- ✅ OK
  | .nat n => .product n      -- ❌ WRONG (no nat in Gen)
```

**Target (CORRECT)**:
```lean
-- Pure GIP version
def F_R_obj : GenObj → RingObj
  | .empty => .zero           -- {0} (trivial ring)
  | .unit => .integers        -- ℤ (integers)

-- Numbers emerge from this, not as input
def project_to_numbers (n : ℕ) : RingObj :=
  -- Construct n-fold product of ℤ via iterated monoidal operations
  iterate_monoidal_product (F_R_obj .unit) n
```

**Then Separately**:
- `Ring_to_Comp: CommRing → Comp` (separate functor)
- `F_comp = Ring_to_Comp ∘ F_R` (composition)

**Migration Impact**: MEDIUM
- Separate Ring and Comp projections
- Rewrite composite functor properly
- Update all uses

---

### File: lib/gip/Gip/Projections/Comp.lean

**Current State**: Complex analysis projection, mixed with RH

**Problem**: This IS the RH bridge - should be in proofs/riemann/

**Action**: MOVE to `proofs/riemann/ComplexExtension.lean`

**Reason**:
- F_comp uses Ring_to_Comp which is RH-specific
- Zeta function integration is RH application
- Should not be in pure GIP foundation

**Migration Impact**: LOW
- Simply move file
- Update imports
- Clear separation of concerns

---

## Files That Should NOT Exist in lib/gip/

### Currently in lib/gip/ (MUST MOVE)

| File | Current Location | Target Location | Reason |
|------|-----------------|-----------------|--------|
| Any balance-specific code | `lib/gip/` | `lib/monoidal/Balance.lean` | Generic monoidal theory |
| Any colimit-specific code | `lib/gip/` | `lib/colimits/` | Generic colimit theory |
| Any N_all construction | `lib/gip/` | `proofs/riemann/NAllConstruction.lean` | RH-specific application |
| Any ζ_gen morphism | `lib/gip/` | `proofs/riemann/ZetaMorphism.lean` | RH-specific |
| Any equilibria definition | `lib/gip/` | `proofs/riemann/Equilibria.lean` | RH-specific |
| Any RH theorem statements | `lib/gip/` | `proofs/riemann/RiemannHypothesis.lean` | Obviously RH-specific |

---

## New Directory Structure (TARGET)

```
categorical/lean/
├── lib/
│   ├── gip/                          # PURE GIP FOUNDATION
│   │   ├── Gip/
│   │   │   ├── Basic.lean            # Only ∅, 𝟙 (NO nat)
│   │   │   ├── Morphisms.lean        # Only genesis, id, comp (NO divisibility, gamma)
│   │   │   ├── Register0.lean        # ∅ definition
│   │   │   ├── Register1.lean        # 𝟙 definition
│   │   │   ├── CategoryLaws.lean     # Category axioms
│   │   │   └── Projections/
│   │   │       ├── Topos.lean        # F_T: Gen → Topos ✅ IMPLEMENT
│   │   │       ├── Set.lean          # F_S: Gen → Set ✅ COMPLETE
│   │   │       └── Ring.lean         # F_R: Gen → CommRing ✅ FIX (no nat, no Comp)
│   │   └── Gip.lean                  # Main export
│   │
│   ├── monoidal/                     # GENERIC MONOIDAL THEORY
│   │   ├── MonoidalCategory.lean    # Definition of monoidal categories
│   │   ├── Coherence.lean           # Mac Lane coherence theorem
│   │   ├── Balance.lean             # Balance conditions (generic)
│   │   └── TensorProducts.lean      # Tensor product structure
│   │
│   └── colimits/                     # GENERIC COLIMIT THEORY
│       ├── Colimit.lean             # Colimit construction
│       ├── Cocone.lean              # Cocone universal property
│       └── Preservation.lean        # Functor preservation of colimits
│
├── proofs/riemann/                   # RH APPLICATION (everything else)
│   ├── ArithmeticStructure.lean     # Define ℕ, ℤ, primes via F_R
│   ├── DivisibilityMorphisms.lean   # divisibility morphisms (via F_R)
│   ├── EulerFactors.lean            # gamma_prime morphisms (via F_R)
│   ├── Instantiation.lean           # instantiation morphisms (via F_R)
│   ├── NAllConstruction.lean        # N_all as colimit (RH-specific)
│   ├── ZetaMorphism.lean            # ζ_gen: N_all → N_all
│   ├── ComplexExtension.lean        # Ring_to_Comp, F_comp
│   ├── Equilibria.lean              # Equilibrium points in N_all
│   ├── EquilibriaZerosMap.lean      # THE BRIDGE (non-circular derivation)
│   ├── BalanceCondition.lean        # RH-specific balance
│   ├── FunctionalEquation.lean      # Derive from monoidal balance
│   └── RiemannHypothesis.lean       # Main RH theorem
│
└── test/
    ├── gip/                          # GIP foundation tests
    │   ├── BasicTests.lean
    │   ├── ToposProjectionTests.lean
    │   ├── SetProjectionTests.lean
    │   └── RingProjectionTests.lean
    │
    └── riemann/                      # RH proof tests
        ├── ArithmeticTests.lean
        ├── ZetaMorphismTests.lean
        └── EquilibriaTests.lean
```

---

## Migration Strategy

### Step 1: Create Target Structure (1 day)
```bash
mkdir -p lib/monoidal lib/colimits
mkdir -p proofs/riemann
# Set up new directory structure
```

### Step 2: Extract Pure GIP (3 days)
1. Create `Gip/Basic.lean.NEW` with only ∅, 𝟙
2. Create `Gip/Morphisms.lean.NEW` with only genesis, id, comp
3. Remove Register2.lean
4. Update all imports

### Step 3: Implement Missing Functors (5 days)
1. Implement F_T: Gen → Topos (2 days)
2. Complete F_S: Gen → Set (2 days)
3. Fix F_R: Gen → CommRing (1 day)

### Step 4: Separate Monoidal Theory (2 days)
1. Move monoidal code to lib/monoidal/
2. Make it generic (not RH-specific)
3. Update imports

### Step 5: Separate Colimit Theory (2 days)
1. Move colimit code to lib/colimits/
2. Make it generic
3. Update imports

### Step 6: Move RH Application Code (3 days)
1. Move all RH-specific code to proofs/riemann/
2. Redefine divisibility, gamma_prime via F_R
3. Move Comp.lean to ComplexExtension.lean
4. Update all imports

### Step 7: Eliminate Circular Axioms (5 days)
1. Audit all axioms
2. Remove circular ones
3. Derive what should be derived
4. Document remaining assumptions

### Step 8: Validation (2 days)
1. Run full test suite
2. Verify GIP compliance
3. Verify non-circularity
4. Update documentation

**TOTAL**: ~3 weeks

---

## Priority Order

1. **CRITICAL**: Remove nat from GenObj (blocks everything)
2. **CRITICAL**: Remove RH morphisms from GenMorphism (circular foundation)
3. **HIGH**: Implement F_T, complete F_S (GIP compliance)
4. **HIGH**: Fix F_R (no bypass to Comp)
5. **HIGH**: Eliminate circular axioms
6. **MEDIUM**: Separate monoidal/colimit theory
7. **MEDIUM**: Move RH code to proofs/
8. **LOW**: Update documentation

---

## Risk Assessment

### Risks of NOT Doing This

- **CRITICAL**: Foundation remains non-compliant with GIP
- **CRITICAL**: Circular axioms undermine proof validity
- **HIGH**: Cannot claim ontological grounding
- **HIGH**: Work cannot be published honestly
- **MEDIUM**: Future work builds on flawed foundation

### Risks of Doing This

- **MEDIUM**: 3 weeks of refactoring delays RH work
- **LOW**: Potential bugs introduced during migration
- **LOW**: Tests temporarily fail during transition

### Risk Mitigation

- Use feature branches for refactoring
- Keep old code until new version validated
- Extensive testing at each step
- Clear rollback plan if issues arise

---

## Success Criteria

✅ **Pure GIP Foundation**:
- GenObj has only ∅, 𝟙
- GenMorphism has only genesis, id, comp
- No RH-specific code in lib/gip/

✅ **Complete Projections**:
- F_T: Gen → Topos implemented
- F_S: Gen → Set completed
- F_R: Gen → CommRing fixed (no bypass)

✅ **Non-Circular**:
- No axioms assuming RH
- Balance derived from coherence
- Clear derivation path

✅ **Clear Architecture**:
- lib/gip/ = pure foundation
- lib/monoidal/ = generic theory
- lib/colimits/ = generic theory
- proofs/riemann/ = RH application

✅ **All Tests Pass**:
- GIP foundation tests pass
- RH proof tests pass (with honest sorries)
- Build succeeds

---

## Conclusion

This audit reveals **fundamental architectural problems** that must be fixed before continuing RH work. The mixing of GIP foundation with RH application has created:
1. Non-compliance with GIP specification
2. Circular axioms in the foundation
3. Missing essential structures
4. Confused separation of concerns

**Recommendation**: STOP current work, execute Phase 0 refactoring (3 weeks), THEN resume RH proof with clean foundation.

---

**Status**: AUDIT COMPLETE
**Next Action**: Begin Phase 0.1 refactoring
**Timeline**: 3 weeks to clean foundation
