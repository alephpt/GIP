# Phase 0 Migration Script - GIP Purification

**Date**: 2025-11-17
**Status**: IN PROGRESS
**Goal**: Replace contaminated GIP foundation with pure version

---

## Migration Strategy

### Step 1: Backup and Prepare (DONE)
- ✅ Backed up contaminated files to `archive/phase0_backup/`
- ✅ Created pure versions: `Basic.lean.new`, `Morphisms.lean.new`
- ✅ Created `proofs/riemann/ArithmeticExtensions.lean` for RH morphisms

### Step 2: Identify Dependent Files (IN PROGRESS)

Files that reference contaminated structures:
- `GenObj.nat` usage
- `instantiation` morphism usage
- `divisibility` morphism usage
- `gamma` (prime) morphism usage

### Step 3: Migration Plan

**3.1: Update lib/gip/ modules**
These should import pure GIP and work unchanged:
- ✅ `Register0.lean` - only uses ∅
- ✅ `Register1.lean` - only uses ∅, 𝟙, γ
- ⚠️ `Register2.lean` - DELETE (numbers not in Gen)
- ⚠️ `Projection.lean` - UPDATE to use pure Gen

**3.2: Update lib/gip/Projections/**
- ✅ `Topos.lean` - IMPLEMENT (missing)
- ⚠️ `Set.lean` - UPDATE to pure Gen (remove nat cases)
- ⚠️ `Ring.lean` - UPDATE to pure Gen (remove nat cases)
- ⚠️ `Comp.lean` - MOVE to proofs/riemann/

**3.3: Move to proofs/riemann/**
All files using arithmetic structure:
- Any N_all construction
- Any ζ_gen definitions
- Any equilibria code
- Any balance conditions using numeric structure
- Any Euler product code

**3.4: Update test/**
Test files need to either:
- Test pure GIP (keep in test/gip/)
- Test RH application (move to test/riemann/)

### Step 4: Execute Swap

```bash
# Swap in pure GIP
mv lib/gip/Gip/Basic.lean lib/gip/Gip/Basic.lean.old
mv lib/gip/Gip/Morphisms.lean lib/gip/Gip/Morphisms.lean.old
mv lib/gip/Gip/Basic.lean.new lib/gip/Gip/Basic.lean
mv lib/gip/Gip/Morphisms.lean.new lib/gip/Gip/Morphisms.lean
```

### Step 5: Fix Imports

**Every file that had**:
```lean
-- OLD (contaminated)
match obj with
| .nat n => ...
```

**Needs to become**:
```lean
-- NEW (pure or moved to RH)
-- Either remove nat case, or move file to proofs/riemann/
```

### Step 6: Build and Fix

Iteratively:
1. Try to build: `lake build Gip`
2. Fix compilation errors
3. Move RH-specific code to proofs/riemann/
4. Repeat until clean build

---

## Files Requiring Migration

### Category 1: Pure GIP (KEEP, FIX)
- `lib/gip/Gip/Register0.lean` ✅
- `lib/gip/Gip/Register1.lean` ✅
- `lib/gip/Gip/ModalTopology/*.lean` ✅
- `lib/gip/Gip/CategoryLaws.lean` - check for nat usage

### Category 2: Projections (FIX)
- `lib/gip/Gip/Projections/Topos.lean` - IMPLEMENT
- `lib/gip/Gip/Projections/Set.lean` - REMOVE nat cases
- `lib/gip/Gip/Projections/Ring.lean` - REMOVE nat cases, fix to target CommRing

### Category 3: RH Application (MOVE)
- `lib/gip/Gip/Projections/Comp.lean` → `proofs/riemann/ComplexExtension.lean`
- Any `N_all` code → `proofs/riemann/NAllConstruction.lean`
- Any `ζ_gen` code → `proofs/riemann/ZetaMorphism.lean`
- Any equilibria code → `proofs/riemann/Equilibria.lean`
- Any balance code using numbers → `proofs/riemann/BalanceCondition.lean`

### Category 4: Tests (SPLIT)
Keep pure GIP tests in `test/gip/`
Move RH tests to `test/riemann/`

---

## Compilation Strategy

### Phase A: Core GIP (Pure)
Goal: Get `lake build Gip.Basic Gip.Morphisms` working
- Should be EASY - only ∅, 𝟙, γ

### Phase B: Projections
Goal: Get `lake build Gip.Projections` working
- Implement F_T (new)
- Fix F_S (remove nat)
- Fix F_R (remove nat, target CommRing)

### Phase C: RH Application
Goal: Get `lake build Riemann` working
- All moved RH code builds
- Uses pure GIP + projections
- Clear separation maintained

---

## Success Criteria

✅ **Pure GIP builds**:
- `Gip.Basic` - only ∅, 𝟙
- `Gip.Morphisms` - only γ, id, comp
- Zero build errors

✅ **Projections complete**:
- F_T: Gen → Topos implemented
- F_S: Gen → Set complete (no nat)
- F_R: Gen → CommRing fixed (no bypass)

✅ **Clean separation**:
- lib/gip/ has NO RH code
- proofs/riemann/ has ALL RH code
- Clear boundary

✅ **Tests pass**:
- GIP foundation tests pass
- RH application tests pass
- Integration tests pass

---

## Current Status

- ✅ Pure files created
- ✅ Backup completed
- ✅ ArithmeticExtensions.lean created
- 🔄 Identifying dependent files
- ⏳ Swap execution
- ⏳ Import fixes
- ⏳ Build validation

---

## Next Actions

1. Complete dependent file analysis
2. Create detailed file-by-file migration plan
3. Execute swap
4. Fix imports iteratively
5. Build and validate

**Estimated Time**: 3-5 days for initial swap and fixes, 1-2 weeks for full validation
