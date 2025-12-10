# Pre-Implementation Decisions

## Version: 1.0
## Date: 2024-12-10
## Status: Requirements Addressed

---

## Requirement 1: Formalize information_loss Axiom ✓

### Decision: Axiomatized Information Loss

**Implementation:**
- Added formal axioms in `Gip/Foundations.lean` (lines 295-299):
  - `noncomputable axiom information_loss_empty : Hom 𝕟 𝕟`
  - `noncomputable axiom information_loss_infinite : Hom 𝕟 𝕟`
- Added documentation explaining semantic meaning (lines 279-293)
- Added theorem `information_loss_principle` stating when information loss occurs
- Updated composition function to use axioms instead of `sorry` (lines 407-409)
- Updated `CategoryInstance.lean` to reference axioms in comments

**Rationale:**
- Axioms formalize the intentional undefined behavior
- Makes semantic intent explicit in the type system
- Preserves existing build without breaking changes
- Documents the principle of identity dissolution through forgetful aspects

**Verification:**
- Build passes with 1927 jobs successful
- Intentional `sorry` remains in CategoryInstance for associativity proof
- No type errors or compilation failures

---

## Requirement 2: Archive Files Decision ✓

### Decision: Leave Archive Untouched (Historical Snapshots)

**Archive Analysis:**
1. **pre-migration-20251201-172806/** (37 files, 148 ProtoIdentity occurrences)
   - Contains complete snapshot from December 1, 2024 migration
   - Files are exact copies before migration
   - Purpose: Historical record for rollback if needed

2. **2025-11-24-foundations-refactor/** (1 file, 13 occurrences)
   - Contains old GrandUnifiedProof before refactor
   - Purpose: Reference for before/after comparison

3. **2025-11-19-cleanup/** and **2025-11-19-doc-consolidation/**
   - Earlier snapshots from November cleanup
   - Purpose: Historical progression tracking

**Rationale:**
- Archives are historical snapshots, not active code
- They serve as backup/reference material
- Updating them would defeat their purpose
- They don't participate in builds or imports
- Standard practice: archives remain unchanged

**Action:** No changes to archive/ directory files

---

## Requirement 3: Omega Strategy Clarification ✓

### Decision: Option A - Extend Existing Definition

**Current State Analysis:**
- `ToposStructure.lean` defines: `def Ω : Obj := 𝕟` (line 231)
- Ω already serves as subobject classifier
- Truth morphisms: `truth_empty : ∅ → Ω` and `truth_inf : ∞ → Ω`
- Theorems establish Ω characterizes ProtoIdentity passage

**Proposed Strategy:**

### Phase 1: Document Current Semantics (Non-Breaking)
```lean
/-- The subobject classifier for GIP is the identity object

    Ω = n represents the manifestation space where all possible
    identities exist as standing waves between ∅ and ∞.

    The truth morphisms (Gen: ∅ → n, Res: ∞ → n) show how
    identities emerge through ProtoIdentity convergence.
-/
def Ω : Obj := 𝕟
```

### Phase 2: Add Manifestation Theorems (After Phi Rename)
```lean
/-- Act/Ω represents the manifestation space of all possible n -/
theorem act_omega_is_manifestation :
  ∀ (phi : Phi), ∃ (n : Ω),
    Act phi = (n_to_empty ⊕ n_to_infinite) :=
by sorry -- Implementation after Phi rename

/-- Each n in Ω is a standing wave between aspects -/
theorem omega_standing_wave :
  ∀ (n : Ω), ∃ (wave : StandingWave),
    wave.source = ∅ ∧ wave.sink = ∞ ∧ wave.node = n :=
by sorry -- Implementation after standing wave formalization
```

**Rationale for Option A:**
1. **Minimal disruption**: Extends rather than replaces
2. **Preserves existing proofs**: All current theorems remain valid
3. **Semantic clarity**: Documents that Ω already represents manifestation
4. **Progressive enhancement**: Can add theorems incrementally
5. **Type safety**: No breaking changes to existing code

**Why not Option B (New Type)?**
- Would require parallel structure
- Confusing to have two "omega" concepts
- Breaks existing theorems

**Why not Option C (Type Alias)?**
- Ω already is effectively an alias for n
- Additional aliasing adds no value

---

## Summary of Decisions

1. **Information Loss**: Formalized as axioms ✓
   - Implementation complete
   - Build verified

2. **Archive Files**: Leave untouched ✓
   - Historical snapshots
   - No updates needed

3. **Omega Strategy**: Extend existing definition ✓
   - Document current semantics now
   - Add manifestation theorems after Phi rename
   - Minimal, non-breaking approach

## Next Steps

With these pre-implementation requirements addressed:

1. **Immediate**: Update REFACTORING_SPEC.md with these decisions
2. **Phase 1**: Proceed with ProtoIdentity → Phi rename (159 occurrences)
3. **Phase 2**: Add Omega manifestation documentation
4. **Phase 3**: Implement standing wave theorems
5. **Phase 4**: Complete refactoring per spec

## Build Verification

```
Build Status: ✓ 1927 jobs successful
Warnings: 1 (intentional sorry in CategoryInstance)
Errors: 0
```

All pre-implementation requirements have been successfully addressed.