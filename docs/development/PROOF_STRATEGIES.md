# Lean 4 Proof Strategies for Gen Category

## Executive Summary

This document provides targeted proof strategies for completing the 27 theorems in our Gen category implementation. Our proofs require handling an inductive `GenMorphism` type with composition baked in, proving uniqueness of morphisms from initial objects, and establishing categorical laws. The key challenge is working with our custom inductive structure rather than Mathlib's abstract category framework.

### Key Insights for Lean Proof Development

1. **Pattern Matching on Inductive Types**: Since `GenMorphism` is inductive, most proofs will use pattern matching or `cases` analysis
2. **Uniqueness via Contradiction**: For proving morphism uniqueness, show any two morphisms must be equal by exhaustive case analysis
3. **Definitional Equality**: Simple structural recursion yields equations provable by `rfl`
4. **Initial Object Property**: The empty object ∅ has exactly one morphism to any object - use this for uniqueness proofs
5. **Composition Elimination**: When proving composition properties, unfold the `comp` constructor and analyze the components

---

## Tactic Reference

### Essential Tactics for Our Proofs

| Tactic | Purpose | Usage in Gen Category |
|--------|---------|----------------------|
| **`intro`/`intros`** | Introduce hypotheses | Start most theorem proofs |
| **`cases`** | Case analysis on inductives | Analyze `GenObj` and `GenMorphism` |
| **`use`** | Provide witness for ∃ | Specify unique morphisms |
| **`constructor`** | Build conjunctions/exists | Prove `∃!` goals |
| **`rfl`** | Reflexivity | Identity and definitional equalities |
| **`exact`** | Provide exact proof term | When we know the specific morphism |
| **`apply`** | Apply theorem/hypothesis | Use previously proven lemmas |
| **`have`** | Intermediate lemmas | Break complex proofs into steps |
| **`sorry`** | Stub proof | Development placeholder |
| **`by_cases`** | Case split on decidable | For divisibility conditions |
| **`simp`** | Simplification | Normalize expressions |
| **`match`/`with` | Pattern matching | Alternative to cases |

### Tactics for Uniqueness (∃!)

For proving `∃! (f : GenMorphism X Y), P f`:

```lean
-- Step 1: Provide the witness
use specific_morphism
-- Step 2: Prove existence and uniqueness
constructor
· -- Prove P holds for the witness
  exact proof_of_P
· -- Prove uniqueness: any other morphism with P equals our witness
  intro g hg
  -- Prove g = specific_morphism
```

---

## Proof Patterns

### Pattern 1: Proving Initial Object Property

```lean
theorem empty_is_initial :
  ∀ (X : GenObj), ∃! (f : GenMorphism ∅ X), True := by
  intro X
  cases X with
  | empty =>
    use GenMorphism.id_empty
    constructor
    · trivial
    · intro f _
      -- Key: only one endomorphism on ∅
      -- Analyze f by cases - must be id_empty
  | unit =>
    use GenMorphism.genesis
    constructor
    · trivial
    · intro f _
      -- Key: genesis is defined as THE morphism ∅ → 𝟙
  | nat n =>
    use GenMorphism.comp GenMorphism.genesis (GenMorphism.instantiation n)
    constructor
    · trivial
    · intro f _
      -- Key: all morphisms ∅ → n factor through 𝟙
```

### Pattern 2: Proving Identity Laws

```lean
theorem left_identity {X Y : GenObj} (f : GenMorphism X Y) :
  (idMorph Y) ∘ f = f := by
  -- Approach: Pattern match on f
  -- For base morphisms (id, genesis, instantiation, divisibility): direct
  -- For composed morphisms: use induction hypothesis
  cases f with
  | id_empty => rfl
  | id_unit => rfl
  | id_nat n => rfl
  | genesis => rfl
  | instantiation n => rfl
  | divisibility n m h => rfl
  | comp g h =>
    -- Need to show: id ∘ (h ∘ g) = h ∘ g
    rfl  -- Should reduce definitionally
```

### Pattern 3: Proving Morphism Uniqueness

```lean
theorem empty_endomorphism_trivial :
  ∀ (f : GenMorphism ∅ ∅), f = GenMorphism.id_empty := by
  intro f
  -- Key insight: By initial property, at most one morphism exists
  -- Since id_empty exists, f must equal it
  cases f with
  | id_empty => rfl
  | comp g h =>
    -- Show this reduces to id_empty
    -- Both g and h : ∅ → ∅, so by IH both are id_empty
    sorry -- Need to set up proper induction
  -- No other constructors produce ∅ → ∅ morphisms
```

---

## Priority 1 Proofs: Detailed Strategies

### 1. `empty_is_initial` (Register0.lean)

**Strategy**: Case analysis on target object X
- **Case ∅**: Use `id_empty`, prove uniqueness by analyzing morphism structure
- **Case 𝟙**: Use `genesis`, prove uniqueness by construction definition
- **Case n**: Use `ι n ∘ γ`, prove uniqueness via factorization

**Key Tactic Sequence**:
```lean
intro X
cases X with
| empty => use GenMorphism.id_empty; constructor; trivial; [uniqueness proof]
| unit => use GenMorphism.genesis; constructor; trivial; [uniqueness proof]
| nat n => use (ι n) ∘ γ; constructor; trivial; [uniqueness proof]
```

### 2. `empty_endomorphism_trivial` (Register0.lean)

**Strategy**: Induction on morphism structure
- Only `id_empty` and compositions of `id_empty` can be endomorphisms on ∅
- Show any composition reduces to `id_empty`

**Key Insight**: This follows from `empty_is_initial` - specialize to X = ∅

### 3. `genesis_unique` (Register1.lean)

**Strategy**: Direct from initial property
- Apply `empty_is_initial` with X = 𝟙
- Extract uniqueness part

**Key Tactic**:
```lean
intro f
have h := empty_is_initial 𝟙
-- Extract that f = γ from uniqueness
```

### 4. `left_identity` and `right_identity` (CategoryAxioms.lean)

**Strategy**: Pattern matching on morphism constructors
- Base cases (non-comp constructors): Should be `rfl`
- Composition case: May need auxiliary lemma about identity absorption

**Potential Challenge**: The `comp` constructor might not reduce automatically. May need:
```lean
@[simp] lemma id_comp_reduce {X Y : GenObj} (f : GenMorphism X Y) :
  GenMorphism.comp (idMorph Y) f = f := by
  -- Define by pattern matching
```

---

## Priority 2 Proofs: Strategies

### 5. `critical_identity`: φ_{n,m} ∘ ι_n = ι_m when n | m

**Strategy**: Use uniqueness of morphisms from 𝟙
- Both sides have type `GenMorphism 𝟙 (GenObj.nat m)`
- By `unique_morphism_from_unit`, there's only one such morphism: `ι m`
- Therefore both sides equal `ι m`

**Key Proof Structure**:
```lean
theorem critical_identity (n m : ℕ) (h : n ∣ m) :
  φ[n, m] h ∘ ι n = ι m := by
  -- Both sides : GenMorphism 𝟙 (GenObj.nat m)
  have unique := Register1.unique_morphism_to_nat m
  -- Apply to LHS
  have lhs_eq : φ[n, m] h ∘ ι n = ι m := unique _
  exact lhs_eq
```

### 6. `universal_factorization` (Register1.lean)

**Strategy**: Use initial object property
- Any morphism ∅ → n must factor through the unique ∅ → 𝟙 (which is γ)
- Then compose with unique 𝟙 → n (which is ι_n)

---

## Resources

### Lean 4 Documentation
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)
- [Induction and Recursion](https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

### Mathlib4 Category Theory
- [CategoryTheory.Category.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html)
- [CategoryTheory.Limits.Shapes.Terminal](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Terminal.html)
- Note: We're not using Mathlib's framework directly, but concepts are similar

### Relevant Examples
- Initial objects in Mathlib use `IsInitial` predicate
- Terminal objects use `IsTerminal` predicate
- Uniqueness often proven via `Subsingleton` typeclass

---

## Recommended Proof Order

### Phase 1: Foundational (Week 1)
1. **`empty_endomorphism_trivial`** - Simplest uniqueness proof
2. **`genesis_unique`** - Direct application of initial property
3. **`left_identity`** - Pattern matching on morphisms
4. **`right_identity`** - Similar to left_identity

### Phase 2: Initial Object Properties (Week 1-2)
5. **`empty_is_initial`** - Core theorem, enables others
6. **`no_morphisms_to_empty`** - Follows from initial property
7. **`no_morphism_unit_to_empty`** - Consequence of above

### Phase 3: Register 1 Theorems (Week 2)
8. **`unique_morphism_to_nat`** - Key for Register 2
9. **`unit_endomorphism_trivial`** - Similar pattern to empty
10. **`instantiation_exists_unique`** - Existence and uniqueness
11. **`universal_factorization`** - Important composition property

### Phase 4: Register 2 and Composition (Week 2-3)
12. **`critical_identity`** - Crucial for category structure
13. **`divisibility_morphism_unique`** - When n | m
14. **`divisibility_composition`** - Transitivity of divisibility
15. **`associativity`** - May require 16 cases

### Phase 5: Completeness (Week 3)
16. Remaining Register 2 theorems
17. Helper lemmas as needed
18. Final verification of `gen_is_category`

---

## Time Estimates

### Priority 1 Theorems (Essential)
| Theorem | Estimated Time | Difficulty | Prerequisites |
|---------|---------------|------------|--------------|
| `empty_endomorphism_trivial` | 1-2 hours | Easy | Understanding inductive types |
| `genesis_unique` | 1 hour | Easy | `empty_is_initial` |
| `left_identity` | 2-3 hours | Medium | Pattern matching skills |
| `right_identity` | 2-3 hours | Medium | Similar to left_identity |
| `empty_is_initial` | 3-4 hours | Hard | Core theorem, needs careful cases |

### Priority 2 Theorems (Important)
| Theorem | Estimated Time | Difficulty | Prerequisites |
|---------|---------------|------------|--------------|
| `critical_identity` | 2-3 hours | Medium | Uniqueness from 𝟙 |
| `universal_factorization` | 2-3 hours | Medium | Initial property |
| `divisibility_morphism_unique` | 3-4 hours | Hard | Morphism analysis |
| `associativity` | 4-6 hours | Hard | Many cases (16 enumerated) |

### Total Estimated Time
- **Priority 1**: 10-15 hours
- **Priority 2**: 12-16 hours
- **All 27 theorems**: 40-60 hours

### Factors Affecting Time
- **Positive**: Many theorems follow similar patterns
- **Negative**: Custom inductive type may not play well with automation
- **Unknown**: How well Lean's definitional reduction handles our `comp` constructor

---

## Potential Blockers and Challenges

### 1. Inductive Type Complexity
**Challenge**: Our `GenMorphism` has `comp` as a constructor, not a defined function
**Mitigation**: May need custom simp lemmas for composition reduction

### 2. Definitional vs Propositional Equality
**Challenge**: Some equations may not be definitional (rfl won't work)
**Mitigation**: Prove custom reduction lemmas, use `simp` with these lemmas

### 3. Termination Checking
**Challenge**: Recursive proofs on `comp` constructor need termination
**Mitigation**: Use well-founded recursion or structural induction carefully

### 4. Universe Levels
**Challenge**: Mixing `Type` and `Prop` can cause universe issues
**Mitigation**: Be explicit about universe levels when needed

### 5. Missing Automation
**Challenge**: Not using Mathlib's category theory automation
**Mitigation**: Build our own simp lemmas and tactics as needed

### 6. Composition Associativity
**Challenge**: 16 cases to verify (as enumerated in axioms file)
**Mitigation**: Try to find pattern that reduces cases, or use systematic case analysis

---

## Next Steps

1. **Start with `empty_endomorphism_trivial`** - Simplest uniqueness proof
2. **Build helper lemmas** as needed for composition reduction
3. **Test pattern matching** on our inductive type early
4. **Document successful patterns** for reuse across similar theorems
5. **Consider automation** if manual proofs become repetitive

## Success Metrics

- ✅ All `sorry` placeholders replaced with actual proofs
- ✅ Lean accepts all proofs without errors
- ✅ Proofs are reasonably concise (avoid excessive verbosity)
- ✅ Critical theorems (`empty_is_initial`, `critical_identity`) are bulletproof
- ✅ `gen_is_category` theorem validates our construction