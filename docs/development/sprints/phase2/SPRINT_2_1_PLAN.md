# Sprint 2.1 Plan: Multiplicative Structure & Euler Product

**Date**: 2025-11-12
**Duration**: 21 days (3 weeks)
**Phase**: 2 - Explicit ζ_gen Construction
**Goal**: Define monoidal structure on N_all and construct partial Euler products
**Status**: Ready to Execute

---

## Executive Summary

**Phase 1 Achievement**: 40/44 proofs completed, all foundational infrastructure proven
**Phase 2 Goal**: Construct ζ_gen explicitly via categorical Euler product
**Sprint 2.1 Mission**: Establish multiplicative structure and partial Euler products as foundation for full ζ_gen construction

### Sprint Context

**What Phase 1 Gave Us**:
- ✅ N_all colimit structure fully proven
- ✅ Prime characterization and generation theorems
- ✅ Axiomatic ζ_gen definition (ZG1-ZG4)
- ✅ Equilibrium theory framework
- ✅ Balance condition established

**What Sprint 2.1 Will Add**:
- ⊗ Monoidal (tensor) structure on N_all
- ζ_S partial Euler products for finite prime sets
- Colimit construction: ζ_gen = colim_S ζ_S
- Foundation for proving ZG1-ZG4 from explicit construction

**Why This Matters**:
Currently ζ_gen is axiomatic. Sprint 2.1 begins the explicit construction that will:
1. Prove the axioms ZG1-ZG4 are satisfied (not just assumed)
2. Enable computation of actual ζ_gen values
3. Support equilibrium point discovery
4. Validate the Euler product formula categorically

---

## 1. Technical Requirements

### 1.1 Monoidal Structure on N_all

**Goal**: Define tensor product ⊗: N_all × N_all → N_all making N_all a monoidal object

**Mathematical Foundation** (from research doc §3.3):
- Classical: Euler product ∏_p (1 - p^(-s))^(-1) is multiplication of functions
- Categorical: Need monoidal structure to express "product" of morphisms
- Approach: Use LCM (least common multiple) for the tensor operation

**Key Definitions**:

```lean
/-- Tensor product on N_all using LCM structure -/
def tensor : NAllObj → NAllObj → NAllObj

notation:50 a " ⊗ " b => tensor a b
```

**Required Properties**:
1. **Associativity**: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
2. **Unit**: ∃ I, (I ⊗ a = a) ∧ (a ⊗ I = a)
3. **Coherence**: Pentagon and triangle diagrams commute

**Connection to Classical Multiplication**:
- For ψ_n, ψ_m where gcd(n,m) = 1: ψ_n ⊗ ψ_m = ψ_{nm}
- General case uses LCM: ψ_n ⊗ ψ_m = ψ_{lcm(n,m)}
- Preserves divisibility structure

**Theorems** (~15 total):
```lean
theorem tensor_associative (a b c : NAllObj) :
  (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)

theorem tensor_unit_left (a : NAllObj) :
  unit_tensor ⊗ a = a

theorem tensor_unit_right (a : NAllObj) :
  a ⊗ unit_tensor = a

theorem tensor_commutative (a b : NAllObj) :
  a ⊗ b = b ⊗ a

theorem tensor_respects_inclusions (n m : ℕ) :
  include n x ⊗ include m y = include (lcm n m) (...)

-- Coherence conditions
theorem pentagon_coherence (a b c d : NAllObj) : ...
theorem triangle_coherence (a b : NAllObj) : ...

-- Connection to multiplication
theorem tensor_coprime_is_product (n m : ℕ) (h : gcd n m = 1) :
  include n x ⊗ include m y = include (n * m) (...)
```

**File**: `Gen/MonoidalStructure.lean` (~350 lines, ~15 theorems)

---

### 1.2 Partial Euler Products

**Goal**: For finite prime set S, define ζ_S = ∏_{p ∈ S} (1 - p^(-s))^(-1) as endomorphism

**Mathematical Foundation** (from research doc §3.4):

The classical Euler product:
```
ζ(s) = ∏_p (1 - p^(-s))^(-1)
     = ∏_p (1 + p^(-s) + p^(-2s) + ...)
```

Categorical translation:
- Each factor (1 - p^(-s))^(-1) becomes a local endomorphism at prime p
- Finite product over S = {p₁, ..., pₙ} is well-defined via ⊗
- Infinite product is colimit over finite sets

**Key Definitions**:

```lean
/-- Finite set of primes -/
def FinitePrimeSet := {S : Finset ℕ // ∀ p ∈ S, Nat.Prime p}

/-- Local Euler factor at prime p: (1 - p^(-s))^(-1) -/
def local_euler_factor (p : ℕ) (h : Nat.Prime p) : NAllObj → NAllObj

/-- Partial Euler product for finite prime set S -/
def euler_product_S (S : FinitePrimeSet) : NAllObj → NAllObj :=
  S.val.fold (⊗) unit_tensor (fun p => local_euler_factor p ...)
```

**Required Properties**:
1. **Well-defined**: ζ_S is an actual endomorphism
2. **Geometric series**: ζ_S(ψ_n) expands as geometric series in primes from S
3. **Factorization**: S₁ ⊆ S₂ implies ζ_S₂ factors through ζ_S₁
4. **Multiplication formula**: ζ_S respects coprime factorization

**Theorems** (~18 total):
```lean
theorem local_factor_is_endomorphism (p : ℕ) (h : Nat.Prime p) :
  is_endomorphism (local_euler_factor p h)

theorem euler_product_S_well_defined (S : FinitePrimeSet) :
  is_endomorphism (euler_product_S S)

theorem geometric_series_expansion (S : FinitePrimeSet) (n : ℕ) :
  euler_product_S S (include n x) =
    Σ_{d | gcd(n, ∏S) = d} include d (...)

theorem factorization_through_subset
    (S₁ S₂ : FinitePrimeSet) (h : S₁.val ⊆ S₂.val) :
  ∃ φ, euler_product_S₂ = φ ∘ euler_product_S₁

theorem euler_product_multiplicative (S : FinitePrimeSet) (n m : ℕ)
    (h_coprime : gcd n m = 1)
    (h_support : ∀ p ∈ S.val, (p ∣ n ∨ p ∣ m) → p ∈ S.val) :
  euler_product_S S (ψ_n ⊗ ψ_m) =
    euler_product_S S (ψ_n) ⊗ euler_product_S S (ψ_m)
```

**File**: `Gen/PartialEulerProducts.lean` (~400 lines, ~18 theorems)

---

### 1.3 Colimit Construction of ζ_gen

**Goal**: Prove ζ_gen = colim_S ζ_S as S ranges over all finite prime sets

**Mathematical Foundation** (from research doc §3.4):

Category-theoretic approach to infinite products:
- **Diagram**: FinitePrimeSet ordered by inclusion forms directed system
- **Functor**: P: FinitePrimeSet → End(N_all) sending S ↦ ζ_S
- **Colimit**: ζ_gen is the colimit (categorical limit) of this diagram
- **Universal Property**: For any f: N_all → N_all compatible with all ζ_S, there exists unique φ: ζ_gen → f

**Key Definitions**:

```lean
/-- Category of finite prime sets with inclusions as morphisms -/
def FinitePrimeSetsCategory : CategoryTheory.Category FinitePrimeSet

/-- Diagram of partial Euler products -/
def euler_product_diagram :
  FinitePrimeSetsCategory ⥤ (NAllObj → NAllObj)

/-- The cocone structure -/
def euler_product_cocone :
  CategoryTheory.Limits.Cocone euler_product_diagram

/-- ζ_gen as the colimit -/
def zeta_gen_from_colimit : NAllObj → NAllObj :=
  euler_product_cocone.pt
```

**Required Properties**:
1. **Diagram**: P(S) is a functor (preserves inclusions)
2. **Cocone**: {ζ_S → ζ_gen} is a cocone (compatibility)
3. **Universal**: For compatible family {f_S}, unique f: ζ_gen → X exists

**Theorems** (~12 total):
```lean
theorem euler_diagram_is_functor :
  CategoryTheory.Functor euler_product_diagram

theorem euler_cocone_is_cocone :
  CategoryTheory.Limits.IsCocone euler_product_cocone

theorem euler_colimit_universal_property :
  CategoryTheory.Limits.IsColimit euler_product_cocone

theorem zeta_gen_equals_colimit :
  ZetaMorphism.ζ_gen = zeta_gen_from_colimit

-- Connection to axioms
theorem colimit_satisfies_ZG1 :
  -- Multiplicativity follows from construction
  is_multiplicative zeta_gen_from_colimit

theorem colimit_satisfies_ZG2 :
  -- Prime determination follows from Euler factors
  determined_by_primes zeta_gen_from_colimit

-- Computation
theorem compute_zeta_via_limit (x : NAllObj) :
  zeta_gen_from_colimit x =
    limit_{S → all primes} (euler_product_S S x)
```

**File**: `Gen/EulerProductColimit.lean` (~300 lines, ~12 theorems)

---

## 2. Proof Strategy

### Week 1: Monoidal Structure (Days 1-7)

#### Days 1-2: Tensor Product Definition (12 hours)

**Goal**: Define ⊗ and prove basic properties

**Tasks**:
1. **Define tensor operation** (3 hours)
   ```lean
   /-- Tensor via LCM on underlying naturals -/
   def tensor (a b : NAllObj) : NAllObj :=
     match a, b with
     | Nall.mk, Nall.mk => Nall.mk  -- Will need refinement
   ```

   **Challenge**: Current Nall has single constructor
   **Solution**: Either:
   - Option A: Extend Nall to carry origin information
   - Option B: Define tensor via universal property + compatibility

   **Decision**: Use Option B (universal property approach)

2. **Prove tensor respects inclusions** (4 hours)
   - Show: include n x ⊗ include m y factors correctly
   - Use: Colimit universal property
   - Prove: Compatibility with divisibility morphisms

3. **Prove commutativity** (3 hours)
   - LCM is commutative: lcm(n,m) = lcm(m,n)
   - Follows from symmetry of definition

4. **Initial testing** (2 hours)
   - Verify tensor type-checks on examples
   - Test: ψ_2 ⊗ ψ_3 = ψ_6
   - Test: ψ_4 ⊗ ψ_6 = ψ_{12}

**Milestone**: Tensor defined and computable

---

#### Days 3-4: Associativity Proof (16 hours)

**Goal**: Prove (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)

**Mathematical Core**:
- LCM associativity: lcm(lcm(n,m),k) = lcm(n,lcm(m,k))
- Extends to all of N_all via colimit

**Proof Strategy**:
```lean
theorem tensor_associative (a b c : NAllObj) :
  (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c) := by
  -- Case analysis on a, b, c from colimit
  obtain ⟨n, x, ha⟩ := nall_from_colimit a
  obtain ⟨m, y, hb⟩ := nall_from_colimit b
  obtain ⟨k, z, hc⟩ := nall_from_colimit c

  -- Rewrite using inclusions
  rw [ha, hb, hc]

  -- Now prove for inclusions
  unfold tensor

  -- Key step: lcm(lcm(n,m),k) = lcm(n,lcm(m,k))
  have h_lcm : Nat.lcm (Nat.lcm n m) k = Nat.lcm n (Nat.lcm m k) :=
    Nat.lcm_assoc n m k

  -- Apply to inclusions
  ...
```

**Challenges**:
1. Need colimit elements to factor through inclusions
2. LCM associativity in Mathlib (may need to prove)
3. Compatibility with colimit structure

**Time Allocation**:
- Day 3: Setup and key lemmas (8 hours)
- Day 4: Main proof and edge cases (8 hours)

**Milestone**: Associativity proven

---

#### Days 5-6: Unit Laws and Coherence (14 hours)

**Goal**: Prove unit laws and coherence diagrams

**Tasks**:

1. **Define unit element** (2 hours)
   ```lean
   /-- Unit for tensor is ψ_1 (the number 1) -/
   def unit_tensor : NAllObj := include 1 GenObj.nat.mk
   ```

2. **Prove left unit law** (4 hours)
   ```lean
   theorem tensor_unit_left (a : NAllObj) :
     unit_tensor ⊗ a = a := by
     obtain ⟨n, x, ha⟩ := nall_from_colimit a
     rw [ha]
     unfold tensor unit_tensor
     -- lcm(1, n) = n
     have : Nat.lcm 1 n = n := Nat.lcm_one_left n
     ...
   ```

3. **Prove right unit law** (4 hours)
   - Similar to left unit
   - Use: lcm(n, 1) = n

4. **Pentagon coherence** (4 hours)
   ```lean
   theorem pentagon_coherence (a b c d : NAllObj) :
     ((a ⊗ b) ⊗ c) ⊗ d = a ⊗ (b ⊗ (c ⊗ d))
   ```
   - Follows from iterated associativity
   - Diagram:
   ```
       ((a⊗b)⊗c)⊗d -----> (a⊗b)⊗(c⊗d)
           |                    |
           v                    v
       (a⊗(b⊗c))⊗d -----> a⊗((b⊗c)⊗d)
                   \      /
                    v    v
                 a⊗(b⊗(c⊗d))
   ```

**Milestone**: Monoidal structure complete

---

#### Day 7: Connection to Multiplication (6 hours)

**Goal**: Prove tensor equals classical multiplication for coprime elements

**Theorem**:
```lean
theorem tensor_coprime_is_product (n m : ℕ)
    (h : Nat.gcd n m = 1)
    (x : GenObj.nat n) (y : GenObj.nat m) :
  include n x ⊗ include m y = include (n * m) (...) := by
  unfold tensor
  -- When gcd(n,m) = 1, lcm(n,m) = n * m
  have h_lcm : Nat.lcm n m = n * m := Nat.lcm_eq_mul_of_coprime h
  rw [h_lcm]
  ...
```

**Testing**:
- Test coprime pairs: (2,3), (5,7), (11,13)
- Test non-coprime: (4,6) gives lcm=12, not product=24
- Verify commutativity preserved

**Deliverable**: `Gen/MonoidalStructure.lean` complete

**Week 1 Summary**:
- ✅ Tensor product defined
- ✅ Associativity proven
- ✅ Unit laws proven
- ✅ Coherence verified
- ✅ Connection to multiplication established

---

### Week 2: Partial Euler Products (Days 8-14)

#### Days 8-9: Local Euler Factors (14 hours)

**Goal**: Define (1 - p^(-s))^(-1) categorically as endomorphism

**Mathematical Background**:
```
(1 - p^(-s))^(-1) = 1 + p^(-s) + p^(-2s) + p^(-3s) + ...
                  = Σ_{k=0}^∞ p^(-ks)
```

Categorical interpretation:
- Acts on ψ_n by "adding all p-divisibilities"
- If p ∤ n: local_factor_p(ψ_n) = ψ_n
- If p^k || n: local_factor_p(ψ_n) = ψ_n ⊗ ψ_p ⊗ ... (geometric sum)

**Definition**:
```lean
/-- Local Euler factor at prime p -/
def local_euler_factor (p : ℕ) (h : Nat.Prime p) : NAllObj → NAllObj :=
  fun x =>
    -- Compute p-adic valuation of x
    let v_p := p_adic_valuation p x
    -- Sum: x ⊗ (1 ⊗ ψ_p ⊗ ψ_{p²} ⊗ ... ⊗ ψ_{p^{∞}})
    geometric_sum_at_p p v_p x
```

**Tasks**:

1. **Define p-adic valuation** (4 hours)
   ```lean
   /-- p-adic valuation: highest power of p dividing n -/
   def p_adic_valuation (p : ℕ) (x : NAllObj) : ℕ :=
     match x with
     | include n y =>
       -- Find k such that p^k || n
       Nat.padicValNat p n
   ```

2. **Define geometric sum** (6 hours)
   ```lean
   /-- Geometric sum 1 + p + p² + ... up to p^v -/
   def geometric_sum_at_p (p v : ℕ) (x : NAllObj) : NAllObj :=
     List.foldl (⊗) x [ψ_p, ψ_{p²}, ..., ψ_{p^v}]
   ```

3. **Prove endomorphism property** (4 hours)
   ```lean
   theorem local_factor_is_endomorphism (p : ℕ) (h : Nat.Prime p) :
     is_endomorphism (local_euler_factor p h)
   ```

**Milestone**: Local factors defined

---

#### Days 10-11: Partial Products ζ_S (14 hours)

**Goal**: Combine local factors into finite products

**Definition**:
```lean
/-- Partial Euler product over finite prime set S -/
def euler_product_S (S : FinitePrimeSet) : NAllObj → NAllObj :=
  fun x =>
    S.val.fold
      (fun acc p => acc ⊗ local_euler_factor p (S.prime_proof p))
      unit_tensor
      x
```

**Tasks**:

1. **Prove well-definedness** (5 hours)
   ```lean
   theorem euler_product_S_well_defined (S : FinitePrimeSet) :
     is_endomorphism (euler_product_S S) := by
     -- Each local factor is endomorphism
     -- Tensor preserves endomorphisms
     -- Fold preserves endomorphisms
     ...
   ```

2. **Prove order independence** (5 hours)
   ```lean
   theorem euler_product_order_independent
       (S : FinitePrimeSet) (perm : S.val.Perm) :
     euler_product_S S = euler_product_S (S.permute perm) := by
     -- Tensor is commutative
     -- Therefore order doesn't matter
     ...
   ```

3. **Compute explicit examples** (4 hours)
   ```lean
   -- Example: S = {2, 3}
   example :
     euler_product_S ⟨{2,3}, ...⟩ (ψ_6) =
       ψ_6 ⊗ ψ_2 ⊗ ψ_3 ⊗ ψ_4 ⊗ ψ_9 := by
     -- Expand geometric series for p=2 and p=3
     ...
   ```

**Milestone**: Finite Euler products defined

---

#### Days 12-14: Factorization Properties (18 hours)

**Goal**: Prove ζ_S₂ factors through ζ_S₁ when S₁ ⊆ S₂

**Key Theorem**:
```lean
theorem factorization_through_subset
    (S₁ S₂ : FinitePrimeSet) (h : S₁.val ⊆ S₂.val) :
  ∃ (φ : NAllObj → NAllObj),
    euler_product_S₂ = φ ∘ euler_product_S₁ := by
  -- S₂ = S₁ ∪ (S₂ \ S₁)
  -- ζ_S₂ = ζ_{S₂\S₁} ∘ ζ_S₁
  -- Define φ = ζ_{S₂\S₁}
  ...
```

**Tasks**:

1. **Subset decomposition** (6 hours)
   - Prove: S₂ = S₁ ∪ T where T = S₂ \ S₁
   - Show: ζ_S₂ = ζ_T ⊗ ζ_S₁ (as endomorphisms)

2. **Multiplicativity** (8 hours)
   ```lean
   theorem euler_product_multiplicative
       (S : FinitePrimeSet) (n m : ℕ)
       (h : gcd n m = 1) :
     euler_product_S S (ψ_n ⊗ ψ_m) =
       euler_product_S S (ψ_n) ⊗ euler_product_S S (ψ_m)
   ```

3. **Directed system structure** (4 hours)
   ```lean
   theorem euler_products_form_directed_system :
     IsDirectedSystem FinitePrimeSet (fun S => euler_product_S S)
   ```

**Deliverable**: `Gen/PartialEulerProducts.lean` complete

**Week 2 Summary**:
- ✅ Local Euler factors defined
- ✅ Partial products ζ_S constructed
- ✅ Factorization properties proven
- ✅ Multiplicativity established

---

### Week 3: Colimit Construction (Days 15-21)

#### Days 15-16: Diagram Construction (14 hours)

**Goal**: Define functor P: FinitePrimeSet → End(N_all)

**Tasks**:

1. **Define category of finite prime sets** (4 hours)
   ```lean
   /-- Morphisms are subset inclusions -/
   instance : Category FinitePrimeSet where
     Hom S T := S.val ⊆ T.val
     id S := subset_refl
     comp f g := subset_trans f g
   ```

2. **Define functor** (6 hours)
   ```lean
   def euler_product_functor :
       FinitePrimeSet ⥤ (NAllObj → NAllObj) where
     obj S := euler_product_S S
     map {S T} h :=
       -- h : S ⊆ T
       -- Need: morphism ζ_S → ζ_T
       factorization_morphism S T h
   ```

3. **Prove functoriality** (4 hours)
   ```lean
   theorem euler_functor_preserves_comp :
     -- F(g ∘ f) = F(g) ∘ F(f)
     euler_product_functor.map (trans h₁ h₂) =
       (euler_product_functor.map h₂) ∘ (euler_product_functor.map h₁)
   ```

**Milestone**: Functor defined

---

#### Days 17-18: Cocone and Compatibility (16 hours)

**Goal**: Construct cocone {ζ_S → ζ_gen} and prove compatibility

**Definition**:
```lean
def euler_product_cocone : Cocone euler_product_functor where
  pt := zeta_gen_candidate  -- The proposed ζ_gen
  ι := {
    app := fun S => inclusion_morphism S
    naturality := ...
  }
```

**Tasks**:

1. **Define limit candidate** (4 hours)
   ```lean
   /-- Candidate for ζ_gen as colimit -/
   def zeta_gen_candidate (x : NAllObj) : NAllObj :=
     -- Take limit over all finite prime sets
     -- For x = ψ_n, only need primes dividing n
     let S_x := finite_primes_dividing x
     euler_product_{S_x} x
   ```

2. **Define cocone legs** (6 hours)
   ```lean
   /-- Natural transformation ζ_S → ζ_gen -/
   def inclusion_morphism (S : FinitePrimeSet) :
       (euler_product_S S) → zeta_gen_candidate := by
     -- For any x and S' ⊇ S containing all primes of x,
     -- ζ_S(x) and ζ_{S'}(x) agree
     ...
   ```

3. **Prove naturality** (6 hours)
   ```lean
   theorem cocone_naturality (S T : FinitePrimeSet) (h : S ⊆ T) :
     inclusion_morphism T ∘ euler_product_functor.map h =
       inclusion_morphism S
   ```

**Milestone**: Cocone constructed

---

#### Days 19-20: Universal Property (16 hours)

**Goal**: Prove ζ_gen satisfies universal property of colimit

**Universal Property**:
```
For any X and compatible family {f_S : ζ_S → X},
∃! φ : ζ_gen → X such that φ ∘ ι_S = f_S for all S
```

**Theorem**:
```lean
theorem euler_colimit_universal_property :
  IsColimit euler_product_cocone := by
  constructor
  intro X compatible_family

  -- Define φ : ζ_gen → X
  use fun z =>
    -- z came from some ζ_S(x) for finite S
    let ⟨S, x, h⟩ := trace_to_finite_set z
    compatible_family S (euler_product_S S x)

  constructor
  · -- Prove: φ ∘ ι_S = f_S
    intro S x
    unfold φ
    -- By construction
    rfl

  · -- Prove uniqueness
    intro φ' h_comm
    funext z
    -- φ' must agree with φ by compatibility
    ...
```

**Tasks**:

1. **Tracing elements** (6 hours)
   - Every z ∈ N_all comes from finite ζ_S
   - Prove: ∀ z, ∃ S x, z = ι_S (ζ_S x)

2. **Compatibility** (6 hours)
   - Show φ well-defined (independent of choice of S)
   - Use: Compatible family property

3. **Uniqueness** (4 hours)
   - Any other φ' must equal φ
   - Follows from universal property

**Milestone**: Universal property proven

---

#### Day 21: Integration and Testing (8 hours)

**Goal**: Verify ζ_gen construction and connect to axioms

**Tasks**:

1. **Prove ζ_gen equals colimit** (3 hours)
   ```lean
   theorem zeta_gen_equals_colimit :
     ZetaMorphism.ζ_gen = zeta_gen_candidate := by
     -- Both satisfy same universal property
     -- Therefore equal by uniqueness
     ...
   ```

2. **Verify ZG1 (multiplicativity)** (2 hours)
   ```lean
   theorem colimit_satisfies_ZG1 :
     is_multiplicative zeta_gen_candidate := by
     -- Each ζ_S is multiplicative
     -- Colimit preserves multiplicativity
     ...
   ```

3. **Verify ZG2 (prime determination)** (2 hours)
   ```lean
   theorem colimit_satisfies_ZG2 :
     determined_by_primes zeta_gen_candidate := by
     -- ζ_gen = colim ζ_S
     -- Each ζ_S determined by primes in S
     -- Therefore ζ_gen determined by all primes
     ...
   ```

4. **Final testing** (1 hour)
   - Compute examples: ζ_gen(ψ_2), ζ_gen(ψ_6), ζ_gen(ψ_{30})
   - Verify against expected values
   - Check performance

**Deliverable**: `Gen/EulerProductColimit.lean` complete

**Week 3 Summary**:
- ✅ Diagram functor constructed
- ✅ Cocone proven
- ✅ Universal property verified
- ✅ ζ_gen = colimit established
- ✅ Connection to axioms verified

---

## 3. Module Design

### 3.1 Gen/MonoidalStructure.lean

**Purpose**: Monoidal structure on N_all via tensor product

**Structure** (~350 lines):
```lean
-- Imports (20 lines)
import Gen.NAll
import Gen.Colimit
import Mathlib.CategoryTheory.Monoidal.Basic

namespace Gen.Monoidal

-- Tensor product definition (50 lines)
/-- Tensor product via LCM -/
def tensor : NAllObj → NAllObj → NAllObj

-- Basic properties (80 lines)
theorem tensor_associative
theorem tensor_commutative
theorem tensor_unit_left
theorem tensor_unit_right

-- Coherence (100 lines)
theorem pentagon_coherence
theorem triangle_coherence
theorem associator_natural
theorem unitor_natural

-- Connection to multiplication (70 lines)
theorem tensor_coprime_is_product
theorem tensor_respects_gcd
theorem tensor_preserves_divisibility

-- Categorical structure (30 lines)
instance : MonoidalCategory NAllCategory

end Gen.Monoidal
```

**Key Theorems**: 15
**Estimated Lines**: 350
**Dependencies**: Gen.NAll, Mathlib.CategoryTheory.Monoidal

---

### 3.2 Gen/PartialEulerProducts.lean

**Purpose**: Finite Euler products ζ_S

**Structure** (~400 lines):
```lean
-- Imports (20 lines)
import Gen.MonoidalStructure
import Gen.Primes
import Mathlib.Data.Finset.Basic

namespace Gen.EulerProduct

-- Finite prime sets (40 lines)
def FinitePrimeSet
def prime_set_subset

-- p-adic valuation (60 lines)
def p_adic_valuation
theorem p_adic_multiplicative

-- Local Euler factors (100 lines)
def local_euler_factor
theorem local_factor_geometric_series
theorem local_factor_is_endomorphism

-- Partial products (80 lines)
def euler_product_S
theorem euler_product_well_defined
theorem euler_product_order_independent

-- Factorization (100 lines)
theorem factorization_through_subset
theorem euler_product_multiplicative
theorem euler_products_directed_system

end Gen.EulerProduct
```

**Key Theorems**: 18
**Estimated Lines**: 400
**Dependencies**: Gen.MonoidalStructure, Gen.Primes

---

### 3.3 Gen/EulerProductColimit.lean

**Purpose**: Colimit construction of ζ_gen

**Structure** (~300 lines):
```lean
-- Imports (20 lines)
import Gen.PartialEulerProducts
import Mathlib.CategoryTheory.Limits.Shapes.Filtered

namespace Gen.ZetaColimit

-- Category structure (50 lines)
instance : Category FinitePrimeSet
theorem finite_primes_directed

-- Functor (60 lines)
def euler_product_functor
theorem functor_preserves_comp

-- Cocone (80 lines)
def zeta_gen_candidate
def euler_product_cocone
theorem cocone_naturality

-- Universal property (90 lines)
theorem euler_colimit_universal_property
theorem zeta_gen_equals_colimit
theorem colimit_satisfies_ZG1
theorem colimit_satisfies_ZG2

end Gen.ZetaColimit
```

**Key Theorems**: 12
**Estimated Lines**: 300
**Dependencies**: Gen.PartialEulerProducts, Mathlib Limits

---

## 4. Success Criteria

### 4.1 Minimum Success (Sprint Completion)

**Core Deliverables**:
- ✅ Tensor product ⊗ defined
- ✅ Associativity proven
- ✅ Unit laws proven
- ✅ Local Euler factors defined
- ✅ Partial products ζ_S defined
- ✅ Factorization property proven

**Build & Tests**:
- ✅ All 3 files compile without errors
- ✅ Basic examples compute correctly
- ✅ No warnings in new modules

**Axiom Usage**:
- ⚠️ May axiomatize some colimit properties
- ⚠️ May axiomatize universal property proof

**Percentage Complete**: ~70% of Phase 2

---

### 4.2 Target Success (Phase 2 Ready)

**All Theorems Proven**:
- ✅ 15/15 monoidal structure theorems
- ✅ 18/18 partial product theorems
- ✅ 12/12 colimit theorems
- ✅ Total: 45 theorems

**Colimit Construction**:
- ✅ Functor proven
- ✅ Cocone constructed
- ✅ Universal property proven
- ✅ ζ_gen = colimit established

**Connection to Axioms**:
- ✅ ZG1 verified from construction
- ✅ ZG2 verified from construction
- ⚠️ ZG3, ZG4 outlined (full proof in Sprint 2.2)

**Percentage Complete**: ~85% of Phase 2

---

### 4.3 Stretch Success (Excellence)

**Full Verification**:
- ✅ All 4 axioms ZG1-ZG4 proven from construction
- ✅ No axioms used (everything proven)
- ✅ Computational efficiency optimized

**Advanced Properties**:
- ✅ Euler product convergence characterized
- ✅ Begin equilibrium point computation
- ✅ Performance benchmarking

**Documentation**:
- ✅ Comprehensive examples library
- ✅ Proof technique commentary
- ✅ Sprint 2.2 detailed plan

**Percentage Complete**: 100% of Phase 2

---

## 5. Mathematical Challenges

### Challenge 1: Defining ⊗ Categorically

**Problem**: N_all currently has single constructor Nall.mk
- How to distinguish ψ_n ⊗ ψ_m from ψ_{nm}?
- Need structural way to track LCM operation

**Solution Options**:

**Option A**: Extend Nall structure
```lean
inductive NAllObj where
  | embed : (n : ℕ) → GenObj.nat n → NAllObj
  | tensor : NAllObj → NAllObj → NAllObj
```
**Pros**: Explicit tensor tracking
**Cons**: Breaks existing proofs, complex equivalence relation

**Option B**: Universal property approach (RECOMMENDED)
```lean
def tensor (a b : NAllObj) : NAllObj :=
  -- Define via universal property
  -- Use colimit factorization
  colimit_factor (fun n m => include (lcm n m))
```
**Pros**: Preserves existing structure
**Cons**: Requires more infrastructure

**Decision**: Use Option B
**Justification**: Aligns with categorical philosophy, preserves Phase 1 work

---

### Challenge 2: Infinite Product Convergence

**Problem**: Classical ∏_p (1 - p^(-s))^(-1) requires analytic convergence
- How to avoid analysis in categorical setting?
- Need purely algebraic/categorical approach

**Solution**: Colimit = Categorical Limit
```
ζ_gen = colim_S ζ_S  (categorical colimit, not analytic limit)
```

**Why This Works**:
- For any ψ_n, only finitely many primes divide n
- Therefore ζ_gen(ψ_n) = ζ_S(ψ_n) for S = primes dividing n
- Colimit makes this precise: "eventual agreement"
- No infinite sums or convergence needed!

**Mathematical Insight**:
This transforms analytical problem into categorical one:
- Analytical: Does ∏_p converge?
- Categorical: Does directed system have colimit?
- Answer: Yes, by directedness of finite prime sets

---

### Challenge 3: Connecting to Classical Euler Product

**Problem**: Need to show categorical ζ_gen corresponds to classical ζ(s)
- Requires projection functor F_R: Gen → ℂ
- This is Phase 3 work

**Sprint 2.1 Approach**: Defer to Phase 3
- Focus on categorical construction
- Verify ZG1-ZG4 axioms satisfied
- Leave projection functor for later

**Justification**: Separation of concerns
- Sprint 2.1: Pure category theory
- Sprint 2.2: Verify all axioms
- Phase 3: Complex structure and projection
- Phase 4: Prove RH

---

## 6. Dependencies & Prerequisites

### 6.1 From Phase 1 (All Complete ✅)

**Infrastructure**:
- ✅ Gen category well-defined
- ✅ N_all colimit constructed
- ✅ Universal property proven
- ✅ Prime structure formalized
- ✅ Divisibility morphisms proven

**Files Available**:
- Gen/NAll.lean - N_all definition
- Gen/Colimit.lean - Colimit properties
- Gen/Primes.lean - Prime structure
- Gen/NAllProperties.lean - All properties proven

**No Blockers**: Phase 1 provides everything needed

---

### 6.2 New Infrastructure Needed

**Mathlib Dependencies**:
```lean
import Mathlib.CategoryTheory.Monoidal.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Filtered
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.GCD
import Mathlib.NumberTheory.Padics.PadicVal
```

**All Available**: No missing dependencies

**New Definitions**:
1. FinitePrimeSet - custom type (40 lines)
2. Monoidal structure instance (30 lines)
3. Directed system instance (20 lines)

**Estimated Setup**: 2-3 hours total

---

### 6.3 For Phase 2 Completion (Sprint 2.2+)

**Sprint 2.1 Will Provide**:
- ⊗ monoidal structure
- ζ_S partial products
- ζ_gen as colimit

**Sprint 2.2 Will Need**:
- Prove ZG3 (colimit preservation)
- Prove ZG4 (balance condition)
- Connect to equilibrium theory
- Performance optimization

**No Blockers Expected**: Clear path forward

---

## 7. Risk Assessment

### Risk 1: Monoidal Axioms Harder Than Expected

**Probability**: MEDIUM
**Impact**: Timeline extends 3-5 days

**Mitigation**:
- Use Mathlib monoidal category infrastructure heavily
- Reference existing monoidal instances (Set, Type, etc.)
- Consult Lean Zulip #category-theory if stuck >2 hours

**Backup Plan**:
- Axiomatize pentagon coherence if proof too complex
- Focus on computational properties over pure theory
- Acceptable to defer edge cases to Sprint 2.2

**Time Buffer**: 20% allocated (Days 7, 14, 21)

---

### Risk 2: Colimit Construction Complex

**Probability**: MEDIUM
**Impact**: Week 3 extends to Week 4

**Mitigation**:
- Use filtered colimit (simpler than general colimit)
- Finite prime sets are directed system (standard result)
- Template from Mathlib.CategoryTheory.Limits examples

**Backup Plan**:
- Axiomatize universal property
- Focus on construction of ζ_gen candidate
- Defer full universal property proof to Sprint 2.2
- Still achieves 70% success criteria

**Escalation**: If Week 3 Day 2 reveals major issues, re-scope immediately

---

### Risk 3: Three Weeks Insufficient

**Probability**: LOW
**Impact**: Sprint extends to 4 weeks

**Mitigation**:
- Focus on core definitions first (Week 1-2)
- Colimit outline acceptable for minimum success
- 70% success criteria allows flexibility
- Buffer days built into each week

**Backup Plan**:
- Extend to 4 weeks (28 days)
- Still within Phase 2 timeline (6 weeks total)
- No impact on overall project schedule

**Decision Point**: End of Week 2 (Day 14)
- If <60% complete: Extend sprint
- If 60-80% complete: Continue as planned
- If >80% complete: Consider stretch goals

---

## 8. Timeline Detail

### Day-by-Day Breakdown

**Week 1: Monoidal Structure**
```
Day 1  (6h): Define tensor, basic type checking
Day 2  (6h): Inclusion respecting, commutativity
Day 3  (8h): Associativity setup, key lemmas
Day 4  (8h): Associativity proof completion
Day 5  (7h): Unit laws (left + right)
Day 6  (7h): Pentagon coherence
Day 7  (6h): Multiplication connection + buffer
Total: 48 hours
```

**Week 2: Partial Euler Products**
```
Day 8  (7h): p-adic valuation definition
Day 9  (7h): Local Euler factors
Day 10 (7h): Partial products ζ_S definition
Day 11 (7h): Well-definedness proofs
Day 12 (6h): Subset factorization
Day 13 (6h): Multiplicativity
Day 14 (6h): Directed system + testing + buffer
Total: 46 hours
```

**Week 3: Colimit Construction**
```
Day 15 (7h): Category of finite prime sets
Day 16 (7h): Functor definition + functoriality
Day 17 (8h): Cocone construction
Day 18 (8h): Cocone naturality
Day 19 (8h): Universal property setup
Day 20 (8h): Universal property proof
Day 21 (8h): Integration, axiom verification, testing
Total: 54 hours
```

**Grand Total**: 148 hours over 21 days (~7 hours/day)

---

### Testing Milestones

**End of Week 1** (Day 7):
```lean
example : ψ_2 ⊗ ψ_3 = ψ_6 := by rfl
example : ψ_4 ⊗ ψ_6 = ψ_{12} := by rfl
example : (ψ_2 ⊗ ψ_3) ⊗ ψ_5 = ψ_2 ⊗ (ψ_3 ⊗ ψ_5) := tensor_associative
```

**End of Week 2** (Day 14):
```lean
example : euler_product_S {2} (ψ_8) = ... := by compute
example : euler_product_S {2,3} (ψ_6) = ... := by compute
example : ∀ S₁ S₂, S₁ ⊆ S₂ → ζ_S₂ factors through ζ_S₁
```

**End of Week 3** (Day 21):
```lean
example : zeta_gen_candidate = ZetaMorphism.ζ_gen := by theorem
example : is_multiplicative zeta_gen_candidate := colimit_satisfies_ZG1
```

---

### Integration Points

**Day 7**: MonoidalStructure.lean → commit
**Day 14**: PartialEulerProducts.lean → commit
**Day 21**: EulerProductColimit.lean → commit

**Testing**: Daily `lake build` checks
**Documentation**: Updated each Friday (Days 7, 14, 21)

---

## 9. Research Needed

### 9.1 Monoidal Categories in Lean

**Question**: How to implement monoidal structure most efficiently?

**Resources**:
- Mathlib.CategoryTheory.Monoidal.Basic
- Mathlib.CategoryTheory.Monoidal.Braided
- Examples: SetCat, Type, Ab (abelian groups)

**Action Items**:
- Study existing MonoidalCategory instances (2 hours)
- Identify reusable patterns (1 hour)
- Template for NAll instance (1 hour)

**Timeline**: Before Day 1 (preparation)

---

### 9.2 Colimit of Endomorphisms

**Question**: How to construct colimit in functor category?

**Resources**:
- Mathlib.CategoryTheory.Limits.Shapes.Filtered
- Mathlib.CategoryTheory.Functor.Category
- nLab: Filtered colimits

**Key Insight**:
```
colim : (J ⥤ C) → C  (colimit of diagram)
```
For us:
```
J = FinitePrimeSet
C = (NAllObj → NAllObj) (endomorphism category)
Diagram = euler_product_functor
```

**Action Items**:
- Understand IsColimit predicate (2 hours)
- Study filtered colimit examples (2 hours)
- Template for Euler product case (2 hours)

**Timeline**: Before Day 15 (end of Week 2)

---

### 9.3 Directed Systems

**Question**: How to prove finite prime sets form directed system?

**Definition**: Category J is directed if:
- ∀ i j ∈ J, ∃ k ∈ J, i → k and j → k
- ∀ i, j: i → j and i → k implies ∃ l: j → l and k → l

**For Finite Prime Sets**:
- Objects: Finite sets of primes S, T
- Morphisms: Inclusions S ⊆ T
- Directedness: S ∪ T is the upper bound

**Proof Sketch**:
```lean
theorem finite_primes_directed :
  IsDirected FinitePrimeSet := by
  intro S T
  use S ∪ T
  constructor
  · exact subset_union_left
  · exact subset_union_right
```

**Action Items**:
- Formalize union operation (1 hour)
- Prove directedness (2 hours)

**Timeline**: Day 15

---

### 9.4 p-adic Valuation

**Question**: Use Mathlib or define custom?

**Mathlib Option**:
```lean
import Mathlib.NumberTheory.Padics.PadicVal
Nat.padicValNat : ℕ → ℕ → ℕ
```

**Custom Option**:
```lean
def p_adic_val (p n : ℕ) : ℕ :=
  if p ∣ n then 1 + p_adic_val p (n / p) else 0
```

**Decision**: Use Mathlib.NumberTheory.Padics.PadicVal
**Reason**: Well-tested, proven properties available

**Action Items**:
- Import padicVal module (5 min)
- Test on examples (30 min)
- Read lemmas available (1 hour)

**Timeline**: Before Day 8

---

## 10. Deliverables Checklist

### 10.1 Code Deliverables

**New Files** (3 total):
- [ ] Gen/MonoidalStructure.lean (~350 lines, 15 theorems)
- [ ] Gen/PartialEulerProducts.lean (~400 lines, 18 theorems)
- [ ] Gen/EulerProductColimit.lean (~300 lines, 12 theorems)

**Total**: ~1050 lines, 45 theorems

**Expected Sorry Count**:
- Minimum success: ~10 sorry (colimit properties)
- Target success: ~3 sorry (edge cases)
- Stretch success: 0 sorry

---

### 10.2 Test Deliverables

**New Test File**:
- [ ] test/EulerProductVerification.lean (~200 lines)

**Test Coverage**:
```lean
-- Monoidal structure tests
example : tensor_associative
example : tensor_unit_laws
example : tensor_coprime_is_product

-- Partial product tests
example : local_factor_computes
example : euler_product_S_examples
example : factorization_examples

-- Colimit tests
example : functor_correct
example : cocone_valid
example : universal_property_holds
```

**Integration Tests**:
- [ ] MonoidalStructure + NAllProperties integration
- [ ] PartialEulerProducts + Primes integration
- [ ] EulerProductColimit + ZetaMorphism connection

---

### 10.3 Documentation Deliverables

**Sprint Documentation**:
- [ ] SPRINT_2_1_PLAN.md (THIS FILE)
- [ ] SPRINT_2_1_SUMMARY.md (end of sprint)
  - Achievements
  - Proof techniques
  - Challenges overcome
  - Examples computed

**Research Documentation**:
- [ ] Update categorical/research/zeta_gen_euler_product.md
  - Add explicit construction details
  - Document computational results
  - Record lessons learned

**Module Documentation**:
- [ ] Gen/MonoidalStructure.lean - comprehensive docstrings
- [ ] Gen/PartialEulerProducts.lean - comprehensive docstrings
- [ ] Gen/EulerProductColimit.lean - comprehensive docstrings

**Status Updates**:
- [ ] README.md - Phase 2 progress update
- [ ] PHASE_2_STATUS.md - Sprint 2.1 completion report

---

## 11. Examples to Compute

### 11.1 Monoidal Examples

**Test tensor product**:
```lean
-- Coprime case: tensor = multiplication
example : ψ_2 ⊗ ψ_3 = ψ_6 := by
  rw [tensor_coprime_is_product]
  rfl

-- Non-coprime: tensor = LCM
example : ψ_4 ⊗ ψ_6 = ψ_{12} := by
  unfold tensor
  -- lcm(4,6) = 12
  norm_num
```

**Associativity check**:
```lean
example : (ψ_2 ⊗ ψ_3) ⊗ ψ_5 = ψ_2 ⊗ (ψ_3 ⊗ ψ_5) := by
  apply tensor_associative
```

---

### 11.2 Local Euler Factor Examples

**Factor at p=2**:
```lean
-- On ψ_1 (2 doesn't divide 1)
example : local_euler_factor 2 _ (ψ_1) = ψ_1 := by compute

-- On ψ_2 (2¹ || 2)
example : local_euler_factor 2 _ (ψ_2) = ψ_2 ⊗ ψ_1 ⊗ ... := by compute

-- On ψ_8 (2³ || 8)
example : local_euler_factor 2 _ (ψ_8) =
  ψ_8 ⊗ ψ_4 ⊗ ψ_2 ⊗ ψ_1 := by compute
```

**Factor at p=3**:
```lean
example : local_euler_factor 3 _ (ψ_9) =
  ψ_9 ⊗ ψ_3 ⊗ ψ_1 := by compute
```

---

### 11.3 Partial Euler Product Examples

**S = {2}**:
```lean
example : euler_product_S {2} (ψ_1) = ψ_1 := by compute
example : euler_product_S {2} (ψ_2) = ψ_2 ⊗ ψ_1 := by compute
example : euler_product_S {2} (ψ_4) = ψ_4 ⊗ ψ_2 ⊗ ψ_1 := by compute
```

**S = {2, 3}**:
```lean
-- On ψ_6 = ψ_2 ⊗ ψ_3
example : euler_product_S {2,3} (ψ_6) =
  -- Factor at 2: ψ_2 ⊗ ψ_1
  -- Factor at 3: ψ_3 ⊗ ψ_1
  -- Combined: (ψ_2 ⊗ ψ_1) ⊗ (ψ_3 ⊗ ψ_1)
  (ψ_2 ⊗ ψ_3) ⊗ (ψ_2 ⊗ ψ_1) ⊗ (ψ_3 ⊗ ψ_1) ⊗ ψ_1 := by compute
```

**S = {2, 3, 5}**:
```lean
example : euler_product_S {2,3,5} (ψ_30) = ... := by compute
-- ψ_30 = ψ_2 ⊗ ψ_3 ⊗ ψ_5
-- Expect: All divisors of 30
```

---

### 11.4 Colimit Examples

**Compute via limit**:
```lean
-- For ψ_6, only primes 2 and 3 matter
example : zeta_gen_candidate (ψ_6) =
  euler_product_{2,3} (ψ_6) := by
  apply colimit_stabilizes
  -- All larger S give same result

-- For ψ_30, primes 2, 3, 5 matter
example : zeta_gen_candidate (ψ_30) =
  euler_product_{2,3,5} (ψ_30) := by
  apply colimit_stabilizes
```

---

## 12. Connection to Phase 1 Axioms

### How Sprint 2.1 Enables Axiom Verification

**Current State (Phase 1)**:
- ζ_gen is **axiomatic** (assumed to exist)
- ZG1-ZG4 are **axioms** (assumed properties)
- Equilibrium theory built on axioms

**After Sprint 2.1**:
- ζ_gen is **constructed** (explicitly via colimit)
- ZG1-ZG4 can be **proven** (derived from construction)
- Equilibrium theory can be **computed**

---

### 12.1 ZG1: Multiplicativity

**Axiom** (current):
```lean
axiom zeta_multiplicative (n m : ℕ) (h : gcd n m = 1) :
  ζ_gen (ψ_n ⊗ ψ_m) = ζ_gen (ψ_n) ⊗ ζ_gen (ψ_m)
```

**Theorem** (Sprint 2.1 enables):
```lean
theorem colimit_satisfies_ZG1 :
  is_multiplicative zeta_gen_candidate := by
  intro n m h_coprime
  unfold zeta_gen_candidate

  -- For coprime n,m with prime factorizations
  -- ζ_gen(ψ_n ⊗ ψ_m) = colim_S ζ_S(ψ_n ⊗ ψ_m)
  --                   = colim_S [ζ_S(ψ_n) ⊗ ζ_S(ψ_m)]  (by ζ_S multiplicative)
  --                   = [colim_S ζ_S(ψ_n)] ⊗ [colim_S ζ_S(ψ_m)]  (colimit commutes with ⊗)
  --                   = ζ_gen(ψ_n) ⊗ ζ_gen(ψ_m)

  apply euler_product_multiplicative
```

**Status After Sprint 2.1**: Outlined (full proof Sprint 2.2)

---

### 12.2 ZG2: Prime Determination

**Axiom** (current):
```lean
axiom zeta_determined_by_primes :
  ∀ f, (∀ p prime, f(ψ_p) = ζ_gen(ψ_p)) → f = ζ_gen
```

**Theorem** (Sprint 2.1 enables):
```lean
theorem colimit_satisfies_ZG2 :
  determined_by_primes zeta_gen_candidate := by
  intro f h_agree_on_primes

  -- ζ_gen = colim_S ζ_S
  -- Each ζ_S is product of local factors at primes in S
  -- Local factors determined by prime values
  -- Therefore ζ_gen determined by all prime values

  funext x
  obtain ⟨n, y, hx⟩ := nall_from_colimit x

  -- Both f and ζ_gen agree on primes
  -- Both are multiplicative (by ZG1)
  -- By FTA, they agree on all elements

  apply agree_on_products_of_primes
```

**Status After Sprint 2.1**: Outlined (full proof Sprint 2.2)

---

### 12.3 ZG3 & ZG4

**ZG3** (Colimit Preservation):
- Requires deeper colimit theory
- Sprint 2.2 focus

**ZG4** (Balance Condition):
- Requires flow strength definitions
- Sprint 2.2-2.3 focus

---

## 13. Conclusion

### 13.1 Sprint 2.1 Mission Summary

**Transform ζ_gen from axiom to construction** by:
1. Defining monoidal structure ⊗ on N_all (Week 1)
2. Constructing partial Euler products ζ_S (Week 2)
3. Taking colimit: ζ_gen = colim_S ζ_S (Week 3)

**Deliverables**:
- 3 new Lean files (~1050 lines)
- 45 new theorems
- Explicit construction of categorical Euler product

### 13.2 Why This Matters

**Foundational Shift**:
- Phase 1: "ζ_gen exists and has properties" (trust)
- Sprint 2.1: "ζ_gen = colim ζ_S" (construction)
- Phase 3: "ζ_gen corresponds to classical ζ(s)" (connection)
- Phase 4: "Non-trivial zeros satisfy RH" (proof)

**Mathematical Beauty**:
The Euler product formula:
```
ζ(s) = ∏_p (1 - p^(-s))^(-1)
```

becomes categorical:
```
ζ_gen = colim_{finite S} ⊗_{p ∈ S} local_factor_p
```

No analysis needed—pure category theory!

### 13.3 Key Insights

**Insight 1**: Monoidal structure via LCM
- Natural: lcm captures "multiplicative join"
- Preserves divisibility
- Coprime case recovers multiplication

**Insight 2**: Finite products well-defined
- No convergence issues
- Computable
- Directed system structure automatic

**Insight 3**: Colimit makes infinite product precise
- Categorical limit, not analytical
- Universal property gives uniqueness
- Enables verification without complex analysis

**Insight 4**: Construction validates axioms
- ZG1, ZG2 follow from construction
- Not assumed—proven!
- Increases confidence in framework

### 13.4 Next Steps After Sprint 2.1

**Sprint 2.2** (2 weeks):
- Prove ZG1-ZG4 from colimit construction
- Verify all axiomatic properties
- Connect equilibrium theory to construction

**Sprint 2.3** (2 weeks):
- Computational implementation
- Performance optimization
- Begin equilibrium point discovery

**Phase 3** (6 weeks):
- Complex projection functor F_R: Gen → ℂ
- Classical ζ(s) correspondence
- Critical line Re(s) = 1/2 interpretation

**Phase 4** (8 weeks):
- Riemann Hypothesis proof
- Equilibrium = balance
- Re(s) = 1/2 for non-trivial zeros

### 13.5 Success Metrics

| Metric | Minimum | Target | Stretch |
|--------|---------|--------|---------|
| Theorems proven | 30/45 (67%) | 40/45 (89%) | 45/45 (100%) |
| Files complete | 2/3 | 3/3 | 3/3 + extras |
| Axioms verified | ZG1 outline | ZG1, ZG2 proven | ZG1-ZG4 proven |
| Examples computed | 5 | 10 | 20 |
| Phase 2 progress | 70% | 85% | 100% |

### 13.6 Timeline Confidence

**High Confidence** (>80%):
- Week 1: Monoidal structure
- Days 8-11: Local factors and ζ_S

**Medium Confidence** (60-80%):
- Days 12-14: Factorization properties
- Days 15-18: Functor and cocone

**Lower Confidence** (50-60%):
- Days 19-21: Universal property proof

**Overall**: 70% confidence in target success (40/45 theorems)

**Risk Mitigation**:
- Buffer days built in
- Minimum success criteria achievable even with setbacks
- Extension to 4 weeks acceptable if needed

---

## Ready to Execute

**Status**: ✅ READY
**Start Date**: 2025-11-12
**Target Completion**: 2025-12-02 (21 days)
**Next Action**: Begin Day 1 - Define tensor product

---

*Document Created*: 2025-11-12
*Sprint*: 2.1 - Multiplicative Structure & Euler Product
*Phase*: 2 - Explicit ζ_gen Construction
*Goal*: Monoidal structure + partial products + colimit construction
*Deliverables*: 3 files, 45 theorems, ~1050 lines
*Success Criteria*: 70% minimum, 85% target, 100% stretch
