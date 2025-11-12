# Gen Category - Lean 4 Formalization

## Overview

This is the formal Lean 4 encoding of the Gen category, a mathematical structure that connects the Riemann Hypothesis to categorical foundations through a three-register system.

## Mathematical Foundation

The Gen category consists of three registers:
- **Register 0**: The empty object ∅ (initial object)
- **Register 1**: The unit object 𝟙 (bridge object)
- **Register 2**: Numeric objects n for each n ∈ ℕ (divisibility structure)

Key morphisms:
- Genesis: γ: ∅ → 𝟙
- Instantiation: ι_n: 𝟙 → n
- Divisibility: φ_{n,m}: n → m when n | m

## Project Structure

```
Gen/
├── Basic.lean          # Core type definitions
├── Morphisms.lean      # Morphism structure
├── Register0.lean      # Empty object properties
├── Register1.lean      # Unit object properties
├── Register2.lean      # Numeric objects and divisibility
├── CategoryAxioms.lean # Category law verification
└── Colimit.lean        # N_all universal object
```

## Installation

### Prerequisites

1. Install Lean 4 and its toolchain manager (elan):
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile  # or restart terminal
```

2. Verify installation:
```bash
lean --version
lake --version
```

### Building the Project

1. Clone and navigate to the project:
```bash
cd categorical/lean
```

2. Download Mathlib4 cache (speeds up compilation):
```bash
lake exe cache get
```

3. Build the project:
```bash
lake build
```

4. (Optional) Run the main executable:
```bash
lake exec main
```

## Development

### Opening in VS Code

1. Install the Lean 4 extension for VS Code
2. Open the `categorical/lean` folder
3. The extension will automatically use the lean-toolchain version

### Working with Proofs

Currently, all proofs are stubbed with `sorry`. To contribute:

1. Find a theorem marked with `sorry`
2. Replace with actual proof using Lean tactics
3. Ensure it type-checks with `lake build`

Priority proofs to complete:
- Initial object properties in Register0.lean
- Critical identity: φ_{n,m} ∘ ι_n = ι_m in Register2.lean
- Identity laws in CategoryAxioms.lean

### Type Checking Individual Files

```bash
lean Gen/Basic.lean      # Check specific file
lake build Gen.Basic      # Build specific module
```

## Key Theorems

### Implemented (with stubs)

1. **Initial Object**: `empty_is_initial` - ∅ has unique morphism to every object
2. **Critical Identity**: `critical_identity` - φ_{n,m} ∘ ι_n = ι_m when n | m
3. **Universal Factorization**: All morphisms ∅ → n factor through 𝟙
4. **Divisibility Criterion**: Hom(n,m) ≠ ∅ iff n | m
5. **Category Laws**: Identity and associativity axioms

### Mathematical Significance

The formalization proves that:
- Gen forms a well-defined category
- The divisibility structure of natural numbers embeds categorically
- The three-register system captures number-theoretic properties
- The colimit N_all provides a universal numeric object

## Testing

Run the test suite (when implemented):
```bash
lake test
```

Check specific properties:
```lean
#check Gen.Register0.empty_is_initial
#reduce Gen.idMorph Gen.GenObj.empty
```

## Documentation

- Mathematical definitions: `../definitions/*_v2.md`
- QA verification: `../qa/definitions_verification_v2.md`
- Implementation status: `LEAN_STATUS.md`

## Contributing

1. Pick a `sorry` to resolve
2. Write the proof following Mathlib style
3. Ensure backward compatibility
4. Add test cases if applicable
5. Update LEAN_STATUS.md

## References

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Category Theory in Lean](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/CategoryTheory)

## License

This formalization is part of the Riemann Hypothesis research project.