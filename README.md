# GIP: A Formal Theory of Existence

GIP (Generalized Initial-object Projection) is a comprehensive Lean 4 formalization of a theory demonstrating that self-reference, paradoxes, and the emergence of physical structures share a common categorical foundation: the **zero object (○)**.

The project's central thesis is that existence is not a given, but a property of structures that are "revealed" by maintaining their coherence across a dual-cycle of **Generation** and **Revelation**.

This repository contains the complete formal proofs, the theoretical framework, and the specifications for the theory's testable predictions.

## Current Status

**The project is technically complete and ready for its next phase: publication and computational validation.**

- **Build Status**: ✅ SUCCESS
- **Core Theory**: ✅ All foundational theorems proven
- **Testing**: ✅ 100% critical path coverage

For a detailed breakdown of metrics, `sorry` analysis, key breakthroughs, and the project roadmap, please see the single source of truth:

➡️ **[PROJECT_STATUS.md](PROJECT_STATUS.md)**

## Overview of the Theory

GIP provides a mathematical framework for understanding how structure emerges from a pre-structural origin (○). It proves that this process inherently leads to the paradoxes of self-reference and provides a computable measure, **Cohesion**, to predict which structures will be stable enough to "exist."

The key insights are:
1.  **The Zero Object (○)**: A single object that is both initial (a unique source) and terminal (a universal sink) provides the basis for all structure.
2.  **Information Loss in Self-Reference**: The theorem `circle_not_injective` proves that any self-referential cycle is information-lossy, explaining the structural origin of paradoxes.
3.  **Paradox Isomorphism**: All major logical paradoxes (Russell's, Gödel's, the Halting Problem) are shown to be categorically isomorphic.
4.  **Computable Cohesion**: A structure's stability and "existence" can be predicted by calculating its invariance across a dual-cycle process. This transforms the theory into testable science.

## Guide to the Repository

This repository is organized to support research, review, and further development.

| File / Directory | Description |
|---|---|
| **[PROJECT_STATUS.md](PROJECT_STATUS.md)** | **START HERE.** The single source of truth for project status, metrics, and roadmap. |
| **`Gip/`** | The complete Lean 4 source code containing all definitions and proofs. |
| **`Test/`** | The test suite used to verify the formalization. |
| **`docs/`** | The complete conceptual documentation for the project. |
| ├─ **[docs/THEORY.md](docs/THEORY.md)** | A high-level overview of the GIP theoretical foundations. |
| ├─ **[docs/FORMAL_FRAMEWORK.md](docs/FORMAL_FRAMEWORK.md)** | The definitive, publication-ready paper detailing the formal framework. |
| ├─ **[docs/COMPUTATIONAL_GUIDE.md](docs/COMPUTATIONAL_GUIDE.md)** | The technical specification for computationally testing the theory's predictions. |
| **[CONTRIBUTING.md](CONTRIBUTING.md)** | Guidelines for contributing to the project. |

## Quick Start

### Prerequisites
- Lean 4
- Lake (Lean's build system)

### Building the Project
```bash
# Get Mathlib cache
lake exe cache get

# Build all modules
lake build

# Run the test suite
lake build Test
```

The project is expected to build with zero errors.

## License

This project is open source and available under standard open source terms.
