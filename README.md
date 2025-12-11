# GIP: A Formal Theory of Existence

GIP (Generalized Initial-object Projection) is a comprehensive Lean 4 formalization of a theory demonstrating that self-reference, paradoxes, and the emergence of physical structures share a common categorical foundation: the **zero object (○)**.

The project's central thesis is that existence is not a given, but a property of structures that are "revealed" by maintaining their coherence across a dual-cycle of **Generation** and **Revelation**.

This repository contains the complete formal proofs, the theoretical framework, and the specifications for the theory's testable predictions.

## Current Status

**The project is technically complete with SMFT correspondence proven. Ready for publication and computational validation.**

- **Build Status**: ✅ SUCCESS (1,927 jobs, 0 errors)
- **Core Theory**: ✅ All foundational theorems proven (Phi convergence model)
- **SMFT Formalization**: ✅ COMPLETE (2,870 LOC, formal proof SMFT IS GIP)
- **Testing**: ✅ 100% critical path coverage

For detailed status and metrics:

➡️ **[docs/status/PROJECT_STATUS.md](docs/status/PROJECT_STATUS.md)** - Complete project status, metrics, and roadmap

## Overview of the Theory

GIP provides a mathematical framework for understanding how structure emerges from a pre-structural origin (○). It proves that this process inherently leads to the paradoxes of self-reference and provides a computable measure, **Cohesion**, to predict which structures will be stable enough to "exist."

The key insights are:
1.  **The Zero Object (○)**: A single object that is both initial (a unique source) and terminal (a universal sink) provides the basis for all structure.
2.  **Phi (Φ) Convergence**: All transformations flow through Phi as a central convergence point, clarifying emergence vs manifestation.
3.  **Information Loss in Self-Reference**: The theorem `circle_not_injective` proves that any self-referential cycle is information-lossy, explaining the structural origin of paradoxes.
4.  **Paradox Isomorphism**: All major logical paradoxes (Russell's, Gödel's, the Halting Problem) are shown to be categorically isomorphic.
5.  **Computable Cohesion**: A structure's stability and "existence" can be predicted by calculating its invariance across a dual-cycle process. This transforms the theory into testable science.
6.  **SMFT IS GIP**: Formal proof that Synchronization Mass Field Theory and Generative Integration Protocol are mathematically identical - synchronization = mass generation = identity emergence.

## Repository Structure

| Directory | Description |
|---|---|
| **[`docs/`](docs/)** | **START HERE** - Complete documentation |
| ├─ [`status/`](docs/status/) | Project status and metrics |
| ├─ [`theory/`](docs/theory/) | Core theoretical foundations |
| ├─ [`guides/`](docs/guides/) | Usage and implementation guides |
| └─ [`publications/`](docs/publications/) | Publication-ready papers |
| **[`Gip/`](Gip/)** | Complete Lean 4 source code (10,336 LOC) |
| **[`Test/`](Test/)** | Comprehensive test suite |
| **[`archive/`](archive/)** | Historical development documents |
| **[`scripts/`](scripts/)** | Build and utility scripts |
| **[CONTRIBUTING.md](CONTRIBUTING.md)** | Contribution guidelines |

## Key Documentation

- **Status**: [docs/status/PROJECT_STATUS.md](docs/status/PROJECT_STATUS.md) - Current state and roadmap
- **Theory**: [docs/theory/FOUNDATIONS.md](docs/theory/FOUNDATIONS.md) - Core concepts with Phi model
- **Usage**: [docs/guides/USAGE.md](docs/guides/USAGE.md) - How to use the library
- **SMFT**: [docs/theory/SMFT_THEORY.md](docs/theory/SMFT_THEORY.md) - Physics correspondence

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
