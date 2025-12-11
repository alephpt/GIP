# GIP Documentation

Welcome to the GIP (Generalized Initial-object Projection) documentation. This guide helps you navigate the project's documentation structure.

## Quick Links

- **Project Status**: [status/PROJECT_STATUS.md](status/PROJECT_STATUS.md) - Current state and metrics
- **Getting Started**: [guides/USAGE.md](guides/USAGE.md) - How to use the library
- **Theory Overview**: [theory/FOUNDATIONS.md](theory/FOUNDATIONS.md) - Core concepts

## Documentation Structure

### Status
Current project state and progress tracking.

- [`PROJECT_STATUS.md`](status/PROJECT_STATUS.md) - Unified status (GIP + SMFT), metrics, roadmap

### Theory
Core theoretical foundations and mathematical framework.

- [`FOUNDATIONS.md`](theory/FOUNDATIONS.md) - GIP core theory with Phi (Φ) model
- [`PHI_MODEL.md`](theory/PHI_MODEL.md) - Phi convergence architecture in detail
- [`SMFT_THEORY.md`](theory/SMFT_THEORY.md) - Synchronization Mass Field Theory
- [`CORRESPONDENCE.md`](theory/CORRESPONDENCE.md) - Formal SMFT ↔ GIP mappings

### Guides
Practical guides for using and understanding the implementation.

- [`USAGE.md`](guides/USAGE.md) - Library usage and examples
- [`COMPUTATION.md`](guides/COMPUTATION.md) - Numerical methods and validation
- [`NOTATION.md`](guides/NOTATION.md) - Symbol reference and conventions

### Publications
Publication-ready documents and papers.

- [`GIP_FRAMEWORK.md`](publications/GIP_FRAMEWORK.md) - Formal framework paper
- [`SMFT_CORRESPONDENCE.md`](publications/SMFT_CORRESPONDENCE.md) - SMFT-GIP identity paper
- [`PREDICTIONS.md`](publications/PREDICTIONS.md) - Testable predictions

## Key Concepts

### The Phi (Φ) Model
All transformations in GIP flow through a central convergence point called Phi (Φ). This architecture explains:
- How identities emerge from emptiness
- Why self-reference creates paradoxes
- The connection to physical synchronization

### SMFT IS GIP
Formally proven: Synchronization Mass Field Theory and GIP are mathematically identical. This means:
- Mass generation = Identity emergence
- Synchronization = Convergence
- Critical phenomena are universal

### Cohesion
A computable measure of structure stability through transformation cycles. High cohesion structures survive and form the universe.

## Implementation

The theory is implemented in Lean 4 with:
- 10,336 lines of verified code
- 322 proven theorems
- 100% critical test coverage
- Clean build (0 errors)

Source code in [`../Gip/`](../Gip/) directory.
Tests in [`../Test/`](../Test/) directory.

## Getting Started

1. **Understand the theory**: Read [theory/FOUNDATIONS.md](theory/FOUNDATIONS.md)
2. **Learn the notation**: Review [guides/NOTATION.md](guides/NOTATION.md)
3. **Try examples**: Follow [guides/USAGE.md](guides/USAGE.md)
4. **Check status**: See [status/PROJECT_STATUS.md](status/PROJECT_STATUS.md)

## Historical Archive

Development history preserved in [`../archive/`](../archive/):
- `2025-11/` - November work (initial development)
- `2025-12/` - December work (Phi model, SMFT formalization)

## Contributing

See [`../CONTRIBUTING.md`](../CONTRIBUTING.md) for contribution guidelines.

## Questions?

- Theory questions → Start with [theory/FOUNDATIONS.md](theory/FOUNDATIONS.md)
- Implementation → See [guides/USAGE.md](guides/USAGE.md)
- Current work → Check [status/PROJECT_STATUS.md](status/PROJECT_STATUS.md)
- Historical context → Browse [`../archive/`](../archive/)