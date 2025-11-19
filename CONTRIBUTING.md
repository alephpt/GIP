# Contributing to GIP

Thank you for your interest in contributing to the GIP formalization project. This guide outlines our development standards and processes.

## Quick Start

### Prerequisites
- Lean 4.14.0
- Lake build system
- Git
- 8GB+ RAM recommended

### Setup
```bash
# Clone repository
git clone [repository-url]
cd gip

# Get Mathlib cache (speeds up builds)
lake exe cache get

# Attempt build (currently failing - see STATUS.md)
lake build
```

## Development Standards

### Code Quality Requirements

#### File Size Limits
- **Maximum 500 lines per file** - Split large files into modules
- **Maximum 50 lines per function** - Extract helper functions if exceeded
- **Maximum 3 levels of nesting** - Refactor complex logic

#### Naming Conventions
- Use descriptive names (no cryptic abbreviations)
- Theorems: `snake_case` describing what is proven
- Types: `PascalCase` for custom types
- Functions: `snake_case` for definitions
- Files: `PascalCase.lean` for module names

#### Error Handling
- No silent failures - all errors must be handled
- Use `panic!` only for truly impossible states
- Provide informative error messages
- Add appropriate logging

#### Zero Tolerance
- **NO hardcoded secrets or credentials**
- **NO commented-out code blocks**
- **NO TODOs in production code**
- **NO duplicate implementations**
- **NO unhandled edge cases**

### Proof Standards

#### Sorry Policy
- **Goal: 0 sorrys** for publication
- Document why a sorry exists with comment
- Create issue for each sorry
- Prioritize sorry resolution

#### Theorem Structure
```lean
/-- Brief description of what the theorem proves -/
theorem theorem_name (hypotheses) : conclusion := by
  -- Proof strategy comment
  proof_steps
```

#### Axiom Guidelines
- Minimize axiom count
- Document why axiom is necessary
- Prefer definitions over axioms when possible
- Group related axioms together

### Testing Approach

#### Unit Tests
- Test each theorem independently
- Cover edge cases
- Test for both positive and negative cases

#### Integration Tests
- Test theorem combinations
- Verify factorization paths
- Check paradox equivalences

#### Build Tests
```bash
# Full build
lake build

# Clean build
lake clean && lake build

# Check for sorrys
grep -r "sorry" Gip/ --include="*.lean" | wc -l
```

## Adding New Theorems

### Process
1. **Check for duplicates** - Search existing codebase
2. **Write specification** - Clear statement of what to prove
3. **Implement proof** - Following standards above
4. **Add tests** - Unit and integration
5. **Update documentation** - In-code and separate docs
6. **Submit PR** - With description and test results

### Template
```lean
import Gip.Core

namespace GIP.YourModule

/-- One-line description of theorem -/
theorem your_theorem_name
  (h1 : hypothesis_1)
  (h2 : hypothesis_2) :
  conclusion := by
  -- Step 1: Description
  step1
  -- Step 2: Description
  step2
  -- QED
  done

-- Unit test
example : your_theorem_name example_input = expected_output := by
  rfl

end GIP.YourModule
```

## Adding New Axioms

### Requirements
1. **Justification** - Why is this axiom necessary?
2. **Minimality** - Can it be derived from existing axioms?
3. **Consistency** - Does it contradict existing axioms?
4. **Documentation** - Clear explanation of meaning

### Template
```lean
/-- Detailed explanation of axiom necessity and meaning -/
axiom axiom_name (parameters) : Type

/-- Example usage showing why axiom is needed -/
example : usage_of_axiom := by
  apply axiom_name
```

## Documentation Requirements

### Code Documentation
- Every public theorem needs a docstring
- Complex proofs need step-by-step comments
- Non-obvious tactics need explanation

### File Documentation
Each file should have a header:
```lean
/-
Copyright (c) 2025 GIP Contributors. All rights reserved.

File: ModuleName.lean
Author(s): [Names]
Description: [What this module provides]
-/
```

### External Documentation
- Theory changes → Update docs/THEORY.md
- New predictions → Update relevant Predictions/*.lean
- API changes → Update README.md
- Status changes → Update STATUS.md

## Commit Guidelines

### Commit Messages
```
type: brief description (max 50 chars)

Longer explanation if needed (wrap at 72 chars)

Fixes: #issue-number (if applicable)
```

Types:
- `feat`: New feature or theorem
- `fix`: Bug fix or sorry resolution
- `docs`: Documentation changes
- `refactor`: Code restructuring
- `test`: Test additions/changes
- `chore`: Build/maintenance tasks

### Examples
```
feat: prove zero object duality theorem

Establishes that empty object is both initial and
terminal, making it a zero object in category theory.

Fixes: #23
```

```
fix: resolve funext type mismatch in Bayesian

Corrected function extensionality application to match
expected type signature.
```

## Pull Request Process

1. **Create feature branch**
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make changes following standards**

3. **Run tests**
   ```bash
   lake build
   ./scripts/test.sh (if exists)
   ```

4. **Check metrics**
   ```bash
   grep -r "sorry" Gip/ --include="*.lean" | wc -l
   ```

5. **Update documentation**

6. **Submit PR with**:
   - Clear description of changes
   - Test results
   - Sorry count before/after
   - Related issue numbers

## Current Priorities

See [STATUS.md](STATUS.md) for current issues and priorities:

1. **P0 - Critical**: Fix BayesianIsomorphism.lean build error
2. **P1 - High**: Resolve 49 sorrys
3. **P2 - Medium**: Documentation updates
4. **P3 - Low**: Code organization improvements

## Architecture Principles

### Separation of Concerns
- **Core**: Basic objects and morphisms
- **Theory**: Mathematical theorems
- **Predictions**: Testable implications
- **Tests**: Verification code

### Dependency Management
- Minimize Mathlib dependencies
- Document why each import is needed
- Prefer local definitions when simple

### Performance Considerations
- Avoid deep recursion in proofs
- Use efficient tactics (`simp` sparingly)
- Profile slow builds with `lake build --verbose`

## Getting Help

### Resources
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

### Project-Specific
- Check STATUS.md for current state
- Review docs/THEORY.md for theoretical background
- See existing code for patterns and examples

## License

By contributing, you agree that your contributions will be licensed under the same terms as the project.

## Code of Conduct

- Be respectful and constructive
- Focus on mathematical correctness
- Help others learn and improve
- Credit sources and collaborators

Thank you for contributing to GIP!