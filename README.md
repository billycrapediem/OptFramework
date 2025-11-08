# OptFramework

A formal verification library for optimization algorithms built in [Lean 4](https://lean-lang.org/). This project provides a rigorous mathematical framework for grouping different optimization algorithms into simple, unified frameworks and formally proving their convergence properties and optimality.

## Overview

OptFramework takes a **framework-based approach** to optimization theory: instead of analyzing algorithms in isolation, we identify general algorithmic frameworks and show that specific algorithms are instantiations of these frameworks. 


## Dependencies

This library builds on top of [Optlib](https://github.com/optsuite/optlib)

## Installation

1. **Install Lean 4**: Follow instructions at [leanprover.github.io](https://leanprover.github.io/lean4/doc/setup.html)

2. **Clone the repository**:
```bash
git clone https://github.com/yourusername/OptFramework.git
cd OptFramework
```

3. **Build the project**:
```bash
lake build
```

## References

## Acknowledgments

Built with Lean 4 and inspired by the formal verification community's work in making mathematics more rigorous and reliable.

---

**Note**: This is an active research project. Proofs are under continuous development and refinement. Some theorems may contain `sorry` placeholders during development.
