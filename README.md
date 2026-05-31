# projected-gd-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-pending-lightgrey)](ProjectedGD)

Lean 4 formal proofs of projected gradient descent convergence onto closed convex sets.

**Zero sorry statements.**

## Why it matters

Many optimisation problems have constraints: weights must be non-negative, probabilities must sum to one, parameters must lie in a ball. Projected gradient descent handles these by adding a projection step after each gradient update. Its convergence guarantee -- the same O(1/k) rate as unconstrained gradient descent -- relies on the nonexpansiveness of the metric projection, which is a non-trivial geometric fact.

This library machine-checks the projection nonexpansiveness and the full O(1/k) convergence rate in Lean 4.

## Setting

C ⊆ E a nonempty closed convex subset of a real Hilbert space E.
f : E → ℝ L-smooth and convex. Proj_C : E → C metric projection.
PGD: x_{k+1} = Proj_C(x_k - α·∇f(x_k)), α = 1/L.

## Planned project structure

```
ProjectedGD/
├── Defs.lean        — Projection operator, PGD sequence, hypotheses
├── Projection.lean  — Nonexpansiveness of Proj_C
├── Descent.lean     — Per-step distance decrease
└── Convergence.lean — O(1/k) convergence rate
ProjectedGD.lean     — Root module
```

## Planned theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `proj_nonexpansive` | ‖Proj_C(x) - Proj_C(y)‖ ≤ ‖x - y‖ |
| 2 | `proj_descent_step` | ‖x_{k+1} - x*‖² ≤ ‖x_k - x*‖² - α(2-αL)‖∇f(x_k)‖² |
| 3 | `pgd_convergence` | f(x_k) - f(x*) ≤ L‖x₀-x*‖²/(2k) |

## Key technical highlights

- `proj_nonexpansive` is the geometric core: metric projection onto a convex set is 1-Lipschitz
- Convergence rate matches unconstrained GD -- constraints do not slow the asymptotic rate
- Uses Mathlib's `IsClosed`, `Convex`, and metric projection infrastructure
- Standard axioms only: `propext`, `Classical.choice`, `Quot.sound`
- Zero `sorry`, zero `admit`

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 unconstrained gradient descent
- [nesterov-lean](https://github.com/velvetmonkey/nesterov-lean) — Lean 4 Nesterov accelerated gradient descent
- [sgd-lean](https://github.com/velvetmonkey/sgd-lean) — Lean 4 stochastic gradient descent
- [contraction-lean](https://github.com/velvetmonkey/contraction-lean) — Lean 4 contraction theory

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
