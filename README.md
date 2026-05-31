# projected-gd-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ProjectedGD)
[![Zenodo](https://img.shields.io/badge/Zenodo-10.5281%2Fzenodo.20475662-blue)](https://zenodo.org/records/20475662)

**projected-gd-lean: Formal Proofs of Projected Gradient Descent Convergence in Lean 4**

Lean 4 formal proofs of projected gradient descent on a closed convex constraint set: nonexpansiveness of the metric projection, a per-step distance decrease, and an O(1/k) averaged convergence rate.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

Unconstrained gradient descent walks freely; *projected* gradient descent must stay inside a feasible set C — after each gradient step it projects back onto C with the metric (nearest-point) projection Π_C. The projection is what makes constrained optimisation tractable, and the entire convergence theory rests on one geometric fact: Π_C is **nonexpansive**, so projecting can only bring iterates closer to the optimum, never further. This library machine-checks that fact and rides it to the classical O(1/k) rate for smooth convex objectives.

## Setting

A real Hilbert space `E` (`InnerProductSpace ℝ E`, `CompleteSpace E`), with C ⊆ E nonempty, closed, and convex, an L-smooth convex objective f, and a constant step size α = 1/L. The metric projection `projConvex` is built from Mathlib's `exists_norm_eq_iInf_of_complete_convex` and characterised by the variational inequality ⟨u − Π_C(u), w − Π_C(u)⟩ ≤ 0 for all w ∈ C.

## Key hypothesis

Smoothness and convexity enter through a single **interpolation inequality**:

```
⟨∇f(x), x − x*⟩ ≥ f(x) − f(x*) + (1/(2L))·‖∇f(x)‖²
```

This is equivalent to f being convex and L-smooth with ∇f(x*) = 0 (the standard Nesterov / Taylor et al. formulation), and it cleanly encapsulates both properties in the form the descent argument needs.

## Main results

- **Firm nonexpansiveness of the projection:** ‖Π(x) − Π(y)‖² ≤ ⟨Π(x) − Π(y), x − y⟩, hence ‖Π_C(x) − Π_C(y)‖ ≤ ‖x − y‖.
- **Per-step distance decrease:**
  ```
  ‖x_{k+1} − x*‖² ≤ ‖x_k − x*‖² − (2/L)(f(x_k) − f(x*))
  ```
- **O(1/k) averaged convergence:** there exists i < k with f(x_i) − f(x*) ≤ L‖x₀ − x*‖²/(2k).

## Project structure

```
ProjectedGD/
├── Defs.lean        — projConvex (metric projection), proj_variational, proj_fixed,
│                      pgdStep / pgdSeq
├── Projection.lean  — proj_firm_nonexpansive, proj_nonexpansive
├── Descent.lean     — grad_step_norm_sq, norm_sq_pgd_descent (per-step decrease)
└── Convergence.lean — pgd_telescoping_sum, pgd_convergence (O(1/k) rate)
ProjectedGD.lean     — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `proj_firm_nonexpansive` | ‖Π(x)−Π(y)‖² ≤ ⟨Π(x)−Π(y), x−y⟩ (firm nonexpansiveness) |
| 2 | `proj_nonexpansive` | ‖Π_C(x) − Π_C(y)‖ ≤ ‖x − y‖ |
| 3 | `grad_step_norm_sq` | ‖(x−α∇f(x))−x*‖² = ‖x−x*‖² − 2α⟨∇f(x),x−x*⟩ + α²‖∇f(x)‖² |
| 4 | `norm_sq_pgd_descent` | ‖x_{k+1}−x*‖² ≤ ‖x_k−x*‖² − (2/L)(f(x_k)−f(x*)) |
| 5 | `pgd_telescoping_sum` | Σ_{i<k} (f(x_i)−f(x*)) ≤ (L/2)‖x₀−x*‖² |
| 6 | `pgd_convergence` | ∃ i < k, f(x_i)−f(x*) ≤ L‖x₀−x*‖²/(2k) — O(1/k) |

## Design note

The per-step descent is stated in **function-gap form** — ‖x_{k+1}−x*‖² ≤ ‖x_k−x*‖² − (2/L)(f(x_k)−f(x*)) — rather than the gradient-norm form −α(2−αL)‖∇f(x_k)‖². The gradient-norm form is **not** correct in general for the projected case with arbitrary L: the coefficient α(2−αL) does not match what co-coercivity yields once a projection step is interposed. The function-gap form is mathematically stronger and is exactly what telescopes into the O(1/k) bound, so it is the form proved here.

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

**projected-gd-lean: Formal Proofs of Projected Gradient Descent Convergence in Lean 4**
Ben Cassie (2026). Companion paper: [paper.md](paper.md).

DOI: https://doi.org/10.5281/zenodo.20475662

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence (O(1/k) rate)
- [nesterov-lean](https://github.com/velvetmonkey/nesterov-lean) — Lean 4 Nesterov accelerated gradient descent (O(1/k²) rate)
- [proximal-gd-lean](https://github.com/velvetmonkey/proximal-gd-lean) — Lean 4 proximal gradient descent for composite objectives (O(1/k) rate)
- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences (O(1/√K) rate)

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
