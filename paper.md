# projected-gd-lean: Formal Proofs of Projected Gradient Descent Convergence in Lean 4

Ben Cassie  
2026

## Abstract

`projected-gd-lean` is a Lean 4 / Mathlib library formalising projected gradient descent over a closed convex feasible set in a real Hilbert space. The library constructs the metric projection onto a nonempty closed convex set, proves firm nonexpansiveness and nonexpansiveness, verifies a per-step projected-gradient distance decrease, and derives the classical `O(1/k)` convergence guarantee for smooth convex optimisation. The development contains zero `sorry`, zero `admit`, and uses standard Lean/Mathlib axioms only. It contributes a checked constrained-optimisation component for the broader Lean ecosystem of gradient methods, Bregman methods, proximal methods, and learning-theoretic stability arguments.

## 1. Introduction

Projected gradient descent is the canonical extension of gradient descent to constrained convex optimisation. An unconstrained gradient step may leave the feasible set. Projected gradient descent repairs this by applying the nearest-point projection onto the constraint set after each step:

```text
x_{k+1} = Pi_C(x_k - (1/L) grad f(x_k)).
```

The proof of convergence depends on two ingredients. The first is the geometry of projection onto a closed convex set. Projection is nonexpansive, and in fact firmly nonexpansive. The second is a smooth-convex interpolation inequality that turns gradient information into function decrease relative to an optimum.

The formal setting is a real Hilbert space `E`, expressed in Lean through `InnerProductSpace R E` and `CompleteSpace E`. The feasible set `C` is nonempty, closed, and convex. The metric projection is constructed from Mathlib's nearest-point projection existence theorem for complete convex sets. The objective `f` is smooth and convex in the first-order sense needed by the descent proof, with a minimiser `xstar` satisfying `grad f(xstar) = 0`.

The key analytic hypothesis is the interpolation inequality

```text
<grad f(x), x - x*> >=
  f(x) - f(x*) + (1 / (2L)) ||grad f(x)||^2.
```

This single condition packages convexity, smoothness, and optimality in exactly the form used by the proof. The library then proves

```text
||x_{k+1} - x*||^2 <=
  ||x_k - x*||^2 - (2/L)(f(x_k) - f(x*)).
```

Summing this inequality gives the `O(1/k)` guarantee that some iterate among the first `k` has small function gap.

## 2. Library Overview

The project is organised into four implementation modules plus a root import file:

- `ProjectedGD/Defs.lean` defines `projConvex` using Mathlib's projection existence theorem, proves `proj_variational` and `proj_fixed`, and defines `pgdStep` and `pgdSeq`.
- `ProjectedGD/Projection.lean` proves firm nonexpansiveness and nonexpansiveness of the projection.
- `ProjectedGD/Descent.lean` proves the gradient-step algebra and the per-step projected-gradient descent inequality.
- `ProjectedGD/Convergence.lean` proves the telescoping sum and the final `O(1/k)` convergence result.
- `ProjectedGD.lean` is the root module importing the library.

The project depends on Lean `v4.28.0` and Mathlib `v4.28.0`.

The projection API is intentionally geometric. `projConvex` returns a point of `C` minimising the distance from a given point. `proj_variational` gives the Hilbert-space variational inequality that characterises the projection. `proj_fixed` states that points already in `C` project to themselves.

The projected-gradient sequence is then defined by composing an ordinary gradient step with this projection. This separates the constrained geometry from the analytic descent argument.

## 3. Theorem Inventory

The source contains six headline results, organised into three layers.

### Layer 1 - Projection Properties

1. `proj_firm_nonexpansive` — Projection onto a closed convex set is firmly nonexpansive:

```text
||Pi(x) - Pi(y)||^2 <= <Pi(x) - Pi(y), x - y>.
```

Firm nonexpansiveness is stronger than ordinary nonexpansiveness and is the natural Hilbert-space projection theorem.

2. `proj_nonexpansive` — Projection is nonexpansive:

```text
||Pi_C(x) - Pi_C(y)|| <= ||x - y||.
```

This follows from firm nonexpansiveness and Cauchy-Schwarz.

### Layer 2 - Descent

3. `grad_step_norm_sq` — The algebraic expansion of a gradient step:

```text
||(x - alpha grad_x) - x*||^2 =
  ||x - x*||^2 - 2 alpha <grad_x, x - x*> + alpha^2 ||grad_x||^2.
```

4. `norm_sq_pgd_descent` — The projected-gradient distance decrease:

```text
||x_{k+1} - x*||^2 <=
  ||x_k - x*||^2 - (2/L)(f(x_k) - f(x*)).
```

This is the central one-step theorem.

### Layer 3 - Convergence

5. `pgd_telescoping_sum` — Summing the per-step inequality gives

```text
sum_{i<k} (f(x_i) - f(x*)) <= (L/2) ||x_0 - x*||^2.
```

6. `pgd_convergence` — The final convergence theorem:

```text
exists i < k,
  f(x_i) - f(x*) <= L ||x_0 - x*||^2 / (2k).
```

This is the standard `O(1/k)` projected-gradient guarantee for the best iterate among the first `k`.

## 4. Key Technical Highlights

### Interpolation Inequality

The library uses the interpolation inequality rather than separate convexity and smoothness hypotheses. This is a standard formulation in smooth convex optimisation: for an `L`-smooth convex function with minimiser `x*`, the gradient inner product controls both the function gap and a gradient-norm term.

Formally, this keeps the descent proof compact. The theorem that matters to projected GD is not smoothness in isolation but exactly the inequality that cancels the gradient-norm term appearing in the squared-step expansion.

### Firm Nonexpansiveness

Nonexpansiveness says projection does not increase distance. Firm nonexpansiveness gives a sharper inner-product inequality. In the Lean development, the variational characterisation of projection is used twice, once for each projected point, and the resulting inequalities combine to prove the firm form.

This result is reusable beyond projected gradient descent. It is also the model for the firm nonexpansiveness of proximal operators in the proximal-gradient library.

### Function-Gap Descent

The per-step descent theorem is stated in function-gap form, not in the unconstrained gradient-norm form. This distinction matters. After a projection step, the iterate displacement is not simply the negative gradient direction. The clean theorem is

```text
distance_next^2 <= distance_now^2 - (2/L) gap_now.
```

This is exactly the form that telescopes into convergence.

### Telescoping to `O(1/k)`

The distance decrease has a non-negative left side and a gap term on the right. Summing over `i < k` cancels the distance differences and bounds the total gap by the initial distance. If every gap were larger than the average bound, the sum would be too large. Therefore at least one iterate satisfies the stated `O(1/k)` guarantee.

## 5. Relation to Sibling Libraries

`gradient-descent-lean` has DOI `10.5281/zenodo.20472996` and handles the unconstrained case. `projected-gd-lean` adds the projection operator and the geometry needed to stay in a feasible set.

`nesterov-lean` has DOI `10.5281/zenodo.20474481` and proves an accelerated `O(1/k^2)` deterministic rate. Projected gradient descent is the simpler `O(1/k)` baseline for constrained smooth convex optimisation.

`proximal-gd-lean` generalises projection: projection onto `C` is the proximal operator of the indicator function of `C`. `projected-gd-lean` is therefore the constrained special case of the composite-objective framework.

`mirror-descent-lean` generalises the projection geometry further. Its Bregman projection replaces Euclidean projection and lets the update adapt to non-Euclidean feasible geometry.

## 6. AI Safety Significance

Constrained optimisation is central to safe system design. Constraints encode resource limits, safety envelopes, admissible policies, trust regions, and invariants that should not be violated by an update. Projected gradient descent is the simplest mathematical model of optimisation that respects a feasible set.

A formal proof makes clear which assumptions support the guarantee: closed convex feasibility, existence of projection, the interpolation inequality, positive smoothness scale, and the correct projected update. If any of these assumptions fails, the theorem cannot be applied.

The library does not validate any deployed optimiser. It supplies a verified constrained-optimisation component that can be used in later formal models of safe policy updates, constrained learning, and projected dynamics.

## 7. Conclusion

`projected-gd-lean` formalises the convergence spine of projected gradient descent in Lean 4. It constructs metric projection onto a closed convex set, proves its firm nonexpansiveness, derives the per-step distance decrease, and telescopes that inequality to an `O(1/k)` convergence guarantee. The result is a compact, importable constrained-optimisation artifact for the Lean ecosystem.

## References

Nesterov, Y. (2004). *Introductory Lectures on Stochastic Optimization*. Springer.

Bauschke, H. H. and Combettes, P. L. (2011). *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*. Springer.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

Cassie, B. (2026). *nesterov-lean: Formal Proofs of Nesterov Accelerated Gradient Descent in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20474481>

