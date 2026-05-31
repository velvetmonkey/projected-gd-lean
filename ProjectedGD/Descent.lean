/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import ProjectedGD.Projection

/-!
# Projected Gradient Descent – Per-step descent

We prove the per-step distance decrease for projected gradient descent:

  `‖x_{k+1} − x*‖² ≤ ‖x_k − x*‖² − (2/L)(f(x_k) − f(x*))`

under the assumptions that `f` is convex and L-smooth, `x*` is a global minimizer
with `∇f(x*) = 0`, and `x* ∈ C`.

## Main results

* `ProjectedGD.norm_sq_proj_sub_le` – per-step distance decrease.
-/

open scoped InnerProductSpace

namespace ProjectedGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)

/-
The squared distance from the gradient step to `x*` expands as:
    `‖(x − α∇f(x)) − x*‖² = ‖x − x*‖² − 2α⟨∇f(x), x − x*⟩ + α²‖∇f(x)‖²`.
-/
omit [CompleteSpace E] in
lemma grad_step_norm_sq (x xstar : E) (grad_x : E) (α : ℝ) :
    ‖(x - α • grad_x) - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * α * @inner ℝ E _ grad_x (x - xstar) +
        α ^ 2 * ‖grad_x‖ ^ 2 := by
  rw [show x - α • grad_x - xstar = (x - xstar) - α • grad_x by abel1, @norm_sub_sq ℝ]
  rw [norm_smul, mul_pow, inner_smul_right]; norm_num; ring_nf
  rw [real_inner_comm]

/-
**Per-step distance decrease for PGD.**

Given:
* `f` is convex: `∀ x y, f(y) ≥ f(x) + ⟨∇f(x), y − x⟩`
* `f` is L-smooth, with the *interpolation inequality*:
  `∀ x, ⟨∇f(x), x − x*⟩ ≥ f(x) − f(x*) + (1/(2L))‖∇f(x)‖²`
  (This holds when `f` is convex, L-smooth, and `∇f(x*) = 0`.)
* `α = 1/L`
* `x* ∈ C`

Then: `‖x_{k+1} − x*‖² ≤ ‖x_k − x*‖² − (2/L)(f(x_k) − f(x*))`.
-/
theorem norm_sq_pgd_descent
    (f : E → ℝ) (grad : E → E) (L : ℝ) (hL : 0 < L)
    (xstar : E) (hxstar_mem : xstar ∈ C)
    -- interpolation inequality (consequence of convexity + L-smoothness + ∇f(x*) = 0)
    (h_interp : ∀ x : E,
      @inner ℝ E _ (grad x) (x - xstar) ≥ f x - f xstar + (1 / (2 * L)) * ‖grad x‖ ^ 2)
    (x : E) :
    ‖projConvex hne hclosed hconv (x - (1 / L) • grad x) - xstar‖ ^ 2 ≤
      ‖x - xstar‖ ^ 2 - (2 / L) * (f x - f xstar) := by
  -- By proj_nonexpansive (and proj_fixed for x*):
  have h_proj_nonexpansive : ‖projConvex hne hclosed hconv (x - (1 / L) • grad x) - xstar‖ ^ 2 ≤ ‖(x - (1 / L) • grad x) - xstar‖ ^ 2 := by
    have := proj_nonexpansive hne hclosed hconv ( x - ( 1 / L ) • grad x ) xstar;
    rw [ show projConvex hne hclosed hconv xstar = xstar from proj_fixed hne hclosed hconv hxstar_mem ] at this ; gcongr;
  convert h_proj_nonexpansive.trans _ using 1;
  convert grad_step_norm_sq x xstar ( grad x ) ( 1 / L ) |> le_of_eq |> le_trans <| ?_ using 1 ; ring_nf at * ; norm_num at *;
  ring_nf at *; nlinarith [ h_interp x, inv_pos.2 hL ] ;

end ProjectedGD