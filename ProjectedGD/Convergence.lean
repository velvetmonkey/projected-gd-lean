/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import ProjectedGD.Descent

/-!
# Projected Gradient Descent – O(1/k) convergence

We prove that projected gradient descent converges at rate O(1/k):

  `f(x_k) − f(x*) ≤ L‖x₀ − x*‖² / (2k)`

for some iterate in the first `k` steps.

## Main results

* `ProjectedGD.pgd_telescoping_sum` — telescoping-sum bound on the sum of function gaps.
* `ProjectedGD.pgd_convergence` — O(1/k) convergence rate.
-/

open Finset
open scoped InnerProductSpace

namespace ProjectedGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)

/-- Telescoping sum: the sum of function gaps is bounded.
    `∑_{i=0}^{k-1} (f(x_i) - f(x*)) ≤ L/2 · ‖x₀ - x*‖²` -/
theorem pgd_telescoping_sum
    (f : E → ℝ) (grad : E → E) (L : ℝ) (hL : 0 < L)
    (xstar : E) (hxstar_mem : xstar ∈ C)
    (h_interp : ∀ x : E,
      @inner ℝ E _ (grad x) (x - xstar) ≥ f x - f xstar + (1 / (2 * L)) * ‖grad x‖ ^ 2)
    (x₀ : E)
    (k : ℕ) :
    (∑ i ∈ range k,
      (f (pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ i) - f xstar))
      ≤ (L / 2) * ‖x₀ - xstar‖ ^ 2 := by
  have h_induction : ∀ k, ∑ i ∈ Finset.range k,
      (f (pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ i) - f xstar) ≤
      (L / 2) * (‖x₀ - xstar‖ ^ 2 -
        ‖pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ k - xstar‖ ^ 2) := by
    intro k
    induction' k with k ih
    · simp +decide [pgdSeq]
    · have h_step :
        ‖pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ (k + 1) - xstar‖ ^ 2 ≤
        ‖pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ k - xstar‖ ^ 2 -
          (2 / L) * (f (pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ k) -
            f xstar) := by
        convert norm_sq_pgd_descent hne hclosed hconv f grad L hL xstar hxstar_mem h_interp
          (pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ k) using 1
      rw [Finset.sum_range_succ]
      field_simp at *
      grind +splitIndPred
  exact le_trans (h_induction k)
    (mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity))

/-- **O(1/k) convergence of projected gradient descent.**

There exists an iterate `i < k` such that
  `f(x_i) − f(x*) ≤ L‖x₀ − x*‖² / (2k)`. -/
theorem pgd_convergence
    (f : E → ℝ) (grad : E → E) (L : ℝ) (hL : 0 < L)
    (xstar : E) (hxstar_mem : xstar ∈ C)
    (h_interp : ∀ x : E,
      @inner ℝ E _ (grad x) (x - xstar) ≥ f x - f xstar + (1 / (2 * L)) * ‖grad x‖ ^ 2)
    (x₀ : E) (k : ℕ) (hk : 0 < k) :
    ∃ i, i < k ∧
      f (pgdSeq grad (1 / L) (projConvex hne hclosed hconv) x₀ i) - f xstar ≤
        L * ‖x₀ - xstar‖ ^ 2 / (2 * k) := by
  by_contra h_all
  push_neg at h_all
  have h_tele := pgd_telescoping_sum hne hclosed hconv f grad L hL xstar hxstar_mem
    h_interp x₀ k
  have h_sum_lb := Finset.sum_lt_sum_of_nonempty
    (show (Finset.range k).Nonempty from ⟨_, Finset.mem_range.mpr hk⟩)
    (fun i hi => h_all i (Finset.mem_range.mp hi))
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h_sum_const : ∑ i ∈ Finset.range k, (L * ‖x₀ - xstar‖ ^ 2 / (2 * (k : ℝ))) =
      k * (L * ‖x₀ - xstar‖ ^ 2 / (2 * k)) := by
    simp [Finset.sum_const, Finset.card_range]
  rw [h_sum_const] at h_sum_lb
  have : k * (L * ‖x₀ - xstar‖ ^ 2 / (2 * k)) = L / 2 * ‖x₀ - xstar‖ ^ 2 := by
    field_simp
  linarith

end ProjectedGD
