/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Projected Gradient Descent – Definitions

This file provides the core definitions for a projected gradient descent (PGD) library
in a real Hilbert space `E`:

* `ProjectedGD.projConvex` – the metric projection onto a nonempty closed convex set.
* `ProjectedGD.pgdSeq` – the PGD iterate sequence  x_{k+1} = Π_C(x_k − α ∇f(x_k)).
* Bundled assumption structures for L-smoothness and convexity.

## Main definitions

* `ProjectedGD.projConvex` : `E → E` — metric (nearest-point) projection onto `C`.
* `ProjectedGD.proj_mem` : the projection lands in `C`.
* `ProjectedGD.proj_dist` : the projection achieves `iInf`.
* `ProjectedGD.proj_variational` : the variational inequality characterising the projection.
* `ProjectedGD.proj_fixed` : points already in `C` are fixed by the projection.
* `ProjectedGD.pgdSeq` : the PGD iteration.
-/

noncomputable section

open scoped InnerProductSpace

namespace ProjectedGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- ============================================================
-- §1  Metric projection onto a nonempty closed convex set
-- ============================================================

variable {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)

/-- The metric projection (nearest-point map) onto a nonempty closed convex subset of a
    real Hilbert space. -/
def projConvex (u : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv u).choose

lemma proj_mem (u : E) : projConvex hne hclosed hconv u ∈ C :=
  (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv u).choose_spec.1

lemma proj_dist (u : E) :
    ‖u - projConvex hne hclosed hconv u‖ = ⨅ w : C, ‖u - w‖ :=
  (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv u).choose_spec.2

/-- Variational inequality: for every `w ∈ C`,
    `⟪u − Π_C(u), w − Π_C(u)⟫ ≤ 0`. -/
lemma proj_variational (u : E) {w : E} (hw : w ∈ C) :
    @inner ℝ E _ (u - projConvex hne hclosed hconv u)
                  (w - projConvex hne hclosed hconv u) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv (proj_mem hne hclosed hconv u)).mp
    (proj_dist hne hclosed hconv u) w hw

/-- If `u ∈ C` then `Π_C(u) = u`. -/
lemma proj_fixed {u : E} (hu : u ∈ C) :
    projConvex hne hclosed hconv u = u := by
  have hmem := proj_mem hne hclosed hconv u
  have hdist := proj_dist hne hclosed hconv u
  -- u achieves distance 0 from itself, and the infimum is ≤ 0
  have h0 : (⨅ w : C, ‖u - w‖) ≤ ‖u - u‖ :=
    ciInf_le (⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ : BddBelow (Set.range (fun w : C => ‖u - w‖))) ⟨u, hu⟩
  rw [sub_self, norm_zero] at h0
  haveI : Nonempty C := hne.to_subtype
  have hge : 0 ≤ ⨅ w : C, ‖u - w‖ := le_ciInf (fun w => norm_nonneg _)
  have : ‖u - projConvex hne hclosed hconv u‖ = 0 := by linarith
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm

-- ============================================================
-- §2  PGD sequence
-- ============================================================

/-- One step of projected gradient descent:
    `pgdStep(x) = Π_C(x − α ∇f(x))`. -/
def pgdStep (grad : E → E) (α : ℝ)
    (proj : E → E) (x : E) : E :=
  proj (x - α • grad x)

/-- The PGD iterate sequence starting from `x₀`. -/
def pgdSeq (grad : E → E) (α : ℝ)
    (proj : E → E) (x₀ : E) : ℕ → E
  | 0     => x₀
  | n + 1 => pgdStep grad α proj (pgdSeq grad α proj x₀ n)

omit [CompleteSpace E] in
lemma pgdSeq_zero (grad : E → E) (α : ℝ) (proj : E → E) (x₀ : E) :
    pgdSeq grad α proj x₀ 0 = x₀ := rfl

omit [CompleteSpace E] in
lemma pgdSeq_succ (grad : E → E) (α : ℝ) (proj : E → E) (x₀ : E) (k : ℕ) :
    pgdSeq grad α proj x₀ (k + 1) =
      proj (pgdSeq grad α proj x₀ k - α • grad (pgdSeq grad α proj x₀ k)) := rfl

end ProjectedGD

end -- noncomputable section
