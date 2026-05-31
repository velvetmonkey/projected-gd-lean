/-
Copyright (c) 2025. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import ProjectedGD.Defs

/-!
# Projected Gradient Descent – Projection properties

This file proves that the metric projection onto a nonempty closed convex subset
of a real Hilbert space is **nonexpansive**:

  `‖Π_C(x) − Π_C(y)‖ ≤ ‖x − y‖`

## Main results

* `ProjectedGD.proj_firm_nonexpansive` — firm nonexpansiveness (inner product form).
* `ProjectedGD.proj_nonexpansive` — nonexpansiveness of the metric projection.
-/

open scoped InnerProductSpace

namespace ProjectedGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)

/-
**Firm nonexpansiveness (inner-product form).**
`⟪Π(x) − Π(y), x − y⟫ ≥ ‖Π(x) − Π(y)‖²`.

This is the key intermediate step from which plain nonexpansiveness follows
by Cauchy–Schwarz.
-/
theorem proj_firm_nonexpansive (x y : E) :
    ‖projConvex hne hclosed hconv x - projConvex hne hclosed hconv y‖ ^ 2 ≤
      @inner ℝ E _ (projConvex hne hclosed hconv x - projConvex hne hclosed hconv y)
                    (x - y) := by
  set px := projConvex hne hclosed hconv x
  set py := projConvex hne hclosed hconv y
  -- Variational inequalities
  have h1 : @inner ℝ E _ (x - px) (py - px) ≤ 0 :=
    proj_variational hne hclosed hconv x (proj_mem hne hclosed hconv y)
  have h2 : @inner ℝ E _ (y - py) (px - py) ≤ 0 :=
    proj_variational hne hclosed hconv y (proj_mem hne hclosed hconv x)
  -- We need: ⟨px - py, x - y⟩ ≥ ‖px - py‖²
  -- From h1: ⟨x - px, py - px⟩ ≤ 0, i.e., ⟨px - x, px - py⟩ ≤ 0
  -- From h2: ⟨y - py, px - py⟩ ≤ 0, i.e., ⟨py - y, py - px⟩ ≤ 0
  -- Sum:  ⟨(px - x) + (py - y), px - py⟩ ≤ 0  ... wait, need to be more careful.
  -- h1 says: ⟨x - px, py - px⟩ ≤ 0
  -- h2 says: ⟨y - py, px - py⟩ ≤ 0
  -- Negate h2: ⟨y - py, py - px⟩ ≥ 0  (flip second argument sign)
  -- Actually: ⟨y - py, px - py⟩ = -⟨y - py, py - px⟩ ... no.
  -- Let me just rearrange.
  -- h1: ⟨x - px, py - px⟩ ≤ 0  ⟹  ⟨x - px, -(px - py)⟩ ≤ 0  ⟹  ⟨x - px, px - py⟩ ≥ 0
  -- h2: ⟨y - py, px - py⟩ ≤ 0  ⟹  ⟨y - py, -(py - px)⟩ ≤ 0  ... same thing.
  -- h2: ⟨y - py, px - py⟩ ≤ 0
  -- Add h1 and -h2:
  -- Actually let's just be direct. We want ⟨px-py, x-y⟩ ≥ ‖px-py‖².
  -- Write x - y = (x - px) + (px - py) + (py - y).
  -- ⟨px-py, x-y⟩ = ⟨px-py, x-px⟩ + ‖px-py‖² + ⟨px-py, py-y⟩
  -- = -⟨x-px, py-px⟩ + (stuff) ... this gets messy.
  -- Let me just have the subagent prove it.
  simp_all +decide [ inner_sub_left, inner_sub_right ];
  simp_all +decide [ real_inner_comm, norm_sub_pow_two_real ];
  linarith

/-
The metric projection onto a nonempty closed convex set is **nonexpansive**:
    `‖Π_C(x) − Π_C(y)‖ ≤ ‖x − y‖`.
-/
theorem proj_nonexpansive (x y : E) :
    ‖projConvex hne hclosed hconv x - projConvex hne hclosed hconv y‖ ≤ ‖x - y‖ := by
  -- From firm nonexpansiveness: ‖px-py‖² ≤ ⟨px-py, x-y⟩ ≤ ‖px-py‖·‖x-y‖ (Cauchy-Schwarz)
  -- So ‖px-py‖ ≤ ‖x-y‖.
  -- By Cauchy-Schwarz: ⟨px - py, x - y⟩ ≤px - py‖ · ‖x - y‖ (use real_inner_le_norm or abs_inner_le_norm).
  have h_cauchy_schwarz : ∀ (u v : E), @inner ℝ E _ u v ≤ ‖u‖ * ‖v‖ := by
    exact fun u v => real_inner_le_norm u v;
  contrapose! h_cauchy_schwarz with h;
  refine' ⟨ projConvex hne hclosed hconv x - projConvex hne hclosed hconv y, x - y, _ ⟩;
  refine' lt_of_lt_of_le _ ( proj_firm_nonexpansive hne hclosed hconv x y );
  rw [ sq ] ; gcongr ; exact lt_of_le_of_lt ( norm_nonneg _ ) h

end ProjectedGD