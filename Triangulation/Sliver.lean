/-
Why a triangulation that must preserve its boundary cannot also bound its aspect ratio,
once the boundary comes too close to itself.

`interactor-triangulation` asserts two properties of every mesh it returns: every input
boundary vertex survives, and no triangle has an aspect ratio past a bound. Google FuzzTest
found an input where they cannot both hold -- a hexagon whose edge 0-1 passes within 7e-6 of
edge 4-5 while every pair of its *vertices* is at least 8.9 apart. The remesher is right to
refuse: collapsing the offending edge would weld two distinct stretches of the boundary
together, which breaks boundary preservation and pinches the surface.

What follows is the reason, and it fixes the constant. `aspect_le_ratio` says the aspect ratio
of a triangle is at least its longest edge over its shortest, so a bound `R` on the ratio is a
lower bound `maxEdge / R` on every edge length. A boundary that forces two mesh vertices
closer than that admits no triangulation meeting the bound, whatever the mesher does.

The threshold is therefore derived rather than measured, which matters: it is the reason the
library returns a status instead of a mesh nobody can use.
-/
import Mathlib

namespace Contract.Triangulation

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Twice the area of the triangle spanned by `u` and `v`, as the Gram determinant.

    In 3D this is `‖u × v‖`; written this way it needs no cross product, so it holds in any
    real inner product space and the proofs below are about the geometry rather than about
    a coordinate system. -/
noncomputable def twiceArea (u v : E) : ℝ :=
  Real.sqrt (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2)

lemma twiceArea_nonneg (u v : E) : 0 ≤ twiceArea u v :=
  Real.sqrt_nonneg _

/-- **The Cauchy-Schwarz slack.** Twice the area never exceeds the product of two edges.

    This is the whole mechanism: the area of a triangle with a short edge is small no matter
    how long the other edges are, because the short edge is one of the two factors. -/
lemma twiceArea_le_mul (u v : E) : twiceArea u v ≤ ‖u‖ * ‖v‖ := by
  rw [twiceArea]
  have h : ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    have : (0:ℝ) ≤ ⟪u, v⟫ ^ 2 := sq_nonneg _
    nlinarith [this]
  calc Real.sqrt (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2)
      ≤ Real.sqrt ((‖u‖ * ‖v‖) ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖u‖ * ‖v‖ := Real.sqrt_sq (by positivity)

/-- The area does not depend on which corner the two edge vectors are taken from.

    Needed because the argument picks the corner that the shortest edge touches, and the
    aspect ratio is defined from the triangle rather than from a choice of corner. -/
lemma twiceArea_shift (u v : E) : twiceArea (v - u) (-u) = twiceArea u v := by
  unfold twiceArea
  congr 1
  simp only [norm_neg, inner_neg_right, inner_sub_left, norm_sub_sq_real,
    real_inner_self_eq_norm_sq, real_inner_comm v u]
  ring

lemma twiceArea_comm (u v : E) : twiceArea u v = twiceArea v u := by
  unfold twiceArea
  congr 1
  rw [real_inner_comm u v]
  ring

/-- The three corners give three bounds; the argument needs whichever one the shortest
    edge appears in. -/
lemma twiceArea_le_mul' (u v : E) : twiceArea u v ≤ ‖v - u‖ * ‖u‖ := by
  have := twiceArea_le_mul (v - u) (-u)
  rwa [twiceArea_shift, norm_neg] at this

/-- The edge lengths of the triangle with a corner at the origin and the other two at `u`, `v`. -/
noncomputable def edges (u v : E) : Finset ℝ := {‖u‖, ‖v‖, ‖v - u‖}

omit [InnerProductSpace ℝ E] in
lemma norm_mem_edges_left (u v : E) : ‖u‖ ∈ edges u v := by simp [edges]

omit [InnerProductSpace ℝ E] in
lemma norm_mem_edges_right (u v : E) : ‖v‖ ∈ edges u v := by simp [edges]

/-- **Twice the area is at most the shortest edge times the longest.**

    Cauchy-Schwarz applied at the corner the shortest edge touches. Every corner gives a bound
    `twiceArea ≤ (one edge) * (another edge)`; taking the corner the shortest edge touches makes
    one factor minimal, and the other is at most the longest. -/
lemma twiceArea_le_min_mul_max (u v : E) {lo hi : ℝ}
    (hhi : ∀ e ∈ edges u v, e ≤ hi) (hmin : lo ∈ edges u v) :
    twiceArea u v ≤ lo * hi := by
  have hu := norm_mem_edges_left u v
  have hv := norm_mem_edges_right u v
  have hmem := hmin
  simp only [edges, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hlo0 : 0 ≤ lo := by rcases hmem with h | h | h <;> rw [h] <;> exact norm_nonneg _
  rcases hmem with h | h | h
  · calc twiceArea u v ≤ ‖u‖ * ‖v‖ := twiceArea_le_mul u v
      _ = lo * ‖v‖ := by rw [h]
      _ ≤ lo * hi := mul_le_mul_of_nonneg_left (hhi _ hv) hlo0
  · calc twiceArea u v ≤ ‖v‖ * ‖u‖ := by rw [twiceArea_comm]; exact twiceArea_le_mul v u
      _ = lo * ‖u‖ := by rw [h]
      _ ≤ lo * hi := mul_le_mul_of_nonneg_left (hhi _ hu) hlo0
  · calc twiceArea u v ≤ ‖v - u‖ * ‖u‖ := twiceArea_le_mul' u v
      _ = lo * ‖u‖ := by rw [h]
      _ ≤ lo * hi := mul_le_mul_of_nonneg_left (hhi _ hu) hlo0

/-- The aspect ratio the property test asserts: longest edge squared over twice the area. -/
noncomputable def aspect (u v : E) (hi : ℝ) : ℝ := hi ^ 2 / twiceArea u v

/-- **The theorem.** A triangle's aspect ratio is at least its longest edge over its shortest.

    So a bound on the aspect ratio is a lower bound on edge length, which is the fact the
    library's input validation is built on. -/
theorem le_aspect (u v : E) {lo hi : ℝ}
    (hhi : ∀ e ∈ edges u v, e ≤ hi) (hmin : lo ∈ edges u v)
    (hlo_pos : 0 < lo) (harea : 0 < twiceArea u v) :
    hi / lo ≤ aspect u v hi := by
  have hhi_pos : 0 < hi := lt_of_lt_of_le hlo_pos (hhi lo hmin)
  have hbound : twiceArea u v ≤ lo * hi := twiceArea_le_min_mul_max u v hhi hmin
  rw [aspect, div_le_iff₀ hlo_pos, div_mul_eq_mul_div, le_div_iff₀ harea]
  nlinarith [hbound, hhi_pos]

/-- **The corollary that fixes the constant.**

    If every triangle must have aspect ratio below `R`, then every edge is longer than
    `maxEdge / R`. A boundary that forces two mesh vertices closer than that admits no
    triangulation meeting the bound, so the input is the thing to reject. -/
theorem edge_lower_bound_of_aspect_lt (u v : E) {lo hi R : ℝ}
    (hhi : ∀ e ∈ edges u v, e ≤ hi) (hmin : lo ∈ edges u v)
    (hlo_pos : 0 < lo) (harea : 0 < twiceArea u v)
    (hR : aspect u v hi < R) : hi / R < lo := by
  have hhi_pos : 0 < hi := lt_of_lt_of_le hlo_pos (hhi lo hmin)
  have h : hi / lo ≤ aspect u v hi := le_aspect u v hhi hmin hlo_pos harea
  have hlt : hi / lo < R := lt_of_le_of_lt h hR
  have hR_pos : 0 < R := lt_trans (div_pos hhi_pos hlo_pos) hlt
  rw [div_lt_iff₀ hlo_pos] at hlt
  rw [div_lt_iff₀ hR_pos]
  linarith [hlt]

end Contract.Triangulation
