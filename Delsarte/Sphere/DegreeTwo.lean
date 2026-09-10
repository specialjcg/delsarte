/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Sphere.LP
import Mathlib.Algebra.Order.Chebyshev

/-!
# Schoenberg positivity at degree 2, in every dimension

`Delsarte.Sphere.schoenbergPos_dim_two` settles every degree, but only in the
plane, and by an argument that uses that `S¹` is a group — false for every other
sphere. This file goes the other way: one degree, every dimension, by an argument
that has nothing special about it and therefore says something about the general
case.

## The argument

Write `A a b = ∑_i x i a * x i b`, the second moment matrix of the configuration.
Two facts, both elementary:

* `∑_(i,j) ⟪x i, x j⟫ ^ 2 = ∑_(a,b) A a b ^ 2` — expand both sides into the same
  quadruple sum;
* `∑_a A a a = M`, because each point is a unit vector.

Cauchy-Schwarz against the constant vector gives `M ^ 2 = (∑_a A a a) ^ 2 ≤ d *
∑_a A a a ^ 2`, and the diagonal terms are part of the full sum, so

`M ^ 2 ≤ d * ∑_(i,j) ⟪x i, x j⟫ ^ 2`.

Since `G_2 t = (d t ^ 2 - 1) / (d - 1)`, that inequality *is* the statement
`∑_(i,j) G_2 ⟪x i, x j⟫ ≥ 0`.

No spherical harmonics, no addition formula, no trace or Frobenius API: the whole
thing is `Finset` manipulation plus `sq_sum_le_card_mul_sum_sq`.

## What it does not do

Degree 2 alone carries no useful certificate — the Odlyzko-Sloane polynomials in
dimensions 8 and 24 have degree 9 and above. This is a load-bearing test of the
architecture, not a step that shortens the road to the kissing number. The
general statement stays open.
-/

namespace Delsarte.Sphere

open Finset Polynomial Delsarte

variable {d M : ℕ}

/-- Swapping two nested pairs of sums. -/
theorem sum_comm_pairs {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, F i j a b
      = ∑ i, ∑ a, ∑ j, ∑ b, F i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, F i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, F i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Closed form of `G_2` as a polynomial. -/
theorem gegenbauerPoly_deg_two (d : ℕ) :
    gegenbauerPoly d 2
      = C ((d : ℚ) / ((d : ℚ) - 1)) * X ^ 2 - C (1 / ((d : ℚ) - 1)) := by
  have h := gegenbauerPoly_add_two d 0
  norm_num at h
  rw [h, one_div]
  ring

/-- Closed form of `G_2` at a real argument. -/
theorem gegenbauerReal_deg_two (d : ℕ) (t : ℝ) :
    gegenbauerReal d 2 t = ((d : ℝ) * t ^ 2 - 1) / ((d : ℝ) - 1) := by
  rw [gegenbauerReal, gegenbauerPoly_deg_two]
  simp only [map_sub, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
  push_cast
  ring

/-- **Schoenberg positivity at degree 2, in every dimension.** -/
theorem schoenbergPos_deg_two (hd : 2 ≤ d) : SchoenbergPos d 2 := by
  intro M c
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  -- The second moment matrix of the configuration.
  set A : Fin d → Fin d → ℝ := fun a b => ∑ i, c.pts i a * c.pts i b with hA
  have h1 : ∀ i j : Fin M, (c.gram i j) ^ 2
      = ∑ a, ∑ b, (c.pts i a * c.pts i b) * (c.pts j a * c.pts j b) := by
    intro i j
    rw [c.gram_eq_sum i j, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h2 : ∀ a b : Fin d, (A a b) ^ 2
      = ∑ i, ∑ j, (c.pts i a * c.pts i b) * (c.pts j a * c.pts j b) := by
    intro a b
    rw [hA, sq, Finset.sum_mul_sum]
  -- The two ways of summing the same quadruple sum.
  have hquad : ∑ i, ∑ j, (c.gram i j) ^ 2 = ∑ a, ∑ b, (A a b) ^ 2 := by
    simp only [h1, h2]
    exact sum_comm_pairs _
  -- Each point is a unit vector, so the trace is the number of points.
  have htr : ∑ a, A a a = (M : ℝ) := by
    simp only [hA]
    rw [Finset.sum_comm]
    have hone : ∀ i : Fin M, ∑ a, c.pts i a * c.pts i a = 1 := by
      intro i
      rw [← c.gram_eq_sum i i, c.gram_self i]
    simp [hone]
  -- Cauchy-Schwarz against the constant vector, then the diagonal is part of the whole.
  have hdiag : ∑ a, (A a a) ^ 2 ≤ ∑ a, ∑ b, (A a b) ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => (A a b) ^ 2) (fun b _ => sq_nonneg _)
        (Finset.mem_univ a)
  have hCS : (M : ℝ) ^ 2 ≤ (d : ℝ) * ∑ a, ∑ b, (A a b) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin d))) (f := fun a => A a a)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [htr] at h
    nlinarith [hdiag, h]
  -- Rewrite the Gegenbauer sum as that same inequality.
  have hval : ∑ i, ∑ j, gegenbauerReal d 2 (c.gram i j)
      = (∑ i, ∑ j, ((d : ℝ) * (c.gram i j) ^ 2 - 1)) / ((d : ℝ) - 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => gegenbauerReal_deg_two d _
  have hnum : ∑ i, ∑ j, ((d : ℝ) * (c.gram i j) ^ 2 - 1)
      = (d : ℝ) * (∑ i, ∑ j, (c.gram i j) ^ 2) - (M : ℝ) ^ 2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    ring
  rw [hval, hnum]
  refine div_nonneg ?_ hd1.le
  rw [hquad]
  linarith [hCS]

/-! ## The positivity is tight

A positivity result that always had slack would mean the Cauchy-Schwarz step threw
something away. It does not: at the orthonormal configuration the sum is exactly
zero.
-/

/-- `d` pairwise orthogonal unit vectors of `ℝ^d`. -/
noncomputable def orthoPoints (d : ℕ) : UnitPoints d d where
  pts := fun i => EuclideanSpace.single i (1 : ℝ)
  norm_pts := fun i => by simp

@[simp]
theorem orthoPoints_gram (d : ℕ) (i j : Fin d) :
    (orthoPoints d).gram i j = if i = j then 1 else 0 := by
  rw [UnitPoints.gram, orthoPoints]
  simp [EuclideanSpace.inner_single_left]

/-- **The degree-2 positivity is attained.** At the orthonormal configuration the
sum is exactly zero, so `schoenbergPos_deg_two` cannot be strengthened to a strict
inequality and the Cauchy-Schwarz step above loses nothing. -/
theorem sum_gegenbauerReal_orthoPoints (hd : 2 ≤ d) :
    ∑ i, ∑ j, gegenbauerReal d 2 ((orthoPoints d).gram i j) = 0 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by intro h; linarith
  have hterm : ∀ i j : Fin d, gegenbauerReal d 2 ((orthoPoints d).gram i j)
      = if i = j then (1 : ℝ) else -1 / ((d : ℝ) - 1) := by
    intro i j
    rw [orthoPoints_gram, gegenbauerReal_deg_two]
    by_cases h : i = j
    · rw [if_pos h, if_pos h]
      field_simp
    · rw [if_neg h, if_neg h]
      norm_num
  have hrow : ∀ i : Fin d, ∑ j : Fin d, gegenbauerReal d 2 ((orthoPoints d).gram i j) = 0 := by
    intro i
    have hsplit : ∀ j : Fin d, (if i = j then (1 : ℝ) else -1 / ((d : ℝ) - 1))
        = -1 / ((d : ℝ) - 1) + (if i = j then 1 - -1 / ((d : ℝ) - 1) else 0) := by
      intro j
      by_cases h : i = j <;> simp [h]
    simp only [hterm, hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  exact Finset.sum_eq_zero fun i _ => hrow i

end Delsarte.Sphere
