/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Sphere.LP
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Schoenberg positivity in dimension 2, and an unconditional bound

`Delsarte.Sphere.SchoenbergPos` is a hypothesis in general. In dimension 2 it is
a theorem, and the proof is the circle transcription of the binary argument of
`Delsarte.Hamming.sum_sum_krawtchouk_nonneg`: a sum of squares of *reals*, with
no harmonic analysis.

At `d = 2` the normalized Gegenbauer polynomials are the Chebyshev polynomials
of the first kind (`Delsarte.gegenbauerPoly_dim_two`), and `T_k (cos θ) = cos kθ`.
A unit vector of the plane is `(cos θ, sin θ)`, so `⟪x i, x j⟫ = cos (θ i - θ j)`
and

`∑_(i,j) G_k ⟪x i, x j⟫ = (∑_i cos k θ i) ^ 2 + (∑_i sin k θ i) ^ 2 ≥ 0`.

## Consequence

`card_le_eight` is the first *unconditional* bound of the sphere side: a family
of unit vectors of the plane with pairwise inner products at most `1/2` has at
most 8 members. The true maximum is 6, attained by the regular hexagon, so the
bound is valid and not tight — as a linear programming bound normally is.

Nothing here says anything about dimension 8 or 24. The argument is specific to
the plane: it uses that the sphere `S¹` is a group, which is false for every
other `S^(d-1)` of interest.
-/

namespace Delsarte.Sphere

open Finset Polynomial Delsarte

variable {M : ℕ}

/-- A point of the unit circle is `(cos θ, sin θ)` for some angle. -/
theorem exists_cos_sin {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, show a * a + b * b = 1 by nlinarith]
    exact Real.sqrt_one
  have hz : (⟨a, b⟩ : ℂ) ≠ 0 := by
    intro hc
    rw [hc] at hn
    simp at hn
  refine ⟨Complex.arg ⟨a, b⟩, ?_, ?_⟩
  · rw [Complex.cos_arg hz, hn]; simp
  · rw [Complex.sin_arg, hn]; simp

/-- In dimension 2 the normalized Gegenbauer polynomial is the Chebyshev
polynomial of the first kind, over `ℝ`. -/
theorem gegenbauerReal_dim_two (k : ℕ) (t : ℝ) :
    gegenbauerReal 2 k t = (Chebyshev.T ℝ (k : ℤ)).eval t := by
  rw [gegenbauerReal, gegenbauerPoly_dim_two, aeval_def, eval₂_eq_eval_map, Chebyshev.map_T]

/-- `G_k (cos θ) = cos (k θ)`. -/
theorem gegenbauerReal_dim_two_cos (k : ℕ) (θ : ℝ) :
    gegenbauerReal 2 k (Real.cos θ) = Real.cos (k * θ) := by
  rw [gegenbauerReal_dim_two, Chebyshev.T_real_cos]
  norm_num

namespace UnitPoints

theorem sq_add_sq (c : UnitPoints 2 M) (i : Fin M) :
    (c.pts i 0) ^ 2 + (c.pts i 1) ^ 2 = 1 := by
  have h := c.gram_self i
  rw [gram_eq_sum, Fin.sum_univ_two] at h
  nlinarith [h]

/-- Angles for every point of a planar configuration. -/
theorem exists_angles (c : UnitPoints 2 M) :
    ∃ θ : Fin M → ℝ, ∀ i, c.pts i 0 = Real.cos (θ i) ∧ c.pts i 1 = Real.sin (θ i) := by
  have h : ∀ i, ∃ t : ℝ, c.pts i 0 = Real.cos t ∧ c.pts i 1 = Real.sin t := by
    intro i
    obtain ⟨t, ht0, ht1⟩ := exists_cos_sin (c.sq_add_sq i)
    exact ⟨t, ht0.symm, ht1.symm⟩
  choose θ hθ using h
  exact ⟨θ, hθ⟩

/-- In dimension 2 the Gram entry is the plain dot product of two coordinate
pairs. -/
theorem gram_eq_dot (c : UnitPoints 2 M) (i j : Fin M) :
    c.gram i j = c.pts i 0 * c.pts j 0 + c.pts i 1 * c.pts j 1 := by
  rw [gram_eq_sum, Fin.sum_univ_two]

theorem gram_eq_cos (c : UnitPoints 2 M) {θ : Fin M → ℝ}
    (hθ : ∀ i, c.pts i 0 = Real.cos (θ i) ∧ c.pts i 1 = Real.sin (θ i)) (i j : Fin M) :
    c.gram i j = Real.cos (θ i - θ j) := by
  rw [gram_eq_dot, (hθ i).1, (hθ i).2, (hθ j).1, (hθ j).2, Real.cos_sub]

end UnitPoints

/-- **Schoenberg positivity in dimension 2.** The circle transcription of the
binary sum-of-squares argument: no spherical harmonics, no complex analysis
beyond producing an angle. -/
theorem schoenbergPos_dim_two (k : ℕ) : SchoenbergPos 2 k := by
  intro M c
  obtain ⟨θ, hθ⟩ := c.exists_angles
  have expand : ∀ a b : Fin M → ℝ,
      ∑ i, ∑ j, (a i * a j + b i * b j) = (∑ i, a i) ^ 2 + (∑ i, b i) ^ 2 := by
    intro a b
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  have hterm : ∀ i j, gegenbauerReal 2 k (c.gram i j)
      = Real.cos (k * θ i) * Real.cos (k * θ j)
        + Real.sin (k * θ i) * Real.sin (k * θ j) := by
    intro i j
    rw [c.gram_eq_cos hθ i j, gegenbauerReal_dim_two_cos,
      show (k : ℝ) * (θ i - θ j) = k * θ i - k * θ j by ring, Real.cos_sub]
  calc (0 : ℝ) ≤ (∑ i, Real.cos (k * θ i)) ^ 2 + (∑ i, Real.sin (k * θ i)) ^ 2 := by positivity
    _ = ∑ i, ∑ j, gegenbauerReal 2 k (c.gram i j) := by
        rw [← expand]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hterm i j).symm

/-- **First unconditional bound of the sphere side.** A family of unit vectors of
the plane whose pairwise inner products are at most `1/2` has at most 8 members.

The true maximum is 6, attained by the regular hexagon. The certificate
`(1, 3, 3, 1)` of `Delsarte.Sphere.certCircle` is therefore valid and not tight,
which is the ordinary situation for a linear programming bound. -/
theorem card_le_eight (c : UnitPoints 2 M) (hc : ∀ i j, i ≠ j → c.gram i j ≤ 1 / 2) :
    (M : ℚ) ≤ 8 :=
  card_le_eight_of_schoenberg (schoenbergPos_dim_two 2) (schoenbergPos_dim_two 3) c hc

/-- The same, as a statement about natural numbers. -/
theorem card_le_eight_nat (c : UnitPoints 2 M) (hc : ∀ i j, i ≠ j → c.gram i j ≤ 1 / 2) :
    M ≤ 8 := by
  have h := card_le_eight c hc
  exact_mod_cast h

/-! ## The lower half: the regular hexagon

An upper bound alone says nothing about how good it is, and a theorem about an
empty class of configurations would be worth nothing at all. The hexagon is the
construction: six unit vectors of the plane whose pairwise inner products are all
at most `1/2`.

Together with `card_le_eight`, the maximum on the circle lies between 6 and 8.
The gap is real and is the LP bound's own slack, not an artefact of the
formalization.

Coordinates rather than angles, so that every check is exact arithmetic in
`√3` with `(√3)² = 3`.
-/

/-- A vector of the plane from its two coordinates. -/
noncomputable def vec (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b]

@[simp] theorem vec_zero (a b : ℝ) : vec a b 0 = a := by simp [vec]

@[simp] theorem vec_one (a b : ℝ) : vec a b 1 = b := by simp [vec]

theorem norm_vec {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : ‖vec a b‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [vec_zero, vec_one, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [h]
  exact Real.sqrt_one

/-- Half of `√3`, the second coordinate of four of the six vertices. -/
noncomputable def hexS : ℝ := Real.sqrt 3 / 2

theorem hexS_sq : hexS ^ 2 = 3 / 4 := by
  rw [hexS, div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  norm_num

/-- The six vertices of the regular hexagon inscribed in the unit circle. -/
noncomputable def hexagon : UnitPoints 2 6 where
  pts := ![vec 1 0, vec (1 / 2) hexS, vec (-(1 / 2)) hexS, vec (-1) 0,
    vec (-(1 / 2)) (-hexS), vec (1 / 2) (-hexS)]
  norm_pts := by
    intro i
    fin_cases i <;>
      exact norm_vec (by nlinarith [hexS_sq])

theorem hexagon_gram_le (i j : Fin 6) (h : i ≠ j) : hexagon.gram i j ≤ 1 / 2 := by
  rw [UnitPoints.gram_eq_dot]
  fin_cases i <;> fin_cases j <;> simp_all [hexagon] <;> nlinarith [hexS_sq]

/-- The constraint is tight: two adjacent vertices sit exactly at `1/2`. So the
hexagon is on the boundary of the admissible class, not comfortably inside it. -/
theorem hexagon_gram_adjacent : hexagon.gram 0 1 = 1 / 2 := by
  rw [UnitPoints.gram_eq_dot]; simp [hexagon]

/-- Opposite vertices are antipodal. -/
theorem hexagon_gram_opposite : hexagon.gram 0 3 = -1 := by
  rw [UnitPoints.gram_eq_dot]; simp [hexagon]

/-- **The lower half.** Six unit vectors of the plane, pairwise inner products at
most `1/2`. The class `card_le_eight` bounds is therefore not empty, and the
maximum lies between 6 and 8. -/
theorem exists_six_points : ∃ c : UnitPoints 2 6, ∀ i j, i ≠ j → c.gram i j ≤ 1 / 2 :=
  ⟨hexagon, hexagon_gram_le⟩

end Delsarte.Sphere
