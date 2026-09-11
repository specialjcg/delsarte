/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Harmonic.Zonal
import Delsarte.Sphere.DegreeThree

/-!
# Schoenberg positivity, at every degree and in every dimension

`Delsarte/Sphere/DegreeTwo.lean` and `DegreeThree.lean` settle degrees 2 and 3 by
hand, and stop there: at degree 4 the trace part of a symmetric tensor is no
longer irreducible, and no single witness tensor can be guessed. This file settles
every degree at once, and the argument is shorter than either of them.

## The mechanism

Everything is already proved elsewhere. `Delsarte/Harmonic/Zonal.lean` produces a
polynomial `Z_k(x, ·)`, harmonic, homogeneous of degree `k`, whose value at `y` is
`G_k ⟪x,y⟫` when both vectors are unit. `Delsarte/Harmonic/Fischer.lean` produces
an inner product for which harmonic polynomials are orthogonal to multiples of
`‖y‖²`, and for which pairing against a power of a linear form is evaluation.

Put together, `fischer_zonal_zonal` says

`⟪Z_k(x,·), Z_k(y,·)⟫ = lead_k · k! · G_k ⟪x,y⟫`

with `lead_k > 0`. So the matrix `G_k ⟪x_i, x_j⟫` is a Gram matrix divided by a
positive number, and `∑_(i,j) G_k ⟪x_i,x_j⟫` is a squared norm. That is the whole
proof of `schoenbergPos_all`.

No spherical harmonics, no dimension of `H_k`, no orthogonal decomposition of the
symmetric tensors, and no projector: the harmonic vector is written down by a
recurrence instead of being obtained by projection, which is what made the
spectral information unnecessary.

## What this does and does not unlock

`SchoenbergPos` is one of the three hypotheses of `card_le_of_sphereCert`. It is
now available at every degree, so the hypothesis `hS` can be discharged. The other
two — a certificate that is nonnegative in the Gegenbauer basis, and that is
nonpositive on `[-1, 1/2]` — are still the caller's problem, and for the kissing
number in dimensions 8 and 24 they are the part that remains.

`hS` is deliberately **not** removed from the statement of `card_le_of_sphereCert`.
A theorem that carries its hypotheses explicitly can be read without the rest of
the repository.

## The positivity is not strict, and not term by term

`sum_gegenbauerReal_antipodal` exhibits a configuration where the sum is exactly
zero: what is proved is `0 ≤`, not `0 <`. And `gegenbauer_deg_four_dim_eight_neg`
below exhibits a negative value of `G_4` itself, in the dimension that matters, so
the positivity of the double sum is a genuine cancellation and not a term-by-term
fact.
-/

namespace Delsarte.Sphere

open Finset MvPolynomial Delsarte Delsarte.Harmonic

variable {d M : ℕ}

/-- A unit point has coordinate squares summing to one. -/
theorem sum_sq_pts (c : UnitPoints d M) (i : Fin M) :
    ∑ a, (c.pts i a) ^ 2 = 1 := by
  have h : (1 : ℝ) = ∑ a, c.pts i a * c.pts i a := by
    rw [← c.gram_eq_sum i i, UnitPoints.gram_self]
  rw [h]
  exact Finset.sum_congr rfl fun a _ => sq (c.pts i a)

/-- **The Gram identity.** The Gegenbauer value of an inner product is, up to a
positive constant, a Fischer inner product of two zonal polynomials.

The `rSq` part of `Z_k(y,·)` dies against the harmonic `Z_k(x,·)`, and what is
left is one evaluation. -/
theorem fischer_zonal_zonal (hd : 2 ≤ d) {x y : Fin d → ℝ}
    (hx : ∑ i, (x i) ^ 2 = 1) (hy : ∑ i, (y i) ^ 2 = 1) (k : ℕ) :
    fischer (zonal d x k) (zonal d y k)
      = zonalLead d k * (Nat.factorial k : ℝ) * gegenbauerReal d k (∑ i, x i * y i) := by
  obtain ⟨w, hw⟩ := rSq_dvd_zonal_sub y k
  have hsplit : zonal d y k = C (zonalLead d k) * linForm y ^ k + rSq d * w := by
    rw [← hw]; ring
  have hzero : fischer (zonal d x k) (rSq d * w) = 0 := by
    rw [fischer_comm, fischer_rSq_mul, mvLaplacian_zonal hd, fischer_zero_right]
  rw [hsplit, fischer_add_right, hzero, add_zero, fischer_C_mul_right,
    fischer_linForm_pow y k _ (zonal_isHomogeneous x k), eval_zonal x y hx hy k]
  ring

/-- **Schoenberg positivity, unconditional.** For every dimension `d ≥ 2` and
every degree `k`, `G_k` is positive definite on the sphere of `ℝ^d`. -/
theorem schoenbergPos_all (hd : 2 ≤ d) (k : ℕ) : SchoenbergPos d k := by
  intro M c
  set L : ℝ := zonalLead d k * (Nat.factorial k : ℝ) with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (zonalLead_pos hd k) (by exact_mod_cast Nat.factorial_pos k)
  set Z : Fin M → MvPolynomial (Fin d) ℝ := fun i => zonal d (fun a => c.pts i a) k with hZ
  have hpair : ∀ i j : Fin M,
      gegenbauerReal d k (c.gram i j) = fischer (Z i) (Z j) / L := by
    intro i j
    have h := fischer_zonal_zonal hd (x := fun a => c.pts i a) (y := fun a => c.pts j a)
      (sum_sq_pts c i) (sum_sq_pts c j) k
    have hne : zonalLead d k ≠ 0 := (zonalLead_pos hd k).ne'
    rw [hZ, h, ← c.gram_eq_sum i j, hL]
    field_simp
  have hrewrite : ∑ i, ∑ j, gegenbauerReal d k (c.gram i j)
      = fischer (∑ i, Z i) (∑ j, Z j) / L := by
    rw [fischer_sum_left, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fischer_sum_right, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => hpair i j
  rw [hrewrite]
  exact div_nonneg (fischer_self_nonneg _) hLpos.le

/-- Degree 4 in particular, the first degree the elementary argument of
`Delsarte/Sphere/DegreeThree.lean` could not reach. -/
theorem schoenbergPos_deg_four (hd : 2 ≤ d) : SchoenbergPos d 4 :=
  schoenbergPos_all hd 4

/-! ### Controls -/

/-- The elementary proofs of degrees 2 and 3 are recovered, so the two routes agree
where they overlap. Both files stay: they carry witnesses this one does not. -/
theorem schoenbergPos_deg_two_of_all (hd : 2 ≤ d) : SchoenbergPos d 2 :=
  schoenbergPos_all hd 2

theorem schoenbergPos_deg_three_of_all (hd : 2 ≤ d) : SchoenbergPos d 3 :=
  schoenbergPos_all hd 3

/-- `G_4` takes negative values in dimension 8, so the positivity just proved is a
cancellation across the double sum, not a term-by-term fact. -/
theorem gegenbauer_deg_four_dim_eight_neg : gegenbauer 8 4 (1 / 2) < 0 := by
  norm_num [gegenbauer]

/-- And the positivity is not strict: two antipodal points make the degree-3 sum
vanish exactly. -/
theorem schoenbergPos_not_strict (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) :
    ∑ i, ∑ j, gegenbauerReal d 3 ((antipodalPoints hv).gram i j) = 0 :=
  sum_gegenbauerReal_antipodal hd hv

end Delsarte.Sphere
