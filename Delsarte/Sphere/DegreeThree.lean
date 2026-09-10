/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Sphere.DegreeTwo

/-!
# Schoenberg positivity at degree 3, in every dimension

One degree above `Delsarte/Sphere/DegreeTwo.lean`, by the same kind of argument:
no spherical harmonics, no addition formula, only `Finset` sums.

## Why degree 3 is not a repetition of degree 2

With `G_3 t = ((d+2) t ^ 3 - 3 t) / (d-1)` the statement to prove is

`3 * ∑_(i,j) ⟪x i, x j⟫ ≤ (d+2) * ∑_(i,j) ⟪x i, x j⟫ ^ 3`.

Write `T a b e = ∑_i x i a * x i b * x i e` and `w a = ∑_i x i a`. Then the two
sides are `3 ‖w‖ ^ 2` and `(d+2) ‖T‖ ^ 2`, and `∑_b T a b b = w a`, because each
point is a unit vector. So what is wanted is a bound on the *contraction* of `T`.

The naive Cauchy-Schwarz gives the wrong constant: `(∑_b T a b b) ^ 2 ≤ d * ∑_(b,c)
(T a b c) ^ 2` yields `d`, and `(d+2)/3` is strictly smaller as soon as `d > 1`.
The symmetry of `T` has to be used, and that is what degree 2 never needed.

## The witness

`witness w a b e = δ a b * w e + δ b e * w a + δ e a * w b`, the symmetrization of
`δ ⊗ w`. Two computations, both a single contraction each (`sum_mul_witness`):

* `⟪T, witness w⟫ = 3 ‖w‖ ^ 2`, one term per contraction of `T`;
* `⟪witness w, witness w⟫ = 3 (d+2) ‖w‖ ^ 2`.

Then `0 ≤ ‖T - witness w / (d+2)‖ ^ 2` expands to exactly
`0 ≤ ‖T‖ ^ 2 - 3 ‖w‖ ^ 2 / (d+2)`. No Cauchy-Schwarz, no case split on `w = 0`:
one square, expanded.

`T - witness w / (d+2)` is the harmonic part of `T`, written out by hand. That is
the whole content of the proof, and the reason it stops here: at degree 4 the
harmonic projection is no longer a single guessable term, because the space it
projects away is no longer irreducible. See issue #23.

## The constant is exact

`(d+2)/3` is not a comfortable choice. On a pure-trace tensor `T = sym (δ ⊗ u)`
the contraction ratio is exactly `(d+2)/3`, so the inequality is sharp and the
expansion above loses nothing. `sum_gegenbauerReal_antipodal` exhibits a
configuration where the sum is exactly zero, and `gegenbauerReal_deg_three_neg_one`
shows `G_3` really does take negative values — the positivity of the double sum is
not a positivity term by term.

## What this does not do

No certificate comes out of degree 3 alone: the Odlyzko-Sloane polynomials in
dimensions 8 and 24 have degree 9 and above. This is a load test of the
architecture, not a step towards the kissing number.
-/

namespace Delsarte.Sphere

open Finset Polynomial Delsarte

variable {d M : ℕ}

/-! ## Rearranging nested sums -/

/-- Swapping two outer indices past three inner ones. -/
theorem sum_comm_five {ι κ α β γ : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [Fintype γ] (F : ι → κ → α → β → γ → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, ∑ e, F i j a b e = ∑ a, ∑ b, ∑ e, ∑ i, ∑ j, F i j a b e := by
  have h : ∑ p : ι × κ, ∑ q : α × β × γ, F p.1 p.2 q.1 q.2.1 q.2.2
      = ∑ q : α × β × γ, ∑ p : ι × κ, F p.1 p.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

/-- Swapping two outer indices past one inner one. -/
theorem sum_comm_three {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    (F : ι → κ → α → ℝ) : ∑ i, ∑ j, ∑ a, F i j a = ∑ a, ∑ i, ∑ j, F i j a := by
  calc ∑ i, ∑ j, ∑ a, F i j a = ∑ i, ∑ a, ∑ j, F i j a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, F i j a := Finset.sum_comm

/-- Cubing a sum. -/
theorem sum_pow_three (f : Fin d → ℝ) :
    (∑ a, f a) ^ 3 = ∑ a, ∑ b, ∑ e, f a * f b * f e := by
  calc (∑ a, f a) ^ 3 = ((∑ a, f a) * ∑ b, f b) * ∑ e, f e := by ring
    _ = (∑ a, ∑ b, f a * f b) * ∑ e, f e := by rw [Finset.sum_mul_sum]
    _ = ∑ a, ∑ b, ∑ e, f a * f b * f e := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _

/-! ## The Kronecker symbol and the witness tensor -/

/-- The Kronecker symbol, real valued. -/
def kron (a b : Fin d) : ℝ := if a = b then 1 else 0

theorem sum_kron_mul (b : Fin d) (f : Fin d → ℝ) : ∑ e, kron b e * f e = f b := by
  simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sum_kron_mul' (b : Fin d) (f : Fin d → ℝ) : ∑ e, kron e b * f e = f b := by
  simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_kron_diag : ∑ a : Fin d, kron a a = (d : ℝ) := by
  simp [kron]

theorem sum_kron (b : Fin d) : ∑ e : Fin d, kron b e = 1 := by
  have := sum_kron_mul b (fun _ => (1 : ℝ))
  simpa using this

/-- The symmetrization of `δ ⊗ w`: the degree-3 witness. -/
def witness (w : Fin d → ℝ) (a b e : Fin d) : ℝ :=
  kron a b * w e + kron b e * w a + kron e a * w b

/-- Contracting any tensor against the witness collapses to its three traces. -/
theorem sum_mul_witness (w : Fin d → ℝ) (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ e, F a b e * witness w a b e
      = (∑ e, (∑ a, F a a e) * w e) + (∑ a, (∑ b, F a b b) * w a)
        + ∑ b, (∑ a, F a b a) * w b := by
  have hsplit : ∀ a b e : Fin d, F a b e * witness w a b e
      = kron a b * (F a b e * w e) + kron b e * (F a b e * w a)
        + kron e a * (F a b e * w b) := by
    intro a b e
    simp only [witness]
    ring
  have h1 : ∑ a, ∑ b, ∑ e, kron a b * (F a b e * w e) = ∑ e, (∑ a, F a a e) * w e := by
    calc ∑ a, ∑ b, ∑ e, kron a b * (F a b e * w e)
        = ∑ a, ∑ b, kron a b * ∑ e, F a b e * w e :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            (Finset.mul_sum _ _ _).symm
      _ = ∑ a, ∑ e, F a a e * w e :=
          Finset.sum_congr rfl fun a _ => sum_kron_mul a _
      _ = ∑ e, ∑ a, F a a e * w e := Finset.sum_comm
      _ = ∑ e, (∑ a, F a a e) * w e :=
          Finset.sum_congr rfl fun e _ => (Finset.sum_mul _ _ _).symm
  have h2 : ∑ a, ∑ b, ∑ e, kron b e * (F a b e * w a) = ∑ a, (∑ b, F a b b) * w a := by
    calc ∑ a, ∑ b, ∑ e, kron b e * (F a b e * w a)
        = ∑ a, ∑ b, F a b b * w a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => sum_kron_mul b _
      _ = ∑ a, (∑ b, F a b b) * w a :=
          Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
  have h3 : ∑ a, ∑ b, ∑ e, kron e a * (F a b e * w b) = ∑ b, (∑ a, F a b a) * w b := by
    calc ∑ a, ∑ b, ∑ e, kron e a * (F a b e * w b)
        = ∑ a, ∑ b, F a b a * w b :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => sum_kron_mul' a _
      _ = ∑ b, ∑ a, F a b a * w b := Finset.sum_comm
      _ = ∑ b, (∑ a, F a b a) * w b :=
          Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  calc ∑ a, ∑ b, ∑ e, F a b e * witness w a b e
      = ∑ a, ∑ b, ∑ e, (kron a b * (F a b e * w e) + kron b e * (F a b e * w a)
          + kron e a * (F a b e * w b)) := by simp only [hsplit]
    _ = (∑ a, ∑ b, ∑ e, kron a b * (F a b e * w e))
          + (∑ a, ∑ b, ∑ e, kron b e * (F a b e * w a))
          + ∑ a, ∑ b, ∑ e, kron e a * (F a b e * w b) := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [h1, h2, h3]

/-- The three traces of the witness itself. -/
theorem witness_trace_one (w : Fin d → ℝ) (e : Fin d) :
    ∑ a, witness w a a e = ((d : ℝ) + 2) * w e := by
  simp only [witness, Finset.sum_add_distrib, ← Finset.sum_mul, sum_kron_diag]
  rw [sum_kron_mul' e w, sum_kron_mul e w]
  ring

theorem witness_trace_two (w : Fin d → ℝ) (a : Fin d) :
    ∑ b, witness w a b b = ((d : ℝ) + 2) * w a := by
  simp only [witness, Finset.sum_add_distrib]
  rw [sum_kron_mul a w, sum_kron_mul' a w, ← Finset.sum_mul, sum_kron_diag]
  ring

theorem witness_trace_three (w : Fin d → ℝ) (b : Fin d) :
    ∑ a, witness w a b a = ((d : ℝ) + 2) * w b := by
  simp only [witness, Finset.sum_add_distrib]
  rw [sum_kron_mul' b w, sum_kron_mul b w, ← Finset.sum_mul, sum_kron_diag]
  ring

/-- The squared norm of the witness. -/
theorem sum_witness_sq (w : Fin d → ℝ) :
    ∑ a, ∑ b, ∑ e, (witness w a b e) ^ 2 = 3 * ((d : ℝ) + 2) * ∑ a, (w a) ^ 2 := by
  have hsq : ∑ a, ∑ b, ∑ e, (witness w a b e) ^ 2
      = ∑ a, ∑ b, ∑ e, witness w a b e * witness w a b e := by
    simp only [pow_two]
  have hterm : ∀ f : Fin d → ℝ,
      ∑ e, (((d : ℝ) + 2) * f e) * f e = ((d : ℝ) + 2) * ∑ e, (f e) ^ 2 := by
    intro f
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hsq, sum_mul_witness w (witness w)]
  simp only [witness_trace_one, witness_trace_two, witness_trace_three, hterm]
  ring


/-! ## The closed form of `G_3` -/

/-- Closed form of `G_3` as a polynomial. -/
theorem gegenbauerPoly_deg_three (hd : 2 ≤ d) :
    gegenbauerPoly d 3
      = C (((d : ℚ) + 2) / ((d : ℚ) - 1)) * X ^ 3 - C ((3 : ℚ) / ((d : ℚ) - 1)) * X := by
  have hd' : (2 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hd0 : (d : ℚ) ≠ 0 := by intro h; rw [h] at hd'; norm_num at hd'
  have hd1 : (d : ℚ) - 1 ≠ 0 := by intro h; linarith [h]
  have h := gegenbauerPoly_add_two d 1
  rw [gegenbauerPoly_deg_two, gegenbauerPoly_one] at h
  rw [h]
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_pow]
  push_cast
  rw [show ((1 : ℚ) + (d : ℚ) - 1) = (d : ℚ) by ring]
  field_simp
  ring

/-- Closed form of `G_3` at a real argument. -/
theorem gegenbauerReal_deg_three (hd : 2 ≤ d) (t : ℝ) :
    gegenbauerReal d 3 t = (((d : ℝ) + 2) * t ^ 3 - 3 * t) / ((d : ℝ) - 1) := by
  rw [gegenbauerReal, gegenbauerPoly_deg_three hd]
  simp only [map_sub, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
  push_cast
  ring

/-! ## The positivity -/

/-- **Schoenberg positivity at degree 3, in every dimension.** -/
theorem schoenbergPos_deg_three (hd : 2 ≤ d) : SchoenbergPos d 3 := by
  intro M c
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdp : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  -- The third moment tensor and the first moment vector of the configuration.
  set T : Fin d → Fin d → Fin d → ℝ :=
    fun a b e => ∑ i, c.pts i a * c.pts i b * c.pts i e with hT
  set w : Fin d → ℝ := fun a => ∑ i, c.pts i a with hw
  have hnorm : ∀ i, ∑ a, c.pts i a * c.pts i a = 1 := fun i => by
    rw [← c.gram_eq_sum i i, c.gram_self i]
  -- The two sides of the inequality, as norms.
  have hcube : ∑ i, ∑ j, (c.gram i j) ^ 3 = ∑ a, ∑ b, ∑ e, (T a b e) ^ 2 := by
    have hL : ∀ i j : Fin M, (c.gram i j) ^ 3
        = ∑ a, ∑ b, ∑ e, (c.pts i a * c.pts i b * c.pts i e)
            * (c.pts j a * c.pts j b * c.pts j e) := by
      intro i j
      rw [c.gram_eq_sum i j, sum_pow_three]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun e _ => by ring
    have hR : ∀ a b e : Fin d, (T a b e) ^ 2
        = ∑ i, ∑ j, (c.pts i a * c.pts i b * c.pts i e)
            * (c.pts j a * c.pts j b * c.pts j e) := by
      intro a b e
      simp only [hT]
      rw [pow_two, Finset.sum_mul_sum]
    simp only [hL, hR]
    exact sum_comm_five _
  have hlin : ∑ i, ∑ j, c.gram i j = ∑ a, (w a) ^ 2 := by
    simp only [c.gram_eq_sum]
    rw [sum_comm_three (fun i j a => c.pts i a * c.pts j a)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hw]
    rw [pow_two, Finset.sum_mul_sum]
  -- The three traces of `T`, each one the first moment vector.
  have hc1 : ∀ e, ∑ a, T a a e = w e := by
    intro e
    simp only [hT, hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ a, c.pts i a * c.pts i a * c.pts i e
        = (∑ a, c.pts i a * c.pts i a) * c.pts i e := by rw [Finset.sum_mul]
      _ = c.pts i e := by rw [hnorm i, one_mul]
  have hc2 : ∀ a, ∑ b, T a b b = w a := by
    intro a
    simp only [hT, hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ b, c.pts i a * c.pts i b * c.pts i b
        = (∑ b, c.pts i b * c.pts i b) * c.pts i a := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = c.pts i a := by rw [hnorm i, one_mul]
  have hc3 : ∀ b, ∑ a, T a b a = w b := by
    intro b
    simp only [hT, hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ a, c.pts i a * c.pts i b * c.pts i a
        = (∑ a, c.pts i a * c.pts i a) * c.pts i b := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = c.pts i b := by rw [hnorm i, one_mul]
  -- Pairing `T` against the witness.
  have hTS : ∑ a, ∑ b, ∑ e, T a b e * witness w a b e = 3 * ∑ a, (w a) ^ 2 := by
    rw [sum_mul_witness]
    simp only [hc1, hc2, hc3, ← pow_two]
    ring
  -- One square, expanded: the harmonic part of `T` has nonnegative norm.
  have hnn : (0 : ℝ) ≤ ∑ a, ∑ b, ∑ e, (T a b e - witness w a b e / ((d : ℝ) + 2)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ a, ∑ b, ∑ e, (T a b e - witness w a b e / ((d : ℝ) + 2)) ^ 2
      = (∑ a, ∑ b, ∑ e, (T a b e) ^ 2) - (3 / ((d : ℝ) + 2)) * ∑ a, (w a) ^ 2 := by
    have key : ∀ a b e : Fin d, (T a b e - witness w a b e / ((d : ℝ) + 2)) ^ 2
        = (T a b e) ^ 2 - (2 / ((d : ℝ) + 2)) * (T a b e * witness w a b e)
          + (1 / ((d : ℝ) + 2) ^ 2) * (witness w a b e) ^ 2 := by
      intro a b e
      field_simp
      ring
    calc ∑ a, ∑ b, ∑ e, (T a b e - witness w a b e / ((d : ℝ) + 2)) ^ 2
        = ∑ a, ∑ b, ∑ e, ((T a b e) ^ 2
            - (2 / ((d : ℝ) + 2)) * (T a b e * witness w a b e)
            + (1 / ((d : ℝ) + 2) ^ 2) * (witness w a b e) ^ 2) := by simp only [key]
      _ = (∑ a, ∑ b, ∑ e, (T a b e) ^ 2)
            - (2 / ((d : ℝ) + 2)) * (∑ a, ∑ b, ∑ e, T a b e * witness w a b e)
            + (1 / ((d : ℝ) + 2) ^ 2) * ∑ a, ∑ b, ∑ e, (witness w a b e) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (∑ a, ∑ b, ∑ e, (T a b e) ^ 2) - (3 / ((d : ℝ) + 2)) * ∑ a, (w a) ^ 2 := by
          rw [hTS, sum_witness_sq]
          field_simp
          ring
  -- The inequality that the Gegenbauer sum is.
  have hkey : 3 * (∑ a, (w a) ^ 2) ≤ ((d : ℝ) + 2) * ∑ a, ∑ b, ∑ e, (T a b e) ^ 2 := by
    rw [hexp, sub_nonneg] at hnn
    calc 3 * (∑ a, (w a) ^ 2)
        = ((d : ℝ) + 2) * ((3 / ((d : ℝ) + 2)) * ∑ a, (w a) ^ 2) := by field_simp
      _ ≤ ((d : ℝ) + 2) * ∑ a, ∑ b, ∑ e, (T a b e) ^ 2 :=
          mul_le_mul_of_nonneg_left hnn hdp.le
  -- Rewrite the Gegenbauer sum as that inequality.
  have hval : ∑ i, ∑ j, gegenbauerReal d 3 (c.gram i j)
      = (∑ i, ∑ j, (((d : ℝ) + 2) * (c.gram i j) ^ 3 - 3 * c.gram i j)) / ((d : ℝ) - 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => gegenbauerReal_deg_three hd _
  have hnum : ∑ i, ∑ j, (((d : ℝ) + 2) * (c.gram i j) ^ 3 - 3 * c.gram i j)
      = ((d : ℝ) + 2) * (∑ i, ∑ j, (c.gram i j) ^ 3) - 3 * ∑ i, ∑ j, c.gram i j := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hval, hnum, hcube, hlin]
  exact div_nonneg (by linarith [hkey]) hd1.le

/-! ## The positivity is tight, and not term by term

Two checks that the statement above is not empty. `G_3` really does take negative
values, so the double sum is not a sum of nonnegative terms; and there is a
configuration where it vanishes, so the inequality cannot be strengthened.
-/

/-- **Negative control**: `G_3 (-1) = -1` in every dimension. -/
theorem gegenbauerReal_deg_three_neg_one (hd : 2 ≤ d) : gegenbauerReal d 3 (-1) = -1 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by intro h; linarith
  rw [gegenbauerReal_deg_three hd]
  field_simp
  ring

/-- Two antipodal unit vectors. -/
noncomputable def antipodalPoints {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    UnitPoints d 2 where
  pts := fun i => if i = 0 then v else -v
  norm_pts := by
    intro i
    by_cases h : i = 0 <;> simp [h, hv]

@[simp]
theorem antipodalPoints_gram {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (i j : Fin 2) :
    (antipodalPoints hv).gram i j = if i = j then 1 else -1 := by
  fin_cases i <;> fin_cases j <;>
    simp [antipodalPoints, UnitPoints.gram, hv, inner_neg_right, inner_neg_left]

/-- Such a configuration exists as soon as the space is not trivial. -/
theorem exists_unit_vector (hd : 2 ≤ d) : ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩

/-- **The degree-3 positivity is attained.** On an antipodal pair the sum is exactly
zero, so `schoenbergPos_deg_three` cannot be strengthened to a strict inequality and
the expansion above loses nothing. -/
theorem sum_gegenbauerReal_antipodal (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) :
    ∑ i, ∑ j, gegenbauerReal d 3 ((antipodalPoints hv).gram i j) = 0 := by
  simp only [Fin.sum_univ_two, antipodalPoints_gram]
  norm_num [gegenbauerReal_eval_one hd, gegenbauerReal_deg_three_neg_one hd]

end Delsarte.Sphere
