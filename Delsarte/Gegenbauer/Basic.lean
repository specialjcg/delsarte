/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Normalized Gegenbauer polynomials

The Gegenbauer polynomials are to the sphere what the Krawtchouk polynomials are
to the Hamming space: the basis in which the Delsarte LP is written. Nothing here
depends on `Delsarte.Krawtchouk` — the two families are bases of two different
linear programs and share only their role.

## Normalization

We use the polynomials `G_k` normalized by `G_k 1 = 1`, not the classical
`C_k^lam` with `lam = (d - 2) / 2`. The two differ by the positive factor
`C_k^lam 1`, so the condition `f_k ≥ 0` that carries the Odlyzko-Sloane bound is
unaffected, while the bound itself becomes `f 1 / f_0 = (∑_k f_k) / f_0` with no
stray constant. A reader comparing coefficients against a table of `C_k^lam`
will find them scaled, and that is intended.

The recurrence, with `d : ℕ` and no natural subtraction anywhere:

`G_0 = 1`, `G_1 = X`, and

`G_(k+2) = (2k + d) / (k + d - 1) * X * G_(k+1) - (k + 1) / (k + d - 1) * G_k`.

The denominator is positive as soon as `2 ≤ d`, which is the hypothesis carried
by every statement that needs it; only `d = 1` is degenerate. The case `d = 2` is
fine and gives the Chebyshev polynomials of the first kind — see
`gegenbauerPoly_dim_two`, which anchors this definition to mathlib's
independently formalized family.

## Two definitions

`gegenbauer d k t : ℚ` is computable: it is what a certificate replay evaluates.
`gegenbauerPoly d k : ℚ[X]` is not, but it carries the polynomial structure that
a later interval-positivity argument (Sturm, or a sum-of-squares decomposition)
will need. `eval_gegenbauerPoly` identifies the two.

## Out of scope

The positivity `∑_(i,j) f ⟪x i, x j⟫ ≥ 0` for unit vectors — the continuous
analogue of `Delsarte.Hamming.sum_sum_krawtchouk_nonneg`, and the hard point of
the sphere side — is not here, nor is the addition formula, nor any method for
certifying `f t ≤ 0` on an interval. This file is the polynomial basis, and
nothing more.

Note `gegenbauer 8 2 0 = -1/7 < 0`: these polynomials are *not* nonnegative on
`[-1, 1]`, which is exactly why `f t ≤ 0` on `[-1, 1/2]` is a hypothesis to be
checked and never a corollary.
-/

namespace Delsarte

open Polynomial

/-- The normalized Gegenbauer value `G_k t` in dimension `d`, computable over
`ℚ`. -/
def gegenbauer (d : ℕ) : ℕ → ℚ → ℚ
  | 0, _ => 1
  | 1, t => t
  | (k + 2), t =>
      (2 * (k : ℚ) + d) / ((k : ℚ) + d - 1) * t * gegenbauer d (k + 1) t
        - ((k : ℚ) + 1) / ((k : ℚ) + d - 1) * gegenbauer d k t

/-- The normalized Gegenbauer polynomial `G_k` in dimension `d`. -/
noncomputable def gegenbauerPoly (d : ℕ) : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | (k + 2) =>
      C ((2 * (k : ℚ) + d) / ((k : ℚ) + d - 1)) * X * gegenbauerPoly d (k + 1)
        - C (((k : ℚ) + 1) / ((k : ℚ) + d - 1)) * gegenbauerPoly d k

@[simp]
theorem gegenbauer_zero (d : ℕ) (t : ℚ) : gegenbauer d 0 t = 1 := rfl

@[simp]
theorem gegenbauer_one (d : ℕ) (t : ℚ) : gegenbauer d 1 t = t := rfl

theorem gegenbauer_add_two (d k : ℕ) (t : ℚ) :
    gegenbauer d (k + 2) t
      = (2 * (k : ℚ) + d) / ((k : ℚ) + d - 1) * t * gegenbauer d (k + 1) t
        - ((k : ℚ) + 1) / ((k : ℚ) + d - 1) * gegenbauer d k t := rfl

@[simp]
theorem gegenbauerPoly_zero (d : ℕ) : gegenbauerPoly d 0 = 1 := rfl

@[simp]
theorem gegenbauerPoly_one (d : ℕ) : gegenbauerPoly d 1 = X := rfl

theorem gegenbauerPoly_add_two (d k : ℕ) :
    gegenbauerPoly d (k + 2)
      = C ((2 * (k : ℚ) + d) / ((k : ℚ) + d - 1)) * X * gegenbauerPoly d (k + 1)
        - C (((k : ℚ) + 1) / ((k : ℚ) + d - 1)) * gegenbauerPoly d k := rfl

/-- The recurrence never divides by zero: for `2 ≤ d` the denominator is at least
`1`. Only `d = 1` is degenerate. -/
theorem gegenbauer_denom_pos {d : ℕ} (hd : 2 ≤ d) (k : ℕ) : 0 < (k : ℚ) + d - 1 := by
  have hd' : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  linarith

theorem gegenbauer_denom_ne_zero {d : ℕ} (hd : 2 ≤ d) (k : ℕ) :
    ((k : ℚ) + d - 1) ≠ 0 :=
  ne_of_gt (gegenbauer_denom_pos hd k)

/-- The computable value is the evaluation of the polynomial. -/
theorem eval_gegenbauerPoly (d k : ℕ) (t : ℚ) :
    (gegenbauerPoly d k).eval t = gegenbauer d k t := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more k ih1 ih2 =>
    rw [gegenbauerPoly_add_two, gegenbauer_add_two]
    simp only [eval_sub, eval_mul, eval_C, eval_X, ih1, ih2]

/-! ## Normalization

`G_k 1 = 1` is the identity that pins the two coefficients of the recurrence:
it holds precisely because `(2k + d) - (k + 1) = k + d - 1`. Proving it therefore
tests both coefficients at once.
-/

theorem gegenbauer_eval_one {d : ℕ} (hd : 2 ≤ d) (k : ℕ) : gegenbauer d k 1 = 1 := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h0 := gegenbauer_denom_ne_zero hd k
    rw [gegenbauer_add_two, ih1, ih2]
    field_simp
    ring

theorem gegenbauer_eval_neg_one {d : ℕ} (hd : 2 ≤ d) (k : ℕ) :
    gegenbauer d k (-1) = (-1 : ℚ) ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more k ih1 ih2 =>
    have h0 := gegenbauer_denom_ne_zero hd k
    rw [gegenbauer_add_two, ih1, ih2]
    field_simp
    ring

/-- `G_k` has degree at most `k`. -/
theorem natDegree_gegenbauerPoly_le (d k : ℕ) : (gegenbauerPoly d k).natDegree ≤ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more k ih1 ih2 =>
    rw [gegenbauerPoly_add_two]
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans natDegree_mul_le ?_
      have h1 : (C ((2 * (k : ℚ) + d) / ((k : ℚ) + d - 1)) * X).natDegree ≤ 1 :=
        le_trans (natDegree_C_mul_le _ _) (by simp)
      omega
    · exact le_trans (natDegree_C_mul_le _ _) (by omega)

/-! ## Anchor: dimension 2 is Chebyshev

At `d = 2` the coefficients collapse to `2` and `1`, and the recurrence becomes
mathlib's `Polynomial.Chebyshev.T_add_two`. This is the strongest available check
on the definition: an independently formalized family agrees with it term by
term.
-/

theorem gegenbauerPoly_dim_two (k : ℕ) : gegenbauerPoly 2 k = Chebyshev.T ℚ (k : ℤ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more k ih1 ih2 =>
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hden : ((k : ℚ) + ((2 : ℕ) : ℚ) - 1) = (k : ℚ) + 1 := by push_cast; ring
    have e1 : (2 * (k : ℚ) + ((2 : ℕ) : ℚ)) / ((k : ℚ) + ((2 : ℕ) : ℚ) - 1) = 2 := by
      rw [hden]; push_cast; field_simp
    have e2 : ((k : ℚ) + 1) / ((k : ℚ) + ((2 : ℕ) : ℚ) - 1) = 1 := by
      rw [hden]; exact div_self hk
    have hC2 : (C (2 : ℚ)) = 2 := by simp only [map_ofNat]
    rw [gegenbauerPoly_add_two, ih1, ih2, e1, e2]
    push_cast
    rw [Chebyshev.T_add_two, hC2, map_one, one_mul]

/-! ## Closed forms in low degree

Two general identities, valid in every dimension `2 ≤ d`. Every numeric check
below is an instance of one of them, so the checks test the recurrence and not a
separately transcribed table.
-/

theorem gegenbauer_deg_two {d : ℕ} (hd : 2 ≤ d) (t : ℚ) :
    gegenbauer d 2 t = ((d : ℚ) * t ^ 2 - 1) / ((d : ℚ) - 1) := by
  have hd' : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hd1 : ((d : ℚ) - 1) ≠ 0 := by intro h; linarith
  have h := gegenbauer_add_two d 0 t
  norm_num at h
  rw [h]
  field_simp

theorem gegenbauer_deg_three {d : ℕ} (hd : 2 ≤ d) (t : ℚ) :
    gegenbauer d 3 t = t * (((d : ℚ) + 2) * t ^ 2 - 3) / ((d : ℚ) - 1) := by
  have hd' : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℚ) ≠ 0 := by intro h; linarith
  have hd1 : ((d : ℚ) - 1) ≠ 0 := by intro h; linarith
  have h := gegenbauer_add_two d 1 t
  norm_num [gegenbauer_deg_two hd] at h
  rw [h]
  field_simp
  ring

/-! ## Numeric checks against known families

Three families formalized or tabulated elsewhere, plus the two target
dimensions. Each is computed from `gegenbauer_deg_two` or `gegenbauer_deg_three`,
so each is a check on the recurrence.
-/

/-- `d = 3` is Legendre: `G_2 = P_2`. -/
theorem gegenbauer_deg_two_dim_three (t : ℚ) : gegenbauer 3 2 t = (3 * t ^ 2 - 1) / 2 := by
  rw [gegenbauer_deg_two (by norm_num)]; norm_num

/-- `d = 3` is Legendre: `G_3 = P_3`. -/
theorem gegenbauer_deg_three_dim_three (t : ℚ) :
    gegenbauer 3 3 t = (5 * t ^ 3 - 3 * t) / 2 := by
  rw [gegenbauer_deg_three (by norm_num)]; push_cast; ring

/-- `d = 4` is Chebyshev of the second kind, scaled: `G_k = U_k / (k + 1)`, so
`G_2 = U_2 / 3`. -/
theorem gegenbauer_deg_two_dim_four (t : ℚ) : gegenbauer 4 2 t = (4 * t ^ 2 - 1) / 3 := by
  rw [gegenbauer_deg_two (by norm_num)]; norm_num

/-- `d = 4`: `G_3 = U_3 / 4 = 2t³ - t`. -/
theorem gegenbauer_deg_three_dim_four (t : ℚ) : gegenbauer 4 3 t = 2 * t ^ 3 - t := by
  rw [gegenbauer_deg_three (by norm_num)]; push_cast; ring

/-- Target dimension 8. -/
theorem gegenbauer_deg_two_dim_eight (t : ℚ) : gegenbauer 8 2 t = (8 * t ^ 2 - 1) / 7 := by
  rw [gegenbauer_deg_two (by norm_num)]; norm_num

/-- Target dimension 8. -/
theorem gegenbauer_deg_three_dim_eight (t : ℚ) :
    gegenbauer 8 3 t = t * (10 * t ^ 2 - 3) / 7 := by
  rw [gegenbauer_deg_three (by norm_num)]; push_cast; ring

/-- Target dimension 24. -/
theorem gegenbauer_deg_two_dim_twentyFour (t : ℚ) :
    gegenbauer 24 2 t = (24 * t ^ 2 - 1) / 23 := by
  rw [gegenbauer_deg_two (by norm_num)]; norm_num

/-- Target dimension 24. -/
theorem gegenbauer_deg_three_dim_twentyFour (t : ℚ) :
    gegenbauer 24 3 t = t * (26 * t ^ 2 - 3) / 23 := by
  rw [gegenbauer_deg_three (by norm_num)]; push_cast; ring

/-! ## Second anchor: dimension 4 is Chebyshev `U`, scaled by `1 / (k + 1)`

One anchor cannot catch an error that happens to vanish where it is taken. At
`d = 2` the coefficients of the recurrence collapse to `2` and `1`, so
`gegenbauerPoly_dim_two` tests the recurrence only at that degenerate point.
Dimension 4 is the other place where the recurrence meets a mathlib family:
there it reads

`G_(k+2) = (2k+4)/(k+3) X G_(k+1) - (k+1)/(k+3) G_k`,

and substituting `G_k = U_k / (k+1)` returns `U_(k+2) = 2 X U_(k+1) - U_k`,
which is `Chebyshev.U_add_two`. The scaling factor is forced, not chosen:
`U_k 1 = k + 1` while our normalization demands `G_k 1 = 1`.
-/

theorem gegenbauerPoly_dim_four (k : ℕ) :
    gegenbauerPoly 4 k = C (1 / ((k : ℚ) + 1)) * Chebyshev.U ℚ (k : ℤ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have h2 : (C (1 / 2 : ℚ)) * 2 = 1 := by
      rw [show (2 : ℚ[X]) = C (2 : ℚ) from by simp only [map_ofNat], ← C_mul]
      norm_num
    have hc : ((1 : ℕ) : ℤ) = 1 := by norm_num
    rw [gegenbauerPoly_one, hc, Chebyshev.U_one, ← mul_assoc,
      show (((1 : ℕ) : ℚ) + 1) = 2 from by norm_num, h2, one_mul]
  | more k ih1 ih2 =>
    have hi1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    have hi2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
    have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℚ) + 2) ≠ 0 := by positivity
    have hk4 : ((k : ℚ) + 4 - 1) ≠ 0 := by
      have : (0 : ℚ) ≤ (k : ℚ) := by positivity
      intro h; linarith
    rw [gegenbauerPoly_add_two, ih1, ih2, hi1, hi2, Chebyshev.U_add_two]
    apply Polynomial.funext
    intro x
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_ofNat]
    push_cast
    field_simp
    ring

/-- The scaling in `gegenbauerPoly_dim_four` is consistent with the
normalization: it recovers `G_k 1 = 1` at `d = 4` from mathlib's
`U_k 1 = k + 1`, by a route that goes through neither the recurrence nor
`gegenbauer_eval_one`. -/
theorem gegenbauer_dim_four_eval_one (k : ℕ) : gegenbauer 4 k 1 = 1 := by
  have h : ((Chebyshev.U ℚ (k : ℤ)).eval 1) = (k : ℚ) + 1 := by
    rw [Chebyshev.U_eval_one]; push_cast; ring
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [← eval_gegenbauerPoly, gegenbauerPoly_dim_four, eval_mul, eval_C, h]
  field_simp

/-- Negative control on the anchor: the `U`-anchor is specific to `d = 4`. In
dimension 8 the same scaled Chebyshev polynomial is a different polynomial, so
`gegenbauerPoly_dim_four` says something about the dimension and is not an
identity that any `d` would satisfy. -/
theorem gegenbauerPoly_dim_eight_ne_chebyshevU :
    gegenbauerPoly 8 2 ≠ C (1 / 3 : ℚ) * Chebyshev.U ℚ 2 := by
  intro h
  have h0 := congrArg (fun p : ℚ[X] => p.eval 0) h
  simp only [eval_mul, eval_C, Chebyshev.U_two, eval_sub, eval_pow, eval_X, eval_one,
    eval_ofNat, eval_gegenbauerPoly] at h0
  rw [gegenbauer_deg_two_dim_eight] at h0
  norm_num at h0

/-! ## Negative control

A basis whose members were all nonnegative would make the LP hypothesis
`f t ≤ 0` on `[-1, 1/2]` vacuous. It is not.
-/

/-- `G_2` in dimension 8 is negative at `0`. So the Gegenbauer polynomials are
not nonnegative on `[-1, 1]`, and `f t ≤ 0` on `[-1, 1/2]` is a genuine
hypothesis rather than a consequence of `f_k ≥ 0`. -/
theorem gegenbauer_deg_two_dim_eight_zero_neg : gegenbauer 8 2 0 < 0 := by
  rw [gegenbauer_deg_two_dim_eight]; norm_num

/-- The same in dimension 24. -/
theorem gegenbauer_deg_two_dim_twentyFour_zero_neg : gegenbauer 24 2 0 < 0 := by
  rw [gegenbauer_deg_two_dim_twentyFour]; norm_num

/-! ## Replay at build time

These run the compiled evaluator on exact `ℚ` arithmetic. They prove nothing —
they are the replay, and they fail the build if the evaluator ever disagrees with
the theorems above.
-/

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard gegenbauer 8 2 0 == -1/7
#guard gegenbauer 8 3 (1/2) == -1/28
#guard gegenbauer 24 2 0 == -1/23
#guard gegenbauer 24 3 (1/2) == 7/92
#guard gegenbauer 2 3 (1/2) == -1
#guard gegenbauer 3 4 1 == 1
#guard gegenbauer 24 7 (-1) == -1
#guard ! (gegenbauer 8 2 0 == 1/7)
#guard gegenbauer 4 5 (1/3) == 115/729
#guard gegenbauer 4 6 (-2/5) == 2353/15625
-- Dimension 8 is not the `U`-anchor: `U_2 0 / 3 = -1/3`, while `G_2 0 = -1/7`.
#guard ! (gegenbauer 8 2 0 == -1/3)

end Delsarte
