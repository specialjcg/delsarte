/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Sphere.Schoenberg
import Delsarte.Certificate.Interval

/-!
# The kissing number in dimensions 8 and 24, from above

A *kissing configuration* is a family of unit vectors of `ℝ^d` whose pairwise
inner products are at most `1/2`: exactly the centres of unit spheres all
touching a central unit sphere without overlapping, since two such spheres are
disjoint precisely when their centres subtend an angle of at least `60°`.

This file certifies

* `kissingLe 8 240`,
* `kissingLe 24 196560`,

by the Odlyzko-Sloane linear programming bound, with `Delsarte/Sphere/LP.lean`
supplying the bound and `Delsarte/Sphere/Schoenberg.lean` supplying positivity at
every degree.

## What is proved, and what is not

**Only the upper bounds.** The matching lower bounds are constructions — the
`E8` root system and the Leech lattice — and neither is formalized here. So the
theorems below read `≤ 240` and `≤ 196560`, never `=`. That the true values are
`240` and `196560` is a fact about mathematics, not a fact about this
repository; what remains unexcluded is every value below those bounds.

That said, the bounds are *saturated*: `kissing_bound_eight_tight` and
`kissing_bound_twentyFour_tight` show the quotient `(∑ f k) / f 0` equals `240`
and `196560` exactly, not approximately and not with room to spare. This route
cannot prove anything stronger, and no rounding is hiding in it.

## Where the certificates come from

The solver is not in the trust base, and here it is not even needed: the two
polynomials are forced by complementary slackness. For the bound to be attained,
`f` must vanish at every inner product that actually occurs off the diagonal —
`{0, ±1/2, ±1}` for `E8`, `{0, ±1/4, ±1/2, ±1}` for Leech — with a double root
at each interior point, where `f ≤ 0` must have a minimum, and a simple root at
each endpoint of `[-1, 1/2]`. That reading gives

* `d = 8` : `(t+1)(t+1/2)² t² (t-1/2)`, degree `6`;
* `d = 24`: `(t+1)(t+1/2)² (t+1/4)² t² (t-1/4)² (t-1/2)`, degree `10`.

The Gegenbauer coefficients were then computed exactly over `ℚ`, and the
identity `lpPoly d N f = <the factored polynomial>` is re-proved here by the
kernel. A reader who distrusts the numbers can ignore where they came from: the
`lpPoly_*` theorems are the verification.

The same factorization gives the interval certificate for free, with a single
square and a single multiplier pair:

`-f = (X + 1) (1/2 - X) · [X (X+1/2) ⋯]²`.

## Negative controls

Four, all measured before being written:

* `certKiss8_fails_dim_twentyFour` — the *same* coefficient vector, read in
  dimension `24`, is positive at `t = 0`, inside the interval. Gegenbauer
  coefficients do not transport across dimensions.
* `certKiss24Short_zero_neg` — dropping the root at `-1/4` in dimension `24`
  makes `f 0` negative, so `card_le_of_sphereCert` refuses the certificate, and
  `certKiss24Short_bound_absurd` shows the quotient it would produce is itself
  negative. The hypothesis `0 < f 0` is load-bearing.
* `neg_lpPoly_certKiss8_not_sos` — `-f` takes a negative value at `1`, so it is
  not a bare sum of squares: the interval multipliers are not decoration.
* `lpReal_certKiss8_one_pos` — outside the interval the certificate is positive,
  which is what makes the bound finite.
-/

namespace Delsarte.Sphere

open Polynomial Finset Delsarte

set_option maxRecDepth 100000

/-! ## The statement -/

/-- `kissingLe d K` : every family of unit vectors of `ℝ^d` with pairwise inner
products at most `1/2` has at most `K` members. -/
def kissingLe (d K : ℕ) : Prop :=
  ∀ (M : ℕ) (c : UnitPoints d M), (∀ i j, i ≠ j → c.gram i j ≤ 1 / 2) → M ≤ K

/-! ## Dimension 8 -/

/-- The Gegenbauer coefficients of `(t+1)(t+1/2)² t² (t-1/2)` in dimension `8`. -/
def certKiss8 : ℕ → ℚ
  | 0 => 3 / 320
  | 1 => 3 / 40
  | 2 => 15 / 64
  | 3 => 39 / 80
  | 4 => 399 / 640
  | 5 => 9 / 16
  | 6 => 33 / 128
  | _ => 0

/-- The expansion is exact. This is the whole verification of the coefficients:
whatever produced them, the kernel checks the identity. -/
theorem lpPoly_certKiss8 :
    lpPoly 8 6 certKiss8 = (X + 1) * (X + C (1 / 2)) ^ 2 * X ^ 2 * (X - C (1 / 2)) := by
  simp only [lpPoly, Finset.sum_range_succ, Finset.sum_range_zero, certKiss8, gegenbauerPoly]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one, eval_zero]
  ring

/-- Nonpositivity on `[-1, 1/2]`, from the factorization: one square, one
multiplier pair, no `nlinarith`. -/
noncomputable def certKiss8SOS :
    Certificate.IntervalCert (-1) (1 / 2) (lpPoly 8 6 certKiss8) where
  sqAB := [X * (X + C (1 / 2))]
  identity := by
    rw [lpPoly_certKiss8]
    apply Polynomial.funext
    intro x
    simp [Certificate.sosPoly]
    ring

theorem lpReal_certKiss8_nonpos {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1 / 2) :
    lpReal 8 6 certKiss8 t ≤ 0 :=
  Certificate.aeval_nonpos_of_intervalCert certKiss8SOS
    (by push_cast; linarith) (by push_cast; linarith)

theorem certKiss8_nonneg : ∀ k ∈ range 7, 0 ≤ certKiss8 k := by
  intro k hk
  rw [mem_range] at hk
  interval_cases k <;> norm_num [certKiss8]

theorem sum_certKiss8 : ∑ k ∈ range 7, certKiss8 k = 9 / 4 := by
  norm_num [Finset.sum_range_succ, certKiss8]

/-- **The kissing number of `ℝ^8` is at most 240.** -/
theorem kissingLe_eight : kissingLe 8 240 := by
  intro M c hc
  have h := card_le_of_sphereCert (d := 8) (N := 6) (f := certKiss8) (by norm_num)
    (fun k _ => schoenbergPos_all (by norm_num) k)
    certKiss8_nonneg (by norm_num [certKiss8])
    (fun _ h1 h2 => lpReal_certKiss8_nonpos h1 h2) c hc
  rw [sum_certKiss8, show certKiss8 0 = 3 / 320 from rfl] at h
  norm_num at h
  exact_mod_cast h

/-! ## Dimension 24 -/

/-- The Gegenbauer coefficients of `(t+1)(t+1/2)²(t+1/4)² t² (t-1/4)²(t-1/2)` in
dimension `24`. -/
def certKiss24 : ℕ → ℚ
  | 0 => 15 / 1490944
  | 1 => 45 / 186368
  | 2 => 3795 / 1949696
  | 3 => 10005 / 905216
  | 4 => 3983025 / 101384192
  | 5 => 56235 / 487424
  | 6 => 2040905 / 8716288
  | 7 => 270135 / 661504
  | 8 => 16675 / 34816
  | 9 => 150075 / 330752
  | 10 => 310155 / 1323008
  | _ => 0

theorem lpPoly_certKiss24 :
    lpPoly 24 10 certKiss24
      = (X + 1) * (X + C (1 / 2)) ^ 2 * (X + C (1 / 4)) ^ 2 * X ^ 2 * (X - C (1 / 4)) ^ 2
          * (X - C (1 / 2)) := by
  simp only [lpPoly, Finset.sum_range_succ, Finset.sum_range_zero, certKiss24, gegenbauerPoly]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one, eval_zero]
  ring

noncomputable def certKiss24SOS :
    Certificate.IntervalCert (-1) (1 / 2) (lpPoly 24 10 certKiss24) where
  sqAB := [X * (X + C (1 / 2)) * (X + C (1 / 4)) * (X - C (1 / 4))]
  identity := by
    rw [lpPoly_certKiss24]
    apply Polynomial.funext
    intro x
    simp [Certificate.sosPoly]
    ring

theorem lpReal_certKiss24_nonpos {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1 / 2) :
    lpReal 24 10 certKiss24 t ≤ 0 :=
  Certificate.aeval_nonpos_of_intervalCert certKiss24SOS
    (by push_cast; linarith) (by push_cast; linarith)

theorem certKiss24_nonneg : ∀ k ∈ range 11, 0 ≤ certKiss24 k := by
  intro k hk
  rw [mem_range] at hk
  interval_cases k <;> norm_num [certKiss24]

theorem sum_certKiss24 : ∑ k ∈ range 11, certKiss24 k = 2025 / 1024 := by
  norm_num [Finset.sum_range_succ, certKiss24]

/-- **The kissing number of `ℝ^24` is at most 196560.** -/
theorem kissingLe_twentyFour : kissingLe 24 196560 := by
  intro M c hc
  have h := card_le_of_sphereCert (d := 24) (N := 10) (f := certKiss24) (by norm_num)
    (fun k _ => schoenbergPos_all (by norm_num) k)
    certKiss24_nonneg (by norm_num [certKiss24])
    (fun _ h1 h2 => lpReal_certKiss24_nonpos h1 h2) c hc
  rw [sum_certKiss24, show certKiss24 0 = 15 / 1490944 from rfl] at h
  norm_num at h
  exact_mod_cast h

/-! ## Saturation

Both quotients are exact integers, and they are the true kissing numbers. The
route is therefore closed: no better certificate exists in this family, and no
rounding was involved in reading the bound off it.
-/

theorem kissing_bound_eight_tight :
    (∑ k ∈ range 7, certKiss8 k) / certKiss8 0 = 240 := by
  norm_num [Finset.sum_range_succ, certKiss8]

theorem kissing_bound_twentyFour_tight :
    (∑ k ∈ range 11, certKiss24 k) / certKiss24 0 = 196560 := by
  norm_num [Finset.sum_range_succ, certKiss24]

/-! ## Negative controls -/

/-- The dimension-8 coefficient vector, read in dimension `24`. -/
theorem lpPoly_certKiss8_dim_twentyFour :
    lpPoly 24 6 certKiss8
      = C (154 / 345) * X ^ 6 + C (189 / 230) * X ^ 5 + C (6671 / 11500) * X ^ 4
        + C (51 / 184) * X ^ 3 + C (277 / 2875) * X ^ 2 + C (3 / 115) * X
        + C (151 / 69000) := by
  simp only [lpPoly, Finset.sum_range_succ, Finset.sum_range_zero, certKiss8, gegenbauerPoly]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one, eval_zero]
  ring

/-- **A certificate does not travel.** The same nonnegative coefficients, in
dimension `24`, give a polynomial that is positive at `t = 0` — a point inside
`[-1, 1/2]`. The Gegenbauer basis depends on `d`, and so does feasibility. -/
theorem certKiss8_fails_dim_twentyFour :
    ¬ ∀ t : ℝ, -1 ≤ t → t ≤ 1 / 2 → lpReal 24 6 certKiss8 t ≤ 0 := by
  intro h
  have h0 := h 0 (by norm_num) (by norm_num)
  rw [lpReal, lpPoly_certKiss8_dim_twentyFour] at h0
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast] at h0
  norm_num at h0

/-- The degree-`8` candidate in dimension `24`: same construction, but with the
root at `-1/4` dropped. -/
def certKiss24Short : ℕ → ℚ
  | 0 => -5 / 39936
  | 1 => 11 / 11648
  | 2 => 23 / 21504
  | 3 => 115 / 9984
  | 4 => 330625 / 6336512
  | 5 => 13225 / 91392
  | 6 => 805 / 4096
  | 7 => 1035 / 2176
  | 8 => 3335 / 8704
  | _ => 0

theorem lpPoly_certKiss24Short :
    lpPoly 24 8 certKiss24Short
      = (X + 1) * (X + C (1 / 2)) ^ 2 * X ^ 2 * (X - C (1 / 4)) ^ 2 * (X - C (1 / 2)) := by
  simp only [lpPoly, Finset.sum_range_succ, Finset.sum_range_zero, certKiss24Short,
    gegenbauerPoly]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one, eval_zero]
  ring

/-- **Degree is not free.** Drop one root and the constant Gegenbauer coefficient
goes negative, so `card_le_of_sphereCert` refuses the certificate. -/
theorem certKiss24Short_zero_neg : certKiss24Short 0 < 0 := by
  norm_num [certKiss24Short]

/-- ...and it must refuse it: the quotient the rejected certificate would produce
is negative, which is not a bound on a cardinality. -/
theorem certKiss24Short_bound_absurd :
    (∑ k ∈ range 9, certKiss24Short k) / certKiss24Short 0 < 0 := by
  norm_num [Finset.sum_range_succ, certKiss24Short]

/-- Outside the interval the certificate is positive, and must be: `f 1 = 9/4` is
the numerator of the bound. -/
theorem lpReal_certKiss8_one_pos : 0 < lpReal 8 6 certKiss8 1 := by
  rw [lpReal_one (by norm_num), sum_certKiss8]
  norm_num

theorem lpReal_certKiss24_one_pos : 0 < lpReal 24 10 certKiss24 1 := by
  rw [lpReal_one (by norm_num), sum_certKiss24]
  norm_num

/-- **The multipliers are load-bearing.** `-f` is negative at `1`, so no
decomposition of it as a bare sum of squares exists: any certificate for `f` is
tied to the interval `[-1, 1/2]` it was written for. -/
theorem neg_lpPoly_certKiss8_not_sos (ps : List ℚ[X]) :
    -(lpPoly 8 6 certKiss8) ≠ Certificate.sosPoly ps := by
  refine Certificate.not_sosPoly_of_aeval_neg (t := 1) ?_ ps
  rw [lpPoly_certKiss8]
  simp only [map_neg, map_mul, map_pow, map_add, map_sub, map_one, aeval_C, aeval_X, eq_ratCast]
  norm_num

end Delsarte.Sphere
