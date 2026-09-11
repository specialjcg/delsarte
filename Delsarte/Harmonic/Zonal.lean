/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Harmonic.Fischer
import Delsarte.Sphere.LP

/-!
# The zonal polynomial: Gegenbauer, homogenised, and harmonic

`Delsarte/Harmonic/Fischer.lean` says that a harmonic polynomial is orthogonal to
every multiple of `rSq`. This file produces the harmonic polynomial, and it is not
a new object: it is `G_k` with the sphere condition put back in as a variable.

## The construction

`zonal d x k` is a polynomial in `y`, of degree `k`, with `x` as a parameter. Its
recurrence is the one of `Delsarte.gegenbauer`, with `t` replaced by the linear
form `⟪x, y⟫` and the constant term multiplied by `‖x‖² ‖y‖²` to restore
homogeneity:

`Z_(k+2) = A_k ⟪x,·⟫ Z_(k+1) - B_k ‖x‖² rSq Z_k`

with `A_k = (2k+d)/(k+d-1)` and `B_k = (k+1)/(k+d-1)` taken verbatim from
`Delsarte.gegenbauer`. On the unit sphere `rSq` evaluates to `1` and `‖x‖² = 1`,
so `eval_zonal` is a two-line induction: the same recurrence, read twice.

## Harmonicity, and the one lemma that is not bookkeeping

`mvLaplacian_zonal` is the point of the file. It follows from a single identity,
`dirDeriv_zonal`:

`∑_i x_i ∂_i Z_(k+1) = (k+1) ‖x‖² Z_k`

Given it, the Laplacian of the recurrence collapses: `Δ` of the first term
contributes `2 ∑_i x_i ∂_i Z_(k+1)`, `Δ` of the second contributes
`(2d + 4k) Z_k` by Euler's identity, and the two cancel because

`A_k (k+1) - B_k (d + 2k) = 0`

both sides being `(k+1)(2k+d)/(k+d-1)`. Nothing is left over.

`dirDeriv_zonal` itself is a two-step induction. Its step reduces to two
identities between rational functions of `k` and `d`,

`(k+2-A_k) A_(k-1) = A_k (k+1) - 2 B_k`    and    `(k+2-A_k) B_(k-1) = k B_k`

whose common key is `k + 2 - A_k = (k+d-2)(k+1)/(k+d-1)`. Both were verified
symbolically for `d ∈ {2,3,4,5}` and `k ≤ 7` before a line was written; they are
closed here by `field_simp` and `ring`.

## Why `2 ≤ d` and why unit vectors

The recurrence divides by `k + d - 1`, which vanishes at `k = 0`, `d = 1`. That is
the only degenerate case, and `mvLaplacian_zonal` carries the hypothesis rather
than hiding it.

`eval_zonal` needs `‖x‖ = ‖y‖ = 1`: what is true in general is the homogenised
identity, and the equality with `gegenbauerReal` is its restriction to the sphere.
`eval_zonal_not_of_non_unit` exhibits the failure off the sphere rather than
leaving it to be assumed.

## What this file does not claim

Nothing here mentions a code, a configuration of points, or a bound. The Gram
matrix appears only in `Delsarte/Sphere/Schoenberg.lean`.
-/

namespace Delsarte.Harmonic

open Finset MvPolynomial Delsarte Delsarte.Sphere

variable {d : ℕ}

/-! ## Operator calculus

The two first-order operators used below, and the Leibniz rules they obey. All of
this is generic: no Gegenbauer, no zonal polynomial. -/

/-- The derivative in the direction `x`. -/
noncomputable def dirDeriv (x : Fin d → ℝ) (p : MvPolynomial (Fin d) ℝ) :
    MvPolynomial (Fin d) ℝ := ∑ i, C (x i) * pderiv i p

/-- The pointwise product of two gradients. -/
noncomputable def gradDot (p q : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, pderiv i p * pderiv i q

theorem dirDeriv_add (x : Fin d → ℝ) (p q : MvPolynomial (Fin d) ℝ) :
    dirDeriv x (p + q) = dirDeriv x p + dirDeriv x q := by
  simp only [dirDeriv, map_add, mul_add]
  rw [Finset.sum_add_distrib]

theorem dirDeriv_sub (x : Fin d → ℝ) (p q : MvPolynomial (Fin d) ℝ) :
    dirDeriv x (p - q) = dirDeriv x p - dirDeriv x q := by
  simp only [dirDeriv, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]

theorem dirDeriv_C_mul (x : Fin d → ℝ) (c : ℝ) (p : MvPolynomial (Fin d) ℝ) :
    dirDeriv x (C c * p) = C c * dirDeriv x p := by
  simp only [dirDeriv, pderiv_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dirDeriv_mul (x : Fin d → ℝ) (p q : MvPolynomial (Fin d) ℝ) :
    dirDeriv x (p * q) = dirDeriv x p * q + p * dirDeriv x q := by
  simp only [dirDeriv, pderiv_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring)
    (Finset.sum_congr rfl fun i _ => by ring)

theorem dirDeriv_linForm (x y : Fin d → ℝ) :
    dirDeriv x (linForm y) = C (∑ i, x i * y i) := by
  simp only [dirDeriv, pderiv_linForm, ← map_mul, ← map_sum]

@[simp]
theorem dirDeriv_one (x : Fin d → ℝ) : dirDeriv x (1 : MvPolynomial (Fin d) ℝ) = 0 := by
  simp [dirDeriv]

theorem dirDeriv_linForm_self (x : Fin d → ℝ) :
    dirDeriv x (linForm x) = C (∑ i, (x i) ^ 2) := by
  rw [dirDeriv_linForm]
  exact congrArg C (Finset.sum_congr rfl fun i _ => (sq (x i)).symm)

theorem pderiv_rSq (i : Fin d) :
    pderiv i (rSq d) = (2 : MvPolynomial (Fin d) ℝ) * X i := by
  classical
  rw [rSq, map_sum, Finset.sum_eq_single i]
  · rw [pderiv_pow, pderiv_X_self, mul_one, pow_one]
    norm_num
  · intro j _ hj
    rw [pderiv_pow, pderiv_X_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem dirDeriv_rSq (x : Fin d → ℝ) :
    dirDeriv x (rSq d) = (2 : MvPolynomial (Fin d) ℝ) * linForm x := by
  simp only [dirDeriv, pderiv_rSq, linForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mvLaplacian_add (p q : MvPolynomial (Fin d) ℝ) :
    mvLaplacian (p + q) = mvLaplacian p + mvLaplacian q := by
  simp only [mvLaplacian, map_add]
  rw [Finset.sum_add_distrib]

theorem mvLaplacian_sub (p q : MvPolynomial (Fin d) ℝ) :
    mvLaplacian (p - q) = mvLaplacian p - mvLaplacian q := by
  simp only [mvLaplacian, map_sub]
  rw [Finset.sum_sub_distrib]

theorem mvLaplacian_C_mul (c : ℝ) (p : MvPolynomial (Fin d) ℝ) :
    mvLaplacian (C c * p) = C c * mvLaplacian p := by
  simp only [mvLaplacian, pderiv_C_mul, Finset.mul_sum]

/-- The Leibniz rule for the Laplacian. The cross term is what makes harmonicity
a statement about `dirDeriv`. -/
theorem mvLaplacian_mul (p q : MvPolynomial (Fin d) ℝ) :
    mvLaplacian (p * q)
      = mvLaplacian p * q + 2 * gradDot p q + p * mvLaplacian q := by
  simp only [mvLaplacian, gradDot, pderiv_mul, map_add, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

@[simp]
theorem mvLaplacian_linForm (x : Fin d → ℝ) : mvLaplacian (linForm x) = 0 := by
  simp only [mvLaplacian, pderiv_linForm, pderiv_C, Finset.sum_const_zero]

theorem mvLaplacian_rSq : mvLaplacian (rSq d) = C (2 * (d : ℝ)) := by
  have h : ∀ i : Fin d, pderiv i (pderiv i (rSq d)) = (2 : MvPolynomial (Fin d) ℝ) := by
    intro i
    rw [pderiv_rSq, pderiv_mul, pderiv_X_self, mul_one,
      show (2 : MvPolynomial (Fin d) ℝ) = C (2 : ℝ) from
        (map_ofNat (C : ℝ →+* MvPolynomial (Fin d) ℝ) 2).symm, pderiv_C]
    ring
  rw [mvLaplacian, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_mul,
    map_ofNat (C : ℝ →+* MvPolynomial (Fin d) ℝ) 2,
    ← map_natCast (C : ℝ →+* MvPolynomial (Fin d) ℝ) d]
  ring

theorem gradDot_linForm_left (x : Fin d → ℝ) (p : MvPolynomial (Fin d) ℝ) :
    gradDot (linForm x) p = dirDeriv x p := by
  simp only [gradDot, dirDeriv, pderiv_linForm]

theorem gradDot_rSq_left {k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k) :
    gradDot (rSq d) p = C (2 * (k : ℝ)) * p := by
  simp only [gradDot, pderiv_rSq]
  have h : ∑ i, (2 : MvPolynomial (Fin d) ℝ) * X i * pderiv i p
      = 2 * ∑ i, X i * pderiv i p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, hp.sum_X_mul_pderiv, nsmul_eq_mul, map_mul,
    map_ofNat (C : ℝ →+* MvPolynomial (Fin d) ℝ) 2,
    ← map_natCast (C : ℝ →+* MvPolynomial (Fin d) ℝ) k]
  ring

/-! ## The zonal polynomial -/

/-- The coefficient of the linear term in the Gegenbauer recurrence. -/
noncomputable def zonalA (d k : ℕ) : ℝ := (2 * (k : ℝ) + d) / ((k : ℝ) + d - 1)

/-- The coefficient of the constant term in the Gegenbauer recurrence. -/
noncomputable def zonalB (d k : ℕ) : ℝ := ((k : ℝ) + 1) / ((k : ℝ) + d - 1)

theorem zonal_denom_pos (hd : 2 ≤ d) (k : ℕ) : 0 < (k : ℝ) + d - 1 := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem zonal_denom_ne_zero (hd : 2 ≤ d) (k : ℕ) : ((k : ℝ) + d - 1) ≠ 0 :=
  (zonal_denom_pos hd k).ne'

theorem zonalA_pos (hd : 2 ≤ d) (k : ℕ) : 0 < zonalA d k := by
  have hnum : (0 : ℝ) < 2 * (k : ℝ) + d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact div_pos hnum (zonal_denom_pos hd k)

/-- Gegenbauer, homogenised: a polynomial in `y` of degree `k`, parameterised by
`x`. The coefficients are those of `Delsarte.gegenbauer`, unchanged. -/
noncomputable def zonal (d : ℕ) (x : Fin d → ℝ) : ℕ → MvPolynomial (Fin d) ℝ
  | 0 => 1
  | 1 => linForm x
  | (k + 2) =>
      C (zonalA d k) * linForm x * zonal d x (k + 1)
        - C (zonalB d k * ∑ i, (x i) ^ 2) * rSq d * zonal d x k

theorem zonal_zero (x : Fin d → ℝ) : zonal d x 0 = 1 := rfl

theorem zonal_one (x : Fin d → ℝ) : zonal d x 1 = linForm x := rfl

theorem zonal_add_two (x : Fin d → ℝ) (k : ℕ) :
    zonal d x (k + 2)
      = C (zonalA d k) * linForm x * zonal d x (k + 1)
        - C (zonalB d k * ∑ i, (x i) ^ 2) * rSq d * zonal d x k := rfl

theorem rSq_isHomogeneous : (rSq d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => by
    simpa using isHomogeneous_X_pow (R := ℝ) i 2

theorem zonal_isHomogeneous (x : Fin d → ℝ) (k : ℕ) : (zonal d x k).IsHomogeneous k := by
  induction k using Nat.twoStepInduction with
  | zero => rw [zonal_zero]; exact isHomogeneous_one (Fin d) ℝ
  | one => rw [zonal_one]; exact linForm_isHomogeneous x
  | more k h1 h2 =>
      rw [zonal_add_two]
      refine IsHomogeneous.sub ?_ ?_
      · have h := ((linForm_isHomogeneous x).C_mul (zonalA d k)).mul h2
        rwa [show 1 + (k + 1) = k + 2 from by omega] at h
      · have h := ((rSq_isHomogeneous (d := d)).C_mul
          (zonalB d k * ∑ i, (x i) ^ 2)).mul h1
        rwa [show 2 + k = k + 2 from by omega] at h

/-! ## Evaluation: on the sphere this is Gegenbauer -/

theorem gegenbauerReal_add_two (d k : ℕ) (t : ℝ) :
    gegenbauerReal d (k + 2) t
      = (2 * (k : ℝ) + d) / ((k : ℝ) + d - 1) * t * gegenbauerReal d (k + 1) t
        - ((k : ℝ) + 1) / ((k : ℝ) + d - 1) * gegenbauerReal d k t := by
  simp only [gegenbauerReal, gegenbauerPoly_add_two, map_sub, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C, eq_ratCast]
  push_cast
  ring

theorem eval_zonal (x y : Fin d → ℝ) (hx : ∑ i, (x i) ^ 2 = 1) (hy : ∑ i, (y i) ^ 2 = 1)
    (k : ℕ) : eval y (zonal d x k) = gegenbauerReal d k (∑ i, x i * y i) := by
  have hL : eval y (linForm x) = ∑ i, x i * y i := eval_linForm x y
  have hR : eval y (rSq d) = 1 := by
    rw [rSq, map_sum]
    simpa using hy
  induction k using Nat.twoStepInduction with
  | zero => rw [zonal_zero]; simp
  | one => rw [zonal_one, hL, gegenbauerReal_one]
  | more k h1 h2 =>
      rw [zonal_add_two, map_sub, map_mul, map_mul, map_mul, map_mul, eval_C, eval_C, hL, hR,
        h1, h2, gegenbauerReal_add_two, zonalA, zonalB, hx]
      ring

/-! ## The leading coefficient -/

/-- The coefficient of `⟪x,y⟫^k` in `zonal d x k`. -/
noncomputable def zonalLead (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (k + 2) => zonalA d k * zonalLead d (k + 1)

theorem zonalLead_pos (hd : 2 ≤ d) (k : ℕ) : 0 < zonalLead d k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [zonalLead]
  | one => norm_num [zonalLead]
  | more k _ h2 => exact mul_pos (zonalA_pos hd k) h2

/-- Everything but the leading term carries a factor `rSq`. This is what lets the
Fischer adjunction discard it. -/
theorem rSq_dvd_zonal_sub (x : Fin d → ℝ) (k : ℕ) :
    rSq d ∣ zonal d x k - C (zonalLead d k) * linForm x ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => rw [zonal_zero]; simp [zonalLead]
  | one => rw [zonal_one]; simp [zonalLead]
  | more k _ h2 =>
      obtain ⟨w, hw⟩ := h2
      refine ⟨C (zonalA d k) * linForm x * w
        - C (zonalB d k * ∑ i, (x i) ^ 2) * zonal d x k, ?_⟩
      have hkey : zonal d x (k + 1)
          = C (zonalLead d (k + 1)) * linForm x ^ (k + 1) + rSq d * w := by
        rw [← hw]; ring
      rw [zonal_add_two, show zonalLead d (k + 2) = zonalA d k * zonalLead d (k + 1) from rfl,
        hkey]
      simp only [map_mul]
      ring

/-! ## The key identity, and harmonicity -/

/-- **The lemma the file exists for.** Differentiating the zonal polynomial in the
direction `x` drops the degree by one and multiplies by `(k+1) ‖x‖²`.

A two-step induction whose step is two identities between rational functions of
`k` and `d`. -/
theorem dirDeriv_zonal (hd : 2 ≤ d) (x : Fin d → ℝ) (k : ℕ) :
    dirDeriv x (zonal d x (k + 1))
      = C (((k : ℝ) + 1) * ∑ i, (x i) ^ 2) * zonal d x k := by
  have key : ∀ m : ℕ,
      (dirDeriv x (zonal d x (m + 1))
          = C (((m : ℝ) + 1) * ∑ i, (x i) ^ 2) * zonal d x m)
        ∧ (dirDeriv x (zonal d x (m + 2))
          = C (((m : ℝ) + 2) * ∑ i, (x i) ^ 2) * zonal d x (m + 1)) := by
    intro m
    induction m with
    | zero =>
        constructor
        · rw [zonal_one, zonal_zero, dirDeriv_linForm_self]
          norm_num
        · have hAB : zonalA d 0 - zonalB d 0 = 1 := by
            rw [zonalA, zonalB]
            have hne : ((0 : ℕ) : ℝ) + d - 1 ≠ 0 := zonal_denom_ne_zero hd 0
            field_simp at hne ⊢
            ring
          have hexp : zonal d x (0 + 2)
              = C (zonalA d 0) * (linForm x * zonal d x 1)
                - C (zonalB d 0 * ∑ i, (x i) ^ 2) * (rSq d * zonal d x 0) := by
            rw [zonal_add_two]; ring
          rw [hexp, zonal_one, zonal_zero, dirDeriv_sub, dirDeriv_C_mul, dirDeriv_C_mul,
            dirDeriv_mul, dirDeriv_mul, dirDeriv_linForm_self, dirDeriv_rSq, dirDeriv_one]
          have H := congrArg (C : ℝ → MvPolynomial (Fin d) ℝ) hAB
          simp only [map_mul, map_add, map_sub, map_one, map_ofNat, map_natCast] at H ⊢
          push_cast
          linear_combination (2 * C (∑ i, (x i) ^ 2) * linForm x) * H
    | succ n ih =>
        refine ⟨?_, ?_⟩
        · push_cast
          rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 from by ring]
          exact ih.2
        have h1 : zonalA d (n + 1) * zonalA d n + zonalA d (n + 1) * ((n : ℝ) + 2)
              - 2 * zonalB d (n + 1) = ((n : ℝ) + 3) * zonalA d n := by
          rw [zonalA, zonalA, zonalB]
          have h0 : ((n : ℝ) + d - 1) ≠ 0 := zonal_denom_ne_zero hd n
          have h1' : (((n + 1 : ℕ) : ℝ) + d - 1) ≠ 0 := zonal_denom_ne_zero hd (n + 1)
          push_cast at h1' ⊢
          field_simp
          ring
        have h2 : zonalA d (n + 1) * zonalB d n + zonalB d (n + 1) * ((n : ℝ) + 1)
              = ((n : ℝ) + 3) * zonalB d n := by
          rw [zonalA, zonalB, zonalB]
          have h0 : ((n : ℝ) + d - 1) ≠ 0 := zonal_denom_ne_zero hd n
          have h1' : (((n + 1 : ℕ) : ℝ) + d - 1) ≠ 0 := zonal_denom_ne_zero hd (n + 1)
          push_cast at h1' ⊢
          field_simp
          ring
        have hexp : zonal d x (n + 1 + 2)
            = C (zonalA d (n + 1)) * (linForm x * zonal d x (n + 2))
              - C (zonalB d (n + 1) * ∑ i, (x i) ^ 2) * (rSq d * zonal d x (n + 1)) := by
          rw [zonal_add_two]; ring
        rw [hexp, dirDeriv_sub, dirDeriv_C_mul, dirDeriv_C_mul, dirDeriv_mul, dirDeriv_mul,
          dirDeriv_linForm_self, dirDeriv_rSq, ih.1, ih.2, zonal_add_two]
        have H1 := congrArg (C : ℝ → MvPolynomial (Fin d) ℝ) h1
        have H2 := congrArg (C : ℝ → MvPolynomial (Fin d) ℝ) h2
        simp only [map_mul, map_add, map_sub, map_one, map_ofNat, map_natCast] at H1 H2 ⊢
        push_cast
        linear_combination (C (∑ i, (x i) ^ 2) * linForm x * zonal d x (n + 1)) * H1
          - (C (∑ i, (x i) ^ 2) * C (∑ i, (x i) ^ 2) * rSq d * zonal d x n) * H2
  exact (key k).1

/-- **Harmonicity.** The zonal polynomial is annihilated by the Laplacian, in
every degree and every dimension `d ≥ 2`. -/
theorem mvLaplacian_zonal (hd : 2 ≤ d) (x : Fin d → ℝ) (k : ℕ) :
    mvLaplacian (zonal d x k) = 0 := by
  induction k using Nat.twoStepInduction with
  | zero =>
      rw [zonal_zero, show (1 : MvPolynomial (Fin d) ℝ) = C 1 from (map_one C).symm]
      simp [mvLaplacian]
  | one => rw [zonal_one, mvLaplacian_linForm]
  | more k h1 h2 =>
      have hAB : zonalA d k * (((k : ℝ) + 1) * 2)
          = zonalB d k * (2 * (d : ℝ) + 2 * (2 * (k : ℝ))) := by
        rw [zonalA, zonalB]
        have h0 : ((k : ℝ) + d - 1) ≠ 0 := zonal_denom_ne_zero hd k
        field_simp
        ring
      have hexp : zonal d x (k + 2)
          = C (zonalA d k) * (linForm x * zonal d x (k + 1))
            - C (zonalB d k * ∑ i, (x i) ^ 2) * (rSq d * zonal d x k) := by
        rw [zonal_add_two]; ring
      rw [hexp, mvLaplacian_sub, mvLaplacian_C_mul, mvLaplacian_C_mul, mvLaplacian_mul,
        mvLaplacian_mul, mvLaplacian_linForm, mvLaplacian_rSq, h1, h2,
        gradDot_linForm_left, gradDot_rSq_left (zonal_isHomogeneous x k),
        dirDeriv_zonal hd]
      have H := congrArg (C : ℝ → MvPolynomial (Fin d) ℝ) hAB
      simp only [map_mul, map_add, map_one, map_ofNat, map_natCast] at H ⊢
      linear_combination (C (∑ i, (x i) ^ 2) * zonal d x k) * H

/-! ### Controls

Three hypotheses appear above. Each is load-bearing, and each is measured here
rather than asserted.
-/

/-- `eval_zonal` is the restriction to the sphere of a homogeneous identity, not
the identity itself. At `d = 2` with `‖x‖ = 2` the two sides are `4` and `7`. -/
theorem eval_zonal_not_of_non_unit :
    eval (![1, 0] : Fin 2 → ℝ) (zonal 2 (![2, 0] : Fin 2 → ℝ) 2) = 4
      ∧ gegenbauerReal 2 2 (∑ i, (![2, 0] : Fin 2 → ℝ) i * (![1, 0] : Fin 2 → ℝ) i) = 7 := by
  constructor
  · rw [zonal_add_two, zonal_one, zonal_zero]
    simp [linForm, rSq, zonalA, zonalB, Fin.sum_univ_two]
    norm_num
  · rw [show (∑ i, (![2, 0] : Fin 2 → ℝ) i * (![1, 0] : Fin 2 → ℝ) i) = 2 from by
      simp [Fin.sum_univ_two]]
    rw [gegenbauerReal_add_two, gegenbauerReal_one, gegenbauerReal_zero]
    norm_num

/-- `dirDeriv_zonal` genuinely needs `2 ≤ d`: at `d = 1` the recurrence divides by
`k + d - 1 = 0` at `k = 0`, the degree-two zonal collapses to `0`, and the
identity asserts `0 = C 2 * X₀`. -/
theorem dirDeriv_zonal_not_of_dim_one :
    dirDeriv (![1] : Fin 1 → ℝ) (zonal 1 (![1] : Fin 1 → ℝ) 2) = 0
      ∧ C (2 : ℝ) * zonal 1 (![1] : Fin 1 → ℝ) 1 ≠ 0 := by
  have hz : zonal 1 (![1] : Fin 1 → ℝ) 2 = 0 := by
    rw [zonal_add_two]
    norm_num [zonalA, zonalB]
  refine ⟨by rw [hz]; simp [dirDeriv], ?_⟩
  rw [zonal_one]
  intro h
  have hc := congrArg (coeff (Finsupp.single (0 : Fin 1) 1)) h
  simp [linForm, coeff_C_mul, coeff_X] at hc

/-- The leading coefficient in dimension `2` is the Chebyshev one, `2^(k-1)`.
This crosses `zonalLead`, defined here from `zonalA`, with
`gegenbauerPoly_two_three`, proved in `Delsarte/Sphere/LP.lean` without ever
mentioning this file. -/
theorem zonalLead_two_three : zonalLead 2 3 = 4 := by
  norm_num [zonalLead, zonalA]

theorem gegenbauerPoly_two_three_coeff : (gegenbauerPoly 2 3).coeff 3 = 4 := by
  rw [gegenbauerPoly_two_three]
  simp [Polynomial.coeff_X]

end Delsarte.Harmonic
