/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Gegenbauer.Basic
import Delsarte.Certificate.Interval
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Delsarte LP on the sphere (Odlyzko-Sloane)

The sphere counterpart of `Delsarte.Hamming.LP`, and staged the same way: the
bound is proved *conditionally* on the positive-definiteness of the Gegenbauer
basis, which is stated here as `SchoenbergPos` and discharged elsewhere.

## The bound

If `f = ∑_(k ≤ N) f_k G_k` has `f_k ≥ 0`, `f_0 > 0`, and `f t ≤ 0` for
`t ∈ [-1, 1/2]`, then any family of unit vectors of `ℝ^d` with pairwise inner
products at most `1/2` has at most `f 1 / f_0` members.

Because the basis is normalized by `G_k 1 = 1`, `f 1 = ∑_k f_k`, so the bound is
a ratio of two rationals read straight off the certificate — no evaluation in
`ℝ` is needed to state it. Evaluation in `ℝ` happens only inside the proof, and
the certificate itself never leaves `ℚ`.

## What is assumed and what is proved

`SchoenbergPos d k` — that `∑_(i,j) G_k ⟪x i, x j⟫ ≥ 0` for every finite family
of unit vectors — is a hypothesis of `card_le_of_sphereCert`, not a theorem. It
is the continuous analogue of `Delsarte.Hamming.sum_sum_krawtchouk_nonneg`, and
the hard point of this whole side: in general it needs the addition formula for
spherical harmonics. Two cases are proved unconditionally here, `k = 0` and
`k = 1`, which is enough to show the property is not vacuous but not enough to
carry a useful certificate.

So nothing in this file is an unconditional bound on any kissing number.

## Checking `f t ≤ 0` on an interval

The hypothesis `hneg` quantifies over a real interval, so it is not a finite
computation. The method chosen for discharging it on concrete certificates is a
*sum-of-squares certificate on the interval*: exhibit rational polynomials with

`-f = σ₀ + (t + 1) (1/2 - t) σ₁`, each `σ` a sum of squares.

and that is what `Delsarte.Certificate.IntervalCert` implements. Soundness is
immediate — on `[-1, 1/2]` the factors are nonnegative and so is every square —
and soundness is all that is needed. The existence direction (Markov-Lukács) never
has to be formalized, because the decomposition is supplied, not derived.

The witness below goes through that machinery rather than around it:
`certCircleSOS` writes `-f` as `(1/2 - X) * (2 (X + 1)) ^ 2`, one square and one
multiplier, and `lpReal_certCircle_nonpos` reads off the interval hypothesis from
it.
-/

namespace Delsarte.Sphere

open Finset Polynomial Delsarte

variable {d M N : ℕ}

/-! ## Gegenbauer at a real argument

The certificate stays rational; only the evaluation is real. `gegenbauerReal` is
`aeval` of the rational polynomial, so every identity proved over `ℚ` transfers.
-/

/-- The Gegenbauer polynomial of dimension `d` and degree `k`, evaluated at a
real point. -/
noncomputable def gegenbauerReal (d k : ℕ) (t : ℝ) : ℝ := aeval t (gegenbauerPoly d k)

@[simp]
theorem gegenbauerReal_zero (d : ℕ) (t : ℝ) : gegenbauerReal d 0 t = 1 := by
  simp [gegenbauerReal]

@[simp]
theorem gegenbauerReal_one (d : ℕ) (t : ℝ) : gegenbauerReal d 1 t = t := by
  simp [gegenbauerReal]

theorem gegenbauerReal_ratCast (d k : ℕ) (t : ℚ) :
    gegenbauerReal d k (t : ℝ) = ((gegenbauer d k t : ℚ) : ℝ) := by
  rw [gegenbauerReal, show ((t : ℝ)) = algebraMap ℚ ℝ t by simp,
    aeval_algebraMap_apply_eq_algebraMap_eval, eval_gegenbauerPoly]
  simp

theorem gegenbauerReal_eval_one (hd : 2 ≤ d) (k : ℕ) : gegenbauerReal d k 1 = 1 := by
  rw [show ((1 : ℝ)) = ((1 : ℚ) : ℝ) by norm_num, gegenbauerReal_ratCast,
    gegenbauer_eval_one hd]

/-! ## Configurations of unit vectors -/

/-- A finite family of unit vectors of `ℝ^d`. -/
structure UnitPoints (d M : ℕ) where
  /-- The points themselves. -/
  pts : Fin M → EuclideanSpace ℝ (Fin d)
  /-- Each one lies on the unit sphere. -/
  norm_pts : ∀ i, ‖pts i‖ = 1

namespace UnitPoints

/-- The Gram entry `⟪x i, x j⟫`. -/
noncomputable def gram (c : UnitPoints d M) (i j : Fin M) : ℝ := inner ℝ (c.pts i) (c.pts j)

@[simp]
theorem gram_self (c : UnitPoints d M) (i : Fin M) : c.gram i i = 1 := by
  rw [gram, real_inner_self_eq_norm_sq, c.norm_pts i]
  norm_num

/-- The Gram entry as a plain coordinate sum. -/
theorem gram_eq_sum (c : UnitPoints d M) (i j : Fin M) :
    c.gram i j = ∑ a, c.pts i a * c.pts j a := by
  rw [gram]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem neg_one_le_gram (c : UnitPoints d M) (i j : Fin M) : -1 ≤ c.gram i j := by
  have h := abs_real_inner_le_norm (c.pts i) (c.pts j)
  rw [c.norm_pts i, c.norm_pts j, one_mul] at h
  exact (abs_le.mp h).1

theorem gram_le_one (c : UnitPoints d M) (i j : Fin M) : c.gram i j ≤ 1 := by
  have h := abs_real_inner_le_norm (c.pts i) (c.pts j)
  rw [c.norm_pts i, c.norm_pts j, one_mul] at h
  exact (abs_le.mp h).2

end UnitPoints

/-! ## Schoenberg positive-definiteness

The continuous analogue of `Delsarte.Hamming.sum_sum_krawtchouk_nonneg`. Stated,
not proved: in general it follows from the addition formula for spherical
harmonics, which is not formalized here.
-/

/-- `G_k` is positive definite on the sphere of `ℝ^d`. -/
def SchoenbergPos (d k : ℕ) : Prop :=
  ∀ (M : ℕ) (c : UnitPoints d M), 0 ≤ ∑ i, ∑ j, gegenbauerReal d k (c.gram i j)

/-- Degree 0 is trivial: the sum is `M ^ 2`. -/
theorem schoenbergPos_zero (d : ℕ) : SchoenbergPos d 0 := by
  intro M c
  simp only [gegenbauerReal_zero, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_fin]
  positivity

/-- Degree 1 is the square of a norm, in every dimension: `∑_(i,j) ⟪x i, x j⟫ =
‖∑_i x i‖ ^ 2`. -/
theorem schoenbergPos_one (d : ℕ) : SchoenbergPos d 1 := by
  intro M c
  have h : ∑ i, ∑ j, gegenbauerReal d 1 (c.gram i j) = ‖∑ i, c.pts i‖ ^ 2 := by
    simp only [gegenbauerReal_one, UnitPoints.gram]
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun i _ => (inner_sum _ _ _).symm
  rw [h]
  positivity

/-! ## The certificate and the bound -/

/-- The polynomial `∑_(k ≤ N) f k * G_k`, with rational coefficients. -/
noncomputable def lpPoly (d N : ℕ) (f : ℕ → ℚ) : ℚ[X] :=
  ∑ k ∈ range (N + 1), C (f k) * gegenbauerPoly d k

/-- Its evaluation at a real point. -/
noncomputable def lpReal (d N : ℕ) (f : ℕ → ℚ) (t : ℝ) : ℝ := aeval t (lpPoly d N f)

theorem lpReal_eq_sum (d N : ℕ) (f : ℕ → ℚ) (t : ℝ) :
    lpReal d N f t = ∑ k ∈ range (N + 1), (f k : ℝ) * gegenbauerReal d k t := by
  simp [lpReal, lpPoly, gegenbauerReal]

/-- At `t = 1` the value is the plain sum of the coefficients — this is what the
normalization `G_k 1 = 1` buys. -/
theorem lpReal_one (hd : 2 ≤ d) (N : ℕ) (f : ℕ → ℚ) :
    lpReal d N f 1 = ((∑ k ∈ range (N + 1), f k : ℚ) : ℝ) := by
  rw [lpReal_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by rw [gegenbauerReal_eval_one hd, mul_one]

/-- **The Odlyzko-Sloane bound**, conditional on Schoenberg positivity.

A family of unit vectors of `ℝ^d` whose pairwise inner products are at most
`1/2` has at most `(∑_k f k) / f 0` members, for any certificate `f` that is
nonnegative in the Gegenbauer basis, has positive constant coefficient, and is
nonpositive on `[-1, 1/2]`. -/
theorem card_le_of_sphereCert (hd : 2 ≤ d) {f : ℕ → ℚ}
    (hS : ∀ k ∈ range (N + 1), SchoenbergPos d k)
    (hf : ∀ k ∈ range (N + 1), 0 ≤ f k) (hf0 : 0 < f 0)
    (hneg : ∀ t : ℝ, -1 ≤ t → t ≤ 1 / 2 → lpReal d N f t ≤ 0)
    (c : UnitPoints d M) (hc : ∀ i j, i ≠ j → c.gram i j ≤ 1 / 2) :
    (M : ℚ) ≤ (∑ k ∈ range (N + 1), f k) / f 0 := by
  -- Off the diagonal the certificate is nonpositive, on it the value is `f 1`.
  have hupper : ∑ i, ∑ j, lpReal d N f (c.gram i j)
      ≤ (M : ℝ) * ((∑ k ∈ range (N + 1), f k : ℚ) : ℝ) := by
    have hrow : ∀ i : Fin M, ∑ j, lpReal d N f (c.gram i j)
        ≤ ((∑ k ∈ range (N + 1), f k : ℚ) : ℝ) := by
      intro i
      have hsplit : ∑ j, lpReal d N f (c.gram i j)
          = ∑ j ∈ univ.erase i, lpReal d N f (c.gram i j) + lpReal d N f (c.gram i i) :=
        (Finset.sum_erase_add _ _ (mem_univ i)).symm
      have hoff : ∑ j ∈ univ.erase i, lpReal d N f (c.gram i j) ≤ 0 :=
        Finset.sum_nonpos fun j hj =>
          hneg _ (c.neg_one_le_gram i j) (hc i j (Ne.symm (mem_erase.mp hj).1))
      rw [hsplit, c.gram_self i, lpReal_one hd]
      linarith
    calc ∑ i, ∑ j, lpReal d N f (c.gram i j)
        ≤ ∑ _i : Fin M, ((∑ k ∈ range (N + 1), f k : ℚ) : ℝ) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (M : ℝ) * ((∑ k ∈ range (N + 1), f k : ℚ) : ℝ) := by
          simp [Finset.sum_const, Finset.card_univ]
  -- Expanding in the Gegenbauer basis, every term is nonnegative but the first.
  have hswap : ∑ i, ∑ j, lpReal d N f (c.gram i j)
      = ∑ k ∈ range (N + 1), (f k : ℝ) * ∑ i, ∑ j, gegenbauerReal d k (c.gram i j) := by
    simp only [lpReal_eq_sum]
    calc ∑ i : Fin M, ∑ j : Fin M, ∑ k ∈ range (N + 1),
            (f k : ℝ) * gegenbauerReal d k (c.gram i j)
        = ∑ i : Fin M, ∑ k ∈ range (N + 1), ∑ j : Fin M,
            (f k : ℝ) * gegenbauerReal d k (c.gram i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k ∈ range (N + 1), ∑ i : Fin M, ∑ j : Fin M,
            (f k : ℝ) * gegenbauerReal d k (c.gram i j) := Finset.sum_comm
      _ = ∑ k ∈ range (N + 1), (f k : ℝ) * ∑ i, ∑ j, gegenbauerReal d k (c.gram i j) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hk0 : ∑ i, ∑ j, gegenbauerReal d 0 (c.gram i j) = (M : ℝ) ^ 2 := by
    simp only [gegenbauerReal_zero, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fin]
    ring
  have hlower : (f 0 : ℝ) * (M : ℝ) ^ 2 ≤ ∑ i, ∑ j, lpReal d N f (c.gram i j) := by
    rw [hswap, Finset.sum_range_succ']
    have htail : 0 ≤ ∑ k ∈ range N,
        (f (k + 1) : ℝ) * ∑ i, ∑ j, gegenbauerReal d (k + 1) (c.gram i j) := by
      refine Finset.sum_nonneg fun k hk => ?_
      rw [mem_range] at hk
      exact mul_nonneg (by exact_mod_cast hf (k + 1) (mem_range.mpr (by omega)))
        (hS (k + 1) (mem_range.mpr (by omega)) M c)
    rw [hk0]
    linarith
  -- Descend to `ℚ` and finish.
  have hQ : f 0 * (M : ℚ) ^ 2 ≤ (M : ℚ) * ∑ k ∈ range (N + 1), f k := by
    have h := le_trans hlower hupper
    exact_mod_cast h
  have hsum : 0 ≤ ∑ k ∈ range (N + 1), f k := Finset.sum_nonneg hf
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa using div_nonneg hsum hf0.le
  · have hM' : (0 : ℚ) < M := by exact_mod_cast hM
    rw [le_div_iff₀ hf0]
    nlinarith [hQ, hM']

/-! ## A certificate that satisfies the hypotheses

A conditional theorem whose hypotheses are contradictory proves nothing. This is
the witness: on the circle, `f t = 4t³ + 6t² - 2 = 2(t+1)²(2t-1)` has Gegenbauer
coefficients `(1, 3, 3, 1)`, all nonnegative with `f_0 = 1 > 0`, and is
nonpositive on `[-1, 1/2]`. The bound it gives is `8 / 1 = 8`.
The kissing number of the circle is 6, so the certificate is valid and not tight
— which is what a *bound* means.
-/

/-- The witness certificate, in dimension 2 and degree 3. -/
def certCircle : ℕ → ℚ
  | 0 => 1
  | 1 => 3
  | 2 => 3
  | 3 => 1
  | _ => 0

theorem gegenbauerPoly_two_two : gegenbauerPoly 2 2 = 2 * X ^ 2 - 1 := by
  rw [gegenbauerPoly_dim_two]
  norm_num [Chebyshev.T_two]

theorem gegenbauerPoly_two_three : gegenbauerPoly 2 3 = 4 * X ^ 3 - 3 * X := by
  rw [gegenbauerPoly_dim_two]
  have h := Chebyshev.T_add_two (R := ℚ) 1
  norm_num [Chebyshev.T_two, Chebyshev.T_one] at h
  norm_num [h]
  ring

theorem lpPoly_certCircle : lpPoly 2 3 certCircle = 4 * X ^ 3 + 6 * X ^ 2 - 2 := by
  simp [lpPoly, Finset.sum_range_succ, certCircle, gegenbauerPoly_two_two,
    gegenbauerPoly_two_three, map_ofNat]
  ring

theorem lpReal_certCircle (t : ℝ) : lpReal 2 3 certCircle t = 4 * t ^ 3 + 6 * t ^ 2 - 2 := by
  rw [lpReal, lpPoly_certCircle]
  simp [map_ofNat]

/-- The interval certificate for the witness: `-f = (1/2 - X) * (2 (X + 1)) ^ 2`.
One square, one multiplier, and no `nlinarith`. -/
noncomputable def certCircleSOS :
    Certificate.IntervalCert (-1) (1 / 2) (lpPoly 2 3 certCircle) where
  sqB := [2 * (X + 1)]
  identity := by
    rw [lpPoly_certCircle]
    apply Polynomial.funext
    intro x
    simp [Certificate.sosPoly]
    ring

theorem lpReal_certCircle_nonpos {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1 / 2) :
    lpReal 2 3 certCircle t ≤ 0 :=
  Certificate.aeval_nonpos_of_intervalCert certCircleSOS
    (by push_cast; linarith) (by push_cast; linarith)

/-- Outside the interval the certificate says nothing, and must not: `f 1 = 8 > 0`
is precisely what makes the bound `f 1 / f 0` finite and useful. -/
theorem lpReal_certCircle_one_pos : 0 < lpReal 2 3 certCircle 1 := by
  rw [lpReal_certCircle]; norm_num

/-- The multiplier is load-bearing. `-f` takes a negative value at `2`, so it is
not a bare sum of squares: any certificate for `f` must use `1/2 - X`, and is
therefore tied to the interval it was written for. -/
theorem neg_lpPoly_certCircle_not_sos (ps : List ℚ[X]) :
    -(lpPoly 2 3 certCircle) ≠ Certificate.sosPoly ps := by
  refine Certificate.not_sosPoly_of_aeval_neg (t := 2) ?_ ps
  rw [lpPoly_certCircle]
  simp [map_ofNat]
  norm_num

theorem sum_certCircle : ∑ k ∈ range 4, certCircle k = 8 := by
  simp [Finset.sum_range_succ, certCircle]
  norm_num

/-- **First bound on the sphere side.** Conditional on Schoenberg positivity in
dimension 2 at degrees 2 and 3 — degrees 0 and 1 are already proved — a family of
unit vectors of the plane with pairwise inner products at most `1/2` has at most
8 members. The true maximum is 6. -/
theorem card_le_eight_of_schoenberg (h2 : SchoenbergPos 2 2) (h3 : SchoenbergPos 2 3)
    (c : UnitPoints 2 M) (hc : ∀ i j, i ≠ j → c.gram i j ≤ 1 / 2) : (M : ℚ) ≤ 8 := by
  have h := card_le_of_sphereCert (d := 2) (N := 3) (f := certCircle) (by norm_num)
    (fun k hk => by
      rw [mem_range] at hk
      interval_cases k
      · exact schoenbergPos_zero 2
      · exact schoenbergPos_one 2
      · exact h2
      · exact h3)
    (fun k hk => by rw [mem_range] at hk; interval_cases k <;> norm_num [certCircle])
    (by norm_num [certCircle])
    (fun _ h1 h2 => lpReal_certCircle_nonpos h1 h2) c hc
  rwa [sum_certCircle, show certCircle 0 = 1 from rfl, div_one] at h

/-! ## Negative control

The interval hypothesis is what does the work. Without it the theorem would be
false, and the following shows it is not automatic: the constant certificate
`f = G_0` is nonnegative in the basis and has `f 0 = 1 > 0`, yet it fails
`f t ≤ 0` — and it would have "proved" that every such family has at most one
member.
-/

theorem not_nonpos_lpReal_const :
    ¬ ∀ t : ℝ, -1 ≤ t → t ≤ 1 / 2 → lpReal 2 0 (fun _ => 1) t ≤ 0 := by
  intro h
  have h0 := h 0 (by norm_num) (by norm_num)
  rw [lpReal_eq_sum] at h0
  norm_num at h0

end Delsarte.Sphere
