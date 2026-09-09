/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Krawtchouk polynomials

The `q`-ary Krawtchouk polynomial of degree `k` and length `n`, evaluated at an
integer point `i`:

`K_k(i) = ∑_{j=0}^{k} (-1)^j (q-1)^{k-j} C(i, j) C(n-i, k-j)`

Values live in `ℚ`, not `ℝ`: the whole certificate path is exact rational
arithmetic. Only integer arguments `i` are ever needed by the Delsarte linear
program for the Hamming scheme, so `krawtchouk` is a `ℕ → ℚ` function rather
than a `Polynomial ℚ` in the evaluation variable.

The generating variable, on the other hand, *is* carried by a genuine
`Polynomial ℚ`: `krawtchoukPoly n q i = (1 + (q-1) X)^(n-i) (1 - X)^i` has
`K_k(i)` as its `k`-th coefficient. That identity is the workhorse behind the
three-term recurrence and orthogonality.
-/

namespace Delsarte

open Finset Polynomial

variable {n q k i : ℕ}

/-- The `q`-ary Krawtchouk polynomial of degree `k` for length `n`, evaluated at `i`. -/
def krawtchouk (n q k i : ℕ) : ℚ :=
  ∑ j ∈ range (k + 1),
    (-1) ^ j * ((q : ℚ) - 1) ^ (k - j) * (i.choose j) * ((n - i).choose (k - j))

/-- The generating polynomial of the `krawtchouk n q · i`, in the variable `X`. -/
noncomputable def krawtchoukPoly (n q i : ℕ) : ℚ[X] :=
  (C ((q : ℚ) - 1) * X + 1) ^ (n - i) * (C (-1 : ℚ) * X + 1) ^ i

/-- Binomial expansion of `(cX + 1)^m`, coefficient by coefficient. -/
theorem coeff_C_mul_X_add_one_pow (c : ℚ) (m a : ℕ) :
    ((C c * X + 1) ^ m).coeff a = (m.choose a : ℚ) * c ^ a := by
  rw [(Commute.all (C c * X) (1 : ℚ[X])).add_pow, Polynomial.finsetSum_coeff]
  simp only [one_pow, mul_one, mul_pow, ← C_pow, ← C_eq_natCast, coeff_mul_C, coeff_C_mul,
    coeff_X_pow, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rcases Nat.lt_or_ge a (m + 1) with ha | ha
  · rw [Finset.sum_ite_eq (range (m + 1)) a]
    simp [ha, mul_comm]
  · rw [Finset.sum_eq_zero, Nat.choose_eq_zero_of_lt ha]
    · simp
    · intro b hb
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega)]

/-- `krawtchouk n q k i` is the `k`-th coefficient of `krawtchoukPoly n q i`. -/
theorem coeff_krawtchoukPoly (n q i k : ℕ) :
    (krawtchoukPoly n q i).coeff k = krawtchouk n q k i := by
  rw [krawtchoukPoly, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  conv_rhs => rw [krawtchouk, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [coeff_C_mul_X_add_one_pow, coeff_C_mul_X_add_one_pow, Nat.add_sub_cancel,
    Nat.sub_sub_self hj]
  ring

theorem krawtchouk_zero_left (n q i : ℕ) : krawtchouk n q 0 i = 1 := by
  simp [krawtchouk]

theorem krawtchouk_zero_right (n q k : ℕ) :
    krawtchouk n q k 0 = (n.choose k : ℚ) * ((q : ℚ) - 1) ^ k := by
  rw [krawtchouk, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr k.succ_pos)]
  · simp [mul_comm]
  · intro j _ hj
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]

theorem krawtchouk_one (n q i : ℕ) :
    krawtchouk n q 1 i = ((q : ℚ) - 1) * ((n - i : ℕ) : ℚ) - i := by
  simp [krawtchouk, Finset.sum_range_succ]
  ring

theorem natDegree_C_mul_X_add_one_le (c : ℚ) : (C c * X + 1 : ℚ[X]).natDegree ≤ 1 := by
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans natDegree_mul_le (by simp)
  · simp

theorem natDegree_krawtchoukPoly_le (n q i : ℕ) (hi : i ≤ n) :
    (krawtchoukPoly n q i).natDegree ≤ n := by
  refine le_trans (natDegree_mul_le) ?_
  refine le_trans (add_le_add (natDegree_pow_le_of_le _ (natDegree_C_mul_X_add_one_le _))
    (natDegree_pow_le_of_le _ (natDegree_C_mul_X_add_one_le _))) ?_
  omega

/-- Generating function of the Krawtchouk values, evaluated at a rational point. -/
theorem sum_krawtchouk_mul_pow (n q i : ℕ) (hi : i ≤ n) (w : ℚ) :
    ∑ l ∈ range (n + 1), krawtchouk n q l i * w ^ l
      = (1 + ((q : ℚ) - 1) * w) ^ (n - i) * (1 - w) ^ i := by
  have h := Polynomial.eval_eq_sum_range' (p := krawtchoukPoly n q i)
    (Nat.lt_succ_of_le (natDegree_krawtchoukPoly_le n q i hi)) w
  simp only [coeff_krawtchoukPoly] at h
  rw [← h, krawtchoukPoly]
  simp only [eval_mul, eval_pow, eval_add, eval_one, eval_C, eval_X]
  ring

/-- Beyond degree `n` the Krawtchouk values vanish on `{0, …, n}`. -/
theorem krawtchouk_eq_zero_of_lt (n q k i : ℕ) (hi : i ≤ n) (hk : n < k) :
    krawtchouk n q k i = 0 := by
  rw [← coeff_krawtchoukPoly]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_krawtchoukPoly_le n q i hi) hk)

/-- The collapse identity behind orthogonality: summing the generating polynomials
against the binomial measure, weighted by a second evaluation point `w`, produces a
single binomial power. -/
theorem sum_C_mul_krawtchoukPoly (n q : ℕ) (w : ℚ) :
    ∑ i ∈ range (n + 1),
        C ((n.choose i : ℚ) * (((q : ℚ) - 1) * (1 - w)) ^ i
            * (1 + ((q : ℚ) - 1) * w) ^ (n - i)) * krawtchoukPoly n q i
      = C ((q : ℚ) ^ n) * (C (((q : ℚ) - 1) * w) * X + 1) ^ n := by
  have hAB : (C (((q : ℚ) - 1) * (1 - w)) * (C (-1 : ℚ) * X + 1)
        + (C ((q : ℚ) - 1) * X + 1) * C (1 + ((q : ℚ) - 1) * w))
      = C ((q : ℚ)) * (C (((q : ℚ) - 1) * w) * X + 1) := by
    simp only [map_mul, map_add, map_sub, map_one, map_neg]
    ring
  have hRHS : C ((q : ℚ) ^ n) * (C (((q : ℚ) - 1) * w) * X + 1) ^ n
      = (C (((q : ℚ) - 1) * (1 - w)) * (C (-1 : ℚ) * X + 1)
          + (C ((q : ℚ) - 1) * X + 1) * C (1 + ((q : ℚ) - 1) * w)) ^ n := by
    rw [hAB, mul_pow, ← C_pow]
  rw [hRHS, (Commute.all _ _).add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [krawtchoukPoly, map_mul, map_pow, map_sub, map_add, map_one, map_neg,
    C_eq_natCast, mul_pow]
  ring

/-- Coefficient form of the collapse identity. -/
theorem sum_binom_mul_krawtchouk_mul_pow (n q k : ℕ) (w : ℚ) :
    ∑ i ∈ range (n + 1),
        (n.choose i : ℚ) * (((q : ℚ) - 1) * (1 - w)) ^ i * (1 + ((q : ℚ) - 1) * w) ^ (n - i)
          * krawtchouk n q k i
      = (q : ℚ) ^ n * ((n.choose k : ℚ) * (((q : ℚ) - 1) * w) ^ k) := by
  have h := congrArg (fun p : ℚ[X] => p.coeff k) (sum_C_mul_krawtchoukPoly n q w)
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_krawtchoukPoly,
    coeff_C_mul_X_add_one_pow] at h
  exact h

/-- Orthogonality of the Krawtchouk polynomials with respect to the binomial measure
`i ↦ C(n,i) (q-1)^i`. -/
theorem sum_krawtchouk_mul_krawtchouk (n q k l : ℕ) (hl : l ≤ n) :
    ∑ i ∈ range (n + 1),
        (n.choose i : ℚ) * ((q : ℚ) - 1) ^ i * krawtchouk n q k i * krawtchouk n q l i
      = if k = l then (q : ℚ) ^ n * (n.choose k) * ((q : ℚ) - 1) ^ k else 0 := by
  set S : ℕ → ℚ := fun m => ∑ i ∈ range (n + 1),
    (n.choose i : ℚ) * ((q : ℚ) - 1) ^ i * krawtchouk n q k i * krawtchouk n q m i with hSdef
  have hpoly : (∑ m ∈ range (n + 1), C (S m) * X ^ m : ℚ[X])
      = C ((q : ℚ) ^ n * (n.choose k) * ((q : ℚ) - 1) ^ k) * X ^ k := by
    apply Polynomial.funext
    intro w
    simp only [eval_finsetSum, eval_mul, eval_pow, eval_C, eval_X]
    have hswap : ∑ m ∈ range (n + 1), S m * w ^ m
        = ∑ i ∈ range (n + 1),
            (n.choose i : ℚ) * (((q : ℚ) - 1) * (1 - w)) ^ i
              * (1 + ((q : ℚ) - 1) * w) ^ (n - i) * krawtchouk n q k i := by
      simp only [hSdef, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      have := sum_krawtchouk_mul_pow n q i hi w
      calc ∑ m ∈ range (n + 1),
              (n.choose i : ℚ) * ((q : ℚ) - 1) ^ i * krawtchouk n q k i
                * krawtchouk n q m i * w ^ m
          = ((n.choose i : ℚ) * ((q : ℚ) - 1) ^ i * krawtchouk n q k i)
              * ∑ m ∈ range (n + 1), krawtchouk n q m i * w ^ m := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
        _ = (n.choose i : ℚ) * (((q : ℚ) - 1) * (1 - w)) ^ i
              * (1 + ((q : ℚ) - 1) * w) ^ (n - i) * krawtchouk n q k i := by
            rw [this, mul_pow]; ring
    rw [hswap, sum_binom_mul_krawtchouk_mul_pow n q k w, mul_pow]
    ring
  have hcoeff := congrArg (fun p : ℚ[X] => p.coeff l) hpoly
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero] at hcoeff
  rw [Finset.sum_ite_eq (range (n + 1)) l,
    if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))] at hcoeff
  have hgoal : S l = if k = l then (q : ℚ) ^ n * (n.choose k) * ((q : ℚ) - 1) ^ k else 0 := by
    rw [hcoeff]
    by_cases hkl : k = l
    · simp [hkl]
    · simp [hkl, Ne.symm hkl]
  exact hgoal

end Delsarte
