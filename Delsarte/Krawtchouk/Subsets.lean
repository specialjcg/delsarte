/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Krawtchouk.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset

/-!
# Krawtchouk values as sums over subsets of a fixed size

`K_k(|S|)` is the sum, over the subsets `t` of size `k`, of a product of two
coefficients: `-1` on `S`, and `q - 1` off it. Reading it that way is what turns
Delsarte positivity into a squared norm, in both the binary and the `q`-ary
route.

Everything here is rational and elementary: the point of a separate file is that
`Delsarte/Hamming/Feasible.lean` — the binary case, whose whole argument stays
inside `ℚ` — and `Delsarte/Hamming/Shell.lean` — the `q`-ary case, which needs
`ℂ` — must share this combinatorics without the binary chain acquiring a
dependency on complex analysis.

The proof is a generating function. `∏_j (C c_j X + 1)` expands over subsets with
`X^{|t|}`, and it *is* `krawtchoukPoly n q i` once the coefficients are read off,
so the grading of `ℚ[X]` does the counting that a direct `powersetCard`
computation would have to do by hand.
-/

namespace Delsarte

open Finset Polynomial

variable {n : ℕ}

/-- Expansion of `∏_j (1 + c_j X)` over subsets: the coefficient of `X^{|t|}` is
the product of the `c_j` over `t`. Pure `Finset.prod_add`, valid over any
commutative ring. -/
theorem prod_add_one_eq_sum_powerset {R : Type*} [CommRing R] (g : Fin n → R) :
    (∏ j : Fin n, (C (g j) * X + 1))
      = ∑ t ∈ (univ : Finset (Fin n)).powerset, C (∏ j ∈ t, g j) * X ^ t.card := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]

/-- Reading the coefficient of `X^k` off that expansion keeps exactly the subsets
of size `k`. -/
theorem coeff_sum_powerset {R : Type*} [CommRing R] (g : Fin n → R) (k : ℕ) :
    Polynomial.coeff (∑ t ∈ (univ : Finset (Fin n)).powerset, C (∏ j ∈ t, g j) * X ^ t.card) k
      = ∑ t ∈ Finset.powersetCard k (univ : Finset (Fin n)), ∏ j ∈ t, g j := by
  rw [Polynomial.finsetSum_coeff, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : t.card = k
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Krawtchouk as a subset sum.** The two coefficients are `-1` inside `S` and
`q - 1` outside, which are exactly the two factors of `krawtchoukPoly n q i`. -/
theorem sum_powersetCard_prod_ite (S : Finset (Fin n)) (q k : ℕ) :
    ∑ t ∈ Finset.powersetCard k (univ : Finset (Fin n)),
        ∏ j ∈ t, (if j ∈ S then (-1 : ℚ) else (q : ℚ) - 1)
      = krawtchouk n q k S.card := by
  have hS : (univ.filter fun j : Fin n => j ∈ S) = S := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hSc : (univ.filter fun j : Fin n => ¬ j ∈ S) = Sᶜ := by
    ext j; simp
  have hpoly : (∏ j : Fin n, (C (if j ∈ S then (-1 : ℚ) else (q : ℚ) - 1) * X + 1))
      = krawtchoukPoly n q S.card := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun j : Fin n => j ∈ S), hS, hSc]
    have h1 : ∏ j ∈ S, (C (if j ∈ S then (-1 : ℚ) else (q : ℚ) - 1) * X + 1)
        = ∏ _j ∈ S, (C (-1 : ℚ) * X + 1) :=
      Finset.prod_congr rfl fun j hj => by rw [if_pos hj]
    have h2 : ∏ j ∈ Sᶜ, (C (if j ∈ S then (-1 : ℚ) else (q : ℚ) - 1) * X + 1)
        = ∏ _j ∈ Sᶜ, (C ((q : ℚ) - 1) * X + 1) :=
      Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.mem_compl.mp hj)]
    rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl, Fintype.card_fin,
      krawtchoukPoly]
    ring
  rw [← coeff_sum_powerset, ← prod_add_one_eq_sum_powerset, hpoly, coeff_krawtchoukPoly]

/-- At `q = 2` the coefficient off `S` is `1`, so the product collapses to a sign.
This is what makes the binary case rational-valued. -/
theorem prod_ite_two_eq_neg_one_pow (S t : Finset (Fin n)) :
    (∏ j ∈ t, (if j ∈ S then (-1 : ℚ) else ((2 : ℕ) : ℚ) - 1)) = (-1 : ℚ) ^ (t ∩ S).card := by
  have h : ∀ j : Fin n, (if j ∈ S then (-1 : ℚ) else ((2 : ℕ) : ℚ) - 1)
      = if j ∈ S then (-1 : ℚ) else 1 := by
    intro j
    by_cases hj : j ∈ S <;> norm_num [hj]
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter]

/-- The binary specialisation, kept as a named statement because
`Delsarte/Hamming/Feasible.lean` consumes exactly this shape. -/
theorem sum_powersetCard_neg_one_pow (S : Finset (Fin n)) (k : ℕ) :
    ∑ t ∈ Finset.powersetCard k (univ : Finset (Fin n)), (-1 : ℚ) ^ (t ∩ S).card
      = krawtchouk n 2 k S.card := by
  rw [← sum_powersetCard_prod_ite S 2 k]
  exact Finset.sum_congr rfl fun t _ => (prod_ite_two_eq_neg_one_pow S t).symm

/-! ### Control

The identity at `n = 2`, `q = 3`, `k = 1`, `S = {0}`. By hand the left side is
`(-1) + 2 = 1`. An off-by-one in the index convention of `krawtchouk` — the one
error a generating-function proof hides best — would not survive this.
-/

theorem krawtchouk_two_three_one_one : krawtchouk 2 3 1 1 = 1 := by
  norm_num [krawtchouk, Finset.sum_range_succ]

theorem sum_powersetCard_prod_ite_control :
    ∑ t ∈ Finset.powersetCard 1 (univ : Finset (Fin 2)),
        ∏ j ∈ t, (if j ∈ ({0} : Finset (Fin 2)) then (-1 : ℚ) else (3 : ℚ) - 1) = 1 := by
  have h := sum_powersetCard_prod_ite ({0} : Finset (Fin 2)) 3 1
  rw [Finset.card_singleton, krawtchouk_two_three_one_one] at h
  exact h

end Delsarte
