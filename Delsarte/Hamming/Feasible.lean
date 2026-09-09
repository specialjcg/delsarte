/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.LP
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset

/-!
# Primal feasibility of the distance distribution (binary case)

The theorem the Hamming half of the project rests on: for every binary code
`C`, every Krawtchouk degree `k` satisfies

`∑_{i} a_i K_k(i) ≥ 0`,

where `a` is the distance distribution of `C`. Combined with
`Delsarte.Hamming.primalFeasible_codeVec` this discharges the hypothesis that
`Delsarte/Hamming/LP.lean` carries throughout, so `A_le_of_dualFeasible_binary`
below bounds `A n 2 d` outright.

## Why this file needs no Fourier analysis

The usual proof reads the sum as a squared norm on the Fourier side of
`(ℤ/2)^n`. Over the binary alphabet the characters take values in `{±1} ⊆ ℚ`,
so nothing complex-valued is ever needed: the identity is a sum of squares of
*rationals*, and the whole argument stays inside `ℚ`.

Characters are indexed by subsets `u ⊆ Fin n`; `chi u x = (-1)^|u ∩ supp x|`.
Two facts drive everything:

* `chi_mul` — `chi u x * chi u y` depends only on where `x` and `y` differ.
* `sum_neg_one_pow_inter` — summing that over all `u` of size `k` produces the
  Krawtchouk value `K_k` at the Hamming distance. This is proved by expanding
  `∏_j (±X + 1)` with `Finset.prod_add` and comparing coefficients with
  `krawtchoukPoly`; the grading of `ℚ[X]` does the counting that would
  otherwise be a `powersetCard` computation.

No linearity of the code is assumed anywhere: `C` is an arbitrary `Finset` of
words.

## Scope

Binary only. For `q > 2` the characters are `q`-th roots of unity and the
argument needs `ℂ` or a cyclotomic ring; that is tracked separately.
-/

namespace Delsarte.Hamming

open Finset Delsarte.LP Delsarte

variable {n d : ℕ}

/-- The character of `(ℤ/2)^n` indexed by `u`, valued in `{±1} ⊆ ℚ`. -/
def chi (u : Finset (Fin n)) (x : Word n 2) : ℚ :=
  (-1) ^ (u.filter fun j => x j = 1).card

/-- Parity bookkeeping: over a binary alphabet, `|u ∩ supp x| + |u ∩ supp y|`
and `|u ∩ {j | x j ≠ y j}|` differ by twice `|u ∩ supp x ∩ supp y|`. -/
theorem card_filter_add_card_filter (u : Finset (Fin n)) (x y : Word n 2) :
    (u.filter fun j => x j = 1).card + (u.filter fun j => y j = 1).card
      = (u.filter fun j => x j ≠ y j).card
        + 2 * (u.filter fun j => x j = 1 ∧ y j = 1).card := by
  have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases h2 (x j) with hx | hx <;> rcases h2 (y j) with hy | hy <;> simp [hx, hy]

/-- Characters are multiplicative: `chi u x * chi u y` sees only the set of
coordinates where `x` and `y` disagree. -/
theorem chi_mul (u : Finset (Fin n)) (x y : Word n 2) :
    chi u x * chi u y = (-1 : ℚ) ^ (u.filter fun j => x j ≠ y j).card := by
  rw [chi, chi, ← pow_add, card_filter_add_card_filter, pow_add, pow_mul]
  norm_num

open Polynomial in
/-- The Krawtchouk value `K_k(|S|)` is the character sum over all `u` of size
`k`. Proved by expanding `∏_j (±X + 1)` over the powerset and reading off the
coefficient of `X^k`. -/
theorem sum_neg_one_pow_inter (S : Finset (Fin n)) (k : ℕ) :
    ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), (-1 : ℚ) ^ (u ∩ S).card
      = krawtchouk n 2 k S.card := by
  have hprod : ∀ t : Finset (Fin n),
      (∏ j ∈ t, (if j ∈ S then (-1 : ℚ) else 1)) = (-1 : ℚ) ^ (t ∩ S).card := by
    intro t
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      Finset.filter_mem_eq_inter]
  have hS : (Finset.univ.filter fun j : Fin n => j ∈ S) = S := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hSc : (Finset.univ.filter fun j : Fin n => ¬ j ∈ S) = Sᶜ := by
    ext j; simp
  have hpoly : (∏ j : Fin n, (C (if j ∈ S then (-1 : ℚ) else 1) * X + 1))
      = krawtchoukPoly n 2 S.card := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j : Fin n => j ∈ S), hS, hSc]
    have h1 : ∏ j ∈ S, (C (if j ∈ S then (-1 : ℚ) else 1) * X + 1)
        = ∏ _j ∈ S, (C (-1 : ℚ) * X + 1) :=
      Finset.prod_congr rfl fun j hj => by rw [if_pos hj]
    have h2 : ∏ j ∈ Sᶜ, (C (if j ∈ S then (-1 : ℚ) else 1) * X + 1)
        = ∏ _j ∈ Sᶜ, (C (1 : ℚ) * X + 1) :=
      Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.mem_compl.mp hj)]
    have hq : ((2 : ℕ) : ℚ) - 1 = 1 := by norm_num
    rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl, Fintype.card_fin,
      krawtchoukPoly, hq]
    ring
  have hexp : (∏ j : Fin n, (C (if j ∈ S then (-1 : ℚ) else 1) * X + 1))
      = ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
          C ((-1 : ℚ) ^ (t ∩ S).card) * X ^ t.card := by
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
      ← map_prod, hprod t]
  have hcoeff : Polynomial.coeff (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
      C ((-1 : ℚ) ^ (t ∩ S).card) * X ^ t.card) k = krawtchouk n 2 k S.card := by
    rw [hexp.symm.trans hpoly, coeff_krawtchoukPoly]
  rw [← hcoeff, Polynomial.finsetSum_coeff, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : t.card = k
  · simp [h]
  · simp [h, Ne.symm h]

/-- The character sum at a pair of words evaluates the Krawtchouk polynomial at
their Hamming distance. -/
theorem sum_chi_mul_chi (x y : Word n 2) (k : ℕ) :
    ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), chi u x * chi u y
      = krawtchouk n 2 k (hammingDist x y) := by
  have hS : ∀ u : Finset (Fin n),
      u ∩ (Finset.univ.filter fun j => x j ≠ y j) = u.filter fun j => x j ≠ y j := by
    intro u; ext j; simp
  have h1 : ∀ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
      chi u x * chi u y
        = (-1 : ℚ) ^ (u ∩ (Finset.univ.filter fun j => x j ≠ y j)).card := by
    intro u _
    rw [chi_mul, hS u]
  rw [Finset.sum_congr rfl h1, sum_neg_one_pow_inter]
  rfl

/-- **Delsarte positivity, unnormalised.** The double sum of `K_k` over all
ordered pairs of codewords is a sum of squares of rationals. -/
theorem sum_sum_krawtchouk_nonneg (C : Code n 2) (k : ℕ) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, krawtchouk n 2 k (hammingDist x y) := by
  have key : ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
      (∑ x ∈ C, chi u x) ^ 2
      = ∑ x ∈ C, ∑ y ∈ C, krawtchouk n 2 k (hammingDist x y) := by
    calc ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), (∑ x ∈ C, chi u x) ^ 2
        = ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            ∑ x ∈ C, ∑ y ∈ C, chi u x * chi u y := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ x ∈ C, ∑ y ∈ C,
            ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), chi u x * chi u y := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_comm]
      _ = ∑ x ∈ C, ∑ y ∈ C, krawtchouk n 2 k (hammingDist x y) :=
          Finset.sum_congr rfl fun x _ =>
            Finset.sum_congr rfl fun y _ => sum_chi_mul_chi x y k
  rw [← key]
  exact Finset.sum_nonneg fun u _ => sq_nonneg _

/-- The distance distribution reassembles the double sum, divided by `|C|`. -/
theorem sum_distDist_mul_krawtchouk (C : Code n 2) (k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n 2 k i
      = (∑ x ∈ C, ∑ y ∈ C, krawtchouk n 2 k (hammingDist x y)) / C.card := by
  have hmem : ∀ p ∈ C ×ˢ C, hammingDist p.1 p.2 ∈ Finset.range (n + 1) := by
    intro p _
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    simpa using hammingDist_le_card_fintype (x := p.1) (y := p.2)
  have hprod : ∑ x ∈ C, ∑ y ∈ C, krawtchouk n 2 k (hammingDist x y)
      = ∑ p ∈ C ×ˢ C, krawtchouk n 2 k (hammingDist p.1 p.2) := by
    rw [Finset.sum_product]
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmem, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconst : ∑ p ∈ (C ×ˢ C).filter (fun p => hammingDist p.1 p.2 = i),
      krawtchouk n 2 k (hammingDist p.1 p.2)
      = ∑ _p ∈ (C ×ˢ C).filter (fun p => hammingDist p.1 p.2 = i), krawtchouk n 2 k i :=
    Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, distDist]
  ring

/-- **Delsarte positivity.** Every Krawtchouk degree gives a valid constraint on
the distance distribution of a binary code. -/
theorem sum_distDist_mul_krawtchouk_nonneg (C : Code n 2) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n 2 k i := by
  rw [sum_distDist_mul_krawtchouk C k]
  exact div_nonneg (sum_sum_krawtchouk_nonneg C k) (by positivity)

/-- Delsarte positivity in the shape `primalFeasible_codeVec` expects: the term
`i = 0` contributes `K_k(0)`, and the terms `0 < i < d` vanish. -/
theorem delsarte_positivity (hd : 1 ≤ d) {C : Code n 2} (hC : C.Nonempty)
    (hmin : MinDistAtLeast d C) (k : ℕ) :
    0 ≤ krawtchouk n 2 k 0 + ∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n 2 k i := by
  have hnn := sum_distDist_mul_krawtchouk_nonneg C k
  have hsub : insert 0 (Finset.Icc d n) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_Icc] at hi
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    rcases hi with rfl | ⟨_, h2⟩
    · exact Nat.zero_le _
    · exact h2
  have hzero : ∀ i ∈ Finset.range (n + 1), i ∉ insert 0 (Finset.Icc d n) →
      distDist C i * krawtchouk n 2 k i = 0 := by
    intro i hi hni
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and_or, not_le] at hni
    obtain ⟨hi0, hid⟩ := hni
    rw [distDist_eq_zero_of_lt hmin (Nat.pos_of_ne_zero hi0)
      (by rcases hid with h | h <;> omega), zero_mul]
  have hsplit : ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n 2 k i
      = distDist C 0 * krawtchouk n 2 k 0
        + ∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n 2 k i := by
    rw [← Finset.sum_subset hsub hzero,
      Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
  rw [hsplit, distDist_zero hC, one_mul] at hnn
  exact hnn

/-- The distance distribution of a binary code is a feasible point of the
Delsarte primal. This is the hypothesis `Delsarte/Hamming/LP.lean` assumes
throughout. -/
theorem primalFeasible_distDist (hd : 1 ≤ d) {C : Code n 2} (hC : C.Nonempty)
    (hmin : MinDistAtLeast d C) :
    PrimalFeasible (delsarteMatrix n 2 d) (delsarteRHS n 2) (codeVec C d) :=
  primalFeasible_codeVec fun k _ => delsarte_positivity hd hC hmin k

/-- **The Delsarte bound for binary codes**, with no remaining hypothesis: any
dual-feasible `y` bounds `A n 2 d`. -/
theorem A_le_of_dualFeasible_binary (hd : 1 ≤ d) {y : ConIdx n → ℚ}
    (hy : DualFeasible (delsarteMatrix n 2 d) (delsarteObj n d) y) :
    (A n 2 d : ℚ) ≤ 1 + delsarteRHS n 2 ⬝ᵥ y :=
  A_le_of_dualFeasible hd (by norm_num)
    (fun _ hC hmin => primalFeasible_distDist hd hC hmin) hy

end Delsarte.Hamming
