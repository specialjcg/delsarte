/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.LP
import Delsarte.Krawtchouk.Subsets
import Delsarte.Hamming.DistDist
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

Binary only, and kept that way on purpose. `Delsarte/Hamming/FeasibleQ.lean`
proves the same statement for every `q`, but the characters there are `q`-th roots
of unity and the argument goes through `ℂ`. This file's project-import closure
contains no complex analysis, so the binary bounds — Golay included — still rest
on a chain that never leaves `ℚ`.
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

/-- The Krawtchouk value `K_k(|S|)` is the character sum over all `u` of size
`k`. The generating-function computation lives in
`Delsarte/Krawtchouk/Subsets.lean`, shared with the `q`-ary route so that the two
cannot drift apart; that file is rational throughout, so this proof still never
leaves `ℚ`. -/
theorem sum_neg_one_pow_inter (S : Finset (Fin n)) (k : ℕ) :
    ∑ u ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), (-1 : ℚ) ^ (u ∩ S).card
      = krawtchouk n 2 k S.card :=
  sum_powersetCard_neg_one_pow S k

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

/-- **Delsarte positivity.** Every Krawtchouk degree gives a valid constraint on
the distance distribution of a binary code. -/
theorem sum_distDist_mul_krawtchouk_nonneg (C : Code n 2) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n 2 k i := by
  rw [sum_distDist_mul_krawtchouk C k]
  exact div_nonneg (sum_sum_krawtchouk_nonneg C k) (by positivity)

/-- Delsarte positivity in the shape `primalFeasible_codeVec` expects. The
bookkeeping is `q`-generic and lives in `Delsarte/Hamming/DistDist.lean`; only
the positivity input is binary. -/
theorem delsarte_positivity (hd : 1 ≤ d) {C : Code n 2} (hC : C.Nonempty)
    (hmin : MinDistAtLeast d C) (k : ℕ) :
    0 ≤ krawtchouk n 2 k 0 + ∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n 2 k i :=
  delsarte_positivity_of_nonneg hd hC hmin k (sum_distDist_mul_krawtchouk_nonneg C k)

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
