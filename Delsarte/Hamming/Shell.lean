/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.CharQ
import Delsarte.Krawtchouk.Subsets
import Mathlib.InformationTheory.Hamming

/-!
# The shell identity: characters of weight `k` sum to a Krawtchouk value

For a `q`-ary alphabet, summing `∏_j χ_{u j}(z j)` over all index vectors `u` of
Hamming weight `k` produces `K_k(w)`, where `w` is the weight of `z`. This is the
combinatorial heart of Delsarte positivity for `q > 2`.

## What the binary case got for free

`Delsarte/Hamming/Feasible.lean` indexes characters by `u : Finset (Fin n)`, so
"weight `k`" is literally "cardinality `k`" and `Finset.powersetCard` is the
shell. Here the index is `u : Fin n → ZMod q`, and a subset of size `k` carries
`(q-1)^k` distinct index vectors. The sum must therefore be decomposed by
support *and* by the nonzero values on that support — the one step with no
binary counterpart.

Both are done at once, by grading the generating function. `X` marks the
nonzero coordinates of `u`:

* `prod_add_one_eq_sum_weight` expands `∏_j (1 + g_j X)` over index vectors,
  with `X^{wt u}`;
* `prod_add_one_eq_sum_powerset` expands the same product over subsets, with
  `X^{|t|}`.

Reading the coefficient of `X^k` off both sides equates a sum over the weight-`k`
shell with a sum over subsets of size `k`, and no explicit bijection is ever
constructed.

## Where `q` enters

Only through `sum_chiQ_ne_zero`: a coordinate of `z` that vanishes contributes
`q - 1`, one that does not contributes `-1`. Those are exactly the two
coefficients of `krawtchoukPoly n q i`, which is
`(C (q-1) X + 1)^(n-i) * (C (-1) X + 1)^i`. So the polynomial identity is the
binary one with `q` left free, and `sum_powersetCard_prod_ite` states it over `ℚ`
— the cast to `ℂ` happens once, at the end.

Nothing here needs `q` prime, and nothing needs the code to be linear: `z` is an
arbitrary vector.
-/

namespace Delsarte.Hamming

open Finset Polynomial Delsarte

variable {n : ℕ}

/-- The support of an index vector: the coordinates where it does not vanish. -/
def suppQ {q : ℕ} (u : Fin n → ZMod q) : Finset (Fin n) :=
  univ.filter fun j => u j ≠ 0

/-- The Hamming weight of an index vector. -/
def wtQ {q : ℕ} (u : Fin n → ZMod q) : ℕ := (suppQ u).card

@[simp]
theorem mem_suppQ {q : ℕ} (u : Fin n → ZMod q) (j : Fin n) : j ∈ suppQ u ↔ u j ≠ 0 := by
  simp [suppQ]

variable {q : ℕ} [NeZero q]

/-- The character of the index vector `u` evaluated at `z`: the product of the
coordinatewise characters. -/
noncomputable def chiVec (u z : Fin n → ZMod q) : ℂ := ∏ j, chiQ (u j) (z j)

/-- Expansion over index vectors, graded by weight. `X` marks the nonzero
coordinates of `u`, so the coefficient of `X^k` collects exactly the weight-`k`
shell. This is the step the binary case never needed. -/
theorem prod_add_one_eq_sum_weight (z : Fin n → ZMod q) :
    (∏ j : Fin n, (C (∑ c ∈ univ.filter (fun c : ZMod q => c ≠ 0), chiQ c (z j)) * X + 1))
      = ∑ u : Fin n → ZMod q, C (chiVec u z) * X ^ wtQ u := by
  have hfac : ∀ j : Fin n,
      C (∑ c ∈ univ.filter (fun c : ZMod q => c ≠ 0), chiQ c (z j)) * X + 1
        = ∑ c : ZMod q, C (chiQ c (z j)) * (if c = 0 then 1 else X) := by
    intro j
    have h : ∑ c : ZMod q, C (chiQ c (z j)) * (if c = 0 then 1 else X)
        = (∑ c ∈ univ.filter (fun c : ZMod q => c = 0), C (chiQ c (z j)) * 1)
          + ∑ c ∈ univ.filter (fun c : ZMod q => ¬ c = 0), C (chiQ c (z j)) * X := by
      simp only [mul_ite]
      rw [Finset.sum_ite]
    rw [h, Finset.filter_eq' univ (0 : ZMod q)]
    simp only [Finset.mem_univ, if_true, Finset.sum_singleton, mul_one, chiQ_zero_left, map_one,
      ne_eq]
    rw [← Finset.sum_mul, ← map_sum]
    ring
  have hterm : ∀ u : Fin n → ZMod q,
      (∏ j : Fin n, (C (chiQ (u j) (z j)) * (if u j = 0 then 1 else X)))
        = C (chiVec u z) * X ^ wtQ u := by
    intro u
    rw [Finset.prod_mul_distrib, ← map_prod, chiVec, Finset.prod_ite, Finset.prod_const_one,
      one_mul, Finset.prod_const, wtQ, suppQ]
  rw [Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun u _ => hterm u

/-- **The shell identity.** Summing the character of every index vector of weight
`k` gives the Krawtchouk value at the weight of `z`. -/
theorem sum_chiVec_shell (z : Fin n → ZMod q) (k : ℕ) :
    ∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k), chiVec u z
      = ((krawtchouk n q k (suppQ z).card : ℚ) : ℂ) := by
  have hg : ∀ j : Fin n, (∑ c ∈ univ.filter (fun c : ZMod q => c ≠ 0), chiQ c (z j))
      = if j ∈ suppQ z then (-1 : ℂ) else (q : ℂ) - 1 := by
    intro j
    rw [sum_chiQ_ne_zero]
    by_cases h : z j = 0
    · rw [if_pos h, if_neg (by simp [h] : j ∉ suppQ z)]
    · rw [if_neg h, if_pos (by simp [h] : j ∈ suppQ z)]
  have hleft : Polynomial.coeff (∑ u : Fin n → ZMod q, C (chiVec u z) * X ^ wtQ u) k
      = ∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k), chiVec u z := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : wtQ u = k
    · simp [h]
    · simp [h, Ne.symm h]
  have hright : ∑ t ∈ Finset.powersetCard k (univ : Finset (Fin n)),
      ∏ j ∈ t, (∑ c ∈ univ.filter (fun c : ZMod q => c ≠ 0), chiQ c (z j))
      = ((krawtchouk n q k (suppQ z).card : ℚ) : ℂ) := by
    rw [← sum_powersetCard_prod_ite (suppQ z) q k]
    push_cast [apply_ite ((Rat.cast : ℚ → ℂ))]
    exact Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun j _ => hg j
  rw [← hleft, ← prod_add_one_eq_sum_weight z, prod_add_one_eq_sum_powerset,
    coeff_sum_powerset, hright]

/-! ### Control

At `n = 1`, `q = 3`, `k = 1` and `z = 0` every character value is `1`, so the
shell sum literally counts its own index set. The count is `(q-1)^k` per support,
here `2`, and `K_1(0) = (q-1) n = 2` agrees. This is the factor the binary case
cannot see: at `q = 2` it is `1` for every `k`, so a proof that forgot it would
still be correct in binary and wrong everywhere else.
-/

theorem card_shell_zmod_three :
    (univ.filter (fun u : Fin 1 → ZMod 3 => wtQ u = 1)).card = 2 := by
  decide

theorem krawtchouk_one_three_one_zero : krawtchouk 1 3 1 0 = 2 := by
  norm_num [krawtchouk, Finset.sum_range_succ]

theorem sum_chiVec_shell_control :
    ∑ u ∈ univ.filter (fun u : Fin 1 → ZMod 3 => wtQ u = 1), chiVec u 0 = 2 := by
  have h := sum_chiVec_shell (0 : Fin 1 → ZMod 3) 1
  rw [show (suppQ (0 : Fin 1 → ZMod 3)).card = 0 from by simp [suppQ],
    krawtchouk_one_three_one_zero] at h
  rw [h]
  norm_num

/-! ### What `#26` will consume -/

/-- Characters are multiplicative against the conjugate: the product sees only the
difference of the two words. The `q`-ary analogue of `chi_mul`. -/
theorem chiVec_mul_conj (u x y : Fin n → ZMod q) :
    chiVec u x * (starRingEnd ℂ) (chiVec u y) = chiVec u (x - y) := by
  rw [chiVec, chiVec, chiVec, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [conj_chiQ, ← chiQ_add_right, Pi.sub_apply, sub_eq_add_neg]

omit [NeZero q] in
/-- The support of a difference is the set of coordinates where the two words
disagree. -/
theorem suppQ_sub (x y : Fin n → ZMod q) :
    suppQ (x - y) = univ.filter fun j => x j ≠ y j := by
  ext j
  simp [sub_eq_zero]

omit [NeZero q] in
/-- ...so its cardinality is the Hamming distance, which is the index at which the
Krawtchouk polynomial gets evaluated. -/
theorem card_suppQ_sub (x y : Fin n → ZMod q) :
    (suppQ (x - y)).card = hammingDist x y := by
  rw [suppQ_sub, hammingDist]

end Delsarte.Hamming
