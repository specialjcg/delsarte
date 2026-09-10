/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Characters of `ZMod q`, and the sum over the alphabet minus zero

The analytic brick under Delsarte positivity for a `q`-ary alphabet. Nothing
combinatorial happens here: one character, four algebraic facts about it, and
one sum.

## Why this file exists at all

`Delsarte/Hamming/Feasible.lean` proves the binary case with no analysis
whatsoever. Over `{0,1}` the characters take values in `{±1} ⊆ ℚ`, so Delsarte
positivity is literally a sum of squares of rationals and the argument never
leaves `ℚ`. That collapses as soon as `q > 2`: the characters are `q`-th roots
of unity. `chiQ_one_ne_one_zmod_three` and `chiQ_one_ne_neg_one_zmod_three`
below pin this down — at `q = 3` a character value is neither `1` nor `-1`, so
no relabelling recovers a rational-valued `chi` and the `ℚ`-only route is
genuinely gone, not merely inconvenient.

## The representation of the alphabet

`Word n q := Fin n → Fin q` throughout the repository, and characters need a
group structure on the alphabet. No transport is required: `ZMod (m + 1)` *is*
`Fin (m + 1)` by definition, which `zmod_succ_eq_fin` records as a `rfl` so
that a future mathlib change breaks the build here rather than silently
somewhere downstream.

The `q`-ary chain therefore works under `[NeZero q]` internally, obtained from
`0 < q` at the public boundary via `NeZero.of_pos`. No statement below needs
`Fin n → Fin q` rewritten, and none needs `q` prime.

## The sum

`sum_chiQ` is character orthogonality on `ZMod q`. It is proved by the
translation trick — multiplying the sum by one non-trivial value permutes the
terms — rather than through the `AddChar` orthogonality API, so that the file
depends only on `chiQ_add_left` and a reindexing `Equiv`.

`sum_chiQ_ne_zero` is the form the shell identity consumes: dropping `c = 0`
turns `q` into `q - 1` and `0` into `-1`, which are exactly the two
coefficients of the per-coordinate factor `((q-1) X + 1)` and `(-X + 1)`.
-/

namespace Delsarte.Hamming

open Finset Complex

/-- The alphabet needs a group structure, and it already has one: `ZMod (m + 1)`
is `Fin (m + 1)` on the nose, so `Word n (m + 1)` is a tuple over `ZMod (m + 1)`
without any transport. Stated as a `rfl` on purpose — it is the one load-bearing
definitional coincidence of the `q`-ary chain, and it should fail loudly. -/
theorem zmod_succ_eq_fin (m : ℕ) : ZMod (m + 1) = Fin (m + 1) := rfl

/-- The public boundary of the `q`-ary chain: a caller states `0 < q`, the
internals run on `[NeZero q]`. Recorded as a lemma so the conversion is checked
rather than asserted in prose. -/
theorem neZero_of_pos {q : ℕ} (hq : 0 < q) : NeZero q := NeZero.of_pos hq

variable {q : ℕ} [NeZero q]

/-- The character of `ZMod q` indexed by `u`, evaluated at `t`: the standard
additive character at `u * t`, so `exp (2 π i u t / q)`. Additive in each
argument separately, which is what makes the double sum over a code factor. -/
noncomputable def chiQ (u t : ZMod q) : ℂ := ZMod.stdAddChar (u * t)

@[simp]
theorem chiQ_zero_left (t : ZMod q) : chiQ (0 : ZMod q) t = 1 := by
  simp [chiQ]

@[simp]
theorem chiQ_zero_right (u : ZMod q) : chiQ u (0 : ZMod q) = 1 := by
  simp [chiQ]

theorem chiQ_add_left (u u' t : ZMod q) : chiQ (u + u') t = chiQ u t * chiQ u' t := by
  simp only [chiQ, add_mul]
  exact ZMod.stdAddChar.map_add_eq_mul _ _

theorem chiQ_add_right (u t t' : ZMod q) : chiQ u (t + t') = chiQ u t * chiQ u t' := by
  simp only [chiQ, mul_add]
  exact ZMod.stdAddChar.map_add_eq_mul _ _

/-- A character value is `1` exactly when its argument vanishes. This is
injectivity of the standard character, and it is the only nontrivial input to
`sum_chiQ`. -/
theorem chiQ_eq_one_iff (u t : ZMod q) : chiQ u t = 1 ↔ u * t = 0 := by
  rw [chiQ, show (1 : ℂ) = ZMod.stdAddChar (0 : ZMod q) from
    (ZMod.stdAddChar.map_zero_eq_one).symm]
  exact ZMod.injective_stdAddChar.eq_iff

@[simp]
theorem norm_chiQ (u t : ZMod q) : ‖chiQ u t‖ = 1 := by
  simp [chiQ, ZMod.stdAddChar_apply, Circle.norm_coe]

theorem conj_chiQ (u t : ZMod q) : (starRingEnd ℂ) (chiQ u t) = chiQ u (-t) := by
  have hmul : chiQ u t * chiQ u (-t) = 1 := by
    rw [← chiQ_add_right, add_neg_cancel, chiQ_zero_right]
  have h : chiQ u (-t) = (chiQ u t)⁻¹ := (inv_eq_of_mul_eq_one_right hmul).symm
  rw [h, Complex.inv_eq_conj (norm_chiQ u t)]

/-- **Orthogonality on `ZMod q`.** The sum of a character over the whole
alphabet is `q` at the trivial argument and `0` otherwise. -/
theorem sum_chiQ (t : ZMod q) :
    ∑ c : ZMod q, chiQ c t = if t = 0 then (q : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht, ZMod.card]
  · rw [if_neg ht]
    -- one non-trivial value permutes the terms, so the sum is its own multiple
    have hb : chiQ 1 t ≠ 1 := by
      rw [ne_eq, chiQ_eq_one_iff, one_mul]
      exact ht
    have hperm : ∑ c : ZMod q, chiQ (1 + c) t = ∑ c : ZMod q, chiQ c t :=
      Fintype.sum_equiv (Equiv.addLeft (1 : ZMod q)) _ _ fun _ => rfl
    have hmul : chiQ 1 t * ∑ c : ZMod q, chiQ c t = ∑ c : ZMod q, chiQ c t := by
      rw [Finset.mul_sum]
      calc ∑ c : ZMod q, chiQ 1 t * chiQ c t
          = ∑ c : ZMod q, chiQ (1 + c) t :=
            Finset.sum_congr rfl fun c _ => (chiQ_add_left 1 c t).symm
        _ = ∑ c : ZMod q, chiQ c t := hperm
    have := sub_eq_zero_of_eq hmul
    rw [← sub_one_mul] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hb
    · exact h

/-- **The per-coordinate factor.** The same sum with `c = 0` removed: `q - 1`
when the argument vanishes, `-1` otherwise. These are the two coefficients that
the generating function of the shell identity multiplies together. -/
theorem sum_chiQ_ne_zero (t : ZMod q) :
    ∑ c ∈ univ.filter (fun c : ZMod q => c ≠ 0), chiQ c t
      = if t = 0 then (q : ℂ) - 1 else -1 := by
  have h : ∑ c ∈ univ.filter (fun c : ZMod q => c ≠ 0), chiQ c t
      = (∑ c : ZMod q, chiQ c t) - chiQ 0 t := by
    rw [Finset.filter_ne' univ (0 : ZMod q), Finset.sum_erase_eq_sub (mem_univ _)]
  rw [h, sum_chiQ, chiQ_zero_left]
  by_cases ht : t = 0 <;> simp [ht]

/-! ### Controls

Three evaluations, each refuting a way the file could be quietly wrong.
-/

/-- The character is not the constant `1`: at `q = 3` the value at `(1,1)` is not
`1`. Without this, `sum_chiQ` could hold for a degenerate `chiQ`. -/
theorem chiQ_one_ne_one_zmod_three : chiQ (1 : ZMod 3) 1 ≠ 1 := by
  rw [ne_eq, chiQ_eq_one_iff]
  decide

/-- **The reason this file exists.** At `q = 3` the value at `(1,1)` is not `-1`
either, so character values leave `{±1}` and the rational-valued `chi` of
`Delsarte/Hamming/Feasible.lean` cannot be recovered by any relabelling. The
`ℚ`-only proof of the binary case is genuinely unavailable, not merely awkward. -/
theorem chiQ_one_ne_neg_one_zmod_three : chiQ (1 : ZMod 3) 1 ≠ -1 := by
  intro h
  have hsq : chiQ (1 : ZMod 3) (1 + 1) = 1 := by
    rw [chiQ_add_right, h]
    ring
  rw [chiQ_eq_one_iff] at hsq
  revert hsq
  decide

/-- Positivity cannot be argued term by term: at `q = 4` the value at `(2,2)` is
`1` although `2 ≠ 0`, so terms of the shell sum genuinely cancel. -/
theorem chiQ_two_two_zmod_four : chiQ (2 : ZMod 4) 2 = 1 := by
  rw [chiQ_eq_one_iff]
  decide

end Delsarte.Hamming
