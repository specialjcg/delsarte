/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Lattice.Leech

/-!
# Separation of the 196 560 minimal vectors, first family

`mem_kissingSet_twentyFour_of_min` is the only conditional statement of this
repository. Its hypothesis is *not* the Leech minimum: it is the finite claim
that the `196 560` explicit vectors of `Leech.lean` are pairwise `32`-separated.
Every vector has squared norm `32` (`norm_leechVec`), and

```
dotp (u - v) (u - v) = 64 - 2 * dotp u v
```

so the hypothesis is exactly `dotp u v ≤ 16` for `u ≠ v`.

## Measured before it was proved

A Python mirror of `leechVec` scanned all `1.93 · 10^10` distinct pairs. The
maximum is `16`, and it is attained on **each** of the six family pairs — none
has any slack. The values taken are `{-32, -16, -8, 0, 8, 16}` throughout: `24`
never occurs, which is the whole difficulty, since a naive triangle inequality
reaches `24` on two of the six cases.

This file settles the three cases involving the first family
`(±4, ±4, 0^22)`. They need no property of the Golay code: the support has two
coordinates, so the product collapses to two terms and the bound follows from
the size of the entries alone. The three remaining cases are issues #38, #39
and #40.
-/

namespace Delsarte.Lattice

open Delsarte Delsarte.Certificate Finset

-- The three tightness witnesses at the end of the file are closed by the
-- kernel on concrete `vec24` lists: twenty-four coordinates unfolded from a
-- `List.range`, which overruns the default recursion depth.
set_option maxRecDepth 10000

/-! ## A vector supported on two coordinates -/

/-- A sum over `range 24` against a function vanishing off `{a, b}`. -/
theorem sum_pair_mul {a b : ℕ} (ha : a < 24) (hb : b < 24) (hab : a ≠ b) (x y : ℤ)
    (g : ℕ → ℤ) :
    ∑ j ∈ range 24, (if j = a then x else if j = b then y else 0) * g j
      = x * g a + y * g b := by
  have hcong : ∀ j ∈ range 24, (if j = a then x else if j = b then y else 0) * g j
      = (if j = a then x * g a else 0) + (if j = b then y * g b else 0) := by
    intro j _
    by_cases hja : j = a
    · subst hja; simp [hab]
    · by_cases hjb : j = b
      · subst hjb; simp [hja]
      · simp [hja, hjb]
  rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range 24) a fun _ => x * g a,
    Finset.sum_ite_eq' (range 24) b fun _ => y * g b]
  simp [Finset.mem_range, ha, hb]

/-- The first family paired with anything given coordinatewise. -/
theorem dotp_leechF1_vec24 {q : ℕ} (hq : q < 276) (st : ℕ) (g : ℕ → ℤ) :
    dotp (leechF1 q st) (vec24 g)
      = signFour st * g (pairOf q).1 + signFour (st / 2) * g (pairOf q).2 := by
  rw [leechF1, dotp_vec24]
  exact sum_pair_mul (lt_trans (pairOf_lt hq) (pairOf_lt_24 hq)) (pairOf_lt_24 hq)
    (Nat.ne_of_lt (pairOf_lt hq)) _ _ g

/-- The two entries of a first-family vector are `±4`. -/
theorem signFour_cases (b : ℕ) : signFour b = 4 ∨ signFour b = -4 := by
  unfold signFour; split <;> simp

/-! ## Coordinate functions of the other two families -/

/-- The coordinate function of the second family. -/
def f2 (o pat j : ℕ) : ℤ :=
  if octadBit o j then (if patSign pat (octadRank o j) then -2 else 2) else 0

theorem leechF2_eq (o pat : ℕ) : leechF2 o pat = vec24 (f2 o pat) := rfl

theorem f2_bounds (o pat j : ℕ) : -2 ≤ f2 o pat j ∧ f2 o pat j ≤ 2 := by
  unfold f2; split <;> [split; skip] <;> constructor <;> norm_num

/-- The coordinate function of the third family. -/
def f3 (c k j : ℕ) : ℤ :=
  if j = k then -3 * golaySign c k else golaySign c j

theorem leechF3_eq (c k : ℕ) : leechF3 c k = vec24 (f3 c k) := rfl

theorem golaySign_cases (c j : ℕ) : golaySign c j = 1 ∨ golaySign c j = -1 := by
  unfold golaySign; split <;> simp

theorem f3_bounds (c k j : ℕ) : -3 ≤ f3 c k j ∧ f3 c k j ≤ 3 := by
  unfold f3
  split
  · rcases golaySign_cases c k with h | h <;> rw [h] <;> constructor <;> norm_num
  · rcases golaySign_cases c j with h | h <;> rw [h] <;> constructor <;> norm_num

/-- Off the distinguished position the third family carries `±1`. -/
theorem f3_off {c k j : ℕ} (h : j ≠ k) : f3 c k j = 1 ∨ f3 c k j = -1 := by
  rw [f3, if_neg h]; exact golaySign_cases c j

/-! ## The three cases involving the first family -/

/-- **F1 against F2.** Two coordinates carrying `±4` meet entries of size at
most `2`, so the product is at most `4 · 2 + 4 · 2 = 16`. -/
theorem dotp_F1_F2 {q : ℕ} (hq : q < 276) (st o pat : ℕ) :
    dotp (leechF1 q st) (leechF2 o pat) ≤ 16 := by
  rw [leechF2_eq, dotp_leechF1_vec24 hq]
  obtain ⟨hlo, hhi⟩ := f2_bounds o pat (pairOf q).1
  obtain ⟨hlo', hhi'⟩ := f2_bounds o pat (pairOf q).2
  rcases signFour_cases st with h1 | h1 <;> rcases signFour_cases (st / 2) with h2 | h2 <;>
    rw [h1, h2] <;> omega

/-- **F1 against F3.** The third family has a single coordinate of size `3`;
the support of the first has two distinct coordinates, so at most one of them
meets it, and the product is at most `4 · 3 + 4 · 1 = 16`. -/
theorem dotp_F1_F3 {q : ℕ} (hq : q < 276) (st c k : ℕ) :
    dotp (leechF1 q st) (leechF3 c k) ≤ 16 := by
  rw [leechF3_eq, dotp_leechF1_vec24 hq]
  have hab : (pairOf q).1 ≠ (pairOf q).2 := Nat.ne_of_lt (pairOf_lt hq)
  obtain ⟨hlo, hhi⟩ := f3_bounds c k (pairOf q).1
  obtain ⟨hlo', hhi'⟩ := f3_bounds c k (pairOf q).2
  have hone : f3 c k (pairOf q).1 = 1 ∨ f3 c k (pairOf q).1 = -1
      ∨ f3 c k (pairOf q).2 = 1 ∨ f3 c k (pairOf q).2 = -1 := by
    by_cases h : (pairOf q).1 = k
    · have h2 : (pairOf q).2 ≠ k := fun hk => hab (h.trans hk.symm)
      rcases f3_off (c := c) h2 with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
    · rcases f3_off (c := c) h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  rcases signFour_cases st with h1 | h1 <;> rcases signFour_cases (st / 2) with h2 | h2 <;>
    rw [h1, h2] <;> rcases hone with h | h | h | h <;> omega

/-! ## The first family against itself -/

/-- The coordinate function of the first family. -/
def f1 (q st j : ℕ) : ℤ :=
  if j = (pairOf q).1 then signFour st
  else if j = (pairOf q).2 then signFour (st / 2) else 0

theorem leechF1_eq (q st : ℕ) : leechF1 q st = vec24 (f1 q st) := rfl

theorem f1_bounds (q st j : ℕ) : -4 ≤ f1 q st j ∧ f1 q st j ≤ 4 := by
  unfold f1
  split
  · rcases signFour_cases st with h | h <;> rw [h] <;> constructor <;> norm_num
  · split
    · rcases signFour_cases (st / 2) with h | h <;> rw [h] <;> constructor <;> norm_num
    · constructor <;> norm_num

theorem f1_zero {q st j : ℕ} (h1 : j ≠ (pairOf q).1) (h2 : j ≠ (pairOf q).2) :
    f1 q st j = 0 := by rw [f1, if_neg h1, if_neg h2]

theorem f1_fst (q st : ℕ) : f1 q st (pairOf q).1 = signFour st := by rw [f1, if_pos rfl]

theorem f1_snd {q : ℕ} (hq : q < 276) (st : ℕ) :
    f1 q st (pairOf q).2 = signFour (st / 2) := by
  rw [f1, if_neg (Nat.ne_of_lt (pairOf_lt hq)).symm, if_pos rfl]

/-- The two signs cannot both agree unless the sign index is the same. -/
theorem signFour_pair {st st' : ℕ} (hst : st < 4) (hst' : st' < 4) (h : st ≠ st') :
    signFour st * signFour st' + signFour (st / 2) * signFour (st' / 2) ≤ 16 := by
  interval_cases st <;> interval_cases st' <;> simp_all [signFour]

/-- **F1 against F1.** Two supports of size two either coincide — and then the
signs must differ, so the product drops to `0` or `-32` — or meet in at most
one coordinate, which caps the product at `16`. -/
theorem dotp_F1_F1 {q q' st st' : ℕ} (hq : q < 276) (hq' : q' < 276)
    (hst : st < 4) (hst' : st' < 4) (hne : ¬(q = q' ∧ st = st')) :
    dotp (leechF1 q st) (leechF1 q' st') ≤ 16 := by
  rw [leechF1_eq q' st', dotp_leechF1_vec24 hq]
  have hlt : (pairOf q).1 < (pairOf q).2 := pairOf_lt hq
  have hlt' : (pairOf q').1 < (pairOf q').2 := pairOf_lt hq'
  obtain ⟨hlo, hhi⟩ := f1_bounds q' st' (pairOf q).1
  obtain ⟨hlo', hhi'⟩ := f1_bounds q' st' (pairOf q).2
  by_cases hA : (pairOf q).1 = (pairOf q').1
  · by_cases hB : (pairOf q).2 = (pairOf q').2
    · -- the same pair: the sign indices must differ
      have hqq : q = q' := pairOf_injOn hq hq' (Prod.ext hA hB)
      have hss : st ≠ st' := fun h => hne ⟨hqq, h⟩
      rw [hA, hB, f1_fst, f1_snd hq']
      exact signFour_pair hst hst' hss
    · -- only the first coordinates meet
      have h2 : (pairOf q).2 ≠ (pairOf q').1 := by omega
      rw [f1_zero h2 hB]
      rcases signFour_cases st with h1 | h1 <;> rcases signFour_cases (st / 2) with hh | hh <;>
        rw [h1, hh] <;> omega
  · by_cases hC : (pairOf q).1 = (pairOf q').2
    · -- the first coordinate of the left pair is the second of the right one
      have h2 : (pairOf q).2 ≠ (pairOf q').2 := by omega
      have h1 : (pairOf q).2 ≠ (pairOf q').1 := by omega
      rw [f1_zero h1 h2]
      rcases signFour_cases st with hs | hs <;> rcases signFour_cases (st / 2) with hh | hh <;>
        rw [hs, hh] <;> omega
    · rw [f1_zero hA hC]
      rcases signFour_cases st with hs | hs <;> rcases signFour_cases (st / 2) with hh | hh <;>
        rw [hs, hh] <;> omega

/-! ## The same three cases, with the arguments swapped -/

theorem dotp_F2_F1 {q : ℕ} (hq : q < 276) (st o pat : ℕ) :
    dotp (leechF2 o pat) (leechF1 q st) ≤ 16 := by
  rw [dotp_comm]; exact dotp_F1_F2 hq st o pat

theorem dotp_F3_F1 {q : ℕ} (hq : q < 276) (st c k : ℕ) :
    dotp (leechF3 c k) (leechF1 q st) ≤ 16 := by
  rw [dotp_comm]; exact dotp_F1_F3 hq st c k

/-! ## Negative controls: the constant `16` cannot be lowered

The measurement reports the maximum as attained on every family pair. Here are
the three witnesses for the pairs settled above, checked by the kernel. Any
future refactor that "improves" one of these bounds to `15` is wrong, and these
three theorems are what will say so.
-/

theorem dotp_F1_F1_tight : dotp (leechF1 0 0) (leechF1 1 0) = 16 := by decide +kernel

theorem dotp_F1_F2_tight : dotp (leechF1 0 0) (leechF2 2 0) = 16 := by decide +kernel

theorem dotp_F1_F3_tight : dotp (leechF1 0 0) (leechF3 1 0) = 16 := by decide +kernel

end Delsarte.Lattice
