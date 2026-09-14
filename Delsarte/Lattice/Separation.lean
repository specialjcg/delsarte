/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Lattice.Leech
import Mathlib.Data.Nat.Bitwise

/-!
# Separation of the 196 560 minimal vectors

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

## The six cases, and what each one costs

| pair    | what closes it                                          |
| ------- | ------------------------------------------------------- |
| F1 - F1 | the size of the entries; the support has two coordinates |
| F1 - F2 | the same                                                 |
| F1 - F3 | the same                                                 |
| F2 - F2 | `minWt_golay24`: two distinct octads meet in `≤ 4` places |
| F3 - F3 | `minWt_golay24`: `24 - 2 w` with `w = 0` or `w ≥ 8`       |
| F2 - F3 | `wtDvd_golay24`: an octad meets a codeword evenly        |

Only the last needs divisibility. Take it away and the crude count reaches
`2 · 7 + 2 · 3 = 20`; the parity of the clash count rules out exactly the odd
multiples of four that would sit above `16`.

The file ends with the six tightness witnesses and with
`mem_kissingSet_twentyFour`, the conditional theorem discharged.
-/

namespace Delsarte.Lattice

open Delsarte Delsarte.Certificate Finset

-- The tightness witnesses at the end of the file are closed by the kernel on
-- concrete `vec24` lists: twenty-four coordinates unfolded from a
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

/-! ## The third family against itself

Two vectors of the third family agree everywhere except at their distinguished
positions, so their product scalar splits into a *global* part — the inner
product of two Golay sign vectors — and a correction supported on at most two
coordinates.

The global part is `24 - 2 w`, where `w` is the weight of the bitwise
difference of the two messages. That is where `minWt_golay24` enters: `w = 0`
or `w ≥ 8`, so the global part is `24` or at most `8`, and the correction is at
most `8` either way. No divisibility is needed here.
-/

/-- A sum over `range 24` of a function that vanishes off `{a, b}`. -/
theorem sum_pair_supp {a b : ℕ} (ha : a < 24) (hb : b < 24) (hab : a ≠ b) (h : ℕ → ℤ)
    (hz : ∀ j, j ≠ a → j ≠ b → h j = 0) :
    ∑ j ∈ range 24, h j = h a + h b := by
  have hcong : ∀ j ∈ range 24,
      h j = (if j = a then h a else 0) + (if j = b then h b else 0) := by
    intro j _
    by_cases hja : j = a
    · subst hja; simp [hab]
    · by_cases hjb : j = b
      · subst hjb; simp [hja]
      · simp [hja, hjb, hz j hja hjb]
  rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range 24) a (fun _ => h a),
    Finset.sum_ite_eq' (range 24) b (fun _ => h b)]
  simp [Finset.mem_range, ha, hb]

/-- Signs multiply the way messages add. This is `cbit_xor` in `ℤ`. -/
theorem golaySign_mul (c c' j : ℕ) :
    golaySign c j * golaySign c' j = golaySign (c ^^^ c') j := by
  unfold golaySign
  rw [cbit_xor]
  cases cbit golay24Row 12 c j <;> cases cbit golay24Row 12 c' j <;> norm_num

/-- The sign vector of a codeword sums to `24 - 2 ·` its weight. -/
theorem sum_golaySign (e : ℕ) :
    ∑ j ∈ range 24, golaySign e j = 24 - 2 * (cwt golay24Row 12 24 e : ℤ) := by
  have h : ∀ j ∈ range 24, golaySign e j
      = 1 - 2 * (if cbit golay24Row 12 e j then (1 : ℤ) else 0) := by
    intro j _; unfold golaySign; split <;> norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum, cwt,
    countP_range_eq_sum]
  push_cast
  simp

/-- Off its distinguished position the third family is exactly a Golay sign. -/
theorem f3_eq_of_ne {c k j : ℕ} (h : j ≠ k) : f3 c k j = golaySign c j := by
  rw [f3, if_neg h]

theorem f3_at (c k : ℕ) : f3 c k k = -3 * golaySign c k := by rw [f3, if_pos rfl]

/-- **F3 against F3.** -/
theorem dotp_F3_F3 {c c' k k' : ℕ} (hc : c < 4096) (hc' : c' < 4096)
    (hk : k < 24) (hk' : k' < 24) (hne : ¬(c = c' ∧ k = k')) :
    dotp (leechF3 c k) (leechF3 c' k') ≤ 16 := by
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  rw [leechF3_eq, leechF3_eq, dotp_vec24]
  have hsplit : ∑ j ∈ range 24, f3 c k j * f3 c' k' j
      = (∑ j ∈ range 24, golaySign c j * golaySign c' j)
        + ∑ j ∈ range 24, (f3 c k j * f3 c' k' j - golaySign c j * golaySign c' j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hzero : ∀ j, j ≠ k → j ≠ k' →
      f3 c k j * f3 c' k' j - golaySign c j * golaySign c' j = 0 := by
    intro j h1 h2; rw [f3_eq_of_ne h1, f3_eq_of_ne h2, sub_self]
  have hPk : golaySign c k * golaySign c' k = 1 ∨ golaySign c k * golaySign c' k = -1 := by
    rcases golaySign_cases c k with h | h <;> rcases golaySign_cases c' k with h' | h' <;>
      rw [h, h'] <;> norm_num
  have hPk' : golaySign c k' * golaySign c' k' = 1 ∨ golaySign c k' * golaySign c' k' = -1 := by
    rcases golaySign_cases c k' with h | h <;> rcases golaySign_cases c' k' with h' | h' <;>
      rw [h, h'] <;> norm_num
  rw [hsplit]
  by_cases hkk : k = k'
  · subst hkk
    have hcorr : ∑ j ∈ range 24, (f3 c k j * f3 c' k j - golaySign c j * golaySign c' j)
        = 8 * (golaySign c k * golaySign c' k) := by
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)
        (fun j _ hj => hzero j hj hj), f3_at, f3_at]
      ring
    have hcc : c ≠ c' := fun h => hne ⟨h, rfl⟩
    have hglob : ∑ j ∈ range 24, golaySign c j * golaySign c' j ≤ 8 := by
      rw [Finset.sum_congr rfl fun j _ => golaySign_mul c c' j, sum_golaySign]
      have hx : c ^^^ c' < 2 ^ 12 := xor_lt_two_pow (by rw [h12]; exact hc)
        (by rw [h12]; exact hc')
      have := minWt_golay24 (c ^^^ c') hx (xor_ne_zero hcc)
      omega
    rw [hcorr]; rcases hPk with h | h <;> rw [h] <;> omega
  · have hcorr : ∑ j ∈ range 24, (f3 c k j * f3 c' k' j - golaySign c j * golaySign c' j)
        = -4 * (golaySign c k * golaySign c' k) + -4 * (golaySign c k' * golaySign c' k') := by
      rw [sum_pair_supp hk hk' hkk _ hzero, f3_at, f3_eq_of_ne (Ne.symm hkk),
        f3_eq_of_ne hkk, f3_at]
      ring
    rw [hcorr]
    by_cases hcc : c = c'
    · subst hcc
      have hglob : ∑ j ∈ range 24, golaySign c j * golaySign c j = 24 := by
        rw [Finset.sum_congr rfl fun j _ => golaySign_sq c j]
        simp
      rw [hglob, golaySign_sq, golaySign_sq]; norm_num
    · have hglob : ∑ j ∈ range 24, golaySign c j * golaySign c' j ≤ 8 := by
        rw [Finset.sum_congr rfl fun j _ => golaySign_mul c c' j, sum_golaySign]
        have hx : c ^^^ c' < 2 ^ 12 := xor_lt_two_pow (by rw [h12]; exact hc)
          (by rw [h12]; exact hc')
        have := minWt_golay24 (c ^^^ c') hx (xor_ne_zero hcc)
        omega
      rcases hPk with h | h <;> rcases hPk' with h' | h' <;> rw [h, h'] <;> omega

/-! ## The second family against itself

Two vectors of the second family are supported on octads, so the product
scalar only sees the overlap. Two *distinct* octads overlap in at most four
coordinates — that is `minWt_golay24` read through inclusion-exclusion — and
four coordinates carrying `±4` cannot pass `16`.

On one and the same octad the overlap is all eight coordinates and the crude
count gives `32`. What saves the bound is `patSign_even`: every sign pattern
carries an even number of minus signs, so two distinct patterns disagree in an
even, nonzero number of places, hence in at least two.
-/

/-- A constant weight distributed over a Boolean predicate, over any range. -/
theorem sum_ite_countP_range (p : ℕ → Bool) (a : ℤ) (n : ℕ) :
    ∑ j ∈ range n, (if p j then a else 0) = a * ((List.range n).countP p : ℤ) := by
  rw [countP_range_eq_sum, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p j <;> simp [h]

/-- A guarded sum over `range n` is the sum over the positions kept. -/
theorem sum_ite_eq_filter (p : ℕ → Bool) (f : ℕ → ℤ) : ∀ n : ℕ,
    ∑ j ∈ range n, (if p j then f j else 0) = (((List.range n).filter p).map f).sum
  | 0 => by simp
  | (n + 1) => by
      rw [Finset.sum_range_succ, sum_ite_eq_filter p f n, List.range_succ,
        List.filter_append, List.map_append, List.sum_append]
      cases h : p n <;> simp [h]

theorem sum_map_range (f : ℕ → ℤ) : ∀ n : ℕ,
    ((List.range n).map f).sum = ∑ j ∈ range n, f j
  | 0 => by simp
  | (n + 1) => by
      rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
        Finset.sum_range_succ]
      simp

/-- **The ranks of the kept positions are exactly `0, …, count - 1`.** Counting
how many predecessors satisfy the predicate numbers the survivors in order. -/
theorem map_rank_filter (p : ℕ → Bool) : ∀ n : ℕ,
    ((List.range n).filter p).map (fun j => (List.range j).countP p)
      = List.range ((List.range n).countP p)
  | 0 => by simp
  | (n + 1) => by
      rw [List.range_succ, List.filter_append, List.map_append, map_rank_filter p n,
        List.countP_append]
      cases h : p n <;> simp [h, List.range_succ]

/-- **Reindexing an octad by rank.** A sum guarded by the octad is a sum over
the eight ranks. -/
theorem sum_octad_rank {o : ℕ} (ho : o < 759) (G : ℕ → ℤ) :
    ∑ j ∈ range 24, (if octadBit o j then G (octadRank o j) else 0)
      = ∑ r ∈ range 8, G r := by
  rw [sum_ite_eq_filter (octadBit o) (fun j => G (octadRank o j)) 24,
    show (fun j => G (octadRank o j))
      = G ∘ (fun j => (List.range j).countP (octadBit o)) from rfl,
    ← List.map_map, map_rank_filter (octadBit o) 24, countP_octadBit ho, sum_map_range]

/-- The same reindexing, for a count. -/
theorem countP_octad_rank {o : ℕ} (ho : o < 759) (P : ℕ → Bool) :
    (List.range 24).countP (fun j => P (octadRank o j) && octadBit o j)
      = (List.range 8).countP P := by
  rw [← List.countP_filter, show (fun j => P (octadRank o j))
      = P ∘ (fun j => (List.range j).countP (octadBit o)) from rfl,
    ← List.countP_map, map_rank_filter (octadBit o) 24, countP_octadBit ho]

/-- Inclusion-exclusion for counts: the symmetric difference is even when both
sides are. -/
theorem countP_xor (p q : ℕ → Bool) : ∀ l : List ℕ,
    l.countP p + l.countP q
      = l.countP (fun j => Bool.xor (p j) (q j)) + 2 * l.countP (fun j => p j && q j)
  | [] => by simp
  | (a :: t) => by
      have ih := countP_xor p q t
      simp only [List.countP_cons]
      cases p a <;> cases q a <;> simp <;> omega

/-- **Two distinct octads meet in at most four coordinates.** -/
theorem countP_octad_inter {o o' : ℕ} (ho : o < 759) (ho' : o' < 759) (hoo : o ≠ o') :
    (List.range 24).countP (fun j => octadBit o j && octadBit o' j) ≤ 4 := by
  have hlt := (mem_octadMsgs (octadOf_mem ho)).1
  have hlt' := (mem_octadMsgs (octadOf_mem ho')).1
  have h8 := (mem_octadMsgs (octadOf_mem ho)).2
  have h8' := (mem_octadMsgs (octadOf_mem ho')).2
  have hne : octadOf o ≠ octadOf o' := fun h => hoo (octadOf_injOn ho ho' h)
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hx : octadOf o ^^^ octadOf o' < 2 ^ 12 :=
    xor_lt_two_pow (by rw [h12]; exact hlt) (by rw [h12]; exact hlt')
  have hmin := minWt_golay24 _ hx (xor_ne_zero hne)
  have h := cwt_add_cwt golay24Row 12 24 (octadOf o) (octadOf o')
  have hc : cinter golay24Row 12 24 (octadOf o) (octadOf o')
      = (List.range 24).countP (fun j => octadBit o j && octadBit o' j) := rfl
  rw [hc] at h
  omega

/-- Two distinct sign patterns disagree somewhere below rank seven. -/
theorem patSign_ne {pat pat' : ℕ} (hp : pat < 128) (hp' : pat' < 128) (h : pat ≠ pat') :
    ∃ r ∈ List.range 8, Bool.xor (patSign pat r) (patSign pat' r) = true := by
  obtain ⟨r, hr7, hrne⟩ : ∃ r, r < 7 ∧ pat.testBit r ≠ pat'.testBit r := by
    by_contra hcon
    push Not at hcon
    refine h (Nat.eq_of_testBit_eq fun i => ?_)
    rcases lt_or_ge i 7 with hi | hi
    · exact hcon i hi
    · have hpow : (2 : ℕ) ^ 7 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]
  refine ⟨r, List.mem_range.mpr (by omega), ?_⟩
  rw [patSign, if_pos hr7, patSign, if_pos hr7]
  cases hb : pat.testBit r <;> cases hb' : pat'.testBit r <;> simp_all

/-- **F2 against F2.** -/
theorem dotp_F2_F2 {o o' pat pat' : ℕ} (ho : o < 759) (ho' : o' < 759)
    (hp : pat < 128) (hp' : pat' < 128) (hne : ¬(o = o' ∧ pat = pat')) :
    dotp (leechF2 o pat) (leechF2 o' pat') ≤ 16 := by
  rw [leechF2_eq, leechF2_eq, dotp_vec24]
  by_cases hoo : o = o'
  · subst hoo
    have hpp : pat ≠ pat' := fun hh => hne ⟨rfl, hh⟩
    have hterm : ∀ j ∈ range 24, f2 o pat j * f2 o pat' j
        = (if octadBit o j then (4 : ℤ) else 0)
          + (if Bool.xor (patSign pat (octadRank o j)) (patSign pat' (octadRank o j))
              && octadBit o j then (-8 : ℤ) else 0) := by
      intro j _
      unfold f2
      by_cases hb : octadBit o j
      · by_cases h1 : patSign pat (octadRank o j) <;>
          by_cases h2 : patSign pat' (octadRank o j) <;> simp [hb, h1, h2]
      · simp [hb]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, sum_ite_countP_range,
      sum_ite_countP_range, countP_octadBit ho,
      countP_octad_rank ho fun r => Bool.xor (patSign pat r) (patSign pat' r)]
    have hx := countP_xor (patSign pat) (patSign pat') (List.range 8)
    have he := patSign_even pat hp
    have he' := patSign_even pat' hp'
    have hpos : 0 < (List.range 8).countP
        fun r => Bool.xor (patSign pat r) (patSign pat' r) :=
      List.countP_pos_iff.mpr (patSign_ne hp hp' hpp)
    omega
  · have hbound : ∀ j ∈ range 24, f2 o pat j * f2 o' pat' j
        ≤ (if octadBit o j && octadBit o' j then (4 : ℤ) else 0) := by
      intro j _
      unfold f2
      by_cases hb : octadBit o j
      · by_cases hb' : octadBit o' j
        · by_cases h1 : patSign pat (octadRank o j) <;>
            by_cases h2 : patSign pat' (octadRank o' j) <;> simp [hb, hb', h1, h2]
        · simp [hb, hb']
      · simp [hb]
    calc ∑ j ∈ range 24, f2 o pat j * f2 o' pat' j
        ≤ ∑ j ∈ range 24, (if octadBit o j && octadBit o' j then (4 : ℤ) else 0) :=
          Finset.sum_le_sum hbound
      _ = 4 * (((List.range 24).countP fun j => octadBit o j && octadBit o' j) : ℤ) :=
          sum_ite_countP_range _ _ _
      _ ≤ 16 := by have := countP_octad_inter ho ho' hoo; omega

/-! ## The second family against the third

This is the one case the minimum distance cannot settle. The octad carries
eight coordinates of `±2`, the third family carries `±1` off its distinguished
position and `∓3` on it. Eight coordinates at `2 · 1` already reach `16`, and
if the distinguished position falls inside the octad the crude count reaches
`2 · 7 + 2 · 3 = 20`.

What closes the gap is `wtDvd_golay24`, through `cinter_golay24_even`: an octad
and a Golay codeword share an even number of coordinates. Combined with
`patSign_even` that makes the number of sign clashes on the octad even, so the
octad part of the product is `16 - 4 M` with `M` even — never `20`, never `12`.
The distinguished position can subtract eight or add eight, and when it adds,
it is itself a clash, so `M ≥ 2` absorbs it exactly.
-/

/-- Where the octad sign and the Golay sign disagree. -/
def octadClash (o pat c j : ℕ) : Bool :=
  Bool.xor (patSign pat (octadRank o j)) (cbit golay24Row 12 c j)

/-- One coordinate of the second family against one Golay sign. -/
theorem f2_mul_golaySign (o pat c j : ℕ) :
    f2 o pat j * golaySign c j
      = (if octadBit o j then (2 : ℤ) else 0)
        + (if octadClash o pat c j && octadBit o j then (-4 : ℤ) else 0) := by
  unfold f2 golaySign octadClash
  by_cases hb : octadBit o j
  · by_cases h1 : patSign pat (octadRank o j) <;>
      by_cases h2 : cbit golay24Row 12 c j <;> simp [hb, h1, h2]
  · simp [hb]

/-- **The clashes on an octad are even in number.** Half of the statement is
`patSign_even`, half is `cinter_golay24_even`. -/
theorem countP_clash_even {o c : ℕ} (ho : o < 759) (hc : c < 4096) {pat : ℕ}
    (hp : pat < 128) :
    (List.range 24).countP (fun j => octadClash o pat c j && octadBit o j) % 2 = 0 := by
  have hp1 : ∀ j : ℕ, Bool.xor (patSign pat (octadRank o j) && octadBit o j)
      (cbit golay24Row 12 c j && octadBit o j)
      = (octadClash o pat c j && octadBit o j) := by
    intro j; unfold octadClash; cases octadBit o j <;> simp
  have hx := countP_xor (fun j => patSign pat (octadRank o j) && octadBit o j)
    (fun j => cbit golay24Row 12 c j && octadBit o j) (List.range 24)
  simp only [hp1] at hx
  have h1 : (List.range 24).countP (fun j => patSign pat (octadRank o j) && octadBit o j)
      = (List.range 8).countP (patSign pat) := countP_octad_rank ho (patSign pat)
  have h2 : (List.range 24).countP (fun j => cbit golay24Row 12 c j && octadBit o j)
      = cinter golay24Row 12 24 c (octadOf o) := rfl
  rw [h1, h2] at hx
  have he := patSign_even pat hp
  have he' := cinter_golay24_even hc (mem_octadMsgs (octadOf_mem ho)).1
  omega

/-- **F2 against F3.** -/
theorem dotp_F2_F3 {o pat c k : ℕ} (ho : o < 759) (hp : pat < 128) (hc : c < 4096)
    (hk : k < 24) : dotp (leechF2 o pat) (leechF3 c k) ≤ 16 := by
  rw [leechF2_eq, leechF3_eq, dotp_vec24]
  have hterm : ∀ j ∈ range 24, f2 o pat j * f3 c k j
      = (f2 o pat j * golaySign c j)
        + (if j = k then -4 * (f2 o pat k * golaySign c k) else 0) := by
    intro j _
    by_cases hjk : j = k
    · subst hjk; rw [f3_at, if_pos rfl]; ring
    · rw [f3_eq_of_ne hjk, if_neg hjk]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun j (_ : j ∈ range 24) => f2_mul_golaySign o pat c j),
    Finset.sum_add_distrib, sum_ite_countP_range, sum_ite_countP_range,
    countP_octadBit ho,
    Finset.sum_ite_eq' (range 24) k fun _ => -4 * (f2 o pat k * golaySign c k),
    if_pos (Finset.mem_range.mpr hk)]
  have heven := countP_clash_even ho hc hp
  by_cases hbk : octadBit o k
  · have hf2k : f2 o pat k = if patSign pat (octadRank o k) then -2 else 2 := by
      unfold f2; rw [if_pos hbk]
    by_cases hxk : octadClash o pat c k
    · have hpos : 0 < (List.range 24).countP fun j => octadClash o pat c j && octadBit o j :=
        List.countP_pos_iff.mpr ⟨k, List.mem_range.mpr hk, by simp [hxk, hbk]⟩
      have hW : f2 o pat k * golaySign c k = -2 := by
        unfold octadClash at hxk
        rw [hf2k, golaySign]
        by_cases h1 : patSign pat (octadRank o k) <;>
          by_cases h2 : cbit golay24Row 12 c k <;> simp_all
      rw [hW]; omega
    · have hW : f2 o pat k * golaySign c k = 2 := by
        unfold octadClash at hxk
        rw [hf2k, golaySign]
        by_cases h1 : patSign pat (octadRank o k) <;>
          by_cases h2 : cbit golay24Row 12 c k <;> simp_all
      rw [hW]; omega
  · have hW : f2 o pat k * golaySign c k = 0 := by
      unfold f2; rw [if_neg hbk, zero_mul]
    rw [hW]
    omega

/-! ## Negative controls: the constant `16` cannot be lowered

The measurement reports the maximum as attained on every family pair. Here are
the three witnesses for the pairs settled above, checked by the kernel. Any
future refactor that "improves" one of these bounds to `15` is wrong, and these
three theorems are what will say so.
-/

theorem dotp_F1_F1_tight : dotp (leechF1 0 0) (leechF1 1 0) = 16 := by decide +kernel

theorem dotp_F1_F2_tight : dotp (leechF1 0 0) (leechF2 2 0) = 16 := by decide +kernel

theorem dotp_F1_F3_tight : dotp (leechF1 0 0) (leechF3 1 0) = 16 := by decide +kernel

theorem dotp_F3_F3_tight : dotp (leechF3 0 0) (leechF3 0 1) = 16 := by decide +kernel

theorem dotp_F2_F2_tight : dotp (leechF2 0 0) (leechF2 0 1) = 16 := by decide +kernel

theorem dotp_F2_F3_tight : dotp (leechF2 0 0) (leechF3 0 1) = 16 := by decide +kernel

/-! ## The separation, assembled

Nine cases, six theorems: the three diagonal ones and the three off-diagonal
ones, each of the latter used twice. The index arithmetic is the splitting of
`leechVec` itself, so `omega` carries it.
-/

/-- **Any two distinct minimal Leech vectors have inner product at most `16`.** -/
theorem dotp_leechVec_le {i j : ℕ} (hi : i < 196560) (hj : j < 196560) (hij : i ≠ j) :
    dotp (leechVec i) (leechVec j) ≤ 16 := by
  by_cases hA : i < 1104
  · rw [leechVec_lo hA]
    by_cases hB : j < 1104
    · rw [leechVec_lo hB]
      exact dotp_F1_F1 (by omega) (by omega) (by omega) (by omega)
        (by rintro ⟨h1, h2⟩; omega)
    · by_cases hC : j < 98256
      · rw [leechVec_mid (by omega) hC]; exact dotp_F1_F2 (by omega) _ _ _
      · rw [leechVec_hi (by omega) (by omega)]; exact dotp_F1_F3 (by omega) _ _ _
  · by_cases hB : i < 98256
    · rw [leechVec_mid (by omega) hB]
      by_cases hC : j < 1104
      · rw [leechVec_lo hC]; exact dotp_F2_F1 (by omega) _ _ _
      · by_cases hD : j < 98256
        · rw [leechVec_mid (by omega) hD]
          exact dotp_F2_F2 (by omega) (by omega) (by omega) (by omega)
            (by rintro ⟨h1, h2⟩; omega)
        · rw [leechVec_hi (by omega) (by omega)]
          exact dotp_F2_F3 (by omega) (by omega) (by omega) (by omega)
    · rw [leechVec_hi (by omega) (by omega)]
      by_cases hC : j < 1104
      · rw [leechVec_lo hC]; exact dotp_F3_F1 (by omega) _ _ _
      · by_cases hD : j < 98256
        · rw [leechVec_mid (by omega) hD]
          rw [dotp_comm]
          exact dotp_F2_F3 (by omega) (by omega) (by omega) (by omega)
        · rw [leechVec_hi (by omega) (by omega)]
          exact dotp_F3_F3 (by omega) (by omega) (by omega) (by omega)
            (by rintro ⟨h1, h2⟩; omega)

/-- **The hypothesis of `mem_kissingSet_twentyFour_of_min`, discharged.** The
`32` is the minimum of the Leech lattice; here it is not assumed but read off
the inner products, through `dotp_vsub` and the constant norm `32`. -/
theorem min_leechVec (i j : Fin 196560) (hij : i ≠ j) :
    (32 : ℤ) ≤ dotp (vsub (leechVec i) (leechVec j)) (vsub (leechVec i) (leechVec j)) := by
  rw [dotp_vsub _ _ (by rw [leechVec_length, leechVec_length]),
    norm_leechVec i.isLt, norm_leechVec j.isLt]
  have := dotp_leechVec_le i.isLt j.isLt fun h => hij (Fin.val_injective h)
  omega

/-- **`196560` is a kissing configuration in dimension 24**, with no hypothesis
left. This is `mem_kissingSet_twentyFour_of_min` with its condition proved. -/
theorem mem_kissingSet_twentyFour : (196560 : ℕ) ∈ Sphere.kissingSet 24 :=
  mem_kissingSet_twentyFour_of_min min_leechVec

/-- **The kissing number of `ℝ^24` is exactly `196 560`.** The upper bound is
the Odlyzko-Sloane linear program of `Delsarte/Sphere/Kissing.lean`; the lower
bound is the Leech configuration above. Neither half is conditional. -/
theorem kissing_twentyFour : IsGreatest (Sphere.kissingSet 24) 196560 :=
  ⟨mem_kissingSet_twentyFour, fun _ hM => Sphere.kissingSet_twentyFour_le _ hM⟩

/-- `196 561` is excluded, which is the upper bound restated. -/
theorem not_mem_kissingSet_twentyFour : (196561 : ℕ) ∉ Sphere.kissingSet 24 := by
  intro h
  have := Sphere.kissingSet_twentyFour_le 196561 h
  norm_num at this

end Delsarte.Lattice
