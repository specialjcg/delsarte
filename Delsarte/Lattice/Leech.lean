/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Octad
import Delsarte.Lattice.Basic
import Mathlib.Data.List.GetD

/-!
# The 196 560 minimal vectors of the Leech lattice

In the scaling where every coordinate is an integer, the minimal vectors of the
Leech lattice have squared norm `32` and come in three shapes:

| count | shape | parameters |
|---|---|---|
| `1 104` | `(±4, ±4, 0^22)` | a pair `i < j`, four signs |
| `97 152` | `(∓2^8, 0^16)` | an octad, `2^7` even sign patterns |
| `98 304` | `(∓3, ±1^23)` | a Golay codeword, a position |

`1104 + 97152 + 98304 = 196560`. The three counts are `4 · C(24,2)`,
`759 · 2^7` and `24 · 2^12`, and the `759` is `octadMsgs_length`.

## Indexed, never listed

`leechVec` is a function `ℕ → List ℤ`, blind above `196 560`, in the idiom of
`MinWt` rather than in `Fin` arithmetic. Listing the vectors would mean handing
the kernel `4.7` million integers, the profile that already cost this repository
a build killed at `22.9 GB`. Nothing here enumerates: the lengths, the norms and
the counts of nonzero coordinates are all proved by symbolic sums over
`Finset.range 24`, for every index at once.

## Everything is tied to the Golay code that was proved

The sign patterns of the third family are `cbit golay24Row 12`, and the supports
of the second are `octadOf`, itself a filter of the same encoding. No second
table of codewords is introduced, so nothing here can drift away from
`A(24, 2, 8) = 4096`.

## Injectivity is work here, and it was free before

In an `IntConfig` a repeated vector is refuted by the separation itself. Not
here: the separation is what we are trying to establish, and deriving it from
`two_dotp_le_of_min` needs the difference of two vectors to be a *nonzero*
lattice vector. So `leechVec_injOn` is proved by hand, by reading the parameters
back off the vector — the families are told apart by their number of nonzero
coordinates, `2`, `8` and `24`, and inside each family the parametrization is
inverted.

The second family is the delicate one. Its sign pattern is indexed by *rank*
within the support, so reading it back needs the `r`-th support element to have
exactly `r` predecessors in the support: that is `countP_range_getD`, proved
once, generically, by induction on the range.

## What is still missing

The separation itself. `two_dotp_le_of_min` reduces it to the Leech minimum —
every nonzero lattice vector has squared norm at least `32` — and that fact is
not proved here, nor anywhere in this repository. Until it is, these `196 560`
vectors are a family with the right shape and no `IntFamily` instance, and
`kissingSet 24` keeps only its upper bound.
-/

namespace Delsarte.Lattice

open Delsarte Delsarte.Certificate Finset

/-! ## Vectors as mapped ranges -/

/-- A vector of `ℤ^24`, given coordinate by coordinate. -/
def vec24 (f : ℕ → ℤ) : List ℤ := (List.range 24).map f

@[simp]
theorem vec24_length (f : ℕ → ℤ) : (vec24 f).length = 24 := by simp [vec24]

/-- Reading a mapped range back coordinate by coordinate. -/
theorem ent_map_range (f : ℕ → ℤ) : ∀ (n j : ℕ), j < n → ent ((List.range n).map f) j = f j
  | 0, j, h => absurd h (Nat.not_lt_zero j)
  | (n + 1), 0, _ => by rw [List.range_succ_eq_map]; simp
  | (n + 1), (j + 1), h => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, ent_cons_succ]
      exact ent_map_range (fun x => f (x + 1)) n j (by omega)

theorem ent_vec24 (f : ℕ → ℤ) {j : ℕ} (hj : j < 24) : ent (vec24 f) j = f j :=
  ent_map_range f 24 j hj

theorem dotp_vec24 (f g : ℕ → ℤ) :
    dotp (vec24 f) (vec24 g) = ∑ j ∈ range 24, f j * g j := by
  rw [dotp_eq_sum _ _ 24 (vec24_length f) (vec24_length g)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ent_vec24 f (Finset.mem_range.mp hj), ent_vec24 g (Finset.mem_range.mp hj)]

/-- The squared norm of a vector given coordinatewise. -/
theorem norm_vec24 (f : ℕ → ℤ) : dotp (vec24 f) (vec24 f) = ∑ j ∈ range 24, f j * f j :=
  dotp_vec24 f f

/-! ## The first family: two coordinates `±4` -/

/-- The `276` pairs `i < j` below `24`, in lexicographic order. -/
def pairList : List (ℕ × ℕ) :=
  (List.range 24).flatMap fun i =>
    (List.range 24).filterMap fun j => if i < j then some (i, j) else none

theorem pairList_length : pairList.length = 276 := by decide +kernel

theorem pairList_nodup : pairList.Nodup := by decide +kernel

theorem pairList_bounds : ∀ p ∈ pairList, p.1 < p.2 ∧ p.2 < 24 := by decide +kernel

/-- The `q`-th pair. -/
def pairOf (q : ℕ) : ℕ × ℕ := pairList.getD q (0, 0)

theorem pairOf_mem {q : ℕ} (hq : q < 276) : pairOf q ∈ pairList := by
  have h : q < pairList.length := by rw [pairList_length]; exact hq
  rw [pairOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem _

theorem pairOf_lt {q : ℕ} (hq : q < 276) : (pairOf q).1 < (pairOf q).2 :=
  (pairList_bounds _ (pairOf_mem hq)).1

theorem pairOf_lt_24 {q : ℕ} (hq : q < 276) : (pairOf q).2 < 24 :=
  (pairList_bounds _ (pairOf_mem hq)).2

theorem pairOf_injOn {q q' : ℕ} (hq : q < 276) (hq' : q' < 276)
    (h : pairOf q = pairOf q') : q = q' := by
  have h1 : q < pairList.length := by rw [pairList_length]; exact hq
  have h2 : q' < pairList.length := by rw [pairList_length]; exact hq'
  have e1 : pairOf q = pairList[q]'h1 := by
    rw [pairOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rfl
  have e2 : pairOf q' = pairList[q']'h2 := by
    rw [pairOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  rw [e1, e2] at h
  have hfin : (⟨q, h1⟩ : Fin pairList.length) = ⟨q', h2⟩ :=
    List.nodup_iff_injective_getElem.mp pairList_nodup h
  exact congrArg Fin.val hfin

/-- `+4` on an even bit, `-4` on an odd one. -/
def signFour (b : ℕ) : ℤ := if b % 2 = 0 then 4 else -4

theorem signFour_sq (b : ℕ) : signFour b * signFour b = 16 := by
  unfold signFour; split <;> norm_num

theorem signFour_ne_zero (b : ℕ) : signFour b ≠ 0 := by
  unfold signFour; split <;> norm_num

/-- `(±4, ±4, 0^22)`, on the pair `q` with the two signs read off `st`. -/
def leechF1 (q st : ℕ) : List ℤ :=
  vec24 fun j =>
    if j = (pairOf q).1 then signFour st
    else if j = (pairOf q).2 then signFour (st / 2) else 0

/-! ## The second family: an octad carrying `±2` -/

/-- Bit `j` of the `o`-th octad. -/
def octadBit (o j : ℕ) : Bool := cbit golay24Row 12 (octadOf o) j

/-- How many support positions of the `o`-th octad lie below `j`. -/
def octadRank (o j : ℕ) : ℕ := (List.range j).countP (octadBit o)

/-- The support of the `o`-th octad, in increasing order. -/
def octadSupp (o : ℕ) : List ℕ := (List.range 24).filter (octadBit o)

/-- The sign at rank `r` for the pattern `pat < 128`: seven free bits, the eighth
their parity, so the number of minus signs on the octad is even. -/
def patSign (pat r : ℕ) : Bool :=
  if r < 7 then pat.testBit r
  else decide ((List.range 7).countP (fun t => pat.testBit t) % 2 = 1)

/-- `(∓2^8, 0^16)`, supported on the `o`-th octad. -/
def leechF2 (o pat : ℕ) : List ℤ :=
  vec24 fun j =>
    if octadBit o j then (if patSign pat (octadRank o j) then -2 else 2) else 0

/-! ## The third family: `(∓3, ±1^23)` -/

/-- The sign of coordinate `j` under the Golay codeword `c`. -/
def golaySign (c j : ℕ) : ℤ := if cbit golay24Row 12 c j then -1 else 1

theorem golaySign_sq (c j : ℕ) : golaySign c j * golaySign c j = 1 := by
  unfold golaySign; split <;> norm_num

/-- `(∓3, ±1^23)`: the signs come from the codeword `c`, the position `k` carries
the `∓3`. -/
def leechF3 (c k : ℕ) : List ℤ :=
  vec24 fun j => if j = k then -3 * golaySign c k else golaySign c j

/-! ## The family, assembled -/

/-- The `m`-th minimal vector, blind above `196 560`. -/
def leechVec (m : ℕ) : List ℤ :=
  if m < 1104 then leechF1 (m / 4) (m % 4)
  else if m < 98256 then leechF2 ((m - 1104) / 128) ((m - 1104) % 128)
  else leechF3 ((m - 98256) / 24) ((m - 98256) % 24)

theorem leechVec_length (m : ℕ) : (leechVec m).length = 24 := by
  unfold leechVec leechF1 leechF2 leechF3
  split
  · exact vec24_length _
  · split
    · exact vec24_length _
    · exact vec24_length _

/-! ## The squared norm is 32 -/

theorem norm_leechF1 {q : ℕ} (hq : q < 276) (st : ℕ) :
    dotp (leechF1 q st) (leechF1 q st) = 32 := by
  have hlt := pairOf_lt hq
  have h24 := pairOf_lt_24 hq
  rw [leechF1, norm_vec24]
  have key : ∀ j ∈ range 24,
      (if j = (pairOf q).1 then signFour st
        else if j = (pairOf q).2 then signFour (st / 2) else 0) *
      (if j = (pairOf q).1 then signFour st
        else if j = (pairOf q).2 then signFour (st / 2) else 0)
      = (if j = (pairOf q).1 then (16 : ℤ) else 0)
        + (if j = (pairOf q).2 then (16 : ℤ) else 0) := by
    intro j _
    by_cases h1 : j = (pairOf q).1
    · have h2 : j ≠ (pairOf q).2 := by omega
      simp only [if_pos h1, if_neg h2, signFour_sq]
      norm_num
    · by_cases h2 : j = (pairOf q).2
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, signFour_sq]
        norm_num
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        norm_num
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range 24) (pairOf q).1 (fun _ => (16 : ℤ)),
    Finset.sum_ite_eq' (range 24) (pairOf q).2 (fun _ => (16 : ℤ)),
    if_pos (Finset.mem_range.mpr (by omega)), if_pos (Finset.mem_range.mpr h24)]
  norm_num

/-- The number of support positions of the `o`-th octad. Its value `8` is the
defining property of an octad, read off `octadMsgs`. -/
theorem countP_octadBit {o : ℕ} (ho : o < 759) :
    (List.range 24).countP (octadBit o) = 8 := by
  have h := (mem_octadMsgs (octadOf_mem ho)).2
  rw [cwt] at h
  exact h

/-- A constant weight distributed over a Boolean predicate, in `ℤ`. -/
theorem sum_ite_countP (p : ℕ → Bool) (a : ℤ) :
    ∑ j ∈ range 24, (if p j then a else 0) = a * ((List.range 24).countP p : ℤ) := by
  rw [countP_range_eq_sum, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p j <;> simp [h]

theorem norm_leechF2 {o : ℕ} (ho : o < 759) (pat : ℕ) :
    dotp (leechF2 o pat) (leechF2 o pat) = 32 := by
  rw [leechF2, norm_vec24]
  have key : ∀ j ∈ range 24,
      (if octadBit o j then (if patSign pat (octadRank o j) then (-2 : ℤ) else 2) else 0) *
        (if octadBit o j then (if patSign pat (octadRank o j) then (-2 : ℤ) else 2) else 0)
        = if octadBit o j then (4 : ℤ) else 0 := by
    intro j _
    by_cases h : octadBit o j
    · by_cases h2 : patSign pat (octadRank o j) <;> simp [h, h2]
    · simp [h]
  rw [Finset.sum_congr rfl key, sum_ite_countP, countP_octadBit ho]
  norm_num

theorem golaySign_ne_zero (c j : ℕ) : golaySign c j ≠ 0 := by
  unfold golaySign; split <;> norm_num

theorem norm_leechF3 (c : ℕ) {k : ℕ} (hk : k < 24) :
    dotp (leechF3 c k) (leechF3 c k) = 32 := by
  rw [leechF3, norm_vec24]
  have key : ∀ j ∈ range 24,
      (if j = k then -3 * golaySign c k else golaySign c j) *
        (if j = k then -3 * golaySign c k else golaySign c j)
        = 1 + (if j = k then (8 : ℤ) else 0) := by
    intro j _
    by_cases h : j = k
    · simp only [if_pos h]
      calc (-3 * golaySign c k) * (-3 * golaySign c k)
          = 9 * (golaySign c k * golaySign c k) := by ring
        _ = 1 + 8 := by rw [golaySign_sq]; norm_num
    · simp only [if_neg h]
      rw [golaySign_sq]
      norm_num
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range 24) k (fun _ => (8 : ℤ)),
    if_pos (Finset.mem_range.mpr hk)]
  simp

/-! ## How many coordinates are nonzero

`2`, `8` and `24`. This is what tells the three families apart, and it is the
first half of injectivity. -/

/-- The number of nonzero coordinates of `v`. -/
def nzCount (v : List ℤ) : ℕ := (List.range 24).countP (fun j => ent v j != 0)

theorem nz_leechF1 {q : ℕ} (hq : q < 276) (st : ℕ) : nzCount (leechF1 q st) = 2 := by
  have hlt := pairOf_lt hq
  have h24 := pairOf_lt_24 hq
  have hne : (pairOf q).1 ≠ (pairOf q).2 := by omega
  rw [nzCount, countP_range_eq_sum]
  have key : ∀ j ∈ range 24,
      (if (ent (leechF1 q st) j != 0) = true then 1 else 0)
        = (if j = (pairOf q).1 then 1 else 0) + (if j = (pairOf q).2 then 1 else 0) := by
    intro j hj
    rw [leechF1, ent_vec24 _ (Finset.mem_range.mp hj)]
    by_cases h1 : j = (pairOf q).1
    · subst h1
      simp [hne, signFour_ne_zero]
    · by_cases h2 : j = (pairOf q).2
      · subst h2
        simp [h1, signFour_ne_zero]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range 24) (pairOf q).1 (fun _ => 1),
    Finset.sum_ite_eq' (range 24) (pairOf q).2 (fun _ => 1),
    if_pos (Finset.mem_range.mpr (by omega)), if_pos (Finset.mem_range.mpr h24)]

theorem nz_leechF2 {o : ℕ} (ho : o < 759) (pat : ℕ) : nzCount (leechF2 o pat) = 8 := by
  rw [nzCount, countP_range_eq_sum, ← countP_octadBit ho, countP_range_eq_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [leechF2, ent_vec24 _ (Finset.mem_range.mp hj)]
  by_cases h : octadBit o j
  · by_cases h2 : patSign pat (octadRank o j) <;> simp [h, h2]
  · simp [h]

theorem nz_leechF3 (c k : ℕ) : nzCount (leechF3 c k) = 24 := by
  rw [nzCount, countP_range_eq_sum]
  have key : ∀ j ∈ range 24, (if (ent (leechF3 c k) j != 0) = true then 1 else 0) = 1 := by
    intro j hj
    rw [leechF3, ent_vec24 _ (Finset.mem_range.mp hj)]
    by_cases h : j = k
    · simp only [if_pos h]
      simp [golaySign_ne_zero]
    · simp only [if_neg h]
      simp [golaySign_ne_zero]
  rw [Finset.sum_congr rfl key]
  simp

/-! ## Injectivity

Not free here. In an `IntConfig` a repeated vector is refuted by the separation
itself, but the separation is what we are trying to establish, so the
parametrization has to be inverted by hand. -/

/-- The `r`-th element of a filtered range has exactly `r` predecessors passing
the filter. This is what lets a sign pattern be indexed by rank and still be read
back off the vector. -/
theorem countP_range_getD (p : ℕ → Bool) :
    ∀ (n r : ℕ), r < ((List.range n).filter p).length →
      (List.range (((List.range n).filter p).getD r 0)).countP p = r
  | 0, r, h => by simp at h
  | (n + 1), r, h => by
      rw [List.range_succ, List.filter_append] at h ⊢
      by_cases hr : r < ((List.range n).filter p).length
      · rw [List.getD_append _ _ _ _ hr]
        exact countP_range_getD p n r hr
      · have hp : p n = true := by
          rcases Bool.eq_false_or_eq_true (p n) with hpn | hpn
          · exact hpn
          · rw [show List.filter p [n] = [] by simp [hpn], List.append_nil] at h
            exact absurd h hr
        rw [show List.filter p [n] = [n] by simp [hp]] at h ⊢
        have hlen : ((List.range n).filter p).length = r := by
          simp only [List.length_append, List.length_cons, List.length_nil] at h
          omega
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self,
          show ([n] : List ℕ).getD 0 0 = n from rfl]
        rw [List.countP_eq_length_filter]
        exact hlen

/-- **The Golay encoding is injective.** Two messages below `4096` whose
codewords agree coordinate by coordinate are equal — otherwise their `xor` would
be a nonzero message, and `minWt_golay24` gives its codeword weight at least
`8`, so some coordinate would differ. -/
theorem cbit_inj {m m' : ℕ} (hm : m < 4096) (hm' : m' < 4096)
    (h : ∀ j < 24, cbit golay24Row 12 m j = cbit golay24Row 12 m' j) : m = m' := by
  by_contra hne
  have hm2 : m < 2 ^ 12 := by rw [show (2 : ℕ) ^ 12 = 4096 from by norm_num]; exact hm
  have hm2' : m' < 2 ^ 12 := by rw [show (2 : ℕ) ^ 12 = 4096 from by norm_num]; exact hm'
  have h8 := minWt_golay24 _ (xor_lt_two_pow hm2 hm2') (xor_ne_zero hne)
  rw [cwt] at h8
  have hz : (List.range 24).countP (cbit golay24Row 12 (m ^^^ m')) = 0 := by
    rw [List.countP_eq_zero]
    intro j hj
    rw [cbit_xor, h j (List.mem_range.mp hj)]
    simp
  omega

/-! ### The first family -/

theorem signFour_inj {a b : ℕ} (h : signFour a = signFour b) : a % 2 = b % 2 := by
  unfold signFour at h
  split_ifs at h with ha hb hb <;> omega

theorem coord_leechF1 {q st : ℕ} {j : ℕ} (hj : j < 24) :
    ent (leechF1 q st) j
      = if j = (pairOf q).1 then signFour st
        else if j = (pairOf q).2 then signFour (st / 2) else 0 := by
  rw [leechF1, ent_vec24 _ hj]

theorem inj_leechF1 {q st q' st' : ℕ} (hq : q < 276) (hq' : q' < 276)
    (hst : st < 4) (hst' : st' < 4) (h : leechF1 q st = leechF1 q' st') :
    q = q' ∧ st = st' := by
  have hlt := pairOf_lt hq
  have hlt' := pairOf_lt hq'
  have h24 := pairOf_lt_24 hq
  have h24' := pairOf_lt_24 hq'
  have hco : ∀ j, j < 24 →
      (if j = (pairOf q).1 then signFour st
        else if j = (pairOf q).2 then signFour (st / 2) else 0)
      = (if j = (pairOf q').1 then signFour st'
        else if j = (pairOf q').2 then signFour (st' / 2) else 0) := by
    intro j hj
    rw [← coord_leechF1 hj, ← coord_leechF1 hj, h]
  have hA : (pairOf q).1 = (pairOf q').1 ∨ (pairOf q).1 = (pairOf q').2 := by
    by_contra hc
    obtain ⟨hc1, hc2⟩ := not_or.mp hc
    have := hco (pairOf q).1 (by omega)
    rw [if_pos rfl, if_neg hc1, if_neg hc2] at this
    exact signFour_ne_zero st this
  have hB : (pairOf q).2 = (pairOf q').1 ∨ (pairOf q).2 = (pairOf q').2 := by
    by_contra hc
    obtain ⟨hc1, hc2⟩ := not_or.mp hc
    have := hco (pairOf q).2 h24
    rw [if_neg (by omega), if_pos rfl, if_neg hc1, if_neg hc2] at this
    exact signFour_ne_zero (st / 2) this
  have h1 : (pairOf q).1 = (pairOf q').1 := by omega
  have h2 : (pairOf q).2 = (pairOf q').2 := by omega
  have hpair : pairOf q = pairOf q' := Prod.ext h1 h2
  refine ⟨pairOf_injOn hq hq' hpair, ?_⟩
  have e1 := hco (pairOf q).1 (by omega)
  rw [if_pos rfl, if_pos h1] at e1
  have e2 := hco (pairOf q).2 h24
  rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos h2] at e2
  have m1 := signFour_inj e1
  have m2 := signFour_inj e2
  omega

/-! ### The second family -/

theorem octadSupp_length {o : ℕ} (ho : o < 759) : (octadSupp o).length = 8 := by
  rw [octadSupp, ← List.countP_eq_length_filter, countP_octadBit ho]

theorem octadSupp_getD_mem {o : ℕ} (ho : o < 759) {r : ℕ} (hr : r < 8) :
    (octadSupp o).getD r 0 ∈ octadSupp o := by
  have hl : r < (octadSupp o).length := by rw [octadSupp_length ho]; exact hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  exact List.getElem_mem _

theorem octadSupp_lt {o j : ℕ} (h : j ∈ octadSupp o) : j < 24 := by
  rw [octadSupp, List.mem_filter, List.mem_range] at h
  exact h.1

theorem octadSupp_bit {o j : ℕ} (h : j ∈ octadSupp o) : octadBit o j = true := by
  rw [octadSupp, List.mem_filter] at h
  exact h.2

theorem octadRank_getD {o : ℕ} (ho : o < 759) {r : ℕ} (hr : r < 8) :
    octadRank o ((octadSupp o).getD r 0) = r := by
  have hl : r < ((List.range 24).filter (octadBit o)).length := by
    rw [← octadSupp, octadSupp_length ho]; exact hr
  exact countP_range_getD (octadBit o) 24 r hl

theorem coord_leechF2 {o pat : ℕ} {j : ℕ} (hj : j < 24) :
    ent (leechF2 o pat) j
      = if octadBit o j then (if patSign pat (octadRank o j) then (-2 : ℤ) else 2) else 0 := by
  rw [leechF2, ent_vec24 _ hj]

theorem inj_leechF2 {o pat o' pat' : ℕ} (ho : o < 759) (ho' : o' < 759)
    (hp : pat < 128) (hp' : pat' < 128) (h : leechF2 o pat = leechF2 o' pat') :
    o = o' ∧ pat = pat' := by
  have hco : ∀ j, j < 24 →
      (if octadBit o j then (if patSign pat (octadRank o j) then (-2 : ℤ) else 2) else 0)
      = if octadBit o' j then (if patSign pat' (octadRank o' j) then (-2 : ℤ) else 2) else 0 := by
    intro j hj
    rw [← coord_leechF2 hj, ← coord_leechF2 hj, h]
  have hbit : ∀ j, j < 24 → octadBit o j = octadBit o' j := by
    intro j hj
    have e := hco j hj
    by_cases a : octadBit o j <;> by_cases b : octadBit o' j <;>
      simp only [a, b, if_true, if_false, Bool.false_eq_true] at e ⊢ <;>
      first
        | rfl
        | (exfalso; revert e; split <;> norm_num)
  have hoo : octadOf o = octadOf o' :=
    cbit_inj (mem_octadMsgs (octadOf_mem ho)).1 (mem_octadMsgs (octadOf_mem ho')).1 hbit
  have hoe : o = o' := octadOf_injOn ho ho' hoo
  subst hoe
  refine ⟨rfl, ?_⟩
  have hbits : ∀ r, r < 7 → pat.testBit r = pat'.testBit r := by
    intro r hr
    have hjm := octadSupp_getD_mem ho (show r < 8 by omega)
    have e := hco ((octadSupp o).getD r 0) (octadSupp_lt hjm)
    rw [if_pos (octadSupp_bit hjm), if_pos (octadSupp_bit hjm),
      octadRank_getD ho (show r < 8 by omega)] at e
    have hps : patSign pat r = patSign pat' r := by
      by_cases a : patSign pat r <;> by_cases b : patSign pat' r <;>
        simp only [a, b, if_true, if_false, Bool.false_eq_true] at e ⊢ <;> try norm_num at e
    rw [patSign, if_pos hr, patSign, if_pos hr] at hps
    exact hps
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 7
  · exact hbits i hi
  · have hpow : (128 : ℕ) ≤ 2 ^ i := by
      calc (128 : ℕ) = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-! ### The third family -/

theorem golaySign_inj {c c' j : ℕ} (h : golaySign c j = golaySign c' j) :
    cbit golay24Row 12 c j = cbit golay24Row 12 c' j := by
  unfold golaySign at h
  by_cases a : cbit golay24Row 12 c j <;> by_cases b : cbit golay24Row 12 c' j <;>
    simp only [a, b, if_true, if_false, Bool.false_eq_true] at h ⊢ <;> try norm_num at h

theorem coord_leechF3 {c k : ℕ} {j : ℕ} (hj : j < 24) :
    ent (leechF3 c k) j = if j = k then -3 * golaySign c k else golaySign c j := by
  rw [leechF3, ent_vec24 _ hj]

theorem inj_leechF3 {c k c' k' : ℕ} (hc : c < 4096) (hc' : c' < 4096)
    (hk : k < 24) (hk' : k' < 24) (h : leechF3 c k = leechF3 c' k') :
    c = c' ∧ k = k' := by
  have hco : ∀ j, j < 24 →
      (if j = k then -3 * golaySign c k else golaySign c j)
      = if j = k' then -3 * golaySign c' k' else golaySign c' j := by
    intro j hj
    rw [← coord_leechF3 hj, ← coord_leechF3 hj, h]
  have hkk : k = k' := by
    by_contra hne
    have e := hco k hk
    rw [if_pos rfl, if_neg hne] at e
    unfold golaySign at e
    split_ifs at e <;> omega
  subst hkk
  refine ⟨?_, rfl⟩
  apply cbit_inj hc hc'
  intro j hj
  have e := hco j hj
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos hjk] at e
    have e' : golaySign c k = golaySign c' k := by
      have : (-3 : ℤ) ≠ 0 := by norm_num
      exact mul_left_cancel₀ this e
    rw [hjk]
    exact golaySign_inj e'
  · rw [if_neg hjk, if_neg hjk] at e
    exact golaySign_inj e

/-! ## The family as a whole -/

theorem leechVec_lo {m : ℕ} (h : m < 1104) : leechVec m = leechF1 (m / 4) (m % 4) := by
  rw [leechVec, if_pos h]

theorem leechVec_mid {m : ℕ} (h1 : ¬m < 1104) (h2 : m < 98256) :
    leechVec m = leechF2 ((m - 1104) / 128) ((m - 1104) % 128) := by
  rw [leechVec, if_neg h1, if_pos h2]

theorem leechVec_hi {m : ℕ} (h1 : ¬m < 1104) (h2 : ¬m < 98256) :
    leechVec m = leechF3 ((m - 98256) / 24) ((m - 98256) % 24) := by
  rw [leechVec, if_neg h1, if_neg h2]

/-- **Every one of the 196 560 vectors has squared norm 32.** -/
theorem norm_leechVec {m : ℕ} (hm : m < 196560) : dotp (leechVec m) (leechVec m) = 32 := by
  rcases lt_or_ge m 1104 with hA | hA
  · rw [leechVec_lo hA]
    exact norm_leechF1 (by omega) _
  · rcases lt_or_ge m 98256 with hB | hB
    · rw [leechVec_mid (by omega) hB]
      exact norm_leechF2 (by omega) _
    · rw [leechVec_hi (by omega) (by omega)]
      exact norm_leechF3 _ (by omega)

/-- **The 196 560 vectors are pairwise distinct.** The families are told apart by
their numbers of nonzero coordinates, `2`, `8` and `24`; inside a family the
parametrization is inverted. -/
theorem leechVec_injOn {m m' : ℕ} (hm : m < 196560) (hm' : m' < 196560)
    (h : leechVec m = leechVec m') : m = m' := by
  have hnz : nzCount (leechVec m) = nzCount (leechVec m') := by rw [h]
  rcases lt_or_ge m 1104 with hA | hA <;> rcases lt_or_ge m' 1104 with hB | hB
  · rw [leechVec_lo hA, leechVec_lo hB] at h
    obtain ⟨hq, hs⟩ := inj_leechF1 (by omega) (by omega) (by omega) (by omega) h
    omega
  · exfalso
    rcases lt_or_ge m' 98256 with hC | hC
    · rw [leechVec_lo hA, leechVec_mid (by omega) hC, nz_leechF1 (by omega),
        nz_leechF2 (by omega)] at hnz
      omega
    · rw [leechVec_lo hA, leechVec_hi (by omega) (by omega), nz_leechF1 (by omega),
        nz_leechF3] at hnz
      omega
  · exfalso
    rcases lt_or_ge m 98256 with hC | hC
    · rw [leechVec_mid (by omega) hC, leechVec_lo hB, nz_leechF2 (by omega),
        nz_leechF1 (by omega)] at hnz
      omega
    · rw [leechVec_hi (by omega) (by omega), leechVec_lo hB, nz_leechF3,
        nz_leechF1 (by omega)] at hnz
      omega
  · rcases lt_or_ge m 98256 with hC | hC <;> rcases lt_or_ge m' 98256 with hD | hD
    · rw [leechVec_mid (by omega) hC, leechVec_mid (by omega) hD] at h
      obtain ⟨ho, hp⟩ := inj_leechF2 (by omega) (by omega) (by omega) (by omega) h
      omega
    · exfalso
      rw [leechVec_mid (by omega) hC, leechVec_hi (by omega) (by omega),
        nz_leechF2 (by omega), nz_leechF3] at hnz
      omega
    · exfalso
      rw [leechVec_hi (by omega) (by omega), leechVec_mid (by omega) hD,
        nz_leechF3, nz_leechF2 (by omega)] at hnz
      omega
    · rw [leechVec_hi (by omega) (by omega), leechVec_hi (by omega) (by omega)] at h
      obtain ⟨hc, hk⟩ := inj_leechF3 (by omega) (by omega) (by omega) (by omega) h
      omega

/-- `1104 + 97152 + 98304 = 196560`: `4 · C(24,2)`, `759 · 2^7` and `24 · 2^12`,
with the `759` supplied by `octadMsgs_length`. -/
theorem leech_count : 4 * 276 + octadMsgs.length * 128 + 24 * 4096 = 196560 := by
  rw [octadMsgs_length]

/-! ## What is still missing, stated precisely -/

/-- **Everything except the separation.** Given the Leech minimum — the
difference of two distinct minimal vectors is again at least as long — the
`196 560` vectors are an `IntFamily 24 196560 32`, and the kissing bound follows.
Nothing else is outstanding: the lengths, the norms and the distinctness are
proved above.

The hypothesis is where the remaining work is. Proving it means formalizing the
lattice and its minimum, and it needs `leechVec_injOn`, since a difference must
be a *nonzero* lattice vector before the minimum says anything about it. -/
def leechFamily
    (hmin : ∀ i j : Fin 196560, i ≠ j →
      (32 : ℤ) ≤ dotp (vsub (leechVec i) (leechVec j)) (vsub (leechVec i) (leechVec j))) :
    IntFamily 24 196560 32 where
  vec := fun i => leechVec i
  npos := by norm_num
  length := fun i => leechVec_length i
  norm := fun i => norm_leechVec i.isLt
  sep := fun i j hij =>
    two_dotp_le_of_min (by rw [leechVec_length, leechVec_length])
      (norm_leechVec i.isLt) (norm_leechVec j.isLt) (hmin i j hij)

/-- The kissing bound in dimension `24`, **conditional** on the Leech minimum.
This is not a proof that the kissing number is `196 560`; it is a statement of
exactly what is left to prove. -/
theorem mem_kissingSet_twentyFour_of_min
    (hmin : ∀ i j : Fin 196560, i ≠ j →
      (32 : ℤ) ≤ dotp (vsub (leechVec i) (leechVec j)) (vsub (leechVec i) (leechVec j))) :
    (196560 : ℕ) ∈ Sphere.kissingSet 24 :=
  (leechFamily hmin).mem_kissingSet

/-! ## Negative controls -/

/-- The sign patterns really do have an even number of minus signs: the eighth
sign is the parity of the first seven, checked on all `128` patterns. -/
theorem patSign_even : ∀ pat < 128, (List.range 8).countP (patSign pat) % 2 = 0 := by
  decide +kernel

/-- ...and raw eight-bit patterns do not: the pattern with only bit `0` set has
an odd number of minus signs. `patSign` is doing work, not decoration. -/
theorem exists_odd_raw : (List.range 8).countP (fun r => (1 : ℕ).testBit r) % 2 = 1 := by
  decide +kernel

/-- Bit `j` of the codeword of message `1`, the first generator row. `isOctad_one`
says it has weight `8`, so this is an octad, and a cheap one: no enumeration is
needed to name it. -/
def ctrlBit (j : ℕ) : Bool := cbit golay24Row 12 1 j

/-- `+2` everywhere on that octad: zero minus signs, an even number. -/
def ctrlEven : List ℤ := vec24 fun j => if ctrlBit j then 2 else 0

/-- The same octad with a single minus sign: an odd number, so not a Leech
vector. -/
def ctrlOdd : List ℤ := vec24 fun j => if ctrlBit j then (if j = 0 then -2 else 2) else 0

/-- The forbidden vector has the right squared norm. The norm is not what
excludes it. -/
theorem ctrlOdd_norm : dotp ctrlOdd ctrlOdd = 32 := by decide +kernel

theorem ctrlEven_norm : dotp ctrlEven ctrlEven = 32 := by decide +kernel

/-- ...and yet it sits at inner product `24` from a genuine member of the family,
far past the `16` that `gram ≤ 1/2` allows. Admitting odd sign patterns would
break the separation, exactly as dropping the parity filter on the `E8` coset
does. Measured against the whole family, this vector exceeds `16` on `264` of
them. -/
theorem ctrlOdd_dotp : dotp ctrlEven ctrlOdd = 24 := by decide +kernel

theorem ctrlOdd_not_separated : ¬ 2 * dotp ctrlEven ctrlOdd ≤ 32 := by
  rw [ctrlOdd_dotp]
  norm_num

/-- The pairs are strictly ordered: no diagonal, so the first family never has a
single coordinate carrying `±8`. -/
theorem pairList_no_diagonal : (5, 5) ∉ pairList := by decide +kernel

end Delsarte.Lattice
