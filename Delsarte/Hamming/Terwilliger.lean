/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring

/-!
# Schrijver's block coefficients and the identity their positivity comes from

Issue #45. The blocks (19) of Schrijver's semidefinite program are positive for
every code; `Delsarte/Hamming/THEOREM1.md` is the argument on paper, and this
file is the part of it that is pure combinatorics.

Fix `k` disjoint pairs of coordinates and weight a subset `v` by

`cc P v = ∏_{(a,b) ∈ P} ([a ∈ v] - [b ∈ v])`,

which vanishes unless `v` meets every pair exactly once. The identity, proved
below as `gram_eq_pow_mul_beta`, is

`∑_{|v|=i, |w|=j, |v ∩ w|=t} cc P v * cc P w = 2^k * beta n i j k t`,

and the reason it matters is that it turns a block entry into `u_iᵀ M u_j` for
explicit vectors, so that `wᵀ B_k w` is `yᵀ M y` with `M` a sum of `χχᵀ`. That is
a sum of squares, which is the shape `Delsarte.SDP.Sparse.Data.Feasible` asks
for — it states positivity as a quadratic form and never mentions a spectrum.

## `mult` is a cardinality here

`tools/schrijver_algebra.py` defines `mult` by a factorial formula. This file
defines it as what it counts, and leaves the closed form to a separate lemma. The
split is deliberate: the identity below needs only the counting, and the
factorial form is needed later, at the bridge to the encoded program, where the
coefficients have to be evaluated against the integers in
`Delsarte/SDP/Schrijver19_6.lean`.

## Signs

Equation (7') carries `(-1)^(k-t+r)`. Over `ℕ` that subtraction truncates, so the
exponent is written `k + t + r`; the two differ by `2t` and give the same sign.
The float version of the same expression was a live defect on the Python side.
-/

namespace Delsarte.Hamming

open Finset

variable {n : ℕ}

/-- Peel two distinct coordinates off a sum over a powerset at once.

`Finset.sum_powerset_insert` peels one; a pair needs both, and the four terms on
the right are the four traces of `v` on `{a, b}`. Mathlib has the one-coordinate
version only, so this is stated here rather than imported. -/
theorem sum_powerset_insert_pair {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    {a b : α} {s : Finset α} (hab : a ≠ b) (ha : a ∉ s) (hb : b ∉ s) (f : Finset α → M) :
    ∑ v ∈ (insert a (insert b s)).powerset, f v
      = ∑ v ∈ s.powerset,
          (f v + f (insert b v) + f (insert a v) + f (insert a (insert b v))) := by
  rw [Finset.sum_powerset_insert (by simp [hab, ha]), Finset.sum_powerset_insert hb,
    Finset.sum_powerset_insert hb]
  simp only [Finset.sum_add_distrib, add_assoc]

/-- Pairs of subsets of `F` with prescribed sizes and prescribed intersection.

Relativised to a set of coordinates rather than stated over `Fin m` for the right
`m`. Peeling one pair removes two coordinates, which would change the type and
put the induction out of reach of `Finset.induction_on`; restricting inside a
fixed `Fin n` keeps it available. `multOn_card` below is what ties this back to
the absolute count. -/
def multOnFinset (F : Finset (Fin n)) (i j t : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((powersetCard i F) ×ˢ powersetCard j F).filter fun p => (p.1 ∩ p.2).card = t

/-- How many pairs `(v, w)` of subsets of `F` have `|v| = i`, `|w| = j` and
`|v ∩ w| = t`. -/
def multOn (F : Finset (Fin n)) (i j t : ℕ) : ℕ := (multOnFinset F i j t).card

/-- Pairs of subsets with prescribed sizes and prescribed intersection. -/
def multFinset (n i j t : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  multOnFinset (univ : Finset (Fin n)) i j t

/-- How many pairs `(v, w)` have `|v| = i`, `|w| = j` and `|v ∩ w| = t`. -/
def mult (n i j t : ℕ) : ℕ := (multFinset n i j t).card

@[simp] theorem multOn_univ (i j t : ℕ) :
    multOn (univ : Finset (Fin n)) i j t = mult n i j t := rfl

/-- The block coefficient `β^t_{i,j,k}`, by (7') of Schrijver's paper. -/
def beta (n i j k t : ℕ) : ℤ :=
  ∑ r ∈ range (t + 1),
    (-1 : ℤ) ^ (k + t + r) * (k.choose (t - r) : ℤ) * (mult (n - 2 * k) (i - k) (j - k) r : ℤ)

/-- The alternating binomial sum `beta` is built from, abstracted over what it
weighs.

Keeping `m` abstract separates the arithmetic of the recurrence -- Pascal and the
signs -- from the combinatorics that supplies the counts. The three lemmas below
are the entire content of the induction on `P`. -/
def betaAux (k t : ℕ) (m : ℕ → ℤ) : ℤ :=
  ∑ r ∈ range (t + 1), (-1 : ℤ) ^ (k + t + r) * (k.choose (t - r) : ℤ) * m r

/-- With no pairs, only `r = t` survives: `C(0, t - r)` vanishes elsewhere. -/
theorem betaAux_zero (t : ℕ) (m : ℕ → ℤ) : betaAux 0 t m = m t := by
  rw [betaAux, Finset.sum_eq_single t]
  · simp
  · intro r hr hrt
    have : t - r ≠ 0 := by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      omega
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero this)]
  · intro h
    simp at h

/-- At `t = 0` the two agreeing traces are impossible, so a pair only flips the
sign. Stated apart from `betaAux_step` because `t - 1` on `ℕ` would silently
readmit them. -/
theorem betaAux_zero_step (k : ℕ) (m : ℕ → ℤ) : betaAux (k + 1) 0 m = -betaAux k 0 m := by
  simp [betaAux, pow_succ]

/-- The recurrence the peeling produces, on the coefficient side. This is Pascal:
`C(k+1, t+1-r) = C(k, t-r) + C(k, t+1-r)`, with the `r = t+1` term split off
because the two sums do not range over the same set. -/
theorem betaAux_step (k t : ℕ) (m : ℕ → ℤ) :
    betaAux (k + 1) (t + 1) m = betaAux k t m - betaAux k (t + 1) m := by
  have hsum : ∑ r ∈ range (t + 1),
        ((-1 : ℤ) ^ (k + 1 + (t + 1) + r) * (((k + 1).choose (t + 1 - r) : ℤ)) * m r)
      = ∑ r ∈ range (t + 1),
        ((-1 : ℤ) ^ (k + t + r) * ((k.choose (t - r) : ℤ)) * m r
          - (-1 : ℤ) ^ (k + (t + 1) + r) * ((k.choose (t + 1 - r) : ℤ)) * m r) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrt : r ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hsub : t + 1 - r = (t - r) + 1 := by omega
    have e1 : (-1 : ℤ) ^ (k + 1 + (t + 1) + r) = (-1 : ℤ) ^ (k + t + r) := by
      rw [show k + 1 + (t + 1) + r = (k + t + r) + 2 by ring, pow_add]; ring
    have e2 : (-1 : ℤ) ^ (k + (t + 1) + r) = -((-1 : ℤ) ^ (k + t + r)) := by
      rw [show k + (t + 1) + r = (k + t + r) + 1 by ring, pow_succ]; ring
    rw [e1, e2, hsub, Nat.choose_succ_succ]
    push_cast
    ring
  have hlast : (-1 : ℤ) ^ (k + 1 + (t + 1) + (t + 1)) * (((k + 1).choose (t + 1 - (t + 1)) : ℤ))
        * m (t + 1)
      = -((-1 : ℤ) ^ (k + (t + 1) + (t + 1)) * ((k.choose (t + 1 - (t + 1)) : ℤ)) * m (t + 1)) := by
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [show k + 1 + (t + 1) + (t + 1) = (k + (t + 1) + (t + 1)) + 1 by ring, pow_succ]
    ring
  simp only [betaAux]
  rw [Finset.sum_range_succ (n := t + 1)
        (f := fun r => (-1 : ℤ) ^ (k + 1 + (t + 1) + r) * (((k + 1).choose (t + 1 - r) : ℤ)) * m r),
      Finset.sum_range_succ (n := t + 1)
        (f := fun r => (-1 : ℤ) ^ (k + (t + 1) + r) * ((k.choose (t + 1 - r) : ℤ)) * m r),
      hsum, Finset.sum_sub_distrib, hlast]
  ring

/-- `beta` relativised to a set `F` of free coordinates, so that no index is a
truncated subtraction and no type changes. Tying this back to `beta` is a
separate step, and it is the one that carries the change of type. -/
def betaOn (F : Finset (Fin n)) (i j k t : ℕ) : ℤ :=
  betaAux k t fun r => (multOn F i j r : ℤ)

/-- The weight of a subset attached to a family of coordinate pairs. It is `0`
unless `v` contains exactly one coordinate of each pair. -/
def cc (P : Finset (Fin n × Fin n)) (v : Finset (Fin n)) : ℤ :=
  ∏ p ∈ P, ((if p.1 ∈ v then (1 : ℤ) else 0) - (if p.2 ∈ v then (1 : ℤ) else 0))

@[simp] theorem cc_empty (v : Finset (Fin n)) : cc (∅ : Finset (Fin n × Fin n)) v = 1 := by
  simp [cc]

theorem cc_insert {p : Fin n × Fin n} {P : Finset (Fin n × Fin n)} (hp : p ∉ P)
    (v : Finset (Fin n)) :
    cc (insert p P) v
      = ((if p.1 ∈ v then (1 : ℤ) else 0) - (if p.2 ∈ v then (1 : ℤ) else 0)) * cc P v := by
  simp [cc, Finset.prod_insert hp]

/-- The coordinates a family of pairs occupies. -/
def coords (P : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  P.image Prod.fst ∪ P.image Prod.snd

/-- `cc P v` vanishes exactly when some pair contributes both its coordinates to
`v` or neither. This is why the block index runs over `k ≤ i ≤ n - k` rather than
`0 ≤ i ≤ n`: a non-zero weight forces `v` to meet every pair. -/
theorem cc_eq_zero_iff (P : Finset (Fin n × Fin n)) (v : Finset (Fin n)) :
    cc P v = 0 ↔ ∃ p ∈ P, (p.1 ∈ v ↔ p.2 ∈ v) := by
  rw [cc, Finset.prod_eq_zero_iff]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  by_cases h1 : p.1 ∈ v <;> by_cases h2 : p.2 ∈ v <;> simp [h1, h2]

/-- A coordinate outside every pair does not change the weight.

The four traces of the peeling insert `a` and/or `b` into `v`, and `cc P` has to
be blind to that: only the pairs of `P` may see it. This is where the hypothesis
that the pairs are coordinate-disjoint gets spent. -/
theorem cc_insert_of_notMem_coords {P : Finset (Fin n × Fin n)} {a : Fin n}
    (ha : a ∉ coords P) (v : Finset (Fin n)) :
    cc P (insert a v) = cc P v := by
  simp only [coords, Finset.mem_union, Finset.mem_image, not_or, not_exists] at ha
  obtain ⟨h1, h2⟩ := ha
  simp only [cc]
  refine Finset.prod_congr rfl fun p hp => ?_
  have e1 : p.1 ≠ a := fun h => h1 p ⟨hp, h⟩
  have e2 : p.2 ≠ a := fun h => h2 p ⟨hp, h⟩
  simp [Finset.mem_insert, e1, e2]

/-- The pairs of `P` are non-degenerate and no two of them share a coordinate.

Stated as `PairwiseDisjoint` rather than by hand: that is exactly the hypothesis
`Finset.card_biUnion` wants, so `card_coords` below is a corollary rather than a
bridge. -/
def DisjointPairs (P : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ P, p.1 ≠ p.2) ∧
    (P : Set (Fin n × Fin n)).PairwiseDisjoint fun p => ({p.1, p.2} : Finset (Fin n))

theorem coords_eq_biUnion (P : Finset (Fin n × Fin n)) :
    coords P = P.biUnion fun p => ({p.1, p.2} : Finset (Fin n)) := by
  ext a
  simp only [coords, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, hp, Or.inl rfl⟩
    · exact ⟨p, hp, Or.inr rfl⟩
  · rintro ⟨p, hp, (rfl | rfl)⟩
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩

/-- Inserting a pair adds exactly its two coordinates. Proved through
`coords_eq_biUnion` rather than by hand: `biUnion_insert` does the work and
avoids unpicking nested existentials. -/
theorem coords_insert (p : Fin n × Fin n) (P : Finset (Fin n × Fin n)) :
    coords (insert p P) = insert p.1 (insert p.2 (coords P)) := by
  rw [coords_eq_biUnion, coords_eq_biUnion, Finset.biUnion_insert]
  simp [Finset.insert_union, Finset.singleton_union]

/-- `k` disjoint pairs occupy `2k` coordinates. This is the readable form of
`DisjointPairs`; the definition is the one the proofs consume. -/
theorem DisjointPairs.card_coords {P : Finset (Fin n × Fin n)} (hP : DisjointPairs P) :
    (coords P).card = 2 * P.card := by
  rw [coords_eq_biUnion, Finset.card_biUnion hP.2,
    Finset.sum_congr rfl fun p hp => Finset.card_pair (hP.1 p hp)]
  simp [mul_comm]

theorem DisjointPairs.subset {P Q : Finset (Fin n × Fin n)} (hQ : DisjointPairs Q)
    (h : P ⊆ Q) : DisjointPairs P :=
  ⟨fun p hp => hQ.1 p (h hp), hQ.2.subset (Finset.coe_subset.2 h)⟩

theorem DisjointPairs.of_insert {p : Fin n × Fin n} {P : Finset (Fin n × Fin n)}
    (hP : DisjointPairs (insert p P)) : DisjointPairs P :=
  hP.subset (Finset.subset_insert p P)

theorem DisjointPairs.ne {a b : Fin n} {P : Finset (Fin n × Fin n)}
    (hP : DisjointPairs (insert (a, b) P)) : a ≠ b :=
  hP.1 (a, b) (Finset.mem_insert_self _ _)

/-- The coordinates of a freshly inserted pair are new. This is the hypothesis
`gramOn_insert_pair` consumes, extracted from `DisjointPairs` once. -/
theorem DisjointPairs.notMem_coords {a b : Fin n} {P : Finset (Fin n × Fin n)}
    (hP : DisjointPairs (insert (a, b) P)) (hab : (a, b) ∉ P) :
    a ∉ coords P ∧ b ∉ coords P := by
  have key : ∀ c : Fin n, (c = a ∨ c = b) → c ∉ coords P := by
    intro c hc hmem
    rw [coords_eq_biUnion, Finset.mem_biUnion] at hmem
    obtain ⟨q, hq, hcq⟩ := hmem
    have hne : (a, b) ≠ q := fun h => hab (h ▸ hq)
    have hd := hP.2 (by simp) (by simp [hq]) hne
    have h1 : c ∈ ({(a, b).1, (a, b).2} : Finset (Fin n)) := by
      rcases hc with rfl | rfl <;> simp
    exact (Finset.disjoint_left.1 hd h1) hcq
  exact ⟨key a (Or.inl rfl), key b (Or.inr rfl)⟩

/-- The left side of the Gram identity, over a ground set `G`.

`G` is the coordinates still in play: the paired ones, `coords P`, together with
the free ones. Peeling a pair keeps `P` inside `G` and shrinks both at once,
which is what makes the recurrence `gramOn_insert` below close. -/
def gramOn (G : Finset (Fin n)) (P : Finset (Fin n × Fin n)) (i j t : ℕ) : ℤ :=
  ∑ q ∈ multOnFinset G i j t, cc P q.1 * cc P q.2

/-- The left side of the Gram identity. -/
def gram (P : Finset (Fin n × Fin n)) (i j t : ℕ) : ℤ :=
  gramOn (univ : Finset (Fin n)) P i j t

theorem gramOn_empty (G : Finset (Fin n)) (i j t : ℕ) :
    gramOn G (∅ : Finset (Fin n × Fin n)) i j t = (multOn G i j t : ℤ) := by
  simp [gramOn, multOn]

theorem gram_empty (i j t : ℕ) :
    gram (∅ : Finset (Fin n × Fin n)) i j t = (mult n i j t : ℤ) := by
  simp [gram, gramOn_empty]

/-- `gramOn` as a sum over *all* subsets of `G`, the three constraints carried by
an `if`.

This is the form the peeling acts on. `Finset.sum_powerset_insert` splits a sum
over `powerset (insert a G)` with no side condition, whereas `powersetCard` would
raise a disjointness and an injectivity obligation at each of the four steps of a
pair. Here the cardinality bookkeeping moves into the `if`, where
`card_insert_of_notMem` discharges it. -/
theorem gramOn_eq_sum_powerset (G : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (i j t : ℕ) :
    gramOn G P i j t
      = ∑ v ∈ G.powerset, ∑ w ∈ G.powerset,
          if v.card = i ∧ w.card = j ∧ (v ∩ w).card = t then cc P v * cc P w else 0 := by
  rw [gramOn, multOnFinset]
  simp only [Finset.sum_filter, powersetCard_eq_filter]
  rw [Finset.sum_product]
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v.card = i
  · simp only [hv, true_and, if_true]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w.card = j <;> simp [hw]
  · simp [hv]

/-- Peeling one pair off the Gram sum.

Of the sixteen traces of `(v, w)` on `{a, b}`, twelve die: the factor
`[a ∈ v] - [b ∈ v]` of `cc` vanishes unless `v` takes exactly one of the two. The
four survivors are `(a,a)`, `(a,b)`, `(b,a)`, `(b,b)`, with signs `+, -, -, +`.
The two agreeing ones raise `|v ∩ w|` by one, the two disagreeing ones leave it
alone, which is where the two different values of `t` on the right come from. -/
theorem gramOn_insert_pair {G : Finset (Fin n)} {a b : Fin n} {P : Finset (Fin n × Fin n)}
    (hab : a ≠ b) (ha : a ∉ G) (hb : b ∉ G) (hP : coords P ⊆ G) (hp : (a, b) ∉ P)
    (i j t : ℕ) :
    gramOn (insert a (insert b G)) (insert (a, b) P) (i + 1) (j + 1) (t + 1)
      = 2 * gramOn G P i j t - 2 * gramOn G P i j (t + 1) := by
  have haP : a ∉ coords P := fun h => ha (hP h)
  have hbP : b ∉ coords P := fun h => hb (hP h)
  simp only [gramOn_eq_sum_powerset, sum_powerset_insert_pair (M := ℤ) hab ha hb]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hav : a ∉ v := fun h => ha (Finset.mem_powerset.1 hv h)
  have hbv : b ∉ v := fun h => hb (Finset.mem_powerset.1 hv h)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- The four traces of `v` each carry their own sum over `w`; regroup them into
  -- one before descending, or `sum_congr` has nothing to match against.
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  have haw : a ∉ w := fun h => ha (Finset.mem_powerset.1 hw h)
  have hbw : b ∉ w := fun h => hb (Finset.mem_powerset.1 hw h)
  have habv : a ∉ insert b v := by simp [hab, hav]
  have habw : a ∉ insert b w := by simp [hab, haw]
  simp [cc_insert hp, cc_insert_of_notMem_coords haP, cc_insert_of_notMem_coords hbP,
    Finset.mem_insert, hav, hbv, haw, hbw, hab, hab.symm, habv, habw,
    Finset.card_insert_of_notMem, Finset.insert_inter_of_notMem,
    Finset.inter_insert_of_notMem, Finset.inter_insert_of_mem]
  -- Four surviving traces, signs `+ - - +`: the two agreeing ones sit at
  -- `|v ∩ w| = t`, the two disagreeing ones at `t + 1`.
  split_ifs <;> ring

/-- Peeling one pair, at `t = 0`.

The two agreeing traces put a shared coordinate into `v ∩ w`, so they would need
`|v ∩ w| = 0` with that coordinate already in it. They are empty, and only the
two disagreeing traces survive. Stating `gramOn_insert_pair` at `t + 1` and this
case apart is what keeps `t - 1` out of the statement: truncated subtraction on
`ℕ` would silently readmit the agreeing terms here. -/
theorem gramOn_insert_pair_zero {G : Finset (Fin n)} {a b : Fin n}
    {P : Finset (Fin n × Fin n)} (hab : a ≠ b) (ha : a ∉ G) (hb : b ∉ G)
    (hP : coords P ⊆ G) (hp : (a, b) ∉ P) (i j : ℕ) :
    gramOn (insert a (insert b G)) (insert (a, b) P) (i + 1) (j + 1) 0
      = -2 * gramOn G P i j 0 := by
  have haP : a ∉ coords P := fun h => ha (hP h)
  have hbP : b ∉ coords P := fun h => hb (hP h)
  simp only [gramOn_eq_sum_powerset, sum_powerset_insert_pair (M := ℤ) hab ha hb]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hav : a ∉ v := fun h => ha (Finset.mem_powerset.1 hv h)
  have hbv : b ∉ v := fun h => hb (Finset.mem_powerset.1 hv h)
  rw [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  have haw : a ∉ w := fun h => ha (Finset.mem_powerset.1 hw h)
  have hbw : b ∉ w := fun h => hb (Finset.mem_powerset.1 hw h)
  have habv : a ∉ insert b v := by simp [hab, hav]
  have habw : a ∉ insert b w := by simp [hab, haw]
  simp [cc_insert hp, cc_insert_of_notMem_coords haP, cc_insert_of_notMem_coords hbP,
    Finset.mem_insert, hav, hbv, haw, hbw, hab, hab.symm, habv, habw,
    Finset.card_insert_of_notMem, Finset.insert_inter_of_notMem,
    Finset.inter_insert_of_notMem, Finset.inter_insert_of_mem]
  split_ifs <;> ring

/-- The Gram sum in closed form, over a ground set split into free coordinates
`F` and the coordinates of `P`.

Parametrised by the *free* sizes `i` and `j` rather than by `i - k`: that keeps
every index honest, where `beta` pays for the same statement with truncated
subtraction and a change of type. `F` stays fixed throughout the induction --
peeling a pair shrinks `coords P`, not `F`.

This is the induction step of the Gram identity of `THEOREM1.md` §4 joined to
its base case. What it does *not* do is tie `betaOn` back to `beta`; that
recollement is still open. -/
theorem gramOn_eq_pow_mul_betaOn (F : Finset (Fin n)) (i j : ℕ) :
    ∀ (P : Finset (Fin n × Fin n)), DisjointPairs P → Disjoint F (coords P) →
    ∀ t, gramOn (F ∪ coords P) P (i + P.card) (j + P.card) t
      = 2 ^ P.card * betaOn F i j P.card t := by
  intro P
  simp only [betaOn]
  induction P using Finset.induction_on with
  | empty =>
      intro _ _ t
      simp [coords, gramOn_empty, betaAux_zero]
  | @insert p P hp ih =>
      obtain ⟨a, b⟩ := p
      intro hPd hFP t
      have hab : a ≠ b := hPd.ne
      have hsub : DisjointPairs P := hPd.of_insert
      obtain ⟨haP, hbP⟩ := hPd.notMem_coords hp
      rw [coords_insert] at hFP
      simp only [Finset.disjoint_insert_right] at hFP
      obtain ⟨haF, hbF, hFP'⟩ := hFP
      have hG : F ∪ coords (insert (a, b) P) = insert a (insert b (F ∪ coords P)) := by
        rw [coords_insert, Finset.union_insert, Finset.union_insert]
      have ha : a ∉ F ∪ coords P := by simp [haF, haP]
      have hb : b ∉ F ∪ coords P := by simp [hbF, hbP]
      have hPG : coords P ⊆ F ∪ coords P := Finset.subset_union_right
      have hcard : (insert (a, b) P).card = P.card + 1 := Finset.card_insert_of_notMem hp
      rw [hG, hcard]
      cases t with
      | zero =>
          rw [show i + (P.card + 1) = (i + P.card) + 1 by ring,
            show j + (P.card + 1) = (j + P.card) + 1 by ring,
            gramOn_insert_pair_zero hab ha hb hPG hp, ih hsub hFP' 0, betaAux_zero_step]
          ring
      | succ t' =>
          rw [show i + (P.card + 1) = (i + P.card) + 1 by ring,
            show j + (P.card + 1) = (j + P.card) + 1 by ring,
            gramOn_insert_pair hab ha hb hPG hp, ih hsub hFP' t', ih hsub hFP' (t' + 1),
            betaAux_step]
          ring

/-- The relativised count is the absolute one for the right `n`.

This is where the change of type lives. `multOn` counts inside a `Finset` of
coordinates; `mult` counts inside `Fin m`. Transporting along
`Finset.orderEmbOfFin` is what `multOn` was introduced to postpone, and this
lemma is the single place that pays for it. `F` is never rewritten: the
embedding's type mentions `#F`, so abstracting `F` would break the motive. -/
theorem multOn_card (F : Finset (Fin n)) (i j r : ℕ) :
    multOn F i j r = mult F.card i j r := by
  classical
  rw [multOn, mult, multFinset]
  set e := (F.orderEmbOfFin rfl).toEmbedding with he
  have hFe : Finset.map e univ = F := Finset.map_orderEmbOfFin_univ F rfl
  have hmem : ∀ v : Finset (Fin F.card), Finset.map e v ⊆ F := by
    intro v x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem F rfl a
  have hlift : ∀ v : Finset (Fin n), v ⊆ F → ∃ u : Finset (Fin F.card), Finset.map e u = v := by
    intro v hv
    have hv' : v ⊆ Finset.image e univ := by rw [← Finset.map_eq_image, hFe]; exact hv
    obtain ⟨u, -, hu⟩ := Finset.subset_image_iff.1 hv'
    exact ⟨u, by rw [Finset.map_eq_image]; exact hu⟩
  refine (Finset.card_bij
      (fun q (_ : q ∈ multOnFinset (univ : Finset (Fin F.card)) i j r) =>
        (q.1.map e, q.2.map e)) ?_ ?_ ?_).symm
  · rintro ⟨v, w⟩ hq
    simp only [multOnFinset, Finset.mem_filter, Finset.mem_product,
      Finset.mem_powersetCard] at hq ⊢
    obtain ⟨⟨⟨-, hv⟩, ⟨-, hw⟩⟩, hvw⟩ := hq
    exact ⟨⟨⟨hmem v, by rw [Finset.card_map]; exact hv⟩,
      ⟨hmem w, by rw [Finset.card_map]; exact hw⟩⟩,
      by rw [← Finset.map_inter, Finset.card_map]; exact hvw⟩
  · rintro ⟨v, w⟩ - ⟨v', w'⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Finset.map_injective e h.1) (Finset.map_injective e h.2)
  · rintro ⟨v, w⟩ hq
    simp only [multOnFinset, Finset.mem_filter, Finset.mem_product,
      Finset.mem_powersetCard] at hq
    obtain ⟨⟨⟨hvF, hv⟩, ⟨hwF, hw⟩⟩, hvw⟩ := hq
    obtain ⟨u, rfl⟩ := hlift v hvF
    obtain ⟨z, rfl⟩ := hlift w hwF
    refine ⟨(u, z), ?_, rfl⟩
    simp only [multOnFinset, Finset.mem_filter, Finset.mem_product,
      Finset.mem_powersetCard]
    rw [Finset.card_map] at hv hw
    rw [← Finset.map_inter, Finset.card_map] at hvw
    exact ⟨⟨⟨Finset.subset_univ u, hv⟩, ⟨Finset.subset_univ z, hw⟩⟩, hvw⟩

/-- The bridge from the relativised coefficient to `beta` as the paper defines
it. The truncated subtractions `i - k` and `j - k` appear here and nowhere
earlier: `betaOn` is stated in free sizes, `beta` in absolute ones. -/
theorem betaOn_eq_beta (F : Finset (Fin n)) (i j k t : ℕ) (hF : F.card = n - 2 * k) :
    betaOn F (i - k) (j - k) k t = beta n i j k t := by
  simp only [betaOn, beta, betaAux]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [multOn_card, hF]

/-- The Gram identity in the paper's notation, over a ground set split into free
coordinates `F` and the coordinates of `P`. -/
theorem gramOn_eq_pow_mul_beta (F : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (hP : DisjointPairs P) (hFP : Disjoint F (coords P))
    (hF : F.card = n - 2 * P.card) (i j t : ℕ) :
    gramOn (F ∪ coords P) P (i + P.card) (j + P.card) t
      = 2 ^ P.card * beta n (i + P.card) (j + P.card) P.card t := by
  rw [gramOn_eq_pow_mul_betaOn F i j P hP hFP t, ← betaOn_eq_beta F _ _ P.card t hF]
  simp

/-- Over the whole cube, given a witness for the free coordinates. -/
theorem gram_eq_pow_mul_beta_of_card (F : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (hP : DisjointPairs P) (hFP : Disjoint F (coords P))
    (hF : F.card = n - 2 * P.card) (hk : 2 * P.card ≤ n) (i j t : ℕ) :
    gram P (i + P.card) (j + P.card) t
      = 2 ^ P.card * beta n (i + P.card) (j + P.card) P.card t := by
  have hcard : (F ∪ coords P).card = n := by
    rw [Finset.card_union_of_disjoint hFP, hF, hP.card_coords]
    omega
  have huniv : F ∪ coords P = (univ : Finset (Fin n)) :=
    Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
  rw [gram, ← huniv]
  exact gramOn_eq_pow_mul_beta F P hP hFP hF i j t

/-- Schrijver's Gram identity, §4 of `THEOREM1.md`, over the whole cube:

    ∑_{|v| = i+k, |w| = j+k, |v ∧ w| = t} c(v) c(w) = 2^k · β^t_{i+k, j+k, k}

for `k = |P|` pairwise coordinate-disjoint pairs. No witness to supply: the free
coordinates are the complement of the paired ones. -/
theorem gram_eq_pow_mul_beta (P : Finset (Fin n × Fin n))
    (hP : DisjointPairs P) (hk : 2 * P.card ≤ n) (i j t : ℕ) :
    gram P (i + P.card) (j + P.card) t
      = 2 ^ P.card * beta n (i + P.card) (j + P.card) P.card t := by
  have hFP : Disjoint ((univ : Finset (Fin n)) \ coords P) (coords P) := Finset.sdiff_disjoint
  have hF : ((univ : Finset (Fin n)) \ coords P).card = n - 2 * P.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, hP.card_coords, Finset.card_univ,
      Fintype.card_fin]
  exact gram_eq_pow_mul_beta_of_card _ P hP hFP hF hk i j t

end Delsarte.Hamming
