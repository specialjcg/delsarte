/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-!
# Schrijver's block coefficients and the identity their positivity comes from

Issue #45. The blocks (19) of Schrijver's semidefinite program are positive for
every code; `Delsarte/Hamming/THEOREM1.md` is the argument on paper, and this
file is the part of it that is pure combinatorics.

Fix `k` disjoint pairs of coordinates and weight a subset `v` by

`cc P v = ∏_{(a,b) ∈ P} ([a ∈ v] - [b ∈ v])`,

which vanishes unless `v` meets every pair exactly once. The identity to prove is

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

end Delsarte.Hamming
