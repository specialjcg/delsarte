/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.Positivity
import Delsarte.Hamming.Triples

/-!
# The triple counts are the orbit sums of the matrix of (19)

Issue #45. `Delsarte/Hamming/Positivity.lean` builds the matrix of (19) indexed by
*words*, `Delsarte/Hamming/Triples.lean` counts *triples of codewords*, and until
this file nothing said they were about the same numbers. They are:

    gramMat C C v w = #{ z ∈ C : z + v ∈ C, z + w ∈ C },

so putting `X = z`, `Y = z + v`, `Z = z + w` turns a pair `(v, w)` together with a
translation into a triple of codewords, and the three statistics match up —
`|X △ Y| = |v|`, `|X △ Z| = |w|`, `|(X △ Y) ∩ (X △ Z)| = |v ∧ w|`. Summing over the
orbit therefore gives `λ^t_{i,j}`.

`tools/check_orbit.py` has measured exactly this since `4765c10`: its
`orbit_average` sums `M` over the orbit and divides by `mult`. That script is the
numerical evidence; `lambdaT_eq_orbit_sum` below is the statement itself.

What the statement does *not* do is pin `interDist` down. Both of its sides are
written with the same `interDist`, and the fibration never looks inside it, so
replacing it by any other function of the two differences leaves the theorem true
and the proof below unchanged. A definition that had drifted from
`|(X △ Y) ∩ (X △ Z)|` would prove this same theorem about the wrong numbers, and
nothing in Lean would notice. `tools/check_triples.py` is what closes that gap: it
recomputes both sides from bitmask arithmetic, importing nothing from here or from
the generator, and its two guards corrupt the orbit side *only* — corrupting both
at once would pass vacuously, for exactly the reason just given.

## Why this is the first brick of Theorem 1

`THEOREM1.md` §6 gives a route to §2 that never names the `Sₙ`-invariant matrix
`M̃`: average the *vector* instead, so that

    Σ_σ (P_σ u_i)ᵀ M (P_σ u_j) = n! · Σ_t x^t_{i,j} · 2^k · β^t_{i,j,k}.

Both halves of that are already proved — `sum_smul_quadForm_nonneg` for the left,
`gram_eq_pow_mul_beta` for the inner sum. But `x^t_{i,j}` lives in `Triples.lean`
and `M` lives in `Positivity.lean`, so the identity could not even be *stated*
across the two. This file is what makes it statable. That document predates
`Triples.lean` and places the missing piece elsewhere; it is stale on this point.

## What this file does not do

Everything else. The orbit constancy of `Σ_σ M[σv,σw]`, the assembly of §3, and
step 4 — the bridge from a quadratic form on words to `Data.blockForm`, which is a
form on encoded lists — are all untouched. `hblocks` still stands and no bound
stops being conditional.

There is also a type gap this file does not close: `gram` in
`Delsarte/Hamming/Terwilliger.lean` sums over `Finset (Fin n)` while `gramMat`
sums over `Word n 2`. Nothing below needs the transport, but the §6 identity will.

## A note on tactics

Nothing below unfolds `orbit` or `tripleSet` with `simp only [orbit]`. Doing that
rewrites the `DecidablePred` instance out from under `Finset.mem_filter`, which
then fails to apply and leaves membership as a raw `Quot.lift`; the two
`mem_orbit` / `mem_tripleSet` lemmas exist so that unfolding happens once, by
term-level unification, where defeq is tolerated.

## Negative controls

On `C = {00, 11}` the kernel decides the counts. They are stated over `ℕ`: the
`ℚ`-valued form does not reduce, because `instDecidableEqRat` gets stuck before
the `Multiset.Pi` enumeration of the cube is consumed.
-/

namespace Delsarte.Hamming

open Finset Delsarte

variable {n : ℕ}

/-! ## Translation invariance

Both statistics count coordinates where words differ, and `z + ·` is injective in
each coordinate, so translating every argument changes nothing. -/

/-- Cancellation in the alphabet, decided rather than derived, so that no instance
has to be matched syntactically later. -/
theorem fin2_add_cancel : ∀ a b c : Fin 2, a + b = a + c → b = c := by decide

/-- Translation preserves the Hamming distance. This is mathlib's
`hammingDist_comp` at the injection `z i + ·`; the repository does not need a
translation lemma of its own. -/
theorem hammingDist_translate (z x y : Word n 2) :
    hammingDist (z + x) (z + y) = hammingDist x y :=
  hammingDist_comp (fun i => (z i + ·)) (fun _ _ _ h => fin2_add_cancel _ _ _ h)

/-- Translation preserves the triple overlap, for the same reason. `interDist` is
this repository's own definition, so there is no mathlib lemma to borrow. -/
theorem interDist_translate (z X Y Z : Word n 2) :
    interDist (z + X) (z + Y) (z + Z) = interDist X Y Z := by
  classical
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun e => h1 (congrArg (fun u : Fin 2 => z c + u) e),
      fun e => h2 (congrArg (fun u : Fin 2 => z c + u) e)⟩
  · intro h
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun e => h1 (fin2_add_cancel _ _ _ e), fun e => h2 (fin2_add_cancel _ _ _ e)⟩

/-- **A distance is a weight.** Translating by `X` sends the pair `(X, Y)` to
`(0, X + Y)`; characteristic two is what makes that translation its own inverse. -/
theorem hammingDist_eq_weight (X Y : Word n 2) :
    hammingDist X Y = hammingDist 0 (X + Y) := by
  rw [← hammingDist_translate X 0 (X + Y), add_zero, ← add_assoc, word_add_self, zero_add]

/-- The triple overlap depends only on the two differences. -/
theorem interDist_eq_weight (X Y Z : Word n 2) :
    interDist X Y Z = interDist 0 (X + Y) (X + Z) := by
  rw [← interDist_translate X 0 (X + Y) (X + Z), add_zero, ← add_assoc, word_add_self,
    zero_add, ← add_assoc, word_add_self, zero_add]

/-! ## The orbit, and the set `lambdaT` counts -/

/-- The orbit `(i, j, t)`: pairs of words with prescribed weights and overlap. No
new statistic is defined — `hammingDist 0 v` is the Hamming weight of `v` and
`interDist 0 v w` the size of the overlap of the two supports. -/
def orbit (n i j t : ℕ) : Finset (Word n 2 × Word n 2) :=
  univ.filter fun p =>
    hammingDist 0 p.1 = i ∧ hammingDist 0 p.2 = j ∧ interDist 0 p.1 p.2 = t

/-- The set whose cardinality is `lambdaT`, named so that it can be fibred. -/
def tripleSet (C : Code n 2) (i j t : ℕ) : Finset (Word n 2 × Word n 2 × Word n 2) :=
  (C ×ˢ C ×ˢ C).filter fun q =>
    hammingDist q.1 q.2.1 = i ∧ hammingDist q.1 q.2.2 = j ∧ interDist q.1 q.2.1 q.2.2 = t

theorem lambdaT_eq_card_tripleSet (C : Code n 2) (i j t : ℕ) :
    lambdaT C i j t = (tripleSet C i j t).card := rfl

/-- Membership in the orbit, unfolded once. -/
theorem mem_orbit {i j t : ℕ} {p : Word n 2 × Word n 2} :
    p ∈ orbit n i j t ↔
      hammingDist 0 p.1 = i ∧ hammingDist 0 p.2 = j ∧ interDist 0 p.1 p.2 = t :=
  ⟨fun h => (Finset.mem_filter.mp h).2,
   fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- Membership in the triple set, unfolded once. -/
theorem mem_tripleSet {C : Code n 2} {i j t : ℕ} {q : Word n 2 × Word n 2 × Word n 2} :
    q ∈ tripleSet C i j t ↔
      (q.1 ∈ C ∧ q.2.1 ∈ C ∧ q.2.2 ∈ C) ∧
        (hammingDist q.1 q.2.1 = i ∧ hammingDist q.1 q.2.2 = j ∧
          interDist q.1 q.2.1 q.2.2 = t) := by
  constructor
  · intro h
    obtain ⟨hm, hs⟩ := Finset.mem_filter.mp h
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hm
    obtain ⟨h2a, h2b⟩ := Finset.mem_product.mp h2
    exact ⟨⟨h1, h2a, h2b⟩, hs⟩
  · rintro ⟨⟨h1, h2, h3⟩, hs⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨h1, Finset.mem_product.mpr ⟨h2, h3⟩⟩, hs⟩

/-! ## The bridge -/

/-- The matrix of (19) counts translations, as §1 of `THEOREM1.md` says it does.
This is the only place the `ℚ`-valued form is turned back into a count. -/
theorem gramMat_eq_card (C : Code n 2) (v w : Word n 2) :
    gramMat C C v w = ((C.filter fun z => z + v ∈ C ∧ z + w ∈ C).card : ℚ) := by
  classical
  rw [gramMat, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h1 : z + v ∈ C <;> by_cases h2 : z + w ∈ C <;> simp [indic, h1, h2]

/-- **The fibration.** Sending a triple to its two differences lands in the orbit,
and the fibre over `(v, w)` is the set of translations the matrix entry counts. -/
theorem card_tripleSet_eq_sum (C : Code n 2) (i j t : ℕ) :
    (tripleSet C i j t).card
      = ∑ p ∈ orbit n i j t, (C.filter fun z => z + p.1 ∈ C ∧ z + p.2 ∈ C).card := by
  classical
  refine (Finset.card_eq_sum_card_fiberwise
    (f := fun q : Word n 2 × Word n 2 × Word n 2 => (q.1 + q.2.1, q.1 + q.2.2))
    (t := orbit n i j t) ?_).trans ?_
  · rintro ⟨X, Y, Z⟩ hq
    obtain ⟨_, hi, hj, ht⟩ := mem_tripleSet.mp hq
    refine mem_orbit.mpr ⟨?_, ?_, ?_⟩
    · change hammingDist 0 (X + Y) = i
      rw [← hammingDist_eq_weight]; exact hi
    · change hammingDist 0 (X + Z) = j
      rw [← hammingDist_eq_weight]; exact hj
    · change interDist 0 (X + Y) (X + Z) = t
      rw [← interDist_eq_weight]; exact ht
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨v, w⟩ := p
  obtain ⟨hv, hw, hvw⟩ := mem_orbit.mp hp
  refine Finset.card_bij' (fun q _ => q.1) (fun z _ => (z, z + v, z + w)) ?_ ?_ ?_ ?_
  · rintro ⟨X, Y, Z⟩ hq
    obtain ⟨hmem, hf⟩ := Finset.mem_filter.mp hq
    obtain ⟨⟨hX, hY, hZ⟩, _⟩ := mem_tripleSet.mp hmem
    have e1 : X + Y = v := congrArg Prod.fst hf
    have e2 : X + Z = w := congrArg Prod.snd hf
    refine Finset.mem_filter.mpr ⟨hX, ?_, ?_⟩
    · rw [← e1, ← add_assoc, word_add_self, zero_add]; exact hY
    · rw [← e2, ← add_assoc, word_add_self, zero_add]; exact hZ
  · intro z hz
    obtain ⟨hzC, h1, h2⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨mem_tripleSet.mpr ⟨⟨hzC, h1, h2⟩, ?_, ?_, ?_⟩, ?_⟩
    · change hammingDist z (z + v) = i
      rw [hammingDist_eq_weight, ← add_assoc, word_add_self, zero_add]; exact hv
    · change hammingDist z (z + w) = j
      rw [hammingDist_eq_weight, ← add_assoc, word_add_self, zero_add]; exact hw
    · change interDist z (z + v) (z + w) = t
      rw [interDist_eq_weight, ← add_assoc, word_add_self, zero_add, ← add_assoc,
        word_add_self, zero_add]
      exact hvw
    · change (z + (z + v), z + (z + w)) = (v, w)
      rw [← add_assoc, word_add_self, zero_add, ← add_assoc, word_add_self, zero_add]
  · rintro ⟨X, Y, Z⟩ hq
    obtain ⟨_, hf⟩ := Finset.mem_filter.mp hq
    have e1 : X + Y = v := congrArg Prod.fst hf
    have e2 : X + Z = w := congrArg Prod.snd hf
    rw [← e1, ← e2, ← add_assoc, word_add_self, zero_add, ← add_assoc, word_add_self,
      zero_add]
  · intro z _
    rfl

/-- **The brick.** The triple count of `Delsarte/Hamming/Triples.lean` is the sum
of the matrix of (19) over the orbit. This is what makes `x^t_{i,j}` an orbit
average of `M` rather than an unrelated definition, and what `tools/check_orbit.py`
has been measuring numerically. -/
theorem lambdaT_eq_orbit_sum (C : Code n 2) (i j t : ℕ) :
    ∑ p ∈ orbit n i j t, gramMat C C p.1 p.2 = lambdaT C i j t := by
  classical
  rw [lambdaT_eq_card_tripleSet, card_tripleSet_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun p _ => gramMat_eq_card C p.1 p.2

/-! ## Negative controls

On `C = {00, 11}` the kernel decides the counts. -/

/-- The orbit is the set it is meant to be: weight one on both sides with full
overlap forces the two words equal, and there are two such words. -/
theorem orbit_control_card : (orbit 2 1 1 1).card = 2 := by decide

/-- **Negative control.** Weight one on both sides with *no* overlap forces the two
words distinct. A mistaken `interDist 0` would confuse this count with the
previous one; they happen to be equal here, so the next control is the sharp one. -/
theorem orbit_control_disjoint : (orbit 2 1 1 0).card = 2 := by decide

/-- **Negative control.** Weight two on both sides with overlap one is impossible
on two coordinates: two words of full weight are equal, so the overlap is two. -/
theorem orbit_control_empty : (orbit 2 2 2 1).card = 0 := by decide

/-- The triple count off the diagonal, decided here because
`Delsarte/Hamming/Triples.lean` decides `(2,0,0)`, `(2,2,1)` and `(1,0,0)` but not
this one. It is the other end of the next control. -/
theorem lambdaT_control_offdiag :
    lambdaT (n := 2) {![0, 0], ![1, 1]} 2 2 2 = 2 := by decide

/-- **The control that carries weight.** Off the diagonal `t = 0`, where
`lambdaT_diag` gives no independent reading, the fibred sum is decided on its own
and matches `lambdaT_control_offdiag` above. Both ends are computed without going
through `card_tripleSet_eq_sum`, so a translation lemma that dropped a coordinate
would make them disagree. -/
theorem orbit_sum_control_offdiag :
    ∑ p ∈ orbit 2 2 2 2,
        (({![0, 0], ![1, 1]} : Code 2 2).filter fun z =>
          z + p.1 ∈ ({![0, 0], ![1, 1]} : Code 2 2) ∧
            z + p.2 ∈ ({![0, 0], ![1, 1]} : Code 2 2)).card = 2 := by
  decide

end Delsarte.Hamming
