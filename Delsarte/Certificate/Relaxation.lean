/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.SDP.Sparse

/-!
# From a checked certificate to a bound on `A(n,2,d)`

The seven conditional bounds of `Delsarte/Certificate/Schrijver*.lean` had the
same proof written out seven times, differing only in `n`, `d` and the bound.
This file holds it once.

## Why the hypothesis is split

`Data.Feasible z` is a conjunction: every block form nonnegative (issue #45,
Schrijver's Theorem 1) and every row form nonnegative (issue #44, the constraints
(20)). Bundled behind a single `hrelax`, discharging one of the two would leave
the statement looking exactly as it did before -- the hypothesis is one opaque
term either way, and no reader could tell that half of it had become a theorem.

So the hypothesis is carried as three, tied together by a predicate `P C z` read
as *`z` is the vector of orbit averages of `C`*:

* `henc` -- every nonempty code of minimum distance `d` has such a `z`, and the
  objective reads its size back. This is the encoding, step 4 of
  `Delsarte/Hamming/THEOREM1.md` §5.
* `hblocks` -- such a `z` makes the blocks positive. **Issue #45.**
* `hrows` -- such a `z` satisfies the inequalities. **Issue #44.**

`P` is deliberately uninterpreted. `Delsarte/Hamming/Triples.lean`, where
`x^t_{i,j}` would be defined, does not exist yet, and nothing here should
pretend to know what the encoding is before it is written. When it is, `P` gets
instantiated and the three hypotheses become three separate obligations that can
fall one at a time.

## What this file does not do

It does not weaken anything. `A_le_of_relaxation` is the same implication the
seven theorems already had, and `enc_of_feasible`, `blocks_of_feasible` and
`rows_of_feasible` feed the old bundled hypothesis straight into it, so no cell
proves less than before. Splitting a hypothesis is bookkeeping; it makes partial
progress *visible*, it does not make any of it happen.
-/

namespace Delsarte.Certificate

open Delsarte.SDP.Sparse

variable {n d : ℕ} {D : Data} {C : Cert} {P : Code n 2 → (ℕ → ℚ) → Prop}

/-- **The old form still works.** Taking `P` to be feasibility itself, the bundled
hypothesis the seven cells used to carry discharges the three split ones, so no
cell proves less than before the split.

Stated as the three arguments `A_le_of_relaxation` wants rather than as one
conjunction, so that it can be fed to it directly; `blocks_of_feasible` and
`rows_of_feasible` are the second and third. -/
theorem enc_of_feasible
    (hrelax : ∀ K : Code n 2, K.Nonempty → MinDistAtLeast d K →
      ∃ z : ℕ → ℚ, D.Feasible z ∧ (K.card : ℚ) = 1 + D.objForm z) :
    ∀ K : Code n 2, K.Nonempty → MinDistAtLeast d K →
      ∃ z : ℕ → ℚ, D.Feasible z ∧ (K.card : ℚ) = 1 + D.objForm z :=
  hrelax

theorem blocks_of_feasible :
    ∀ _K : Code n 2, ∀ z, D.Feasible z → ∀ b w, 0 ≤ D.blockForm b z w :=
  fun _ _ hz => hz.1

theorem rows_of_feasible :
    ∀ _K : Code n 2, ∀ z, D.Feasible z → ∀ l, 0 ≤ D.rowForm l z :=
  fun _ _ hz => hz.2

/-- **The shared step.** A certificate that checks, a program that relaxes the code
problem, and a bound on the certified value give `A(n,2,d) ≤ N`.

The three hypotheses are the split described above; `hbnum` is the kernel-decided
comparison of each cell, and `hcheck` its `check_data`. -/
theorem A_le_of_relaxation {N : ℕ}
    (hcheck : D.check C = true)
    (hT : 0 < C.T)
    (hbnum : D.bnum C < (N : ℤ) * (C.T : ℤ))
    (henc : ∀ K : Code n 2, K.Nonempty → MinDistAtLeast d K →
      ∃ z : ℕ → ℚ, P K z ∧ (K.card : ℚ) = 1 + D.objForm z)
    (hblocks : ∀ K : Code n 2, ∀ z, P K z → ∀ b w, 0 ≤ D.blockForm b z w)
    (hrows : ∀ K : Code n 2, ∀ z, P K z → ∀ l, 0 ≤ D.rowForm l z) :
    A n 2 d ≤ N := by
  obtain ⟨K, hmin, hcard⟩ := exists_code_card_eq_A n 2 d
  rcases Finset.eq_empty_or_nonempty K with rfl | hK
  · rw [Finset.card_empty] at hcard
    omega
  obtain ⟨z, hPz, hobj⟩ := henc K hK hmin
  have hle := Data.objForm_le hcheck ⟨hblocks K z hPz, hrows K z hPz⟩
  have hTQ : (0 : ℚ) < C.T := by exact_mod_cast hT
  have hb : (D.bnum C : ℚ) < (N : ℚ) * C.T := by exact_mod_cast hbnum
  have hdiv : (D.bnum C : ℚ) / C.T < N := (div_lt_iff₀ hTQ).mpr hb
  have hlt : K.card < N + 1 := by
    have : (K.card : ℚ) < (N : ℚ) + 1 := by linarith
    exact_mod_cast this
  omega

end Delsarte.Certificate
