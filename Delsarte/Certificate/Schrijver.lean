/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.Certificate.Relaxation
import Delsarte.SDP.Schrijver19_6

/-!
# Schrijver's semidefinite bound `A(19,6) ≤ 1280`, conditionally

Schrijver (IEEE Trans. Inf. Theory 51, 2005, Table I) bounds `A(19,6)` by `1280`
with a semidefinite program built on the Terwilliger algebra of the Hamming cube.
The value has since been improved (`1237`, Gijswijt–Mittelmann–Schrijver 2012). It
is certified here because a known number is what validates the pipeline: float
solve, exact rounding (`tools/schrijver_cert.py`), integer encoding
(`tools/schrijver_emit.py`), kernel check (`Delsarte.SDP.Sparse`).

## What is proved

`A_19_6_le_of_relaxation`: **if** a predicate `P C z` reading *`z` is the vector of
orbit averages of `C`* satisfies three things -- every nonempty binary code of
length 19 and minimum distance 6 has such a `z` with `|C| = 1 + objForm z`
(`henc`), such a `z` makes the blocks positive (`hblocks`), such a `z` satisfies
the inequalities (`hrows`) -- **then** `A(19,6) ≤ 1280`. The certificate part
carries no assumption: `Schrijver19_6.check_data` and `bnum_lt` are decided by the
kernel. The step from there to the bound is
`Delsarte.Certificate.A_le_of_relaxation`, shared by all seven cells.

## What is not

The three hypotheses, and they are three on purpose: `hblocks` is issue #45,
Schrijver's Theorem 1; `hrows` is issue #44, the constraints (20); `henc` is the
encoding, step 4 of `Delsarte/Hamming/THEOREM1.md` §5. Bundled behind one
`Feasible`, discharging either would have left the statement looking unchanged.
Nothing here shows that `Schrijver19_6.data` is Schrijver's program. Until all
three fall, they are named assumptions.

## Negative controls

* `not_check_certBad`: the certificate with its first multiplier raised by `1 / T`
  is rejected.
* `not_bnum_lt_1279`: this certificate bounds the objective by `1279.04`, so it
  proves `1280` and nothing smaller.
-/

namespace Delsarte.Certificate.Schrijver

open Delsarte.SDP.Sparse Delsarte.SDP.Schrijver19_6

/-- The certified value `1 + bnum / T` is below `1281`. -/
theorem bnum_lt : data.bnum cert < 1280 * (cert.T : ℤ) := by decide +kernel

/-- **Negative control.** The certificate proves `1280` and no smaller value. -/
theorem not_bnum_lt_1279 : ¬ data.bnum cert < 1279 * (cert.T : ℤ) := by decide +kernel

/-- The certificate with its first multiplier raised by one unit, that is `1 / T`. -/
noncomputable def certBad : Cert := { cert with mu := (cert.mu.headD 0 + 1) :: cert.mu.tail }

/-- The first row is `1 - x ≥ 0` on variable `0`, so its coefficient moves. -/
theorem coeff_certBad : data.coeff certBad 0 ≠ 0 := by decide +kernel

/-- **Negative control.** Raising one multiplier by `1 / T` breaks the check. -/
theorem not_check_certBad : data.check certBad = false := by
  refine Bool.eq_false_iff.mpr fun h => coeff_certBad ?_
  exact Data.coeff_eq_zero_of_check h (by rw [nv_data]; omega)

/-- **Schrijver's bound `A(19,6) ≤ 1280`**, conditional on the encoded program being
a relaxation of the code problem. The module docstring says what the hypothesis
still asks. -/
theorem A_19_6_le_of_relaxation {P : Code 19 2 → (ℕ → ℚ) → Prop}
    (henc : ∀ K : Code 19 2, K.Nonempty → MinDistAtLeast 6 K →
      ∃ z : ℕ → ℚ, P K z ∧ (K.card : ℚ) = 1 + data.objForm z)
    (hblocks : ∀ K z, P K z → ∀ b w, 0 ≤ data.blockForm b z w)
    (hrows : ∀ K z, P K z → ∀ l, 0 ≤ data.rowForm l z) :
    A 19 2 6 ≤ 1280 :=
  A_le_of_relaxation check_data (by decide +kernel) bnum_lt henc hblocks hrows

end Delsarte.Certificate.Schrijver
