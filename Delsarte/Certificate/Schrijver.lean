/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
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

`A_19_6_le_of_relaxation`: **if** every nonempty binary code of length 19 and
minimum distance 6 yields a feasible point `z` of `Schrijver19_6.data` with
`|C| = 1 + objForm z`, **then** `A(19,6) ≤ 1280`. The certificate part carries no
assumption: `Schrijver19_6.check_data` and `bnum_lt` are decided by the kernel.

## What is not

The hypothesis. Nothing here shows that `Schrijver19_6.data` is Schrijver's
program, nor that it is a relaxation: that the constraints (20) hold for every code
(issue #44) and that the blocks (19) are positive semidefinite (issue #45,
Schrijver's Theorem 1). Until then the hypothesis is a named assumption.

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
theorem A_19_6_le_of_relaxation
    (hrelax : ∀ C : Code 19 2, C.Nonempty → MinDistAtLeast 6 C →
      ∃ z : ℕ → ℚ, data.Feasible z ∧ (C.card : ℚ) = 1 + data.objForm z) :
    A 19 2 6 ≤ 1280 := by
  obtain ⟨C, hmin, hcard⟩ := exists_code_card_eq_A 19 2 6
  rcases Finset.eq_empty_or_nonempty C with rfl | hC
  · rw [Finset.card_empty] at hcard
    omega
  obtain ⟨z, hz, hobj⟩ := hrelax C hC hmin
  have hle := Data.objForm_le check_data hz
  have hT : (0 : ℚ) < cert.T := by exact_mod_cast (by decide +kernel : 0 < cert.T)
  have hb : (data.bnum cert : ℚ) < 1280 * cert.T := by exact_mod_cast bnum_lt
  have hdiv : (data.bnum cert : ℚ) / cert.T < 1280 := (div_lt_iff₀ hT).mpr hb
  have hlt : C.card < 1281 := by exact_mod_cast (by linarith : (C.card : ℚ) < 1281)
  omega

end Delsarte.Certificate.Schrijver
