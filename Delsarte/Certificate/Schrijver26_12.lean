/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.SDP.Schrijver26_12

/-!
# A semidefinite bound `A(26,12) ≤ 98`, conditionally

The same pipeline as `Delsarte.Certificate.Schrijver`: float solve, exact
rounding (`tools/schrijver_cert.py`), integer encoding (`tools/schrijver_emit.py`),
kernel check (`Delsarte.SDP.Sparse`). Certified value of the objective:
98.154160785.

## What this bound is worth

Less than the literature, and only just. Brouwer's table gives
`64 ≤ A(26,12) ≤ 96`, so `98` misses the published upper bound by two and the
cell stays open. What it does beat is this repository's own linear program, which
gives `113` on the same cell. The gain is for the repository, not against the
state of the art, and it is recorded as such.

## What is proved

`A_26_12_le_of_relaxation`: **if** every nonempty binary code of length 26 and
minimum distance 12 yields a feasible point `z` of `Schrijver26_12.data` with
`|C| = 1 + objForm z`, **then** `A(26,12) ≤ 98`. The certificate part carries no
assumption: `Schrijver26_12.check_data` and `bnum_lt` are decided by the kernel.

## What is not

The hypothesis, exactly as in `Delsarte.Certificate.Schrijver`: nothing here shows
that `Schrijver26_12.data` is Schrijver's program, nor that it is a relaxation --
that the constraints (20) hold for every code (issue #44) and that the blocks (19)
are positive semidefinite (issue #45). Until then the hypothesis is a named
assumption, and this statement is not a bound this repository has proved.

## The solver warned

`CLARABEL` returned this point with `Solution may be inaccurate`. That warning is
about the float solve, which is outside the trust base; the exact integer check
below is what decides, and it passes. The warning is recorded rather than hidden
because it is the normal case this pipeline is built for: the solver proposes, the
kernel disposes. It matters more here than elsewhere: two units separate this
bound from the published one, so a sharper solve on this cell is the one place in
this batch where the gap could plausibly close.

## Negative controls

* `not_check_certBad`: the certificate with its first multiplier raised by `1 / T`
  is rejected.
* `not_bnum_lt_97`: this certificate bounds the objective by `98.15`, so it proves
  `98` and nothing smaller.
-/

namespace Delsarte.Certificate.Schrijver26_12

open Delsarte.SDP.Sparse Delsarte.SDP.Schrijver26_12

/-- The certified value `1 + bnum / T` is below `99`. -/
theorem bnum_lt : data.bnum cert < 98 * (cert.T : ℤ) := by decide +kernel

/-- **Negative control.** The certificate proves `98` and no smaller value. -/
theorem not_bnum_lt_97 : ¬ data.bnum cert < 97 * (cert.T : ℤ) := by decide +kernel

/-- The certificate with its first multiplier raised by one unit, that is `1 / T`. -/
noncomputable def certBad : Cert := { cert with mu := (cert.mu.headD 0 + 1) :: cert.mu.tail }

/-- The first row is `1 - x ≥ 0` on variable `0`, so its coefficient moves. -/
theorem coeff_certBad : data.coeff certBad 0 ≠ 0 := by decide +kernel

/-- **Negative control.** Raising one multiplier by `1 / T` breaks the check. -/
theorem not_check_certBad : data.check certBad = false := by
  refine Bool.eq_false_iff.mpr fun h => coeff_certBad ?_
  exact Data.coeff_eq_zero_of_check h (by rw [nv_data]; omega)

/-- **The bound `A(26,12) ≤ 98`**, conditional on the encoded program being a
relaxation of the code problem. The module docstring says what the hypothesis
still asks, and what the bound is worth against the literature. -/
theorem A_26_12_le_of_relaxation
    (hrelax : ∀ C : Code 26 2, C.Nonempty → MinDistAtLeast 12 C →
      ∃ z : ℕ → ℚ, data.Feasible z ∧ (C.card : ℚ) = 1 + data.objForm z) :
    A 26 2 12 ≤ 98 := by
  obtain ⟨C, hmin, hcard⟩ := exists_code_card_eq_A 26 2 12
  rcases Finset.eq_empty_or_nonempty C with rfl | hC
  · rw [Finset.card_empty] at hcard
    omega
  obtain ⟨z, hz, hobj⟩ := hrelax C hC hmin
  have hle := Data.objForm_le check_data hz
  have hT : (0 : ℚ) < cert.T := by exact_mod_cast (by decide +kernel : 0 < cert.T)
  have hb : (data.bnum cert : ℚ) < 98 * cert.T := by exact_mod_cast bnum_lt
  have hdiv : (data.bnum cert : ℚ) / cert.T < 98 := (div_lt_iff₀ hT).mpr hb
  have hlt : C.card < 99 := by exact_mod_cast (by linarith : (C.card : ℚ) < 99)
  omega

end Delsarte.Certificate.Schrijver26_12
