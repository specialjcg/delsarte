/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.SDP.Schrijver25_10

/-!
# A semidefinite bound `A(25,10) ≤ 505`, conditionally

The same pipeline as `Delsarte.Certificate.Schrijver`: float solve, exact
rounding (`tools/schrijver_cert.py`), integer encoding (`tools/schrijver_emit.py`),
kernel check (`Delsarte.SDP.Sparse`). Certified value of the objective:
505.211478807.

This is the largest cell transcribed here: 186 variables, 307 rows, 28556
nonzeros in the blocks, `W` of order `2 ^ 122`, and about two minutes of kernel
work in `Delsarte.SDP.Schrijver25_10`.

## What this bound is worth

Less than the literature, and by a wide margin. Brouwer's table gives
`192 ≤ A(25,10) ≤ 466`, so `505` beats nothing that is published and the cell
stays open. What it does beat is this repository's own linear program, which gives
`551` on the same cell. The gain is for the repository, not against the state of
the art, and it is recorded as such.

## What is proved

`A_25_10_le_of_relaxation`: **if** every nonempty binary code of length 25 and
minimum distance 10 yields a feasible point `z` of `Schrijver25_10.data` with
`|C| = 1 + objForm z`, **then** `A(25,10) ≤ 505`. The certificate part carries no
assumption: `Schrijver25_10.check_data` and `bnum_lt` are decided by the kernel.

## What is not

The hypothesis, exactly as in `Delsarte.Certificate.Schrijver`: nothing here shows
that `Schrijver25_10.data` is Schrijver's program, nor that it is a relaxation --
that the constraints (20) hold for every code (issue #44) and that the blocks (19)
are positive semidefinite (issue #45). Until then the hypothesis is a named
assumption, and this statement is not a bound this repository has proved.

## The solver warned, and float disagreed with exact

`CLARABEL` returned this point with `Solution may be inaccurate`. Worse, this is
the cell where the float value and the exact one part company most visibly: the
solve reports `505.211330`, the exact rational evaluation gives `505.211478807`,
a gap of about `1.5e-4`. Both floor to `505`, so nothing is lost here -- but the
gap is the whole argument for doing this exactly. Reading the bound off the float
would have been a bet; only the kernel check makes it a statement.

## Negative controls

* `not_check_certBad`: the certificate with its first multiplier raised by `1 / T`
  is rejected.
* `not_bnum_lt_504`: this certificate bounds the objective by `505.21`, so it
  proves `505` and nothing smaller.
-/

namespace Delsarte.Certificate.Schrijver25_10

open Delsarte.SDP.Sparse Delsarte.SDP.Schrijver25_10

/-- The certified value `1 + bnum / T` is below `506`. -/
theorem bnum_lt : data.bnum cert < 505 * (cert.T : ℤ) := by decide +kernel

/-- **Negative control.** The certificate proves `505` and no smaller value. -/
theorem not_bnum_lt_504 : ¬ data.bnum cert < 504 * (cert.T : ℤ) := by decide +kernel

/-- The certificate with its first multiplier raised by one unit, that is `1 / T`. -/
noncomputable def certBad : Cert := { cert with mu := (cert.mu.headD 0 + 1) :: cert.mu.tail }

/-- The first row is `1 - x ≥ 0` on variable `0`, so its coefficient moves. -/
theorem coeff_certBad : data.coeff certBad 0 ≠ 0 := by decide +kernel

/-- **Negative control.** Raising one multiplier by `1 / T` breaks the check. -/
theorem not_check_certBad : data.check certBad = false := by
  refine Bool.eq_false_iff.mpr fun h => coeff_certBad ?_
  exact Data.coeff_eq_zero_of_check h (by rw [nv_data]; omega)

/-- **The bound `A(25,10) ≤ 505`**, conditional on the encoded program being a
relaxation of the code problem. The module docstring says what the hypothesis
still asks, and what the bound is worth against the literature. -/
theorem A_25_10_le_of_relaxation
    (hrelax : ∀ C : Code 25 2, C.Nonempty → MinDistAtLeast 10 C →
      ∃ z : ℕ → ℚ, data.Feasible z ∧ (C.card : ℚ) = 1 + data.objForm z) :
    A 25 2 10 ≤ 505 := by
  obtain ⟨C, hmin, hcard⟩ := exists_code_card_eq_A 25 2 10
  rcases Finset.eq_empty_or_nonempty C with rfl | hC
  · rw [Finset.card_empty] at hcard
    omega
  obtain ⟨z, hz, hobj⟩ := hrelax C hC hmin
  have hle := Data.objForm_le check_data hz
  have hT : (0 : ℚ) < cert.T := by exact_mod_cast (by decide +kernel : 0 < cert.T)
  have hb : (data.bnum cert : ℚ) < 505 * cert.T := by exact_mod_cast bnum_lt
  have hdiv : (data.bnum cert : ℚ) / cert.T < 505 := (div_lt_iff₀ hT).mpr hb
  have hlt : C.card < 506 := by exact_mod_cast (by linarith : (C.card : ℚ) < 506)
  omega

end Delsarte.Certificate.Schrijver25_10
