/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.SDP.Schrijver21_10

/-!
# A semidefinite bound `A(21,10) ≤ 49`, conditionally

The same pipeline as `Delsarte.Certificate.Schrijver`, on a cell nobody has
transcribed: float solve, exact rounding (`tools/schrijver_cert.py`), integer
encoding (`tools/schrijver_emit.py`), kernel check (`Delsarte.SDP.Sparse`).
Certified value of the objective: 49.761175570.

## What this bound is worth

Less than the literature. `A(21,10)` is known to lie in `42 … 47`, so `49` beats
nothing that is published, and the cell stays open. What it does beat is this
repository's own linear program, which gives `64` on the same cell. The gain is
for the repository, not against the state of the art, and it is recorded as such.

## What is proved

`A_21_10_le_of_relaxation`: **if** every nonempty binary code of length 21 and
minimum distance 10 yields a feasible point `z` of `Schrijver21_10.data` with
`|C| = 1 + objForm z`, **then** `A(21,10) ≤ 49`. The certificate part carries no
assumption: `Schrijver21_10.check_data` and `bnum_lt` are decided by the kernel.

## What is not

The hypothesis, exactly as in `Delsarte.Certificate.Schrijver`: nothing here shows
that `Schrijver21_10.data` is Schrijver's program, nor that it is a relaxation --
that the constraints (20) hold for every code (issue #44) and that the blocks (19)
are positive semidefinite (issue #45). Until then the hypothesis is a named
assumption, and this statement is not a bound this repository has proved.

## Negative controls

* `not_check_certBad`: the certificate with its first multiplier raised by `1 / T`
  is rejected.
* `not_bnum_lt_48`: this certificate bounds the objective by `48.76`, so it proves
  `49` and nothing smaller.
-/

namespace Delsarte.Certificate.Schrijver21_10

open Delsarte.SDP.Sparse Delsarte.SDP.Schrijver21_10

/-- The certified value `1 + bnum / T` is below `50`. -/
theorem bnum_lt : data.bnum cert < 49 * (cert.T : ℤ) := by decide +kernel

/-- **Negative control.** The certificate proves `49` and no smaller value. -/
theorem not_bnum_lt_48 : ¬ data.bnum cert < 48 * (cert.T : ℤ) := by decide +kernel

/-- The certificate with its first multiplier raised by one unit, that is `1 / T`. -/
noncomputable def certBad : Cert := { cert with mu := (cert.mu.headD 0 + 1) :: cert.mu.tail }

/-- The first row is `1 - x ≥ 0` on variable `0`, so its coefficient moves. -/
theorem coeff_certBad : data.coeff certBad 0 ≠ 0 := by decide +kernel

/-- **Negative control.** Raising one multiplier by `1 / T` breaks the check. -/
theorem not_check_certBad : data.check certBad = false := by
  refine Bool.eq_false_iff.mpr fun h => coeff_certBad ?_
  exact Data.coeff_eq_zero_of_check h (by rw [nv_data]; omega)

/-- **The bound `A(21,10) ≤ 49`**, conditional on the encoded program being a
relaxation of the code problem. The module docstring says what the hypothesis
still asks, and what the bound is worth against the literature. -/
theorem A_21_10_le_of_relaxation
    (hrelax : ∀ C : Code 21 2, C.Nonempty → MinDistAtLeast 10 C →
      ∃ z : ℕ → ℚ, data.Feasible z ∧ (C.card : ℚ) = 1 + data.objForm z) :
    A 21 2 10 ≤ 49 := by
  obtain ⟨C, hmin, hcard⟩ := exists_code_card_eq_A 21 2 10
  rcases Finset.eq_empty_or_nonempty C with rfl | hC
  · rw [Finset.card_empty] at hcard
    omega
  obtain ⟨z, hz, hobj⟩ := hrelax C hC hmin
  have hle := Data.objForm_le check_data hz
  have hT : (0 : ℚ) < cert.T := by exact_mod_cast (by decide +kernel : 0 < cert.T)
  have hb : (data.bnum cert : ℚ) < 49 * cert.T := by exact_mod_cast bnum_lt
  have hdiv : (data.bnum cert : ℚ) / cert.T < 49 := (div_lt_iff₀ hT).mpr hb
  have hlt : C.card < 50 := by exact_mod_cast (by linarith : (C.card : ℚ) < 50)
  omega

end Delsarte.Certificate.Schrijver21_10
