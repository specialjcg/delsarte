/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.Certificate.Relaxation
import Delsarte.SDP.Schrijver22_10

/-!
# A semidefinite bound `A(22,10) ≤ 90`, conditionally

The same pipeline as `Delsarte.Certificate.Schrijver`: float solve, exact
rounding (`tools/schrijver_cert.py`), integer encoding (`tools/schrijver_emit.py`),
kernel check (`Delsarte.SDP.Sparse`). Certified value of the objective:
90.329449920. The cell has 91 variables, 138 rows, 13458 nonzeros in the blocks,
and `W` of order `2 ^ 110`.

## The one cell that needed a different solver

`CLARABEL` does not return a point here at all -- it raises
`cvxpy.error.SolverError` -- which is why this cell was missing when the other
five were transcribed. The solver is now a parameter,
`schrijver_emit.py 22 10 OUT.lean --solver=SCS`, and SCS converges. That changes
nothing about what is trusted: the float point is rounded to rationals and
re-checked exactly, so a different solver can only change *which* bound is
reached, never whether an invalid certificate passes. Every other shipped cell
still regenerates byte-for-byte on the unchanged `CLARABEL` default.

The bound does depend on the solver's tolerances. At
`eps_abs = eps_rel = 1e-9, max_iters = 200000` the same pipeline reaches
89.426040411, one integer lower. The number recorded here is the one the
committed command produces at SCS's default settings, because that is the one
this repository can replay. Two successive regenerations agree byte-for-byte.

## What this bound is worth

Nothing against the literature. Brouwer's table gives `64 ≤ A(22,10) ≤ 84`, so
`90` is six above the published upper bound and the cell stays open. What it beats
is this repository's own linear program, which gives `95`. As with the other five,
the gain is for the repository, not against the state of the art.

## What is proved

`A_22_10_le_of_relaxation`: **if** a predicate `P C z` reading *`z` is the vector of
orbit averages of `C`* satisfies `henc`, `hblocks` and `hrows` for length 22 and
minimum distance 10, **then** `A(22,10) ≤ 90`. The certificate part carries no
assumption: `Schrijver22_10.check_data` and `bnum_lt` are decided by the kernel.
The shared step is `Delsarte.Certificate.A_le_of_relaxation`.

## What is not

The three hypotheses, exactly as in `Delsarte.Certificate.Schrijver`: `hblocks` is
issue #45, `hrows` is issue #44, `henc` is the encoding. Nothing here shows that
`Schrijver22_10.data` is Schrijver's program. Until all three fall they are named
assumptions, and this statement is not a bound this repository has proved.

## A correction, recorded rather than quietly fixed

An earlier README claimed SCS drove this cell "to about 68, below Brouwer's 84",
and read that as the `BETTER` verdict `crosscheck_brouwer.py` says to treat as a
bug. It was neither a bug nor a bound: 68 was the `after mapping` line, the state
*before* the correction passes, carrying a residual of 5.2e-01. Those passes only
ever raise the value -- `bump` adds nonnegative amounts -- and they carry it to
90.33. Nothing ever went below a published bound.

## Negative controls

* `not_check_certBad`: the certificate with its first multiplier raised by `1 / T`
  is rejected.
* `not_bnum_lt_89`: this certificate bounds the objective by `90.33`, so it
  proves `90` and nothing smaller.
-/

namespace Delsarte.Certificate.Schrijver22_10

open Delsarte.SDP.Sparse Delsarte.SDP.Schrijver22_10

/-- The certified value `1 + bnum / T` is below `91`. -/
theorem bnum_lt : data.bnum cert < 90 * (cert.T : ℤ) := by decide +kernel

/-- **Negative control.** The certificate proves `90` and no smaller value. -/
theorem not_bnum_lt_89 : ¬ data.bnum cert < 89 * (cert.T : ℤ) := by decide +kernel

/-- The certificate with its first multiplier raised by one unit, that is `1 / T`. -/
noncomputable def certBad : Cert := { cert with mu := (cert.mu.headD 0 + 1) :: cert.mu.tail }

/-- The first row is `1 - x ≥ 0` on variable `0`, so its coefficient moves. -/
theorem coeff_certBad : data.coeff certBad 0 ≠ 0 := by decide +kernel

/-- **Negative control.** Raising one multiplier by `1 / T` breaks the check. -/
theorem not_check_certBad : data.check certBad = false := by
  refine Bool.eq_false_iff.mpr fun h => coeff_certBad ?_
  exact Data.coeff_eq_zero_of_check h (by rw [nv_data]; omega)

/-- **The bound `A(22,10) ≤ 90`**, conditional on the encoded program being a
relaxation of the code problem. The module docstring says what the hypothesis
still asks, and what the bound is worth against the literature. -/
theorem A_22_10_le_of_relaxation {P : Code 22 2 → (ℕ → ℚ) → Prop}
    (henc : ∀ K : Code 22 2, K.Nonempty → MinDistAtLeast 10 K →
      ∃ z : ℕ → ℚ, P K z ∧ (K.card : ℚ) = 1 + data.objForm z)
    (hblocks : ∀ K z, P K z → ∀ b w, 0 ≤ data.blockForm b z w)
    (hrows : ∀ K z, P K z → ∀ l, 0 ≤ data.rowForm l z) :
    A 22 2 10 ≤ 90 :=
  A_le_of_relaxation check_data (by decide +kernel) bnum_lt henc hblocks hrows

end Delsarte.Certificate.Schrijver22_10
