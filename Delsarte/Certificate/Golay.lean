/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Integer

/-!
# `A(23,2,7) ≤ 4096`, and what exactness buys

The perfect binary Golay code has 4096 words, so the linear program is tight here.
Only the upper half is proved: no code is constructed, so this is not an equality.

The certificate is stored as integers scaled by their common denominator, and the
check is `decide` — kernel reduction of `ℤ` arithmetic, see
`Delsarte/Certificate/Integer.lean`. The rational form is derived from the integer
one, so the two cannot drift apart, and `Delsarte/Certificate/Files.lean` checks
the derived rationals against `examples/a-23-7.cert`.
-/

namespace Delsarte.Certificate

open Finset Delsarte

-- kernel reduction of the table walks 24 columns of 24 entries; the elaborator's
-- default recursion depth is far below that
set_option maxRecDepth 100000

/-- Optimal certificate for `n = 23`, `d = 7`, scaled by the common denominator
`2772`. As rationals: `1, 41/66, 857/2772, 323/2772, 95/2772, 5/924`, then zeros,
then `5/1386, 79/2772, 277/2772, 37/132, 7/12, 1`. Index `0` is unused and must be
zero. -/
def golayInt : List ℤ :=
  [0, 2772, 1722, 857, 323, 95, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   10, 79, 277, 777, 1617, 2772]

/-- The common denominator of `certGolay`. -/
def golayDen : ℤ := 2772

/-- The Golay certificate as rationals. Derived, not transcribed. -/
def certGolay : ℕ → ℚ := ratOfInt golayInt golayDen

/-- The kernel accepts the scaled certificate. Seventeen dual constraints, each a
sum of twenty-three integer products. -/
theorem intCheck_golayInt : intCheck 23 7 golayInt golayDen = true := by decide

theorem dualCert_certGolay : DualCert 23 2 7 certGolay :=
  dualCert_of_intCheck intCheck_golayInt

/-- A binary code of length 23 with minimum distance 7 has at most 4096 words. The
perfect binary Golay code has exactly 4096, so this bound is attained — but no code
is constructed here, and this file proves only the upper half. -/
theorem A_twentyThree_two_seven_le_4096 : A 23 2 7 ≤ 4096 :=
  A_le_of_intCert (p := golayInt) (D := golayDen) (by norm_num) intCheck_golayInt (by decide)

/-! ## Control: the exactness is what carries the result

Lowering one coefficient of the Golay certificate by `10 ^ (-30)` — a change no
`Float` can represent — turns the bound into

`4095.999999999999999999999999999747`

whose floor is 4095. A verifier that had rounded anywhere would then "prove"
`A(23,2,7) ≤ 4095`, and that statement is **false**: the perfect binary Golay code
has 4096 words. The exact check refuses the perturbed vector, at distances 11, 12
and 13.

Scaling by `10 ^ 30` keeps the perturbation integral, so the refusal too is decided
by the kernel.
-/

/-- The Golay certificate with `y 2` lowered by `10 ^ (-30)`, scaled by
`2772 · 10 ^ 30`. -/
def golayIntPerturbed : List ℤ :=
  (golayInt.map (· * 10 ^ 30)).set 2 (1722 * 10 ^ 30 - 2772)

/-- The scaled denominator that goes with `golayIntPerturbed`. -/
def golayDenPerturbed : ℤ := golayDen * 10 ^ 30

theorem not_intCheck_golayIntPerturbed :
    intCheck 23 7 golayIntPerturbed golayDenPerturbed = false := by decide

/-- And the refusal is not an artefact of the encoding: the perturbed vector is not
dual feasible at all, because the constraint at distance 11 fails. -/
theorem not_dualCert_golayIntPerturbed :
    ¬ DualCert 23 2 7 (ratOfInt golayIntPerturbed golayDenPerturbed) :=
  not_dualCert_of_intSlack (n := 23) (d := 7) (i := 11) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard dualCheck 23 2 7 certGolay
#guard bound 23 2 certGolay == 4096
#guard certGolay 2 == 41 / 66
#guard !dualCheck 23 2 7 (ratOfInt golayIntPerturbed golayDenPerturbed)
#guard bound 23 2 (ratOfInt golayIntPerturbed golayDenPerturbed) < 4096
-- the perturbed bound is above 4095, so only a rounding verifier would accept it
#guard bound 23 2 (ratOfInt golayIntPerturbed golayDenPerturbed) > 4095

end Delsarte.Certificate
