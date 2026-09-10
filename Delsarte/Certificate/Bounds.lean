/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Integer

/-!
# Certified bounds on `A(n, 2, d)`

Each bound here is a theorem about `A n 2 d`, obtained by handing a vector of
rationals to `Delsarte.Certificate.A_le_of_dualCert`. The vectors came from the
exact rational simplex in `tools/delsarte_lp.py`, which is not imported, not
trusted, and plays no part in any proof: it is a source of candidates. If it
returned nonsense, `DualCert` would refuse it.

## Two bounds

`A(23,2,7) ≤ 4096` lives in `Delsarte/Certificate/Golay.lean`, which imports only
the verifier so that Lake elaborates it in parallel with this module: it is the
most expensive exact check in the repository.

| bound | true value | remark |
|---|---|---|
| `A(5,2,3) ≤ 4` | 4 | the LP is tight |
| `A(13,2,5) ≤ 64` | 64 | tight; the Hamming bound only gives 89 |

Only the upper halves are proved. The matching codes exist — that is why the
values are known — but no code is constructed here, so nothing below may be read
as `A(n,2,d) = ...`.

## Two independent evaluations

Each proof is `decide` on the certificate scaled by its common denominator: the
kernel reduces integer arithmetic, and the Krawtchouk table is built by the
difference recurrence in `Delsarte/Certificate/Integer.lean`. The `#guard` lines at
the end run the compiled checker on the rational form instead, which evaluates
`krawtchouk` from its *binomial* definition. So each certificate is checked twice,
by two routes that share neither the arithmetic nor the recurrence, and
`krawCol_getD` is what says the two routes must agree.
-/

namespace Delsarte.Certificate

open Finset Delsarte

-- kernel reduction of the Krawtchouk table needs more than the default depth
set_option maxRecDepth 100000

/-! ## `A(5,2,3) ≤ 4`

The optimum of the LP, where `Delsarte.Certificate.certFiveThree` only reached 6.
-/

/-- Optimal certificate for `n = 5`, `d = 3`, scaled by its common denominator
`2`. Index `0` is unused. -/
def certFiveInt : List ℤ := [0, 1, 0, 0, 0, 1]

/-- The common denominator of `certFive`. -/
def certFiveDen : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`, `y 5 = 1/2`. Derived from the
integer form, so the two cannot drift apart. -/
def certFive : ℕ → ℚ := ratOfInt certFiveInt certFiveDen

theorem intCheck_certFive : intCheck 5 3 certFiveInt certFiveDen = true := by decide

theorem dualCert_certFive : DualCert 5 2 3 certFive :=
  dualCert_of_intCheck intCheck_certFive

/-- A binary code of length 5 with minimum distance 3 has at most 4 words. This is
the exact value. -/
theorem A_five_two_three_le_four : A 5 2 3 ≤ 4 :=
  A_le_of_intCert (p := certFiveInt) (D := certFiveDen) (by norm_num) intCheck_certFive
    (by decide)

/-! ## `A(13,2,5) ≤ 64`

The sphere-packing bound gives only `2 ^ 13 / (1 + 13 + 78) = 89`, so this is a
bound the linear program earns and elementary counting does not.
-/

/-- Optimal certificate for `n = 13`, `d = 5`, scaled by its common denominator
`10`. Symmetric. Index `0` is unused. -/
def certThirteenInt : List ℤ := [0, 6, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 6]

/-- The common denominator of `certThirteen`. -/
def certThirteenDen : ℤ := 10

/-- The same certificate as rationals: `3/5, 1/5, 1/10`, zeros, `1/10, 1/5, 3/5`.
Derived from the integer form, so the two cannot drift apart. -/
def certThirteen : ℕ → ℚ := ratOfInt certThirteenInt certThirteenDen

-- nine dual constraints, each a sum of thirteen integer products
theorem intCheck_certThirteen : intCheck 13 5 certThirteenInt certThirteenDen = true := by
  decide

theorem dualCert_certThirteen : DualCert 13 2 5 certThirteen :=
  dualCert_of_intCheck intCheck_certThirteen

/-- A binary code of length 13 with minimum distance 5 has at most 64 words. -/
theorem A_thirteen_two_five_le_64 : A 13 2 5 ≤ 64 :=
  A_le_of_intCert (p := certThirteenInt) (D := certThirteenDen) (by norm_num)
    intCheck_certThirteen (by decide)

/-! ## Replay through the other definition

These run the compiled checker, which evaluates `krawtchouk` from its binomial
definition — the route the proofs above could not take. Agreement between the two
is not a coincidence to be hoped for: it is `krawtchoukRec_eq`.
-/

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard dualCheck 5 2 3 certFive
#guard dualCheck 13 2 5 certThirteen
#guard bound 13 2 certThirteen == 64
#guard bound 5 2 certFive == 4

end Delsarte.Certificate
