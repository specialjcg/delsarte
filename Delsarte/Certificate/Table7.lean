/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Floor

/-!
# Certified bounds, part 7: sixteen cells where the linear program is already integral

Parts 1 to 6 were assembled one certificate at a time, which is why they are small:
each one cost tens of seconds of `norm_num` when they were written. Since
`Delsarte/Certificate/Integer.lean` the check is kernel reduction in `ℤ`, and the
marginal cost was measured rather than guessed -- four certificates including the
worst denominator of this file add about two seconds and eighty megabytes to a build
whose baseline is mathlib's own three and a half gigabytes. So the selection here is
no longer limited by what the checker can afford.

What limits it instead is integrality. `A_le_of_intCert` needs the linear program's
optimum to *be* an integer; when it is not, the bound has to go through the floor
route of `Delsarte/Certificate/Floor.lean`. The sixteen cells below are exactly the
ones where the exact optimum is already an integer and the resulting bound is at
least ten, so the certificate carries real content rather than a near-trivial count.

| bound | | bound | | bound |
|---|---|---|---|---|
| `A(11,2,6) ≤ 12` | | `A(19,2,10) ≤ 20` | | `A(23,2,12) ≤ 24` |
| `A(14,2,4) ≤ 512` | | `A(20,2,10) ≤ 40` | | `A(24,2,12) ≤ 48` |
| `A(14,2,6) ≤ 64` | | `A(22,2,8) ≤ 1024` | | `A(26,2,14) ≤ 14` |
| `A(15,2,4) ≤ 1024` | | `A(22,2,12) ≤ 12` | | `A(27,2,14) ≤ 28` |
| `A(15,2,8) ≤ 16` | | `A(23,2,8) ≤ 2048` | | `A(28,2,14) ≤ 56` |
| `A(18,2,10) ≤ 10` | | | | |

Only upper bounds are proved. Whether a cell's true value is *known* is a separate
question, settled by the published table and reported by
`tools/crosscheck_brouwer.py`, not claimed here. As everywhere in this repository the
solver of `tools/delsarte_lp.py` produced the candidates and appears in no proof:
every vector below is re-verified by exact integer arithmetic in the kernel.
-/

namespace Delsarte.Certificate

open Delsarte

-- kernel reduction of the Krawtchouk table needs more than the default depth
set_option maxRecDepth 100000

-- The `#`-command linter is off here on purpose: these commands are the replay. They
-- run the compiled rational checker on the *binomial* definition of `krawtchouk`,
-- while the proofs go through the integer difference table.
set_option linter.hashCommand false

/-- Certificate for `n = 11`, `d = 6`, scaled by its common denominator
`1`. Index `0` is unused. -/
def cert11_6Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert11_6`. -/
def cert11_6Den : ℤ := 1

/-- The same certificate as rationals: `y 1 = 1`. Derived from the integer form, so the two
cannot drift apart. -/
def cert11_6 : ℕ → ℚ := ratOfInt cert11_6Int cert11_6Den

-- 6 dual constraints, each a sum of 11 integer products
theorem intCheck_cert11_6 : intCheck 11 6 cert11_6Int cert11_6Den = true := by decide

theorem dualCert_cert11_6 : DualCert 11 2 6 cert11_6 :=
  dualCert_of_intCheck intCheck_cert11_6

theorem A_11_2_6_le : A 11 2 6 ≤ 12 :=
  A_le_of_intCert (p := cert11_6Int) (D := cert11_6Den) (by norm_num) intCheck_cert11_6
    (by decide)

#guard dualCheck 11 2 6 cert11_6
#guard bound 11 2 cert11_6 == 12

/-- Certificate for `n = 14`, `d = 4`, scaled by its common denominator
`1092`. Index `0` is unused. -/
def cert14_4Int : List ℤ :=
  [0, 819, 540, 329, 154, 62, 0, 0, 0, 29, 28, 35, 6, 0, 0]

/-- The common denominator of `cert14_4`. -/
def cert14_4Den : ℤ := 1092

/-- The same certificate as rationals: `y 1 = 3/4`, `y 2 = 45/91`, `y 3 = 47/156`, `y 4 =
11/78`, `y 5 = 31/546`, `y 9 = 29/1092`, `y 10 = 1/39`, `y 11 = 5/156`, `y 12 = 1/182`. Derived
from the integer form, so the two cannot drift apart. -/
def cert14_4 : ℕ → ℚ := ratOfInt cert14_4Int cert14_4Den

-- 11 dual constraints, each a sum of 14 integer products
theorem intCheck_cert14_4 : intCheck 14 4 cert14_4Int cert14_4Den = true := by decide

theorem dualCert_cert14_4 : DualCert 14 2 4 cert14_4 :=
  dualCert_of_intCheck intCheck_cert14_4

theorem A_14_2_4_le : A 14 2 4 ≤ 512 :=
  A_le_of_intCert (p := cert14_4Int) (D := cert14_4Den) (by norm_num) intCheck_cert14_4
    (by decide)

#guard dualCheck 14 2 4 cert14_4
#guard bound 14 2 cert14_4 == 512

/-- Certificate for `n = 14`, `d = 6`, scaled by its common denominator
`1560`. Index `0` is unused. -/
def cert14_6Int : List ℤ :=
  [0, 936, 304, 101, 0, 0, 0, 0, 0, 0, 0, 55, 8, 0, 0]

/-- The common denominator of `cert14_6`. -/
def cert14_6Den : ℤ := 1560

/-- The same certificate as rationals: `y 1 = 3/5`, `y 2 = 38/195`, `y 3 = 101/1560`, `y 11 =
11/312`, `y 12 = 1/195`. Derived from the integer form, so the two cannot drift apart. -/
def cert14_6 : ℕ → ℚ := ratOfInt cert14_6Int cert14_6Den

-- 9 dual constraints, each a sum of 14 integer products
theorem intCheck_cert14_6 : intCheck 14 6 cert14_6Int cert14_6Den = true := by decide

theorem dualCert_cert14_6 : DualCert 14 2 6 cert14_6 :=
  dualCert_of_intCheck intCheck_cert14_6

theorem A_14_2_6_le : A 14 2 6 ≤ 64 :=
  A_le_of_intCert (p := cert14_6Int) (D := cert14_6Den) (by norm_num) intCheck_cert14_6
    (by decide)

#guard dualCheck 14 2 6 cert14_6
#guard bound 14 2 cert14_6 == 64

/-- Certificate for `n = 15`, `d = 4`, scaled by its common denominator
`182`. Index `0` is unused. -/
def cert15_4Int : List ℤ :=
  [0, 147, 96, 64, 29, 14, 0, 0, 0, 5, 8, 8, 7, 0, 0, 0]

/-- The common denominator of `cert15_4`. -/
def cert15_4Den : ℤ := 182

/-- The same certificate as rationals: `y 1 = 21/26`, `y 2 = 48/91`, `y 3 = 32/91`, `y 4 =
29/182`, `y 5 = 1/13`, `y 9 = 5/182`, `y 10 = 4/91`, `y 11 = 4/91`, `y 12 = 1/26`. Derived from
the integer form, so the two cannot drift apart. -/
def cert15_4 : ℕ → ℚ := ratOfInt cert15_4Int cert15_4Den

-- 12 dual constraints, each a sum of 15 integer products
theorem intCheck_cert15_4 : intCheck 15 4 cert15_4Int cert15_4Den = true := by decide

theorem dualCert_cert15_4 : DualCert 15 2 4 cert15_4 :=
  dualCert_of_intCheck intCheck_cert15_4

theorem A_15_2_4_le : A 15 2 4 ≤ 1024 :=
  A_le_of_intCert (p := cert15_4Int) (D := cert15_4Den) (by norm_num) intCheck_cert15_4
    (by decide)

#guard dualCheck 15 2 4 cert15_4
#guard bound 15 2 cert15_4 == 1024

/-- Certificate for `n = 15`, `d = 8`, scaled by its common denominator
`1`. Index `0` is unused. -/
def cert15_8Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert15_8`. -/
def cert15_8Den : ℤ := 1

/-- The same certificate as rationals: `y 1 = 1`. Derived from the integer form, so the two
cannot drift apart. -/
def cert15_8 : ℕ → ℚ := ratOfInt cert15_8Int cert15_8Den

-- 8 dual constraints, each a sum of 15 integer products
theorem intCheck_cert15_8 : intCheck 15 8 cert15_8Int cert15_8Den = true := by decide

theorem dualCert_cert15_8 : DualCert 15 2 8 cert15_8 :=
  dualCert_of_intCheck intCheck_cert15_8

theorem A_15_2_8_le : A 15 2 8 ≤ 16 :=
  A_le_of_intCert (p := cert15_8Int) (D := cert15_8Den) (by norm_num) intCheck_cert15_8
    (by decide)

#guard dualCheck 15 2 8 cert15_8
#guard bound 15 2 cert15_8 == 16

/-- Certificate for `n = 18`, `d = 10`, scaled by its common denominator
`2`. Index `0` is unused. -/
def cert18_10Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert18_10`. -/
def cert18_10Den : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`. Derived from the integer form, so the two
cannot drift apart. -/
def cert18_10 : ℕ → ℚ := ratOfInt cert18_10Int cert18_10Den

-- 9 dual constraints, each a sum of 18 integer products
theorem intCheck_cert18_10 : intCheck 18 10 cert18_10Int cert18_10Den = true := by decide

theorem dualCert_cert18_10 : DualCert 18 2 10 cert18_10 :=
  dualCert_of_intCheck intCheck_cert18_10

theorem A_18_2_10_le : A 18 2 10 ≤ 10 :=
  A_le_of_intCert (p := cert18_10Int) (D := cert18_10Den) (by norm_num) intCheck_cert18_10
    (by decide)

#guard dualCheck 18 2 10 cert18_10
#guard bound 18 2 cert18_10 == 10

/-- Certificate for `n = 19`, `d = 10`, scaled by its common denominator
`1`. Index `0` is unused. -/
def cert19_10Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert19_10`. -/
def cert19_10Den : ℤ := 1

/-- The same certificate as rationals: `y 1 = 1`. Derived from the integer form, so the two
cannot drift apart. -/
def cert19_10 : ℕ → ℚ := ratOfInt cert19_10Int cert19_10Den

-- 10 dual constraints, each a sum of 19 integer products
theorem intCheck_cert19_10 : intCheck 19 10 cert19_10Int cert19_10Den = true := by decide

theorem dualCert_cert19_10 : DualCert 19 2 10 cert19_10 :=
  dualCert_of_intCheck intCheck_cert19_10

theorem A_19_2_10_le : A 19 2 10 ≤ 20 :=
  A_le_of_intCert (p := cert19_10Int) (D := cert19_10Den) (by norm_num) intCheck_cert19_10
    (by decide)

#guard dualCheck 19 2 10 cert19_10
#guard bound 19 2 cert19_10 == 20

/-- Certificate for `n = 20`, `d = 10`, scaled by its common denominator
`10`. Index `0` is unused. -/
def cert20_10Int : List ℤ :=
  [0, 10, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert20_10`. -/
def cert20_10Den : ℤ := 10

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 1/10`. Derived from the integer form,
so the two cannot drift apart. -/
def cert20_10 : ℕ → ℚ := ratOfInt cert20_10Int cert20_10Den

-- 11 dual constraints, each a sum of 20 integer products
theorem intCheck_cert20_10 : intCheck 20 10 cert20_10Int cert20_10Den = true := by decide

theorem dualCert_cert20_10 : DualCert 20 2 10 cert20_10 :=
  dualCert_of_intCheck intCheck_cert20_10

theorem A_20_2_10_le : A 20 2 10 ≤ 40 :=
  A_le_of_intCert (p := cert20_10Int) (D := cert20_10Den) (by norm_num) intCheck_cert20_10
    (by decide)

#guard dualCheck 20 2 10 cert20_10
#guard bound 20 2 cert20_10 == 40

/-- Certificate for `n = 22`, `d = 8`, scaled by its common denominator
`47286`. Index `0` is unused. -/
def cert22_8Int : List ℤ :=
  [0, 36471, 18701, 7779, 2346, 515, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75, 0, 0, 0, 0]

/-- The common denominator of `cert22_8`. -/
def cert22_8Den : ℤ := 47286

/-- The same certificate as rationals: `y 1 = 12157/15762`, `y 2 = 18701/47286`, `y 3 =
2593/15762`, `y 4 = 391/7881`, `y 5 = 515/47286`, `y 18 = 25/15762`. Derived from the integer
form, so the two cannot drift apart. -/
def cert22_8 : ℕ → ℚ := ratOfInt cert22_8Int cert22_8Den

-- 15 dual constraints, each a sum of 22 integer products
theorem intCheck_cert22_8 : intCheck 22 8 cert22_8Int cert22_8Den = true := by decide

theorem dualCert_cert22_8 : DualCert 22 2 8 cert22_8 :=
  dualCert_of_intCheck intCheck_cert22_8

theorem A_22_2_8_le : A 22 2 8 ≤ 1024 :=
  A_le_of_intCert (p := cert22_8Int) (D := cert22_8Den) (by norm_num) intCheck_cert22_8
    (by decide)

#guard dualCheck 22 2 8 cert22_8
#guard bound 22 2 cert22_8 == 1024

/-- Certificate for `n = 22`, `d = 12`, scaled by its common denominator
`2`. Index `0` is unused. -/
def cert22_12Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert22_12`. -/
def cert22_12Den : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`. Derived from the integer form, so the two
cannot drift apart. -/
def cert22_12 : ℕ → ℚ := ratOfInt cert22_12Int cert22_12Den

-- 11 dual constraints, each a sum of 22 integer products
theorem intCheck_cert22_12 : intCheck 22 12 cert22_12Int cert22_12Den = true := by decide

theorem dualCert_cert22_12 : DualCert 22 2 12 cert22_12 :=
  dualCert_of_intCheck intCheck_cert22_12

theorem A_22_2_12_le : A 22 2 12 ≤ 12 :=
  A_le_of_intCert (p := cert22_12Int) (D := cert22_12Den) (by norm_num) intCheck_cert22_12
    (by decide)

#guard dualCheck 22 2 12 cert22_12
#guard bound 22 2 cert22_12 == 12

/-- Certificate for `n = 23`, `d = 8`, scaled by its common denominator
`450`. Index `0` is unused. -/
def cert23_8Int : List ℤ :=
  [0, 450, 240, 115, 34, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

/-- The common denominator of `cert23_8`. -/
def cert23_8Den : ℤ := 450

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 8/15`, `y 3 = 23/90`, `y 4 = 17/225`,
`y 5 = 1/45`, `y 19 = 1/450`. Derived from the integer form, so the two cannot drift apart. -/
def cert23_8 : ℕ → ℚ := ratOfInt cert23_8Int cert23_8Den

-- 16 dual constraints, each a sum of 23 integer products
theorem intCheck_cert23_8 : intCheck 23 8 cert23_8Int cert23_8Den = true := by decide

theorem dualCert_cert23_8 : DualCert 23 2 8 cert23_8 :=
  dualCert_of_intCheck intCheck_cert23_8

theorem A_23_2_8_le : A 23 2 8 ≤ 2048 :=
  A_le_of_intCert (p := cert23_8Int) (D := cert23_8Den) (by norm_num) intCheck_cert23_8
    (by decide)

#guard dualCheck 23 2 8 cert23_8
#guard bound 23 2 cert23_8 == 2048

/-- Certificate for `n = 23`, `d = 12`, scaled by its common denominator
`1`. Index `0` is unused. -/
def cert23_12Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert23_12`. -/
def cert23_12Den : ℤ := 1

/-- The same certificate as rationals: `y 1 = 1`. Derived from the integer form, so the two
cannot drift apart. -/
def cert23_12 : ℕ → ℚ := ratOfInt cert23_12Int cert23_12Den

-- 12 dual constraints, each a sum of 23 integer products
theorem intCheck_cert23_12 : intCheck 23 12 cert23_12Int cert23_12Den = true := by decide

theorem dualCert_cert23_12 : DualCert 23 2 12 cert23_12 :=
  dualCert_of_intCheck intCheck_cert23_12

theorem A_23_2_12_le : A 23 2 12 ≤ 24 :=
  A_le_of_intCert (p := cert23_12Int) (D := cert23_12Den) (by norm_num) intCheck_cert23_12
    (by decide)

#guard dualCheck 23 2 12 cert23_12
#guard bound 23 2 cert23_12 == 24

/-- Certificate for `n = 24`, `d = 12`, scaled by its common denominator
`12`. Index `0` is unused. -/
def cert24_12Int : List ℤ :=
  [0, 12, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert24_12`. -/
def cert24_12Den : ℤ := 12

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 1/12`. Derived from the integer form,
so the two cannot drift apart. -/
def cert24_12 : ℕ → ℚ := ratOfInt cert24_12Int cert24_12Den

-- 13 dual constraints, each a sum of 24 integer products
theorem intCheck_cert24_12 : intCheck 24 12 cert24_12Int cert24_12Den = true := by decide

theorem dualCert_cert24_12 : DualCert 24 2 12 cert24_12 :=
  dualCert_of_intCheck intCheck_cert24_12

theorem A_24_2_12_le : A 24 2 12 ≤ 48 :=
  A_le_of_intCert (p := cert24_12Int) (D := cert24_12Den) (by norm_num) intCheck_cert24_12
    (by decide)

#guard dualCheck 24 2 12 cert24_12
#guard bound 24 2 cert24_12 == 48

/-- Certificate for `n = 26`, `d = 14`, scaled by its common denominator
`2`. Index `0` is unused. -/
def cert26_14Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert26_14`. -/
def cert26_14Den : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`. Derived from the integer form, so the two
cannot drift apart. -/
def cert26_14 : ℕ → ℚ := ratOfInt cert26_14Int cert26_14Den

-- 13 dual constraints, each a sum of 26 integer products
theorem intCheck_cert26_14 : intCheck 26 14 cert26_14Int cert26_14Den = true := by decide

theorem dualCert_cert26_14 : DualCert 26 2 14 cert26_14 :=
  dualCert_of_intCheck intCheck_cert26_14

theorem A_26_2_14_le : A 26 2 14 ≤ 14 :=
  A_le_of_intCert (p := cert26_14Int) (D := cert26_14Den) (by norm_num) intCheck_cert26_14
    (by decide)

#guard dualCheck 26 2 14 cert26_14
#guard bound 26 2 cert26_14 == 14

/-- Certificate for `n = 27`, `d = 14`, scaled by its common denominator
`1`. Index `0` is unused. -/
def cert27_14Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert27_14`. -/
def cert27_14Den : ℤ := 1

/-- The same certificate as rationals: `y 1 = 1`. Derived from the integer form, so the two
cannot drift apart. -/
def cert27_14 : ℕ → ℚ := ratOfInt cert27_14Int cert27_14Den

-- 14 dual constraints, each a sum of 27 integer products
theorem intCheck_cert27_14 : intCheck 27 14 cert27_14Int cert27_14Den = true := by decide

theorem dualCert_cert27_14 : DualCert 27 2 14 cert27_14 :=
  dualCert_of_intCheck intCheck_cert27_14

theorem A_27_2_14_le : A 27 2 14 ≤ 28 :=
  A_le_of_intCert (p := cert27_14Int) (D := cert27_14Den) (by norm_num) intCheck_cert27_14
    (by decide)

#guard dualCheck 27 2 14 cert27_14
#guard bound 27 2 cert27_14 == 28

/-- Certificate for `n = 28`, `d = 14`, scaled by its common denominator
`14`. Index `0` is unused. -/
def cert28_14Int : List ℤ :=
  [0, 14, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert28_14`. -/
def cert28_14Den : ℤ := 14

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 1/14`. Derived from the integer form,
so the two cannot drift apart. -/
def cert28_14 : ℕ → ℚ := ratOfInt cert28_14Int cert28_14Den

-- 15 dual constraints, each a sum of 28 integer products
theorem intCheck_cert28_14 : intCheck 28 14 cert28_14Int cert28_14Den = true := by decide

theorem dualCert_cert28_14 : DualCert 28 2 14 cert28_14 :=
  dualCert_of_intCheck intCheck_cert28_14

theorem A_28_2_14_le : A 28 2 14 ≤ 56 :=
  A_le_of_intCert (p := cert28_14Int) (D := cert28_14Den) (by norm_num) intCheck_cert28_14
    (by decide)

#guard dualCheck 28 2 14 cert28_14
#guard bound 28 2 cert28_14 == 56

/-!
## Negative controls

A checker that has never rejected anything has not been tested. Both refusals below
are decided by the same kernel arithmetic that accepts the sixteen certificates
above.
-/

/-- A tampered certificate: the first coefficient lowered from `36471` to `36000`.
The dual constraints stop holding and the feasibility check rejects it. -/
def cert22_8Bad : List ℤ :=
  [0, 36000, 18701, 7779, 2346, 515, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75, 0, 0, 0, 0]

theorem intCheck_cert22_8Bad : intCheck 22 8 cert22_8Bad cert22_8Den = false := by
  decide

/-- The strict bound check refuses `2047`. The linear program's value at `n = 23`,
`d = 8` is exactly `2048`, so no dual vector certifies less and the integrality step
of `Floor.lean` buys nothing here -- as it buys nothing anywhere in this file, which
is why every bound above goes through `A_le_of_intCert` instead. -/
theorem intBoundLt_cert23_8_reject : intBoundLt 23 cert23_8Int cert23_8Den 2047 = false := by
  decide

end Delsarte.Certificate
