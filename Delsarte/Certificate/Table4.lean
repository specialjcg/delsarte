/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Integer

/-!
# Certified bounds, part 4: five bounds from `n = 16` to `n = 22`

Parts 1 to 3 stop at `n = 24` because they were written when one certificate cost
tens of seconds of `norm_num` on exact rational arithmetic. Since
`Delsarte/Certificate/Integer.lean` the check is kernel reduction in `ℤ` and costs
milliseconds, so the table can afford to say more. Nothing else changed: the solver
in `tools/delsarte_lp.py` is still a source of candidates and appears in no proof.

| bound | attained by | Hamming bound |
|---|---|---|
| `A(16,2,4) ≤ 2048` | extended Hamming `[16,11,4]` | 3855 |
| `A(16,2,6) ≤ 256` | Nordstrom–Robinson, nonlinear | 478 |
| `A(16,2,8) ≤ 32` | Reed–Muller `RM(1,4) = [16,5,8]` | 94 |
| `A(21,2,7) ≤ 1024` | Golay shortened twice, `[21,10,7]` | 1342 |
| `A(22,2,7) ≤ 2048` | Golay shortened once, `[22,11,7]` | 2337 |

Only the upper halves are proved. The "attained by" column *names a construction*
whose word count matches the bound, which is why the value is known — but no code is
constructed anywhere in this repository, so no line may be read as an equality.

Every row here beats the sphere-packing bound, and `A(16,2,6)` is the one whose
optimal code is *not* linear — the linear program never assumed it was.
-/

namespace Delsarte.Certificate

open Delsarte

-- kernel reduction of the Krawtchouk table needs more than the default depth
set_option maxRecDepth 100000

-- The `#`-command linter is off here on purpose: these commands are the replay. They
-- run the compiled rational checker on the *binomial* definition of `krawtchouk`,
-- while the proofs go through the integer difference table.
set_option linter.hashCommand false

/-- Certificate for `n = 16`, `d = 4`, scaled by its common denominator
`336`. Index `0` is unused. -/
def cert16_4Int : List ℤ :=
  [0, 336, 189, 162, 66, 46, 6, 0, 0, 0, 15, 10, 18, 6, 0, 0, 0]

/-- The common denominator of `cert16_4`. -/
def cert16_4Den : ℤ := 336

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 9/16`, `y 3 = 27/56`, `y 4 = 11/56`,
`y 5 = 23/168`, `y 6 = 1/56`, `y 10 = 5/112`, `y 11 = 5/168`, `y 12 = 3/56`, `y 13 = 1/56`.
Derived from the integer form, so the two cannot drift apart. -/
def cert16_4 : ℕ → ℚ := ratOfInt cert16_4Int cert16_4Den

-- 13 dual constraints, each a sum of 16 integer products
theorem intCheck_cert16_4 : intCheck 16 4 cert16_4Int cert16_4Den = true := by decide

theorem dualCert_cert16_4 : DualCert 16 2 4 cert16_4 :=
  dualCert_of_intCheck intCheck_cert16_4

theorem A_16_2_4_le : A 16 2 4 ≤ 2048 :=
  A_le_of_intCert (p := cert16_4Int) (D := cert16_4Den) (by norm_num) intCheck_cert16_4
    (by decide)

#guard dualCheck 16 2 4 cert16_4
#guard bound 16 2 cert16_4 == 2048
/-- Certificate for `n = 16`, `d = 6`, scaled by its common denominator
`24080`. Index `0` is unused. -/
def cert16_6Int : List ℤ :=
  [0, 17325, 7224, 3592, 954, 90, 0, 0, 0, 35, 0, 0, 250, 0, 0, 0, 0]

/-- The common denominator of `cert16_6`. -/
def cert16_6Den : ℤ := 24080

/-- The same certificate as rationals: `y 1 = 495/688`, `y 2 = 3/10`, `y 3 = 449/3010`, `y 4 =
477/12040`, `y 5 = 9/2408`, `y 9 = 1/688`, `y 12 = 25/2408`. Derived from the integer form, so
the two cannot drift apart. -/
def cert16_6 : ℕ → ℚ := ratOfInt cert16_6Int cert16_6Den

-- 11 dual constraints, each a sum of 16 integer products
theorem intCheck_cert16_6 : intCheck 16 6 cert16_6Int cert16_6Den = true := by decide

theorem dualCert_cert16_6 : DualCert 16 2 6 cert16_6 :=
  dualCert_of_intCheck intCheck_cert16_6

theorem A_16_2_6_le : A 16 2 6 ≤ 256 :=
  A_le_of_intCert (p := cert16_6Int) (D := cert16_6Den) (by norm_num) intCheck_cert16_6
    (by decide)

#guard dualCheck 16 2 6 cert16_6
#guard bound 16 2 cert16_6 == 256
/-- Certificate for `n = 16`, `d = 8`, scaled by its common denominator
`8`. Index `0` is unused. -/
def cert16_8Int : List ℤ :=
  [0, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert16_8`. -/
def cert16_8Den : ℤ := 8

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 1/8`. Derived from the integer form,
so the two cannot drift apart. -/
def cert16_8 : ℕ → ℚ := ratOfInt cert16_8Int cert16_8Den

-- 9 dual constraints, each a sum of 16 integer products
theorem intCheck_cert16_8 : intCheck 16 8 cert16_8Int cert16_8Den = true := by decide

theorem dualCert_cert16_8 : DualCert 16 2 8 cert16_8 :=
  dualCert_of_intCheck intCheck_cert16_8

theorem A_16_2_8_le : A 16 2 8 ≤ 32 :=
  A_le_of_intCert (p := cert16_8Int) (D := cert16_8Den) (by norm_num) intCheck_cert16_8
    (by decide)

#guard dualCheck 16 2 8 cert16_8
#guard bound 16 2 cert16_8 == 32
/-- Certificate for `n = 21`, `d = 7`, scaled by its common denominator
`364`. Index `0` is unused. -/
def cert21_7Int : List ℤ :=
  [0, 284, 154, 68, 21, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 28, 99, 259]

/-- The common denominator of `cert21_7`. -/
def cert21_7Den : ℤ := 364

/-- The same certificate as rationals: `y 1 = 71/91`, `y 2 = 11/26`, `y 3 = 17/91`, `y 4 =
3/52`, `y 5 = 5/364`, `y 18 = 3/182`, `y 19 = 1/13`, `y 20 = 99/364`, `y 21 = 37/52`. Derived
from the integer form, so the two cannot drift apart. -/
def cert21_7 : ℕ → ℚ := ratOfInt cert21_7Int cert21_7Den

-- 15 dual constraints, each a sum of 21 integer products
theorem intCheck_cert21_7 : intCheck 21 7 cert21_7Int cert21_7Den = true := by decide

theorem dualCert_cert21_7 : DualCert 21 2 7 cert21_7 :=
  dualCert_of_intCheck intCheck_cert21_7

theorem A_21_2_7_le : A 21 2 7 ≤ 1024 :=
  A_le_of_intCert (p := cert21_7Int) (D := cert21_7Den) (by norm_num) intCheck_cert21_7
    (by decide)

#guard dualCheck 21 2 7 cert21_7
#guard bound 21 2 cert21_7 == 1024
/-- Certificate for `n = 22`, `d = 7`, scaled by its common denominator
`182`. Index `0` is unused. -/
def cert22_7Int : List ℤ :=
  [0, 182, 102, 52, 16, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 22, 77, 182]

/-- The common denominator of `cert22_7`. -/
def cert22_7Den : ℤ := 182

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 51/91`, `y 3 = 2/7`, `y 4 = 8/91`, `y
5 = 5/182`, `y 19 = 3/91`, `y 20 = 11/91`, `y 21 = 11/26`, `y 22 = 1`. Derived from the integer
form, so the two cannot drift apart. -/
def cert22_7 : ℕ → ℚ := ratOfInt cert22_7Int cert22_7Den

-- 16 dual constraints, each a sum of 22 integer products
theorem intCheck_cert22_7 : intCheck 22 7 cert22_7Int cert22_7Den = true := by decide

theorem dualCert_cert22_7 : DualCert 22 2 7 cert22_7 :=
  dualCert_of_intCheck intCheck_cert22_7

theorem A_22_2_7_le : A 22 2 7 ≤ 2048 :=
  A_le_of_intCert (p := cert22_7Int) (D := cert22_7Den) (by norm_num) intCheck_cert22_7
    (by decide)

#guard dualCheck 22 2 7 cert22_7
#guard bound 22 2 cert22_7 == 2048

end Delsarte.Certificate
