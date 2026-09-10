/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Integer

/-!
# Certified bounds, part 5: three bounds from `n = 26` to `n = 32`

Parts 1 to 3 stop at `n = 24` because they were written when one certificate cost
tens of seconds of `norm_num` on exact rational arithmetic. Since
`Delsarte/Certificate/Integer.lean` the check is kernel reduction in `ℤ` and costs
milliseconds, so the table can afford to say more. Nothing else changed: the solver
in `tools/delsarte_lp.py` is still a source of candidates and appears in no proof.

| bound | attained by | Hamming bound |
|---|---|---|
| `A(26,2,5) ≤ 163840` | *not claimed* | 190650 |
| `A(31,2,3) ≤ 67108864` | perfect Hamming `[31,26,3]` | 67108864 |
| `A(32,2,4) ≤ 67108864` | extended Hamming `[32,26,4]` | 130150524 |

Only the upper halves are proved. The "attained by" column *names a construction*
whose word count matches the bound, which is why the value is known — but no code is
constructed anywhere in this repository, so no line may be read as an equality.
`A(26,2,5)` has no construction cited, so nothing at all is claimed about
attainment there; the bound stands alone.

`A(31,2,3)` is the one row in this repository where the linear program earns
**nothing**: its bound equals the sphere-packing bound, to the unit. That is what
"perfect code" means — the Hamming spheres tile the cube, and elementary counting is
already exact. It is kept for that reason, next to `A(32,2,4)`, where the same family
gains a factor of almost two over counting.
-/

namespace Delsarte.Certificate

open Delsarte

-- kernel reduction of the Krawtchouk table needs more than the default depth
set_option maxRecDepth 100000

-- The `#`-command linter is off here on purpose: these commands are the replay. They
-- run the compiled rational checker on the *binomial* definition of `krawtchouk`,
-- while the proofs go through the integer difference table.
set_option linter.hashCommand false

/-- Certificate for `n = 26`, `d = 5`, scaled by its common denominator
`960`. Index `0` is unused. -/
def cert26_5Int : List ℤ :=
  [0, 700, 490, 336, 216, 135, 75, 40, 16, 6, 0, 0, 0, 1, 1, 0, 0, 0, 6, 16, 40, 75, 135, 216,
   336, 490, 700]

/-- The common denominator of `cert26_5`. -/
def cert26_5Den : ℤ := 960

/-- The same certificate as rationals: `y 1 = 35/48`, `y 2 = 49/96`, `y 3 = 7/20`, `y 4 =
9/40`, `y 5 = 9/64`, `y 6 = 5/64`, `y 7 = 1/24`, `y 8 = 1/60`, `y 9 = 1/160`, `y 13 = 1/960`,
`y 14 = 1/960`, `y 18 = 1/160`, `y 19 = 1/60`, `y 20 = 1/24`, `y 21 = 5/64`, `y 22 = 9/64`, `y
23 = 9/40`, `y 24 = 7/20`, `y 25 = 49/96`, `y 26 = 35/48`. Derived from the integer form, so
the two cannot drift apart. -/
def cert26_5 : ℕ → ℚ := ratOfInt cert26_5Int cert26_5Den

-- 22 dual constraints, each a sum of 26 integer products
theorem intCheck_cert26_5 : intCheck 26 5 cert26_5Int cert26_5Den = true := by decide

theorem dualCert_cert26_5 : DualCert 26 2 5 cert26_5 :=
  dualCert_of_intCheck intCheck_cert26_5

theorem A_26_2_5_le : A 26 2 5 ≤ 163840 :=
  A_le_of_intCert (p := cert26_5Int) (D := cert26_5Den) (by norm_num) intCheck_cert26_5
    (by decide)

#guard dualCheck 26 2 5 cert26_5
#guard bound 26 2 cert26_5 == 163840
/-- Certificate for `n = 31`, `d = 3`, scaled by its common denominator
`420`. Index `0` is unused. -/
def cert31_3Int : List ℤ :=
  [0, 420, 322, 315, 237, 225, 165, 150, 106, 90, 60, 45, 27, 15, 7, 0, 0, 0, 6, 15, 25, 45, 57,
   90, 102, 150, 160, 225, 231, 315, 315, 420]

/-- The common denominator of `cert31_3`. -/
def cert31_3Den : ℤ := 420

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 23/30`, `y 3 = 3/4`, `y 4 = 79/140`,
`y 5 = 15/28`, `y 6 = 11/28`, `y 7 = 5/14`, `y 8 = 53/210`, `y 9 = 3/14`, `y 10 = 1/7`, `y 11 =
3/28`, `y 12 = 9/140`, `y 13 = 1/28`, `y 14 = 1/60`, `y 18 = 1/70`, `y 19 = 1/28`, `y 20 =
5/84`, `y 21 = 3/28`, `y 22 = 19/140`, `y 23 = 3/14`, `y 24 = 17/70`, `y 25 = 5/14`, `y 26 =
8/21`, `y 27 = 15/28`, `y 28 = 11/20`, `y 29 = 3/4`, `y 30 = 3/4`, `y 31 = 1`. Derived from the
integer form, so the two cannot drift apart. -/
def cert31_3 : ℕ → ℚ := ratOfInt cert31_3Int cert31_3Den

-- 29 dual constraints, each a sum of 31 integer products
theorem intCheck_cert31_3 : intCheck 31 3 cert31_3Int cert31_3Den = true := by decide

theorem dualCert_cert31_3 : DualCert 31 2 3 cert31_3 :=
  dualCert_of_intCheck intCheck_cert31_3

theorem A_31_2_3_le : A 31 2 3 ≤ 67108864 :=
  A_le_of_intCert (p := cert31_3Int) (D := cert31_3Den) (by norm_num) intCheck_cert31_3
    (by decide)

#guard dualCheck 31 2 3 cert31_3
#guard bound 31 2 cert31_3 == 67108864
/-- Certificate for `n = 32`, `d = 4`, scaled by its common denominator
`50624`. Index `0` is unused. -/
def cert32_4Int : List ℤ :=
  [0, 50624, 38759, 37730, 27482, 26078, 17758, 16408, 10120, 9064, 4741, 4066, 1506, 1182, 84,
   0, 0, 0, 707, 626, 1658, 1358, 2378, 1784, 2536, 1672, 2017, 1042, 994, 238, 0, 0, 0]

/-- The common denominator of `cert32_4`. -/
def cert32_4Den : ℤ := 50624

/-- The same certificate as rationals: `y 1 = 1`, `y 2 = 49/64`, `y 3 = 2695/3616`, `y 4 =
1963/3616`, `y 5 = 13039/25312`, `y 6 = 8879/25312`, `y 7 = 293/904`, `y 8 = 1265/6328`, `y 9 =
1133/6328`, `y 10 = 4741/50624`, `y 11 = 2033/25312`, `y 12 = 753/25312`, `y 13 = 591/25312`,
`y 14 = 3/1808`, `y 18 = 101/7232`, `y 19 = 313/25312`, `y 20 = 829/25312`, `y 21 = 97/3616`,
`y 22 = 1189/25312`, `y 23 = 223/6328`, `y 24 = 317/6328`, `y 25 = 209/6328`, `y 26 =
2017/50624`, `y 27 = 521/25312`, `y 28 = 71/3616`, `y 29 = 17/3616`. Derived from the integer
form, so the two cannot drift apart. -/
def cert32_4 : ℕ → ℚ := ratOfInt cert32_4Int cert32_4Den

-- 29 dual constraints, each a sum of 32 integer products
theorem intCheck_cert32_4 : intCheck 32 4 cert32_4Int cert32_4Den = true := by decide

theorem dualCert_cert32_4 : DualCert 32 2 4 cert32_4 :=
  dualCert_of_intCheck intCheck_cert32_4

theorem A_32_2_4_le : A 32 2 4 ≤ 67108864 :=
  A_le_of_intCert (p := cert32_4Int) (D := cert32_4Den) (by norm_num) intCheck_cert32_4
    (by decide)

#guard dualCheck 32 2 4 cert32_4
#guard bound 32 2 cert32_4 == 67108864

end Delsarte.Certificate
