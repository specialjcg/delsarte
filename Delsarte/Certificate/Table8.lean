/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Floor

/-!
# Certified bounds, part 8: twelve small cells, completed for the table's sake

`Table7` keeps the cells whose bound is at least ten. These twelve are the rest of
the integral ones: bounds between four and eight, where the linear program still has
something to say but not much, and a reader could reasonably reconstruct several of
them by hand from the Plotkin bound.

They are here for one reason, and it is worth stating rather than dressing up as
mathematics. The gap between what this repository proves and what it *could* prove
with the machinery it already has was invisible for as long as the list of claims was
maintained by hand. Filling the integral cells completely, small ones included, is
what makes the remaining gap mean something: what is missing from
`tools/crosscheck_brouwer.py` after this file is missing because the linear program's
optimum is not an integer, not because nobody typed it in.

| bound | | bound | | bound |
|---|---|---|---|---|
| `A(6,2,4) ≤ 4` | | `A(14,2,8) ≤ 8` | | `A(21,2,12) ≤ 8` |
| `A(9,2,6) ≤ 4` | | `A(15,2,10) ≤ 4` | | `A(21,2,14) ≤ 4` |
| `A(10,2,6) ≤ 6` | | `A(18,2,12) ≤ 4` | | `A(24,2,16) ≤ 4` |
| `A(12,2,8) ≤ 4` | | `A(20,2,12) ≤ 6` | | `A(28,2,16) ≤ 8` |

Cells with `d = n` are deliberately absent: `A(n, 2, n) ≤ 2` is a one-line counting
argument and a certificate for it would be theatre. So are the cells the floor route
of `Delsarte/Certificate/Floor.lean` could reach, which all come out at `A ≤ 2`, `4`
or `6` -- the same objection applies to them.
-/

namespace Delsarte.Certificate

open Delsarte

-- kernel reduction of the Krawtchouk table needs more than the default depth
set_option maxRecDepth 100000

-- The `#`-command linter is off here on purpose: these commands are the replay.
set_option linter.hashCommand false

/-- Certificate for `n = 6`, `d = 4`, scaled by its common denominator
`2`. Index `0` is unused. -/
def cert6_4Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0]

/-- The common denominator of `cert6_4`. -/
def cert6_4Den : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`. Derived from the integer form, so the two
cannot drift apart. -/
def cert6_4 : ℕ → ℚ := ratOfInt cert6_4Int cert6_4Den

-- 3 dual constraints, each a sum of 6 integer products
theorem intCheck_cert6_4 : intCheck 6 4 cert6_4Int cert6_4Den = true := by decide

theorem dualCert_cert6_4 : DualCert 6 2 4 cert6_4 :=
  dualCert_of_intCheck intCheck_cert6_4

theorem A_6_2_4_le : A 6 2 4 ≤ 4 :=
  A_le_of_intCert (p := cert6_4Int) (D := cert6_4Den) (by norm_num) intCheck_cert6_4
    (by decide)

#guard dualCheck 6 2 4 cert6_4
#guard bound 6 2 cert6_4 == 4

/-- Certificate for `n = 9`, `d = 6`, scaled by its common denominator
`3`. Index `0` is unused. -/
def cert9_6Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert9_6`. -/
def cert9_6Den : ℤ := 3

/-- The same certificate as rationals: `y 1 = 1/3`. Derived from the integer form, so the two
cannot drift apart. -/
def cert9_6 : ℕ → ℚ := ratOfInt cert9_6Int cert9_6Den

-- 4 dual constraints, each a sum of 9 integer products
theorem intCheck_cert9_6 : intCheck 9 6 cert9_6Int cert9_6Den = true := by decide

theorem dualCert_cert9_6 : DualCert 9 2 6 cert9_6 :=
  dualCert_of_intCheck intCheck_cert9_6

theorem A_9_2_6_le : A 9 2 6 ≤ 4 :=
  A_le_of_intCert (p := cert9_6Int) (D := cert9_6Den) (by norm_num) intCheck_cert9_6
    (by decide)

#guard dualCheck 9 2 6 cert9_6
#guard bound 9 2 cert9_6 == 4

/-- Certificate for `n = 10`, `d = 6`, scaled by its common denominator
`2`. Index `0` is unused. -/
def cert10_6Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert10_6`. -/
def cert10_6Den : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`. Derived from the integer form, so the two
cannot drift apart. -/
def cert10_6 : ℕ → ℚ := ratOfInt cert10_6Int cert10_6Den

-- 5 dual constraints, each a sum of 10 integer products
theorem intCheck_cert10_6 : intCheck 10 6 cert10_6Int cert10_6Den = true := by decide

theorem dualCert_cert10_6 : DualCert 10 2 6 cert10_6 :=
  dualCert_of_intCheck intCheck_cert10_6

theorem A_10_2_6_le : A 10 2 6 ≤ 6 :=
  A_le_of_intCert (p := cert10_6Int) (D := cert10_6Den) (by norm_num) intCheck_cert10_6
    (by decide)

#guard dualCheck 10 2 6 cert10_6
#guard bound 10 2 cert10_6 == 6

/-- Certificate for `n = 12`, `d = 8`, scaled by its common denominator
`4`. Index `0` is unused. -/
def cert12_8Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert12_8`. -/
def cert12_8Den : ℤ := 4

/-- The same certificate as rationals: `y 1 = 1/4`. Derived from the integer form, so the two
cannot drift apart. -/
def cert12_8 : ℕ → ℚ := ratOfInt cert12_8Int cert12_8Den

-- 5 dual constraints, each a sum of 12 integer products
theorem intCheck_cert12_8 : intCheck 12 8 cert12_8Int cert12_8Den = true := by decide

theorem dualCert_cert12_8 : DualCert 12 2 8 cert12_8 :=
  dualCert_of_intCheck intCheck_cert12_8

theorem A_12_2_8_le : A 12 2 8 ≤ 4 :=
  A_le_of_intCert (p := cert12_8Int) (D := cert12_8Den) (by norm_num) intCheck_cert12_8
    (by decide)

#guard dualCheck 12 2 8 cert12_8
#guard bound 12 2 cert12_8 == 4

/-- Certificate for `n = 14`, `d = 8`, scaled by its common denominator
`2`. Index `0` is unused. -/
def cert14_8Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert14_8`. -/
def cert14_8Den : ℤ := 2

/-- The same certificate as rationals: `y 1 = 1/2`. Derived from the integer form, so the two
cannot drift apart. -/
def cert14_8 : ℕ → ℚ := ratOfInt cert14_8Int cert14_8Den

-- 7 dual constraints, each a sum of 14 integer products
theorem intCheck_cert14_8 : intCheck 14 8 cert14_8Int cert14_8Den = true := by decide

theorem dualCert_cert14_8 : DualCert 14 2 8 cert14_8 :=
  dualCert_of_intCheck intCheck_cert14_8

theorem A_14_2_8_le : A 14 2 8 ≤ 8 :=
  A_le_of_intCert (p := cert14_8Int) (D := cert14_8Den) (by norm_num) intCheck_cert14_8
    (by decide)

#guard dualCheck 14 2 8 cert14_8
#guard bound 14 2 cert14_8 == 8

/-- Certificate for `n = 15`, `d = 10`, scaled by its common denominator
`5`. Index `0` is unused. -/
def cert15_10Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert15_10`. -/
def cert15_10Den : ℤ := 5

/-- The same certificate as rationals: `y 1 = 1/5`. Derived from the integer form, so the two
cannot drift apart. -/
def cert15_10 : ℕ → ℚ := ratOfInt cert15_10Int cert15_10Den

-- 6 dual constraints, each a sum of 15 integer products
theorem intCheck_cert15_10 : intCheck 15 10 cert15_10Int cert15_10Den = true := by decide

theorem dualCert_cert15_10 : DualCert 15 2 10 cert15_10 :=
  dualCert_of_intCheck intCheck_cert15_10

theorem A_15_2_10_le : A 15 2 10 ≤ 4 :=
  A_le_of_intCert (p := cert15_10Int) (D := cert15_10Den) (by norm_num) intCheck_cert15_10
    (by decide)

#guard dualCheck 15 2 10 cert15_10
#guard bound 15 2 cert15_10 == 4

/-- Certificate for `n = 18`, `d = 12`, scaled by its common denominator
`6`. Index `0` is unused. -/
def cert18_12Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert18_12`. -/
def cert18_12Den : ℤ := 6

/-- The same certificate as rationals: `y 1 = 1/6`. Derived from the integer form, so the two
cannot drift apart. -/
def cert18_12 : ℕ → ℚ := ratOfInt cert18_12Int cert18_12Den

-- 7 dual constraints, each a sum of 18 integer products
theorem intCheck_cert18_12 : intCheck 18 12 cert18_12Int cert18_12Den = true := by decide

theorem dualCert_cert18_12 : DualCert 18 2 12 cert18_12 :=
  dualCert_of_intCheck intCheck_cert18_12

theorem A_18_2_12_le : A 18 2 12 ≤ 4 :=
  A_le_of_intCert (p := cert18_12Int) (D := cert18_12Den) (by norm_num) intCheck_cert18_12
    (by decide)

#guard dualCheck 18 2 12 cert18_12
#guard bound 18 2 cert18_12 == 4

/-- Certificate for `n = 20`, `d = 12`, scaled by its common denominator
`4`. Index `0` is unused. -/
def cert20_12Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert20_12`. -/
def cert20_12Den : ℤ := 4

/-- The same certificate as rationals: `y 1 = 1/4`. Derived from the integer form, so the two
cannot drift apart. -/
def cert20_12 : ℕ → ℚ := ratOfInt cert20_12Int cert20_12Den

-- 9 dual constraints, each a sum of 20 integer products
theorem intCheck_cert20_12 : intCheck 20 12 cert20_12Int cert20_12Den = true := by decide

theorem dualCert_cert20_12 : DualCert 20 2 12 cert20_12 :=
  dualCert_of_intCheck intCheck_cert20_12

theorem A_20_2_12_le : A 20 2 12 ≤ 6 :=
  A_le_of_intCert (p := cert20_12Int) (D := cert20_12Den) (by norm_num) intCheck_cert20_12
    (by decide)

#guard dualCheck 20 2 12 cert20_12
#guard bound 20 2 cert20_12 == 6

/-- Certificate for `n = 21`, `d = 12`, scaled by its common denominator
`3`. Index `0` is unused. -/
def cert21_12Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert21_12`. -/
def cert21_12Den : ℤ := 3

/-- The same certificate as rationals: `y 1 = 1/3`. Derived from the integer form, so the two
cannot drift apart. -/
def cert21_12 : ℕ → ℚ := ratOfInt cert21_12Int cert21_12Den

-- 10 dual constraints, each a sum of 21 integer products
theorem intCheck_cert21_12 : intCheck 21 12 cert21_12Int cert21_12Den = true := by decide

theorem dualCert_cert21_12 : DualCert 21 2 12 cert21_12 :=
  dualCert_of_intCheck intCheck_cert21_12

theorem A_21_2_12_le : A 21 2 12 ≤ 8 :=
  A_le_of_intCert (p := cert21_12Int) (D := cert21_12Den) (by norm_num) intCheck_cert21_12
    (by decide)

#guard dualCheck 21 2 12 cert21_12
#guard bound 21 2 cert21_12 == 8

/-- Certificate for `n = 21`, `d = 14`, scaled by its common denominator
`7`. Index `0` is unused. -/
def cert21_14Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert21_14`. -/
def cert21_14Den : ℤ := 7

/-- The same certificate as rationals: `y 1 = 1/7`. Derived from the integer form, so the two
cannot drift apart. -/
def cert21_14 : ℕ → ℚ := ratOfInt cert21_14Int cert21_14Den

-- 8 dual constraints, each a sum of 21 integer products
theorem intCheck_cert21_14 : intCheck 21 14 cert21_14Int cert21_14Den = true := by decide

theorem dualCert_cert21_14 : DualCert 21 2 14 cert21_14 :=
  dualCert_of_intCheck intCheck_cert21_14

theorem A_21_2_14_le : A 21 2 14 ≤ 4 :=
  A_le_of_intCert (p := cert21_14Int) (D := cert21_14Den) (by norm_num) intCheck_cert21_14
    (by decide)

#guard dualCheck 21 2 14 cert21_14
#guard bound 21 2 cert21_14 == 4

/-- Certificate for `n = 24`, `d = 16`, scaled by its common denominator
`8`. Index `0` is unused. -/
def cert24_16Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert24_16`. -/
def cert24_16Den : ℤ := 8

/-- The same certificate as rationals: `y 1 = 1/8`. Derived from the integer form, so the two
cannot drift apart. -/
def cert24_16 : ℕ → ℚ := ratOfInt cert24_16Int cert24_16Den

-- 9 dual constraints, each a sum of 24 integer products
theorem intCheck_cert24_16 : intCheck 24 16 cert24_16Int cert24_16Den = true := by decide

theorem dualCert_cert24_16 : DualCert 24 2 16 cert24_16 :=
  dualCert_of_intCheck intCheck_cert24_16

theorem A_24_2_16_le : A 24 2 16 ≤ 4 :=
  A_le_of_intCert (p := cert24_16Int) (D := cert24_16Den) (by norm_num) intCheck_cert24_16
    (by decide)

#guard dualCheck 24 2 16 cert24_16
#guard bound 24 2 cert24_16 == 4

/-- Certificate for `n = 28`, `d = 16`, scaled by its common denominator
`4`. Index `0` is unused. -/
def cert28_16Int : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The common denominator of `cert28_16`. -/
def cert28_16Den : ℤ := 4

/-- The same certificate as rationals: `y 1 = 1/4`. Derived from the integer form, so the two
cannot drift apart. -/
def cert28_16 : ℕ → ℚ := ratOfInt cert28_16Int cert28_16Den

-- 13 dual constraints, each a sum of 28 integer products
theorem intCheck_cert28_16 : intCheck 28 16 cert28_16Int cert28_16Den = true := by decide

theorem dualCert_cert28_16 : DualCert 28 2 16 cert28_16 :=
  dualCert_of_intCheck intCheck_cert28_16

theorem A_28_2_16_le : A 28 2 16 ≤ 8 :=
  A_le_of_intCert (p := cert28_16Int) (D := cert28_16Den) (by norm_num) intCheck_cert28_16
    (by decide)

#guard dualCheck 28 2 16 cert28_16
#guard bound 28 2 cert28_16 == 8

/-!
## Negative control

The bound is small here, which makes the refusal cheap to read: `A(21,2,12) ≤ 8` is
certified, and `7` is not, by the same decision procedure.
-/

/-- The strict bound check refuses `7`. The linear program's value at `n = 21`,
`d = 12` is exactly `8`, so no dual vector certifies less. -/
theorem intBoundLt_cert21_12_reject : intBoundLt 21 cert21_12Int cert21_12Den 7 = false := by
  decide

end Delsarte.Certificate
