/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Floor
import Delsarte.Code.Shorten

/-!
# Open entries of the binary table

The certificates in `Table1` to `Table5` all bound entries of `A(n, 2, d)` whose
exact value is known. This module is the first that does not: every bound below
sits on a row of the binary table where the literature still quotes an interval.

Two things are new here.

* The bound check is the strict one from `Delsarte/Certificate/Floor.lean`. The
  linear program's optimum at `n = 18`, `d = 4` is `32768 / 5 = 6553.6`, and no dual
  vector reaches `6553` — that step is the integrality of `A`, not the program.
* Four of the bounds are *composed*: the program certifies a shorter length, and
  `A_succ_le` from `Delsarte/Code/Shorten.lean` doubles it. On these rows the
  composition is strictly stronger than the program alone.

| bound | program alone | composed | best known |
|---|---|---|---|
| `A(18,2,4) ≤ 6553` | 6553 | — | 6552 |
| `A(19,2,4) ≤ 13106` | 13107 | **13106** | 13104 |
| `A(20,2,4) ≤ 26212` | 26214 | **26212** | 26168 |
| `A(23,2,4) ≤ 174762` | 174762 | — | 172361 |
| `A(24,2,4) ≤ 349524` | 349525 | **349524** | 344308 |
| `A(26,2,4) ≤ 1198372` | 1198372 | — | 1198368 |
| `A(27,2,4) ≤ 2396744` | 2396745 | **2396744** | 2396736 |
| `A(28,2,4) ≤ 4793488` | 4793490 | **4793488** | 4792950 |
| `A(28,2,12) ≤ 288` | 288 | — | 288 |

The "best known" column is quoted from the literature and proved nowhere here.
Read the table honestly: **no bound below improves on the literature.** Eight of
the nine are weaker, by amounts ranging from one codeword to five hundred. The
last, `A(28,2,12) ≤ 288`, matches the best known upper bound on an entry that is
still open — its lower bound is 178 — and that is the only row where this
repository says as much as the literature about an unsolved entry.

What is gained is not a better number. It is that these particular bounds are now
checked by the kernel, on integer arithmetic, from a certificate that can be
replayed. The solver that produced the dual vectors appears in no proof.

The gap that remains is not small and should not be dressed up: the literature's
bounds on these rows come from strengthenings of the linear program — Schrijver's
semidefinite relaxation above all — that are not formalised here.
-/

namespace Delsarte.Certificate

open Delsarte

-- kernel reduction of the Krawtchouk table needs more than the default depth
set_option maxRecDepth 100000

-- The `#`-command linter is off here on purpose: these commands are the replay. They
-- run the compiled rational checker on the *binomial* definition of `krawtchouk`,
-- while the proofs go through the integer difference table.
set_option linter.hashCommand false

/-- Certificate for `n = 28`, `d = 12`, scaled by its common denominator
`6384`. Index `0` is unused. Linear-programming optimum `288`. -/
def cert28_12Int : List ℤ :=
  [0, 4389, 1064, 264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135, 0, 0,
   0]

/-- The common denominator of `cert28_12`. -/
def cert28_12Den : ℤ := 6384

/-- The same certificate as rationals: `y 1 = 11/16`, `y 2 = 1/6`, `y 3 = 11/266`, `y 25 =
45/2128`. Derived from the integer form, so the two cannot drift apart. -/
def cert28_12 : ℕ → ℚ := ratOfInt cert28_12Int cert28_12Den

-- 17 dual constraints, each a sum of 28 integer products
theorem intCheck_cert28_12 : intCheck 28 12 cert28_12Int cert28_12Den = true := by decide

theorem dualCert_cert28_12 : DualCert 28 2 12 cert28_12 :=
  dualCert_of_intCheck intCheck_cert28_12

theorem A_28_2_12_le : A 28 2 12 ≤ 288 :=
  A_le_of_intCertLt (p := cert28_12Int) (D := cert28_12Den) (by norm_num) intCheck_cert28_12
    (by decide)

#guard dualCheck 28 2 12 cert28_12
#guard bound 28 2 cert28_12 == 288

/-- Certificate for `n = 18`, `d = 4`, scaled by its common denominator
`14280`. Index `0` is unused. Linear-programming optimum `32768/5`. -/
def cert18_4Int : List ℤ :=
  [0, 11424, 8512, 6083, 3892, 2348, 1096, 455, 0, 0, 0, 259, 332, 508, 392, 343, 56, 0, 0]

/-- The common denominator of `cert18_4`. -/
def cert18_4Den : ℤ := 14280

/-- The same certificate as rationals: `y 1 = 4/5`, `y 2 = 152/255`, `y 3 = 869/2040`, `y 4 =
139/510`, `y 5 = 587/3570`, `y 6 = 137/1785`, `y 7 = 13/408`, `y 11 = 37/2040`, `y 12 =
83/3570`, `y 13 = 127/3570`, `y 14 = 7/255`, `y 15 = 49/2040`, `y 16 = 1/255`. Derived from the
integer form, so the two cannot drift apart. -/
def cert18_4 : ℕ → ℚ := ratOfInt cert18_4Int cert18_4Den

-- 15 dual constraints, each a sum of 18 integer products
theorem intCheck_cert18_4 : intCheck 18 4 cert18_4Int cert18_4Den = true := by decide

theorem dualCert_cert18_4 : DualCert 18 2 4 cert18_4 :=
  dualCert_of_intCheck intCheck_cert18_4

theorem A_18_2_4_le : A 18 2 4 ≤ 6553 :=
  A_le_of_intCertLt (p := cert18_4Int) (D := cert18_4Den) (by norm_num) intCheck_cert18_4
    (by decide)

#guard dualCheck 18 2 4 cert18_4
#guard bound 18 2 cert18_4 == 32768/5

/-- Certificate for `n = 23`, `d = 4`, scaled by its common denominator
`31185`. Index `0` is unused. Linear-programming optimum `524288/3`. -/
def cert23_4Int : List ℤ :=
  [0, 26675, 21200, 16920, 12258, 8964, 5616, 3584, 1631, 777, 0, 0, 0, 410, 728, 1104, 1341,
   1359, 1296, 872, 590, 0, 0, 0]

/-- The common denominator of `cert23_4`. -/
def cert23_4Den : ℤ := 31185

/-- The same certificate as rationals: `y 1 = 485/567`, `y 2 = 4240/6237`, `y 3 = 376/693`, `y
4 = 454/1155`, `y 5 = 332/1155`, `y 6 = 208/1155`, `y 7 = 512/4455`, `y 8 = 233/4455`, `y 9 =
37/1485`, `y 13 = 82/6237`, `y 14 = 104/4455`, `y 15 = 368/10395`, `y 16 = 149/3465`, `y 17 =
151/3465`, `y 18 = 16/385`, `y 19 = 872/31185`, `y 20 = 118/6237`. Derived from the integer
form, so the two cannot drift apart. -/
def cert23_4 : ℕ → ℚ := ratOfInt cert23_4Int cert23_4Den

-- 20 dual constraints, each a sum of 23 integer products
theorem intCheck_cert23_4 : intCheck 23 4 cert23_4Int cert23_4Den = true := by decide

theorem dualCert_cert23_4 : DualCert 23 2 4 cert23_4 :=
  dualCert_of_intCheck intCheck_cert23_4

theorem A_23_2_4_le : A 23 2 4 ≤ 174762 :=
  A_le_of_intCertLt (p := cert23_4Int) (D := cert23_4Den) (by norm_num) intCheck_cert23_4
    (by decide)

#guard dualCheck 23 2 4 cert23_4
#guard bound 23 2 cert23_4 == 524288/3

/-- Certificate for `n = 26`, `d = 4`, scaled by its common denominator
`60060`. Index `0` is unused. Linear-programming optimum `8388608/7`. -/
def cert26_4Int : List ℤ :=
  [0, 51480, 42768, 34903, 27368, 21016, 15216, 10719, 6804, 4144, 1952, 847, 0, 0, 0, 583, 908,
   1576, 1776, 2151, 1944, 1864, 1232, 847, 132, 0, 0]

/-- The common denominator of `cert26_4`. -/
def cert26_4Den : ℤ := 60060

/-- The same certificate as rationals: `y 1 = 6/7`, `y 2 = 324/455`, `y 3 = 3173/5460`, `y 4 =
622/1365`, `y 5 = 5254/15015`, `y 6 = 1268/5005`, `y 7 = 3573/20020`, `y 8 = 81/715`, `y 9 =
148/2145`, `y 10 = 488/15015`, `y 11 = 11/780`, `y 15 = 53/5460`, `y 16 = 227/15015`, `y 17 =
394/15015`, `y 18 = 148/5005`, `y 19 = 717/20020`, `y 20 = 162/5005`, `y 21 = 466/15015`, `y 22
= 4/195`, `y 23 = 11/780`, `y 24 = 1/455`. Derived from the integer form, so the two cannot
drift apart. -/
def cert26_4 : ℕ → ℚ := ratOfInt cert26_4Int cert26_4Den

-- 23 dual constraints, each a sum of 26 integer products
theorem intCheck_cert26_4 : intCheck 26 4 cert26_4Int cert26_4Den = true := by decide

theorem dualCert_cert26_4 : DualCert 26 2 4 cert26_4 :=
  dualCert_of_intCheck intCheck_cert26_4

theorem A_26_2_4_le : A 26 2 4 ≤ 1198372 :=
  A_le_of_intCertLt (p := cert26_4Int) (D := cert26_4Den) (by norm_num) intCheck_cert26_4
    (by decide)

#guard dualCheck 26 2 4 cert26_4
#guard bound 26 2 cert26_4 == 8388608/7

/-!
## Composition with shortening

`A_succ_le` says a code of length `n + 1` splits into two codes of length `n`
with the same minimum distance. Doubling a certified bound at length `n` is
therefore valid at length `n + 1`, and on these four rows it lands below what the
linear program reaches on its own.
-/

/-- `2 × 6553 = 13106`, one below the program's own `13107` at this length. -/
theorem A_19_2_4_le : A 19 2 4 ≤ 13106 := by
  have h : A 19 2 4 ≤ 2 * A 18 2 4 := A_succ_le 18 2 4
  have hb := A_18_2_4_le
  omega

/-- `2 × 13106 = 26212`, two below the program's `26214`. -/
theorem A_20_2_4_le : A 20 2 4 ≤ 26212 := by
  have h : A 20 2 4 ≤ 2 * A 19 2 4 := A_succ_le 19 2 4
  have hb := A_19_2_4_le
  omega

/-- `2 × 174762 = 349524`, one below the program's `349525`. -/
theorem A_24_2_4_le : A 24 2 4 ≤ 349524 := by
  have h : A 24 2 4 ≤ 2 * A 23 2 4 := A_succ_le 23 2 4
  have hb := A_23_2_4_le
  omega

/-- `2 × 1198372 = 2396744`, one below the program's `2396745`. -/
theorem A_27_2_4_le : A 27 2 4 ≤ 2396744 := by
  have h : A 27 2 4 ≤ 2 * A 26 2 4 := A_succ_le 26 2 4
  have hb := A_26_2_4_le
  omega

/-- `2 × 2396744 = 4793488`, two below the program's `4793490`. -/
theorem A_28_2_4_le : A 28 2 4 ≤ 4793488 := by
  have h : A 28 2 4 ≤ 2 * A 27 2 4 := A_succ_le 27 2 4
  have hb := A_27_2_4_le
  omega

/-!
## Negative controls

A checker that has never rejected anything has not been tested. Three refusals,
each decided by the same kernel arithmetic that accepts the certificates above.
-/

/-- The strict bound check refuses `287`. The linear program's value at
`n = 28`, `d = 12` is exactly `288`, so no dual vector certifies less, and the
integrality step buys nothing here. -/
theorem intBoundLt_cert28_12_reject : intBoundLt 28 cert28_12Int cert28_12Den 287 = false := by
  decide

/-- The strict bound check refuses `6552`: rounding `6553.6` down stops at
`6553`, and the checker will not be pushed further. -/
theorem intBoundLt_cert18_4_reject : intBoundLt 18 cert18_4Int cert18_4Den 6552 = false := by
  decide

/-- A tampered certificate: the first coefficient lowered from `4389` to `4000`.
The dual constraints stop holding and the feasibility check rejects it. -/
def cert28_12Bad : List ℤ :=
  [0, 4000, 1064, 264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135, 0, 0,
   0]

theorem intCheck_cert28_12Bad : intCheck 28 12 cert28_12Bad cert28_12Den = false := by
  decide

end Delsarte.Certificate
