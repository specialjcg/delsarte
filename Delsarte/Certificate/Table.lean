/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Bounds

/-!
# A table of certified bounds on `A(n, 2, d)`

Same machinery as `Delsarte.Certificate.Bounds`, applied in bulk. Every vector
below is the optimum of the linear program, computed by `tools/delsarte_lp.py`
and re-verified here; the solver is a source of candidates and appears in no
proof.

The declarations in this file are **generated** by `delsarte_lp.emit_lean` rather
than typed. Transcribing a dozen certificates by hand is a good way to introduce a
typo that no theorem would catch — a wrong `y` is usually infeasible, but it can
also be feasible and prove a *different*, weaker bound without anyone noticing.
Generation removes that step; Lean re-checks the result, and
`Delsarte/Certificate/Files.lean` pins each `.cert` file to the definition here.

| bound | true value | Hamming bound |
|---|---|---|
| `A(6,2,3) ≤ 8` | 8 | 9 |
| `A(7,2,4) ≤ 8` | 8 | 16 |
| `A(8,2,4) ≤ 16` | 16 | 28 |
| `A(10,2,5) ≤ 12` | 12 | 18 |
| `A(11,2,5) ≤ 24` | 24 | 30 |
| `A(12,2,5) ≤ 40` | 32 | 51 |
| `A(13,2,3) ≤ 512` | 512 | 585 |
| `A(14,2,5) ≤ 128` | 128 | 154 |
| `A(15,2,5) ≤ 256` | 256 | 270 |
| `A(12,2,6) ≤ 24` | 24 | 51 |
| `A(15,2,6) ≤ 128` | 128 | 270 |
| `A(24,2,8) ≤ 4096` | 4096 | 7216 |

Only upper halves. No code is constructed anywhere in this repository, so no line
of this table may be read as an equality — the "true value" column is quoted from
the literature, not proved here.

`A(12,2,5) ≤ 40` is the entry that is *not* tight, and it is kept for that reason:
the true value is 32, and the plain Delsarte linear program does not reach it.
A table showing only its successes would be advertising.

Every other row is tight, and every row beats the sphere-packing bound in the
last column — which is the point. These are bounds the linear program earns and
elementary counting does not.
-/

namespace Delsarte.Certificate

open Delsarte

/-- Certificate for `n = 6`, `d = 3`; the linear program's optimum. -/
def cert6_3 : ℕ → ℚ
  | 1 => 1
  | 6 => 1
  | _ => 0

set_option maxHeartbeats 800000 in
-- 4 dual constraints, each a sum of 6 Krawtchouk values
theorem dualCert_cert6_3 : DualCert 6 2 3 cert6_3 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert6_3]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 6 2 _ _ (by norm_num)] <;>
      norm_num [cert6_3, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 800000 in
-- the same unfolding, at i = 0
theorem bound_cert6_3 : bound 6 2 cert6_3 = 8 := by
  rw [bound_eq_rec]
  norm_num [cert6_3, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_6_2_3_le : A 6 2 3 ≤ 8 :=
  A_le_of_dualCert (by norm_num) dualCert_cert6_3 (by rw [bound_cert6_3]; norm_num)


/-- Certificate for `n = 7`, `d = 4`; the linear program's optimum. -/
def cert7_4 : ℕ → ℚ
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 800000 in
-- 4 dual constraints, each a sum of 7 Krawtchouk values
theorem dualCert_cert7_4 : DualCert 7 2 4 cert7_4 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert7_4]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 7 2 _ _ (by norm_num)] <;>
      norm_num [cert7_4, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 800000 in
-- the same unfolding, at i = 0
theorem bound_cert7_4 : bound 7 2 cert7_4 = 8 := by
  rw [bound_eq_rec]
  norm_num [cert7_4, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_7_2_4_le : A 7 2 4 ≤ 8 :=
  A_le_of_dualCert (by norm_num) dualCert_cert7_4 (by rw [bound_cert7_4]; norm_num)


/-- Certificate for `n = 8`, `d = 4`; the linear program's optimum. -/
def cert8_4 : ℕ → ℚ
  | 1 => 1
  | 2 => 1/4
  | _ => 0

set_option maxHeartbeats 800000 in
-- 5 dual constraints, each a sum of 8 Krawtchouk values
theorem dualCert_cert8_4 : DualCert 8 2 4 cert8_4 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert8_4]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 8 2 _ _ (by norm_num)] <;>
      norm_num [cert8_4, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 800000 in
-- the same unfolding, at i = 0
theorem bound_cert8_4 : bound 8 2 cert8_4 = 16 := by
  rw [bound_eq_rec]
  norm_num [cert8_4, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_8_2_4_le : A 8 2 4 ≤ 16 :=
  A_le_of_dualCert (by norm_num) dualCert_cert8_4 (by rw [bound_cert8_4]; norm_num)


/-- Certificate for `n = 10`, `d = 5`; the linear program's optimum. -/
def cert10_5 : ℕ → ℚ
  | 1 => 1
  | 10 => 1
  | _ => 0

set_option maxHeartbeats 800000 in
-- 6 dual constraints, each a sum of 10 Krawtchouk values
theorem dualCert_cert10_5 : DualCert 10 2 5 cert10_5 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert10_5]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 10 2 _ _ (by norm_num)] <;>
      norm_num [cert10_5, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 800000 in
-- the same unfolding, at i = 0
theorem bound_cert10_5 : bound 10 2 cert10_5 = 12 := by
  rw [bound_eq_rec]
  norm_num [cert10_5, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_10_2_5_le : A 10 2 5 ≤ 12 :=
  A_le_of_dualCert (by norm_num) dualCert_cert10_5 (by rw [bound_cert10_5]; norm_num)


/-- Certificate for `n = 11`, `d = 5`; the linear program's optimum. -/
def cert11_5 : ℕ → ℚ
  | 1 => 1
  | 2 => 1/5
  | 11 => 1
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 7 dual constraints, each a sum of 11 Krawtchouk values
theorem dualCert_cert11_5 : DualCert 11 2 5 cert11_5 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert11_5]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 11 2 _ _ (by norm_num)] <;>
      norm_num [cert11_5, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert11_5 : bound 11 2 cert11_5 = 24 := by
  rw [bound_eq_rec]
  norm_num [cert11_5, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_11_2_5_le : A 11 2 5 ≤ 24 :=
  A_le_of_dualCert (by norm_num) dualCert_cert11_5 (by rw [bound_cert11_5]; norm_num)


/-- Certificate for `n = 12`, `d = 5`; the linear program's optimum. -/
def cert12_5 : ℕ → ℚ
  | 1 => 2/3
  | 2 => 7/27
  | 3 => 1/18
  | 11 => 5/54
  | 12 => 5/9
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 8 dual constraints, each a sum of 12 Krawtchouk values
theorem dualCert_cert12_5 : DualCert 12 2 5 cert12_5 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert12_5]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 12 2 _ _ (by norm_num)] <;>
      norm_num [cert12_5, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert12_5 : bound 12 2 cert12_5 = 40 := by
  rw [bound_eq_rec]
  norm_num [cert12_5, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_12_2_5_le : A 12 2 5 ≤ 40 :=
  A_le_of_dualCert (by norm_num) dualCert_cert12_5 (by rw [bound_cert12_5]; norm_num)


/-- Certificate for `n = 13`, `d = 3`; the linear program's optimum. -/
def cert13_3 : ℕ → ℚ
  | 1 => 3/4
  | 2 => 1/2
  | 3 => 1/3
  | 4 => 1/6
  | 5 => 1/12
  | 9 => 1/12
  | 10 => 1/6
  | 11 => 1/3
  | 12 => 1/2
  | 13 => 3/4
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 11 dual constraints, each a sum of 13 Krawtchouk values
theorem dualCert_cert13_3 : DualCert 13 2 3 cert13_3 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert13_3]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 13 2 _ _ (by norm_num)] <;>
      norm_num [cert13_3, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert13_3 : bound 13 2 cert13_3 = 512 := by
  rw [bound_eq_rec]
  norm_num [cert13_3, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_13_2_3_le : A 13 2 3 ≤ 512 :=
  A_le_of_dualCert (by norm_num) dualCert_cert13_3 (by rw [bound_cert13_3]; norm_num)


/-- Certificate for `n = 14`, `d = 5`; the linear program's optimum. -/
def cert14_5 : ℕ → ℚ
  | 1 => 1
  | 2 => 1/5
  | 3 => 1/5
  | 12 => 1/5
  | 13 => 1/5
  | 14 => 1
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 10 dual constraints, each a sum of 14 Krawtchouk values
theorem dualCert_cert14_5 : DualCert 14 2 5 cert14_5 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert14_5]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 14 2 _ _ (by norm_num)] <;>
      norm_num [cert14_5, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert14_5 : bound 14 2 cert14_5 = 128 := by
  rw [bound_eq_rec]
  norm_num [cert14_5, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_14_2_5_le : A 14 2 5 ≤ 128 :=
  A_le_of_dualCert (by norm_num) dualCert_cert14_5 (by rw [bound_cert14_5]; norm_num)


/-- Certificate for `n = 15`, `d = 5`; the linear program's optimum. -/
def cert15_5 : ℕ → ℚ
  | 1 => 1
  | 2 => 11/35
  | 3 => 1/5
  | 4 => 2/35
  | 12 => 1/35
  | 13 => 1/5
  | 14 => 1/5
  | 15 => 1
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 11 dual constraints, each a sum of 15 Krawtchouk values
theorem dualCert_cert15_5 : DualCert 15 2 5 cert15_5 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert15_5]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 15 2 _ _ (by norm_num)] <;>
      norm_num [cert15_5, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert15_5 : bound 15 2 cert15_5 = 256 := by
  rw [bound_eq_rec]
  norm_num [cert15_5, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_15_2_5_le : A 15 2 5 ≤ 256 :=
  A_le_of_dualCert (by norm_num) dualCert_cert15_5 (by rw [bound_cert15_5]; norm_num)


/-- Certificate for `n = 12`, `d = 6`; the linear program's optimum. -/
def cert12_6 : ℕ → ℚ
  | 1 => 1
  | 2 => 1/6
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 7 dual constraints, each a sum of 12 Krawtchouk values
theorem dualCert_cert12_6 : DualCert 12 2 6 cert12_6 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert12_6]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 12 2 _ _ (by norm_num)] <;>
      norm_num [cert12_6, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert12_6 : bound 12 2 cert12_6 = 24 := by
  rw [bound_eq_rec]
  norm_num [cert12_6, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_12_2_6_le : A 12 2 6 ≤ 24 :=
  A_le_of_dualCert (by norm_num) dualCert_cert12_6 (by rw [bound_cert12_6]; norm_num)


/-- Certificate for `n = 15`, `d = 6`; the linear program's optimum. -/
def cert15_6 : ℕ → ℚ
  | 1 => 1
  | 2 => 1/5
  | 3 => 3/17
  | 12 => 2/85
  | _ => 0

set_option maxHeartbeats 1200000 in
-- 10 dual constraints, each a sum of 15 Krawtchouk values
theorem dualCert_cert15_6 : DualCert 15 2 6 cert15_6 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert15_6]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 15 2 _ _ (by norm_num)] <;>
      norm_num [cert15_6, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1200000 in
-- the same unfolding, at i = 0
theorem bound_cert15_6 : bound 15 2 cert15_6 = 128 := by
  rw [bound_eq_rec]
  norm_num [cert15_6, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_15_2_6_le : A 15 2 6 ≤ 128 :=
  A_le_of_dualCert (by norm_num) dualCert_cert15_6 (by rw [bound_cert15_6]; norm_num)


/-- Certificate for `n = 24`, `d = 8`; the linear program's optimum. -/
def cert24_8 : ℕ → ℚ
  | 1 => 1
  | 2 => 1899761/3371616
  | 3 => 104119/421452
  | 4 => 1466405/17700984
  | 5 => 94789/4425246
  | 6 => 69857/23601312
  | 18 => 47213/23601312
  | 19 => 103097/8850492
  | 20 => 547199/17700984
  | 21 => 12329/210726
  | 22 => 184085/3371616
  | _ => 0

set_option maxHeartbeats 2000000 in
-- 17 dual constraints, each a sum of 24 Krawtchouk values
theorem dualCert_cert24_8 : DualCert 24 2 8 cert24_8 := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [cert24_8]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 24 2 _ _ (by norm_num)] <;>
      norm_num [cert24_8, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 2000000 in
-- the same unfolding, at i = 0
theorem bound_cert24_8 : bound 24 2 cert24_8 = 4096 := by
  rw [bound_eq_rec]
  norm_num [cert24_8, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem A_24_2_8_le : A 24 2 8 ≤ 4096 :=
  A_le_of_dualCert (by norm_num) dualCert_cert24_8 (by rw [bound_cert24_8]; norm_num)



end Delsarte.Certificate
