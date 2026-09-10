/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Verify

/-!
# Certified bounds on `A(n, 2, d)`

Each bound here is a theorem about `A n 2 d`, obtained by handing a vector of
rationals to `Delsarte.Certificate.A_le_of_dualCert`. The vectors came from the
exact rational simplex in `tools/delsarte_lp.py`, which is not imported, not
trusted, and plays no part in any proof: it is a source of candidates. If it
returned nonsense, `DualCert` would refuse it.

## The three bounds

| bound | true value | remark |
|---|---|---|
| `A(5,2,3) ≤ 4` | 4 | the LP is tight |
| `A(13,2,5) ≤ 64` | 64 | tight; the Hamming bound only gives 89 |
| `A(23,2,7) ≤ 4096` | 4096 | tight; the perfect binary Golay code attains it |

Only the upper halves are proved. The matching codes exist — that is why the
values are known — but no code is constructed here, so nothing below may be read
as `A(n,2,d) = ...`.

## Two independent evaluations

Every proof goes through `dualSlack_eq_rec`, that is through the three-term
recurrence, because `norm_num` cannot evaluate `Nat.choose` at these sizes. The
`#guard` lines at the end run the compiled checker instead, which evaluates
`krawtchouk` from its *binomial* definition. So each certificate is checked twice,
by two routes that share no arithmetic, and `krawtchoukRec_eq` is what says the
two routes must agree.
-/

namespace Delsarte.Certificate

open Finset Delsarte

/-! ## `A(5,2,3) ≤ 4`

The optimum of the LP, where `Delsarte.Certificate.certFiveThree` only reached 6.
-/

/-- Optimal certificate for `n = 5`, `d = 3`. -/
def certFive : ℕ → ℚ
  | 1 => 1 / 2
  | 5 => 1 / 2
  | _ => 0

theorem dualCert_certFive : DualCert 5 2 3 certFive := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [certFive]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 5 2 _ _ (by norm_num)] <;>
      norm_num [certFive, krawtchoukRec, Finset.sum_Icc_succ_top]

theorem bound_certFive : bound 5 2 certFive = 4 := by
  rw [bound_eq_rec]
  norm_num [certFive, krawtchoukRec, Finset.sum_Icc_succ_top]

/-- A binary code of length 5 with minimum distance 3 has at most 4 words. This is
the exact value. -/
theorem A_five_two_three_le_four : A 5 2 3 ≤ 4 :=
  A_le_of_dualCert (by norm_num) dualCert_certFive (by rw [bound_certFive]; norm_num)

/-! ## `A(13,2,5) ≤ 64`

The sphere-packing bound gives only `2 ^ 13 / (1 + 13 + 78) = 89`, so this is a
bound the linear program earns and elementary counting does not.
-/

/-- Optimal certificate for `n = 13`, `d = 5`. Symmetric, denominators at most 10. -/
def certThirteen : ℕ → ℚ
  | 1 => 3 / 5
  | 2 => 1 / 5
  | 3 => 1 / 10
  | 11 => 1 / 10
  | 12 => 1 / 5
  | 13 => 3 / 5
  | _ => 0

set_option maxHeartbeats 1000000 in
-- nine dual constraints, each a sum of thirteen Krawtchouk values unfolded from
-- the recurrence; exact rational arithmetic, no shortcut available
theorem dualCert_certThirteen : DualCert 13 2 5 certThirteen := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [certThirteen]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 13 2 _ _ (by norm_num)] <;>
      norm_num [certThirteen, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 1000000 in
-- same unfolding, at i = 0
theorem bound_certThirteen : bound 13 2 certThirteen = 64 := by
  rw [bound_eq_rec]
  norm_num [certThirteen, krawtchoukRec, Finset.sum_Icc_succ_top]

/-- A binary code of length 13 with minimum distance 5 has at most 64 words. -/
theorem A_thirteen_two_five_le_64 : A 13 2 5 ≤ 64 :=
  A_le_of_dualCert (by norm_num) dualCert_certThirteen (by rw [bound_certThirteen]; norm_num)

/-! ## `A(23,2,7) ≤ 4096`

The perfect binary Golay code attains this, so the linear program is tight here.
-/

/-- Optimal certificate for `n = 23`, `d = 7`. -/
def certGolay : ℕ → ℚ
  | 1 => 1
  | 2 => 41 / 66
  | 3 => 857 / 2772
  | 4 => 323 / 2772
  | 5 => 95 / 2772
  | 6 => 5 / 924
  | 18 => 5 / 1386
  | 19 => 79 / 2772
  | 20 => 277 / 2772
  | 21 => 37 / 132
  | 22 => 7 / 12
  | 23 => 1
  | _ => 0

set_option maxHeartbeats 4000000 in
-- seventeen dual constraints, each a sum of twenty-three Krawtchouk values with
-- denominators up to 2772; this is the largest exact check in the repository
theorem dualCert_certGolay : DualCert 23 2 7 certGolay := by
  constructor
  · intro k hk; fin_cases hk <;> norm_num [certGolay]
  · intro i hi
    fin_cases hi <;>
      rw [dualSlack_eq_rec 23 2 _ _ (by norm_num)] <;>
      norm_num [certGolay, krawtchoukRec, Finset.sum_Icc_succ_top]

set_option maxHeartbeats 4000000 in
-- same unfolding, at i = 0
theorem bound_certGolay : bound 23 2 certGolay = 4096 := by
  rw [bound_eq_rec]
  norm_num [certGolay, krawtchoukRec, Finset.sum_Icc_succ_top]

/-- A binary code of length 23 with minimum distance 7 has at most 4096 words. The
perfect binary Golay code has exactly 4096, so this bound is attained — but no code
is constructed here, and this file proves only the upper half. -/
theorem A_twentyThree_two_seven_le_4096 : A 23 2 7 ≤ 4096 :=
  A_le_of_dualCert (by norm_num) dualCert_certGolay (by rw [bound_certGolay]; norm_num)

/-! ## Control: the exactness is what carries the result

Lowering one coefficient of the Golay certificate by `10 ^ (-30)` — a change no
floating-point number can represent — turns the bound into

`4095.999999999999999999999999999747`

whose floor is 4095. A verifier that had rounded anywhere would then "prove"
`A(23,2,7) ≤ 4095`, and that statement is **false**: the perfect binary Golay code
has 4096 words. The check refuses the perturbed vector, at distances 11, 12 and 13.
-/

/-- The Golay certificate perturbed below the resolution of any `Float`. -/
def certGolayPerturbed : ℕ → ℚ :=
  fun k => if k = 2 then certGolay k - 1 / 10 ^ 30 else certGolay k

set_option maxHeartbeats 1000000 in
-- one constraint of the Golay size, with a 10^-30 perturbation carried exactly
theorem not_dualCert_certGolayPerturbed : ¬ DualCert 23 2 7 certGolayPerturbed := by
  intro h
  have h2 := h.2 11 (by decide)
  rw [dualSlack_eq_rec 23 2 _ _ (by norm_num)] at h2
  norm_num [certGolayPerturbed, certGolay, krawtchoukRec, Finset.sum_Icc_succ_top] at h2

/-! ## Replay through the other definition

These run the compiled checker, which evaluates `krawtchouk` from its binomial
definition — the route the proofs above could not take. Agreement between the two
is not a coincidence to be hoped for: it is `krawtchoukRec_eq`.
-/

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard dualCheck 5 2 3 certFive
#guard dualCheck 13 2 5 certThirteen
#guard dualCheck 23 2 7 certGolay
#guard bound 13 2 certThirteen == 64
#guard bound 23 2 certGolay == 4096
#guard ! dualCheck 23 2 7 certGolayPerturbed
#guard bound 23 2 certGolayPerturbed < 4096

end Delsarte.Certificate
