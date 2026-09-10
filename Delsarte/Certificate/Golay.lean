/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Verify

/-!
# `A(23,2,7) ≤ 4096`, and what exactness buys

The perfect binary Golay code has 4096 words, so the linear program is tight here.
Only the upper half is proved: no code is constructed, so this is not an equality.

Its own module because it is the most expensive exact check in the repository, and
importing only the verifier lets Lake elaborate it in parallel with the rest of
the table.
-/

namespace Delsarte.Certificate

open Finset Delsarte

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


-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard dualCheck 23 2 7 certGolay
#guard bound 23 2 certGolay == 4096
#guard !dualCheck 23 2 7 certGolayPerturbed
#guard bound 23 2 certGolayPerturbed < 4096

end Delsarte.Certificate
