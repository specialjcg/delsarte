/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Integer

/-!
# The first ternary bound: `A(11,3,5) ≤ 729`

Until now the repository was in an uncomfortable position: `A_le_bound_of_dualCheck_qary`
proved that dual feasibility bounds `A n q d` for every `q ≥ 1`, and not a single
certificate existed for any `q` other than `2`, because the integer Krawtchouk
table was built by a binary recurrence. `Delsarte/Certificate/IntTable.lean` removed
that restriction; this file is the first bound that uses it.

## What is proved, and what is not

A ternary code of length 11 with minimum distance 5 has at most 729 words. The
ternary Golay code has exactly `3^6 = 729`, so the bound is **attained** — but no
code is constructed here, and only the upper half is proved. The LP optimum is
exactly 729, not merely at most: the certificate below makes
`intBoundLeQ` an equality, `60 + ⟨p, K(·,0)⟩ = 729 · 60`.

Soundness runs through `A_le_of_intCertQ`, hence `A_le_bound_of_dualCert_qary`,
hence the `q`-ary primal feasibility of `Delsarte/Hamming/FeasibleQ.lean`. No step
of the chain is binary.

## The certificate

Found by `tools/delsarte_lp.py` with `q = 3`, rounded to rationals, and then
re-verified here from scratch: the solver's output is a candidate, and `decide` is
the authority. Its denominators are `1, 12, 15, 30, 60`, so `60` clears them all
and the scaled vector is integral with no repair step.

## Why the exactness matters here, more than in the binary case

The bound is attained, so there is no slack at all between what is proved and what
is true. Lowering one coefficient by `10 ^ (-30)` — a change no `Float` can
represent — drops the bound below 729 while keeping it above 728. A verifier that
rounded anywhere would then report `A(11,3,5) ≤ 728`, and that statement is
**false**: the ternary Golay code has 729 words. The control below exhibits exactly
that vector and shows the exact check refuses it, at distance 8.
-/

namespace Delsarte.Certificate

open Delsarte

-- kernel reduction of the ternary table walks 12 columns of 12 entries
set_option maxRecDepth 100000

/-- Optimal certificate for `n = 11`, `q = 3`, `d = 5`, scaled by the common
denominator `60`. As rationals: `1, 8/15, 11/60, 1/30`, then zeros, then `1/12`.
Index `0` is unused and must be zero. -/
def cert11_3_5Int : List ℤ :=
  [0, 60, 32, 11, 2, 0, 0, 0, 0, 0, 0, 5]

/-- The common denominator of `cert11_3_5`. -/
def cert11_3_5Den : ℤ := 60

/-- The ternary certificate as rationals. Derived from the integer form, so the two
cannot drift apart. -/
def cert11_3_5 : ℕ → ℚ := ratOfInt cert11_3_5Int cert11_3_5Den

/-- The kernel accepts the scaled certificate. Seven dual constraints, each a sum
of eleven integer products against a column of the **ternary** table. -/
theorem intCheck_cert11_3_5 : intCheckQ 11 3 5 cert11_3_5Int cert11_3_5Den = true := by
  decide

theorem dualCert_cert11_3_5 : DualCert 11 3 5 cert11_3_5 :=
  dualCert_of_intCheckQ intCheck_cert11_3_5

/-- **A ternary code of length 11 with minimum distance 5 has at most 729 words.**

The ternary Golay code has exactly 729, so the bound is attained. No code is
constructed here. -/
theorem A_11_3_5_le : A 11 3 5 ≤ 729 :=
  A_le_of_intCertQ (p := cert11_3_5Int) (D := cert11_3_5Den) (by norm_num) (by norm_num)
    intCheck_cert11_3_5 (by decide)

/-! ## Control: the exactness is what carries the result

Lowering `y 1` by `10 ^ (-30)` turns the bound into a rational strictly between
728 and 729. A verifier that had rounded anywhere would "prove" `A(11,3,5) ≤ 728`,
and that is **false**. Scaling by `10 ^ 30` keeps the perturbation integral, so the
refusal is decided by the kernel too.
-/

/-- The ternary certificate with `y 1` lowered by `10 ^ (-30)`, scaled by
`60 · 10 ^ 30`. -/
def cert11_3_5IntPerturbed : List ℤ :=
  (cert11_3_5Int.map (· * 10 ^ 30)).set 1 (60 * 10 ^ 30 - 60)

/-- The scaled denominator that goes with `cert11_3_5IntPerturbed`. -/
def cert11_3_5DenPerturbed : ℤ := cert11_3_5Den * 10 ^ 30

theorem not_intCheck_cert11_3_5Perturbed :
    intCheckQ 11 3 5 cert11_3_5IntPerturbed cert11_3_5DenPerturbed = false := by
  decide

/-- And the refusal is not an artefact of the encoding: the perturbed vector is not
dual feasible at all, because the constraint at distance 8 fails. `K_1(8) = -2` is
negative, so lowering `y 1` lowers that slack. -/
theorem not_dualCert_cert11_3_5Perturbed :
    ¬ DualCert 11 3 5 (ratOfInt cert11_3_5IntPerturbed cert11_3_5DenPerturbed) :=
  not_dualCert_of_intSlackQ (n := 11) (q := 3) (d := 5) (i := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

-- The `#`-command linter is off here on purpose: these commands are the replay.
set_option linter.hashCommand false

#guard dualCheck 11 3 5 cert11_3_5
#guard bound 11 3 cert11_3_5 == 729
#guard cert11_3_5 2 == 8 / 15
#guard cert11_3_5 11 == 1 / 12

-- the perturbed bound is below 729 and above 728: only a rounding verifier would
-- accept it, and the answer it would give is false
#guard !dualCheck 11 3 5 (ratOfInt cert11_3_5IntPerturbed cert11_3_5DenPerturbed)
#guard bound 11 3 (ratOfInt cert11_3_5IntPerturbed cert11_3_5DenPerturbed) < 729
#guard bound 11 3 (ratOfInt cert11_3_5IntPerturbed cert11_3_5DenPerturbed) > 728

-- The ternary table agrees with the binomial definition of `krawtchouk`, entry by
-- entry: Pascal weighted by `q-1` plus differences on one side, an alternating sum
-- of products of binomial coefficients on the other.
#guard (List.range 8).all fun i =>
  (List.range 8).all fun k => ((ent (krawColQ 7 3 i) k : ℚ)) == krawtchouk 7 3 k i

-- and it reproduces the binary table at `q = 2`, by evaluation as well as by
-- `Delsarte.Certificate.krawCol_eq`
#guard (List.range 8).all fun i => krawColQ 7 2 i == krawCol 7 i

-- column 0 is the weighted Pascal row `C(11,k) 2^k`
#guard krawColQ 11 3 0 == [1, 22, 220, 1320, 5280, 14784, 29568, 42240, 42240, 28160, 11264, 2048]

end Delsarte.Certificate
