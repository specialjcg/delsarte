/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.Feasible

/-!
# Exact certificate verification over `ℚ`

A Delsarte certificate is a vector of rationals `y k`, one per Krawtchouk degree
`1 ≤ k ≤ n`. `DualCert` is the property of being dual feasible, decidable and
therefore checkable; `A_le_bound_of_dualCert` turns it into a bound on
`A n 2 d`.

Nothing here is mathematically interesting, and that is the point: the verifier
is plumbing between a vector of rationals and
`Delsarte.Hamming.A_le_of_dualFeasible_binary`. The solver that produced `y` is
not imported, not trusted, and not named.

## What is checked

Dual feasibility of the Delsarte LP is `0 ≤ y` and `c ≤ y ᵥ* A`. With
`A k i = -K_k(i)` and `c = 1` this reads

* `0 ≤ y k` for every degree `1 ≤ k ≤ n`;
* `1 ≤ -∑_k y k K_k(i)` for every admissible distance `d ≤ i ≤ n`.

The minus sign is the one `delsarteMatrix` carries; `dualSlack` is the single
place it appears in this file.

## Proof versus replay

Two things are deliberately kept apart.

* `DualCert` is a `Prop`. It is what the theorems consume, and the concrete
  instances below are *proved*, by `norm_num` on exact rational arithmetic.
* `dualCheck` is the same statement as a `Bool`, via the `Decidable` instance,
  and `dualCheck_eq_true_iff` ties the two together. It runs on compiled code:
  the `#guard` lines below execute the checker at build time on real `ℚ`
  arithmetic. A `#guard` proves nothing — it is the replay, not the proof.

Note that `decide` cannot close any of this: the kernel does not reduce `ℚ`
arithmetic (`Rat.normalize` goes through `Nat.gcd`). Hence `norm_num`
throughout, and no `native_decide` anywhere — `#print axioms` stays clean.

## Replay

The certificate file format is described in `Delsarte/Certificate/FORMAT.md`,
with `Delsarte/Certificate/examples/a-5-3.cert` as a worked instance.
Transcribing such a file into Lean is currently manual; the Lean declaration
*is* the statement being proved, so nothing needs to be trusted between the two.
-/

namespace Delsarte.Certificate

open Finset Matrix Delsarte Delsarte.LP Delsarte.Hamming

variable {n q d : ℕ} {y : ℕ → ℚ}

/-- Value of the dual constraint at distance `i`, that is `(y ᵥ* A) i`. The only
place the sign convention of `delsarteMatrix` shows up in this file. -/
def dualSlack (n q : ℕ) (y : ℕ → ℚ) (i : ℕ) : ℚ :=
  -∑ k ∈ Finset.Icc 1 n, y k * krawtchouk n q k i

/-- The bound a valid certificate yields: `1 + ∑_k y k K_k(0)`. -/
def bound (n q : ℕ) (y : ℕ → ℚ) : ℚ :=
  1 + ∑ k ∈ Finset.Icc 1 n, y k * krawtchouk n q k 0

/-- `y` is a dual-feasible certificate for the Delsarte LP of parameters
`n, q, d`. -/
def DualCert (n q d : ℕ) (y : ℕ → ℚ) : Prop :=
  (∀ k ∈ Finset.Icc 1 n, 0 ≤ y k) ∧ ∀ i ∈ Finset.Icc d n, 1 ≤ dualSlack n q y i

set_option maxSynthPendingDepth 4 in
instance : Decidable (DualCert n q d y) := by unfold DualCert; infer_instance

/-- The certificate check as a `Bool`, for running rather than reasoning. -/
def dualCheck (n q d : ℕ) (y : ℕ → ℚ) : Bool := decide (DualCert n q d y)

theorem dualCheck_eq_true_iff : dualCheck n q d y = true ↔ DualCert n q d y :=
  decide_eq_true_iff

/-- A certificate is dual feasible in the sense of `Delsarte.LP`. -/
theorem dualFeasible_of_dualCert (h : DualCert n q d y) :
    DualFeasible (delsarteMatrix n q d) (delsarteObj n d) (fun k : ConIdx n => y k.1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun k => h1 k.1 k.2, fun i => ?_⟩
  have hvm : ((fun k : ConIdx n => y k.1) ᵥ* delsarteMatrix n q d) i
      = ∑ k : ConIdx n, y k.1 * delsarteMatrix n q d k i := rfl
  have hsum : ∑ k : ConIdx n, y k.1 * delsarteMatrix n q d k i = dualSlack n q y i.1 := by
    rw [dualSlack, ← Finset.sum_coe_sort (Finset.Icc 1 n)
      (fun k => y k * krawtchouk n q k i.1), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp [delsarteMatrix]
  rw [hvm, hsum]
  simpa [delsarteObj] using h2 i.1 i.2

/-- **The verifier.** A dual-feasible certificate bounds `A n 2 d`. -/
theorem A_le_bound_of_dualCert (hd : 1 ≤ d) (h : DualCert n 2 d y) :
    (A n 2 d : ℚ) ≤ bound n 2 y := by
  have hdot : delsarteRHS n 2 ⬝ᵥ (fun k : ConIdx n => y k.1)
      = ∑ k ∈ Finset.Icc 1 n, y k * krawtchouk n 2 k 0 := by
    rw [← Finset.sum_coe_sort (Finset.Icc 1 n) (fun k => y k * krawtchouk n 2 k 0)]
    exact Finset.sum_congr rfl fun k _ => by simp [delsarteRHS, mul_comm]
  rw [bound, ← hdot]
  exact A_le_of_dualFeasible_binary hd (dualFeasible_of_dualCert h)

/-- Same statement, consuming the `Bool` the checker produces. -/
theorem A_le_bound_of_dualCheck (hd : 1 ≤ d) (h : dualCheck n 2 d y = true) :
    (A n 2 d : ℚ) ≤ bound n 2 y :=
  A_le_bound_of_dualCert hd (dualCheck_eq_true_iff.mp h)

/-! ## A certificate, verified

`n = 5`, `q = 2`, `d = 3`, `y = (1, 0, 0, 0, 0)`. The dual slack at distances
3, 4, 5 is `1, 3, 5`, all at least 1, and the bound is `1 + K_1(0) = 6`. The
true value is `A(5,3) = 4`, so the certificate is valid and not tight.
-/

/-- The certificate of `Delsarte/Certificate/examples/a-5-3.cert`. -/
def certFiveThree : ℕ → ℚ := fun k => if k = 1 then 1 else 0

/-- Tactic block for unfolding a concrete `dualSlack` or `bound` to a rational. -/
local macro "cert_num" : tactic =>
  `(tactic| norm_num [certFiveThree, dualSlack, bound, krawtchouk,
      Finset.sum_Icc_succ_top, Finset.sum_range_succ])

theorem dualCert_certFiveThree : DualCert 5 2 3 certFiveThree := by
  constructor
  · intro k hk; fin_cases hk <;> cert_num
  · intro i hi; fin_cases hi <;> cert_num

theorem bound_certFiveThree : bound 5 2 certFiveThree = 6 := by cert_num

/-- **First unconditional numerical bound of this repository.** A binary code of
length 5 with minimum distance 3 has at most 6 words. -/
theorem A_five_two_three_le_six : (A 5 2 3 : ℚ) ≤ 6 := by
  rw [← bound_certFiveThree]
  exact A_le_bound_of_dualCert (by norm_num) dualCert_certFiveThree

/-! ## Negative controls

A verifier that has never rejected anything has proved nothing. Each of the
following is a certificate the check must refuse, and does.
-/

/-- Rejected: a negative multiplier. Dual feasibility needs `y ≥ 0`. -/
theorem not_dualCert_negComponent :
    ¬ DualCert 5 2 3 (fun k => if k = 1 then -1 else 0) := by
  intro h
  have h1 := h.1 1 (by decide)
  norm_num at h1

/-- Rejected: halving a valid certificate. `y = (1/2, 0, 0, 0, 0)` is
nonnegative, but its slack at distance 3 is `1/2 < 1`. The check is therefore
not merely testing the sign of `y`. -/
theorem not_dualCert_halved :
    ¬ DualCert 5 2 3 (fun k => if k = 1 then 1 / 2 else 0) := by
  intro h
  have h2 := h.2 3 (by decide)
  norm_num [dualSlack, krawtchouk, Finset.sum_Icc_succ_top, Finset.sum_range_succ] at h2

/-- Rejected: the same certificate read at the wrong minimum distance. Valid for
`d = 3`, it fails at `d = 2`, where distance 2 has slack `-1`. A certificate is
tied to its parameters. -/
theorem not_dualCert_wrongD : ¬ DualCert 5 2 2 certFiveThree := by
  intro h
  have h2 := h.2 2 (by decide)
  norm_num [certFiveThree, dualSlack, krawtchouk,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ] at h2

/-! ## Replay at build time

These run the compiled checker on exact `ℚ` arithmetic. They prove nothing —
they are the replay, and they fail the build if the checker's verdict ever
disagrees with the theorems above.
-/

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard dualCheck 5 2 3 certFiveThree
#guard ! dualCheck 5 2 3 (fun k => if k = 1 then -1 else 0)
#guard ! dualCheck 5 2 3 (fun k => if k = 1 then 1 / 2 else 0)
#guard ! dualCheck 5 2 2 certFiveThree

end Delsarte.Certificate
