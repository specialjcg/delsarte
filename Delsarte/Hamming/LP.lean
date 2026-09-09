/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Delsarte.Krawtchouk.Basic
import Delsarte.LP.WeakDuality

/-!
# The Delsarte linear program for the Hamming scheme

The primal variables are the distance distribution entries `a_d, …, a_n` of a
code; the entries `a_1, …, a_{d-1}` are *eliminated* rather than constrained to
zero, so the program has no equality constraints at all and drops straight into
the `A x ≤ b`, `x ≥ 0` shape of `Delsarte.LP`.

## Sign convention

Delsarte's constraint is usually written with the inequality pointing the other
way,

`K_k(0) + ∑_{i=d}^{n} a_i K_k(i) ≥ 0`,

whereas `Delsarte.LP.PrimalFeasible` expects `A x ≤ b`. The matrix therefore
carries a **minus sign**: `A k i = -K_k(i)`, with `b k = K_k(0)`. Getting this
backwards yields a bound that is false and still compiles, so `delsarteMatrix`
is the single place where the sign lives, and `primalFeasible_codeVec` states
the constraint in its usual orientation.

The objective is `c = 1`, so `⟨c, x⟩ = ∑_{i≥d} a_i = |C| - 1`.

Nothing here proves that a code's distance distribution *is* primal feasible:
that is the Fourier-positivity statement, and it is assumed as a hypothesis
throughout this file.
-/

namespace Delsarte.Hamming

open Finset Matrix Delsarte.LP

variable {n q d : ℕ}

/-- Primal variables: the admissible distances `d ≤ i ≤ n`. -/
abbrev DistIdx (n d : ℕ) := {i : ℕ // i ∈ Finset.Icc d n}

/-- Constraints: the Krawtchouk degrees `1 ≤ k ≤ n`. -/
abbrev ConIdx (n : ℕ) := {k : ℕ // k ∈ Finset.Icc 1 n}

/-- Constraint matrix of the Delsarte LP. The minus sign turns Delsarte's
`≥ 0` constraint into the `A x ≤ b` orientation of `Delsarte.LP`. -/
def delsarteMatrix (n q d : ℕ) : Matrix (ConIdx n) (DistIdx n d) ℚ :=
  fun k i => -krawtchouk n q k.1 i.1

/-- Right-hand side of the Delsarte LP: `b k = K_k(0) = C(n,k) (q-1)^k`. -/
def delsarteRHS (n q : ℕ) : ConIdx n → ℚ := fun k => krawtchouk n q k.1 0

/-- Objective of the Delsarte LP: the all-ones vector. -/
def delsarteObj (n d : ℕ) : DistIdx n d → ℚ := fun _ => 1

/-- The distance distribution of `C`, read as a primal point. -/
def codeVec (C : Code n q) (d : ℕ) : DistIdx n d → ℚ := fun i => distDist C i.1

theorem delsarteRHS_nonneg (hq : 1 ≤ q) (k : ConIdx n) : 0 ≤ delsarteRHS n q k := by
  have hq' : (0 : ℚ) ≤ (q : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    linarith
  rw [delsarteRHS, krawtchouk_zero_right]
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq' _)

/-- Delsarte's positivity constraint, in its usual orientation, is exactly primal
feasibility of the distance distribution. -/
theorem primalFeasible_codeVec {C : Code n q}
    (h : ∀ k ∈ Finset.Icc 1 n,
      0 ≤ krawtchouk n q k 0 + ∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n q k i) :
    PrimalFeasible (delsarteMatrix n q d) (delsarteRHS n q) (codeVec C d) := by
  refine ⟨fun i => distDist_nonneg _ _, fun k => ?_⟩
  have hk := h k.1 k.2
  have hsum : ∑ i : DistIdx n d, delsarteMatrix n q d k i * codeVec C d i
      = -∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n q k.1 i := by
    rw [← Finset.sum_coe_sort (Finset.Icc d n)
      (fun i => distDist C i * krawtchouk n q k.1 i), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [delsarteMatrix, codeVec]; ring
  have hmv : (delsarteMatrix n q d *ᵥ codeVec C d) k
      = ∑ i : DistIdx n d, delsarteMatrix n q d k i * codeVec C d i := rfl
  rw [hmv, hsum, delsarteRHS]
  linarith

/-- Weak duality, instantiated at the Delsarte LP. -/
theorem sum_le_of_feasible {x : DistIdx n d → ℚ} {y : ConIdx n → ℚ}
    (hx : PrimalFeasible (delsarteMatrix n q d) (delsarteRHS n q) x)
    (hy : DualFeasible (delsarteMatrix n q d) (delsarteObj n d) y) :
    ∑ i, x i ≤ delsarteRHS n q ⬝ᵥ y := by
  calc ∑ i, x i = delsarteObj n d ⬝ᵥ x := by simp [dotProduct, delsarteObj]
    _ ≤ delsarteRHS n q ⬝ᵥ y := weak_duality hx hy

/-- The Delsarte bound for one code, conditional on primal feasibility of its
distance distribution. -/
theorem card_le_of_primalFeasible (hd : 1 ≤ d) {C : Code n q} (hC : C.Nonempty)
    (hmin : MinDistAtLeast d C)
    (hx : PrimalFeasible (delsarteMatrix n q d) (delsarteRHS n q) (codeVec C d))
    {y : ConIdx n → ℚ} (hy : DualFeasible (delsarteMatrix n q d) (delsarteObj n d) y) :
    (C.card : ℚ) ≤ 1 + delsarteRHS n q ⬝ᵥ y := by
  have hsub : insert 0 (Finset.Icc d n) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_Icc] at hi
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    rcases hi with rfl | ⟨_, h2⟩
    · exact Nat.zero_le _
    · exact h2
  have hzero : ∀ i ∈ Finset.range (n + 1), i ∉ insert 0 (Finset.Icc d n) →
      distDist C i = 0 := by
    intro i hi hni
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and_or, not_le] at hni
    obtain ⟨hi0, hid⟩ := hni
    exact distDist_eq_zero_of_lt hmin (Nat.pos_of_ne_zero hi0)
      (by rcases hid with h | h <;> omega)
  have hsplit : (C.card : ℚ) = distDist C 0 + ∑ i ∈ Finset.Icc d n, distDist C i := by
    rw [← sum_distDist hC, ← Finset.sum_subset hsub hzero,
      Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
  rw [hsplit, distDist_zero hC]
  have hle := sum_le_of_feasible hx hy
  rw [show ∑ i ∈ Finset.Icc d n, distDist C i = ∑ i : DistIdx n d, codeVec C d i from
    (Finset.sum_coe_sort (Finset.Icc d n) (fun i => distDist C i)).symm]
  linarith [hle]

/-- The Delsarte bound on `A(n,d)`, conditional on primal feasibility. -/
theorem A_le_of_dualFeasible (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hfeas : ∀ C : Code n q, C.Nonempty → MinDistAtLeast d C →
      PrimalFeasible (delsarteMatrix n q d) (delsarteRHS n q) (codeVec C d))
    {y : ConIdx n → ℚ} (hy : DualFeasible (delsarteMatrix n q d) (delsarteObj n d) y) :
    (A n q d : ℚ) ≤ 1 + delsarteRHS n q ⬝ᵥ y := by
  obtain ⟨C, hmin, hcard⟩ := exists_code_card_eq_A n q d
  rcases Finset.eq_empty_or_nonempty C with rfl | hC
  · have hnn : 0 ≤ delsarteRHS n q ⬝ᵥ y :=
      Finset.sum_nonneg fun k _ => mul_nonneg (delsarteRHS_nonneg hq k) (hy.1 k)
    simp only [Finset.card_empty] at hcard
    rw [← hcard]
    push_cast
    linarith
  · rw [← hcard]
    exact card_le_of_primalFeasible hd hC hmin (hfeas C hC hmin) hy

end Delsarte.Hamming
