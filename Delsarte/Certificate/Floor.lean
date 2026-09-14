/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Integer

/-!
# Rounding the bound down

`A_le_of_intCert` proves `A n 2 d ≤ B` from `bound ≤ B`, so it can only be used
when the linear program's optimum is itself an integer. Every entry of
`Delsarte/Certificate/Table1.lean` and its neighbours happens to be of that kind.

Most entries are not. The optimum of `A(18, 2, 4)` is `32768 / 5 = 6553.6`, and no
dual vector reaches `6553`: the program's value is what it is, and `6553.6` is
the best any certificate can say. The missing step is not linear programming at
all — it is that `A n q d` counts codewords and is therefore a natural number.
From `A ≤ 6553.6` and `A : ℕ` one gets `A ≤ 6553`.

So this file repeats `A_le_of_intCertQ` with a strict inequality: the check
becomes `bound < B + 1`, which for an integral `A` is exactly `A ≤ B`. The
arithmetic stays in `ℤ`, decided by the kernel on the scaled certificate, as in
`Delsarte/Certificate/Integer.lean`.

The gain is at most one codeword per entry, and it is real: on the binary table
it is the difference between `A(18,2,4) ≤ 6554` and `A(18,2,4) ≤ 6553`.
-/

namespace Delsarte.Certificate

open Delsarte

/-- The bound check, strict: `1 + ∑ y k K_k(0) < B + 1`, scaled by `D`. -/
def intBoundLtQ (n q : ℕ) (p : List ℤ) (D B : ℤ) : Bool :=
  decide (D + dotp p (pascalRowQ q n) < (B + 1) * D)

/-- The binary specialisation of `intBoundLtQ`. -/
def intBoundLt (n : ℕ) (p : List ℤ) (D B : ℤ) : Bool :=
  decide (D + dotp p (pascalRow n) < (B + 1) * D)

theorem intBoundLt_eq (n : ℕ) (p : List ℤ) (D B : ℤ) :
    intBoundLt n p D B = intBoundLtQ n 2 p D B := by
  rw [intBoundLt, intBoundLtQ, pascalRow_eq]

/-- **Certificate plus integrality.** A dual certificate bounding the linear
program strictly below `B + 1` bounds `A n q d` by `B`. -/
theorem A_le_of_intCertLtQ {n q d B : ℕ} {p : List ℤ} {D : ℤ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (h : intCheckQ n q d p D = true) (hb : intBoundLtQ n q p D (B : ℤ) = true) :
    A n q d ≤ B := by
  have hcert := dualCert_of_intCheckQ h
  simp only [intCheckQ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, hp0⟩, hD⟩, -⟩, -⟩ := h
  have hD' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  simp only [intBoundLtQ, decide_eq_true_eq] at hb
  have key : (D : ℚ) + ((dotp p (pascalRowQ q n) : ℤ) : ℚ) < ((B : ℚ) + 1) * (D : ℚ) := by
    have hcast : ((D + dotp p (pascalRowQ q n) : ℤ) : ℚ) < ((((B : ℤ) + 1) * D : ℤ) : ℚ) := by
      exact_mod_cast hb
    push_cast at hcast ⊢
    linarith
  have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n q k 0
      = ((dotp p (pascalRowQ q n) : ℤ) : ℚ) / (D : ℚ) := by
    simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_eq_dotpQ n q 0 (Nat.zero_le n) p hlen hp0, krawColQ]
  have hdiv : ((dotp p (pascalRowQ q n) : ℤ) : ℚ) / (D : ℚ) < (B : ℚ) := by
    rw [div_lt_iff₀ hD']
    nlinarith [key]
  have hbd : bound n q (ratOfInt p D) < (B : ℚ) + 1 := by
    rw [bound, hsum]
    linarith
  have h1 : ((A n q d : ℕ) : ℚ) < (B : ℚ) + 1 :=
    lt_of_le_of_lt (A_le_bound_of_dualCert_qary hq hd hcert) hbd
  have h2 : A n q d < B + 1 := by exact_mod_cast h1
  omega

/-- The binary specialisation of `A_le_of_intCertLtQ`. -/
theorem A_le_of_intCertLt {n d B : ℕ} {p : List ℤ} {D : ℤ} (hd : 1 ≤ d)
    (h : intCheck n d p D = true) (hb : intBoundLt n p D (B : ℤ) = true) :
    A n 2 d ≤ B :=
  A_le_of_intCertLtQ (by norm_num) hd (by rwa [intCheck_eq] at h)
    (by rwa [intBoundLt_eq] at hb)

end Delsarte.Certificate
