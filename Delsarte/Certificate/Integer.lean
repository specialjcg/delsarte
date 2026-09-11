/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Verify
import Delsarte.Certificate.IntTable

/-!
# Integer certificates, decided by the kernel

The verifier of `Delsarte.Certificate.Verify` checks a rational certificate with
`norm_num`. It has to: the kernel cannot reduce `ℚ` arithmetic, because
`Rat.normalize` calls `Nat.gcd`. So `decide` is unusable there, and every
constraint costs a simp traversal.

The kernel does reduce `ℤ` well. This file moves the check into `ℤ`:

* the certificate is scaled by its common denominator `D`, so that `p k = D * y k`
  are integers, and `1 ≤ dualSlack` becomes `D ≤ -∑ p k K_k(i)`;
* the Krawtchouk table is built by the **difference recurrence**
  `K_(k+1)(i+1) = K_(k+1)(i) - K_k(i) - (q-1) K_k(i+1)` (`Delsarte.krawtchouk_diff`),
  starting from the weighted Pascal row `K_k(0) = C(n,k) (q-1)^k`. Neither step
  divides, so nothing leaves `ℤ`. The table itself lives in
  `Delsarte/Certificate/IntTable.lean`, for an arbitrary alphabet size;
* the table is built once, as a list, and every column is shared. `Nat.choose`
  never appears: it is unusable in the kernel, whereas one Pascal row is `O(n²)`
  additions.

The whole check is then `decide`, and the certificate proofs cost milliseconds
instead of tens of seconds. `native_decide` is *not* used anywhere: the kernel
does the reduction, so no compiler enters the trust base.

## Two checks, one implementation

`intCheckQ` is the check at an arbitrary alphabet size; `intCheck` is the binary
one, kept with its original definition because twenty-four generated certificates
are `decide` proofs that reduce through it. Its soundness is no longer proved
separately: `intCheck_eq` sends it to `intCheckQ` at `q = 2`, and that equality is
a theorem rather than a definitional identity, which is what makes it a control.
-/

namespace Delsarte.Certificate

open Finset Delsarte

/-! ## The table, without division

Every definition here is structurally recursive with a single recursive call, so
kernel reduction visits each column once. That is the whole point: written as
`fun i => (difference recurrence applied i times)`, the same table would be
recomputed for every constraint.
-/

/-- One step of Pascal's rule, carrying the previous entry. -/
def pascalAux : ℤ → List ℤ → List ℤ
  | prev, [] => [prev]
  | prev, a :: as => (prev + a) :: pascalAux a as

/-- Row `n` of Pascal's triangle: `K_k(0) = C(n,k)` for `k = 0, …, n`. -/
def pascalRow : ℕ → List ℤ
  | 0 => [1]
  | (n + 1) => pascalAux 0 (pascalRow n)

/-- One step of the difference recurrence, carrying the previous entry of the old
column (`po`) and of the new one (`pn`). -/
def krawStepAux : ℤ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | po, pn, a :: as => (a - po - pn) :: krawStepAux a (a - po - pn) as

/-- Column `i + 1` of the binary Krawtchouk table from column `i`. The head is
`K_0(i+1) = 1`. -/
def krawStep : List ℤ → List ℤ
  | [] => []
  | _ :: as => 1 :: krawStepAux 1 1 as

/-- Column `i` of the binary Krawtchouk table: `[K_0(i), …, K_n(i)]`. -/
def krawCol (n : ℕ) : ℕ → List ℤ
  | 0 => pascalRow n
  | (i + 1) => krawStep (krawCol n i)

/-- The table as an indexed list, built in one pass so that each column is
computed once. The order is irrelevant: the check folds over it. -/
def krawTableAux (n : ℕ) : ℕ → List (ℕ × List ℤ)
  | 0 => [(0, pascalRow n)]
  | (i + 1) =>
      match krawTableAux n i with
      | [] => []
      | (j, c) :: cs => (i + 1, krawStep c) :: (j, c) :: cs

/-- Columns `0` to `n` of the binary Krawtchouk table, each paired with its
index. -/
def krawTable (n : ℕ) : List (ℕ × List ℤ) := krawTableAux n n

/-! ## The binary table is the `q`-ary table at `q = 2`

The definitions above are kept literally as they were. Twenty-four generated
certificates reduce through them, and changing what the kernel reduces is a risk
taken for no gain. What is not kept is their *proofs*: each statement below is now
one rewrite away from `Delsarte/Certificate/IntTable.lean`, which proves it for
arbitrary `q`.

The bridge is a theorem, not a definitional identity, and that is deliberate: it is
the anti-regression control. If the `q`-ary recurrence drifted from the binary one
— a swapped coefficient, a missing weight — these six lemmas would stop compiling,
rather than the twenty-four certificates failing much later with no explanation.
-/

theorem pascalAux_eq (p : ℤ) (l : List ℤ) : pascalAux p l = pascalAuxQ 2 p l := by
  induction l generalizing p with
  | nil => norm_num [pascalAux, pascalAuxQ]
  | cons a as ih =>
    rw [pascalAux, pascalAuxQ, ih]
    norm_num

theorem pascalRow_eq (n : ℕ) : pascalRow n = pascalRowQ 2 n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pascalRow, pascalRowQ, ih, pascalAux_eq]

theorem krawStepAux_eq (po pn : ℤ) (l : List ℤ) :
    krawStepAux po pn l = krawStepAuxQ 2 po pn l := by
  induction l generalizing po pn with
  | nil => rfl
  | cons a as ih =>
    have hc : (((2 : ℕ) : ℤ) - 1) = 1 := by norm_num
    rw [krawStepAux, krawStepAuxQ, hc, one_mul, ih]

theorem krawStep_eq (l : List ℤ) : krawStep l = krawStepQ 2 l := by
  cases l with
  | nil => rfl
  | cons a as => rw [krawStep, krawStepQ, krawStepAux_eq]

theorem krawCol_eq (n i : ℕ) : krawCol n i = krawColQ n 2 i := by
  induction i with
  | zero => exact pascalRow_eq n
  | succ i ih => rw [krawCol, krawColQ, ih, krawStep_eq]

theorem krawTableAux_eq_q (n i : ℕ) : krawTableAux n i = krawTableAuxQ n 2 i := by
  induction i with
  | zero => rw [krawTableAux, krawTableAuxQ, pascalRow_eq]
  | succ i ih =>
    rw [krawTableAux, krawTableAuxQ, ih]
    cases krawTableAuxQ n 2 i with
    | nil => rfl
    | cons jc cs =>
      obtain ⟨j, c⟩ := jc
      simp only [krawStep_eq]

theorem krawTable_eq (n : ℕ) : krawTable n = krawTableQ n 2 :=
  krawTableAux_eq_q n n

/-! ## The binary statements, derived -/

theorem length_pascalRow (n : ℕ) : (pascalRow n).length = n + 1 := by
  rw [pascalRow_eq]; exact length_pascalRowQ 2 n

theorem length_krawCol (n i : ℕ) : (krawCol n i).length = n + 1 := by
  rw [krawCol_eq]; exact length_krawColQ n 2 i

theorem pascalRow_getD (n k : ℕ) : ent (pascalRow n) k = (n.choose k : ℤ) := by
  rw [pascalRow_eq, pascalRowQ_getD]
  norm_num

theorem krawCol_getD_zero (n i : ℕ) : ent (krawCol n i) 0 = 1 := by
  rw [krawCol_eq]; exact krawColQ_getD_zero n 2 i

/-- **Correctness of the integer table.** Every entry is the Krawtchouk value it
claims to be, out-of-range indices included, where both sides are zero. -/
theorem krawCol_getD (n : ℕ) :
    ∀ i, i ≤ n → ∀ k, (ent (krawCol n i) k : ℚ) = krawtchouk n 2 k i := by
  intro i hi k
  rw [krawCol_eq]
  exact krawColQ_getD n 2 i hi k

/-- Every column of index at most `n` is in the table, paired with its index. -/
theorem mem_krawTable (n i : ℕ) (hi : i ≤ n) : (i, krawCol n i) ∈ krawTable n := by
  rw [krawTable_eq, krawCol_eq]
  exact mem_krawTableQ n 2 i hi

/-! ## From the integer check to the rational certificate -/

/-- The dual constraint, in one integer inner product. -/
theorem sum_eq_dotpQ (n q i : ℕ) (hi : i ≤ n) (p : List ℤ) (hp : p.length = n + 1)
    (hp0 : ent p 0 = 0) :
    ∑ k ∈ Finset.Icc 1 n, ((ent p k : ℚ)) * krawtchouk n q k i
      = ((dotp p (krawColQ n q i) : ℤ) : ℚ) := by
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [dotp_eq_sum p (krawColQ n q i) (n + 1) hp (length_krawColQ n q i)]
  push_cast
  rw [hrange, Finset.sum_insert (by simp)]
  rw [hp0]
  simp only [Int.cast_zero, zero_mul, zero_add]
  exact (Finset.sum_congr rfl fun k _ => by rw [krawColQ_getD n q i hi k]).symm

theorem sum_eq_dotp (n i : ℕ) (hi : i ≤ n) (p : List ℤ) (hp : p.length = n + 1)
    (hp0 : ent p 0 = 0) :
    ∑ k ∈ Finset.Icc 1 n, ((ent p k : ℚ)) * krawtchouk n 2 k i
      = ((dotp p (krawCol n i) : ℤ) : ℚ) := by
  rw [krawCol_eq]
  exact sum_eq_dotpQ n 2 i hi p hp hp0

/-- The scaled certificate, read back as a rational one. -/
def ratOfInt (p : List ℤ) (D : ℤ) (k : ℕ) : ℚ := (ent p k : ℚ) / (D : ℚ)

/-- Dual feasibility in `ℤ`, at any alphabet size: the certificate `p` scaled by
`D`. Every conjunct is decidable by kernel reduction of integer arithmetic. -/
def intCheckQ (n q d : ℕ) (p : List ℤ) (D : ℤ) : Bool :=
  decide (p.length = n + 1) && decide (ent p 0 = 0) && decide (0 < D) &&
    p.all (fun x => decide (0 ≤ x)) &&
    (krawTableQ n q).all (fun ic => decide (ic.1 < d) || decide (D ≤ -dotp p ic.2))

/-- The bound test: `1 + (∑ p k K_k(0)) / D ≤ B`, cleared of its denominator. -/
def intBoundLeQ (n q : ℕ) (p : List ℤ) (D B : ℤ) : Bool :=
  decide (D + dotp p (pascalRowQ q n) ≤ B * D)

theorem dualCert_of_intCheckQ {n q d : ℕ} {p : List ℤ} {D : ℤ}
    (h : intCheckQ n q d p D = true) : DualCert n q d (ratOfInt p D) := by
  simp only [intCheckQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨hlen, hp0⟩, hD⟩, hpos⟩, hslack⟩ := h
  have hD' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  constructor
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hklen : k < p.length := by omega
    have hmem := hpos _ (ent_mem p k hklen)
    have : (0 : ℚ) ≤ (ent p k : ℚ) := by exact_mod_cast hmem
    exact div_nonneg this (le_of_lt hD')
  · intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨hdi, hin⟩ := hi
    have hik := hslack (i, krawColQ n q i) (mem_krawTableQ n q i hin)
    have hik' : D ≤ -dotp p (krawColQ n q i) := by
      rcases hik with h | h
      · exact absurd h (by omega)
      · exact h
    have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n q k i
        = ((dotp p (krawColQ n q i) : ℤ) : ℚ) / (D : ℚ) := by
      simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
      rw [sum_eq_dotpQ n q i hin p hlen hp0]
    have hkey : (D : ℚ) ≤ -((dotp p (krawColQ n q i) : ℤ) : ℚ) := by
      have : ((D : ℤ) : ℚ) ≤ ((-dotp p (krawColQ n q i) : ℤ) : ℚ) := by exact_mod_cast hik'
      push_cast at this ⊢
      linarith
    rw [dualSlack, hsum, ← neg_div, le_div_iff₀ hD']
    linarith

/-- **The integer verifier, at any alphabet size.** A scaled dual certificate that
the kernel accepts bounds `A n q d`.

Soundness goes through `A_le_bound_of_dualCert_qary`, which needs only `q ≥ 1`;
nothing on this path is binary. -/
theorem A_le_of_intCertQ {n q d B : ℕ} {p : List ℤ} {D : ℤ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (h : intCheckQ n q d p D = true) (hb : intBoundLeQ n q p D (B : ℤ) = true) :
    A n q d ≤ B := by
  have hcert := dualCert_of_intCheckQ h
  simp only [intCheckQ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, hp0⟩, hD⟩, -⟩, -⟩ := h
  have hD' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  simp only [intBoundLeQ, decide_eq_true_eq] at hb
  have key : (D : ℚ) + ((dotp p (pascalRowQ q n) : ℤ) : ℚ) ≤ (B : ℚ) * (D : ℚ) := by
    have : ((D + dotp p (pascalRowQ q n) : ℤ) : ℚ) ≤ (((B : ℤ) * D : ℤ) : ℚ) := by
      exact_mod_cast hb
    push_cast at this ⊢
    linarith
  have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n q k 0
      = ((dotp p (pascalRowQ q n) : ℤ) : ℚ) / (D : ℚ) := by
    simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_eq_dotpQ n q 0 (Nat.zero_le n) p hlen hp0, krawColQ]
  have hdiv : ((dotp p (pascalRowQ q n) : ℤ) : ℚ) / (D : ℚ) ≤ (B : ℚ) - 1 := by
    rw [div_le_iff₀ hD']
    nlinarith [key]
  have hbd : bound n q (ratOfInt p D) ≤ (B : ℚ) := by
    rw [bound, hsum]
    linarith
  have h1 : ((A n q d : ℕ) : ℚ) ≤ (B : ℚ) :=
    le_trans (A_le_bound_of_dualCert_qary hq hd hcert) hbd
  exact_mod_cast h1

/-! ## The binary check, unchanged, and derived

`intCheck` and `intBoundLe` keep their original definitions byte for byte: the
twenty-four generated certificates are `decide` proofs that reduce through them.
Only their soundness proofs are gone, replaced by the `q`-ary ones composed with
the bridge.
-/

/-- Dual feasibility in `ℤ`: the certificate `p` scaled by `D`. Every conjunct is
decidable by kernel reduction of integer arithmetic. -/
def intCheck (n d : ℕ) (p : List ℤ) (D : ℤ) : Bool :=
  decide (p.length = n + 1) && decide (ent p 0 = 0) && decide (0 < D) &&
    p.all (fun x => decide (0 ≤ x)) &&
    (krawTable n).all (fun ic => decide (ic.1 < d) || decide (D ≤ -dotp p ic.2))

/-- The bound test: `1 + (∑ p k K_k(0)) / D ≤ B`, cleared of its denominator. -/
def intBoundLe (n : ℕ) (p : List ℤ) (D B : ℤ) : Bool :=
  decide (D + dotp p (pascalRow n) ≤ B * D)

theorem intCheck_eq (n d : ℕ) (p : List ℤ) (D : ℤ) :
    intCheck n d p D = intCheckQ n 2 d p D := by
  rw [intCheck, intCheckQ, krawTable_eq]

theorem intBoundLe_eq (n : ℕ) (p : List ℤ) (D B : ℤ) :
    intBoundLe n p D B = intBoundLeQ n 2 p D B := by
  rw [intBoundLe, intBoundLeQ, pascalRow_eq]

theorem dualCert_of_intCheck {n d : ℕ} {p : List ℤ} {D : ℤ} (h : intCheck n d p D = true) :
    DualCert n 2 d (ratOfInt p D) :=
  dualCert_of_intCheckQ (by rwa [intCheck_eq] at h)

/-- **The integer verifier.** A scaled dual certificate that the kernel accepts
bounds `A n 2 d`. -/
theorem A_le_of_intCert {n d B : ℕ} {p : List ℤ} {D : ℤ} (hd : 1 ≤ d)
    (h : intCheck n d p D = true) (hb : intBoundLe n p D (B : ℤ) = true) :
    A n 2 d ≤ B :=
  A_le_of_intCertQ (by norm_num) hd (by rwa [intCheck_eq] at h) (by rwa [intBoundLe_eq] at hb)

/-! ## The check rejects, and says so in the language of the LP

`intCheck = false` on its own only says the verifier refused. This turns a single
violated constraint into the statement that no dual certificate is there to be
had — which is what a negative control has to say.
-/

theorem not_dualCert_of_intSlackQ {n q d : ℕ} {p : List ℤ} {D : ℤ} (hlen : p.length = n + 1)
    (hp0 : ent p 0 = 0) (hD : 0 < D) {i : ℕ} (hdi : d ≤ i) (hin : i ≤ n)
    (h : -dotp p (krawColQ n q i) < D) : ¬ DualCert n q d (ratOfInt p D) := by
  intro hcert
  have hD' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hslack := hcert.2 i (Finset.mem_Icc.mpr ⟨hdi, hin⟩)
  have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n q k i
      = ((dotp p (krawColQ n q i) : ℤ) : ℚ) / (D : ℚ) := by
    simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_eq_dotpQ n q i hin p hlen hp0]
  rw [dualSlack, hsum, ← neg_div, le_div_iff₀ hD'] at hslack
  have hlt : ((-dotp p (krawColQ n q i) : ℤ) : ℚ) < ((D : ℤ) : ℚ) := by exact_mod_cast h
  push_cast at hslack hlt
  linarith

theorem not_dualCert_of_intSlack {n d : ℕ} {p : List ℤ} {D : ℤ} (hlen : p.length = n + 1)
    (hp0 : ent p 0 = 0) (hD : 0 < D) {i : ℕ} (hdi : d ≤ i) (hin : i ≤ n)
    (h : -dotp p (krawCol n i) < D) : ¬ DualCert n 2 d (ratOfInt p D) :=
  not_dualCert_of_intSlackQ hlen hp0 hD hdi hin (by rwa [krawCol_eq] at h)

/-! ## Negative controls

A verifier that has never refused anything has not been tested. These are the four
ways the encoding can be wrong, plus one vector that is simply infeasible.
-/

/-- The zero certificate is not dual feasible: every slack is `0 < 1`. Proved, not
merely refused by the `Bool`. -/
theorem not_dualCert_zero_intCert :
    ¬ DualCert 5 2 3 (ratOfInt [0, 0, 0, 0, 0, 0] 1) :=
  not_dualCert_of_intSlack (n := 5) (d := 3) (i := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- The `#`-command linter is off here on purpose: these commands are the replay.
set_option linter.hashCommand false

-- The table agrees with the binomial definition of `krawtchouk`, entry by entry.
-- Two evaluations that share nothing: Pascal plus differences on one side, an
-- alternating sum of binomial coefficients on the other.
#guard (List.range 8).all fun i =>
  (List.range 8).all fun k => ((ent (krawCol 7 i) k : ℚ)) == krawtchouk 7 2 k i

#guard krawCol 5 0 == [1, 5, 10, 10, 5, 1]
#guard krawCol 5 1 == [1, 3, 2, -2, -3, -1]
#guard krawCol 5 5 == [1, -5, 10, -10, 5, -1]

-- A certificate the check accepts: `y 1 = 1` at `n = 5`, `d = 3`.
#guard intCheck 5 3 [0, 1, 0, 0, 0, 0] 1

-- and the four malformed encodings, each refused
#guard !intCheck 5 3 [0, 1, 0, 0, 0, 0] 0          -- denominator zero
#guard !intCheck 5 3 [1, 1, 0, 0, 0, 0] 1          -- index 0 not zero
#guard !intCheck 5 3 [0, -1, 0, 0, 0, 0] 1         -- a negative coefficient
#guard !intCheck 5 3 [0, 1, 0, 0, 0] 1             -- wrong length

-- and an infeasible one: halving the certificate halves every slack
#guard !intCheck 5 3 [0, 1, 0, 0, 0, 0] 2

end Delsarte.Certificate
-- probe
