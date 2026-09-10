/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Verify

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
  `K_(k+1)(i+1) = K_(k+1)(i) - K_k(i) - K_k(i+1)` (`Delsarte.krawtchouk_diff` at
  `q = 2`), starting from the Pascal row `K_k(0) = C(n,k)`. Neither step divides,
  so nothing leaves `ℤ`;
* the table is built once, as a list, and every column is shared. `Nat.choose`
  never appears: it is unusable in the kernel, whereas one Pascal row is `O(n²)`
  additions.

The whole check is then `decide`, and the certificate proofs cost milliseconds
instead of tens of seconds. `native_decide` is *not* used anywhere: the kernel
does the reduction, so no compiler enters the trust base.
-/

namespace Delsarte.Certificate

open Finset Delsarte

/-! ## Entries

A private accessor, rather than `List.getD`: the simp set normalizes `List.getD`
into `l[k]?.getD`, which makes every rewrite below miss. `ent` is opaque to simp
and its three equations are `rfl`.
-/

/-- Entry `k` of a list of integers, zero outside the list. -/
def ent : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, (k + 1) => ent l k

@[simp] theorem ent_nil (k : ℕ) : ent [] k = 0 := rfl

@[simp] theorem ent_cons_zero (a : ℤ) (l : List ℤ) : ent (a :: l) 0 = a := rfl

@[simp] theorem ent_cons_succ (a : ℤ) (l : List ℤ) (k : ℕ) :
    ent (a :: l) (k + 1) = ent l k := rfl

theorem ent_eq_zero_of_length_le : ∀ (l : List ℤ) (k : ℕ), l.length ≤ k → ent l k = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: l, (k + 1), h => ent_eq_zero_of_length_le l k (by simpa using h)

theorem ent_mem : ∀ (l : List ℤ) (k : ℕ), k < l.length → ent l k ∈ l
  | [], _, h => absurd h (by simp)
  | a :: _, 0, _ => List.mem_cons_self ..
  | _ :: l, (k + 1), h => List.mem_cons_of_mem _ (ent_mem l k (by simpa using h))

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

/-- Integer inner product of a scaled certificate with a column. -/
def dotp (p col : List ℤ) : ℤ := (List.zipWith (· * ·) p col).sum

/-! ## Lengths -/

theorem length_pascalAux (p : ℤ) (l : List ℤ) : (pascalAux p l).length = l.length + 1 := by
  induction l generalizing p with
  | nil => rfl
  | cons a as ih => simp [pascalAux, ih]

theorem length_pascalRow (n : ℕ) : (pascalRow n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pascalRow, length_pascalAux, ih]

theorem length_krawStepAux (po pn : ℤ) (l : List ℤ) :
    (krawStepAux po pn l).length = l.length := by
  induction l generalizing po pn with
  | nil => rfl
  | cons a as ih => simp [krawStepAux, ih]

theorem length_krawStep (l : List ℤ) : (krawStep l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a as => simp [krawStep, length_krawStepAux]

theorem length_krawCol (n i : ℕ) : (krawCol n i).length = n + 1 := by
  induction i with
  | zero => exact length_pascalRow n
  | succ i ih => rw [krawCol, length_krawStep, ih]

/-! ## The Pascal row is the first column -/

theorem pascalAux_getD_zero (p : ℤ) (l : List ℤ) :
    ent (pascalAux p l) 0 = p + ent l 0 := by
  cases l <;> simp [pascalAux]

theorem pascalAux_getD_succ (p : ℤ) (l : List ℤ) (k : ℕ) :
    ent (pascalAux p l) (k + 1) = ent l k + ent l (k + 1) := by
  induction l generalizing p k with
  | nil => cases k <;> simp [pascalAux]
  | cons a as ih =>
    cases k with
    | zero => simp [pascalAux, pascalAux_getD_zero]
    | succ k => simpa [pascalAux] using ih a k

theorem pascalRow_getD (n k : ℕ) : ent (pascalRow n) k = (n.choose k : ℤ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [pascalRow]
  | succ n ih =>
    cases k with
    | zero => rw [pascalRow, pascalAux_getD_zero, ih]; simp
    | succ k =>
      rw [pascalRow, pascalAux_getD_succ, ih, ih, Nat.choose_succ_succ]
      push_cast
      ring

/-! ## One step of the difference recurrence -/

theorem krawStepAux_getD_zero (po pn : ℤ) (l : List ℤ) (hl : l ≠ []) :
    ent (krawStepAux po pn l) 0 = ent l 0 - po - pn := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simp [krawStepAux]

theorem krawStepAux_getD_succ (po pn : ℤ) (l : List ℤ) (k : ℕ) (hk : k + 1 < l.length) :
    ent (krawStepAux po pn l) (k + 1)
      = ent l (k + 1) - ent l k - ent (krawStepAux po pn l) k := by
  induction l generalizing po pn k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero =>
      have has : as ≠ [] := by
        intro h; rw [h] at hk; simp at hk
      simp only [krawStepAux, ent_cons_succ, ent_cons_zero]
      rw [krawStepAux_getD_zero _ _ _ has]
    | succ k =>
      have hk' : k + 1 < as.length := by simpa using hk
      simpa [krawStepAux] using ih a (a - po - pn) k hk'

theorem krawStep_getD_zero (l : List ℤ) (hl : l ≠ []) : ent (krawStep l) 0 = 1 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simp [krawStep]

/-- The list step realizes the difference recurrence. The hypothesis `ent l 0 = 1`
is `K_0(i) = 1`, which `krawStep` hardcodes in its head. -/
theorem krawStep_getD_succ (l : List ℤ) (h0 : ent l 0 = 1) (k : ℕ) (hk : k + 1 < l.length) :
    ent (krawStep l) (k + 1)
      = ent l (k + 1) - ent l k - ent (krawStep l) k := by
  cases l with
  | nil => simp at hk
  | cons a as =>
    have ha : a = 1 := by simpa using h0
    subst ha
    cases k with
    | zero =>
      have has : as ≠ [] := by
        intro h; rw [h] at hk; simp at hk
      simp only [krawStep, ent_cons_succ, ent_cons_zero]
      rw [krawStepAux_getD_zero _ _ _ has]
    | succ k =>
      have hk' : k + 1 < as.length := by simpa using hk
      simpa [krawStep] using krawStepAux_getD_succ 1 1 as k hk'

/-! ## The table is the Krawtchouk table -/

theorem krawCol_getD_zero (n i : ℕ) : ent (krawCol n i) 0 = 1 := by
  induction i with
  | zero => rw [krawCol, pascalRow_getD]; simp
  | succ i ih =>
    refine krawStep_getD_zero _ ?_
    intro h
    have := length_krawCol n i
    rw [h] at this
    simp at this

/-- **Correctness of the integer table.** Every entry is the Krawtchouk value it
claims to be, out-of-range indices included, where both sides are zero. -/
theorem krawCol_getD (n : ℕ) :
    ∀ i, i ≤ n → ∀ k, (ent (krawCol n i) k : ℚ) = krawtchouk n 2 k i := by
  intro i
  induction i with
  | zero =>
    intro _ k
    rw [krawCol, pascalRow_getD, krawtchouk_zero_right]
    norm_num
  | succ i ih =>
    intro hi k
    have hi' : i ≤ n := by omega
    have hin : i < n := by omega
    induction k with
    | zero =>
      rw [krawCol_getD_zero, krawtchouk_zero_left]
      norm_num
    | succ k ihk =>
      by_cases hkn : k + 1 ≤ n
      · have hlen : k + 1 < (krawCol n i).length := by rw [length_krawCol]; omega
        rw [krawCol, krawStep_getD_succ _ (krawCol_getD_zero n i) k hlen]
        push_cast
        rw [ih hi' (k + 1), ih hi' k, ← krawCol, ihk]
        rw [krawtchouk_diff n 2 k i hin]
        norm_num
      · have h1 : ent (krawCol n (i + 1)) (k + 1) = 0 :=
          ent_eq_zero_of_length_le _ _ (by rw [length_krawCol]; omega)
        rw [h1, krawtchouk_eq_zero_of_lt n 2 (k + 1) (i + 1) hi (by omega)]
        norm_num

theorem krawTableAux_eq (n i : ℕ) :
    krawTableAux n i = ((List.range (i + 1)).reverse).map (fun j => (j, krawCol n j)) := by
  induction i with
  | zero => simp [krawTableAux, krawCol]
  | succ i ih =>
    have hr : ∀ m : ℕ, (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      intro m; rw [List.range_succ, List.reverse_append]; simp
    rw [krawTableAux, ih, hr, List.map_cons, hr (i + 1), List.map_cons, hr, List.map_cons,
      krawCol]

/-- Every column of index at most `n` is in the table, paired with its index. -/
theorem mem_krawTable (n i : ℕ) (hi : i ≤ n) : (i, krawCol n i) ∈ krawTable n := by
  rw [krawTable, krawTableAux_eq]
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  simp only [List.mem_reverse, List.mem_range]
  omega

/-! ## From the integer check to the rational certificate -/

theorem dotp_eq_sum (p col : List ℤ) (m : ℕ) (hp : p.length = m) (hc : col.length = m) :
    dotp p col = ∑ k ∈ Finset.range m, ent p k * ent col k := by
  induction p generalizing col m with
  | nil =>
    simp only [List.length_nil] at hp
    subst hp
    simp [dotp]
  | cons a as ih =>
    cases col with
    | nil =>
      exfalso
      simp only [List.length_nil, List.length_cons] at hp hc
      omega
    | cons b bs =>
      have hm : m = as.length + 1 := by
        simp only [List.length_cons] at hp
        omega
      subst hm
      have hbs : bs.length = as.length := by
        simp only [List.length_cons] at hc
        omega
      rw [Finset.sum_range_succ']
      simp only [ent_cons_succ, ent_cons_zero]
      rw [← ih bs as.length rfl hbs]
      simp only [dotp, List.zipWith_cons_cons, List.sum_cons]
      ring

/-- The dual constraint, in one integer inner product. -/
theorem sum_eq_dotp (n i : ℕ) (hi : i ≤ n) (p : List ℤ) (hp : p.length = n + 1)
    (hp0 : ent p 0 = 0) :
    ∑ k ∈ Finset.Icc 1 n, ((ent p k : ℚ)) * krawtchouk n 2 k i
      = ((dotp p (krawCol n i) : ℤ) : ℚ) := by
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [dotp_eq_sum p (krawCol n i) (n + 1) hp (length_krawCol n i)]
  push_cast
  rw [hrange, Finset.sum_insert (by simp)]
  rw [hp0]
  simp only [Int.cast_zero, zero_mul, zero_add]
  exact (Finset.sum_congr rfl fun k _ => by rw [krawCol_getD n i hi k]).symm

/-- The scaled certificate, read back as a rational one. -/
def ratOfInt (p : List ℤ) (D : ℤ) (k : ℕ) : ℚ := (ent p k : ℚ) / (D : ℚ)

/-- Dual feasibility in `ℤ`: the certificate `p` scaled by `D`. Every conjunct is
decidable by kernel reduction of integer arithmetic. -/
def intCheck (n d : ℕ) (p : List ℤ) (D : ℤ) : Bool :=
  decide (p.length = n + 1) && decide (ent p 0 = 0) && decide (0 < D) &&
    p.all (fun x => decide (0 ≤ x)) &&
    (krawTable n).all (fun ic => decide (ic.1 < d) || decide (D ≤ -dotp p ic.2))

/-- The bound test: `1 + (∑ p k K_k(0)) / D ≤ B`, cleared of its denominator. -/
def intBoundLe (n : ℕ) (p : List ℤ) (D B : ℤ) : Bool :=
  decide (D + dotp p (pascalRow n) ≤ B * D)

theorem dualCert_of_intCheck {n d : ℕ} {p : List ℤ} {D : ℤ} (h : intCheck n d p D = true) :
    DualCert n 2 d (ratOfInt p D) := by
  simp only [intCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
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
    have hik := hslack (i, krawCol n i) (mem_krawTable n i hin)
    have hik' : D ≤ -dotp p (krawCol n i) := by
      rcases hik with h | h
      · exact absurd h (by omega)
      · exact h
    have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n 2 k i
        = ((dotp p (krawCol n i) : ℤ) : ℚ) / (D : ℚ) := by
      simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
      rw [sum_eq_dotp n i hin p hlen hp0]
    have hkey : (D : ℚ) ≤ -((dotp p (krawCol n i) : ℤ) : ℚ) := by
      have : ((D : ℤ) : ℚ) ≤ ((-dotp p (krawCol n i) : ℤ) : ℚ) := by exact_mod_cast hik'
      push_cast at this ⊢
      linarith
    rw [dualSlack, hsum, ← neg_div, le_div_iff₀ hD']
    linarith

/-- **The integer verifier.** A scaled dual certificate that the kernel accepts
bounds `A n 2 d`. -/
theorem A_le_of_intCert {n d B : ℕ} {p : List ℤ} {D : ℤ} (hd : 1 ≤ d)
    (h : intCheck n d p D = true) (hb : intBoundLe n p D (B : ℤ) = true) :
    A n 2 d ≤ B := by
  have hcert := dualCert_of_intCheck h
  simp only [intCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, hp0⟩, hD⟩, -⟩, -⟩ := h
  have hD' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  simp only [intBoundLe, decide_eq_true_eq] at hb
  have key : (D : ℚ) + ((dotp p (pascalRow n) : ℤ) : ℚ) ≤ (B : ℚ) * (D : ℚ) := by
    have : ((D + dotp p (pascalRow n) : ℤ) : ℚ) ≤ (((B : ℤ) * D : ℤ) : ℚ) := by
      exact_mod_cast hb
    push_cast at this ⊢
    linarith
  refine A_le_of_dualCert hd hcert ?_
  have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n 2 k 0
      = ((dotp p (pascalRow n) : ℤ) : ℚ) / (D : ℚ) := by
    simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_eq_dotp n 0 (Nat.zero_le n) p hlen hp0, krawCol]
  have hdiv : ((dotp p (pascalRow n) : ℤ) : ℚ) / (D : ℚ) ≤ (B : ℚ) - 1 := by
    rw [div_le_iff₀ hD']
    nlinarith [key]
  rw [bound, hsum]
  linarith

/-! ## The check rejects, and says so in the language of the LP

`intCheck = false` on its own only says the verifier refused. This turns a single
violated constraint into the statement that no dual certificate is there to be
had — which is what a negative control has to say.
-/

theorem not_dualCert_of_intSlack {n d : ℕ} {p : List ℤ} {D : ℤ} (hlen : p.length = n + 1)
    (hp0 : ent p 0 = 0) (hD : 0 < D) {i : ℕ} (hdi : d ≤ i) (hin : i ≤ n)
    (h : -dotp p (krawCol n i) < D) : ¬ DualCert n 2 d (ratOfInt p D) := by
  intro hcert
  have hD' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hslack := hcert.2 i (Finset.mem_Icc.mpr ⟨hdi, hin⟩)
  have hsum : ∑ k ∈ Finset.Icc 1 n, ratOfInt p D k * krawtchouk n 2 k i
      = ((dotp p (krawCol n i) : ℤ) : ℚ) / (D : ℚ) := by
    simp only [ratOfInt, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_eq_dotp n i hin p hlen hp0]
  rw [dualSlack, hsum, ← neg_div, le_div_iff₀ hD'] at hslack
  have hlt : ((-dotp p (krawCol n i) : ℤ) : ℚ) < ((D : ℤ) : ℚ) := by exact_mod_cast h
  push_cast at hslack hlt
  linarith

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
