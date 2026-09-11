/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Krawtchouk.Basic

/-!
# The integer Krawtchouk table, for any alphabet

`Delsarte/Certificate/Integer.lean` decides dual feasibility by kernel reduction,
which forces the whole computation into `ℤ`: no division anywhere. This file holds
the table it reduces over, built for an arbitrary alphabet size `q`.

## Why the table is division-free at every `q`

Two facts from `Delsarte/Krawtchouk/Basic.lean`, both already stated for arbitrary
`q`, are all that is needed:

* `krawtchouk_zero_right`: `K_k(0) = C(n,k) (q-1)^k`. Column `0` is therefore a
  **weighted Pascal row**, `W(n+1,k) = W(n,k) + (q-1) W(n,k-1)`, which is Pascal's
  rule with one extra factor and no division;
* `krawtchouk_diff`: `K_(k+1)(i+1) = K_(k+1)(i) - K_k(i) - (q-1) K_k(i+1)`, which
  takes column `i` to column `i+1` by integer subtractions alone.

So nothing about `q` reintroduces a denominator, and `decide` remains the verifier.

## The one place an error would hide

In `krawStepAuxQ`, `po` is the previous entry of the **old** column and `pn` the
previous entry of the **new** one. The recurrence gives `po` the coefficient `1`
and `pn` the coefficient `(q-1)`. Swapping them is invisible at `q = 2`, where both
coefficients are `1`, and wrong everywhere else.

`krawStepAuxWrong` below is that swap, written out. `krawStepAuxWrong_eq_two` shows
the two agree at `q = 2`, and `krawStepAuxWrong_ne_three` shows they disagree at
`q = 3` — so the control has teeth, and a reader can see what the binary tests
could never have caught.

## Structure

Every definition is structurally recursive with one recursive call, so kernel
reduction visits each column once. Written as `fun i => (recurrence applied i
times)`, the same table would be recomputed for every constraint.

This file knows nothing about the LP: no `DualCert`, no `A`. It imports only the
Krawtchouk polynomials.
-/

namespace Delsarte.Certificate

open Delsarte

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

/-- Integer inner product of a scaled certificate with a column. -/
def dotp (p col : List ℤ) : ℤ := (List.zipWith (· * ·) p col).sum

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

/-! ## The table, without division -/

/-- One step of the weighted Pascal rule, carrying the previous entry. The weight
`q - 1` is the only difference with Pascal's triangle. -/
def pascalAuxQ (q : ℕ) : ℤ → List ℤ → List ℤ
  | prev, [] => [((q : ℤ) - 1) * prev]
  | prev, a :: as => (((q : ℤ) - 1) * prev + a) :: pascalAuxQ q a as

/-- Column `0` of the table: `K_k(0) = C(n,k) (q-1)^k` for `k = 0, …, n`. -/
def pascalRowQ (q : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | (n + 1) => pascalAuxQ q 0 (pascalRowQ q n)

/-- One step of the difference recurrence, carrying the previous entry of the old
column (`po`, coefficient `1`) and of the new one (`pn`, coefficient `q - 1`). -/
def krawStepAuxQ (q : ℕ) : ℤ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | po, pn, a :: as =>
      (a - po - ((q : ℤ) - 1) * pn) :: krawStepAuxQ q a (a - po - ((q : ℤ) - 1) * pn) as

/-- Column `i + 1` from column `i`. The head is `K_0(i+1) = 1`. -/
def krawStepQ (q : ℕ) : List ℤ → List ℤ
  | [] => []
  | _ :: as => 1 :: krawStepAuxQ q 1 1 as

/-- Column `i` of the `q`-ary Krawtchouk table: `[K_0(i), …, K_n(i)]`. -/
def krawColQ (n q : ℕ) : ℕ → List ℤ
  | 0 => pascalRowQ q n
  | (i + 1) => krawStepQ q (krawColQ n q i)

/-- The table as an indexed list, built in one pass so that each column is
computed once. -/
def krawTableAuxQ (n q : ℕ) : ℕ → List (ℕ × List ℤ)
  | 0 => [(0, pascalRowQ q n)]
  | (i + 1) =>
      match krawTableAuxQ n q i with
      | [] => []
      | (j, c) :: cs => (i + 1, krawStepQ q c) :: (j, c) :: cs

/-- Columns `0` to `n` of the `q`-ary Krawtchouk table, each paired with its
index. -/
def krawTableQ (n q : ℕ) : List (ℕ × List ℤ) := krawTableAuxQ n q n

/-! ## Lengths -/

theorem length_pascalAuxQ (q : ℕ) (p : ℤ) (l : List ℤ) :
    (pascalAuxQ q p l).length = l.length + 1 := by
  induction l generalizing p with
  | nil => rfl
  | cons a as ih => simp [pascalAuxQ, ih]

theorem length_pascalRowQ (q n : ℕ) : (pascalRowQ q n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pascalRowQ, length_pascalAuxQ, ih]

theorem length_krawStepAuxQ (q : ℕ) (po pn : ℤ) (l : List ℤ) :
    (krawStepAuxQ q po pn l).length = l.length := by
  induction l generalizing po pn with
  | nil => rfl
  | cons a as ih => simp [krawStepAuxQ, ih]

theorem length_krawStepQ (q : ℕ) (l : List ℤ) : (krawStepQ q l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a as => simp [krawStepQ, length_krawStepAuxQ]

theorem length_krawColQ (n q i : ℕ) : (krawColQ n q i).length = n + 1 := by
  induction i with
  | zero => exact length_pascalRowQ q n
  | succ i ih => rw [krawColQ, length_krawStepQ, ih]

/-! ## The weighted Pascal row is column zero -/

theorem pascalAuxQ_getD_zero (q : ℕ) (p : ℤ) (l : List ℤ) :
    ent (pascalAuxQ q p l) 0 = ((q : ℤ) - 1) * p + ent l 0 := by
  cases l <;> simp [pascalAuxQ]

theorem pascalAuxQ_getD_succ (q : ℕ) (p : ℤ) (l : List ℤ) (k : ℕ) :
    ent (pascalAuxQ q p l) (k + 1) = ((q : ℤ) - 1) * ent l k + ent l (k + 1) := by
  induction l generalizing p k with
  | nil => cases k <;> simp [pascalAuxQ]
  | cons a as ih =>
    cases k with
    | zero => simp [pascalAuxQ, pascalAuxQ_getD_zero]
    | succ k => simpa [pascalAuxQ] using ih a k

theorem pascalRowQ_getD (q n k : ℕ) :
    ent (pascalRowQ q n) k = (n.choose k : ℤ) * ((q : ℤ) - 1) ^ k := by
  induction n generalizing k with
  | zero => cases k <;> simp [pascalRowQ]
  | succ n ih =>
    cases k with
    | zero => rw [pascalRowQ, pascalAuxQ_getD_zero, ih]; simp
    | succ k =>
      rw [pascalRowQ, pascalAuxQ_getD_succ, ih, ih, Nat.choose_succ_succ]
      push_cast
      ring

/-! ## One step of the difference recurrence -/

theorem krawStepAuxQ_getD_zero (q : ℕ) (po pn : ℤ) (l : List ℤ) (hl : l ≠ []) :
    ent (krawStepAuxQ q po pn l) 0 = ent l 0 - po - ((q : ℤ) - 1) * pn := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simp [krawStepAuxQ]

theorem krawStepAuxQ_getD_succ (q : ℕ) (po pn : ℤ) (l : List ℤ) (k : ℕ)
    (hk : k + 1 < l.length) :
    ent (krawStepAuxQ q po pn l) (k + 1)
      = ent l (k + 1) - ent l k - ((q : ℤ) - 1) * ent (krawStepAuxQ q po pn l) k := by
  induction l generalizing po pn k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero =>
      have has : as ≠ [] := by
        intro h; rw [h] at hk; simp at hk
      simp only [krawStepAuxQ, ent_cons_succ, ent_cons_zero]
      rw [krawStepAuxQ_getD_zero _ _ _ _ has]
    | succ k =>
      have hk' : k + 1 < as.length := by simpa using hk
      simpa [krawStepAuxQ] using ih a (a - po - ((q : ℤ) - 1) * pn) k hk'

theorem krawStepQ_getD_zero (q : ℕ) (l : List ℤ) (hl : l ≠ []) :
    ent (krawStepQ q l) 0 = 1 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simp [krawStepQ]

/-- The list step realizes the difference recurrence. The hypothesis `ent l 0 = 1`
is `K_0(i) = 1`, which `krawStepQ` hardcodes in its head. -/
theorem krawStepQ_getD_succ (q : ℕ) (l : List ℤ) (h0 : ent l 0 = 1) (k : ℕ)
    (hk : k + 1 < l.length) :
    ent (krawStepQ q l) (k + 1)
      = ent l (k + 1) - ent l k - ((q : ℤ) - 1) * ent (krawStepQ q l) k := by
  cases l with
  | nil => simp at hk
  | cons a as =>
    have ha : a = 1 := by simpa using h0
    subst ha
    cases k with
    | zero =>
      have has : as ≠ [] := by
        intro h; rw [h] at hk; simp at hk
      simp only [krawStepQ, ent_cons_succ, ent_cons_zero]
      rw [krawStepAuxQ_getD_zero _ _ _ _ has]
    | succ k =>
      have hk' : k + 1 < as.length := by simpa using hk
      simpa [krawStepQ] using krawStepAuxQ_getD_succ q 1 1 as k hk'

/-! ## The table is the Krawtchouk table -/

theorem krawColQ_getD_zero (n q i : ℕ) : ent (krawColQ n q i) 0 = 1 := by
  induction i with
  | zero => rw [krawColQ, pascalRowQ_getD]; simp
  | succ i ih =>
    refine krawStepQ_getD_zero _ _ ?_
    intro h
    have := length_krawColQ n q i
    rw [h] at this
    simp at this

/-- **Correctness of the integer table, at any alphabet size.** Every entry is the
Krawtchouk value it claims to be, out-of-range indices included, where both sides
are zero. -/
theorem krawColQ_getD (n q : ℕ) :
    ∀ i, i ≤ n → ∀ k, (ent (krawColQ n q i) k : ℚ) = krawtchouk n q k i := by
  intro i
  induction i with
  | zero =>
    intro _ k
    rw [krawColQ, pascalRowQ_getD, krawtchouk_zero_right]
    push_cast
    ring
  | succ i ih =>
    intro hi k
    have hi' : i ≤ n := by omega
    have hin : i < n := by omega
    induction k with
    | zero =>
      rw [krawColQ_getD_zero, krawtchouk_zero_left]
      norm_num
    | succ k ihk =>
      by_cases hkn : k + 1 ≤ n
      · have hlen : k + 1 < (krawColQ n q i).length := by rw [length_krawColQ]; omega
        rw [krawColQ, krawStepQ_getD_succ q _ (krawColQ_getD_zero n q i) k hlen]
        push_cast
        rw [ih hi' (k + 1), ih hi' k, ← krawColQ, ihk]
        rw [krawtchouk_diff n q k i hin]
      · have h1 : ent (krawColQ n q (i + 1)) (k + 1) = 0 :=
          ent_eq_zero_of_length_le _ _ (by rw [length_krawColQ]; omega)
        rw [h1, krawtchouk_eq_zero_of_lt n q (k + 1) (i + 1) hi (by omega)]
        norm_num

theorem krawTableAuxQ_eq (n q i : ℕ) :
    krawTableAuxQ n q i = ((List.range (i + 1)).reverse).map (fun j => (j, krawColQ n q j)) := by
  induction i with
  | zero => simp [krawTableAuxQ, krawColQ]
  | succ i ih =>
    have hr : ∀ m : ℕ, (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
      intro m; rw [List.range_succ, List.reverse_append]; simp
    rw [krawTableAuxQ, ih, hr, List.map_cons, hr (i + 1), List.map_cons, hr, List.map_cons,
      krawColQ]

/-- Every column of index at most `n` is in the table, paired with its index. -/
theorem mem_krawTableQ (n q i : ℕ) (hi : i ≤ n) : (i, krawColQ n q i) ∈ krawTableQ n q := by
  rw [krawTableQ, krawTableAuxQ_eq]
  refine List.mem_map.mpr ⟨i, ?_, rfl⟩
  simp only [List.mem_reverse, List.mem_range]
  omega

/-! ### Control: the coefficient placement

`krawStepAuxWrong` swaps the roles of `po` and `pn`. At `q = 2` both coefficients
are `1`, so the swap is a no-op and no binary test can see it. At `q = 3` the two
columns differ, and the correct one is the one the Krawtchouk definition gives.
-/

/-- The swap: `pn` given the coefficient `1` and `po` the coefficient `q - 1`. -/
def krawStepAuxWrong (q : ℕ) : ℤ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | po, pn, a :: as =>
      (a - pn - ((q : ℤ) - 1) * po) :: krawStepAuxWrong q a (a - pn - ((q : ℤ) - 1) * po) as

theorem krawStepAuxWrong_eq_two (po pn : ℤ) (l : List ℤ) :
    krawStepAuxWrong 2 po pn l = krawStepAuxQ 2 po pn l := by
  induction l generalizing po pn with
  | nil => rfl
  | cons a as ih =>
    have harg : a - pn - (((2 : ℕ) : ℤ) - 1) * po = a - po - (((2 : ℕ) : ℤ) - 1) * pn := by
      push_cast; ring
    rw [krawStepAuxWrong, krawStepAuxQ, harg, ih]

theorem krawStepAuxWrong_ne_three :
    krawStepAuxWrong 3 1 1 [4, 4] ≠ krawStepAuxQ 3 1 1 [4, 4] := by
  decide

/-- And the correct column is the Krawtchouk one: at `n = 2`, `q = 3`, column `1`
is `[1, 1, -2]`, where the swap would give `-5` in the last entry. -/
theorem krawColQ_two_three_one : krawColQ 2 3 1 = [1, 1, -2] := by
  decide

theorem krawtchouk_two_three_two_one : krawtchouk 2 3 2 1 = -2 := by
  norm_num [krawtchouk, Finset.sum_range_succ]

end Delsarte.Certificate
