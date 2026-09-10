/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.Shell
import Delsarte.Hamming.DistDist

/-!
# Primal feasibility of the distance distribution, for every alphabet size

The theorem the `q`-ary half of the Hamming side rests on: for every code `C`
over an alphabet of size `q ≥ 1` and every Krawtchouk degree `k`,

`∑_i a_i K_k(i) ≥ 0`,

where `a` is the distance distribution of `C`. No linearity is assumed: `C` is an
arbitrary `Finset` of words. Combined with `Delsarte.Hamming.primalFeasible_codeVec`
this discharges the hypothesis that `Delsarte/Hamming/LP.lean` carries, so
`A_le_of_dualFeasible_qary` bounds `A n q d` outright — for every `q`, where
`A_le_of_dualFeasible_binary` covered only `q = 2`.

## Why this file needs `ℂ` and the binary one does not

`Delsarte/Hamming/Feasible.lean` proves the same statement at `q = 2` without any
analysis: binary characters take values in `{±1} ⊆ ℚ`, so the sum is a sum of
squares of rationals. That route is genuinely closed for `q > 2`, not merely
awkward — `Delsarte.Hamming.chiQ_one_ne_neg_one_zmod_three` shows a character
value at `q = 3` that is neither `1` nor `-1`, so no relabelling produces a
rational-valued character.

The proof here is the same identity read over `ℂ`: the double sum over ordered
pairs is `∑_u ‖∑_{x ∈ C} χ_u(x)‖²`, a sum of squared moduli, one term per index
vector of weight `k`. `Delsarte/Hamming/Shell.lean` supplies the shell identity
that turns the inner sum into `K_k`, and `chiVec_mul_conj` is what makes the
double sum a squared modulus rather than a bare product.

## The descent to `ℚ`

Everything the repository verifies is exact over `ℚ`, so a positivity statement
living in `ℝ` or `ℂ` would be useless here. The chain is explicit and it is the
whole content of `sum_sum_krawtchouk_nonneg_zmod`: the identity holds in `ℂ`
between the cast of a rational and the cast of a real; `Complex.ofReal` is
injective, so it holds in `ℝ`; the real side is a sum of `Complex.normSq`, hence
nonnegative; and `Rat.cast` is order-reflecting, so the rational is nonnegative.
No cyclotomic ring, and no algebraic number theory.

## The shape of the alphabet hypothesis

`Word n q := Fin n → Fin q`, and `ZMod (m + 1)` *is* `Fin (m + 1)`, so a code over
an alphabet of size `m + 1` already is a set of vectors over `ZMod (m + 1)` with
nothing to transport — see `Delsarte.Hamming.zmod_succ_eq_fin`. The statements
below are therefore proved at `m + 1` and exposed at `1 ≤ q`, which is where
`obtain ⟨m, rfl⟩` happens, once.
-/

namespace Delsarte.Hamming

open Finset Delsarte.LP Delsarte

variable {n d m : ℕ} {q : ℕ} [NeZero q]

/-- **The Delsarte identity over `ℂ`.** The double sum of `K_k` over ordered pairs
of codewords is a sum of squared moduli, one per index vector of weight `k`. -/
theorem sum_normSq_shell_eq (C : Finset (Fin n → ZMod q)) (k : ℕ) :
    ((∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k),
        Complex.normSq (∑ x ∈ C, chiVec u x) : ℝ) : ℂ)
      = ((∑ x ∈ C, ∑ y ∈ C, krawtchouk n q k (hammingDist x y) : ℚ) : ℂ) := by
  have h1 : ∀ u : Fin n → ZMod q,
      ((Complex.normSq (∑ x ∈ C, chiVec u x) : ℝ) : ℂ)
        = ∑ x ∈ C, ∑ y ∈ C, chiVec u (x - y) := by
    intro u
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => chiVec_mul_conj u x y
  have h2 : ∀ x y : Fin n → ZMod q,
      (∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k), chiVec u (x - y))
        = ((krawtchouk n q k (hammingDist x y) : ℚ) : ℂ) := by
    intro x y
    rw [sum_chiVec_shell, card_suppQ_sub]
  calc ((∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k),
        Complex.normSq (∑ x ∈ C, chiVec u x) : ℝ) : ℂ)
      = ∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k),
          ((Complex.normSq (∑ x ∈ C, chiVec u x) : ℝ) : ℂ) := by push_cast; ring
    _ = ∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k),
          ∑ x ∈ C, ∑ y ∈ C, chiVec u (x - y) :=
        Finset.sum_congr rfl fun u _ => h1 u
    _ = ∑ x ∈ C, ∑ y ∈ C,
          ∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k), chiVec u (x - y) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ C, ∑ y ∈ C, ((krawtchouk n q k (hammingDist x y) : ℚ) : ℂ) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h2 x y
    _ = ((∑ x ∈ C, ∑ y ∈ C, krawtchouk n q k (hammingDist x y) : ℚ) : ℂ) := by
        push_cast; ring

/-- **Delsarte positivity, unnormalised, for every alphabet size.** The descent
from `ℂ` to `ℚ` is explicit: the identity above, injectivity of `Complex.ofReal`,
nonnegativity of `Complex.normSq`, then order-reflection of `Rat.cast`. -/
theorem sum_sum_krawtchouk_nonneg_zmod (C : Finset (Fin n → ZMod q)) (k : ℕ) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, krawtchouk n q k (hammingDist x y) := by
  have hR : 0 ≤ ∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k),
      Complex.normSq (∑ x ∈ C, chiVec u x) :=
    Finset.sum_nonneg fun u _ => Complex.normSq_nonneg _
  have hRQ : (∑ u ∈ univ.filter (fun u : Fin n → ZMod q => wtQ u = k),
      Complex.normSq (∑ x ∈ C, chiVec u x))
      = ((∑ x ∈ C, ∑ y ∈ C, krawtchouk n q k (hammingDist x y) : ℚ) : ℝ) := by
    exact_mod_cast sum_normSq_shell_eq C k
  rw [hRQ] at hR
  exact_mod_cast hR

/-- Delsarte positivity on the distance distribution, at an alphabet of size
`m + 1`. -/
theorem sum_distDist_mul_krawtchouk_nonneg_succ (C : Code n (m + 1)) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n (m + 1) k i := by
  rw [sum_distDist_mul_krawtchouk C k]
  exact div_nonneg (sum_sum_krawtchouk_nonneg_zmod (q := m + 1) C k) (by positivity)

/-- The distance distribution of a code over an alphabet of size `m + 1` is a
feasible point of the Delsarte primal. -/
theorem primalFeasible_distDist_succ (hd : 1 ≤ d) {C : Code n (m + 1)} (hC : C.Nonempty)
    (hmin : MinDistAtLeast d C) :
    PrimalFeasible (delsarteMatrix n (m + 1) d) (delsarteRHS n (m + 1)) (codeVec C d) :=
  primalFeasible_codeVec fun k _ =>
    delsarte_positivity_of_nonneg hd hC hmin k (sum_distDist_mul_krawtchouk_nonneg_succ C k)

omit [NeZero q] in
/-- **Primal feasibility for every alphabet size.** The `q`-ary counterpart of
`Delsarte.Hamming.primalFeasible_distDist`, which covers `q = 2` only. -/
theorem primalFeasible_distDist_qary (hq : 1 ≤ q) (hd : 1 ≤ d) {C : Code n q}
    (hC : C.Nonempty) (hmin : MinDistAtLeast d C) :
    PrimalFeasible (delsarteMatrix n q d) (delsarteRHS n q) (codeVec C d) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  exact primalFeasible_distDist_succ hd hC hmin

omit [NeZero q] in
/-- **The Delsarte bound for `q`-ary codes**, with no remaining hypothesis: any
dual-feasible `y` bounds `A n q d`. The `binary` suffix is gone because the
restriction is gone. -/
theorem A_le_of_dualFeasible_qary (hq : 1 ≤ q) (hd : 1 ≤ d) {y : ConIdx n → ℚ}
    (hy : DualFeasible (delsarteMatrix n q d) (delsarteObj n d) y) :
    (A n q d : ℚ) ≤ 1 + delsarteRHS n q ⬝ᵥ y :=
  A_le_of_dualFeasible hd hq (fun _ hC hmin => primalFeasible_distDist_qary hq hd hC hmin) hy

/-! ### Negative control

A verifier that has never refused anything has proved nothing, and the binary
control (`n = 5`, `q = 2`) does not exercise a single line of this file.

Take `n = 2`, `q = 3` and the candidate distance distribution `(1, 0, 3)`. It
passes every obvious sanity check: it is nonnegative, it starts at `1`, and it
sums to `4`, so it looks like the distribution of a four-word ternary code of
length `2` with all pairs at distance `2`. Delsarte at `k = 1` refuses it, and
that is the only thing that does.
-/

theorem krawtchouk_two_three_one_zero : krawtchouk 2 3 1 0 = 4 := by
  norm_num [krawtchouk, Finset.sum_range_succ]

theorem krawtchouk_two_three_one_two : krawtchouk 2 3 1 2 = -2 := by
  norm_num [krawtchouk, Finset.sum_range_succ]

/-- No ternary code of length `2` has distance distribution `(1, 0, 3)`: the
Delsarte constraint at `k = 1` gives `1 · 4 + 0 · 1 + 3 · (-2) = -2 < 0`. -/
theorem no_code_distDist_one_zero_three (C : Code 2 3)
    (h0 : distDist C 0 = 1) (h1 : distDist C 1 = 0) (h2 : distDist C 2 = 3) : False := by
  have hnn := sum_distDist_mul_krawtchouk_nonneg_succ (m := 2) (n := 2) C 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2] at hnn
  norm_num [krawtchouk, Finset.sum_range_succ] at hnn

end Delsarte.Hamming
