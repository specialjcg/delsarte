/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.DistDist
import Delsarte.Hamming.Terwilliger

/-!
# The triple counts `λ^t_{i,j}` and the variables `x^t_{i,j}`

Issue #44. Schrijver's semidefinite program has one variable per orbit of ordered
triples of codewords. For `X, Y, Z` in a binary code `C` the three statistics are
`|X △ Y|`, `|X △ Z|` and `|(X △ Y) ∩ (X △ Z)|`; over `𝔽₂` the first two are Hamming
distances and the third counts the coordinates on which `X` differs from both. So

    λ^t_{i,j}(C) = #{ (X,Y,Z) ∈ C³ : |X△Y| = i, |X△Z| = j, |(X△Y)∩(X△Z)| = t },
    x^t_{i,j}(C) = λ^t_{i,j}(C) / ( |C| · mult n i j t ).

No `symmDiff` appears. The repository's idiom, set by `Delsarte/Hamming/Feasible.lean`,
is to filter coordinates on the fly rather than convert between `Word n 2` and
`Finset (Fin n)`, and mathlib's `hammingDist` is already `#{i | x i ≠ y i}`.

`mult` is **not** redefined here. `Delsarte/Hamming/Terwilliger.lean` defines it as
a cardinality and says why in its own docstring; a second definition by factorials
would be exactly the drift `tools/schrijver_algebra.py` warns about. This file is
the first to import both halves — `Terwilliger.lean`, which knew only mathlib, and
the code side — and they do not clash.

## What this file proves

The socle, and only it:

* `lambdaT_diag` — the `j = 0, t = 0` fibre of the triple product is the pair fibre
  `distDist` is built from. `|X△Z| = 0` forces `Z = X`, which makes `t = 0`
  automatic, so the third coordinate carries nothing the pair does not.
* `mult_zero_zero` — `mult n i 0 0 = n.choose i`, from the cardinal definition:
  `powersetCard 0` is a singleton and the intersection condition is vacuous.
* `xT_diag` — hence `x⁰_{i,0} = distDist C i / n.choose i`.
* `sum_choose_mul_xT_diag` — hence `∑ᵢ C(n,i) · x⁰_{i,0} = |C|`, the last line of
  issue #44's constraint list. The binomials cancel and what remains is
  `sum_distDist`; no counting happens here that `Delsarte/Code/Basic.lean` had not
  already done.

## What it does not

The four families (20)(i)–(iv) are **not** proved. (i) `x⁰_{0,0} = 1`, (iii)
invariance under permuting `(i, j, i+j−2t)`, (iv) vanishing when one of the three
lands in `1..d−1` look mechanical from the definitions; (ii),
`x⁰_{i,0} + x⁰_{j,0} ≤ 1 + x^t_{i,j}`, is an inclusion–exclusion inequality on sets
of translations and is the one that is not. So `hrows` — the hypothesis of
`A_..._le_of_relaxation` that this file exists to discharge — still stands, and
`Delsarte/Certificate/Relaxation.lean` still names it. Nothing about the blocks
(#45) is touched.

All four families were checked numerically before this file was written, on codes
built to have the stated minimum distance, in exact rational arithmetic: (i) gave
`1`, (iii) held on 1728 permutation pairs with none skipped, (ii) held on 453
cases, (iv) had no violation. (iv) also got a negative control — a code of distance
`d − 1` tested against `d` violates it in the thousands — so the condition is not
vacuous. Those checks are not in the repository and are not replayable; that is a
gap, not a result.

## Negative controls

`lambdaT_control_wrong_t` and `lambdaT_control_no_pair` are decided by the kernel
on `C = {00, 11}`. The first is the one that matters: a mistaken `interDist` — one
that counted the wrong intersection — would make it nonzero.
-/

namespace Delsarte.Hamming

open Finset Delsarte

variable {n : ℕ}

/-- The coordinates on which `X` differs from both `Y` and `Z`. This is
`|(X △ Y) ∩ (X △ Z)|` written without ever forming a symmetric difference. -/
def interDist (X Y Z : Word n 2) : ℕ :=
  (univ.filter fun c => X c ≠ Y c ∧ X c ≠ Z c).card

/-- `λ^t_{i,j}(C)`: ordered triples of codewords with the three prescribed
statistics. -/
def lambdaT (C : Code n 2) (i j t : ℕ) : ℕ :=
  ((C ×ˢ C ×ˢ C).filter fun p =>
      hammingDist p.1 p.2.1 = i ∧ hammingDist p.1 p.2.2 = j ∧
        interDist p.1 p.2.1 p.2.2 = t).card

/-- `x^t_{i,j}(C)`: the triple count over `|C|` and the orbit size. These are the
variables of Schrijver's program. -/
def xT (C : Code n 2) (i j t : ℕ) : ℚ :=
  (lambdaT C i j t : ℚ) / (C.card * mult n i j t)

/-- `interDist X Y X = 0`: no coordinate differs from `X` in `X`. -/
@[simp] theorem interDist_self_right (X Y : Word n 2) : interDist X Y X = 0 := by
  simp [interDist]

/-- On the diagonal the orbit size is a binomial. From the cardinal definition:
`powersetCard 0` is `{∅}`, so the intersection condition holds everywhere and what
is counted is `powersetCard i univ`. -/
theorem mult_zero_zero (n i : ℕ) : mult n i 0 0 = n.choose i := by
  classical
  rw [mult, multFinset, multOnFinset, Finset.powersetCard_zero]
  rw [Finset.filter_true_of_mem (by
    rintro ⟨v, w⟩ hp
    simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_singleton] at hp
    rw [hp.2]
    simp)]
  simp [Finset.card_powersetCard]

/-- **The socle.** The `j = 0`, `t = 0` fibre of the triple product counts exactly
the pairs at distance `i`: `|X △ Z| = 0` forces `Z = X`, and then the third
statistic vanishes on its own. -/
theorem lambdaT_diag (C : Code n 2) (i : ℕ) :
    lambdaT C i 0 0 = ((C ×ˢ C).filter fun p => hammingDist p.1 p.2 = i).card := by
  classical
  refine Finset.card_bij' (fun p _ => (p.1, p.2.1)) (fun p _ => (p.1, p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨X, Y, Z⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp.1.1, hp.1.2.1⟩, hp.2.1⟩
  · rintro ⟨X, Y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp.1.1, hp.1.2, hp.1.1⟩, hp.2, by simp, by simp⟩
  · rintro ⟨X, Y, Z⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    have : Z = X := (hammingDist_eq_zero.mp hp.2.2.1).symm
    simp [this]
  · rintro ⟨X, Y⟩ _
    rfl

/-- `x⁰_{i,0}` is the distance distribution divided by the shell size. -/
theorem xT_diag (C : Code n 2) (i : ℕ) :
    xT C i 0 0 = distDist C i / n.choose i := by
  rw [xT, lambdaT_diag, mult_zero_zero, distDist, div_div]

/-- **The last line of issue #44's list.** `|C| = ∑ᵢ C(n,i) · x⁰_{i,0}`. The
binomials cancel against the shell sizes and `sum_distDist` closes it. -/
theorem sum_choose_mul_xT_diag {C : Code n 2} (hC : C.Nonempty) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ) * xT C i 0 0 = C.card := by
  rw [← sum_distDist hC]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  have hne : (n.choose i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi').ne'
  rw [xT_diag C i, mul_div_cancel₀ _ hne]

/-! ## Negative controls

On `C = {00, 11}` the kernel decides the triple counts outright. -/

/-- The diagonal value the socle predicts: two ordered pairs at distance `2`. -/
theorem lambdaT_control_diag : lambdaT (n := 2) {![0, 0], ![1, 1]} 2 0 0 = 2 := by decide

/-- **Negative control.** An `interDist` counting the wrong intersection would make
this nonzero: on this code the two words differ everywhere, so `t = 2`, never `1`. -/
theorem lambdaT_control_wrong_t : lambdaT (n := 2) {![0, 0], ![1, 1]} 2 2 1 = 0 := by decide

/-- **Negative control.** No pair of this code is at distance `1`. -/
theorem lambdaT_control_no_pair : lambdaT (n := 2) {![0, 0], ![1, 1]} 1 0 0 = 0 := by decide

end Delsarte.Hamming
