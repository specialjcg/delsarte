/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Defs

/-!
# The quadratic form behind Schrijver's blocks

Issue #45. `Delsarte/Hamming/THEOREM1.md` is the argument on paper; this file is
step 1 of its §5 and the positivity half of step 2 — the part that never mentions
a block.

The matrix of (19) is a sum of rank-one matrices `χ_z χ_zᵀ`, where `χ_z` is the
0/1 vector `v ↦ [z + v ∈ C]`. Its quadratic form is therefore a sum of squares,
which is the shape `Delsarte.SDP.Sparse.Data.Feasible` asks for — that predicate
states positivity as a quadratic form and never mentions a spectrum.

The sum over `z` runs over an arbitrary `S`, and no proof below uses anything
about it. That is deliberate: `S = C` gives the first family of (19) and the
complement gives the second, so both are one lemma.

## What this file does not do

It does not prove Theorem 1. §5 lists four steps — these two, the Gram identity
(proved in `Delsarte/Hamming/Terwilliger.lean`), and the bridge to the encoded
program.

Three things are missing, not one. The bridge. The other half of §2: that `M̃` is
`Sₙ`-invariant, hence equal to `Σ x^t_{i,j} M^t_{i,j}`, which is what makes the
`x^t_{i,j}` the program's variables at all — nothing below mentions an orbit. And
the assembly of §3, which builds the vectors `u_i` and identifies `u_iᵀ M̃ u_j`
with a block entry; §5 does not list it as a step, but it is not contained in any
of the four either. So `A_19_6_le_of_relaxation` still carries its hypotheses, and
will until all three are done. Since `Delsarte/Certificate/Relaxation.lean` those
hypotheses are three separate ones -- `hblocks` for #45, `hrows` for #44, `henc`
for the encoding -- so what is proved here can be read off the statement rather
than hidden inside one `Feasible`. Nothing below discharges any of them.

## Characteristic two

`Word n 2` is `Fin n → Fin 2`, and `Mathlib.Data.ZMod.Defs` is what gives `Fin 2`
its additive group, hence `Word n 2` its `Pi.addCommGroup`. That addition is
definitionally `Fin.add`, so translation still computes and pointwise facts about
`Fin 2` remain `decide`-able. Nothing analytic is imported: the closure of
`ZMod.Defs` contains no `Mathlib.Analysis` and no `Mathlib.Topology` module.
-/

namespace Delsarte.Hamming

open Finset Delsarte

variable {n : ℕ}

/-! ## Translation -/

/-- Characteristic two on the alphabet. Stated for all `x` at once so that
`decide` never meets a free variable. -/
theorem fin2_add_self : ∀ x : Fin 2, x + x = 0 := by decide

/-- Characteristic two on words, pointwise from the alphabet. -/
theorem word_add_self (v : Word n 2) : v + v = 0 :=
  funext fun j => fin2_add_self (v j)

/-- Translation by `z` is an involution. -/
theorem translate_involutive (z : Word n 2) :
    Function.Involutive fun v : Word n 2 => z + v := by
  intro v
  change z + (z + v) = v
  rw [← add_assoc, word_add_self, zero_add]

/-- Translation by `z` is a bijection of the ambient space. This is all §1 and §2
ask of the group structure. -/
theorem translate_bijective (z : Word n 2) :
    Function.Bijective fun v : Word n 2 => z + v :=
  (translate_involutive z).bijective

/-! ## The rank-one decomposition -/

/-- The 0/1 vector `χ_z` of §1: it sees `v` exactly when the translate `z + v`
is a codeword. -/
def indic (C : Code n 2) (z v : Word n 2) : ℚ :=
  if z + v ∈ C then 1 else 0

/-- The unnormalised matrix of §1, summed over an arbitrary set `S` of
translations. `S = C` gives the first family of (19), the complement the second;
no proof below looks at `S`. -/
def gramMat (S C : Code n 2) (v w : Word n 2) : ℚ :=
  ∑ z ∈ S, indic C z v * indic C z w

/-- **Step 1.** The quadratic form of `gramMat` is a sum of squares. This is the
whole content: positivity is then one line. -/
theorem quadForm_eq_sum_sq (S C : Code n 2) (a : Word n 2 → ℚ) :
    ∑ v, ∑ w, a v * a w * gramMat S C v w
      = ∑ z ∈ S, (∑ v, indic C z v * a v) ^ 2 := by
  calc ∑ v, ∑ w, a v * a w * gramMat S C v w
      = ∑ v, ∑ w, ∑ z ∈ S, indic C z v * a v * (indic C z w * a w) := by
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
        rw [gramMat, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ v, ∑ z ∈ S, ∑ w, indic C z v * a v * (indic C z w * a w) :=
        Finset.sum_congr rfl fun v _ => Finset.sum_comm
    _ = ∑ z ∈ S, ∑ v, ∑ w, indic C z v * a v * (indic C z w * a w) :=
        Finset.sum_comm
    _ = ∑ z ∈ S, (∑ v, indic C z v * a v) ^ 2 :=
        Finset.sum_congr rfl fun z _ => by rw [sq, Finset.sum_mul_sum]

/-- **Step 1, as used.** A sum of `χχᵀ` over any index set is positive
semidefinite. No structure of the code is used. -/
theorem quadForm_nonneg (S C : Code n 2) (a : Word n 2 → ℚ) :
    0 ≤ ∑ v, ∑ w, a v * a w * gramMat S C v w := by
  rw [quadForm_eq_sum_sq]
  exact Finset.sum_nonneg fun z _ => sq_nonneg _

/-! ## Averaging -/

/-- Relabelling the ambient space by a bijection carries the form at `a` to the
form at `a ∘ e`. Applied to a coordinate permutation this is the statement that
`P_σ` is orthogonal, which is all the positivity half of §2 uses about `Sₙ`. The
other half, the orbit decomposition, needs far more and is not here. -/
theorem quadForm_comp (S C : Code n 2) (a : Word n 2 → ℚ) (e : Word n 2 ≃ Word n 2) :
    ∑ v, ∑ w, a (e v) * a (e w) * gramMat S C (e v) (e w)
      = ∑ v, ∑ w, a v * a w * gramMat S C v w := by
  conv_rhs => rw [← Equiv.sum_comp e fun v => ∑ w, a v * a w * gramMat S C v w]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_rhs => rw [← Equiv.sum_comp e fun w => a (e v) * a w * gramMat S C (e v) w]

/-- **Step 2, positivity half.** Any nonnegative combination of these forms is
nonnegative. The
average over `Sₙ` of §2 is the case where `T` is the group, `c` is `1 / n!` and
`b σ` is `a ∘ P_σ`; the proof needs no group theory, only that the weights are
nonnegative. -/
theorem sum_smul_quadForm_nonneg {ι : Type*} (T : Finset ι) (c : ι → ℚ)
    (hc : ∀ i ∈ T, 0 ≤ c i) (S C : Code n 2) (b : ι → Word n 2 → ℚ) :
    0 ≤ ∑ i ∈ T, c i * ∑ v, ∑ w, b i v * b i w * gramMat S C v w :=
  Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (quadForm_nonneg S C (b i))

end Delsarte.Hamming
