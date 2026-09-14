/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Shortening: `A (n + 1) q d ≤ q * A n q d`

A purely combinatorial bound, independent of the linear program. Fix the last
coordinate: the code splits into `q` fibres, and dropping that coordinate maps
each fibre injectively onto a code of length `n` with the same minimum distance,
because two words sharing their last letter differ only in the first `n`.

## Why this is worth having

The linear program and this recursion are incomparable. Neither dominates: on
the binary table the program is usually far stronger, but it is a relaxation and
its optimum need not be an integer, so it can miss by a unit what an integral
argument catches. Composing the two — take the program's bound at length `n`,
double it, keep whichever is smaller at length `n + 1` — is strictly better than
either alone on `A(19,4)`, `A(20,4)`, `A(24,4)`, `A(27,4)` and `A(28,4)`.

The gain is one or two codewords. It is kept because it is *earned*: the bound
that comes out is composed of two certified steps and owes nothing to a solver's
floating point.

No claim is made that this reaches the best bounds in the literature. It does
not; those rest on further arguments not formalised here.
-/

namespace Delsarte

open Finset

variable {n q d : ℕ}

/-- Drop the last coordinate of a word. -/
def res (x : Word (n + 1) q) : Word n q := fun i => x i.castSucc

/-- Hamming distance splits off the last coordinate. -/
theorem hammingDist_eq_res_add (x y : Word (n + 1) q) :
    hammingDist x y
      = hammingDist (res x) (res y) + (if x (Fin.last n) ≠ y (Fin.last n) then 1 else 0) := by
  have hl : hammingDist x y = ∑ i : Fin (n + 1), if x i ≠ y i then 1 else 0 :=
    Finset.card_filter _ _
  have hr : hammingDist (res x) (res y)
      = ∑ i : Fin n, if x i.castSucc ≠ y i.castSucc then 1 else 0 :=
    Finset.card_filter _ _
  rw [hl, hr]
  exact Fin.sum_univ_castSucc (f := fun i => if x i ≠ y i then 1 else 0)

/-- Shortening preserves distance between words that agree on the last letter. -/
theorem hammingDist_res (x y : Word (n + 1) q) (h : x (Fin.last n) = y (Fin.last n)) :
    hammingDist (res x) (res y) = hammingDist x y := by
  rw [hammingDist_eq_res_add x y, if_neg (by simp [h])]
  omega

/-- Shortening is injective on a fibre of the last coordinate. -/
theorem res_inj_of_last {x y : Word (n + 1) q} (hr : res x = res y)
    (hl : x (Fin.last n) = y (Fin.last n)) : x = y := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · exact hl
  · intro j
    exact congrFun hr j

/-- The image of a fibre under shortening still has minimum distance `d`. -/
theorem minDistAtLeast_image_res {C : Code (n + 1) q} (hC : MinDistAtLeast d C) (v : Fin q) :
    MinDistAtLeast d ((C.filter fun x => x (Fin.last n) = v).image res) := by
  classical
  intro x' hx' y' hy' hne
  simp only [Finset.mem_image, Finset.mem_filter] at hx' hy'
  obtain ⟨x, ⟨hxC, hxv⟩, rfl⟩ := hx'
  obtain ⟨y, ⟨hyC, hyv⟩, rfl⟩ := hy'
  have hl : x (Fin.last n) = y (Fin.last n) := by rw [hxv, hyv]
  have hxy : x ≠ y := fun h => hne (by rw [h])
  rw [hammingDist_res x y hl]
  exact hC x hxC y hyC hxy

/-- **Shortening bound.** Fixing one coordinate splits a code into `q` pieces, each
of which is a code of length `n` with the same minimum distance. -/
theorem A_succ_le (n q d : ℕ) : A (n + 1) q d ≤ q * A n q d := by
  classical
  obtain ⟨C, hC, hcard⟩ := exists_code_card_eq_A (n + 1) q d
  rw [← hcard]
  have hsplit : C.card = ∑ v : Fin q, (C.filter fun x => x (Fin.last n) = v).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_univ (x (Fin.last n))
  rw [hsplit]
  calc ∑ v : Fin q, (C.filter fun x => x (Fin.last n) = v).card
      ≤ ∑ _v : Fin q, A n q d := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hinj : Set.InjOn (res (n := n) (q := q))
            ↑(C.filter fun x => x (Fin.last n) = v) := by
          intro x hx y hy h
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
          exact res_inj_of_last h (by rw [hx.2, hy.2])
        rw [← Finset.card_image_of_injOn hinj]
        exact card_le_A (minDistAtLeast_image_res hC v)
    _ = q * A n q d := by simp [Finset.sum_const, Finset.card_univ]

end Delsarte
