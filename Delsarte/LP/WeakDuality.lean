/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weak duality for finite linear programs

This file states and proves weak duality for a linear program in standard
inequality form, over an arbitrary ordered commutative ring with finitely many
variables and constraints.

The statement is deliberately self-contained. Mathlib has the conic machinery
(`ProperCone`, `ProperCone.dual`, the hyperplane separation theorems that amount
to Farkas' lemma) but no notion of a linear program and no duality theorem for
one; `Mathlib/Analysis/Convex/Cone/Basic.lean` lists both as open TODOs. Weak
duality, unlike strong duality, needs none of that machinery: no topology, no
completeness, no separation argument. It is a chain of two termwise sum
comparisons.

That elementary character is exactly what makes the certificate scheme work. A
dual feasible point yields a valid upper bound on the primal optimum whether or
not it is optimal, so a certificate reduces to a vector of rationals and
checking it reduces to exact dot products.

## Main definitions

* `Delsarte.LP.PrimalFeasible`: `0 ≤ x` and `A *ᵥ x ≤ b`.
* `Delsarte.LP.DualFeasible`: `0 ≤ y` and `c ≤ y ᵥ* A`.

## Main results

* `Delsarte.LP.weak_duality`: any primal feasible `x` and dual feasible `y`
  satisfy `c ⬝ᵥ x ≤ b ⬝ᵥ y`.
* `Delsarte.LP.le_of_dualFeasible`: the certificate form — a single dual
  feasible `y` bounds *every* primal feasible objective value.
-/

namespace Delsarte.LP

open Matrix

variable {ι κ R : Type*} [Fintype ι] [Fintype κ]
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {A : Matrix ι κ R} {b : ι → R} {c x : κ → R} {y : ι → R}

/-- `x` is feasible for the primal program `max c ⬝ᵥ x` subject to
`A *ᵥ x ≤ b` and `0 ≤ x`. -/
def PrimalFeasible (A : Matrix ι κ R) (b : ι → R) (x : κ → R) : Prop :=
  0 ≤ x ∧ A *ᵥ x ≤ b

/-- `y` is feasible for the dual program `min b ⬝ᵥ y` subject to
`c ≤ y ᵥ* A` and `0 ≤ y`. -/
def DualFeasible (A : Matrix ι κ R) (c : κ → R) (y : ι → R) : Prop :=
  0 ≤ y ∧ c ≤ y ᵥ* A

theorem dotProduct_le_dotProduct_right {u v w : κ → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w :=
  Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (huv i) (hw i)

theorem dotProduct_le_dotProduct_left {u v : ι → R} {w : ι → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    w ⬝ᵥ u ≤ w ⬝ᵥ v :=
  Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (huv i) (hw i)

/-- **Weak duality.** The primal objective at any feasible point is bounded
above by the dual objective at any feasible point. -/
theorem weak_duality (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  obtain ⟨hx0, hxb⟩ := hx
  obtain ⟨hy0, hyc⟩ := hy
  calc c ⬝ᵥ x
      ≤ (y ᵥ* A) ⬝ᵥ x := dotProduct_le_dotProduct_right hyc hx0
    _ = y ⬝ᵥ (A *ᵥ x) := (dotProduct_mulVec y A x).symm
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_left hxb hy0
    _ = b ⬝ᵥ y := dotProduct_comm y b

/-- The certificate form of weak duality: one dual feasible `y` bounds the
objective of every primal feasible point at once. Optimality of `y` is not
required, which is what lets a solver's rounded output serve as a certificate. -/
theorem le_of_dualFeasible (hy : DualFeasible A c y) :
    ∀ x, PrimalFeasible A b x → c ⬝ᵥ x ≤ b ⬝ᵥ y :=
  fun _ hx ↦ weak_duality hx hy

end Delsarte.LP
