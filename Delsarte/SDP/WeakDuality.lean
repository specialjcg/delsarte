/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Weak duality for finite semidefinite programs, in certificate form

The semidefinite analogue of `Delsarte/LP/WeakDuality.lean`. A program has a
linear objective, finitely many *blocks* — affine matrix pencils
`F₀ + ∑ᵤ xᵤ Fᵤ` required to be positive as quadratic forms — and finitely many
affine inequalities.

A certificate is not a dual matrix but a **Gram factorisation** of one:
weights `d_r ≥ 0` and vectors `v_r` per block, multipliers `μ ≥ 0` for the
inequalities, and a bound `B`. It is valid when the objective plus the
certificate's combination of constraints is the constant `B`, *coefficient by
coefficient*. Then on any feasible point every added term is nonnegative, and
the objective is at most `B`.

Two choices make the check cheap and the statement weak in the right way.

* Positivity is asked of `w ⬝ᵥ (M *ᵥ w)` only. Neither symmetry nor
  `Matrix.PosSemidef` enters: a bound needs the quadratic form, nothing else.
  A matrix that is `PosSemidef` satisfies the hypothesis
  (`Matrix.PosSemidef.dotProduct_mulVec_nonneg`), so nothing is lost downstream.
* Validity is a finite list of equalities between elements of `R`, one per
  variable plus one for the constant. Over `ℚ` it is decided by evaluation. No
  trace inequality, no eigenvalue, no square root.

The order on `R` is only partial, as in the linear case: the proof is two
nonnegative sums and one ring identity, and never compares two arbitrary
elements.

## Main definitions

* `Delsarte.SDP.pencil`: the affine matrix `F₀ + ∑ᵤ xᵤ Fᵤ`.
* `Delsarte.SDP.QuadNonneg`: `0 ≤ w ⬝ᵥ (M *ᵥ w)` for every `w`.
* `Delsarte.SDP.Program`, `Delsarte.SDP.Program.Feasible`.
* `Delsarte.SDP.Cert`, `Delsarte.SDP.Cert.Valid`.

## Main results

* `Delsarte.SDP.dotProduct_pencil_mulVec`: the quadratic form of a pencil is
  affine in `x`.
* `Delsarte.SDP.Cert.le_bound`: a valid certificate bounds the objective of
  every feasible point.
* `Delsarte.SDP.toy_le_one`, `Delsarte.SDP.toy_tight`,
  `Delsarte.SDP.not_valid_toyHalf`: a two-by-two example whose bound is
  certified, attained, and cannot be claimed any lower by the same vectors.
-/

namespace Delsarte.SDP

open Matrix Finset

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

section Pencil

variable {n κ : Type*} [Fintype n] [Fintype κ]

/-- The affine matrix pencil `F₀ + ∑ᵤ xᵤ Fᵤ`, entry by entry. -/
def pencil (F₀ : Matrix n n R) (F : κ → Matrix n n R) (x : κ → R) : Matrix n n R :=
  Matrix.of fun i j => F₀ i j + ∑ u, x u * F u i j

/-- Positivity as a quadratic form. -/
def QuadNonneg (M : Matrix n n R) : Prop :=
  ∀ w : n → R, 0 ≤ w ⬝ᵥ (M *ᵥ w)

omit [PartialOrder R] [IsOrderedRing R] in
/-- **The quadratic form of a pencil is affine in the variables.** This is the
identity that turns validity of a certificate into equalities of coefficients. -/
theorem dotProduct_pencil_mulVec (F₀ : Matrix n n R) (F : κ → Matrix n n R)
    (x : κ → R) (w : n → R) :
    w ⬝ᵥ (pencil F₀ F x *ᵥ w) = w ⬝ᵥ (F₀ *ᵥ w) + ∑ u, x u * (w ⬝ᵥ (F u *ᵥ w)) := by
  simp only [pencil, dotProduct, mulVec, of_apply, add_mul, sum_add_distrib, mul_add,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc ∑ i, ∑ j, ∑ u, w i * (x u * F u i j * w j)
      = ∑ i, ∑ u, ∑ j, w i * (x u * F u i j * w j) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ u, ∑ i, ∑ j, w i * (x u * F u i j * w j) := sum_comm
    _ = ∑ u, ∑ i, ∑ j, x u * (w i * (F u i j * w j)) :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end Pencil

/-- A semidefinite program in inequality form, with variables `κ`, blocks `β`
of shapes `ι b`, and affine inequalities `γ`. -/
structure Program (κ β γ : Type*) (ι : β → Type*) (R : Type*) where
  /-- Objective coefficients: maximise `obj ⬝ᵥ x`. -/
  obj : κ → R
  /-- Constant part of each block. -/
  F₀ : ∀ b, Matrix (ι b) (ι b) R
  /-- Coefficient matrix of each variable in each block. -/
  F : ∀ b, κ → Matrix (ι b) (ι b) R
  /-- Linear part of each inequality `a ⬝ᵥ x + a₀ ≥ 0`. -/
  a : γ → κ → R
  /-- Constant part of each inequality. -/
  a₀ : γ → R

variable {κ β γ : Type*} {ι : β → Type*} [Fintype κ] [Fintype β] [Fintype γ]
  [∀ b, Fintype (ι b)]

/-- `x` satisfies every block and every inequality. -/
def Program.Feasible (P : Program κ β γ ι R) (x : κ → R) : Prop :=
  (∀ b, QuadNonneg (pencil (P.F₀ b) (P.F b) x)) ∧ ∀ l, 0 ≤ P.a l ⬝ᵥ x + P.a₀ l

/-- A certificate: per block, weighted Gram vectors; per inequality, a multiplier;
and the claimed bound. -/
structure Cert (P : Program κ β γ ι R) (ρ : β → Type*) where
  /-- Weight of each Gram vector. -/
  d : ∀ b, ρ b → R
  /-- The Gram vectors of each block. -/
  v : ∀ b, ρ b → ι b → R
  /-- Multiplier of each inequality. -/
  μ : γ → R
  /-- The claimed upper bound. -/
  bound : R

variable {ρ : β → Type*} [∀ b, Fintype (ρ b)]

/-- What the certificate spends on the blocks, for the coefficient matrices `M`. -/
def Cert.blockSum {P : Program κ β γ ι R} (C : Cert P ρ) (M : ∀ b, Matrix (ι b) (ι b) R) : R :=
  ∑ b, ∑ r, C.d b r * (C.v b r ⬝ᵥ (M b *ᵥ C.v b r))

/-- Validity: nonnegative weights and multipliers, and the objective plus the
certificate's combination equal to `bound` coefficient by coefficient. -/
structure Cert.Valid {P : Program κ β γ ι R} (C : Cert P ρ) : Prop where
  d_nonneg : ∀ b r, 0 ≤ C.d b r
  μ_nonneg : ∀ l, 0 ≤ C.μ l
  coeff : ∀ u, P.obj u + C.blockSum (fun b => P.F b u) + ∑ l, C.μ l * P.a l u = 0
  const : C.blockSum P.F₀ + ∑ l, C.μ l * P.a₀ l = C.bound

/-- **Weak duality, certificate form.** A valid certificate bounds the objective
of every feasible point. It need not be optimal, which is what lets a rounded
solver output serve. -/
theorem Cert.le_bound {P : Program κ β γ ι R} {C : Cert P ρ} (hC : C.Valid) {x : κ → R}
    (hx : P.Feasible x) : P.obj ⬝ᵥ x ≤ C.bound := by
  obtain ⟨hB, hL⟩ := hx
  -- The spent quantities, each nonnegative on a feasible point.
  have hS : 0 ≤ ∑ b, ∑ r, C.d b r * (C.v b r ⬝ᵥ (pencil (P.F₀ b) (P.F b) x *ᵥ C.v b r)) :=
    sum_nonneg fun b _ => sum_nonneg fun r _ => mul_nonneg (hC.d_nonneg b r) (hB b _)
  have hT : 0 ≤ ∑ l, C.μ l * (P.a l ⬝ᵥ x + P.a₀ l) :=
    sum_nonneg fun l _ => mul_nonneg (hC.μ_nonneg l) (hL l)
  -- Both are affine in `x`, with the coefficients that validity pins down.
  have eS : ∑ b, ∑ r, C.d b r * (C.v b r ⬝ᵥ (pencil (P.F₀ b) (P.F b) x *ᵥ C.v b r))
      = C.blockSum P.F₀ + ∑ u, x u * C.blockSum (fun b => P.F b u) := by
    simp only [Cert.blockSum, dotProduct_pencil_mulVec, mul_add, sum_add_distrib,
      Finset.mul_sum]
    congr 1
    calc ∑ b, ∑ r, ∑ u, C.d b r * (x u * (C.v b r ⬝ᵥ (P.F b u *ᵥ C.v b r)))
        = ∑ b, ∑ u, ∑ r, C.d b r * (x u * (C.v b r ⬝ᵥ (P.F b u *ᵥ C.v b r))) :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ u, ∑ b, ∑ r, C.d b r * (x u * (C.v b r ⬝ᵥ (P.F b u *ᵥ C.v b r))) := sum_comm
      _ = ∑ u, ∑ b, ∑ r, x u * (C.d b r * (C.v b r ⬝ᵥ (P.F b u *ᵥ C.v b r))) :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have eT : ∑ l, C.μ l * (P.a l ⬝ᵥ x + P.a₀ l)
      = ∑ l, C.μ l * P.a₀ l + ∑ u, x u * ∑ l, C.μ l * P.a l u := by
    simp only [dotProduct, mul_add, sum_add_distrib, Finset.mul_sum]
    rw [add_comm]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hobj : P.obj ⬝ᵥ x + ∑ u, x u * C.blockSum (fun b => P.F b u)
      + ∑ u, x u * ∑ l, C.μ l * P.a l u = 0 := by
    simp only [dotProduct, ← sum_add_distrib]
    exact sum_eq_zero fun u _ => by
      rw [show P.obj u * x u + x u * C.blockSum (fun b => P.F b u)
          + x u * ∑ l, C.μ l * P.a l u
          = x u * (P.obj u + C.blockSum (fun b => P.F b u) + ∑ l, C.μ l * P.a l u) by ring,
        hC.coeff u, mul_zero]
  rw [eS] at hS
  rw [eT] at hT
  -- The objective is the bound minus what was spent.
  have key : P.obj ⬝ᵥ x = C.bound
      - ((C.blockSum P.F₀ + ∑ u, x u * C.blockSum (fun b => P.F b u))
        + (∑ l, C.μ l * P.a₀ l + ∑ u, x u * ∑ l, C.μ l * P.a l u)) := by
    rw [← hC.const]
    linear_combination hobj
  rw [key]
  exact sub_le_self _ (add_nonneg hS hT)

/-! ## A two-by-two example, and its negative control

Maximise `x` subject to `[[1, x], [x, 1]]` positive. The Gram vector `(1, -1)`
with weight `1/2` spends `(1/2)(2 - 2x) = 1 - x`, so `x + (1 - x) = 1`: the
bound is `1`. It is attained at `x = 1`, where the form is `(w₀ + w₁)²`. The
same vector cannot certify `1/2`: the constant coefficient is `1`, not `1/2`.
-/

/-- The toy program: one variable, one two-by-two block, no inequality. -/
def toy : Program (Fin 1) (Fin 1) (Fin 0) (fun _ => Fin 2) ℚ where
  obj := ![1]
  F₀ := fun _ => !![1, 0; 0, 1]
  F := fun _ _ => !![0, 1; 1, 0]
  a := Fin.elim0
  a₀ := Fin.elim0

/-- The certificate `(1, -1)` with weight `1/2`, claiming bound `B`. -/
def toyCert (B : ℚ) : Cert toy (fun _ => Fin 1) where
  d := fun _ _ => 1 / 2
  v := fun _ _ => ![1, -1]
  μ := Fin.elim0
  bound := B

theorem valid_toyCert : (toyCert 1).Valid where
  d_nonneg := fun _ _ => by norm_num [toyCert]
  μ_nonneg := fun l => l.elim0
  coeff := fun u => by
    fin_cases u
    simp [toy, toyCert, Cert.blockSum, dotProduct, mulVec, Fin.sum_univ_two]
    norm_num
  const := by
    simp [toy, toyCert, Cert.blockSum, dotProduct, mulVec, Fin.sum_univ_two]
    norm_num

/-- Every feasible `x` of the toy program is at most `1`. -/
theorem toy_le_one {x : Fin 1 → ℚ} (hx : toy.Feasible x) : x 0 ≤ 1 := by
  have := Cert.le_bound valid_toyCert hx
  simpa [toy, toyCert, dotProduct] using this

/-- **Positive control:** the bound is attained. -/
theorem toy_tight : toy.Feasible ![1] := by
  refine ⟨fun b w => ?_, fun l => l.elim0⟩
  have h : w ⬝ᵥ (pencil (toy.F₀ b) (toy.F b) ![1] *ᵥ w) = (w 0 + w 1) ^ 2 := by
    simp [pencil, toy, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  rw [h]
  exact sq_nonneg _

/-- **Negative control:** the same Gram vector does not certify `1/2`. -/
theorem not_valid_toyHalf : ¬ (toyCert (1 / 2)).Valid := by
  intro h
  have := h.const
  simp [toy, toyCert, Cert.blockSum, dotProduct, mulVec, Fin.sum_univ_two] at this

end Delsarte.SDP
