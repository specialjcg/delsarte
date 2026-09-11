/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Fischer inner product on polynomials

Everything here is a statement about coefficients. No sphere, no Gegenbauer, no
geometry: the file exists so that `Delsarte/Sphere/Schoenberg.lean` can read a
Gram matrix off a polynomial identity, and the two properties that make that
possible are proved here once.

## What the product is for

`⟪p, q⟫ := ∑_α α! · p_α · q_α`, with `α! = ∏_i (α_i)!`. Two properties carry the
whole argument, and both are pure coefficient bookkeeping:

* **adjunction** `⟪rSq * p, q⟫ = ⟪p, Δ q⟫`, where `rSq = ∑_i X_i ^ 2` represents
  `‖y‖ ^ 2` and `Δ = ∑_i ∂_i ^ 2`. Multiplying by the radius squared and taking
  the Laplacian are adjoint;
* **reproduction** `⟪p, (∑_i y_i X_i) ^ k⟫ = k! · p y` for `p` homogeneous of
  degree `k`. Evaluation at a point is pairing against a power of a linear form.

Together they say: a harmonic `p` is orthogonal to every multiple of `rSq`, and
what survives of a pairing is one evaluation. That is the whole mechanism by
which `∑_(i,j) G_k ⟪x_i, x_j⟫` becomes a squared norm.

## Why the constant in the adjunction is exactly one

It is tempting to expect a factor `d` or `k`. There is none, and the reason is a
single identity on weights:

`(β + 2 e_i)! = β! · (β_i + 1) · (β_i + 2)`

which is precisely the factor that `∂_i ^ 2` produces on the coefficient of
`β + 2 e_i`. The weight `α!` is *chosen* to make this cancel; any other weight
breaks the adjunction. `fischer_rSq_mul_control` pins this down numerically in
`d = 2`, where a spurious factor `d` would read `4` instead of `2`.

Everything else is built from one lemma, `fischer_X_mul`, which is the same
statement one variable at a time: multiplication by `X i` is adjoint to `∂_i`.

## Why reproduction needs homogeneity

`(∑_i y_i X_i) ^ k` lives entirely in degree `k`, so it cannot see any part of
`p` outside that degree. Without the hypothesis the two sides simply differ, and
`fischer_linForm_pow_not_of_inhomogeneous` exhibits the gap rather than leaving
it to the reader's trust.

The proof does **not** expand the multinomial. It uses Euler's identity
`∑_i X_i ∂_i p = k • p` (which mathlib has) to strip one degree at a time, so the
induction step is `fischer_X_mul` applied `d` times and nothing else.

## Scope

This file knows nothing about `Delsarte`. It imports only mathlib, and its
project-import closure is empty — the binary chain and the certificate machinery
are unaffected by anything here.
-/

namespace Delsarte.Harmonic

open Finset MvPolynomial

variable {d : ℕ}

/-! ## The weight -/

/-- The Fischer weight of a multi-index: `α! = ∏_i (α_i)!`. -/
def fischerWeight (α : Fin d →₀ ℕ) : ℕ := ∏ i, Nat.factorial (α i)

@[simp]
theorem fischerWeight_zero : fischerWeight (0 : Fin d →₀ ℕ) = 1 := by
  simp [fischerWeight]

theorem fischerWeight_pos (α : Fin d →₀ ℕ) : 0 < fischerWeight α :=
  Finset.prod_pos fun i _ => Nat.factorial_pos (α i)

/-- The one identity that makes the whole file work: bumping a multi-index by one
in coordinate `i` multiplies the weight by exactly `α i + 1`, which is exactly the
factor `∂_i` produces. -/
theorem fischerWeight_single_add (i : Fin d) (α : Fin d →₀ ℕ) :
    fischerWeight (Finsupp.single i 1 + α) = fischerWeight α * (α i + 1) := by
  classical
  rw [fischerWeight, fischerWeight, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∀ j ∈ (Finset.univ : Finset (Fin d)).erase i,
      Nat.factorial ((Finsupp.single i 1 + α : Fin d →₀ ℕ) j) = Nat.factorial (α j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hji]
  rw [Finset.prod_congr rfl hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1 (α i), Nat.factorial_succ]
  ring

/-! ## The product -/

/-- The Fischer inner product. The sum runs over the support of the first
argument; `fischer_eq_sum` says any larger index set gives the same value, which
is what makes the form symmetric and bilinear. -/
def fischer (p q : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ α ∈ p.support, (fischerWeight α : ℝ) * coeff α p * coeff α q

theorem fischer_eq_sum {p q : MvPolynomial (Fin d) ℝ} {s : Finset (Fin d →₀ ℕ)}
    (hp : p.support ⊆ s) :
    fischer p q = ∑ α ∈ s, (fischerWeight α : ℝ) * coeff α p * coeff α q := by
  simp only [fischer]
  refine Finset.sum_subset hp fun α _ hα => ?_
  rw [notMem_support_iff.mp hα, mul_zero, zero_mul]

theorem fischer_comm (p q : MvPolynomial (Fin d) ℝ) : fischer p q = fischer q p := by
  classical
  rw [fischer_eq_sum (s := p.support ∪ q.support) Finset.subset_union_left,
    fischer_eq_sum (s := p.support ∪ q.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun α _ => by ring

@[simp]
theorem fischer_zero_left (q : MvPolynomial (Fin d) ℝ) : fischer 0 q = 0 := by
  simp [fischer]

theorem fischer_add_left (p₁ p₂ q : MvPolynomial (Fin d) ℝ) :
    fischer (p₁ + p₂) q = fischer p₁ q + fischer p₂ q := by
  classical
  have hs : (p₁ + p₂).support ⊆ p₁.support ∪ p₂.support := MvPolynomial.support_add
  rw [fischer_eq_sum hs, fischer_eq_sum (q := q) (Finset.subset_union_left (s₂ := p₂.support)),
    fischer_eq_sum (q := q) (Finset.subset_union_right (s₁ := p₁.support)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_add]; ring

theorem fischer_C_mul_left (c : ℝ) (p q : MvPolynomial (Fin d) ℝ) :
    fischer (C c * p) q = c * fischer p q := by
  have hs : (C c * p).support ⊆ p.support := by
    intro α hα
    rw [mem_support_iff, coeff_C_mul] at hα
    exact mem_support_iff.mpr (right_ne_zero_of_mul hα)
  rw [fischer_eq_sum hs, fischer, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_C_mul]; ring

theorem fischer_C_mul_right (c : ℝ) (p q : MvPolynomial (Fin d) ℝ) :
    fischer p (C c * q) = c * fischer p q := by
  rw [fischer_comm, fischer_C_mul_left, fischer_comm]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℝ)
    (q : MvPolynomial (Fin d) ℝ) :
    fischer (∑ i ∈ s, f i) q = ∑ i ∈ s, fischer (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, fischer_add_left, ih, Finset.sum_insert ha]

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℝ)
    (p : MvPolynomial (Fin d) ℝ) :
    fischer p (∑ i ∈ s, f i) = ∑ i ∈ s, fischer p (f i) := by
  rw [fischer_comm, fischer_sum_left]
  exact Finset.sum_congr rfl fun i _ => fischer_comm _ _

theorem fischer_monomial_left (α : Fin d →₀ ℕ) (a : ℝ) (q : MvPolynomial (Fin d) ℝ) :
    fischer (monomial α a) q = (fischerWeight α : ℝ) * a * coeff α q := by
  have hs : (monomial α a : MvPolynomial (Fin d) ℝ).support ⊆ {α} := by
    intro β hβ
    rw [mem_support_iff, coeff_monomial] at hβ
    by_cases h : α = β
    · simp [h]
    · simp [h] at hβ
  rw [fischer_eq_sum hs, Finset.sum_singleton, coeff_monomial, if_pos rfl]

/-! ## Positivity

The only place the real numbers are used as an ordered field. -/

theorem fischer_self_nonneg (p : MvPolynomial (Fin d) ℝ) : 0 ≤ fischer p p := by
  rw [fischer]
  refine Finset.sum_nonneg fun α _ => ?_
  have h : (fischerWeight α : ℝ) * coeff α p * coeff α p
      = (fischerWeight α : ℝ) * (coeff α p) ^ 2 := by ring
  rw [h]
  positivity

theorem fischer_self_eq_zero_iff (p : MvPolynomial (Fin d) ℝ) :
    fischer p p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [MvPolynomial.eq_zero_iff]
    intro α
    by_cases hα : α ∈ p.support
    · have hnn : ∀ β ∈ p.support, 0 ≤ (fischerWeight β : ℝ) * coeff β p * coeff β p := by
        intro β _
        have : (fischerWeight β : ℝ) * coeff β p * coeff β p
            = (fischerWeight β : ℝ) * (coeff β p) ^ 2 := by ring
        rw [this]; positivity
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h α hα
      have hw : (fischerWeight α : ℝ) ≠ 0 := by
        exact_mod_cast (fischerWeight_pos α).ne'
      have h2 : (coeff α p) ^ 2 = 0 := by
        have : (fischerWeight α : ℝ) * (coeff α p) ^ 2 = 0 := by
          rw [← hzero]; ring
        exact (mul_eq_zero.mp this).resolve_left hw
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    · exact notMem_support_iff.mp hα
  · intro h; rw [h]; simp

/-! ## The adjunction -/

/-- Multiplication by `X i` is adjoint to `∂_i`. The whole file rests on this and
on `fischerWeight_single_add`. -/
theorem fischer_X_mul (i : Fin d) (p q : MvPolynomial (Fin d) ℝ) :
    fischer (X i * p) q = fischer p (pderiv i q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α a =>
      have hX : (X i : MvPolynomial (Fin d) ℝ) * monomial α a
          = monomial (Finsupp.single i 1 + α) a := by
        rw [show (X i : MvPolynomial (Fin d) ℝ) = monomial (Finsupp.single i 1) 1 from by
          rw [← MvPolynomial.X_pow_eq_monomial, pow_one], monomial_mul, one_mul]
      rw [hX, fischer_monomial_left, fischer_monomial_left, coeff_pderiv,
        fischerWeight_single_add, add_comm (Finsupp.single i 1) α]
      push_cast
      ring
  | add p₁ p₂ h₁ h₂ => rw [mul_add, fischer_add_left, fischer_add_left, h₁, h₂]

/-- The formal radius squared, representing `‖y‖ ^ 2`. -/
noncomputable def rSq (d : ℕ) : MvPolynomial (Fin d) ℝ := ∑ i, (X i) ^ 2

/-- The Laplacian. -/
noncomputable def mvLaplacian (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, pderiv i (pderiv i p)

@[simp]
theorem mvLaplacian_zero : mvLaplacian (0 : MvPolynomial (Fin d) ℝ) = 0 := by
  simp [mvLaplacian]

/-- **The adjunction.** Multiplying by the radius squared is adjoint to the
Laplacian, with constant exactly `1`. -/
theorem fischer_rSq_mul (p q : MvPolynomial (Fin d) ℝ) :
    fischer (rSq d * p) q = fischer p (mvLaplacian q) := by
  rw [rSq, Finset.sum_mul, fischer_sum_left, mvLaplacian, fischer_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_two, mul_assoc, fischer_X_mul, fischer_X_mul]

/-! ## The linear form and reproduction -/

/-- The linear form `y ↦ ⟪x, y⟫`, as a polynomial in `y` with `x` as parameter. -/
noncomputable def linForm (x : Fin d → ℝ) : MvPolynomial (Fin d) ℝ := ∑ i, C (x i) * X i

theorem eval_linForm (x y : Fin d → ℝ) : eval y (linForm x) = ∑ i, x i * y i := by
  simp [linForm]

theorem linForm_isHomogeneous (x : Fin d → ℝ) : (linForm x).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (x i) i

theorem pderiv_linForm (x : Fin d → ℝ) (i : Fin d) :
    pderiv i (linForm x) = C (x i) := by
  classical
  rw [linForm, map_sum, Finset.sum_eq_single i]
  · rw [pderiv_C_mul, pderiv_X_self, mul_one]
  · intro j _ hj; rw [pderiv_C_mul, pderiv_X_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pderiv_linForm_pow (x : Fin d → ℝ) (i : Fin d) (k : ℕ) :
    pderiv i (linForm x ^ (k + 1)) = C ((k + 1 : ℝ) * x i) * linForm x ^ k := by
  rw [pderiv_pow, pderiv_linForm, Nat.add_sub_cancel, map_mul,
    show ((k + 1 : ℕ) : MvPolynomial (Fin d) ℝ) = C (((k + 1 : ℕ) : ℝ)) from
      (map_natCast (C : ℝ →+* MvPolynomial (Fin d) ℝ) (k + 1)).symm]
  push_cast
  ring

/-- **Reproduction.** Pairing a homogeneous polynomial of degree `k` against the
`k`-th power of a linear form evaluates it, up to `k!`.

The hypothesis is not decoration: see
`fischer_linForm_pow_not_of_inhomogeneous`. -/
theorem fischer_linForm_pow (y : Fin d → ℝ) (k : ℕ) (p : MvPolynomial (Fin d) ℝ)
    (hp : p.IsHomogeneous k) :
    fischer p (linForm y ^ k) = (Nat.factorial k : ℝ) * eval y p := by
  induction k generalizing p with
  | zero =>
      rw [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
      rw [hp, C_apply, fischer_monomial_left]
      simp
  | succ k ih =>
      have hsmul : ((k + 1 : ℕ) : ℝ) * fischer p (linForm y ^ (k + 1))
          = fischer (∑ i, X i * pderiv i p) (linForm y ^ (k + 1)) := by
        rw [hp.sum_X_mul_pderiv, nsmul_eq_mul,
          ← map_natCast (C : ℝ →+* MvPolynomial (Fin d) ℝ) (k + 1), fischer_C_mul_left]
      have hstep : fischer (∑ i, X i * pderiv i p) (linForm y ^ (k + 1))
          = ((k + 1 : ℝ) * (Nat.factorial k : ℝ)) * ∑ i, y i * eval y (pderiv i p) := by
        rw [fischer_sum_left, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hh : (pderiv i p).IsHomogeneous k := by
          simpa using hp.pderiv (i := i)
        rw [fischer_X_mul, pderiv_linForm_pow, fischer_C_mul_right, ih _ hh]
        ring
      have heval : ∑ i, y i * eval y (pderiv i p) = ((k + 1 : ℝ)) * eval y p := by
        have := congrArg (eval y) hp.sum_X_mul_pderiv
        rw [map_sum] at this
        simp only [map_mul, eval_X, nsmul_eq_mul, map_natCast] at this
        rw [this]
        push_cast
        ring
      have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have : ((k + 1 : ℕ) : ℝ) * fischer p (linForm y ^ (k + 1))
          = ((k + 1 : ℕ) : ℝ) * (Nat.factorial (k + 1) : ℝ) * eval y p := by
        rw [hsmul, hstep, heval, Nat.factorial_succ]
        push_cast
        ring
      field_simp at this
      linarith [this]

/-! ### Controls

A weight that never changed an answer, and an adjunction whose constant was never
measured, would both pass every theorem above unnoticed. These four pin them down.
-/

theorem X_sq_eq_monomial :
    (X 0 : MvPolynomial (Fin 1) ℝ) ^ 2 = monomial (Finsupp.single 0 2) 1 := by
  rw [← MvPolynomial.X_pow_eq_monomial]

theorem fischerWeight_single_two : fischerWeight (Finsupp.single (0 : Fin 1) 2) = 2 := by
  simp [fischerWeight]

/-- The weight is not the identity: `⟪X₀², X₀²⟫ = 2`, whereas the naive sum of
products of coefficients is `1`. Were the two equal, the adjunction would be false
and nothing above would notice. -/
theorem fischer_ne_coeff_dot :
    fischer ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2) ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2) = 2 ∧
      ∑ α ∈ ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2).support,
          coeff α ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2)
            * coeff α ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2) = 1 := by
  constructor
  · rw [X_sq_eq_monomial, fischer_monomial_left, coeff_monomial, if_pos rfl,
      fischerWeight_single_two]
    norm_num
  · rw [X_sq_eq_monomial, support_monomial]
    norm_num

/-- The adjunction constant is exactly `1`, measured in `d = 2` where a spurious
factor `d` would read `4`. -/
theorem fischer_rSq_mul_control :
    fischer (rSq 2 * 1) ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2) = 2 ∧
      fischer (1 : MvPolynomial (Fin 2) ℝ) (mvLaplacian ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2))
        = 2 := by
  have h := fischer_rSq_mul (1 : MvPolynomial (Fin 2) ℝ) ((X 0) ^ 2)
  have hleft : fischer (rSq 2 * 1) ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2) = 2 := by
    rw [mul_one, rSq, Finset.sum_fin_eq_sum_range]
    norm_num [Finset.sum_range_succ, fischer_add_left]
    rw [show (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ 2 = monomial (Finsupp.single 0 2) 1 from by
        rw [← MvPolynomial.X_pow_eq_monomial],
      show (X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ 2 = monomial (Finsupp.single 1 2) 1 from by
        rw [← MvPolynomial.X_pow_eq_monomial],
      fischer_monomial_left, fischer_monomial_left, coeff_monomial,
      coeff_monomial, if_pos rfl, if_neg (by
        simp [Finsupp.single_eq_single_iff])]
    simp [fischerWeight, Finsupp.single_apply]
  exact ⟨hleft, by rw [← h]; exact hleft⟩

/-- Reproduction genuinely needs homogeneity: at `d = 1`, `p = 1 + X₀` and `k = 1`
the two sides are `1` and `2`. -/
theorem fischer_linForm_pow_not_of_inhomogeneous :
    fischer (1 + X 0 : MvPolynomial (Fin 1) ℝ) (linForm (fun _ => (1 : ℝ)) ^ 1) = 1 ∧
      (Nat.factorial 1 : ℝ) * eval (fun _ => (1 : ℝ)) (1 + X 0 : MvPolynomial (Fin 1) ℝ) = 2 := by
  have hL : linForm (fun _ => (1 : ℝ)) = (X 0 : MvPolynomial (Fin 1) ℝ) := by
    simp [linForm]
  constructor
  · rw [hL, pow_one, fischer_add_left,
      show (1 : MvPolynomial (Fin 1) ℝ) = monomial 0 1 from by rw [← C_apply, map_one],
      show (X 0 : MvPolynomial (Fin 1) ℝ) = monomial (Finsupp.single 0 1) 1 from by
        rw [← MvPolynomial.X_pow_eq_monomial, pow_one],
      fischer_monomial_left, fischer_monomial_left, coeff_monomial, coeff_monomial,
      if_pos rfl, if_neg (by simp [Finsupp.single_eq_zero])]
    simp [fischerWeight]
  · simp
    norm_num

end Delsarte.Harmonic
