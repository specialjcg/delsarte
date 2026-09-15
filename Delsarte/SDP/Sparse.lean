/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sparse semidefinite certificates, checked by the kernel

`Delsarte/SDP/WeakDuality.lean` states weak duality over `Finset` sums and
matrices. That is the right statement and the wrong thing to evaluate: the
Schrijver program for `A(19,6)` has 15 010 nonzero block coefficients, and its
certificate has denominators of two hundred bits. This file is the evaluable
counterpart, with the same argument.

## Data

Everything is an integer list, grouped the way the check reads it.

* Variable `u` carries a scale `m u`; every coefficient attached to `u` is an
  integer to be divided by `m u`. For Schrijver's program `m u` is the multinomial
  of the orbit and the coefficients are the integers `β`.
* Blocks: a constant part per block, entries `(p, q, c)`; and per variable,
  entries `(b, p, q, c)` meaning `c / m u` at position `(p, q)` of block `b`.
* Inequalities: a constant per row; per variable, entries `(l, a)` meaning
  `a / m u` in row `l`.

## Certificate

Per block, Gram vectors with integer entries over a denominator `V` and weights
in `ℕ` over a denominator `W`; per row, a multiplier in `ℕ` over `T = W V²`.
Weights and multipliers are natural numbers, so their signs cost nothing.

## Check

For each variable `u`, multiplied through by `m u · T`:

`T · obj u + ∑ c · G(b, p, q) + ∑ μ l · a = 0`,
`G(b, p, q) = ∑ weight · v p · v q` over the Gram vectors of block `b`.

The bound is `bnum / T`, `bnum` being the same contraction on the constant parts.
Nothing about the scales is checked: the argument never divides by them.

## Main results

* `Delsarte.SDP.Sparse.Data.objForm_le`: a certificate that checks bounds the
  objective of every feasible point by `bnum / T`.
* `Delsarte.SDP.Sparse.toy_le_one`, `Delsarte.SDP.Sparse.not_check_toyBad`: the
  two-by-two example of `WeakDuality.lean` in this encoding, accepted with its
  true bound, rejected with a doubled weight.
-/

namespace Delsarte.SDP.Sparse

/-! ## List lemmas -/

theorem cast_sum_map {α : Type*} (L : List α) (f : α → ℤ) :
    ((L.map f).sum : ℚ) = (L.map fun a => (f a : ℚ)).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]

theorem sum_map_swap {α β : Type*} (L₁ : List α) (L₂ : List β) (f : α → β → ℚ) :
    (L₁.map fun a => (L₂.map fun b => f a b).sum).sum
      = (L₂.map fun b => (L₁.map fun a => f a b).sum).sum := by
  induction L₁ with
  | nil => simp
  | cons a t ih => simp [ih, List.sum_map_add]

theorem sum_range_ite (f : ℕ → ℚ) (k : ℕ) : ∀ N : ℕ,
    ((List.range N).map fun b => if k = b then f b else 0).sum = if k < N then f k else 0
  | 0 => by simp
  | N + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, sum_range_ite f k N]
      by_cases h : k < N
      · simp [h, show k ≠ N by omega, show k < N + 1 by omega]
      · by_cases h' : k = N
        · subst h'; simp
        · simp [h, h', show ¬ k < N + 1 by omega]

theorem sum_map_congr {α : Type*} {L : List α} {f g : α → ℚ} (h : ∀ a ∈ L, f a = g a) :
    (L.map f).sum = (L.map g).sum := by
  rw [List.map_congr_left h]

/-! ## Data and semantics -/

/-- A sparse program with integer data, grouped by variable. -/
structure Data where
  /-- Scale of each variable; its coefficients are divided by it. -/
  scale : List ℕ
  /-- Objective numerators. -/
  obj : List ℤ
  /-- Constant part of each block: `(p, q, c)`. -/
  base : List (List (ℕ × ℕ × ℤ))
  /-- Per variable, block entries `(b, p, q, c)`. -/
  byVar : List (List (ℕ × ℕ × ℕ × ℤ))
  /-- Constant of each inequality. -/
  rowBase : List ℤ
  /-- Per variable, inequality entries `(l, a)`. -/
  rowByVar : List (List (ℕ × ℤ))

namespace Data

variable (D : Data)

/-- Number of variables. -/
def nv : ℕ := D.scale.length

/-- The scale of variable `u`, in `ℚ`. -/
def m (u : ℕ) : ℚ := (D.scale.getD u 1 : ℚ)

/-- Quadratic form of a constant entry list. -/
def qf (L : List (ℕ × ℕ × ℤ)) (w : ℕ → ℚ) : ℚ :=
  (L.map fun e => (e.2.2 : ℚ) * (w e.1 * w e.2.1)).sum

/-- Quadratic form of the entries of one variable that fall in block `b`. -/
def qfAt (L : List (ℕ × ℕ × ℕ × ℤ)) (b : ℕ) (w : ℕ → ℚ) : ℚ :=
  (L.map fun e => if e.1 = b then (e.2.2.2 : ℚ) * (w e.2.1 * w e.2.2.1) else 0).sum

/-- The quadratic form of block `b` at the point `z`, evaluated at `w`. -/
def blockForm (b : ℕ) (z w : ℕ → ℚ) : ℚ :=
  qf (D.base.getD b []) w
    + ((List.range D.nv).map fun u => z u / D.m u * qfAt (D.byVar.getD u []) b w).sum

/-- The coefficient of one variable in row `l`. -/
def rowAt (L : List (ℕ × ℤ)) (l : ℕ) : ℚ :=
  (L.map fun e => if e.1 = l then (e.2 : ℚ) else 0).sum

/-- The left side of inequality `l` at the point `z`. -/
def rowForm (l : ℕ) (z : ℕ → ℚ) : ℚ :=
  (D.rowBase.getD l 0 : ℚ)
    + ((List.range D.nv).map fun u => z u / D.m u * rowAt (D.rowByVar.getD u []) l).sum

/-- The objective at `z`. -/
def objForm (z : ℕ → ℚ) : ℚ :=
  ((List.range D.nv).map fun u => z u / D.m u * (D.obj.getD u 0 : ℚ)).sum

/-- Every block positive, every inequality satisfied. -/
def Feasible (z : ℕ → ℚ) : Prop :=
  (∀ b w, 0 ≤ D.blockForm b z w) ∧ ∀ l, 0 ≤ D.rowForm l z

end Data

/-! ## Certificate and check -/

/-- A certificate: Gram vectors per block, multipliers per row. -/
structure Cert where
  /-- Denominator of the vector entries. -/
  V : ℕ
  /-- Denominator of the weights. -/
  W : ℕ
  /-- Per block, `(weight numerator, vector numerators)`. -/
  grams : List (List (ℕ × List ℤ))
  /-- Multiplier numerators, over `W * V ^ 2`. -/
  mu : List ℕ

namespace Cert

variable (C : Cert)

/-- The common denominator `W V²`. -/
def T : ℕ := C.W * C.V ^ 2

/-- A Gram vector as a function, entries divided by `V`. -/
def vec (g : ℕ × List ℤ) (p : ℕ) : ℚ := (g.2.getD p 0 : ℚ) / C.V

/-- Numerator of the Gram matrix of block `b` at `(p, q)`. -/
def gramNum (b p q : ℕ) : ℤ :=
  ((C.grams.getD b []).map fun g => (g.1 : ℤ) * (g.2.getD p 0 * g.2.getD q 0)).sum

end Cert

namespace Data

variable (D : Data) (C : Cert)

/-- The integer coefficient of variable `u`, multiplied by `m u · T`. -/
def coeff (u : ℕ) : ℤ :=
  (C.T : ℤ) * D.obj.getD u 0
    + ((D.byVar.getD u []).map fun e => e.2.2.2 * C.gramNum e.1 e.2.1 e.2.2.1).sum
    + ((D.rowByVar.getD u []).map fun e => (C.mu.getD e.1 0 : ℤ) * e.2).sum

/-- The bound's numerator, over `T`. -/
def bnum : ℤ :=
  ((List.range C.grams.length).map fun b =>
      ((D.base.getD b []).map fun e => e.2.2 * C.gramNum b e.1 e.2.1).sum).sum
    + ((List.range C.mu.length).map fun l => (C.mu.getD l 0 : ℤ) * D.rowBase.getD l 0).sum

/-- The check the kernel runs. -/
def check : Bool :=
  0 < C.V && 0 < C.W && (List.range D.nv).all fun u => D.coeff C u == 0

end Data

/-! ## Soundness -/

namespace Data

variable {D : Data} {C : Cert}

theorem gramNum_eq_zero {b : ℕ} (hb : C.grams.length ≤ b) (p q : ℕ) : C.gramNum b p q = 0 := by
  rw [Cert.gramNum, List.getD_eq_default _ _ hb]
  simp

theorem gramNum_cast (b p q : ℕ) :
    (C.gramNum b p q : ℚ) = ((C.grams.getD b []).map fun g =>
      (g.1 : ℚ) * ((g.2.getD p 0 : ℚ) * g.2.getD q 0)).sum := by
  simp [Cert.gramNum, cast_sum_map]

/-- One weighted Gram vector against one constant entry list, scaled by `T`. -/
theorem T_mul_qf (hV : 0 < C.V) (hW : 0 < C.W) (g : ℕ × List ℤ) (L : List (ℕ × ℕ × ℤ)) :
    (C.T : ℚ) * ((g.1 : ℚ) / C.W * Data.qf L (C.vec g))
      = (L.map fun e => (e.2.2 : ℚ) * ((g.1 : ℚ) * ((g.2.getD e.1 0 : ℚ)
          * g.2.getD e.2.1 0))).sum := by
  have hV' : (C.V : ℚ) ≠ 0 := by exact_mod_cast hV.ne'
  have hW' : (C.W : ℚ) ≠ 0 := by exact_mod_cast hW.ne'
  simp only [Data.qf, ← List.sum_map_mul_left]
  refine sum_map_congr fun e _ => ?_
  simp only [Cert.T, Cert.vec]
  push_cast
  field_simp

/-- The same, for the entries of one variable in block `b`. -/
theorem T_mul_qfAt (hV : 0 < C.V) (hW : 0 < C.W) (g : ℕ × List ℤ)
    (L : List (ℕ × ℕ × ℕ × ℤ)) (b : ℕ) :
    (C.T : ℚ) * ((g.1 : ℚ) / C.W * Data.qfAt L b (C.vec g))
      = (L.map fun e => if e.1 = b then (e.2.2.2 : ℚ) * ((g.1 : ℚ)
          * ((g.2.getD e.2.1 0 : ℚ) * g.2.getD e.2.2.1 0)) else 0).sum := by
  have hV' : (C.V : ℚ) ≠ 0 := by exact_mod_cast hV.ne'
  have hW' : (C.W : ℚ) ≠ 0 := by exact_mod_cast hW.ne'
  simp only [Data.qfAt, ← List.sum_map_mul_left]
  refine sum_map_congr fun e _ => ?_
  by_cases h : e.1 = b
  · simp only [h, if_true, Cert.T, Cert.vec]
    push_cast
    field_simp
  · simp [h]

/-- All Gram vectors of block `b` against a constant entry list. -/
theorem T_mul_gram_qf (hV : 0 < C.V) (hW : 0 < C.W) (b : ℕ) (L : List (ℕ × ℕ × ℤ)) :
    ((C.grams.getD b []).map fun g => (C.T : ℚ) * ((g.1 : ℚ) / C.W * Data.qf L (C.vec g))).sum
      = (L.map fun e => (e.2.2 : ℚ) * C.gramNum b e.1 e.2.1).sum := by
  rw [sum_map_congr fun g _ => T_mul_qf hV hW g L, sum_map_swap]
  refine sum_map_congr fun e _ => ?_
  rw [List.sum_map_mul_left, gramNum_cast]

/-- All Gram vectors of block `b` against the entries of one variable. -/
theorem T_mul_gram_qfAt (hV : 0 < C.V) (hW : 0 < C.W) (b : ℕ) (L : List (ℕ × ℕ × ℕ × ℤ)) :
    ((C.grams.getD b []).map fun g =>
        (C.T : ℚ) * ((g.1 : ℚ) / C.W * Data.qfAt L b (C.vec g))).sum
      = (L.map fun e => if e.1 = b then (e.2.2.2 : ℚ) * C.gramNum b e.2.1 e.2.2.1
          else 0).sum := by
  rw [sum_map_congr fun g _ => T_mul_qfAt hV hW g L b, sum_map_swap]
  refine sum_map_congr fun e _ => ?_
  by_cases h : e.1 = b
  · simp only [h, if_true]
    rw [List.sum_map_mul_left, gramNum_cast]
  · simp [h]

/-- What the Gram vectors spend on the blocks, scaled by `T`. -/
theorem T_mul_spent (hV : 0 < C.V) (hW : 0 < C.W) (z : ℕ → ℚ) :
    (C.T : ℚ) * ((List.range C.grams.length).map fun b =>
        ((C.grams.getD b []).map fun g => (g.1 : ℚ) / C.W * D.blockForm b z (C.vec g)).sum).sum
      = ((List.range C.grams.length).map fun b =>
          ((D.base.getD b []).map fun e => (e.2.2 : ℚ) * C.gramNum b e.1 e.2.1).sum).sum
        + ((List.range D.nv).map fun u => z u / D.m u *
          ((D.byVar.getD u []).map fun e =>
            (e.2.2.2 : ℚ) * C.gramNum e.1 e.2.1 e.2.2.1).sum).sum := by
  have h1 : ∀ b, (C.T : ℚ) * ((C.grams.getD b []).map fun g =>
      (g.1 : ℚ) / C.W * D.blockForm b z (C.vec g)).sum
      = ((D.base.getD b []).map fun e => (e.2.2 : ℚ) * C.gramNum b e.1 e.2.1).sum
        + ((List.range D.nv).map fun u => z u / D.m u * ((D.byVar.getD u []).map fun e =>
            if e.1 = b then (e.2.2.2 : ℚ) * C.gramNum b e.2.1 e.2.2.1 else 0).sum).sum := by
    intro b
    have hg : ∀ g ∈ C.grams.getD b [], (C.T : ℚ) * ((g.1 : ℚ) / C.W * D.blockForm b z (C.vec g))
        = (C.T : ℚ) * ((g.1 : ℚ) / C.W * Data.qf (D.base.getD b []) (C.vec g))
          + ((List.range D.nv).map fun u => z u / D.m u *
              ((C.T : ℚ) * ((g.1 : ℚ) / C.W * Data.qfAt (D.byVar.getD u []) b (C.vec g)))).sum := by
      intro g _
      simp only [Data.blockForm, mul_add, ← List.sum_map_mul_left]
      congr 1
      exact sum_map_congr fun u _ => by ring
    rw [← List.sum_map_mul_left, sum_map_congr hg, List.sum_map_add, T_mul_gram_qf hV hW,
      sum_map_swap]
    congr 1
    refine sum_map_congr fun u _ => ?_
    rw [List.sum_map_mul_left, T_mul_gram_qfAt hV hW]
  rw [← List.sum_map_mul_left, sum_map_congr fun b _ => h1 b, List.sum_map_add, sum_map_swap]
  congr 1
  refine sum_map_congr fun u _ => ?_
  rw [List.sum_map_mul_left, sum_map_swap]
  congr 1
  refine sum_map_congr fun e _ => ?_
  rw [sum_range_ite (fun b => (e.2.2.2 : ℚ) * C.gramNum b e.2.1 e.2.2.1) e.1]
  split_ifs with h
  · rfl
  · rw [gramNum_eq_zero (not_lt.mp h)]; simp

/-- What the multipliers spend on the inequalities, scaled by `T`. -/
theorem T_mul_rows (hV : 0 < C.V) (hW : 0 < C.W) (z : ℕ → ℚ) :
    (C.T : ℚ) * ((List.range C.mu.length).map fun l =>
        (C.mu.getD l 0 : ℚ) / C.T * D.rowForm l z).sum
      = ((List.range C.mu.length).map fun l =>
          (C.mu.getD l 0 : ℚ) * (D.rowBase.getD l 0 : ℚ)).sum
        + ((List.range D.nv).map fun u => z u / D.m u *
          ((D.rowByVar.getD u []).map fun e => (C.mu.getD e.1 0 : ℚ) * e.2).sum).sum := by
  have hT : (C.T : ℚ) ≠ 0 := by
    simp only [Cert.T]; push_cast; positivity
  have h1 : ∀ l, (C.T : ℚ) * ((C.mu.getD l 0 : ℚ) / C.T * D.rowForm l z)
      = (C.mu.getD l 0 : ℚ) * (D.rowBase.getD l 0 : ℚ)
        + ((List.range D.nv).map fun u => z u / D.m u *
            ((C.mu.getD l 0 : ℚ) * rowAt (D.rowByVar.getD u []) l)).sum := by
    intro l
    have hc : (C.T : ℚ) * ((C.mu.getD l 0 : ℚ) / C.T) = C.mu.getD l 0 := by field_simp
    rw [← mul_assoc, hc, Data.rowForm, mul_add, ← List.sum_map_mul_left]
    congr 1
    exact sum_map_congr fun u _ => by ring
  rw [← List.sum_map_mul_left, sum_map_congr fun l _ => h1 l, List.sum_map_add, sum_map_swap]
  congr 1
  refine sum_map_congr fun u _ => ?_
  rw [List.sum_map_mul_left]
  congr 1
  simp only [Data.rowAt, ← List.sum_map_mul_left, mul_ite, mul_zero]
  rw [sum_map_swap]
  refine sum_map_congr fun e _ => ?_
  rw [sum_range_ite (fun l => (C.mu.getD l 0 : ℚ) * e.2) e.1]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (not_lt.mp h)]; simp

theorem T_mul_obj (z : ℕ → ℚ) :
    (C.T : ℚ) * D.objForm z
      = ((List.range D.nv).map fun u => z u / D.m u * ((C.T : ℚ) * D.obj.getD u 0)).sum := by
  rw [Data.objForm, ← List.sum_map_mul_left]
  exact sum_map_congr fun u _ => by ring

/-- **Soundness.** A certificate that checks bounds the objective of every
feasible point by `bnum / T`. -/
theorem objForm_le (hc : D.check C = true) {z : ℕ → ℚ} (hz : D.Feasible z) :
    D.objForm z ≤ (D.bnum C : ℚ) / C.T := by
  simp only [Data.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hc
  obtain ⟨⟨hV, hW⟩, hcoef⟩ := hc
  obtain ⟨hB, hL⟩ := hz
  have hTpos : (0 : ℚ) < C.T := by
    simp only [Cert.T]; push_cast; positivity
  set S := ((List.range C.grams.length).map fun b =>
    ((C.grams.getD b []).map fun g => (g.1 : ℚ) / C.W * D.blockForm b z (C.vec g)).sum).sum
    with hSdef
  set R := ((List.range C.mu.length).map fun l =>
    (C.mu.getD l 0 : ℚ) / C.T * D.rowForm l z).sum with hRdef
  have hS : 0 ≤ S := by
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    refine List.sum_nonneg fun y hy => ?_
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hy
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (hB b _)
  have hR : 0 ≤ R := by
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (div_nonneg (by positivity) hTpos.le) (hL l)
  have hzero : ((List.range D.nv).map fun u => z u / D.m u *
      ((C.T : ℚ) * D.obj.getD u 0
        + ((D.byVar.getD u []).map fun e => (e.2.2.2 : ℚ) * C.gramNum e.1 e.2.1 e.2.2.1).sum
        + ((D.rowByVar.getD u []).map fun e => (C.mu.getD e.1 0 : ℚ) * e.2).sum)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    have h := congrArg (fun k : ℤ => (k : ℚ)) (hcoef u hu)
    simp only [Data.coeff, Int.cast_add, Int.cast_mul, Int.cast_natCast, cast_sum_map,
      Int.cast_zero] at h
    rw [h, mul_zero]
  have hb : (D.bnum C : ℚ)
      = ((List.range C.grams.length).map fun b =>
          ((D.base.getD b []).map fun e => (e.2.2 : ℚ) * C.gramNum b e.1 e.2.1).sum).sum
        + ((List.range C.mu.length).map fun l =>
          (C.mu.getD l 0 : ℚ) * (D.rowBase.getD l 0 : ℚ)).sum := by
    simp [Data.bnum, cast_sum_map]
  have key : (C.T : ℚ) * (D.objForm z + S + R) = D.bnum C := by
    rw [mul_add, mul_add, T_mul_obj, T_mul_spent hV hW, T_mul_rows hV hW, hb]
    simp only [mul_add, List.sum_map_add] at hzero
    linarith
  rw [le_div_iff₀ hTpos]
  nlinarith [key, hS, hR, hTpos]

end Data

/-! ## The two-by-two example, and its negative control

Maximise `x` subject to `[[1, x], [x, 1]]` positive, as in `WeakDuality.lean`.
One variable of scale `1`; block `0` has constant part the identity and the
variable on the off-diagonal. The Gram vector `(1, -1)` with weight `1/2`
certifies the bound `1`; with weight `1` it is rejected.
-/

/-- The toy program. -/
def toyData : Data where
  scale := [1]
  obj := [1]
  base := [[(0, 0, 1), (1, 1, 1)]]
  byVar := [[(0, 0, 1, 1), (0, 1, 0, 1)]]
  rowBase := []
  rowByVar := [[]]

/-- Weight `1/2` on `(1, -1)`. -/
def toyCert : Cert where
  V := 1
  W := 2
  grams := [[(1, [1, -1])]]
  mu := []

/-- Weight `1` on `(1, -1)`: twice too much. -/
def toyBad : Cert := { toyCert with W := 1 }

theorem check_toy : toyData.check toyCert = true := by decide

/-- **Positive control.** Every feasible point of the toy program is at most `1`. -/
theorem toy_le_one {z : ℕ → ℚ} (hz : toyData.Feasible z) : z 0 ≤ 1 := by
  have h := Data.objForm_le check_toy hz
  have hb : toyData.bnum toyCert = 2 := by decide
  have hT : toyCert.T = 2 := by decide
  rw [hb, hT] at h
  simpa [Data.objForm, Data.nv, Data.m, toyData] using h

/-- **Negative control.** The doubled weight is rejected. -/
theorem not_check_toyBad : toyData.check toyBad = false := by decide

end Delsarte.SDP.Sparse
