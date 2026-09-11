/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Sphere.Kissing
import Delsarte.Certificate.IntTable

/-!
# The 240 roots of `E8`, and the kissing number of `ℝ^8`

`Delsarte/Sphere/Kissing.lean` proves `kissingLe 8 240` from above. This file
supplies the construction from below, and the two together give

`kissing_eight : IsGreatest (kissingSet 8) 240`

— the first place in this repository where an equality is asserted rather than a
bound.

## The root system is defined, not tabulated

A table of 240 vectors pasted from a script is a table nobody can check. The
roots are therefore written as what they are, in the doubled scaling that keeps
every coordinate an integer:

* `d8Roots` — the `112` vectors `±2 e_i ± 2 e_j` with `i < j`;
* `cosetRoots` — the `128` vectors with all coordinates `±1` and an even number
  of `-1`, read off the `256` bit patterns by their parity.

Both families have squared norm `8`, so after dividing by `√8` every vector is a
unit vector, and the Gram entry is `⟨u, v⟩ / 8`. What has to be checked is
`⟨u, v⟩ ≤ 4` off the diagonal.

## Why `Pairwise`, and why `decide`

The condition is checked on one side of the diagonal only, by
`List.Pairwise`: `28 680` integer dot products rather than `57 600`, and no list
equality test per pair. That matters — the full square measured at just under
three minutes of kernel time, the triangle at about one hundred seconds.

`List.Pairwise` is a condition on *positions*, which is exactly what is needed.
A repeated vector would give `⟨u, u⟩ = 8 > 4` and fail the check, so
distinctness is not a separate hypothesis to be trusted: it is a consequence of
the same computation (`e8Roots_nodup`).

The alternative was structural — integrality of the inner product on `E8` plus
the equality case of Cauchy-Schwarz — and it would have needed the parity
argument for the symmetric difference of two even sets. The computation is
shorter and checks strictly more: it verifies the `240` vectors themselves, not
a lemma about an abstract lattice that would still have to be instantiated.

## Negative controls

* `not_pairwise_odd_coset` — the vector `(1,…,1,-1)` has squared norm `8` like
  every root, yet its inner product with `(1,…,1)` is `6 > 4`. The parity filter
  in `cosetRoots` is what excludes it; the norm condition alone does not. Drop
  the filter and the configuration has `368` vectors and is not a kissing
  configuration.
* `not_pairwise_duplicate` — a repeated vector is rejected, so the count `240` is
  a count of distinct points.
* `d8Roots_length` and `cosetRoots_length` — `112 + 128`. Neither family alone
  reaches `240`; `cosetRoots` alone would give `128`, well under the bound.
* Dimension 24 is deliberately absent. Leech has `196 560` minimal vectors, and
  the same argument there gives only `⟨u, v⟩ ≤ 6`, i.e. `gram ≤ 3/4`: excluding
  `⟨u, v⟩ = 5` needs a property of the lattice that nothing here provides. So
  `kissingSet 24` still has only an upper bound, and the README says so.
-/

namespace Delsarte.Sphere

open Finset Delsarte Delsarte.Certificate

set_option maxRecDepth 4000000

/-! ## The roots -/

/-- The sign read off bit `i` of `m`: `+1` for a clear bit, `-1` for a set one. -/
def e8Sign (m i : ℕ) : ℤ := if m / 2 ^ i % 2 = 0 then 1 else -1

/-- The `128` vectors with all coordinates `±1` and an even number of `-1`. -/
def cosetRoots : List (List ℤ) :=
  (List.range 256).filterMap fun m =>
    if (List.range 8).countP (fun i => m / 2 ^ i % 2 == 1) % 2 == 0
    then some ((List.range 8).map (e8Sign m)) else none

/-- The `112` vectors `±2 e_i ± 2 e_j`, `i < j`. -/
def d8Roots : List (List ℤ) :=
  (List.range 8).flatMap fun i => (List.range 8).flatMap fun j =>
    if i < j then
      [(2 : ℤ), -2].flatMap fun s => [(2 : ℤ), -2].map fun t =>
        (List.range 8).map fun k => if k == i then s else if k == j then t else 0
    else []

/-- The `240` roots of `E8`, scaled so that every coordinate is an integer and
every squared norm is `8`. -/
def e8Roots : List (List ℤ) := d8Roots ++ cosetRoots

/-! ## What the kernel checks -/

theorem d8Roots_length : d8Roots.length = 112 := by decide

theorem cosetRoots_length : cosetRoots.length = 128 := by decide

theorem e8Roots_length : e8Roots.length = 240 := by decide

/-- Every root has `8` coordinates and squared norm `8`. -/
theorem e8Roots_shape : e8Roots.all (fun u => u.length == 8 && dotp u u == 8) = true := by
  decide

set_option maxHeartbeats 2000000 in
-- The 28 680 dot products take roughly a hundred seconds of kernel time, well
-- past the default budget. Scoped to this declaration, the only one needing it.
/-- **The separation.** Read on positions, so a repeated vector would fail it. -/
theorem e8Roots_pairwise : e8Roots.Pairwise (fun u v => dotp u v ≤ 4) := by decide

/-! ## From the list to indexed points -/

/-- The `i`-th root. -/
def e8Root (i : Fin 240) : List ℤ := e8Roots.getD i []

theorem e8Root_eq_getElem (i : Fin 240) :
    e8Root i = e8Roots[(i : ℕ)]'(by rw [e8Roots_length]; exact i.isLt) := by
  have h : (i : ℕ) < e8Roots.length := by rw [e8Roots_length]; exact i.isLt
  rw [e8Root, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem e8Root_mem (i : Fin 240) : e8Root i ∈ e8Roots := by
  rw [e8Root_eq_getElem]
  exact List.getElem_mem _

theorem e8Root_length (i : Fin 240) : (e8Root i).length = 8 := by
  have h := List.all_eq_true.mp e8Roots_shape _ (e8Root_mem i)
  simpa using (Bool.and_eq_true _ _ |>.mp h).1

theorem e8Root_dotp_self (i : Fin 240) : dotp (e8Root i) (e8Root i) = 8 := by
  have h := List.all_eq_true.mp e8Roots_shape _ (e8Root_mem i)
  simpa using (Bool.and_eq_true _ _ |>.mp h).2

/-- Off the diagonal the dot product is at most `4`, in both orders. -/
theorem e8Root_dotp_le {i j : Fin 240} (hij : i ≠ j) : dotp (e8Root i) (e8Root j) ≤ 4 := by
  have hlen : ∀ k : Fin 240, (k : ℕ) < e8Roots.length := fun k => by
    rw [e8Roots_length]; exact k.isLt
  have hpw := List.pairwise_iff_getElem.mp e8Roots_pairwise
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · rw [e8Root_eq_getElem, e8Root_eq_getElem]
    exact hpw _ _ (hlen i) (hlen j) h
  · rw [dotp_comm, e8Root_eq_getElem, e8Root_eq_getElem]
    exact hpw _ _ (hlen j) (hlen i) h

/-- The roots are pairwise distinct: a repetition would give `8 ≤ 4`. -/
theorem e8Roots_nodup : e8Roots.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro a b hab
  by_contra hne
  have hlt : (a : ℕ) ≠ (b : ℕ) := fun h => hne (Fin.ext h)
  have hpw := List.pairwise_iff_getElem.mp e8Roots_pairwise
  have hd : dotp e8Roots[(a : ℕ)] e8Roots[(b : ℕ)] ≤ 4 := by
    rcases lt_or_gt_of_ne hlt with h | h
    · exact hpw _ _ a.isLt b.isLt h
    · rw [dotp_comm]; exact hpw _ _ b.isLt a.isLt h
  have hab' : e8Roots[(a : ℕ)] = e8Roots[(b : ℕ)] := hab
  rw [hab'] at hd
  have hself : dotp e8Roots[(b : ℕ)] e8Roots[(b : ℕ)] = 8 := by
    have hmem : e8Roots[(b : ℕ)] ∈ e8Roots := List.getElem_mem _
    have h := List.all_eq_true.mp e8Roots_shape _ hmem
    simpa using (Bool.and_eq_true _ _ |>.mp h).2
  rw [hself] at hd
  norm_num at hd

/-! ## The unit vectors -/

theorem sqrt_eight_mul_self : Real.sqrt 8 * Real.sqrt 8 = 8 :=
  Real.mul_self_sqrt (by norm_num)

/-- The `i`-th root, divided by `√8`. -/
noncomputable def e8Vec (i : Fin 240) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 fun k : Fin 8 => (ent (e8Root i) k : ℝ) / Real.sqrt 8

@[simp]
theorem e8Vec_apply (i : Fin 240) (k : Fin 8) :
    WithLp.ofLp (e8Vec i) k = (ent (e8Root i) k : ℝ) / Real.sqrt 8 := rfl

/-- The bridge from `Finset.sum` over `Fin 8` to the list-level `dotp`. -/
theorem sum_ent_mul (i j : Fin 240) :
    ∑ k : Fin 8, (ent (e8Root i) k : ℝ) * (ent (e8Root j) k : ℝ)
      = ((dotp (e8Root i) (e8Root j) : ℤ) : ℝ) := by
  have h := dotp_eq_sum (e8Root i) (e8Root j) 8 (e8Root_length i) (e8Root_length j)
  rw [h]
  push_cast
  exact Fin.sum_univ_eq_sum_range (fun k => (ent (e8Root i) k : ℝ) * (ent (e8Root j) k : ℝ)) 8

theorem inner_e8Vec (i j : Fin 240) :
    inner ℝ (e8Vec i) (e8Vec j) = ((dotp (e8Root i) (e8Root j) : ℤ) : ℝ) / 8 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, e8Vec_apply,
    div_mul_div_comm]
  rw [← Finset.sum_div, sqrt_eight_mul_self, sum_ent_mul j i, dotp_comm (e8Root j) (e8Root i)]

theorem norm_e8Vec (i : Fin 240) : ‖e8Vec i‖ = 1 := by
  have h : ‖e8Vec i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_e8Vec, e8Root_dotp_self]
    norm_num
  nlinarith [norm_nonneg (e8Vec i), h]

/-- The `240` unit vectors. -/
noncomputable def e8Points : UnitPoints 8 240 where
  pts := e8Vec
  norm_pts := norm_e8Vec

theorem e8Points_gram (i j : Fin 240) :
    e8Points.gram i j = ((dotp (e8Root i) (e8Root j) : ℤ) : ℝ) / 8 :=
  inner_e8Vec i j

/-- **The separation, on the sphere.** -/
theorem e8Points_gram_le {i j : Fin 240} (hij : i ≠ j) : e8Points.gram i j ≤ 1 / 2 := by
  rw [e8Points_gram]
  have h : ((dotp (e8Root i) (e8Root j) : ℤ) : ℝ) ≤ 4 := by
    exact_mod_cast e8Root_dotp_le hij
  linarith

/-! ## The kissing number of `ℝ^8` -/

theorem mem_kissingSet_eight : (240 : ℕ) ∈ kissingSet 8 :=
  ⟨e8Points, fun _ _ hij => e8Points_gram_le hij⟩

/-- **The kissing number of `ℝ^8` is exactly 240.** The upper bound is the
Odlyzko-Sloane linear program of `Delsarte/Sphere/Kissing.lean`; the lower bound
is the root system above. Neither half is conditional. -/
theorem kissing_eight : IsGreatest (kissingSet 8) 240 :=
  ⟨mem_kissingSet_eight, fun _ hM => kissingSet_eight_le _ hM⟩

/-- `241` is excluded, which is the content of the upper bound restated. -/
theorem not_mem_kissingSet_eight : (241 : ℕ) ∉ kissingSet 8 := by
  intro h
  have := kissingSet_eight_le 241 h
  norm_num at this

/-! ## Negative controls -/

/-- Odd parity is excluded by the filter, not by the norm: this vector has
squared norm `8` exactly like every root. -/
theorem odd_coset_norm : dotp [1, 1, 1, 1, 1, 1, 1, -1] [1, 1, 1, 1, 1, 1, 1, -1] = 8 := by
  decide

/-- ...and yet it is at dot product `6 > 4` from `(1, …, 1)`, so admitting it
would break the separation. Dropping the parity filter gives `368` vectors and no
kissing configuration. -/
theorem not_pairwise_odd_coset :
    ¬ List.Pairwise (fun u v => dotp u v ≤ 4)
      [[1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, -1]] := by decide

/-- A repeated vector is rejected by the same check, so `240` counts distinct
points. -/
theorem not_pairwise_duplicate :
    ¬ List.Pairwise (fun u v => dotp u v ≤ 4)
      [[2, 2, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0]] := by decide

/-- Neither family reaches `240` alone. -/
theorem cosetRoots_lt_240 : cosetRoots.length < 240 := by
  rw [cosetRoots_length]; norm_num

theorem d8Roots_lt_240 : d8Roots.length < 240 := by
  rw [d8Roots_length]; norm_num

end Delsarte.Sphere
