/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Sphere.Kissing
import Delsarte.Certificate.IntTable

/-!
# Integer configurations, and separation from a lattice minimum

`Delsarte/Sphere/E8.lean` turns `240` integer vectors into a member of
`kissingSet 8`. Ninety of its lines say nothing about `E8`: they divide by
`√8`, push a list-level `dotp` through `PiLp`, and read a `List.Pairwise` on
positions as a condition on `Fin 240`. Dimension `24` would copy them verbatim
with `8` replaced by `24`, `240` by `196 560` and `8` by `32`. This file writes
them once.

## What a configuration is

`IntConfig n M N` is `M` integer vectors of length `n`, each of squared norm
`N`, pairwise separated by `2 ⟪u, v⟫ ≤ N`. Dividing by `√N` sends them to the
unit sphere of `ℝ^n` and the separation to `gram ≤ 1/2`, which is exactly
membership in `kissingSet n`. The count `M` is a field rather than
`vecs.length`, so a user states `IntConfig 24 196560 32` and never rewrites a
cardinality afterwards.

Distinctness is not a field. A repeated vector would give `2 N ≤ N`, which
`0 < N` refutes; `IntConfig.nodup` is therefore a consequence of the separation,
not an extra thing to be trusted. This is the same accounting as the linear
codes of `Delsarte/Code/Linear.lean`, where injectivity of the encoding follows
from the minimum weight instead of being assumed.

## Where the separation comes from

`two_dotp_le_of_min` is the one line that makes dimension `24` conceivable at
all. If `u` and `v` have squared norm `N` and their difference has squared norm
at least `N`, then

`N ≤ |u - v|² = N - 2 ⟪u, v⟫ + N`, hence `2 ⟪u, v⟫ ≤ N`.

For a lattice, `u - v` is again a lattice vector, so "at least `N`" is the
lattice minimum and nothing more. One inequality replaces the `M (M-1) / 2`
inner products a direct check would need — `28 680` for `E8`, which the kernel
does decide, and `1.9 · 10¹⁰` for Leech, which it never will.

## What this file does not prove

`IntConfig.sep` is a hypothesis. `two_dotp_le_of_min` reduces it to a minimum,
but the minimum itself is a fact about a specific lattice, and no such fact is
established here. For `E8` the minimum is bypassed entirely: `e8Config` feeds
the brute-force `e8Roots_pairwise` into the structure, and the kernel still
checks all `28 680` products. Leech will need the minimum, and that proof does
not exist yet in this repository.

## Negative control

`two_dotp_le_of_min_fails` exhibits two vectors of squared norm `8` whose
difference has squared norm `4` and whose separation fails, `2 · 6 = 12 > 8`.
The minimum hypothesis is load-bearing, and the witness is the same pair that
`E8.lean`'s `not_pairwise_odd_coset` rejects: dropping the parity filter on the
coset is exactly dropping the minimum.
-/

namespace Delsarte.Lattice

open Finset Delsarte Delsarte.Certificate

/-! ## Differences of integer vectors -/

/-- Coordinatewise difference. Defined on lists, so it is total; every statement
below pairs it with an equality of lengths. -/
def vsub (u v : List ℤ) : List ℤ := List.zipWith (· - ·) u v

@[simp]
theorem vsub_cons (a b : ℤ) (as bs : List ℤ) :
    vsub (a :: as) (b :: bs) = (a - b) :: vsub as bs := rfl

theorem vsub_length (u v : List ℤ) : (vsub u v).length = min u.length v.length := by
  simp [vsub]

/-- The squared norm of a difference, expanded. Proved by induction on the lists
rather than through `dotp_eq_sum`, which would need an ambient dimension. -/
theorem dotp_vsub : ∀ u v : List ℤ, u.length = v.length →
    dotp (vsub u v) (vsub u v) = dotp u u - 2 * dotp u v + dotp v v := by
  intro u
  induction u with
  | nil =>
      intro v h
      cases v with
      | nil => simp [vsub, dotp]
      | cons b bs => simp at h
  | cons a as ih =>
      intro v h
      cases v with
      | nil => simp at h
      | cons b bs =>
          have h' : as.length = bs.length := by simpa using h
          rw [vsub_cons]
          simp only [dotp_cons]
          rw [ih bs h']
          ring

/-- **Separation is a consequence of the minimum.** Two vectors of squared norm
`N` whose difference is no shorter than `N` are separated at `N / 2`. For a
lattice this is the whole of the pairwise condition: the difference is a lattice
vector, and `N` is the minimum. -/
theorem two_dotp_le_of_min {u v : List ℤ} {N : ℤ} (hlen : u.length = v.length)
    (hnu : dotp u u = N) (hnv : dotp v v = N)
    (hmin : N ≤ dotp (vsub u v) (vsub u v)) :
    2 * dotp u v ≤ N := by
  rw [dotp_vsub u v hlen, hnu, hnv] at hmin
  omega

/-! ## Configurations -/

/-- `M` integer vectors of length `n` and squared norm `N`, separated at `N / 2`.
The separation is stated as `2 ⟪u, v⟫ ≤ N` to stay inside `ℤ`. -/
structure IntConfig (n M : ℕ) (N : ℤ) where
  /-- The vectors, in the scaling where every coordinate is an integer. -/
  vecs : List (List ℤ)
  /-- How many there are. A field, so no cardinality has to be rewritten later. -/
  card : vecs.length = M
  /-- The squared norm is positive, which is what makes `√N` a scaling factor. -/
  npos : 0 < N
  /-- Every vector has `n` coordinates and squared norm `N`. -/
  shape : vecs.all (fun u => u.length == n && dotp u u == N) = true
  /-- The separation, read on positions: one side of the diagonal only. -/
  sep : vecs.Pairwise (fun u v => 2 * dotp u v ≤ N)

namespace IntConfig

variable {n M : ℕ} {N : ℤ}

/-! ### From the list to indexed vectors -/

/-- The `i`-th vector. -/
def vec (c : IntConfig n M N) (i : Fin M) : List ℤ := c.vecs.getD i []

theorem vec_eq_getElem (c : IntConfig n M N) (i : Fin M) :
    c.vec i = c.vecs[(i : ℕ)]'(by rw [c.card]; exact i.isLt) := by
  have h : (i : ℕ) < c.vecs.length := by rw [c.card]; exact i.isLt
  rw [vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem vec_mem (c : IntConfig n M N) (i : Fin M) : c.vec i ∈ c.vecs := by
  rw [vec_eq_getElem]
  exact List.getElem_mem _

theorem vec_length (c : IntConfig n M N) (i : Fin M) : (c.vec i).length = n := by
  have h := List.all_eq_true.mp c.shape _ (c.vec_mem i)
  simpa using (Bool.and_eq_true _ _ |>.mp h).1

theorem dotp_self (c : IntConfig n M N) (i : Fin M) : dotp (c.vec i) (c.vec i) = N := by
  have h := List.all_eq_true.mp c.shape _ (c.vec_mem i)
  simpa using (Bool.and_eq_true _ _ |>.mp h).2

/-- The separation off the diagonal, in both orders. -/
theorem dotp_le (c : IntConfig n M N) {i j : Fin M} (hij : i ≠ j) :
    2 * dotp (c.vec i) (c.vec j) ≤ N := by
  have hlen : ∀ k : Fin M, (k : ℕ) < c.vecs.length := fun k => by
    rw [c.card]; exact k.isLt
  have hpw := List.pairwise_iff_getElem.mp c.sep
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · rw [vec_eq_getElem, vec_eq_getElem]
    exact hpw _ _ (hlen i) (hlen j) h
  · rw [dotp_comm, vec_eq_getElem, vec_eq_getElem]
    exact hpw _ _ (hlen j) (hlen i) h

/-- The vectors are pairwise distinct: a repetition would give `2 N ≤ N`. -/
theorem nodup (c : IntConfig n M N) : c.vecs.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro a b hab
  by_contra hne
  have hlt : (a : ℕ) ≠ (b : ℕ) := fun h => hne (Fin.ext h)
  have hpw := List.pairwise_iff_getElem.mp c.sep
  have hd : 2 * dotp c.vecs[(a : ℕ)] c.vecs[(b : ℕ)] ≤ N := by
    rcases lt_or_gt_of_ne hlt with h | h
    · exact hpw _ _ a.isLt b.isLt h
    · rw [dotp_comm]; exact hpw _ _ b.isLt a.isLt h
  have hab' : c.vecs[(a : ℕ)] = c.vecs[(b : ℕ)] := hab
  rw [hab'] at hd
  have hself : dotp c.vecs[(b : ℕ)] c.vecs[(b : ℕ)] = N := by
    have hmem : c.vecs[(b : ℕ)] ∈ c.vecs := List.getElem_mem _
    have h := List.all_eq_true.mp c.shape _ hmem
    simpa using (Bool.and_eq_true _ _ |>.mp h).2
  rw [hself] at hd
  have hN := c.npos
  omega

/-! ### The unit vectors -/

theorem sqrt_mul_self (c : IntConfig n M N) :
    Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
  Real.mul_self_sqrt (by exact_mod_cast c.npos.le)

theorem cast_npos (c : IntConfig n M N) : (0 : ℝ) < (N : ℝ) := by exact_mod_cast c.npos

/-- The `i`-th vector, divided by `√N`. -/
noncomputable def point (c : IntConfig n M N) (i : Fin M) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun k : Fin n => (ent (c.vec i) k : ℝ) / Real.sqrt (N : ℝ)

@[simp]
theorem point_apply (c : IntConfig n M N) (i : Fin M) (k : Fin n) :
    WithLp.ofLp (c.point i) k = (ent (c.vec i) k : ℝ) / Real.sqrt (N : ℝ) := rfl

/-- The bridge from `Finset.sum` over `Fin n` to the list-level `dotp`. -/
theorem sum_ent_mul (c : IntConfig n M N) (i j : Fin M) :
    ∑ k : Fin n, (ent (c.vec i) k : ℝ) * (ent (c.vec j) k : ℝ)
      = ((dotp (c.vec i) (c.vec j) : ℤ) : ℝ) := by
  have h := dotp_eq_sum (c.vec i) (c.vec j) n (c.vec_length i) (c.vec_length j)
  rw [h]
  push_cast
  exact Fin.sum_univ_eq_sum_range
    (fun k => (ent (c.vec i) k : ℝ) * (ent (c.vec j) k : ℝ)) n

theorem inner_point (c : IntConfig n M N) (i j : Fin M) :
    inner ℝ (c.point i) (c.point j) = ((dotp (c.vec i) (c.vec j) : ℤ) : ℝ) / (N : ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, point_apply,
    div_mul_div_comm]
  rw [← Finset.sum_div, c.sqrt_mul_self, c.sum_ent_mul j i,
    dotp_comm (c.vec j) (c.vec i)]

theorem norm_point (c : IntConfig n M N) (i : Fin M) : ‖c.point i‖ = 1 := by
  have hN := c.cast_npos
  have h : ‖c.point i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, c.inner_point, c.dotp_self]
    field_simp
  nlinarith [norm_nonneg (c.point i), h]

/-- The configuration on the unit sphere. -/
noncomputable def points (c : IntConfig n M N) : Sphere.UnitPoints n M where
  pts := c.point
  norm_pts := c.norm_point

theorem gram_eq (c : IntConfig n M N) (i j : Fin M) :
    c.points.gram i j = ((dotp (c.vec i) (c.vec j) : ℤ) : ℝ) / (N : ℝ) :=
  c.inner_point i j

/-- **The separation, on the sphere.** -/
theorem gram_le (c : IntConfig n M N) {i j : Fin M} (hij : i ≠ j) :
    c.points.gram i j ≤ 1 / 2 := by
  have hN := c.cast_npos
  have h : 2 * ((dotp (c.vec i) (c.vec j) : ℤ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast c.dotp_le hij
  rw [gram_eq, div_le_iff₀ hN]
  linarith

/-- **The lower bound.** `M` unit vectors of `ℝ^n`, pairwise at inner product at
most `1/2`: a kissing configuration of size `M`. -/
theorem mem_kissingSet (c : IntConfig n M N) : M ∈ Sphere.kissingSet n :=
  ⟨c.points, fun _ _ hij => c.gram_le hij⟩

end IntConfig

/-! ## Negative control -/

/-- All coordinates `+1`, in the doubled `E8` scaling. -/
def onesEight : List ℤ := [1, 1, 1, 1, 1, 1, 1, 1]

/-- The same with one sign flipped: odd parity, so `E8.lean`'s coset filter
rejects it, though its squared norm is `8` like every root. -/
def oddEight : List ℤ := [1, 1, 1, 1, 1, 1, 1, -1]

/-- The minimum hypothesis of `two_dotp_le_of_min` is load-bearing. Both vectors
have squared norm `8`; their difference has squared norm `4`, below it; and the
conclusion fails, `2 * 6 = 12 > 8`. Equal norms alone separate nothing. -/
theorem two_dotp_le_of_min_fails :
    dotp onesEight onesEight = 8 ∧ dotp oddEight oddEight = 8
      ∧ dotp (vsub onesEight oddEight) (vsub onesEight oddEight) = 4
      ∧ ¬ 2 * dotp onesEight oddEight ≤ 8 :=
  ⟨by decide, by decide, by decide, by decide⟩

end Delsarte.Lattice
