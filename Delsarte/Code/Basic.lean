/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Codes in the Hamming scheme

Basic combinatorial objects behind the Delsarte linear program for the Hamming
scheme: codes, minimum distance, the maximal size `A n q d`, and the distance
distribution of a code.

A code is an arbitrary `Finset` of words; no linear structure is assumed
anywhere. `A n q d` is a maximum over a `Finset` of codes rather than a real
supremum: the ambient space is finite, so the set of admissible cardinalities
is a finite set of naturals. The distance distribution takes values in `ℚ`,
which is what an exactly verified certificate needs.
-/

namespace Delsarte

variable {n q d : ℕ}

/-- A word of length `n` over an alphabet of size `q`. -/
abbrev Word (n q : ℕ) := Fin n → Fin q

/-- A code: an arbitrary set of words. No linear structure is assumed. -/
abbrev Code (n q : ℕ) := Finset (Word n q)

/-- Any two distinct codewords are at Hamming distance at least `d`. -/
def MinDistAtLeast (d : ℕ) (C : Code n q) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y

instance (d : ℕ) (C : Code n q) : Decidable (MinDistAtLeast d C) := by
  unfold MinDistAtLeast; infer_instance

theorem minDistAtLeast_empty : MinDistAtLeast (n := n) (q := q) d ∅ := by
  simp [MinDistAtLeast]

/-- The codes of length `n` over `Fin q` whose minimum distance is at least `d`. -/
def admissible (n q d : ℕ) : Finset (Code n q) :=
  Finset.univ.filter (MinDistAtLeast d)

theorem mem_admissible {C : Code n q} : C ∈ admissible n q d ↔ MinDistAtLeast d C := by
  simp [admissible]

theorem admissible_nonempty : (admissible n q d).Nonempty :=
  ⟨∅, mem_admissible.mpr minDistAtLeast_empty⟩

/-- `A n q d`: the largest size of a `q`-ary code of length `n` with minimum
distance at least `d`. -/
def A (n q d : ℕ) : ℕ :=
  (admissible n q d).sup Finset.card

theorem card_le_A {C : Code n q} (h : MinDistAtLeast d C) : C.card ≤ A n q d :=
  Finset.le_sup (f := Finset.card) (mem_admissible.mpr h)

theorem exists_code_card_eq_A (n q d : ℕ) :
    ∃ C : Code n q, MinDistAtLeast d C ∧ C.card = A n q d := by
  obtain ⟨C, hC, hsup⟩ := Finset.exists_mem_eq_sup _ admissible_nonempty Finset.card
  exact ⟨C, mem_admissible.mp hC, hsup.symm⟩

/-- The distance distribution of `C`: `distDist C i` is the average number of
codewords at distance exactly `i` from a fixed codeword. -/
def distDist (C : Code n q) (i : ℕ) : ℚ :=
  (((C ×ˢ C).filter fun p => hammingDist p.1 p.2 = i).card : ℚ) / C.card

theorem distDist_nonneg (C : Code n q) (i : ℕ) : 0 ≤ distDist C i :=
  div_nonneg (by positivity) (by positivity)

theorem distDist_zero {C : Code n q} (hC : C.Nonempty) : distDist C 0 = 1 := by
  have hfil : ((C ×ˢ C).filter fun p => hammingDist p.1 p.2 = 0) = C.diag := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag, hammingDist_eq_zero]
    constructor
    · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, hx⟩, rfl⟩
  rw [distDist, hfil, Finset.diag_card]
  exact div_self (by exact_mod_cast hC.card_pos.ne')

theorem distDist_eq_zero_of_lt {C : Code n q} (h : MinDistAtLeast d C) {i : ℕ}
    (hi : 0 < i) (hid : i < d) : distDist C i = 0 := by
  have hfil : ((C ×ˢ C).filter fun p => hammingDist p.1 p.2 = i) = ∅ := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.notMem_empty, iff_false, not_and]
    rintro ⟨hx, hy⟩ hd
    have hxy : x ≠ y := by
      rintro rfl
      rw [hammingDist_self] at hd
      omega
    have := h x hx y hy hxy
    omega
  rw [distDist, hfil]
  simp

theorem sum_distDist {C : Code n q} (hC : C.Nonempty) :
    ∑ i ∈ Finset.range (n + 1), distDist C i = C.card := by
  have hmem : ∀ p ∈ C ×ˢ C, hammingDist p.1 p.2 ∈ Finset.range (n + 1) := by
    intro p _
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    simpa using hammingDist_le_card_fintype (x := p.1) (y := p.2)
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  have hne : (C.card : ℚ) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  simp only [distDist]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← hfib, Finset.card_product]
  push_cast
  field_simp

end Delsarte
