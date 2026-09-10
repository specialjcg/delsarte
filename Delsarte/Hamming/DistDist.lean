/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Hamming.LP

/-!
# From the double sum over a code to the Delsarte primal

Two pieces of bookkeeping that carry a Delsarte constraint from the shape it is
*proved* in — a double sum over ordered pairs of codewords — to the shape
`Delsarte/Hamming/LP.lean` consumes. Neither knows anything about characters,
positivity, or the size of the alphabet: both hold for every `q`.

They live in their own file because the binary route
(`Delsarte/Hamming/Feasible.lean`, rational throughout) and the `q`-ary route
(`Delsarte/Hamming/FeasibleQ.lean`, which needs `ℂ`) both need them, and the
binary chain must not acquire a dependency on complex analysis to reuse a
counting argument. Same reason as `Delsarte/Krawtchouk/Subsets.lean`.
-/

namespace Delsarte.Hamming

open Finset Delsarte.LP Delsarte

variable {n d q : ℕ}

/-- The distance distribution reassembles the double sum, divided by `|C|`. Pure
counting: the pairs at distance `i` are collected into one fibre. -/
theorem sum_distDist_mul_krawtchouk (C : Code n q) (k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n q k i
      = (∑ x ∈ C, ∑ y ∈ C, krawtchouk n q k (hammingDist x y)) / C.card := by
  have hmem : ∀ p ∈ C ×ˢ C, hammingDist p.1 p.2 ∈ Finset.range (n + 1) := by
    intro p _
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    simpa using hammingDist_le_card_fintype (x := p.1) (y := p.2)
  have hprod : ∑ x ∈ C, ∑ y ∈ C, krawtchouk n q k (hammingDist x y)
      = ∑ p ∈ C ×ˢ C, krawtchouk n q k (hammingDist p.1 p.2) := by
    rw [Finset.sum_product]
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmem, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconst : ∑ p ∈ (C ×ˢ C).filter (fun p => hammingDist p.1 p.2 = i),
      krawtchouk n q k (hammingDist p.1 p.2)
      = ∑ _p ∈ (C ×ˢ C).filter (fun p => hammingDist p.1 p.2 = i), krawtchouk n q k i :=
    Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, distDist]
  ring

/-- Delsarte positivity in the shape `primalFeasible_codeVec` expects: the term
`i = 0` contributes `K_k(0)`, and the terms `0 < i < d` vanish because the code
has no pair that close. The positivity itself is the hypothesis `hnn` — that is
what differs between `q = 2` and `q > 2`, and it is the only thing that does. -/
theorem delsarte_positivity_of_nonneg (hd : 1 ≤ d) {C : Code n q} (hC : C.Nonempty)
    (hmin : MinDistAtLeast d C) (k : ℕ)
    (hnn : 0 ≤ ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n q k i) :
    0 ≤ krawtchouk n q k 0 + ∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n q k i := by
  have hsub : insert 0 (Finset.Icc d n) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_Icc] at hi
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    rcases hi with rfl | ⟨_, h2⟩
    · exact Nat.zero_le _
    · exact h2
  have hzero : ∀ i ∈ Finset.range (n + 1), i ∉ insert 0 (Finset.Icc d n) →
      distDist C i * krawtchouk n q k i = 0 := by
    intro i hi hni
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and_or, not_le] at hni
    obtain ⟨hi0, hid⟩ := hni
    rw [distDist_eq_zero_of_lt hmin (Nat.pos_of_ne_zero hi0)
      (by rcases hid with h | h <;> omega), zero_mul]
  have hsplit : ∑ i ∈ Finset.range (n + 1), distDist C i * krawtchouk n q k i
      = distDist C 0 * krawtchouk n q k 0
        + ∑ i ∈ Finset.Icc d n, distDist C i * krawtchouk n q k i := by
    rw [← Finset.sum_subset hsub hzero,
      Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
  rw [hsplit, distDist_zero hC, one_mul] at hnn
  exact hnn

end Delsarte.Hamming
