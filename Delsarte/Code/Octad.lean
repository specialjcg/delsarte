/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Code.Golay

/-!
# The 759 octads of the extended Golay code

An *octad* is a codeword of weight `8` in the extended binary Golay code
`[24, 12, 8]`. There are `759` of them, and they carry the largest of the three
families of minimal Leech vectors: `759 × 2^7 = 97 152` vectors of shape
`(∓2^8, 0^16)`, one per octad and per even sign pattern on its support.

## Which Golay code

`golay24Row` of `Delsarte/Code/Golay.lean`, the one whose minimum distance `8`
the kernel has already checked and which gives `A(24, 2, 8) = 4096`. The octads
are read off the same generator rows and the same encoding `cwt`, so nothing
here introduces a second, unverified table of codewords. A file that pasted its
own list of `759` supports would be a file nobody can check.

## What the kernel does, and what it costs

`octadMsgs` is `(List.range 4096).filter isOctad`: the messages, not the
codewords. Its `Nodup` is then free — a filter of `List.range` — and that
matters, because the Leech construction indexes octads by position and needs
distinct positions to name distinct octads.

Its length is the expensive half. Counting the weight-`8` codewords means
encoding all `4096` messages, the same sweep as `minWt_golay24`, and the kernel
never prunes its weak-head normal form cache inside a declaration. So the count
is cut into eight slices of `512`, each its own declaration, exactly as the
minimum-weight check was after a build was killed at `22.9 GB`. The slices are
uneven — `210, 120, 56, 120, 56, 21, 56, 120` — which is a property of the code,
not of the cut.

`filter_range_split8` is generic in the predicate, so the reassembly costs
nothing to elaborate; only the eight `decide +kernel` calls pay.

## Negative controls

* `not_isOctad_zero` — the zero message encodes the zero codeword, weight `0`.
  The filter is not vacuous at the bottom.
* `not_isOctad_nine` — message `9` has weight `12`. Weight `12` is the bulk of
  the code (`2576` of the `4096` words), and `759` is genuinely a count of
  something rarer, not a restatement of the code size.
* `isOctad_one` — message `1` is the first generator row: the polynomial `g` has
  odd weight `7`, so the parity bit is `1` and the row has weight `8`. A positive
  witness, so the filter is not vacuous at the top either.
-/

namespace Delsarte

set_option maxRecDepth 100000

/-! ## The octads -/

/-- Message `m` encodes a codeword of weight `8`. -/
def isOctad (m : ℕ) : Bool := cwt golay24Row 12 24 m == 8

/-- The messages whose codewords are octads. Filtering `List.range` rather than
listing supports keeps `Nodup` free and keeps the octads tied to the Golay code
that was actually proved. -/
def octadMsgs : List ℕ := (List.range 4096).filter isOctad

/-- `filter` over `range 4096`, cut into eight slices of `512`. Generic in the
predicate: the reassembly is free, and only the slices below pay. -/
theorem filter_range_split8 (p : ℕ → Bool) :
    (List.range 4096).filter p
      = (List.range' 0 512).filter p ++ (List.range' 512 512).filter p
        ++ (List.range' 1024 512).filter p ++ (List.range' 1536 512).filter p
        ++ (List.range' 2048 512).filter p ++ (List.range' 2560 512).filter p
        ++ (List.range' 3072 512).filter p ++ (List.range' 3584 512).filter p := by
  have h : ∀ s a b : ℕ, (List.range' s (a + b)).filter p
      = (List.range' s a).filter p ++ (List.range' (s + a) b).filter p := by
    intro s a b
    rw [← List.range'_append, List.filter_append]
    simp
  rw [List.range_eq_range']
  rw [show (4096 : ℕ) = 512 + 3584 from rfl, h 0 512 3584,
    show (0 + 512 : ℕ) = 512 from rfl,
    show (3584 : ℕ) = 512 + 3072 from rfl, h 512 512 3072,
    show (512 + 512 : ℕ) = 1024 from rfl,
    show (3072 : ℕ) = 512 + 2560 from rfl, h 1024 512 2560,
    show (1024 + 512 : ℕ) = 1536 from rfl,
    show (2560 : ℕ) = 512 + 2048 from rfl, h 1536 512 2048,
    show (1536 + 512 : ℕ) = 2048 from rfl,
    show (2048 : ℕ) = 512 + 1536 from rfl, h 2048 512 1536,
    show (2048 + 512 : ℕ) = 2560 from rfl,
    show (1536 : ℕ) = 512 + 1024 from rfl, h 2560 512 1024,
    show (2560 + 512 : ℕ) = 3072 from rfl,
    show (1024 : ℕ) = 512 + 512 from rfl, h 3072 512 512,
    show (3072 + 512 : ℕ) = 3584 from rfl]
  simp [List.append_assoc]

/-! ## The count, one slice at a time -/

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice0 : ((List.range' 0 512).filter isOctad).length = 210 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice1 : ((List.range' 512 512).filter isOctad).length = 120 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice2 : ((List.range' 1024 512).filter isOctad).length = 56 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice3 : ((List.range' 1536 512).filter isOctad).length = 120 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice4 : ((List.range' 2048 512).filter isOctad).length = 56 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice5 : ((List.range' 2560 512).filter isOctad).length = 21 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice6 : ((List.range' 3072 512).filter isOctad).length = 56 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- One slice of the sweep: 512 messages encoded and weighed, far past the default.
theorem octadSlice7 : ((List.range' 3584 512).filter isOctad).length = 120 := by decide +kernel

/-- **There are exactly 759 octads.** -/
theorem octadMsgs_length : octadMsgs.length = 759 := by
  rw [octadMsgs, filter_range_split8]
  simp only [List.length_append, octadSlice0, octadSlice1, octadSlice2, octadSlice3,
    octadSlice4, octadSlice5, octadSlice6, octadSlice7]

/-! ## What the Leech construction reads -/

/-- Free, because `octadMsgs` filters a range instead of listing supports. -/
theorem octadMsgs_nodup : octadMsgs.Nodup := List.nodup_range.filter _

theorem mem_octadMsgs {m : ℕ} (h : m ∈ octadMsgs) : m < 4096 ∧ cwt golay24Row 12 24 m = 8 := by
  rw [octadMsgs, List.mem_filter, List.mem_range] at h
  exact ⟨h.1, by simpa [isOctad] using h.2⟩

/-- The `o`-th octad message. -/
def octadOf (o : ℕ) : ℕ := octadMsgs.getD o 0

theorem octadOf_mem {o : ℕ} (ho : o < 759) : octadOf o ∈ octadMsgs := by
  have h : o < octadMsgs.length := by rw [octadMsgs_length]; exact ho
  rw [octadOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem _

/-- Distinct positions name distinct octads. This is what lets the Leech family
index its largest part by `o < 759` and still be injective. -/
theorem octadOf_injOn {o o' : ℕ} (ho : o < 759) (ho' : o' < 759)
    (h : octadOf o = octadOf o') : o = o' := by
  have h1 : o < octadMsgs.length := by rw [octadMsgs_length]; exact ho
  have h2 : o' < octadMsgs.length := by rw [octadMsgs_length]; exact ho'
  have e1 : octadOf o = octadMsgs[o]'h1 := by
    rw [octadOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rfl
  have e2 : octadOf o' = octadMsgs[o']'h2 := by
    rw [octadOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  rw [e1, e2] at h
  have hfin : (⟨o, h1⟩ : Fin octadMsgs.length) = ⟨o', h2⟩ :=
    List.nodup_iff_injective_getElem.mp octadMsgs_nodup h
  exact congrArg Fin.val hfin

/-! ## Negative controls -/

/-- The zero codeword has weight `0`, not `8`. -/
theorem not_isOctad_zero : isOctad 0 = false := by decide +kernel

/-- Message `9` has weight `12`. Weight `12` is the bulk of the code — `2576` of
the `4096` words — so `759` counts something rarer than "a codeword". -/
theorem cwt_nine : cwt golay24Row 12 24 9 = 12 := by decide +kernel

theorem not_isOctad_nine : isOctad 9 = false := by decide +kernel

/-- A positive witness: message `1` is the first generator row. `g` has odd
weight `7`, so its parity bit is `1` and the row has weight `8`. -/
theorem isOctad_one : isOctad 1 = true := by decide +kernel

end Delsarte
