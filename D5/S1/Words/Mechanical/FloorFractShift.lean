/- GID: D5/S1/Words/Mechanical/FloorFractShift
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In every linearly ordered floor ring, a shifted floor splits off the fractional part, whose shifted floor is the shift floor plus its carry indicator. -/

import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT

Pinned-library search:
* Searched the complete pinned `Mathlib` and Lean-core source trees by target
  names, target formula fragments, and combinations of `floor`, `fract`,
  `indicator`, `Beatty`, `Sturmian`, and `mechanical`.
* Inspected the floor API in `Mathlib/Algebra/Order/Floor/{Defs,Div,Extended,
  Ring,Semifield,Semiring}.lean`, including `Int.floor_intCast_add`,
  `Int.le_floor_add`, `Int.le_floor_add_floor`, `Int.floor_add_fract`,
  `Int.fract_add_floor`, `Int.fract_add`, `Int.fract_add_le`,
  `Int.fract_add_fract_le`, `Int.fract_nonneg`, and `Int.fract_lt_one`.
* Inspected `Mathlib/Algebra/Order/Round.lean`, the complete pinned
  `Mathlib/Dynamics/` tree, `Mathlib/NumberTheory/Rayleigh.lean` (Beatty
  sequences), the continued-fraction floor/fract files, and the pinned Lean
  core. None contains either target statement or a theorem trivially
  reformulating either one. Of the inspected floor API, `Int.floor_intCast_add`,
  `Int.floor_add_fract`, `Int.floor_eq_iff`, `Int.fract_nonneg`, and
  `Int.fract_lt_one` are used directly below.
* Repository search found exactly the five private pairs identified in the
  task, spread across `Words`, `Words/Complexity`, `Words/Mechanical`, and
  `Words/ReturnWords`; no public declaration in the repository shares either
  target name.

Generality and address decisions:
* The natural-universality rule at specification line 86 applies: neither
  result depends on `Real`. Both are stated for `[Ring R] [LinearOrder R]
  [IsOrderedRing R] [FloorRing R]`. This is the pinned spelling, weaker than
  the usual strict ordered-ring assumptions; `IsOrderedRing` is required even
  by pinned `Int.floor_intCast_add`. Generalization therefore succeeds, with
  no `Real`, Archimedean, field, or D5 hypothesis.
* The header records `G`. Specification line 86 defines `G` as general
  machinery subject to the natural-universality rule, while `I` is instance
  luck such as a fixed class number or modulus; neither declaration carries
  instance-specific data. Rule H10 at specification line 219, enforced by
  SL-010, requires the field and forbids a `G` file from importing instance
  facts; this file imports `Mathlib` alone. The worked example at specification
  line 346 (`ModelSet→G`) confirms the parameterized side of that distinction;
  its final specialization is illustrative, not a requirement imposed here.
* The selected GID is `D5/S1/Words/Mechanical/FloorFractShift`. Specification
  line 92 keeps `Metallic/` and `Moduli/` as uninstantiated coordinates that
  SL-021 rejects under M0, so no admissible generic-package address exists. The
  D5 address is conservative because all five consumers are mechanical-word
  arguments, two copies already live in this bucket, adding this file leaves
  the bucket below the strictly-greater-than-12 split threshold, and placing it
  in the 12-file `Words` root would trigger that threshold.

Thin-wrapper check:
* `floor_add_sub_floor` has two substantive steps after rewrite bookkeeping:
  reconstruct `x + t` from the integer and fractional parts of `x`, then
  cancel the resulting integer floors.
* `floor_fract_add_indicator` has three substantive steps after rewrite
  bookkeeping: decompose `t`, split on the carry threshold, and prove the two
  floor intervals from the fractional-part bounds. Neither theorem is a
  one-step consequence of one pinned declaration.

The inspected-candidate list above is not claimed to be exhaustive.
-/

namespace D5.S1.Words.Mechanical.FloorFractShift

/-- A floor increment depends only on the starting fractional part. -/
theorem floor_add_sub_floor {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
    [FloorRing R] (x t : R) :
    ⌊x + t⌋ - ⌊x⌋ = ⌊Int.fract x + t⌋ := by
  have hx : (⌊x⌋ : R) + (Int.fract x + t) = x + t := by
    calc
      (⌊x⌋ : R) + (Int.fract x + t) = ((⌊x⌋ : R) + Int.fract x) + t := by
        rw [add_assoc]
      _ = x + t := by rw [Int.floor_add_fract]
  rw [← hx, Int.floor_intCast_add]
  omega

/-- Adding two fractional parts contributes exactly the indicated carry. -/
theorem floor_fract_add_indicator {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
    [FloorRing R] (x t : R) :
    ⌊Int.fract x + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ Int.fract x then 1 else 0 := by
  have hdecomp : (⌊t⌋ : R) + (Int.fract x + Int.fract t) = Int.fract x + t := by
    calc
      (⌊t⌋ : R) + (Int.fract x + Int.fract t) =
          Int.fract x + ((⌊t⌋ : R) + Int.fract t) := by ac_rfl
      _ = Int.fract x + t := by rw [Int.floor_add_fract]
  rw [← hdecomp, Int.floor_intCast_add]
  congr 1
  by_cases h : 1 - Int.fract t ≤ Int.fract x
  · rw [if_pos h, Int.floor_eq_iff]
    norm_num
    constructor
    · exact (sub_le_iff_le_add.mp h)
    · simpa only [one_add_one_eq_two] using
        add_lt_add (Int.fract_lt_one x) (Int.fract_lt_one t)
  · rw [if_neg h, Int.floor_eq_iff]
    norm_num
    constructor
    · exact add_nonneg (Int.fract_nonneg x) (Int.fract_nonneg t)
    · have hlt : Int.fract x < 1 - Int.fract t := lt_of_not_ge h
      exact lt_sub_iff_add_lt.mp hlt

#print axioms floor_add_sub_floor
#print axioms floor_fract_add_indicator

end D5.S1.Words.Mechanical.FloorFractShift
