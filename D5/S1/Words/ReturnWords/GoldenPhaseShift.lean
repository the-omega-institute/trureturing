/- GID: D5/S1/Words/ReturnWords/GoldenPhaseShift
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden mechanical phases commute with shifts of their natural-number index. -/

import Mathlib
import D5.S1.Words.ReturnWords.GoldenOccurrenceGaps

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT

Inspected candidates:
* Pinned mathlib's complete `Mathlib/Algebra/Order/Floor/` directory, especially
  `Int.fract_add`, `Int.fract_add_intCast`, `Int.fract_add_natCast`,
  `Int.fract_intCast_add`, `Int.fract_natCast_add`, `Int.fract_eq_fract`,
  `Int.fract_fract`, and `Int.floor_add_fract`; plus
  `Mathlib/Algebra/Field/Periodic.lean` for `Int.fract_periodic`.
* The complete pinned Batteries and Lean-core source trees for fractional-part,
  floor-shift, and periodicity declarations; neither tree defines `Int.fract` or
  a theorem with the target shape.
* The repository-wide `golden_phase_add`, `goldenPhase`, and nested-`Int.fract`
  matches. This found the three frozen private copies motivating this interface,
  the private generic `GoldenArcFirstReturnInternal.local_orbit_phase_add`, and
  the public two-sided identity `ThreeGap.fract_add_fract_eq`.
* The related private declarations `golden_phase_add_eq_sub_nat`,
  `golden_phase_add_of_no_wrap`, and `golden_phase_add_of_wrap`.

Substantive non-bookkeeping lemmas actually used by the proof:
* `Int.floor_add_fract`
* `Int.fract_intCast_add`

The proof also explicitly uses `add_assoc` for reassociation bookkeeping.

The closest pinned declarations do not supply the whole result in one
application: `Int.fract_add` only gives an unspecified integer discrepancy,
the cast-shift lemmas require an explicit integer summand, and
`Int.fract_periodic` only states period one. The public D5 theorem
`ThreeGap.fract_add_fract_eq` is also not the same claim: it reduces both
summands before the outer `Int.fract`, whereas the target leaves the displacement
unreduced; deriving the target from it still requires a separate integer-shift
invariance argument. After removing unfolding, cast normalization,
reassociation, and ring normalization, the substantive-reasoning count is two:
decompose the base argument into its integer floor and fractional part, then
remove that integer translation. These are the two independent lemmas listed
above rather than one pinned theorem plus bookkeeping.

Generality is `I`: the public statement is about the concrete Real-valued
`goldenPhase` and `goldenMechanicalSlope`, and its weakest repository import is
the instance-level module defining `goldenPhase`. A mathematical generalization
does succeed for an arbitrary linearly ordered floor ring and an arbitrary
slope: one replaces `goldenPhase i` by the defining fractional-part expression.
It fails only as a substitute for this public interface, because `goldenPhase`
itself is a concrete, non-parameterized definition; replacing it changes the
addressable statement rather than generalizing one of its binders.
Publishing a generic one-sided declaration here would not serve an additional
named consumer. Over `Real`, the existing public two-sided reduction
`ThreeGap.fract_add_fract_eq` can derive the corresponding one-sided identity
only through a second reduction or integer-shift invariance step; it is not the
same theorem.

The address is `D5/S1/Words/ReturnWords/GoldenPhaseShift`. Before this file, the
current worktree has ten Lean files in `Words/ReturnWords`, so the addition leaves
the bucket at eleven, below the split trigger. The concept belongs here because
two of the three frozen modules containing exact private copies are return-word
modules, and `goldenPhase` is defined in `GoldenOccurrenceGaps` in this bucket.

The three related conditional declarations are not published here. The
subtraction-by-a-natural form is used only by `GoldenGapFirstReturn`; the no-wrap
and wrap forms are used only by `GoldenCubePeriodsSupport` and depend on that
module's displacement case split. None has the repeated-consumer evidence that
justifies this interface file.

The inspected-candidate list is not claimed to be exhaustive.
-/

namespace D5.S1.Words.ReturnWords.GoldenPhaseShift

/-- Shifting a golden mechanical phase shifts its argument before reduction mod one. -/
theorem golden_phase_add (i d : Nat) :
    goldenPhase (i + d) =
      Int.fract (goldenPhase i + (d : Real) * goldenMechanicalSlope) := by
  rw [goldenPhase, goldenPhase]
  have harg : (((i + d + 1 : Nat) : Real) * goldenMechanicalSlope) =
      (((i + 1 : Nat) : Real) * goldenMechanicalSlope) +
        (d : Real) * goldenMechanicalSlope := by
    push_cast
    ring
  rw [harg]
  conv_lhs =>
    enter [1, 1]
    rw [← Int.floor_add_fract (((i + 1 : Nat) : Real) * goldenMechanicalSlope)]
  rw [add_assoc, Int.fract_intCast_add]

#print axioms golden_phase_add

end D5.S1.Words.ReturnWords.GoldenPhaseShift
