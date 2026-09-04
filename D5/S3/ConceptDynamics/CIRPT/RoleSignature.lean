/- GID: D5/S3/ConceptDynamics/CIRPT/RoleSignature
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CIRPT/RoleSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four-bit signatures partition off-diagonal pairs and recover role counts. -/

import D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/- Library-search audit trail (2026-09-04):
   * Repository searches for `axisOrdinal`, `roleSignature`, signature
     histograms, and generic off-diagonal pair finsets found no existing
     declarations; the CIRPT primitive bundle API is reused directly.
   * This Mathlib pin has no `Finset.any`. Exact hit
     `Finset.fold_op_rel_iff_or`, together with `decide_eq_true_eq` and
     `Bool.and_eq_true_iff`, supplies Boolean reflection for axis separation.
   * Pinned Mathlib exact hits `Finset.card_eq_sum_card_fiberwise` and
     `Finset.sum_card_fiberwise_eq_card_filter` supply the sixteen-class
     partition and the filtered per-role count identity. No counting lemma is
     reproved locally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CIRPT

universe u

/-- Canonical bit coordinate for each CIRPT primitive role. -/
def axisOrdinal : PrimitiveAxis -> Fin 4
  | .cut => 0
  | .flow => 1
  | .admit => 2
  | .anchor => 3

/-- Decode a four-bit coordinate back to its CIRPT primitive role. -/
def axisOfOrdinal (ordinal : Fin 4) : PrimitiveAxis :=
  if ordinal = 0 then .cut
  else if ordinal = 1 then .flow
  else if ordinal = 2 then .admit
  else .anchor

/-- Decoding the canonical coordinate of a role returns that role. -/
@[simp] theorem axisOfOrdinal_axisOrdinal (axis : PrimitiveAxis) :
    axisOfOrdinal (axisOrdinal axis) = axis := by
  cases axis <;> rfl

namespace PrimitiveBundle

/-- Whether some atom on one role axis distinguishes the supplied pair. -/
def separatesOnAxis {X : Type u} (bundle : PrimitiveBundle X)
    (axis : PrimitiveAxis) (left right : X) : Bool :=
  let _ := bundle.indexFintype
  let _ := bundle.indexDecidableEq
  Finset.fold (fun left right => left || right) false
    (fun index =>
      decide ((bundle.atom index).axis = axis) &&
        decide (¬(bundle.atom index).kernel.relation left right)) Finset.univ

/-- Axis separation is true exactly when a role-matching atom distinguishes
the pair. -/
theorem separatesOnAxis_eq_true_iff
    {X : Type u} (bundle : PrimitiveBundle X)
    (axis : PrimitiveAxis) (left right : X) :
    bundle.separatesOnAxis axis left right = true <->
      ∃ index,
        (bundle.atom index).axis = axis ∧
          ¬(bundle.atom index).kernel.relation left right := by
  let _ := bundle.indexFintype
  let _ := bundle.indexDecidableEq
  unfold separatesOnAxis
  have foldCharacterization :=
    Finset.fold_op_rel_iff_or
      (op := fun left right : Bool => left || right)
      (r := fun _ actual : Bool => actual = true)
      (b := false)
      (f := fun index =>
        decide ((bundle.atom index).axis = axis) &&
          decide (¬(bundle.atom index).kernel.relation left right))
      (s := Finset.univ) (c := true) (by
        intro expected leftResult rightResult
        simp)
  simpa only [Bool.false_eq_true, false_or, Finset.mem_univ, true_and,
    Bool.and_eq_true_iff, decide_eq_true_eq] using foldCharacterization

/-- The four Boolean coordinates recording which primitive roles separate a pair. -/
def roleSignature {X : Type u} (bundle : PrimitiveBundle X)
    (left right : X) : Fin 4 -> Bool :=
  fun coordinate =>
    bundle.separatesOnAxis (axisOfOrdinal coordinate) left right

/-- Bundle agreement is equivalent to a zero role signature. -/
theorem agrees_iff_roleSignature_zero
    {X : Type u} (bundle : PrimitiveBundle X) (left right : X) :
    bundle.agrees left right <->
      bundle.roleSignature left right = fun _ => false := by
  constructor
  · intro agrees
    funext coordinate
    apply Bool.eq_false_iff.mpr
    intro separated
    rcases (bundle.separatesOnAxis_eq_true_iff
      (axisOfOrdinal coordinate) left right).1 separated with
      ⟨index, _, notRelated⟩
    exact notRelated (agrees index)
  · intro signatureZero index
    by_contra notRelated
    have separated :
        bundle.roleSignature left right
          (axisOrdinal (bundle.atom index).axis) = true := by
      simp only [roleSignature, axisOfOrdinal_axisOrdinal]
      exact (bundle.separatesOnAxis_eq_true_iff
        (bundle.atom index).axis left right).2 ⟨index, rfl, notRelated⟩
    have zeroAtAxis := congrFun signatureZero
      (axisOrdinal (bundle.atom index).axis)
    rw [separated] at zeroAtAxis
    exact Bool.false_ne_true zeroAtAxis.symm

end PrimitiveBundle

/-- All ordered pairs of distinct elements of a finite type. -/
def offDiagonalPairs (X : Type u) [Fintype X] [DecidableEq X] : Finset (X × X) :=
  Finset.univ.filter fun pair => pair.1 ≠ pair.2

namespace PrimitiveBundle

/-- Off-diagonal pairs separated by at least one atom on a specified role axis. -/
def separationPairsOnAxis
    {X : Type u} [Fintype X] [DecidableEq X]
    (bundle : PrimitiveBundle X) (axis : PrimitiveAxis) : Finset (X × X) :=
  (offDiagonalPairs X).filter fun pair =>
    bundle.separatesOnAxis axis pair.1 pair.2 = true

/-- Exact multiplicity of one four-bit signature among ordered off-diagonal pairs. -/
def signatureHistogram
    {X : Type u} [Fintype X] [DecidableEq X]
    (bundle : PrimitiveBundle X) (signature : Fin 4 -> Bool) : Nat :=
  ((offDiagonalPairs X).filter fun pair =>
    bundle.roleSignature pair.1 pair.2 = signature).card

/-- CIRPT-IE-011: the sixteen role signatures partition all ordered
off-diagonal pairs. -/
theorem four_role_signature_partition
    {X : Type u} [Fintype X] [DecidableEq X]
    (bundle : PrimitiveBundle X) :
    ∑ signature, bundle.signatureHistogram signature =
      (offDiagonalPairs X).card := by
  classical
  simpa only [signatureHistogram] using
    (Finset.card_eq_sum_card_fiberwise
      (s := offDiagonalPairs X)
      (t := Finset.univ)
      (f := fun pair => bundle.roleSignature pair.1 pair.2)
      (by
        intro signature _
        exact Finset.mem_univ _)).symm

/-- Summing histogram classes whose role bit is true recovers exactly the
off-diagonal separation count for that role. -/
theorem signature_histogram_axis_count
    {X : Type u} [Fintype X] [DecidableEq X]
    (bundle : PrimitiveBundle X) (axis : PrimitiveAxis) :
    ∑ signature with signature (axisOrdinal axis) = true,
        bundle.signatureHistogram signature =
      (bundle.separationPairsOnAxis axis).card := by
  classical
  simpa only [signatureHistogram, separationPairsOnAxis, roleSignature,
    axisOfOrdinal_axisOrdinal, Finset.mem_filter, Finset.mem_univ, true_and] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (offDiagonalPairs X)
      (Finset.univ.filter fun signature : Fin 4 -> Bool =>
        signature (axisOrdinal axis) = true)
      (fun pair => bundle.roleSignature pair.1 pair.2))

end PrimitiveBundle

end D5.S3.ConceptDynamics.CIRPT
