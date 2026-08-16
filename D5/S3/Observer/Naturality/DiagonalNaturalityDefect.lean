/- GID: D5/S3/Observer/Naturality/DiagonalNaturalityDefect
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/DiagonalNaturalityDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The worst diagonal naturality defect is exactly the semiconjugacy defect. -/

import D5.S3.Observer.MetricGeometry.SemiconjugacyComposition
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/- Library-search audit trail (2026-08-16):
   * The repository definition `semiconjugacyDefect` is the exact uniform defect
     used by the source statement and is imported rather than reproved.
   * Loogle found the exact complete-lattice declarations `le_iSup` and
     `iSup_le`; both are applied below.
   * LeanSearch returned HTTP 404 for the full diagonal-naturality query.
   * Pinned-Mathlib and repository searches found no equal or stronger theorem
     identifying the double diagonal supremum with the semiconjugacy defect. -/

namespace D5.S3.Observer.Naturality.DiagonalNaturalityDefect

open D5.S3.Observer.MetricGeometry.SemiconjugacyComposition

/-- Apply a value projection to every entry of an address table. -/
def pointwiseTableProjection
    {A Y Z : Type*} (projection : Y -> Z) (table : A × A -> Y) : A × A -> Z :=
  fun index => projection (table index)

/-- Apply a value projection to every coordinate of an output vector. -/
def pointwiseOutputProjection
    {A Y Z : Type*} (projection : Y -> Z) (output : A -> Y) : A -> Z :=
  fun address => projection (output address)

/-- Read a table on its diagonal and then apply the supplied update. -/
def diagonalUpdate
    {A Y : Type*} (update : Y -> Y) (table : A × A -> Y) : A -> Y :=
  fun address => update (table (address, address))

/-- Every diagonal naturality defect is bounded by the uniform semiconjugacy
defect, and the supremum over all tables and addresses attains that defect. -/
theorem diagonal_naturality_defect_eq_semiconjugacy_defect
    {A Y Z : Type*} [Nonempty A] [Finite Y] [PseudoEMetricSpace Z]
    (tau : Y -> Y) (sigma : Z -> Z) (projection : Y -> Z) :
    (forall (table : A × A -> Y) (address : A),
      edist
          (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
          (diagonalUpdate sigma (pointwiseTableProjection projection table) address) <=
        semiconjugacyDefect tau sigma projection) ∧
      (⨆ table : A × A -> Y, ⨆ address : A,
        edist
          (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
          (diagonalUpdate sigma (pointwiseTableProjection projection table) address)) =
        semiconjugacyDefect tau sigma projection := by
  constructor
  · intro table address
    exact le_iSup
      (fun y : Y => edist (projection (tau y)) (sigma (projection y)))
      (table (address, address))
  · apply le_antisymm
    · apply iSup_le
      intro table
      apply iSup_le
      intro address
      exact le_iSup
        (fun y : Y => edist (projection (tau y)) (sigma (projection y)))
        (table (address, address))
    · unfold semiconjugacyDefect
      apply iSup_le
      intro y
      let address : A := Classical.choice (inferInstance : Nonempty A)
      let table : A × A -> Y := fun _ => y
      calc
        edist (projection (tau y)) (sigma (projection y)) =
            edist
              (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
              (diagonalUpdate sigma (pointwiseTableProjection projection table) address) := by
          rfl
        _ <= ⨆ address : A,
            edist
              (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
              (diagonalUpdate sigma (pointwiseTableProjection projection table) address) :=
          le_iSup (fun address : A =>
            edist
              (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
              (diagonalUpdate sigma (pointwiseTableProjection projection table) address)) address
        _ <= ⨆ table : A × A -> Y, ⨆ address : A,
            edist
              (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
              (diagonalUpdate sigma (pointwiseTableProjection projection table) address) :=
          le_iSup (fun table : A × A -> Y => ⨆ address : A,
            edist
              (pointwiseOutputProjection projection (diagonalUpdate tau table) address)
              (diagonalUpdate sigma (pointwiseTableProjection projection table) address)) table

/-- The hypotheses are inhabited by a one-address, one-state system with
real-valued observations. -/
example : True := by
  have _witness :=
    diagonal_naturality_defect_eq_semiconjugacy_defect
      (A := Unit) (Y := Unit) (Z := Real)
      id id (fun _ => 0)
  exact True.intro

#print axioms diagonal_naturality_defect_eq_semiconjugacy_defect

end D5.S3.Observer.Naturality.DiagonalNaturalityDefect
