import D5.S3.VertexAlgebra.BcGhostVacuum
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostVacuum

namespace Reg.D5.S3.VertexAlgebra.BcGhostVacuum

noncomputable section

universe u

private theorem negativeVacuum_distinct :
    L (K := ULift.{u} ℤ) (-1) vacuum ≠ L (-2) vacuum := by
  intro equality
  have observation := congrArg
    (fun state : Fock (ULift.{u} ℤ) => (L 2 state) ∅) equality
  rw [L_vacuum_annihilation (K := ULift.{u} ℤ) (-1) (by omega), map_zero,
    L_vacuum_contraction (K := ULift.{u} ℤ) 2 (by omega)] at observation
  have integerObservation := congrArg
    (fun value : ULift.{u} ℤ => value.down) observation
  norm_num [vacuum, Finsupp.smul_apply, smul_eq_mul] at integerObservation

namespace Annihilation

structure Parameters where
  K : Type u
  ring : CommRing K

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := letI := parameter.ring; Fock parameter.K
  Anchor := Empty
  finiteAnchor := inferInstance

def sourceRealization : Realization signature.{u} :=
  realize signature (fun _ parameter mode => letI := parameter.ring; L mode vacuum)
    (fun empty => nomatch empty)

def rejected : Realization signature.{u} :=
  realize signature (fun _ parameter _ => letI := parameter.ring; vacuum)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ (K : Type u) (ring : CommRing K), letI := ring
    ∀ (m : ℤ) (_hm : -1 ≤ m),
      readout.readout () (⟨K, ring⟩ : Parameters.{u}) m = 0

def sourceStatement : Prop :=
  ∀ {K : Type u} [CommRing K] (m : ℤ) (_hm : -1 ≤ m),
    L (K := K) m vacuum = 0

private theorem sourceReconstruction :
    sourceStatement.{u} ↔ arena.{u}.Law sourceRealization.{u} := Iff.rfl

private theorem exactTarget : sourceStatement.{u} :=
  @_root_.D5.S3.VertexAlgebra.BcGhostVacuum.L_vacuum_annihilation.{u}

private theorem actualPositive : arena.{u}.Law sourceRealization.{u} :=
  sourceReconstruction.mp exactTarget

private theorem rejectedLaw : ¬ arena.{u}.Law rejected.{u} := by
  intro law
  let K := ULift.{u} ℤ
  have equality := law K inferInstance 0 (by omega)
  change (vacuum : Fock K) = 0 at equality
  have integerObservation := congrArg (fun state : Fock K => (state ∅).down) equality
  norm_num [vacuum] at integerObservation

private theorem variation : Variation arena.{u} sourceRealization.{u} :=
  ⟨actualPositive, rejected, rejectedLaw⟩

private theorem sensitivity : Sensitivity arena.{u} sourceRealization.{u} := by
  constructor
  · intro role
    refine ⟨rejected, ?_, rfl, rejectedLaw⟩
    intro other distinct
    exact (distinct (Subsingleton.elim _ _)).elim
  · intro empty
    exact nomatch empty

#print axioms sourceReconstruction
#print axioms exactTarget
#print axioms variation
#print axioms sensitivity

end Annihilation

namespace Contraction

structure Parameters where
  K : Type u
  ring : CommRing K

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := letI := parameter.ring; Fock parameter.K
  Anchor := Empty
  finiteAnchor := inferInstance

def sourceRealization : Realization signature.{u} :=
  realize signature (fun _ parameter mode => letI := parameter.ring; L (-mode) vacuum)
    (fun empty => nomatch empty)

def rejected : Realization signature.{u} :=
  realize signature (fun _ parameter _ => letI := parameter.ring; 0)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ (K : Type u) (ring : CommRing K), letI := ring
    ∀ (r : ℤ) (_hr : 0 < r),
      L (K := K) r (readout.readout () (⟨K, ring⟩ : Parameters.{u}) r) =
        (((-13 * (r ^ 3 - r) / 6 : ℤ) : K)) • vacuum

def sourceStatement : Prop :=
  ∀ {K : Type u} [CommRing K] (r : ℤ) (_hr : 0 < r),
    L (K := K) r (L (-r) vacuum) =
      (((-13 * (r ^ 3 - r) / 6 : ℤ) : K)) • vacuum

private theorem sourceReconstruction :
    sourceStatement.{u} ↔ arena.{u}.Law sourceRealization.{u} := Iff.rfl

private theorem exactTarget : sourceStatement.{u} :=
  @_root_.D5.S3.VertexAlgebra.BcGhostVacuum.L_vacuum_contraction.{u}

private theorem actualPositive : arena.{u}.Law sourceRealization.{u} :=
  sourceReconstruction.mp exactTarget

private theorem rejectedLaw : ¬ arena.{u}.Law rejected.{u} := by
  intro law
  let K := ULift.{u} ℤ
  have observation := congrArg (fun state : Fock K => state ∅)
    (law K inferInstance 2 (by omega))
  have integerObservation := congrArg
    (fun value : ULift.{u} ℤ => value.down) observation
  norm_num [rejected, realize, vacuum, Finsupp.smul_apply, smul_eq_mul]
    at integerObservation
  change (0 : ℤ) = -13 at integerObservation
  norm_num at integerObservation

private theorem dependence :
    ObservationalDependence signature.{u} sourceRealization.{u} := by
  intro role
  let parameter : Parameters.{u} := ⟨ULift.{u} ℤ, inferInstance⟩
  refine ⟨parameter, 1, 2, ?_⟩
  change L (K := ULift.{u} ℤ) (-1) vacuum ≠ L (-2) vacuum
  exact negativeVacuum_distinct.{u}

def registration : Registration arena.{u} sourceStatement.{u} where
  actual := sourceRealization
  bridge := sourceReconstruction
  variation := ⟨actualPositive, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other distinct
      exact (distinct (Subsingleton.elim _ _)).elim
    · intro empty
      exact nomatch empty
  dependence := dependence

#print axioms sourceReconstruction
#print axioms exactTarget
#print axioms registration

end Contraction

end

end Reg.D5.S3.VertexAlgebra.BcGhostVacuum
