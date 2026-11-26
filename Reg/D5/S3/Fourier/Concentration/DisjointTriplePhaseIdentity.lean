import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Ring.ULift
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity

/-! Dependence of the disjoint triple sum on its pair contribution. -/

namespace Reg.D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity
open _root_.Reg.Support

noncomputable section

universe uJ uR

abbrev RingScope := Σ R : Type uR, CommRing R

abbrev signature := UniverseSingleReadout.signature RingScope.{uR}
  (fun p => p.1 × p.1) (fun p => p.1)

def actual : Realization signature.{uR} :=
  realize signature (fun _ p => @pairPolynomial p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature.{uR} :=
  realize signature (fun _ p _ => letI := p.2; (0 : p.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uR}
  Law V := ∀ {J : Type uJ} {R : Type uR} [Fintype J] [DecidableEq J] [CommRing R]
      (x y : J → R) (_ : ∀ j, x j * y j = 1),
    let pairPart := V.readout () ⟨R, inferInstance⟩
    disjointMass (slotWeight x y) =
      pairPart ((Fintype.card J : R), (∑ j, x j) * ∑ j, y j) -
        3 * ((∑ j, x j ^ 2) * (∑ j, y j) ^ 2 + (∑ j, y j ^ 2) * (∑ j, x j) ^ 2)

private theorem rejected_law : ¬ arena.{uJ, uR}.Law rejected := by
  intro law
  have h := law (J := ULift.{uJ} Unit) (R := ULift.{uR} ℤ)
    (fun _ => 1) (fun _ => 1) (by simp)
  simp [disjointMass, rejected, realize] at h
  have hInt := congrArg ULift.down h
  change (6 : ℤ) = 0 at hInt
  norm_num at hInt

private theorem dependence : ObservationalDependence signature.{uR} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{uR} ℤ, inferInstance⟩, (0, 0), (1, 1), ?_⟩
  intro h
  have hInt := congrArg ULift.down h
  change (0 : ℤ) = 6 at hInt
  norm_num at hInt

def evidence : Registration arena.{uJ, uR} (type_of% @disjoint_triple_phase_identity.{uJ, uR}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@disjoint_triple_phase_identity.{uJ, uR}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@disjoint_triple_phase_identity.{uJ, uR}) (Realization signature.{uR}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uJ, uR}⟩
  objectArena := .source ⟨arena.{uJ, uR}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uJ, uR} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity
