import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.Partitions.BilgiciThetaQuartic

/-! The quotient class of a candidate cofactor is the readout. -/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Partitions.BilgiciThetaQuartic

open _root_.D5.S3.Arith.Partitions.BilgiciThetaQuartic
open _root_.D5.S3.ConceptDynamics.InformationEscape
open MvPolynomial

private abbrev R := MvPolynomial (Fin 9) (ZMod 19)
private abbrev ThetaQuotient := R ⧸ ITheta

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ThetaQuotient
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ q => Ideal.Quotient.mk ITheta q) (fun e => nomatch e)

noncomputable def arena : DependentFamily.Arena where
  signature := signature
  Law := fun readout =>
    ∃ q : R,
      q ≠ 0 ∧ q.IsHomogeneous 4 ∧ q.IsWeightedHomogeneous w (9 : ZMod 19) ∧
      (weightedHomogeneousComponent w (11 : ZMod 19) (paperB * paperC ^ 3) - S_Z * q
        ∈ Ideal.span (Set.range theta)) ∧ (show ThetaQuotient from readout.readout () () q) ≠ 0

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

noncomputable def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ThetaQuotient)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  rintro ⟨_, _, _, _, _, h⟩
  exact h rfl

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    obtain ⟨q, _, _, _, _, hq⟩ := result
    refine ⟨(), q, (0 : R), ?_⟩
    change Ideal.Quotient.mk ITheta q ≠ Ideal.Quotient.mk ITheta 0
    rwa [map_zero]

/-- Replacing the actual quotient map by zero destroys the existence of a surviving cofactor. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@result) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Partitions.BilgiciThetaQuartic.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Partitions.BilgiciThetaQuartic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ q => Ideal.Quotient.mk ITheta q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Partitions.BilgiciThetaQuartic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Partitions.BilgiciThetaQuartic
