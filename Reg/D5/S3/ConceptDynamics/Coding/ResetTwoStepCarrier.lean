import D5.S3.ConceptDynamics.Coding.ResetTwoStepCarrier
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic
noncomputable section

abbrev squareSignature : Signature where
  Params := ℕ
  State _ := MonoidAlgebra ℕ Sign
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def squareActual : Realization squareSignature :=
  realize squareSignature (fun _ _ v => v.coeff (1 : Sign)) (fun e => nomatch e)

def squareRejected : Realization squareSignature :=
  realize squareSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev squareArena : Arena where
  signature := squareSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    r.readout () q ((twoStepMatrix q) (origin hq) (origin hq)) = 1

private theorem square_actual_law : squareArena.Law squareActual := by
  intro q hq
  simpa [squareActual, realize] using twoStep_origin_square_coeff q hq

private theorem square_rejected_law : ¬ squareArena.Law squareRejected := by
  intro h
  have hz := h 1 (by decide)
  norm_num [squareRejected, realize] at hz

def squareRegistration : Registration squareArena (squareArena.Law squareActual) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨square_actual_law, squareRejected, square_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨squareRejected, ?_, rfl, square_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, MonoidAlgebra.single (1 : Sign) (1 : ℕ), 0, ?_⟩
    norm_num [squareActual, realize, MonoidAlgebra.coeff_single]

noncomputable def registration_square : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.twoStep_origin_square_coeff)
    (Realization squareSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.square_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.squareRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena⟩
  objectArena := .source ⟨squareArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena ⟨squareRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize squareSignature
    (fun _ _ v => v.coeff (1 : Sign)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev carrierSignature : Signature where
  Params := ℕ
  State _ := MonoidAlgebra ℕ Sign
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def carrierActual : Realization carrierSignature :=
  realize carrierSignature (fun _ _ v => v.coeff (1 : Sign)) (fun e => nomatch e)

def carrierRejected : Realization carrierSignature :=
  realize carrierSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev carrierArena : Arena where
  signature := carrierSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    r.readout () q ((twoStepCarrier q) (origin hq) (origin hq)) = 2

private theorem carrier_actual_law : carrierArena.Law carrierActual := by
  intro q hq
  simpa [carrierActual, realize] using twoStep_origin_coeff q hq

private theorem carrier_rejected_law : ¬ carrierArena.Law carrierRejected := by
  intro h
  have hz := h 1 (by decide)
  norm_num [carrierRejected, realize] at hz

def carrierRegistration : Registration carrierArena (carrierArena.Law carrierActual) where
  actual := carrierActual
  bridge := Iff.rfl
  variation := ⟨carrier_actual_law, carrierRejected, carrier_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨carrierRejected, ?_, rfl, carrier_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, MonoidAlgebra.single (1 : Sign) (1 : ℕ), 0, ?_⟩
    norm_num [carrierActual, realize, MonoidAlgebra.coeff_single]

noncomputable def registration_carrier : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.twoStep_origin_coeff)
    (Realization carrierSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.carrier_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.carrierRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨carrierArena⟩
  objectArena := .source ⟨carrierArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source carrierArena ⟨carrierRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize carrierSignature
    (fun _ _ v => v.coeff (1 : Sign)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic
