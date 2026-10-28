import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.PostLie.AriProjection
import Reg.Support.SingleDependentReadout

/-! Source-bound observation families for the original finite ari statements. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S1.Words.PostLie.AriProjection
open _root_.D5.S1.Words.PostLie.AriWordOperations
open _root_.D5.S1.Words.PostLie.AriProjection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev projectionSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => H) (fun _ => Polynomial ℚ)
def projectionActual : Realization projectionSignature :=
  realize projectionSignature (fun _ k p => pureProjection k p) (fun e => nomatch e)
def projectionRejected : Realization projectionSignature :=
  realize projectionSignature (fun _ _ _ => 1) (fun e => nomatch e)

def projectionCoeffArena : Arena where
  signature := projectionSignature
  Law R := ∀ (k d : ℕ) (p : H), (R.readout () k p).coeff d = p.coeff (FreeMonoid.ofList (List.replicate d k))

private theorem projectionCoeff_rejected : ¬ projectionCoeffArena.Law projectionRejected := by
  intro h
  have hc := h 0 0 0
  change (1 : Polynomial ℚ).coeff 0 = (0 : H).coeff 1 at hc
  norm_num at hc

def projectionCoeffFamily : Registration projectionCoeffArena (∀ (k d : ℕ) (p : H), (pureProjection k p).coeff d = p.coeff (FreeMonoid.ofList (List.replicate d k))) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨pureProjection_coeff, projectionRejected, projectionCoeff_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ projectionCoeff_rejected
  dependence := by
    change ObservationalDependence projectionSignature projectionActual
    intro i
    refine ⟨0, (0 : H), letter 0, ?_⟩
    change pureProjection 0 (0 : H) ≠ pureProjection 0 (letter 0)
    intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
    simp only [pureProjection_coeff] at hc
    norm_num [letter, wordBasis] at hc

def projectionCoeffAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriProjection.pureProjection_coeff) (Realization projectionSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriProjection.projectionCoeffUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriProjection.projectionCoeffFamily
  realizationSource := none
  generated := false
  arena := .source ⟨projectionCoeffArena⟩
  objectArena := .source ⟨projectionCoeffArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionCoeffArena ⟨projectionCoeffFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ k p => pureProjection k p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def projectionCommutatorArena : Arena where
  signature := projectionSignature
  Law R := ∀ (k : ℕ) (p q : H), R.readout () k (commutator p q) = 0

private theorem projectionCommutator_rejected : ¬ projectionCommutatorArena.Law projectionRejected := by
  intro h
  have hc := h 0 0 0
  change (1 : Polynomial ℚ) = 0 at hc
  exact one_ne_zero hc

def projectionCommutatorFamily : Registration projectionCommutatorArena (∀ (k : ℕ) (p q : H), pureProjection k (commutator p q) = 0) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨pureProjection_commutator, projectionRejected, projectionCommutator_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ projectionCommutator_rejected
  dependence := by
    change ObservationalDependence projectionSignature projectionActual
    intro i
    refine ⟨0, (0 : H), letter 0, ?_⟩
    change pureProjection 0 (0 : H) ≠ pureProjection 0 (letter 0)
    intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
    simp only [pureProjection_coeff] at hc
    norm_num [letter, wordBasis] at hc

def projectionCommutatorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriProjection.pureProjection_commutator) (Realization projectionSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriProjection.projectionCommutatorUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriProjection.projectionCommutatorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨projectionCommutatorArena⟩
  objectArena := .source ⟨projectionCommutatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionCommutatorArena ⟨projectionCommutatorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ k p => pureProjection k p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def actionProjectionArena : Arena where
  signature := projectionSignature
  Law R := ∀ (k : ℕ) (A : Word) (s : ℕ), A ≠ 1 → R.readout () k (letterAction A s) = 0

private theorem actionProjection_rejected : ¬ actionProjectionArena.Law projectionRejected := by
  intro h
  have ha : FreeMonoid.of (0 : ℕ) ≠ 1 := by simp
  have hc := h 0 (FreeMonoid.of 0) 0 ha
  change (1 : Polynomial ℚ) = 0 at hc
  exact one_ne_zero hc

def actionProjectionFamily : Registration actionProjectionArena (∀ (k : ℕ) (A : Word) (s : ℕ), A ≠ 1 → pureProjection k (letterAction A s) = 0) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨letterAction_projection, projectionRejected, actionProjection_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ actionProjection_rejected
  dependence := by
    change ObservationalDependence projectionSignature projectionActual
    intro i
    refine ⟨0, (0 : H), letter 0, ?_⟩
    change pureProjection 0 (0 : H) ≠ pureProjection 0 (letter 0)
    intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
    simp only [pureProjection_coeff] at hc
    norm_num [letter, wordBasis] at hc

def actionProjectionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriProjection.letterAction_projection) (Realization projectionSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriProjection.actionProjectionUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriProjection.actionProjectionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨actionProjectionArena⟩
  objectArena := .source ⟨actionProjectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actionProjectionArena ⟨actionProjectionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ k p => pureProjection k p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriProjection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev actionSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Word (fun _ => ℕ) (fun _ => H)
def actionActual : Realization actionSignature :=
  realize actionSignature (fun _ A s => letterAction A s) (fun e => nomatch e)
def actionRejected : Realization actionSignature :=
  realize actionSignature (fun _ _ _ => wordBasis (1 : Word)) (fun e => nomatch e)

def actionAboveArena : Arena where
  signature := actionSignature
  Law R := ∀ (k : ℕ) (A : Word) (s : ℕ), R.readout () A s ∈ above k (level k (FreeMonoid.of s))

private theorem actionAbove_rejected : ¬ actionAboveArena.Law actionRejected := by
  intro h
  have hb := h 0 1 1
  change wordBasis (1 : Word) ∈ above 0 (level 0 (FreeMonoid.of 1)) at hb
  have hc := hb 1 (by simp [wordBasis])
  change level 0 (FreeMonoid.of 1) ≤ level 0 (1 : Word) at hc
  simp at hc

def actionAboveFamily : Registration actionAboveArena (∀ (k : ℕ) (A : Word) (s : ℕ), letterAction A s ∈ above k (level k (FreeMonoid.of s))) where
  actual := actionActual
  bridge := Iff.rfl
  variation := ⟨letterAction_above, actionRejected, actionAbove_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ actionAbove_rejected
  dependence := by
    change ObservationalDependence actionSignature actionActual
    intro i
    refine ⟨(1 : Word), (0 : ℕ), (1 : ℕ), ?_⟩
    change letterAction 1 0 ≠ letterAction 1 1
    simp only [letterAction, ite_true, letter]
    intro h
    have hw := FreeMonoid.of_injective (wordBasis.injective h)
    omega

def actionAboveAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriProjection.letterAction_above) (Realization actionSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriProjection.actionAboveUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriProjection.actionAboveFamily
  realizationSource := none
  generated := false
  arena := .source ⟨actionAboveArena⟩
  objectArena := .source ⟨actionAboveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actionAboveArena ⟨actionAboveFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize actionSignature (fun _ A s => letterAction A s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriProjection
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.PostLie.AriProjection
