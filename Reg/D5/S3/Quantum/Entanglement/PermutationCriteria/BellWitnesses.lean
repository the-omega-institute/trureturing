import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses
import Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses

/-! Source-bound coordinate, matrix, and norm observations of the Bell witnesses. -/

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
open Matrix
open scoped Classical ComplexOrder MatrixOrder

noncomputable section

abbrev natSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def natActual : Realization natSignature :=
  realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace CoordinateKernel

abbrev arena : Arena where
  signature := iffSignature
  Law R := ∀ {r d : ℕ} (side : Bool) (σ : Equiv.Perm (Fin (2 * r))) (hd : 2 ≤ d)
    (S : Finset (Fin r)) (t u : Fin 2 × Fin 2),
    R.readout () () (sideImage side σ hd S t = sideImage side σ hd S u)
      (((∃ i ∈ S, sideSelected side (σ (ketPos i))) → t.1 = u.1) ∧
        ((∃ i ∈ S, sideSelected side (σ (braPos i))) → t.2 = u.2))

private theorem evidence : (¬ arena.Law iffRejected) ∧
    ObservationalDependence iffSignature iffActual := by
  constructor
  · intro h
    exact @h 1 2 false (Equiv.refl _) (by decide) ∅ (0, 0) (0, 0)
  · intro _
    refine ⟨(), True, False, ?_⟩
    intro he
    have hbad : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
    exact hbad.mpr trivial

def source_registration : Registration arena (type_of% @sideImage_kernel) where
  actual := iffActual
  bridge := Iff.rfl
  variation := ⟨@sideImage_kernel, iffRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law iffActual iffRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sideImage_kernel) (Realization iffSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.sideImage_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses.CoordinateKernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize iffSignature (fun _ _ P Q => P ↔ Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end CoordinateKernel

namespace PermutedEntries

abbrev arena : Arena where
  signature := matrixSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (σ : Equiv.Perm (Fin (2 * r))) (i j : Fin r),
    R.readout () (r, d) (permute σ (bellWitness hd i j))
      (BellBlocks.fourEntries (sideImage true σ hd {i, j}) (sideImage false σ hd {i, j}))

private theorem evidence : (¬ arena.Law matrixRejected) ∧
    ObservationalDependence matrixSignature matrixActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) (Equiv.refl _) 0 0
  · intro _
    refine ⟨(1, 2), 0, 1, ?_⟩
    intro he
    have hbad : (1 : Matrix (Index 1 2) (Index 1 2) ℂ) = 0 :=
      Eq.mp (congrFun he 0) rfl
    exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @permute_bellWitness) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@permute_bellWitness, matrixRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law matrixActual matrixRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@permute_bellWitness) (Realization matrixSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.permute_bellWitness.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses.PermutedEntries.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ _ A B => A = B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end PermutedEntries

namespace BellNorm

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (σ : Equiv.Perm (Fin (2 * r))) (i j : Fin r),
    R.readout () () (traceNorm (permute σ (bellWitness hd i j)))
      (BellBlocks.bellValue
        (LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet σ) i)
          (RowSetRecovery.rowLabels (rowSet σ) j)))

private theorem evidence : (¬ arena.Law realRejected) ∧
    ObservationalDependence realSignature realActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) (Equiv.refl _) 0 0
  · intro _
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def source_registration : Registration arena (type_of% @bellWitness_traceNorm) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨@bellWitness_traceNorm, realRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realActual realRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bellWitness_traceNorm) (Realization realSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.bellWitness_traceNorm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses.BellNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end BellNorm

namespace PairDistance

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) {σ μ : Equiv.Perm (Fin (2 * r))}
    (_h : Dependent r d σ μ) (i j : Fin r),
    R.readout () ()
      (LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet σ) i)
        (RowSetRecovery.rowLabels (rowSet σ) j))
      (LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet μ) i)
        (RowSetRecovery.rowLabels (rowSet μ) j))

private theorem evidence : (¬ arena.Law natRejected) ∧
    ObservationalDependence natSignature natActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) (Equiv.refl _) (Equiv.refl _)
      (by intro ρ hρ; rfl) 0 0
  · intro _
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    intro he
    have hbad : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def source_registration : Registration arena (type_of% @dependent_pairDistance) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@dependent_pairDistance, natRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dependent_pairDistance) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.dependent_pairDistance.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses.PairDistance.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end PairDistance

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses
