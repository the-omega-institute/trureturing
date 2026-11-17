import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the mixed and Bell witness statements. -/

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Classical ComplexOrder MatrixOrder

noncomputable section

abbrev matrixSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun p => Matrix (Index p.1 p.2) (Index p.1 p.2) ℂ)
    (fun p => Matrix (Index p.1 p.2) (Index p.1 p.2) ℂ → Prop)

def matrixActual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ A B => A = B) (fun e => nomatch e)
def matrixRejected : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev densitySignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun p => Matrix (Index p.1 p.2) (Index p.1 p.2) ℂ) (fun _ => Prop)

def densityActual : Realization densitySignature :=
  realize densitySignature (fun _ _ A => IsDensity A) (fun e => nomatch e)
def densityRejected : Realization densitySignature :=
  realize densitySignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev realSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def realActual : Realization realSignature :=
  realize realSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def realRejected : Realization realSignature :=
  realize realSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev iffSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)
def iffActual : Realization iffSignature :=
  realize iffSignature (fun _ _ P Q => P ↔ Q) (fun e => nomatch e)
def iffRejected : Realization iffSignature :=
  realize iffSignature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace SingleDensity

abbrev arena : Arena where
  signature := densitySignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (i : Fin r),
    R.readout () (r, d) (singleWitness hd i)

private theorem evidence : (¬ arena.Law densityRejected) ∧
    ObservationalDependence densitySignature densityActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) 0
  · intro _
    refine ⟨(1, 2), singleWitness (r := 1) (d := 2) (by decide) 0, 0, ?_⟩
    intro he
    have hp : densityActual.readout () (1, 2)
        (singleWitness (r := 1) (d := 2) (by decide) 0) := singleWitness_isDensity _ _
    have hz : IsDensity (0 : Matrix (Index 1 2) (Index 1 2) ℂ) := Eq.mp he hp
    have ht := hz.2
    norm_num at ht

def source_registration : Registration arena (type_of% @singleWitness_isDensity) where
  actual := densityActual
  bridge := Iff.rfl
  variation := ⟨@singleWitness_isDensity, densityRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law densityActual densityRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singleWitness_isDensity) (Realization densitySignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.singleWitness_isDensity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses.SingleDensity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize densitySignature (fun _ _ A => IsDensity A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end SingleDensity

namespace BellDensity

abbrev arena : Arena where
  signature := densitySignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (i j : Fin r),
    R.readout () (r, d) (bellWitness hd i j)

private theorem evidence : (¬ arena.Law densityRejected) ∧
    ObservationalDependence densitySignature densityActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) 0 0
  · intro _
    refine ⟨(1, 2), singleWitness (r := 1) (d := 2) (by decide) 0, 0, ?_⟩
    intro he
    have hp : densityActual.readout () (1, 2)
        (singleWitness (r := 1) (d := 2) (by decide) 0) := singleWitness_isDensity _ _
    have hz : IsDensity (0 : Matrix (Index 1 2) (Index 1 2) ℂ) := Eq.mp he hp
    have ht := hz.2
    norm_num at ht

def source_registration : Registration arena (type_of% @bellWitness_isDensity) where
  actual := densityActual
  bridge := Iff.rfl
  variation := ⟨@bellWitness_isDensity, densityRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law densityActual densityRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bellWitness_isDensity) (Realization densitySignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.bellWitness_isDensity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses.BellDensity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize densitySignature (fun _ _ A => IsDensity A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end BellDensity

namespace SingleEntries

abbrev arena : Arena where
  signature := matrixSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (i : Fin r),
    R.readout () (r, d) (singleWitness hd i)
      (Matrix.single (bitPattern hd {i} 0) (bitPattern hd {i} 0) (1 / 2) +
        Matrix.single (bitPattern hd {i} 1) (bitPattern hd {i} 1) (1 / 2))

private theorem evidence : (¬ arena.Law matrixRejected) ∧
    ObservationalDependence matrixSignature matrixActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) 0
  · intro _
    refine ⟨(1, 2), 0, 1, ?_⟩
    intro he
    have hbad : (1 : Matrix (Index 1 2) (Index 1 2) ℂ) = 0 :=
      Eq.mp (congrFun he 0) rfl
    exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @singleWitness_eq) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@singleWitness_eq, matrixRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law matrixActual matrixRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singleWitness_eq) (Realization matrixSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.singleWitness_eq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses.SingleEntries.source_registration
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
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end SingleEntries

namespace BellEntries

abbrev arena : Arena where
  signature := matrixSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (i j : Fin r),
    R.readout () (r, d) (bellWitness hd i j)
      (Matrix.single (bitPattern hd {i, j} 0) (bitPattern hd {i, j} 0) (1 / 2) +
        Matrix.single (bitPattern hd {i, j} 0) (bitPattern hd {i, j} 1) (1 / 2) +
        Matrix.single (bitPattern hd {i, j} 1) (bitPattern hd {i, j} 0) (1 / 2) +
        Matrix.single (bitPattern hd {i, j} 1) (bitPattern hd {i, j} 1) (1 / 2))

private theorem evidence : (¬ arena.Law matrixRejected) ∧
    ObservationalDependence matrixSignature matrixActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) 0 0
  · intro _
    refine ⟨(1, 2), 0, 1, ?_⟩
    intro he
    have hbad : (1 : Matrix (Index 1 2) (Index 1 2) ℂ) = 0 :=
      Eq.mp (congrFun he 0) rfl
    exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @bellWitness_eq) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@bellWitness_eq, matrixRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law matrixActual matrixRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bellWitness_eq) (Realization matrixSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.bellWitness_eq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses.BellEntries.source_registration
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
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end BellEntries

namespace SingleNorm

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) (σ : Equiv.Perm (Fin (2 * r))) (i : Fin r),
    R.readout () () (traceNorm (permute σ (singleWitness hd i)))
      (if LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet σ) i)
        then Real.sqrt (1 / 2) else 1)

private theorem evidence : (¬ arena.Law realRejected) ∧
    ObservationalDependence realSignature realActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) (Equiv.refl _) 0
  · intro _
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def source_registration : Registration arena (type_of% @singleWitness_traceNorm) where
  actual := realActual
  bridge := Iff.rfl
  variation := ⟨@singleWitness_traceNorm, realRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realActual realRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singleWitness_traceNorm) (Realization realSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.singleWitness_traceNorm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses.SingleNorm.source_registration
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
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end SingleNorm

namespace SameSide

abbrev arena : Arena where
  signature := iffSignature
  Law R := ∀ {r d : ℕ} (hd : 2 ≤ d) {σ μ : Equiv.Perm (Fin (2 * r))}
    (_h : Dependent r d σ μ) (i : Fin r),
    R.readout () () (LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet σ) i))
      (LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet μ) i))

private theorem evidence : (¬ arena.Law iffRejected) ∧
    ObservationalDependence iffSignature iffActual := by
  constructor
  · intro h
    exact @h 1 2 (by decide) (Equiv.refl _) (Equiv.refl _)
      (by intro ρ hρ; rfl) 0
  · intro _
    refine ⟨(), True, False, ?_⟩
    intro he
    have hbad : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
    exact hbad.mpr trivial

def source_registration : Registration arena (type_of% @dependent_sameSide) where
  actual := iffActual
  bridge := Iff.rfl
  variation := ⟨@dependent_sameSide, iffRejected, evidence.1⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law iffActual iffRejected evidence.1
  dependence := evidence.2

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dependent_sameSide) (Realization iffSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.dependent_sameSide.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses.SameSide.source_registration
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
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end SameSide

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
