import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CommutingFidelityMoments
import Reg.Support.SingleDependentReadout

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Matrix.CommutingFidelityMoments
open _root_.D5.S3.Quantum.Matrix.CommutingFidelityMoments
open _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory
open scoped ComplexOrder MatrixOrder

abbrev realPartSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def realPartActual : Realization realPartSignature := realize realPartSignature
  (fun _ _ z => z.re) (fun e => nomatch e)

def realPartRejected : Realization realPartSignature := realize realPartSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev integrableArena : Arena where
  signature := realPartSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ),
    A.PosSemidef → B.PosSemidef → Commute A B → ∀ {j : ℕ}, 1 ≤ j →
    IntegrableOn (fun s => R.readout () () (Matrix.trace (sandwich A B s ^ j))) (Ioi 0)

private theorem not_integrable_one : ¬ IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) := by
  simp [integrableOn_const_iff]

private theorem integrable_rejected : ¬ integrableArena.{u}.Law realPartRejected := by
  intro h
  exact not_integrable_one (h (n := ULift.{u} Unit) 0 0
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero (Commute.refl 0)
    (j := 1) (by norm_num))

private theorem realPart_dependence : ObservationalDependence realPartSignature realPartActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [realPartActual, realize]

def integrabilityFamily : Registration integrableArena.{u} (type_of% @integrable_moment.{u}) where
  actual := realPartActual
  bridge := Iff.rfl
  variation := ⟨@integrable_moment, realPartRejected, integrable_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrableArena.Law realPartActual realPartRejected integrable_rejected
  dependence := realPart_dependence

def integrabilityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_moment.{u}) (Realization realPartSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CommutingFidelityMoments.integrabilityUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CommutingFidelityMoments.integrabilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrableArena⟩
  objectArena := .source ⟨integrableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrableArena ⟨integrabilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realPartSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CommutingFidelityMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms integrabilityFamily
#print axioms integrabilityRegistration

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature := realize signature
  (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ),
    A.PosSemidef → B.PosSemidef → A ≠ 0 → B ≠ 0 → Commute A B →
    ∀ {j : ℕ}, 1 ≤ j →
    R.readout () () (scalarMoment j (Matrix.trace A).re (Matrix.trace B).re *
      squaredNormalizedFidelity A B ^ j) (gamma j A B)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let I : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := 1
  exact h I I Matrix.PosSemidef.one Matrix.PosSemidef.one one_ne_zero one_ne_zero
    (Commute.refl I) (j := 1) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  simp [actual, realize] at he

def family : Registration arena.{u} (type_of% @commuting_fidelity_moment.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@commuting_fidelity_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@commuting_fidelity_moment.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CommutingFidelityMoments.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CommutingFidelityMoments.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CommutingFidelityMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Matrix.CommutingFidelityMoments
