import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Invariance

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

namespace EqualRows

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r d : ℕ} (σ μ : Equiv.Perm (Fin (2 * r)))
    (_hrow : rowSet μ = rowSet σ) (ρ : Matrix (Index r d) (Index r d) ℂ),
    R.readout () () (traceNorm (permute μ ρ)) (traceNorm (permute σ ρ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 0 (Equiv.refl _) (Equiv.refl _) rfl 0

def source_registration : Registration arena (type_of% @traceNorm_eq_of_rowSet) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_eq_of_rowSet, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_eq_of_rowSet) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.Invariance.traceNorm_eq_of_rowSet.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Invariance.EqualRows.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
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

end EqualRows

namespace FourSymmetries

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r d : ℕ} (σ μ : Equiv.Perm (Fin (2 * r)))
    (_hrow : rowSet μ = rowSet σ ∨ rowSet μ = (rowSet σ)ᶜ ∨
      rowSet μ = (rowSet σ).map (J r).toEmbedding ∨
      rowSet μ = ((rowSet σ).map (J r).toEmbedding)ᶜ)
    (ρ : Matrix (Index r d) (Index r d) ℂ) (_hρ : IsDensity ρ),
    R.readout () () (traceNorm (permute σ ρ)) (traceNorm (permute μ ρ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ρ : Matrix (Index 0 2) (Index 0 2) ℂ := 1
  have hρ : IsDensity ρ := ⟨Matrix.PosSemidef.one, by simp [ρ, Matrix.trace_one, Index]⟩
  exact @h 0 2 (Equiv.refl _) (Equiv.refl _) (Or.inl rfl) ρ hρ

def source_registration : Registration arena (type_of% @dependent_of_rowSet_orbit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dependent_of_rowSet_orbit, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dependent_of_rowSet_orbit) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.Invariance.dependent_of_rowSet_orbit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Invariance.FourSymmetries.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.Setup
      name := `D5.S3.Quantum.Entanglement.PermutationCriteria.Dependent
      path := #["body", "body", "body", "body", "body"] }
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

end FourSymmetries

end

end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Invariance


namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ P Q => P ↔ Q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r d : ℕ), 1 ≤ r → 2 ≤ d →
    ∀ σ μ : Equiv.Perm (Fin (2 * r)),
      R.readout () () (Dependent r d σ μ)
        (rowSet μ = rowSet σ ∨ rowSet μ = (rowSet σ)ᶜ ∨
          rowSet μ = (rowSet σ).map (J r).toEmbedding ∨
          rowSet μ = ((rowSet σ).map (J r).toEmbedding)ᶜ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 2 (by decide) (by decide) (Equiv.refl _) (Equiv.refl _)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro h
  have hh : False ↔ True := Eq.mp (congrFun h True) Iff.rfl
  exact hh.mpr trivial

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P Q => P ↔ Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
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

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
