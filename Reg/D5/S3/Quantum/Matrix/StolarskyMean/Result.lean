import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.StolarskyMean.Result

/-! Mean matrix source families and the full conjecture. -/

noncomputable section
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.Defs
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.Spectral
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.StolarskyMean.Result

private theorem not_conditionallyNegative_one :
    ¬ ConditionallyNegative (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have hh := h ![1, -1] (by simp)
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.one_apply] at hh

namespace Stolarsky
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℕ)
    (fun p => Fin p.2 → ℝ) (fun p => Matrix (Fin p.2) (Fin p.2) ℝ)

def actual : Realization signature :=
  realize signature (fun _ p a => stolarskyMatrix p.1 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {γ : ℝ}, 2 ≤ γ → ∀ {n : ℕ} (a : Fin n → ℝ),
    (∀ i, 0 < a i) → ConditionallyNegative (R.readout () ⟨γ, n⟩ a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact not_conditionallyNegative_one (@h 2 (by norm_num) 2 (fun _ => 1) (by simp))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, (fun _ => 1), (fun _ => 2), ?_⟩
  intro he
  have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) he
  norm_num [actual, realize, stolarskyMatrix, stolarsky] at hh

def family : Registration arena (type_of% @conditionallyNegative_stolarsky) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conditionallyNegative_stolarsky, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conditionallyNegative_stolarsky) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Result.Stolarsky.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Result.Stolarsky.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => stolarskyMatrix p.1 a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.Result
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Stolarsky

namespace ClassA
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℕ)
    (fun p => Fin (p.2 + 1) → ℝ)
    (fun p => Matrix (Fin (p.2 + 1)) (Fin (p.2 + 1)) ℝ)

def actual : Realization signature :=
  realize signature (fun _ p a => stolarskyMatrix p.1 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {γ : ℝ}, 2 ≤ γ → ∀ {n : ℕ} (a : Fin (n + 1) → ℝ),
    (∀ i, 0 < a i) → InClassA (R.readout () ⟨γ, n⟩ a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (@h 2 (by norm_num) 0 (fun _ => 1) (by simp)).1 0 0
  change (0 : ℝ) < 0 at hh
  exact (lt_irrefl 0) hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 0⟩, (fun _ => 1), (fun _ => 2), ?_⟩
  intro he
  have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) he
  norm_num [actual, realize, stolarskyMatrix, stolarsky] at hh

def family : Registration arena (type_of% @inClassA_stolarsky) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inClassA_stolarsky, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inClassA_stolarsky) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Result.ClassA.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Result.ClassA.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => stolarskyMatrix p.1 a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.Result
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ClassA


end Reg.D5.S3.Quantum.Matrix.StolarskyMean.Result
