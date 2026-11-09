import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
open _root_.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
open _root_.D5.S3.Quantum.FiniteDimensional (bornProbability)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
universe u

namespace Accretive
/-- Observe the dimension coefficient at its exact scalar operand. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ c => c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
/-- Retain all index types, instance dictionaries and both matrix operands. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ), A.PosSemidef → B.IsHermitian →
    A ≤ R.readout () () (Fintype.card ι : ℝ) • CFC.abs (A + Complex.I • B)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} (Fin 1)) inferInstance inferInstance 1 0
    PosSemidef.one isHermitian_zero
  have hz : (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) ≤ 0 := by
    simpa [rejected, realize] using hb
  have hd := (Matrix.le_iff.mp hz).diag_nonneg (i := ULift.up 0)
  norm_num at hd
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena.{u} (type_of% @accretive_le_card_abs.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@accretive_le_card_abs.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@accretive_le_card_abs.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound.Accretive.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound.Accretive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Accretive

namespace Boundedness
/-- Observe the exact quotient set as the unnormalized density varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun _ => Set ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ rho => quotientValues rho) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
/-- Retain every original conjunct around the selected quotient-set occurrence. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 1 ≤ n → ∃ (C : ℝ), 0 ≤ C ∧
    ∀ (rho : Matrix (Fin n) (Fin n) ℂ), rho.PosDef →
      (R.readout () n rho).Nonempty ∧
      IsLUB (quotientValues rho) (a rho) ∧ a rho ≤ C
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, hrest⟩ := h 1 le_rfl
  exact (hrest 1 PosDef.one).1.ne_empty rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change quotientValues (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠ quotientValues 1
  have h1 : (1 : ℝ) ∈ quotientValues (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    refine ⟨1, 0, PosSemidef.one, isHermitian_zero, by simp, ?_⟩
    norm_num [bornProbability, Matrix.trace, Fin.sum_univ_one]
  intro h
  have hz : (1 : ℝ) ∈ quotientValues (0 : Matrix (Fin 1) (Fin 1) ℂ) := h.symm ▸ h1
  obtain ⟨A, B, hA, hB, hne, he⟩ := hz
  norm_num [bornProbability] at he

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound.Boundedness.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound.Boundedness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => quotientValues rho) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
    definition := some {
      owner := `D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
      name := `D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Boundedness
end
end Reg.D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
