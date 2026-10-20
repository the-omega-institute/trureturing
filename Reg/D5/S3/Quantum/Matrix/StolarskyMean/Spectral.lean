import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.StolarskyMean.Spectral

/-! Spectral source families with matrix observations. -/

noncomputable section
open scoped ComplexOrder
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.Defs
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.Spectral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

namespace Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral

private theorem numPosEig_zero (n : ℕ) :
    numPosEig (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  classical
  have h := Matrix.isHermitian_zero (n := Fin n) (α := ℝ)
  have he := h.eigenvalues_eq_zero_iff.mpr rfl
  simp only [numPosEig, dite_eq_left h]
  simp [he]

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℝ) (fun n => Matrix (Fin n) (Fin n) ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, 0, 1, zero_ne_one⟩

namespace Count
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ},
    M.IsHermitian → ConditionallyNegative M → (∃ i, 0 < M i i) →
      numPosEig (R.readout () n M) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : ConditionallyNegative (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro c hs
    have hz : c = 0 := by
      ext i
      fin_cases i
      simpa using hs
    simp [hz]
  have hh := @h 1 1 Matrix.isHermitian_one hc ⟨0, by simp⟩
  change numPosEig (0 : Matrix (Fin 1) (Fin 1) ℝ) = 1 at hh
  rw [numPosEig_zero] at hh
  omega

def family : Registration arena (type_of% @numPosEig_eq_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨numPosEig_eq_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@numPosEig_eq_one) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral.Count.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral.Count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.Spectral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Count

namespace Plane
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ},
    M.IsHermitian → ∀ {W : Submodule ℝ (Fin n → ℝ)},
    2 ≤ Module.finrank ℝ W → RHLinalg.PosDefOn M W →
      2 ≤ numPosEig (R.readout () n M)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : RHLinalg.PosDefOn (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊤ := by
    intro x _ hx
    simpa [RHLinalg.hermForm] using
      (Matrix.PosDef.one (n := Fin 2) (R := ℝ)).dotProduct_mulVec_pos hx
  have hd : 2 ≤ Module.finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) := by simp
  have hh := @h 2 1 Matrix.isHermitian_one ⊤ hd hp
  change 2 ≤ numPosEig (0 : Matrix (Fin 2) (Fin 2) ℝ) at hh
  rw [numPosEig_zero] at hh
  omega

def family : Registration arena (type_of% @two_le_numPosEig_of_posDefOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_le_numPosEig_of_posDefOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_le_numPosEig_of_posDefOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral.Plane.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral.Plane.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.Spectral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Plane

namespace ClassA
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (fun n => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
    M.IsHermitian → (∀ i j, 0 < M i j) → ConditionallyNegative M →
      InClassA (R.readout () n M)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : ConditionallyNegative (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro c hs
    have hz : c = 0 := by
      ext i
      fin_cases i
      simpa using hs
    simp [hz]
  have hp : ∀ i j : Fin 1, 0 < (1 : Matrix (Fin 1) (Fin 1) ℝ) i j := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num
  have hh := @h 0 1 Matrix.isHermitian_one hp hc
  have hz := hh.1 0 0
  change (0 : ℝ) < 0 at hz
  exact (lt_irrefl 0 hz)

def family : Registration arena (type_of% @inClassA_of_conditionallyNegative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inClassA_of_conditionallyNegative, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨0, 0, 1, zero_ne_one⟩
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inClassA_of_conditionallyNegative) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral.ClassA.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral.ClassA.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.Spectral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ClassA

#print axioms Count.audit
#print axioms Plane.audit
#print axioms ClassA.audit

end Reg.D5.S3.Quantum.Matrix.StolarskyMean.Spectral
