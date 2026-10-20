import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨7, 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]

abbrev upperArena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) (hn : 7 ≤ n) (hn13 : n ≤ 13)
    (rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ),
    rho.PosSemidef → rho.trace = 1 → APPT rho →
      O.readout () n rho ≤ purityValue n
private theorem upperRejected_law : ¬ upperArena.Law rejected := by
  intro h
  obtain ⟨_, _, ⟨rho, _, _, hd, ha, _⟩, _⟩ :=
    physical_finite7_maximum 7 (by decide) (by decide)
  have hb := h 7 (by decide) (by decide) rho hd.1 hd.2 ha
  change (1 : ℝ) ≤ purityValue 7 at hb
  norm_num [purityValue] at hb
def upperFamily : Registration upperArena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.physical_purity_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_purity_upper_bound, rejected, upperRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    upperArena.Law actual rejected upperRejected_law
  dependence := actual_dependence

abbrev maximumArena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) (hn : 7 ≤ n) (hn13 : n ≤ 13),
    0 < (((4*n : ℕ) : ℝ) + 2) ∧
    (∀ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      rho.PosSemidef → rho.trace = 1 → APPT rho →
      O.readout () n rho ≤ purityValue n) ∧
    (∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      rho = _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity.normalizedRay
        (Pi.single (basisZero n hn) 1) ∧
      rho = diagonal (fun p : Fin 4 × Fin n =>
        if p = basisZero n hn then (3 / (((4*n : ℕ) : ℂ) + 2) : ℂ)
        else (1 / (((4*n : ℕ) : ℂ) + 2) : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
      (rho * rho).trace.re = purityValue n) ∧
    (physicalPurities n).Nonempty ∧ BddAbove (physicalPurities n) ∧
    sSup (physicalPurities n) = purityValue n
private theorem maximumRejected_law : ¬ maximumArena.Law rejected := by
  intro h
  apply upperRejected_law
  intro n hn hn13
  exact (h n hn hn13).2.1
def maximumFamily : Registration maximumArena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.physical_finite7_maximum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_finite7_maximum, rejected, maximumRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    maximumArena.Law actual rejected maximumRejected_law
  dependence := actual_dependence

/-- The full source telescope is reconstructed with its actual purity readout. -/
def upperAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.physical_purity_upper_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.physical_purity_upper_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.upperFamily
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The full source telescope is reconstructed with its actual purity readout. -/
def maximumAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.physical_finite7_maximum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.physical_finite7_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity.maximumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨maximumArena⟩
  objectArena := .source ⟨maximumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source maximumArena ⟨maximumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms upperFamily
#print axioms maximumFamily
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitFiniteMaximumPurity
