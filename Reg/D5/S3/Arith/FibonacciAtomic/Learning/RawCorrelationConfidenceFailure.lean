import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
open _root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
open Filter LeanInformationAudit
open scoped Topology

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure

@[reducible] def rawSignature : Signature where
  Params := ℝ × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization rawSignature :=
  realize rawSignature
    (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2))
    (fun e => nomatch e)

def rejected : Realization rawSignature :=
  realize rawSignature
    (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := rawSignature
  Law R := ∀ a K : ℝ, 0 < a → a ≤ 1 → 0 < K →
    Tendsto (fun rho => R.readout () (a, K) rho) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ))

theorem actual_law : arena.Law actual := by
  intro a K ha ha1 hK
  exact RawLimit.raw_confidence_failure a K ha ha1 hK

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hgood := RawLimit.raw_confidence_failure 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hshift := hgood.add_const (1 : ℝ)
  have heq : (1 / 2 : ℝ) = 1 / 2 + 1 := by
    apply tendsto_nhds_unique hbad
    simpa only [rejected, realize, rawSignature] using hshift
  norm_num at heq

theorem dependence_proof : ObservationalDependence rawSignature actual := by
  intro i
  cases i
  have hgood := RawLimit.raw_confidence_failure 1 1 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨rho, hrho⟩ := (hgood.eventually
    (lt_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))).exists
  refine ⟨(1,1), 0, rho, ?_⟩
  have hz : Law.misorder 0 1 (Scale.sampleLength 0 1 1) = 0 := by
    simp [Scale.sampleLength, Law.misorder]
  change Law.misorder 0 1 (Scale.sampleLength 0 1 1) ≠ _
  rw [hz]
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.RawLimit.raw_confidence_failure)
    (type_of% (realize rawSignature
      (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.rawLimitUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rawSignature
    (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure,
    definition := none, coordinates := #[0, 1],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "fn", "arg", "body"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
