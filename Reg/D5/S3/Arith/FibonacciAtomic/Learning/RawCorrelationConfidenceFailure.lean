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

@[reducible] def rawSignature : Signature.{0, 0, 0, 0, 0} where
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

def arena : Arena.{0, 0, 0, 0, 0} where
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
    have hm : Scale.sampleLength 0 1 1 = 0 := by norm_num [Scale.sampleLength]
    rw [hm]
    simp [Law.misorder]
  change Law.misorder 0 1 (Scale.sampleLength 0 1 1) ≠
    Law.misorder rho 1 (Scale.sampleLength rho 1 1)
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.RawLimit.raw_confidence_failure)
    (type_of% (realize.{0,0,0,0,0} rawSignature (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2)) (fun e => nomatch e))) Unit Unit := {
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
  readout := some (realize.{0,0,0,0,0} rawSignature
    (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "arg", "body"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

namespace MainResult
open _root_.D5.S3.Arith.FibonacciAtomic
open Law
open scoped BigOperators

set_option quotPrecheck false in
local notation "trueClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.1, w.2.2.1, w.2.2.2.1])
set_option quotPrecheck false in
local notation "rivalClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.2.1, w.2.2.1, w.2.2.2.1])

def arena : Arena.{0, 0, 0, 0, 0} where
  signature := rawSignature
  Law R := ∀ (a K : ℝ), 0 < a → a ≤ 1 → 0 < K →
    (∀ rho : ℝ, 0 < rho → rho ≤ 1 / 8 →
      HeterogeneousTeacherSeparation.Admissible rho (positionLaw rho) ∧
      (∀ w : Record, difference w =
        (HeterogeneousTeacherSeparation.highIndicator w.1 -
          HeterogeneousTeacherSeparation.highIndicator w.2.1) *
        HeterogeneousTeacherSeparation.lowIndicator w.2.2.1 *
        (1 - 2 * HeterogeneousTeacherSeparation.highIndicator w.2.2.1 *
          HeterogeneousTeacherSeparation.lowIndicator w.2.2.2.1)) ∧
      (expectation rho a (fun w => difference w ^ 2) = 2 * rho * (1 - 5 * rho + 12 * rho ^ 2) ∧
        expectation rho a (fun w => (((trueClass w).val : ℝ) - 1) ^ 2 -
          (((rivalClass w).val : ℝ) - 1) ^ 2) = -2 * rho + 10 * rho ^ 2 ∧
        expectation rho a (fun w => (score w : ℝ)) = 3 * a * rho ^ 3 ∧
        variance rho a = (8 + a) / 12 * (2 * rho * (1 - 5 * rho + 12 * rho ^ 2)) -
          9 * a ^ 2 * rho ^ 6 ∧
        0 < expectation rho a (fun w => (score w : ℝ)))) ∧
    Tendsto (fun rho => R.readout () (a, K) rho)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) ∧
    (∀ select : (rho : ℝ) → (Fin (Scale.sampleLength rho a K) → Record) → Fin 4,
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c,
        Selection.candidateScore c w ≤ Selection.candidateScore (select rho w) w) →
      (1 / 2 : ℝ) ≤ liminf
        (fun rho => Selection.failureMass rho a (Scale.sampleLength rho a K) (select rho))
        (𝓝[>] (0 : ℝ))) ∧
    (∀ q : (rho : ℝ) → (Fin (Scale.sampleLength rho a K) → Record) → Fin 4 → ℝ,
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, 0 ≤ q rho w c) →
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w, ∑ c, q rho w c = 1) →
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, 0 < q rho w c →
        ∀ d, Selection.candidateScore d w ≤ Selection.candidateScore c w) →
      (1 / 2 : ℝ) ≤ liminf
        (fun rho => RandomSelection.failureMass rho a (Scale.sampleLength rho a K) (q rho))
        (𝓝[>] (0 : ℝ)))

theorem actual_law : arena.Law actual := by
  intro a K ha ha1 hK
  exact _root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.result a K ha ha1 hK

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact _root_.Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.rejected_law
    (fun a K ha ha1 hK => (h a K ha ha1 hK).2.1)

def proof_record : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    haveI : Subsingleton arena.signature.Role := inferInstanceAs (Subsingleton Unit)
    exact ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
      rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence_proof

noncomputable def registration_result : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.result)
    (type_of% (realize.{0,0,0,0,0} rawSignature (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.resultUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.MainResult.proof_record,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} rawSignature
    (fun _ p rho => Law.misorder rho p.1 (Scale.sampleLength rho p.1 p.2))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn", "arg", "body"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


end MainResult

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
