import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
open Filter LeanInformationAudit
open scoped Topology

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

@[reducible] def countSignature : Signature.{0, 0, 0, 0, 0} where
  Params := ℝ × ℝ × ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization countSignature :=
  realize countSignature
    (fun _ p rho => FiniteTail.tail (Law.cleanRecordMass rho p.1) Law.nonzero (Scale.sampleLength rho p.1 p.2.1) p.2.2)
    (fun e => nomatch e)

def rejected : Realization countSignature :=
  realize countSignature
    (fun _ p rho => FiniteTail.tail (Law.cleanRecordMass rho p.1) Law.nonzero (Scale.sampleLength rho p.1 p.2.1) p.2.2 + 1)
    (fun e => nomatch e)

def arena : Arena.{0, 0, 0, 0, 0} where
  signature := countSignature
  Law R := ∀ a K : ℝ, 0 < a → a ≤ 1 → 0 < K → ∀ N : ℕ,
    Tendsto (fun rho => R.readout () (a, K, N) rho) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))

theorem actual_law : arena.Law actual := by
  intro a K ha ha1 hK N
  exact Law.nonzero_count_diverges a K ha ha1 hK N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1 (by norm_num) (by norm_num) (by norm_num) 0
  have hgood := Law.nonzero_count_diverges 1 1 (by norm_num) (by norm_num) (by norm_num) 0
  have hshift := hgood.add_const (1 : ℝ)
  have heq : (0 : ℝ) = 0 + 1 := by
    apply tendsto_nhds_unique hbad
    simpa only [rejected, realize, countSignature] using hshift
  norm_num at heq

theorem dependence_proof : ObservationalDependence countSignature actual := by
  intro i
  cases i
  have hgood := Law.nonzero_count_diverges 1 1 (by norm_num) (by norm_num) (by norm_num) 0
  obtain ⟨rho, hrho⟩ := (hgood.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  refine ⟨(1,1,0), 0, rho, ?_⟩
  have hz : FiniteTail.tail (Law.cleanRecordMass 0 1) Law.nonzero
      (Scale.sampleLength 0 1 1) 0 = 1 := by
    have hm : Scale.sampleLength 0 1 1 = 0 := by norm_num [Scale.sampleLength]
    rw [hm]
    simp [FiniteTail.tail, FiniteTail.count]
  change FiniteTail.tail (Law.cleanRecordMass 0 1) Law.nonzero
    (Scale.sampleLength 0 1 1) 0 ≠
    FiniteTail.tail (Law.cleanRecordMass rho 1) Law.nonzero (Scale.sampleLength rho 1 1) 0
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.nonzero_count_diverges)
    (Realization countSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.countLimitUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize countSignature
    (fun _ p rho => FiniteTail.tail (Law.cleanRecordMass rho p.1) Law.nonzero (Scale.sampleLength rho p.1 p.2.1) p.2.2)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none, coordinates := #[0, 1, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "body"],
      stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
