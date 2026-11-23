import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
import Reg.Support.DependentFamily

/-! Source-bound readouts for the fixed-horizon AURIC record. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
open LeanInformationAudit Matrix
open scoped Matrix MatrixGroups

noncomputable section

namespace Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord

private def noOutcome : History 1 := fun _ => false
private def yesOutcome : History 1 := fun _ => true

private theorem distinctReadouts : chronologicalWord noOutcome ≠ chronologicalWord yesOutcome := by
  intro h
  have hv : chronologicalWord noOutcome = letter false := by
    simp [chronologicalWord, noOutcome, List.ofFn_succ, word]
  have hw : chronologicalWord yesOutcome = letter true := by
    simp [chronologicalWord, yesOutcome, List.ofFn_succ, word]
  rw [hv, hw] at h
  have he := congrArg (fun M : Qutrit => (M 0 0).im) h
  change (((Real.cos angle : ℂ) * 1 +
      (Complex.I * (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ)) * 0)).im =
    (((Real.cos angle : ℂ) * 0 +
      (Complex.I * (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ)) * 1)).im at he
  simp [Complex.mul_im] at he
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hz : Real.sqrt 5 = 1 := by linarith
  rw [hz] at hsq
  norm_num at hsq

@[reducible] def fiberSignature : Signature where
  Params := ℕ
  State := History
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Qutrit
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def fiberArena : Arena where
  signature := fiberSignature
  Law R := ∀ {n : ℕ} (v w : History n),
    ((∃ z : ℂ, ‖z‖ = 1 ∧ R.readout () n v = z • chronologicalWord w) ↔
      projectiveWord (List.ofFn v).reverse = projectiveWord (List.ofFn w).reverse) ∧
    (classOf v = classOf w ↔
      projectiveWord (List.ofFn v).reverse = projectiveWord (List.ofFn w).reverse)

def fiberCounterfactual : Realization fiberSignature :=
  realize fiberSignature (fun _ _ _ => 1) (fun i => nomatch i)

private theorem fiberCounterfactual_fails : ¬ fiberArena.Law fiberCounterfactual := by
  intro h
  obtain ⟨z, _, hz⟩ := (h noOutcome noOutcome).1.mpr rfl
  have he := congrArg (fun M : Qutrit => M 1 1) hz
  have hword : chronologicalWord noOutcome = letter false := by
    simp [chronologicalWord, noOutcome, List.ofFn_succ, word]
  rw [hword] at he
  change (1 : Qutrit) 1 1 = z * letter false 1 1 at he
  have zeroEntry : letter false 1 1 = 0 := by
    change (Real.cos angle : ℂ) * 0 +
      (Complex.I * (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ)) * 0 = 0
    simp
  simp [zeroEntry] at he

def fiberFamily : Registration fiberArena (type_of% @chronological_fibers) where
  actual := realize fiberSignature (fun _ _ w => chronologicalWord w) (fun i => nomatch i)
  bridge := Iff.rfl
  variation := ⟨@chronological_fibers, fiberCounterfactual, fiberCounterfactual_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fiberCounterfactual, ?_, rfl, fiberCounterfactual_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨1, noOutcome, yesOutcome, distinctReadouts⟩

def chronologicalFibersRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@chronological_fibers) (Realization fiberSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord.chronological_fibers
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord.fiberFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fiberArena⟩
  objectArena := .source ⟨fiberArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fiberArena ⟨fiberFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fiberSignature (fun _ _ w => chronologicalWord w) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "body", "arg",
        "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe u

open scoped Kronecker
open _root_.D5.S3.Quantum.Measurement.Auric.SimulatorUpper (Level)
open _root_.D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)

private abbrev TraceParams := Σ s : Type u, Σ _ : Fintype s, Σ _ : DecidableEq s, List Bool

@[reducible] def traceSignature : Signature where
  Params := TraceParams.{u}
  State p := Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Level × p.1) (Level × p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def traceObservation (p : TraceParams.{u})
    (ρ : Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ) : Matrix (Level × p.1) (Level × p.1) ℂ :=
  letI := p.2.1
  letI := p.2.2.1
  let embed := code ⊗ₖ (1 : Matrix p.1 p.1 ℂ)
  measuredHistory p.2.2.2 (embed * ρ * embedᴴ)

@[reducible] def traceArena : Arena where
  signature := traceSignature.{u}
  Law R := ∀ {s : Type u} [k : Fintype s] [d : DecidableEq s]
    (w : List Bool) (ρ : Matrix (Fin 3 × s) (Fin 3 × s) ℂ), ρ.trace = 1 →
    let _embed := code ⊗ₖ (1 : Matrix s s ℂ)
    (R.readout () ⟨s, k, d, w⟩ ρ).trace = (1 / 2 : ℂ) ^ w.length

private def traceCounterfactual : Realization traceSignature.{u} :=
  realize traceSignature (fun _ _ _ => 0) (fun i => nomatch i)

private abbrev Sample := ULift.{u} Unit

private def sampleInput (i : Fin 3) : Matrix (Fin 3 × Sample.{u}) (Fin 3 × Sample.{u}) ℂ :=
  Matrix.single (i, ⟨()⟩) (i, ⟨()⟩) 1

private theorem sampleInput_trace (i : Fin 3) : (sampleInput.{u} i).trace = 1 :=
  Matrix.trace_single_eq_same _ _

private theorem traceCounterfactual_fails : ¬ traceArena.{u}.Law traceCounterfactual.{u} := by
  intro h
  have he := h (s := Sample.{u}) [] (sampleInput 2) (sampleInput_trace 2)
  change (0 : Matrix (Level × Sample.{u}) (Level × Sample.{u}) ℂ).trace =
    (1 / 2 : ℂ) ^ ([] : List Bool).length at he
  simp at he

private theorem embedded_single_diagonal {I O : Type*} [Fintype I] [DecidableEq I]
    (B : Matrix O I ℂ) (x : O) (i : I) :
    (B * Matrix.single i i (1 : ℂ) * Bᴴ) x x = B x i * star (B x i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
  · intro j _ hj
    rw [Matrix.mul_single_apply_of_ne (1 : ℂ) i i x j hj B, zero_mul]
  · simp

private theorem normalizedInputs_have_distinct_outputs :
    let B : Matrix (Level × Sample.{u}) (Fin 3 × Sample.{u}) ℂ :=
      code ⊗ₖ (1 : Matrix Sample.{u} Sample.{u} ℂ)
    (B * sampleInput.{u} 2 * Bᴴ : Matrix (Level × Sample.{u}) (Level × Sample.{u}) ℂ) ≠
      B * sampleInput.{u} 0 * Bᴴ := by
  dsimp only
  intro h
  let B : Matrix (Level × Sample.{u}) (Fin 3 × Sample.{u}) ℂ :=
    code ⊗ₖ (1 : Matrix Sample.{u} Sample.{u} ℂ)
  let x : Level × Sample.{u} := (2, ⟨()⟩)
  have he := congrArg (fun M : Matrix (Level × Sample.{u}) (Level × Sample.{u}) ℂ => M x x) h
  change (B * sampleInput.{u} 2 * Bᴴ) x x = (B * sampleInput.{u} 0 * Bᴴ) x x at he
  dsimp only [sampleInput] at he
  rw [embedded_single_diagonal, embedded_single_diagonal] at he
  have h2 : B x (2, ⟨()⟩) = 1 := by simp [B, x, code]
  have h0 : B x (0, ⟨()⟩) = 0 := by simp [B, x, code]
  simp [h2, h0] at he

def traceFamily : Registration traceArena.{u} (type_of% @measuredHistory_trace.{u}) where
  actual := realize traceSignature (fun _ => traceObservation) (fun i => nomatch i)
  bridge := Iff.rfl
  variation := ⟨@measuredHistory_trace.{u}, traceCounterfactual, traceCounterfactual_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨traceCounterfactual, ?_, rfl, traceCounterfactual_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, traceSignature]
    intro i
    let p : TraceParams.{u} := ⟨Sample.{u}, inferInstanceAs (Fintype (ULift.{u} Unit)),
      inferInstanceAs (DecidableEq (ULift.{u} Unit)), []⟩
    let last : Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ := sampleInput.{u} 2
    let first : Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ := sampleInput.{u} 0
    refine ⟨p, last, first, ?_⟩
    exact normalizedInputs_have_distinct_outputs.{u}

def measuredHistoryTraceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@measuredHistory_trace.{u}) (Realization traceSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord.measuredHistory_trace
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord.traceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena.{u}⟩
  objectArena := .source ⟨traceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena.{u} ⟨traceFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature.{u} (fun _ => traceObservation) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev LawParams := Σ s : Type u, Σ _ : Fintype s, Σ _ : DecidableEq s, ℕ

@[reducible] def lawSignature : Signature where
  Params := LawParams.{u}
  State p := Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ↥(RecordClass p.2.2.2) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def lawObservation (p : LawParams.{u})
    (ρ : Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ) : ↥(RecordClass p.2.2.2) → ℝ :=
  letI := p.2.1
  letI := p.2.2.1
  measuredLaw ρ

@[reducible] def lawArena : Arena where
  signature := lawSignature.{u}
  Law R := ∀ {s : Type u} [k : Fintype s] [d : DecidableEq s] (n : ℕ)
    (ρ : Matrix (Fin 3 × s) (Fin 3 × s) ℂ), ρ.trace = 1 →
    pushforward (classProjective n) (R.readout () ⟨s, k, d, n⟩ ρ) = projectiveLaw n ∧
      ∀ k : RecordClass n, projectiveLaw n (classProjective n k) =
        ((Finset.univ.filter (fun w : History n => classOf w = k)).card : ℝ) / (2 : ℝ) ^ n

private def lawCounterfactual : Realization lawSignature.{u} :=
  realize lawSignature (fun _ _ _ => 0) (fun i => nomatch i)

private def emptyHistory : History 0 := fun i => i.elim0

private theorem emptyEndpoint_positive :
    0 < projectiveLaw 0 (classProjective 0 (classOf emptyHistory)) := by
  classical
  rw [(fair_projective_record 0 (sampleInput.{0} 2) (sampleInput_trace 2)).2]
  have hpos : 0 < (Finset.univ.filter (fun w : History 0 => classOf w = classOf emptyHistory)).card :=
    Finset.card_pos.mpr ⟨emptyHistory, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact div_pos (by exact_mod_cast hpos) (by positivity)

private theorem lawCounterfactual_fails : ¬ lawArena.{u}.Law lawCounterfactual.{u} := by
  classical
  intro h
  let y := classProjective 0 (classOf emptyHistory)
  have he := congrFun (h (s := Sample.{u}) 0 (sampleInput 2) (sampleInput_trace 2)).1 y
  change pushforward (classProjective 0) (0 : ↥(RecordClass 0) → ℝ) y = projectiveLaw 0 y at he
  exact (ne_of_gt emptyEndpoint_positive)
    (by simpa [pushforward] using he.symm)

private theorem zero_has_zero_measured_mass :
    measuredLaw (n := 0) (0 : Matrix (Fin 3 × Sample.{u}) (Fin 3 × Sample.{u}) ℂ) = 0 := by
  classical
  funext k
  simp [measuredLaw, pushforward, List.ofFn_zero, measuredHistory]

private theorem normalized_changes_measured_mass :
    measuredLaw (n := 0) (0 : Matrix (Fin 3 × Sample.{u}) (Fin 3 × Sample.{u}) ℂ) ≠
      measuredLaw (n := 0) (sampleInput.{u} 2) := by
  classical
  intro h
  have he := congrArg (pushforward (classProjective 0)) (zero_has_zero_measured_mass.symm.trans h)
  rw [(fair_projective_record 0 (sampleInput.{u} 2) (sampleInput_trace 2)).1] at he
  have hy := congrFun he (classProjective 0 (classOf emptyHistory))
  exact (ne_of_gt emptyEndpoint_positive)
    (by simpa [pushforward] using hy.symm)

def lawFamily : Registration lawArena.{u} (type_of% @fair_projective_record.{u}) where
  actual := realize lawSignature (fun _ => lawObservation) (fun i => nomatch i)
  bridge := Iff.rfl
  variation := ⟨@fair_projective_record.{u}, lawCounterfactual, lawCounterfactual_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawCounterfactual, ?_, rfl, lawCounterfactual_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, lawSignature]
    intro i
    let p : LawParams.{u} := ⟨Sample.{u}, inferInstanceAs (Fintype (ULift.{u} Unit)),
      inferInstanceAs (DecidableEq (ULift.{u} Unit)), 0⟩
    let ρ : Matrix (Fin 3 × p.1) (Fin 3 × p.1) ℂ := sampleInput.{u} 2
    exact ⟨p, 0, ρ, normalized_changes_measured_mass.{u}⟩

def fairProjectiveRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fair_projective_record.{u}) (Realization lawSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord.fair_projective_record
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord.lawFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lawArena.{u}⟩
  objectArena := .source ⟨lawArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lawArena.{u} ⟨lawFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lawSignature.{u} (fun _ => lawObservation) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
