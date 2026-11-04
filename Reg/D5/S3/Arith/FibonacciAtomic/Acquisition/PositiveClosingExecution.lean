import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution
import Reg.Support.DependentFamily

/-! Full natural-pair realization of positive chronological execution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution
open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
  (Run paidReads Instruction continuous_transport)
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
  (residueSource runWord replace quantity costBound)
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
  (direction graftBound)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool × List
    (_root_.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport.Event)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H v => (executionWord H v, executionEvents H v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ([], [])) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ), 1 ≤ H → ∀ v : ℕ × ℕ,
    let w := (R.readout () H v).1
    let es := (R.readout () H v).2
    (∃ t, Run (controller H) H (controller H).initial v es t (runWord w v) (residueSource H v)) ∧
    _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport.finalWord
      [] es = w ∧
    residueSource H (runWord w v) = residueSource H v ∧
    1 ≤ period H ∧ period H ≤ H ^ 4 ∧ matrix H ^ period H = 1 ∧
    (∀ k, 1 ≤ k → matrix H ^ k = 1 → period H ≤ k) ∧
    paidReads es = tests H v false + tests H v true ∧
    paidReads es = (if H = 1 then 0 else 2 * costBound H) ∧
    (w.count true = period H * (direction H * tests H v false +
      (direction H + 1) * tests H v true)) ∧
    w.count false = H * graftSum H v ∧
    w.count true ≤ period H * (2 * direction H + 1) * costBound H ∧
    w.count false ≤ 2 * H * graftBound H * costBound H ∧
    (graftSuffixes w).length = w.count false ∧
    runWord w v = replace^[w.count true] v +
      ((graftSuffixes w).map (fun r => replace^[r] (1, 0))).sum ∧
    (∀ pre post, w = pre ++ post → quantity (runWord pre v) ≤ quantity (runWord w v)) ∧
    quantity (runWord w v) ≤ 2 ^ w.count true * (quantity v + 2 * w.count false) ∧
    (H = 1 → w = [] ∧ es = [])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, bad, _⟩ := h 2 (by decide) (0, 0)
  have hb : costBound 2 = 1 := by decide +kernel
  norm_num [rejected, realize, paidReads, hb] at bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, (0, 0), (1, 0), ?_⟩
  change (executionWord 2 (0, 0), executionEvents 2 (0, 0)) ≠
    (executionWord 2 (1, 0), executionEvents 2 (1, 0))
  intro h
  have he : executionEvents 2 (0, 0) = executionEvents 2 (1, 0) := congrArg Prod.snd h
  obtain ⟨t₀, r₀⟩ := (positive_execution 2 (by decide) (0, 0)).1
  obtain ⟨t₁, r₁⟩ := (positive_execution 2 (by decide) (1, 0)).1
  have c₀ := (continuous_transport (controller 2) 2 _ _ _ _ _ r₀).2.1
  have c₁ := (continuous_transport (controller 2) 2 _ _ _ _ _ r₁).2.1
  rw [he] at c₀
  have ht : t₀ = t₁ := congrArg Prod.fst (c₀.symm.trans c₁)
  have terminal {s x es t y l} (hr : Run (controller 2) 2 s x es t y l) :
      (controller 2).code t = Instruction.halt l := by
    induction hr <;> assumption
  have hl : residueSource 2 (0, 0) = residueSource 2 (1, 0) := by
    apply Instruction.halt.inj
    exact (terminal r₀).symm.trans ((congrArg (controller 2).code ht).trans (terminal r₁))
  have hx := congrArg Prod.fst hl
  norm_num [residueSource] at hx

def sourceRegistration : Registration arena (type_of% positive_execution) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_execution, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@positive_execution) (Realization signature) Type Unit where
  unitName := `positiveClosingExecution
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H v => (executionWord H v, executionEvents H v))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "letValue"], stateBinder := 2,
        functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "letValue"], stateBinder := 2,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms sourceRegistration

namespace ResidueTransport

abbrev signature : Signature where
  Params := ℕ × List Bool
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod p.1 × ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v =>
    _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.run (1, 0)
      (p.2.map Bool.not) (residueSource p.1 v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ) (w : List Bool) (v : ℕ × ℕ),
    residueSource H (runWord w v) = R.readout () (H, w) v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have h := congrArg Prod.fst (bad 2 [] (1, 0))
  change (1 : ZMod 2) = 0 at h
  exact one_ne_zero h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(2, []), (0, 0), (1, 0), ?_⟩
  intro h
  have he := congrArg Prod.fst h
  change (0 : ZMod 2) = 1 at he
  exact zero_ne_one he

def sourceRegistration : Registration arena (type_of% residue_run) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨residue_run, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@residue_run) (Realization signature) Type Unit where
  unitName := `wholeWordResidueTransport
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution.ResidueTransport.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v =>
    _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.run (1, 0)
      (p.2.map Bool.not) (residueSource p.1 v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms sourceRegistration

end ResidueTransport

end Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution
