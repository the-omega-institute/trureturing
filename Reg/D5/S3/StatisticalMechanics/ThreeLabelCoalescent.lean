import D5.S3.StatisticalMechanics.ThreeLabelCoalescent
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.SingleDependentReadout

/-! Source-owned registrations and typed analysis of the five partition masses. -/

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open _root_.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Parameters retain the complete trajectory and the observation time; the
states are the five actual partitions, including zero-mass initial states. -/
abbrev massSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ((ℝ → Fin 5 → ℝ) × ℝ) (fun _ => Fin 5) (fun _ => ℝ)

def massActual : Realization massSignature :=
  realize massSignature (fun _ pt i => pt.1 pt.2 i) (fun e => nomatch e)

def massRejected : Realization massSignature :=
  realize massSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem massDependence : ObservationalDependence massSignature massActual := by
  intro i
  refine ⟨⟨(fun _ j => (j.val : ℝ)), 0⟩, 0, 1, ?_⟩
  norm_num [massActual, realize]

def forwardArena : Arena where
  signature := massSignature
  Law R := ∀ (h : ℝ) (_hh : 0 < h) (p : ℝ → Fin 5 → ℝ)
    (_hp : ForwardLaw h p) (t : ℝ) (_ht : 0 ≤ t),
    (fun i => R.readout () (p, t) i) = explicit h t ∧
      delta (fun i => R.readout () (p, t) i) = v h t * H h t

private theorem forwardRejected : ¬ forwardArena.Law massRejected := by
  intro hl
  have hp := (positive_probability_solution 1 (by norm_num)).1
  have hz := (hl 1 (by norm_num) (explicit 1) hp 0 le_rfl).1
  have hh := congrFun hz 0
  norm_num [massRejected, realize, explicit, u, v] at hh

def forwardEvidence : Registration forwardArena (type_of% forward_solution) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨forward_solution, massRejected, forwardRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    forwardArena.Law massActual massRejected forwardRejected
  dependence := massDependence

def probabilityArena : Arena where
  signature := massSignature
  Law R := ∀ (h : ℝ), 0 < h →
    ForwardLaw h (explicit h) ∧ ∀ (p : ℝ → Fin 5 → ℝ), ForwardLaw h p → ∀ t, 0 < t →
      (fun i => R.readout () (p, t) i) = explicit h t ∧
      (∑ i, R.readout () (p, t) i) = 1 ∧ (∀ i, 0 < R.readout () (p, t) i) ∧
      delta (fun i => R.readout () (p, t) i) = v h t * H h t ∧
      0 < pyramidWidth (fun i => R.readout () (p, t) i) ∧
      0 < 1 - Z (fun i => R.readout () (p, t) i) ∧
      (delta (fun i => R.readout () (p, t) i) = 0 ↔
        R.readout () (p, t) 3 = productJoint (fun i => R.readout () (p, t) i)) ∧
      (delta (fun i => R.readout () (p, t) i) = 0 ↔
        (fun i => R.readout () (p, t) i) = productCompletion (fun i => R.readout () (p, t) i)) ∧
      (∀ f, taskError (fun i => R.readout () (p, t) i) f =
        contrast f * delta (fun i => R.readout () (p, t) i) /
          (1 - Z (fun i => R.readout () (p, t) i)))

private theorem probabilityRejected : ¬ probabilityArena.Law massRejected := by
  intro hl
  have hs := hl 1 (by norm_num)
  have hz := (hs.2 (explicit 1) hs.1 1 (by norm_num)).2.2.1 0
  norm_num [massRejected, realize] at hz

def probabilityEvidence : Registration probabilityArena (type_of% positive_probability_solution) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨positive_probability_solution, massRejected, probabilityRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    probabilityArena.Law massActual massRejected probabilityRejected
  dependence := massDependence

abbrev determinantSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ → Fin 5 → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def determinantActual : Realization determinantSignature :=
  realize determinantSignature (fun _ p t => delta (p t)) (fun e => nomatch e)

def determinantRejected : Realization determinantSignature :=
  realize determinantSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem determinantDependence : ObservationalDependence determinantSignature determinantActual := by
  intro i
  refine ⟨(fun t => ![1, 0, 0, t, 0]), 0, 1, ?_⟩
  norm_num [determinantActual, realize, delta]

def zerosArena : Arena where
  signature := determinantSignature
  Law R := ∀ (h : ℝ) (_hh : 0 < h) (p : ℝ → Fin 5 → ℝ) (_hp : ForwardLaw h p)
    (a b c : ℝ) (_ha : 0 < a) (_hab : a < b) (_hbc : b < c),
    R.readout () p a = 0 → R.readout () p b = 0 → R.readout () p c ≠ 0

private theorem zerosRejected : ¬ zerosArena.Law determinantRejected := by
  intro hl
  have hp := (positive_probability_solution 1 (by norm_num)).1
  have hz := hl 1 (by norm_num) (explicit 1) hp 1 2 3
    (by norm_num) (by norm_num) (by norm_num)
  simp [determinantRejected, realize] at hz

def zerosEvidence : Registration zerosArena (type_of% no_three_positive_zeros) where
  actual := determinantActual
  bridge := Iff.rfl
  variation := ⟨no_three_positive_zeros, determinantRejected, zerosRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    zerosArena.Law determinantActual determinantRejected zerosRejected
  dependence := determinantDependence

abbrev foldSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => ℝ) (fun _ => ℝ)

def foldActual : Realization foldSignature :=
  realize foldSignature (fun _ h t => H h t) (fun e => nomatch e)

def foldRejected : Realization foldSignature :=
  realize foldSignature (fun _ _ _ => 1) (fun e => nomatch e)

def foldArena : Arena where
  signature := foldSignature
  Law R := ∃ hc τc : ℝ, hc ∈ Set.Ioo 1 8 ∧ 0 < τc ∧ R.readout () hc τc = 0 ∧
    deriv (H hc) τc = 0 ∧ 0 < deriv (deriv (H hc)) τc ∧
    (∀ h t : ℝ, 0 < h → 0 < t → H h t = 0 → deriv (H h) t = 0 → h = hc ∧ t = τc) ∧
    (∀ h : ℝ, 0 < h → h < hc → TwoCrossings h) ∧
    (∀ t : ℝ, 0 < t → t ≠ τc → 0 < H hc t) ∧
    (∀ h : ℝ, hc < h → ∀ t : ℝ, 0 < t → 0 < H h t)

private theorem foldRejectedLaw : ¬ foldArena.Law foldRejected := by
  rintro ⟨hc, τc, _, _, hz, _⟩
  norm_num [foldRejected, realize] at hz

private theorem foldDependence : ObservationalDependence foldSignature foldActual := by
  intro i
  obtain ⟨hc, τc, hh, _, _, _, _, _, _, _, high⟩ := unique_fold_classification
  refine ⟨hc + 1, 0, 1, ?_⟩
  have hp := high (hc + 1) (by linarith) 1 (by norm_num)
  have hk : K (hc + 1) ≠ 0 := ne_of_gt (by dsimp [K]; linarith [hh.1])
  have hz : H (hc + 1) 0 = 0 := by
    simp [H, u, v]
    field_simp [hk]
    dsimp [K]
    ring
  change H (hc + 1) 0 ≠ H (hc + 1) 1
  rw [hz]
  exact ne_of_lt hp

def foldEvidence : Registration foldArena (type_of% unique_fold_classification) where
  actual := foldActual
  bridge := Iff.rfl
  variation := ⟨unique_fold_classification, foldRejected, foldRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    foldArena.Law foldActual foldRejected foldRejectedLaw
  dependence := foldDependence

abbrev endpointSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ((Fin 7 → ℝ) × (ℝ → Fin 5 → ℝ)) (fun _ => ℝ) (fun _ => ℝ)

def endpointActual : Realization endpointSignature :=
  realize endpointSignature (fun _ rp t => rp.2 t 0) (fun e => nomatch e)

def endpointRejected : Realization endpointSignature :=
  realize endpointSignature (fun _ _ _ => 0) (fun e => nomatch e)

def endpointArena : Arena where
  signature := endpointSignature
  Law R := ∀ (r : Fin 7 → ℝ) (_hr : ∀ i, 0 < r i)
    (p : ℝ → Fin 5 → ℝ) (_hp : GeneralForwardLaw r p),
    (∀ t, 0 ≤ t → R.readout () (r, p) t = Real.exp (-outgoing r * t)) ∧
    (∀ t, 0 ≤ t → p t 1 * p t 2 / p t 0 ≤
      r 0 * r 1 * t ^ 2 *
        Real.exp (-(min (r 4) (outgoing r) + min (r 5) (outgoing r) - outgoing r) * t)) ∧
    (∀ t, 0 ≤ t →
      p t 1 ≤ r 0 * t * Real.exp (-min (r 4) (outgoing r) * t) ∧
      p t 2 ≤ r 1 * t * Real.exp (-min (r 5) (outgoing r) * t) ∧
      p t 4 ≤ r 2 * t * Real.exp (-min (r 6) (outgoing r) * t)) ∧
    HasDerivAt (fun t => delta (p t)) (r 3) 0 ∧
    (∀ h, 0 < h →
      min (baseRates h 4) (outgoing (baseRates h)) +
        min (baseRates h 5) (outgoing (baseRates h)) - outgoing (baseRates h) = 1 / 4 ∧
      ∀ q, ForwardLaw h q → GeneralForwardLaw (baseRates h) q)

theorem unitGeneral : GeneralForwardLaw (baseRates 1) (explicit 1) := by
  have hq := (positive_probability_solution 1 (by norm_num)).1
  refine ⟨hq.start, ?_, ?_, ?_⟩
  · intro t ht i
    convert hq.equation t ht i using 1
    fin_cases i <;> norm_num [generalForward, forward, baseRates, outgoing, ell] <;> ring
  · intro t ht i
    rcases eq_or_lt_of_le ht with he | he
    · rw [← he, hq.start]; fin_cases i <;> norm_num [initial]
    · exact ((positive_probability_solution 1 (by norm_num)).2 _ hq t he).2.2.1 i |>.le
  · intro t ht
    rcases eq_or_lt_of_le ht with he | he
    · rw [← he, hq.start]; norm_num [initial, Fin.sum_univ_succ]
    · exact ((positive_probability_solution 1 (by norm_num)).2 _ hq t he).2.1

private theorem endpointRejectedLaw : ¬ endpointArena.Law endpointRejected := by
  intro hl
  have hpos : ∀ i, 0 < baseRates 1 i := by
    intro i; fin_cases i <;> norm_num [baseRates, ell]
  have hz := (hl (baseRates 1) hpos (explicit 1) unitGeneral).1 0 le_rfl
  norm_num [endpointRejected, realize] at hz

private theorem endpointDependence : ObservationalDependence endpointSignature endpointActual := by
  intro i
  refine ⟨((fun _ => 1), (fun t => ![t, 0, 0, 0, 0])), 0, 1, ?_⟩
  norm_num [endpointActual, realize]

def endpointEvidence : Registration endpointArena (type_of% seven_rate_endpoint_certificates) where
  actual := endpointActual
  bridge := Iff.rfl
  variation := ⟨seven_rate_endpoint_certificates, endpointRejected, endpointRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    endpointArena.Law endpointActual endpointRejected endpointRejectedLaw
  dependence := endpointDependence

/-- The function-valued operand p(t) has the finite partition type as its domain. -/
def forwardSelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescent
  definition := none
  coordinates := #[2, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

def probabilitySelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescent
  definition := none
  coordinates := #[2, 4]
  readouts := #[{
    path := #["body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

def zerosSelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescent
  definition := none
  coordinates := #[2]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
    stateBinder := 4
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def foldSelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescent
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
    stateBinder := 1
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def endpointSelection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.ThreeLabelCoalescent
  definition := none
  coordinates := #[0, 2]
  readouts := #[{
    path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"]
    stateBinder := 4
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def forwardRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@forward_solution) (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.forwardUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.forwardEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨forwardArena⟩
  objectArena := .source ⟨forwardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source forwardArena ⟨forwardEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature massActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some forwardSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

def probabilityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@positive_probability_solution) (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.probabilityUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.probabilityEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨probabilityArena⟩
  objectArena := .source ⟨probabilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source probabilityArena ⟨probabilityEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature massActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some probabilitySelection
  continuation := .unknown
  familyRecord := none
  options := #[]

def zerosRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@no_three_positive_zeros) (Realization determinantSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.zerosUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.zerosEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨zerosArena⟩
  objectArena := .source ⟨zerosArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zerosArena ⟨zerosEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize determinantSignature determinantActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some zerosSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

def foldRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@unique_fold_classification) (Realization foldSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.foldUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.foldEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨foldArena⟩
  objectArena := .source ⟨foldArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source foldArena ⟨foldEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize foldSignature foldActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some foldSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

def endpointRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@seven_rate_endpoint_certificates) (Realization endpointSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.endpointUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent.endpointEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena⟩
  objectArena := .source ⟨endpointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena ⟨endpointEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize endpointSignature endpointActual.readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some endpointSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The selected source is the complete five-partition probability law at one
observation time, with its complete original theorem telescope. -/
def probabilitySource : Analysis.Source (@positive_probability_solution) :=
  Analysis.Source.ofRegistration _ probabilityEvidence .exact probabilitySelection

def probabilityAnalysis : AuricFib.Contract.Application (@positive_probability_solution) where
  evidence := .typed {
    source := probabilitySource
    plan := { task := (), initial := [], additions := [[()], []] }
    acquisition := .unavailable
      "Five actual partition states with proved real law and event means; no certified finite equality table for symbolic exponential masses or native continuation adapter" }

#print axioms forwardRegistration
#print axioms probabilityRegistration
#print axioms zerosRegistration
#print axioms foldRegistration
#print axioms endpointRegistration
#print axioms probabilityAnalysis
end Reg.D5.S3.StatisticalMechanics.ThreeLabelCoalescent
