import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Classical BigOperators
noncomputable section
universe u v

namespace SourceModel

private lemma prefix_measurable (a : Letter) : Measurable (prefixRaw a) := by
  exact measurable_of_countable _

private lemma prefix_none (a : Letter) : (prefixRaw a) ⁻¹' {none} = {none} := by
  ext t
  cases t <;> simp [prefixRaw]

private lemma prefix_nil (a : Letter) : (prefixRaw a) ⁻¹' {some []} = ∅ := by
  ext t
  cases t <;> simp [prefixRaw]

private lemma prefix_cons (a b : Letter) (w : List Letter) :
    (prefixRaw a) ⁻¹' {some (b::w)} = if a=b then {some w} else ∅ := by
  ext t
  cases t <;> by_cases h : a=b <;> simp [prefixRaw,h]

private def generated (phase : ActivePhase) (r : unitInterval) : Measure RawTail :=
  match phase with
  | .p => alphaMass r • Measure.dirac (some [0]) +
      betaMass r • (explicitStoppedWordLaw .beta r).map (prefixRaw 1)
  | .beta => betaMass r • Measure.dirac (some [1]) +
      alphaMass r • (explicitStoppedWordLaw .p r).map (prefixRaw 0)

private theorem complete_first_step (phase : ActivePhase) (r : unitInterval) :
    explicitStoppedWordLaw phase r = generated phase r := by
  apply Measure.ext_of_singleton
  intro t
  cases t with
  | none =>
      cases phase <;>
        simp [generated, Measure.map_apply (prefix_measurable _) (measurableSet_singleton _),
          prefix_none, explicitStoppedWordLaw, Measure.sum_apply]
  | some w =>
      cases w with
      | nil =>
          cases phase <;>
            simp [generated, Measure.map_apply (prefix_measurable _) (measurableSet_singleton _),
              prefix_nil, explicit_finite_mass, ← parses_normal_form,
              Parses, pendingColor]
      | cons b w =>
          cases phase <;> fin_cases b <;> cases w <;>
            simp [generated, Measure.map_apply (prefix_measurable _) (measurableSet_singleton _),
              prefix_cons, explicit_finite_mass, ← parses_normal_form,
              Parses, pendingColor, totalRead, legalRead, wordMass,
              bernoulliMeasure, alphaMass, betaMass]
          all_goals split_ifs <;> simp only [ENNReal.smul_def, smul_eq_mul]


private lemma probability (phase : ActivePhase) (r : unitInterval) :
    IsProbabilityMeasure (explicitStoppedWordLaw phase r) := by
  rw [← (actual_fourth_segment_stopped_word_law r phase).2]
  exact Measure.isProbabilityMeasure_map (measurable_stopped_read_word phase).aemeasurable

private theorem q_first_real (r : unitInterval) (E : Set RawTail) :
    (explicitStoppedWordLaw .p r).real E =
      (r:ℝ)*(if some [0] ∈ E then 1 else 0) +
      (1-(r:ℝ))*(explicitStoppedWordLaw .beta r).real ((prefixRaw 1) ⁻¹' E) := by
  haveI := probability .p r
  haveI := probability .beta r
  have hm : MeasurableSet E := trivial
  have he := congrArg (fun m : Measure RawTail => m E) (complete_first_step .p r)
  simp only [generated, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (prefix_measurable _) hm] at he
  rw [Measure.real, he, ENNReal.toReal_add (by exact ENNReal.mul_ne_top (by simp [alphaMass, betaMass]) (measure_ne_top _ _)) (by exact ENNReal.mul_ne_top (by simp [alphaMass, betaMass]) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  by_cases hx : some [0] ∈ E <;>
    simp [alphaMass, betaMass, unitInterval.coe_symm_eq, Measure.dirac_apply' _ hm,
      Set.indicator_apply, Measure.real, hx]

private theorem w_first_real (r : unitInterval) (E : Set RawTail) :
    (explicitStoppedWordLaw .beta r).real E =
      (1-(r:ℝ))*(if some [1] ∈ E then 1 else 0) +
      (r:ℝ)*(explicitStoppedWordLaw .p r).real ((prefixRaw 0) ⁻¹' E) := by
  haveI := probability .p r
  haveI := probability .beta r
  have hm : MeasurableSet E := trivial
  have he := congrArg (fun m : Measure RawTail => m E) (complete_first_step .beta r)
  simp only [generated, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (prefix_measurable _) hm] at he
  rw [Measure.real, he, ENNReal.toReal_add (by exact ENNReal.mul_ne_top (by simp [alphaMass, betaMass]) (measure_ne_top _ _)) (by exact ENNReal.mul_ne_top (by simp [alphaMass, betaMass]) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  by_cases hx : some [1] ∈ E <;>
    simp [alphaMass, betaMass, unitInterval.coe_symm_eq, Measure.dirac_apply' _ hm,
      Set.indicator_apply, Measure.real, hx]

private def third : unitInterval := ⟨1/3, by norm_num⟩

private def actualTable (X Y : Type*) [Fintype X] [Fintype Y] [Unique X] [Unique Y] : RegularTable X Y where
  pi _ := 1
  tau _ := 1
  B _ _ := 1
  A _ _ := 1
  u _ := 1/3
  v _ := 1/3
  pi_nonneg _ := by norm_num
  tau_nonneg _ := by norm_num
  pi_sum := by simp
  tau_sum := by simp
  B_nonneg _ _ := by norm_num
  A_nonneg _ _ := by norm_num
  B_sum _ := by simp
  A_sum _ := by simp
  pi_B _ := by simp
  tau_A _ := by simp
  u_box _ := by norm_num
  v_box _ := by norm_num
  Q _ := explicitStoppedWordLaw .p third
  W _ := explicitStoppedWordLaw .beta third
  Qprob _ := probability .p third
  Wprob _ := probability .beta third
  q_generate _ E := by simpa [third] using q_first_real third E
  w_generate _ E := by simpa [third] using w_first_real third E



private lemma all_event_distance (phase : ActivePhase) (r t : unitInterval) :
    FullTVBound (explicitStoppedWordLaw phase r).real
      (explicitStoppedWordLaw phase t) 1 := by
  intro E
  haveI := probability phase r
  haveI := probability phase t
  have h1 : 0 ≤ (explicitStoppedWordLaw phase r).real E := measureReal_nonneg
  have h2 : (explicitStoppedWordLaw phase r).real E ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ (explicitStoppedWordLaw phase t).real E := measureReal_nonneg
  have h4 : (explicitStoppedWordLaw phase t).real E ≤ 1 := measureReal_le_one
  apply abs_le.mpr
  constructor <;> linarith

private theorem model_bounds (X Y : Type*) [Fintype X] [Fintype Y] [Unique X] [Unique Y] :
    (∀ y, 0 < (actualTable X Y).tau y → (actualTable X Y).v y = (1/3:ℝ)) ∧
    (∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound (actualTable X Y).qMean (explicitStoppedWordLaw .p r) (1116529/22781250+1)) ∧
    (∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound (actualTable X Y).wMean (explicitStoppedWordLaw .beta r) (239/6750+1)) := by
  constructor
  · intro y hy; rfl
  constructor
  · intro r hr E
    have h := all_event_distance .p third r E
    simpa [RegularTable.qMean, actualTable] using
      h.trans (show (1:ℝ) ≤ 1116529/22781250+1 by norm_num)
  · intro r hr E
    have h := all_event_distance .beta third r E
    simpa [RegularTable.wMean, actualTable] using
      h.trans (show (1:ℝ) ≤ 239/6750+1 by norm_num)



end SourceModel


abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ep eb => max ep eb) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law f := ∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (R : RegularTable X Y) (s ep eb : ℝ),
    1/3 ≤ s ∧ s ≤ 2/5 →
    (∀ y, 0 < R.tau y → R.v y = s) →
    0 ≤ ep → 0 ≤ eb →
    (∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound R.qMean (explicitStoppedWordLaw .p r) (1116529/22781250+ep)) →
    (∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound R.wMean (explicitStoppedWordLaw .beta r) (239/6750+eb)) →
    1/35200 < f.readout () ep eb

theorem actual_law : arena.{u,v}.Law actual := by
  intro X Y iX iY R s ep eb hbox hs hep heb hQ hW
  exact R.constant_suspension_separator s ep eb hbox hs hep heb hQ hW

theorem source_bridge :
    (type_of% (@RegularTable.constant_suspension_separator.{u,v})) ↔ arena.{u,v}.Law actual := by
  rfl

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]

-- A law-changing intervention requires one inhabited original regular-table instance.
theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let T := SourceModel.actualTable (ULift.{u} Unit) (ULift.{v} Unit)
  obtain ⟨hs,hQ,hW⟩ := SourceModel.model_bounds (ULift.{u} Unit) (ULift.{v} Unit)
  have hh := h T (1/3) 1 1 (by norm_num) hs (by norm_num) (by norm_num) hQ hW
  norm_num [rejected, realize] at hh

def sourceRegistration : Registration arena.{u,v}
    (type_of% (@RegularTable.constant_suspension_separator.{u,v})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := actual_dependence


noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@RegularTable.constant_suspension_separator.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.registration_1.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨sourceRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ep eb => max ep eb) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration_1

end

namespace PeriodicReuse
noncomputable section
abbrev endpointSignature : Signature where
  Params := unitInterval
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def endpointActual : Realization endpointSignature :=
  realize endpointSignature (fun _ r j => (explicitStoppedWordLaw .p r).real {some (pWord j 1)})
    (fun e => nomatch e)
def endpointRejected : Realization endpointSignature :=
  realize endpointSignature (fun _ _ _ => 0) (fun e => nomatch e)
def endpointArena : Arena where
  signature := endpointSignature
  Law R := ∀ (r : unitInterval) (j : ℕ),
    R.readout () r j = (1-(r:ℝ))^2*((r:ℝ)*(1-r))^j
private theorem rejected_endpoint : ¬ endpointArena.Law endpointRejected := by
  intro law
  have he := law endpointA 0
  norm_num [endpointRejected,realize,endpointA] at he
private theorem endpoint_dependence : ObservationalDependence endpointSignature endpointActual := by
  intro role
  refine ⟨endpointA,0,1,?_⟩
  change (explicitStoppedWordLaw .p endpointA).real {some (pWord 0 1)} ≠
    (explicitStoppedWordLaw .p endpointA).real {some (pWord 1 1)}
  rw [endpoint_p_word,endpoint_p_word]
  norm_num [endpointA]
def endpointRecord : Registration endpointArena (type_of% (@endpoint_p_word)) where
  actual := endpointActual
  bridge := Iff.rfl
  variation := ⟨endpoint_p_word,endpointRejected,rejected_endpoint⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨endpointRejected,?_,rfl,rejected_endpoint⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := endpoint_dependence

def endpointRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@endpoint_p_word) (type_of% (realize endpointSignature
      (fun _ r j => (explicitStoppedWordLaw .p r).real {some (pWord j 1)})
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.PeriodicReuse.endpoint,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.PeriodicReuse.endpointRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨endpointArena⟩, objectArena := .source ⟨endpointArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source endpointArena ⟨endpointRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize endpointSignature
    (fun _ r j => (explicitStoppedWordLaw .p r).real {some (pWord j 1)})
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator,
    definition := none, coordinates := #[0],
    readouts := #[{
        path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms endpointRecord
end
end PeriodicReuse

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.ProbabilityAudit
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section

abbrev signature : Signature where
  Params := ActivePhase
  State _ := unitInterval
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ phase r => explicitStoppedWordLaw phase r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law f := ∀ (phase : ActivePhase) (r : unitInterval), IsProbabilityMeasure (f.readout () phase r)

theorem source_bridge : (type_of% (@endpoint_probability)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := endpoint_probability

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h .p ⟨0,by norm_num⟩).measure_univ
  simp [rejected,realize] at hh

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨.p,⟨0,by norm_num⟩,⟨1,by norm_num⟩,?_⟩
  intro h
  have he := congrArg (fun P : Measure RawTail => P {some [0]}) h
  simp only [actual,realize] at he
  have hf : ∃ b, WordFamily .p b [0] := ⟨0,0,rfl⟩
  rw [explicit_finite_mass,explicit_finite_mass,if_pos hf,if_pos hf] at he
  norm_num [wordMass,alphaMass,bernoulliMeasure] at he

def sourceRegistration : Registration arena (type_of% (@endpoint_probability)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@endpoint_probability) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.probability_registration.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.ProbabilityAudit.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ phase r => explicitStoppedWordLaw phase r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration_1
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator.ProbabilityAudit
