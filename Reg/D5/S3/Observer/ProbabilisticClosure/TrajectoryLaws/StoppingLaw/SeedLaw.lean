import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open MeasureTheory
universe u

noncomputable section

abbrev signature : Signature where
  Params := Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : Bool) (k : ℕ), R.readout () j k =
    (List.range k).map (fun i : ℕ => j.toInt + 2 * ((i : ℤ) + 1) + 1)

private theorem actual_law : arena.Law actual := by
  exact witness_read_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h false 1
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@witness_read_addresses)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨false, 0, 1, ?_⟩
    simp [actual, realize, witnessEdges]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@witness_read_addresses)
    (type_of% (realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

namespace RawMinimum

abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν], IsLeast {R : ℕ | ∃ Q : RawRule U, Q.CompletionLawful ν ∧ Q.TotalCap k ∧ Q.SameFullLaw (stoppingRule j k) β j ν ∧ Q.WithinActualRadius j R} (R.readout () () k)

private theorem actual_law : arena.{u}.Law actual := by
  exact @stopping_witness_exact_radius.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h (U := ULift.{u} Unit) β false 1 (by omega) ν
  have hs := stopping_witness_exact_radius β false 1 (by omega) ν
  have hc := hs.2 hb.1
  norm_num [rejected, realize] at hc

def evidence : Registration arena.{u} (type_of% (@stopping_witness_exact_radius.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stopping_witness_exact_radius.{u})
    (type_of% (realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RawMinimum.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RawMinimum.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end RawMinimum

namespace CompletedMinimum

abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν], IsLeast {R : ℕ | ∃ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) ∧ Q.TotalCap k ∧ Q.fullLaw β j ν = (stoppingRule j k).fullLaw β j ν ∧ Q.CompletedWithinActualRadius j R} (R.readout () () k)

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.completed_stopping_witness_exact_radius.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h (U := ULift.{u} Unit) β false 1 (by omega) ν
  have hs := CompletedRule.completed_stopping_witness_exact_radius β false 1 (by omega) ν
  have hc := hs.2 hb.1
  norm_num [rejected, realize] at hc

def evidence : Registration arena.{u} (type_of% (@CompletedRule.completed_stopping_witness_exact_radius.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CompletedRule.completed_stopping_witness_exact_radius.{u})
    (type_of% (realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedMinimum.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedMinimum.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletedMinimum

namespace RadiusLower

abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k) (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν) (r : ℕ) (hr : Q.WithinActualRadius j r), R.readout () () k ≤ r

private theorem actual_law : arena.{u}.Law actual := by
  exact @original_rule_radius_lower.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hb := h β false 1 (by omega) ν Q hQ hc hl 3 hr
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@original_rule_radius_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rule_radius_lower.{u})
    (type_of% (realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RadiusLower.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RadiusLower.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end RadiusLower

namespace FullWitnessMass

abbrev signature : Signature where
  Params := Σ _ : Bias, ℕ
  State p := Observation
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (B : Set U) (hB : MeasurableSet B) (z : Observation), ((stoppingRule j k).fullLaw β j ν).real (B ×ˢ {z}) = ν.real B * R.readout () ⟨β, k⟩ z

private theorem actual_law : arena.{u}.Law actual := by
  exact @stopping_witness_full_law.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h β false 1 (by omega) ν Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  have hs := stopping_witness_full_law β false 1 (by omega) ν Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  norm_num [rejected, realize, stoppingMass] at hb hs
  linarith

def evidence : Registration arena.{u} (type_of% (@stopping_witness_full_law.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨⟨β, 1⟩, ⟨.a false, none, false, 0⟩, ⟨.a false, some (.a false), true, 1⟩, ?_⟩
    norm_num [actual, realize, stoppingMass, Bias.π, β]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stopping_witness_full_law.{u})
    (type_of% (realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.FullWitnessMass.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.FullWitnessMass.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[2, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"],
      stateBinder := 10, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end FullWitnessMass

namespace OriginalWitnessContract

abbrev signature : Signature where
  Params := Σ _ : Bias, ℕ
  State p := Observation
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν], (stoppingRule (U := U) j k).Lawful ∧ (stoppingRule (U := U) j k).TotalCap k ∧
      (∀ v ∈ (witnessTree j k).formalRuns,
        v.returned = true ∧ 1 ≤ v.paid ∧ v.paid ≤ k) ∧
      (∀ B : Set U, MeasurableSet B → ∀ z : Observation,
        ((stoppingRule j k).fullLaw β j ν).real (B ×ˢ {z}) =
          ν.real B * R.readout () ⟨β, k⟩ z) ∧
      (stoppingRule (U := U) j k).WithinActualRadius j (2 * k + 1)

private theorem actual_law : arena.{u}.Law actual := by
  exact @stopping_witness_original_contract.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := (h β false 1 (by omega) ν).2.2.2.1 Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  have hs := stopping_witness_full_law β false 1 (by omega) ν Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  norm_num [rejected, realize, stoppingMass] at hb hs
  linarith

def evidence : Registration arena.{u} (type_of% (@stopping_witness_original_contract.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨⟨β, 1⟩, ⟨.a false, none, false, 0⟩, ⟨.a false, some (.a false), true, 1⟩, ?_⟩
    norm_num [actual, realize, stoppingMass, Bias.π, β]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stopping_witness_original_contract.{u})
    (type_of% (realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.OriginalWitnessContract.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.OriginalWitnessContract.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[2, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "arg", "arg"],
      stateBinder := 10, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end OriginalWitnessContract

namespace OriginalSharpProbability

abbrev signature : Signature where
  Params := Bias
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β k => β.T k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k) (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν),
    ((1 + R.readout () β k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) ∧
      ((sourceLaw β).prod ν).real ((stoppingRule (U := U) j k).remote j (2 * k + 1)) =
        (1 + β.T k) / 2) ∧
      (k = 1 → ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) = 1)

private theorem actual_law : arena.{u}.Law actual := by
  exact @original_rule_sharp_remote_probability.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hb := (h β false 1 (by omega) ν Q hQ hc hl).1.1
  have hs := (original_rule_sharp_remote_probability β false 1 (by omega) ν Q hQ hc hl).2 rfl
  rw [hs] at hb
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@original_rule_sharp_remote_probability.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨β, 1, 2, ?_⟩
    exact ne_of_gt (β.T_succ_lt 1)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rule_sharp_remote_probability.{u})
    (type_of% (realize signature (fun _ β k => β.T k) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.OriginalSharpProbability.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.OriginalSharpProbability.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ β k => β.T k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end OriginalSharpProbability

namespace CompletedSharpProbability

abbrev signature : Signature where
  Params := Bias
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β k => β.T k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν)) (hc : Q.TotalCap k) (hlaw : Q.fullLaw β j ν = (stoppingRule j k).fullLaw β j ν),
    (∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      (∀ᵐ u ∂ν, (∀ᵐ s ∂sourceLaw β, Q.normalize k (s,u) = (T u).val) ∧
        ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
          (T u).val = ReadTree.stopComb (es.map (fun e => 2 * e + (!j).toInt)) ∧
          es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k)) ∧
      ((1 + R.readout () β k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1))) ∧
      (((sourceLaw β).prod ν).real
        ((stoppingRule (U := U) j k).remote j (2 * k + 1)) = (1 + β.T k) / 2) ∧
      (k = 1 → ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) = 1)

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.original_rule_stopping_results.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (CompletedRule.completed_stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hb := (h β false 1 (by omega) ν Q hQ hc hl).2.1
  have hs := (CompletedRule.original_rule_stopping_results β false 1 (by omega) ν Q hQ hc hl).2.2.2 rfl
  rw [hs] at hb
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@CompletedRule.original_rule_stopping_results.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨β, 1, 2, ?_⟩
    exact ne_of_gt (β.T_succ_lt 1)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CompletedRule.original_rule_stopping_results.{u})
    (type_of% (realize signature (fun _ β k => β.T k) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedSharpProbability.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedSharpProbability.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ β k => β.T k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletedSharpProbability

namespace OriginalRigidity

abbrev signature : Signature where
  Params := Unit
  State p := List ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .leaf none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k) (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν), ∀ᵐ u ∂ν, ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      Q.normalize k u = R.readout () () (es.map (fun e => 2 * e + (!j).toInt)) ∧
      es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k

private theorem actual_law : arena.{u}.Law actual := by
  exact @original_rule_stopping_rigidity.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hs := original_rule_stopping_rigidity β false 1 (by omega) ν Q hQ hc hl
  have hb := h β false 1 (by omega) ν Q hQ hc hl
  obtain ⟨u, hu, hv⟩ := (hs.and hb).exists
  obtain ⟨es, hlen, _, L, he, _, _⟩ := hu
  obtain ⟨es₀, _, _, L₀, he₀, _, _⟩ := hv
  change Q.normalize 1 u = ReadTree.leaf none at he₀
  rw [he₀] at he
  cases es with
  | nil => simp at hlen
  | cons e es => cases he

def evidence : Registration arena.{u} (type_of% (@original_rule_stopping_rigidity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨(), [], [0], ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_rule_stopping_rigidity.{u})
    (type_of% (realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.OriginalRigidity.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.OriginalRigidity.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end OriginalRigidity

namespace CanonicalWitness

abbrev signature : Signature where
  Params := Bool
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j k => witnessTree j k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .leaf none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k), HasStoppingLaw β (lawWindow (witnessTree j k)) j k (R.readout () j k)

private theorem actual_law : arena.Law actual := by
  exact @witness_canonical_law

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let V := lawWindow (witnessTree false 1)
  let z : Observation := ⟨.a false, none, false, 0⟩
  have hb := (h β false 1 (by decide)) z
  change fullMass β V false (.leaf none) z = 0 at hb
  have hm := ReadTree.fullMass_a β V false false (.leaf none) none 0
  have he : {S : Spins | S (targetIndex false false) = false ∧ ((ReadTree.leaf none).run (visible false S)).output = none ∧ ((ReadTree.leaf none).run (visible false S)).paid = 0} = {S | S (targetIndex false false) = false} := by
    ext S
    simp [ReadTree.run, Execution.paid]
  rw [he, SpinWindow.spin_prob β V (targetIndex false false) (by simp [V, lawWindow, targetIndex]) false] at hm
  norm_num [Bias.π, β] at hm
  change fullMass β V false (.leaf none) z = 1 / 3 at hm
  rw [hb] at hm
  norm_num at hm

def evidence : Registration arena (type_of% (@witness_canonical_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨false, 1, 2, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@witness_canonical_law)
    (type_of% (realize signature (fun _ j k => witnessTree j k) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CanonicalWitness.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CanonicalWitness.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ j k => witnessTree j k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CanonicalWitness

namespace RawLawSections

abbrev signature : Signature where
  Params := Bias
  State p := Set SourcePoint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k) (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : Q.fullLaw β j ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × U => (p.2, w p.1))),
    ∀ᵐ u ∂ν, ∀ z : Observation, fullMass β (lawWindow (Q.normalize k u)) j (Q.normalize k u) z = R.readout () β (w ⁻¹' {z})

private theorem actual_law : arena.{u}.Law actual := by
  exact @full_same_seed_law_forces_sections.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hQ : Q.CompletionLawful ν := by
    constructor
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (ReadTree.leaf none).eventAfter r)
      exact measurable_const
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (0 : NNReal))
      exact measurable_const
  let w : SourcePoint → Observation := fun s => observation false s.1 (.leaf none) s.2
  have hw : Measurable w := measurable_observation false (.leaf none)
  have hj : Q.joint false = fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1) := by
    funext p
    have hs := Q.normalization_pointwise 0 hc p.1.1 p.1.2 p.2
    have hd := Q.normalization_return_indicator 0 hc p.1.1 p.1.2 p.2
    dsimp only [RawRule.joint, RawRule.rawObservation, w, observation]
    rw [hs.2.1, hd, hs.2.2]
    rfl
  have hlaw : Q.fullLaw β false ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1)) := by
    unfold RawRule.fullLaw
    rw [hj]
  have hb := h β false ν Q hQ 0 hc w hw hlaw
  obtain ⟨u, hu⟩ := hb.exists
  let z : Observation := ⟨.a false, none, false, 0⟩
  have hx := hu z
  have hs := sourceLaw_observation β false (Q.normalize 0 u) z
  have hbnd : fullMass β (lawWindow (Q.normalize 0 u)) false (Q.normalize 0 u) z ≤ 1 := by
    rw [← hs]
    exact measureReal_le_one
  norm_num [rejected, realize] at hx
  linarith

def evidence : Registration arena.{u} (type_of% (@full_same_seed_law_forces_sections.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨β, ∅, Set.univ, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_same_seed_law_forces_sections.{u})
    (type_of% (realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RawLawSections.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RawLawSections.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end RawLawSections

namespace CompletedLawSections

abbrev signature : Signature where
  Params := Bias
  State p := Set SourcePoint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν)) (k : ℕ) (hc : Q.TotalCap k) (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : Q.fullLaw β j ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × U => (p.2, w p.1))),
    ∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      (Q.normalize k =ᵐ[(sourceLaw β).prod ν] fun p => (T p.2).val) ∧
      (∀ᵐ u ∂ν, (∀ᵐ s ∂sourceLaw β, Q.normalize k (s,u) = (T u).val) ∧
        ∀ z, fullMass β (lawWindow (T u).val) j (T u).val z = R.readout () β (w ⁻¹' {z}))

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.full_law_sections.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hQ : Q.CompletionLawful ν := by
    constructor
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (ReadTree.leaf none).eventAfter r)
      exact measurable_const
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (0 : NNReal))
      exact measurable_const
  let w : SourcePoint → Observation := fun s => observation false s.1 (.leaf none) s.2
  have hw : Measurable w := measurable_observation false (.leaf none)
  have hj : Q.joint false = fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1) := by
    funext p
    have hs := Q.normalization_pointwise 0 hc p.1.1 p.1.2 p.2
    have hd := Q.normalization_return_indicator 0 hc p.1.1 p.1.2 p.2
    dsimp only [RawRule.joint, RawRule.rawObservation, w, observation]
    rw [hs.2.1, hd, hs.2.2]
    rfl
  have hlaw : Q.fullLaw β false ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1)) := by
    unfold RawRule.fullLaw
    rw [hj]
  let C : CompletedRule (ULift.{u} Unit) := CompletedRule.fromRaw Q
  have hC : C.Lawful ((sourceLaw β).prod ν) := CompletedRule.fromRaw_completion_lawful Q ν hQ _ Measure.quasiMeasurePreserving_snd
  have hcap : C.TotalCap 0 := by intro s u; exact hc s.1 s.2 u
  have hclaw : C.fullLaw β false ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1)) := hlaw
  obtain ⟨F, _, _, hf⟩ := h β false ν C hC 0 hcap w hw hclaw
  obtain ⟨u, hu⟩ := hf.exists
  let z : Observation := ⟨.a false, none, false, 0⟩
  have hx := hu.2 z
  have hs := sourceLaw_observation β false (F u).val z
  have hbnd : fullMass β (lawWindow (F u).val) false (F u).val z ≤ 1 := by
    rw [← hs]
    exact measureReal_le_one
  norm_num [rejected, realize] at hx
  linarith

def evidence : Registration arena.{u} (type_of% (@CompletedRule.full_law_sections.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨β, ∅, Set.univ, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CompletedRule.full_law_sections.{u})
    (type_of% (realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedLawSections.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedLawSections.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "body", "arg", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletedLawSections

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
