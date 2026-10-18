import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
noncomputable section
universe u

namespace RealizedLaw

abbrev signature : Signature where
  Params := Σ U : Type u, Σ _ : U → ReadTree, Bool
  State p := SourcePoint × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 × Observation
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p z => selectorJoint p.2.2 p.2.1 z) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ z => (z.2, ⟨.a false, none, false, 0⟩)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law A := ∀ {U : Type u} [MeasurableSpace U] (T : U → ReadTree) (k : ℕ)
    (hT : ∀ u, (T u).height ≤ k) (β : Bias) (j : Bool) (ν : Measure U),
    (RawRule.realize T).fullLaw β j ν =
      ((sourceLaw β).prod ν).map (fun z => A.readout () ⟨U, T, j⟩ z)

private theorem actual_law : arena.{u}.Law actual := @RawRule.fullLaw_realize.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  have hc : ∀ u, (T u).height ≤ 0 := fun _ => by rfl
  have hb := h T 0 hc β false ν
  have ha := RawRule.fullLaw_realize T 0 hc β false ν
  have he := ha.symm.trans hb
  have hE : MeasurableSet {z : ULift.{u} Unit × Observation | z.2.output = some (.a false)} :=
    (Set.to_countable _).measurableSet
  have hx := congrArg (fun μ : Measure (ULift.{u} Unit × Observation) =>
    μ {z | z.2.output = some (.a false)}) he
  dsimp only [rejected, realize] at hx
  rw [Measure.map_apply (measurable_selectorJoint false T measurable_const) hE,
    Measure.map_apply (measurable_snd.prodMk measurable_const) hE] at hx
  simpa [rejected, realize, selectorJoint, T, observation, ReadTree.run, Set.preimage] using hx

def evidence : Registration arena.{u} (type_of% (@RawRule.fullLaw_realize.{u})) where
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
    refine ⟨⟨ULift.{u} Unit, (fun _ => .leaf none), false⟩,
      ((false, fun _ => false), ULift.up ()), ((false, fun _ => true), ULift.up ()), ?_⟩
    intro he
    have hx := congrArg (fun z : ULift.{u} Unit × Observation => z.2.endpoint) he
    norm_num [actual, realize, selectorJoint, observation, _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.hidden] at hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.fullLaw_realize.{u})
    (type_of% (realize signature.{u} (fun _ p z => selectorJoint p.2.2 p.2.1 z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RealizedLaw.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.RealizedLaw.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p z => selectorJoint p.2.2 p.2.1 z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[0, 2, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := true,
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

end RealizedLaw

namespace CompletedJoint

abbrev signature : Signature where
  Params := Σ U : Type u, Σ _ : Bool, SourcePoint × U
  State _ := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Observation
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p T => observation p.2.1 p.2.2.1.1 T p.2.2.1.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => ⟨.a false, some (.a false), true, 0⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law A := ∀ {U : Type u} [MeasurableSpace U] (Q : CompletedRule U) (k : ℕ)
    (hc : Q.TotalCap k) (j : Bool) (p : SourcePoint × U),
    Q.completedJoint j p = (p.2, A.readout () ⟨U, j, p⟩ (Q.normalize k p))

private theorem actual_law : arena.{u}.Law actual := @CompletedRule.completed_joint_normalize.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  let Q := CompletedRule.fromRaw (RawRule.realize T)
  have hc : Q.TotalCap 0 := fun s u => RawRule.realize_cap T 0 (fun _ => by rfl) s.1 s.2 u
  let p : SourcePoint × ULift.{u} Unit := ((false, fun _ => false), ULift.up ())
  have hb := h Q 0 hc false p
  have ha := CompletedRule.completed_joint_normalize Q 0 hc false p
  have hx := congrArg (fun z : ULift.{u} Unit × Observation => z.2.output) (ha.symm.trans hb)
  change (none : Option Hidden) = some (.a false) at hx
  contradiction

def evidence : Registration arena.{u} (type_of% (@CompletedRule.completed_joint_normalize.{u})) where
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
    refine ⟨⟨ULift.{u} Unit, false, ((false, fun _ => false), ULift.up ())⟩,
      .leaf none, .leaf (some (.a false)), ?_⟩
    intro he
    have hx := congrArg Observation.output he
    simp [actual, realize, observation, ReadTree.run] at hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CompletedRule.completed_joint_normalize.{u})
    (type_of% (realize signature.{u} (fun _ p T => observation p.2.1 p.2.2.1.1 T p.2.2.1.2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedJoint.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw.CompletedJoint.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p T => observation p.2.1 p.2.2.1.1 T p.2.2.1.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw,
    definition := none,
    coordinates := #[0, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletedJoint

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
