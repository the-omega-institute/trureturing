import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open MeasureTheory
universe u

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : Bool, ℤ
  State _ := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ : Bool) (S : Spins) (e : ℤ),
    R.readout () ⟨φ, e⟩ S = Bool.xor (S e) (S (e + 1))

private theorem actual_law : arena.Law actual := by
  exact active_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h false (fun _ => false) 0
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@active_visible)) where
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
    refine ⟨⟨false, 0⟩, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    simp [actual, realize, visible]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@active_visible)
    (type_of% (realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
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

namespace ActualEndpoint

abbrev signature : Signature where
  Params := Σ _ : Bool, Bool
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Hidden
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => hidden p.2 S p.1.toInt) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Hidden.a false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j φ : Bool) (S : Spins), R.readout () ⟨j, φ⟩ S = targetClass j φ (S (targetIndex j φ))

private theorem actual_law : arena.Law actual := by
  exact @actual_endpoint

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false false (fun _ => true)
  simpa [rejected, realize, targetClass, targetIndex] using hb

def evidence : Registration arena (type_of% (@actual_endpoint)) where
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
    refine ⟨⟨false, false⟩, (fun _ => false), (fun _ => true), ?_⟩
    simp [actual, realize, _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.hidden]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_endpoint)
    (type_of% (realize signature (fun _ p S => hidden p.2 S p.1.toInt) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ActualEndpoint.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ActualEndpoint.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p S => hidden p.2 S p.1.toInt) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
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

end ActualEndpoint

namespace OppositePhase

abbrev signature : Signature where
  Params := Σ _ : Bool, ℤ
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => visible (!p.1) S p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ : Bool) (S : Spins) (t : ℤ), (t - φ.toInt) % 2 = 0 → R.readout () ⟨φ, t⟩ S = false

private theorem actual_law : arena.Law actual := by
  exact @opposite_phase_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false (fun _ => false) 0 (by decide)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@opposite_phase_visible)) where
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
    refine ⟨⟨false, 1⟩, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    simp [actual, realize, visible]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@opposite_phase_visible)
    (type_of% (realize signature (fun _ p S => visible (!p.1) S p.2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.OppositePhase.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.OppositePhase.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p S => visible (!p.1) S p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
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

end OppositePhase

namespace ConstantSource

abbrev signature : Signature where
  Params := Bool
  State p := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => fun _ => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ e => decide (e = 0)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ s : Bool) (t : ℤ), visible φ (R.readout () φ s) t = false

private theorem actual_law : arena.Law actual := by
  exact @constant_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false false 0
  simpa [rejected, realize, visible] using hb

def evidence : Registration arena (type_of% (@constant_visible)) where
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
    refine ⟨false, false, true, ?_⟩
    intro h
    have hb := congrFun h 0
    simpa [actual, realize] using hb

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@constant_visible)
    (type_of% (realize signature (fun _ _ s => fun _ => s) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ConstantSource.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ConstantSource.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ s => fun _ => s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"],
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

end ConstantSource

namespace ZeroComb

abbrev signature : Signature where
  Params := List ℤ
  State p := ℤ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨none, []⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool) (h : ∀ t ∈ ts, x t = false), R.readout () ts x = ⟨some (.a false), ts.map (fun t => (t, false))⟩

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.stopComb_all_zero

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [] (fun _ => false) (by simp)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.stopComb_all_zero)) where
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
    refine ⟨[0], (fun _ => false), (fun _ => true), ?_⟩
    intro h
    have hb := congrArg Execution.output h
    simpa [actual, realize, ReadTree.stopComb, ReadTree.run, Execution.prepend] using hb

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.stopComb_all_zero)
    (type_of% (realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ZeroComb.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ZeroComb.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
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

end ZeroComb

namespace Agreement

abbrev signature : Signature where
  Params := Σ _ : ReadTree, Bool
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => p.1.run (visible p.2 S)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨none, []⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (φ : Bool) (S S₀ : Spins) (h : ∀ i ∈ T.support, S i = S₀ i), R.readout () ⟨T, φ⟩ S = T.run (visible φ S₀)

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.source_run_eq_of_agree

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf (some (.a false))) false (fun _ => false) (fun _ => false) (by simp)
  simpa [rejected, realize, ReadTree.run] using hb

def evidence : Registration arena (type_of% (@ReadTree.source_run_eq_of_agree)) where
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
    refine ⟨⟨.read 0 (.leaf (some (.a false))) (.leaf (some (.a true))), false⟩, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    intro h
    have hb := congrArg Execution.output h
    simpa [actual, realize, ReadTree.run, visible, Execution.prepend] using hb

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.source_run_eq_of_agree)
    (type_of% (realize signature (fun _ p S => p.1.run (visible p.2 S)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.Agreement.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.Agreement.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p S => p.1.run (visible p.2 S)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
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

end Agreement

namespace PaidPrepend

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.paid) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (t : ℤ) (b : Bool) (v : Execution), R.readout () () (v.prepend t b) = v.paid + 1

private theorem actual_law : arena.Law actual := by
  exact @Execution.paid_prepend

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 false ⟨none, []⟩
  norm_num [rejected, realize, Execution.paid] at hb

def evidence : Registration arena (type_of% (@Execution.paid_prepend)) where
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
    refine ⟨(), ⟨none, []⟩, ⟨none, [(0, false)]⟩, ?_⟩
    norm_num [actual, realize, Execution.paid]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Execution.paid_prepend)
    (type_of% (realize signature (fun _ _ v => v.paid) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.PaidPrepend.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.PaidPrepend.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.paid) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
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

end PaidPrepend

namespace PaidCap

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.paid) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) {k : ℕ} (h : T.height ≤ k) (x : ℤ → Bool), R.readout () () (T.run x) ≤ k

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.paid_cap

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf none) (k := 0) (by decide) (fun _ => false)
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@ReadTree.paid_cap)) where
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
    refine ⟨(), ⟨none, []⟩, ⟨none, [(0, false)]⟩, ?_⟩
    norm_num [actual, realize, Execution.paid]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.paid_cap)
    (type_of% (realize signature (fun _ _ v => v.paid) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.PaidCap.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.PaidCap.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.paid) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
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

end PaidCap

namespace RecordAddresses

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (x : ℤ → Bool), ∀ a ∈ (T.run x).record, a.1 ∈ R.readout () () T

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.record_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.read 0 (.leaf none) (.leaf none)) (fun _ => false) (0, false) (by simp [ReadTree.run, Execution.prepend])
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.record_addresses)) where
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
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    simp [actual, realize, ReadTree.addresses]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.record_addresses)
    (type_of% (realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.RecordAddresses.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.RecordAddresses.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
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

end RecordAddresses

namespace LeafFromZero

abbrev signature : Signature where
  Params := Unit
  State p := Option Hidden
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ o => .leaf o) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .read 0 (.leaf none) (.leaf none)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (x : ℤ → Bool) (h : (T.run x).paid = 0), T = R.readout () () (T.run x).output

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.leaf_of_paid_zero

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf none) (fun _ => false) (by decide)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.leaf_of_paid_zero)) where
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
    refine ⟨(), none, some (.a false), ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.leaf_of_paid_zero)
    (type_of% (realize signature (fun _ _ o => .leaf o) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.LeafFromZero.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.LeafFromZero.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ o => .leaf o) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg"],
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

end LeafFromZero

namespace UnfoldHeight

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (k : ℕ) (u : U) (r : Record), R.readout () () (Q.unfold k u r) ≤ k

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.unfold_height.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  have hb := h (RawRule.realize T) 0 (ULift.up ()) []
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@RawRule.unfold_height.{u})) where
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
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.unfold_height.{u})
    (type_of% (realize signature (fun _ _ T => T.height) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.UnfoldHeight.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.UnfoldHeight.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.height) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
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

end UnfoldHeight

namespace NormalizeRealized

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (T : U → ReadTree) (k : ℕ) (u : U) (hT : R.readout () () (T u) ≤ k), (RawRule.realize T).normalize k u = T u

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.normalize_realize.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 0 (.leaf none) (.leaf none)
  have hb := h T 0 (ULift.up ()) (by change 0 ≤ 0; decide)
  change ReadTree.leaf none = ReadTree.read 0 (.leaf none) (.leaf none) at hb
  cases hb

def evidence : Registration arena.{u} (type_of% (@RawRule.normalize_realize.{u})) where
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
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.normalize_realize.{u})
    (type_of% (realize signature (fun _ _ T => T.height) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.NormalizeRealized.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.NormalizeRealized.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.height) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"],
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

end NormalizeRealized

namespace RealizedCap

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (T : U → ReadTree) (k : ℕ) (hT : ∀ u, R.readout () () (T u) ≤ k), (RawRule.realize T).TotalCap k

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.realize_cap.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 0 (.leaf none) (.leaf none)
  have hb := h T 0 (fun _ => by change 0 ≤ 0; decide)
  have ht := ((RawRule.realize T).normalization_pointwise 0 hb false (fun _ => false) (ULift.up ())).1.2
  change EventKind.read 0 = EventKind.terminal none at ht
  cases ht

def evidence : Registration arena.{u} (type_of% (@RawRule.realize_cap.{u})) where
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
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.realize_cap.{u})
    (type_of% (realize signature (fun _ _ T => T.height) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.RealizedCap.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.RealizedCap.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.height) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "body", "fn", "arg"],
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

end RealizedCap

namespace PointwiseOutput

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Hidden
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.output) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k) (φ : Bool) (S : Spins) (u : U), let v := (Q.normalize k u).run (visible φ S)
    Q.Completes u (visible φ S) v ∧ Q.output u (visible φ S) = R.readout () () v ∧ Q.paidCount u (visible φ S) = v.paid

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.normalization_pointwise.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hs := Q.normalization_pointwise 0 hc false (fun _ => false) (ULift.up ())
  have ho := hs.2.1
  change Q.output (ULift.up ()) (visible false (fun _ => false)) = some (.a false) at ho
  have hb := (h Q 0 hc false (fun _ => false) (ULift.up ())).2.1
  rw [ho] at hb
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.normalization_pointwise.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨some (.a false), []⟩, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.normalization_pointwise.{u})
    (type_of% (realize signature (fun _ _ v => v.output) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.PointwiseOutput.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.PointwiseOutput.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.output) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"],
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

end PointwiseOutput

namespace UnfoldTerminal

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Hidden
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.output) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (u : U) (x : ℤ → Bool) (k n : ℕ) (r : Record)
    (hr : Q.readPrefix u x n = some r)
    (hc : ∀ m s, Q.readPrefix u x m = some s → m ≤ n + k),
    let v := (Q.unfold k u r).run x
    Q.readPrefix u x (n + v.paid) = some (r ++ v.record) ∧
      Q.next u (r ++ v.record) = .terminal (R.readout () () v)

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.unfold_correct.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : RawRule (ULift.{u} Unit) := ⟨(fun _ _ => .terminal (some (.a false))), (fun _ _ => 0)⟩
  have hc : ∀ m s, Q.readPrefix (ULift.up ()) (fun _ => false) m = some s → m ≤ 0 + 0 := by
    intro m s hs
    cases m with
    | zero => omega
    | succ m => simp [RawRule.readPrefix, Q] at hs
  have hb := (h Q (ULift.up ()) (fun _ => false) 0 0 [] rfl hc).2
  simpa [rejected, realize, Q] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.unfold_correct.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨some (.a false), []⟩, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.unfold_correct.{u})
    (type_of% (realize signature (fun _ _ v => v.output) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.UnfoldTerminal.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.UnfoldTerminal.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.output) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"],
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

end UnfoldTerminal

namespace ReturnIndicator

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.returned) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k) (φ : Bool) (S : Spins) (u : U), decide (Q.returnTime u (visible φ S) < ⊤) = R.readout () () ((Q.normalize k u).run (visible φ S))

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.normalization_return_indicator.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hs := Q.normalization_pointwise 0 hc false (fun _ => false) (ULift.up ())
  have ho := hs.2.1
  change Q.output (ULift.up ()) (visible false (fun _ => false)) = some (.a false) at ho
  have hr := Q.normalization_return_indicator 0 hc false (fun _ => false) (ULift.up ())
  have hb := h Q 0 hc false (fun _ => false) (ULift.up ())
  change decide (Q.returnTime (ULift.up ()) (visible false (fun _ => false)) < ⊤) = true at hr
  rw [hr] at hb
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.normalization_return_indicator.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨some (.a false), []⟩, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.normalization_return_indicator.{u})
    (type_of% (realize signature (fun _ _ v => v.returned) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ReturnIndicator.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.ReturnIndicator.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.returned) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"],
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

end ReturnIndicator

namespace CompletedOutput

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Hidden
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.output) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : CompletedRule U) (k : ℕ) (hc : Q.TotalCap k) (p : SourcePoint × U),
    let v := (Q.normalize k p).run (visible p.1.1 p.1.2)
    (Q.atSource p.1).Completes p.2 (visible p.1.1 p.1.2) v ∧
      (Q.atSource p.1).output p.2 (visible p.1.1 p.1.2) = R.readout () () v ∧
      (Q.atSource p.1).paidCount p.2 (visible p.1.1 p.1.2) = v.paid

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.completed_normalization_execution.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : CompletedRule (ULift.{u} Unit) := CompletedRule.fromRaw (RawRule.realize T)
  have hc : Q.TotalCap 0 := by
    intro s u
    exact RawRule.realize_cap T 0 (fun _ => by rfl) s.1 s.2 u
  let p : SourcePoint × ULift.{u} Unit := ((false, fun _ => false), ULift.up ())
  have hs := (Q.completed_normalization_execution 0 hc p).2.1
  have hb := (h Q 0 hc p).2.1
  change (Q.atSource p.1).output p.2 (visible p.1.1 p.1.2) = some (.a false) at hs
  rw [hs] at hb
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@CompletedRule.completed_normalization_execution.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨some (.a false), []⟩, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CompletedRule.completed_normalization_execution.{u})
    (type_of% (realize signature (fun _ _ v => v.output) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletedOutput.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletedOutput.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.output) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"],
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

end CompletedOutput

namespace FormalCombRuns

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.formalRuns) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [⟨none, []⟩]) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ts : List ℤ), ∀ v ∈ R.readout () () (ReadTree.stopComb ts),
      v.output = some (.a false) ∧ v.paid = ts.length ∨
      v.output = some (.a true) ∧ 1 ≤ v.paid ∧ v.paid ≤ ts.length

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.stopComb_formal_outcomes

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [] ⟨none, []⟩ (by simp [rejected, realize])
  simpa using hb

def evidence : Registration arena (type_of% (@ReadTree.stopComb_formal_outcomes)) where
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
    refine ⟨(), .leaf none, .leaf (some (.a false)), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.stopComb_formal_outcomes)
    (type_of% (realize signature (fun _ _ T => T.formalRuns) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.FormalCombRuns.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.FormalCombRuns.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.formalRuns) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "domain", "fn", "arg"],
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

end FormalCombRuns

namespace FiniteReturn

abbrev signature : Signature where
  Params := Unit
  State p := Option Hidden
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ o => o.isSome) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (u : U) (x : ℤ → Bool), Q.returnTime u x < ⊤ ↔ R.readout () () (Q.output u x) = true

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.finite_return_iff.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hs := Q.normalization_pointwise 0 hc false (fun _ => false) (ULift.up ())
  have ho := hs.2.1
  change Q.output (ULift.up ()) (visible false (fun _ => false)) = some (.a false) at ho
  have hr : Q.returnTime (ULift.up ()) (visible false (fun _ => false)) < ⊤ := (Q.finite_return_iff _ _).2 (by rw [ho]; rfl)
  have hb := (h Q (ULift.up ()) (visible false (fun _ => false))).1 hr
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.finite_return_iff.{u})) where
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
    refine ⟨(), none, some (.a false), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.finite_return_iff.{u})
    (type_of% (realize signature (fun _ _ o => o.isSome) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.FiniteReturn.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.FiniteReturn.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ o => o.isSome) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"],
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

end FiniteReturn

namespace CompletedRecord

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Record
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.record) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (u : U) (x : ℤ → Bool) {v : Execution} (hv : Q.Completes u x v) {n : ℕ} {r : Record}
    (hr : Q.readPrefix u x n = some r), ∀ a ∈ r, a ∈ R.readout () () v

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.completes_record_subset.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 0 (.leaf none) (.leaf none)
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  let x : ℤ → Bool := fun _ => false
  let v : Execution := ⟨none, [(0, false)]⟩
  have hv : Q.Completes (ULift.up ()) x v := by constructor <;> rfl
  have hb := h Q (ULift.up ()) x (v := v) hv (n := 1) (r := [(0, false)]) rfl (0, false) (by simp)
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.completes_record_subset.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨none, [(0, false)]⟩, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.completes_record_subset.{u})
    (type_of% (realize signature (fun _ _ v => v.record) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletedRecord.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletedRecord.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ v => v.record) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
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

end CompletedRecord

namespace CompletionVersion

abbrev signature : Signature where
  Params := Σ V : Type u, V
  State p := p.1 → ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ _ _ => .read 0 (.leaf none) (.leaf none)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (ν : Measure U) (hQ : Q.CompletionLawful ν) (k : ℕ), ∃ F : U → {T : ReadTree // T.height ≤ k}, Measurable F ∧ ∀ᵐ u ∂ν, R.readout () ⟨U, u⟩ (Q.normalize k) = (F u).val

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.completion_normalization_version.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
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
  obtain ⟨F, _, he⟩ := h Q ν hQ 0
  obtain ⟨u, hu⟩ := he.exists
  have hh := (F u).property
  have heq : ReadTree.read 0 (.leaf none) (.leaf none) = (F u).val := by simpa [rejected, realize] using hu
  rw [← heq] at hh
  norm_num [ReadTree.height] at hh

def evidence : Registration arena.{u} (type_of% (@RawRule.completion_normalization_version.{u})) where
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
    refine ⟨⟨ULift.{u} Unit, ULift.up ()⟩, (fun _ => ReadTree.leaf none), (fun _ => ReadTree.leaf (some (.a false))), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.completion_normalization_version.{u})
    (type_of% (realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletionVersion.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletionVersion.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 7],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletionVersion

namespace CompletionBridge

abbrev signature : Signature where
  Params := Σ V : Type u, V
  State p := p.1 → ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ _ _ => .read 0 (.leaf none) (.leaf none)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (ν : Measure U) (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k), ∃ F : U → {T : ReadTree // T.height ≤ k}, Measurable F ∧
      (∀ᵐ u ∂ν, R.readout () ⟨U, u⟩ (Q.normalize k) = (F u).val) ∧
      ∀ᵐ u ∂ν, ∀ (φ : Bool) (S : Spins), let v := (F u).val.run (visible φ S)
        Q.Completes u (visible φ S) v ∧ Q.output u (visible φ S) = v.output ∧ Q.paidCount u (visible φ S) = v.paid

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.completion_normalization_bridge.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
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
  obtain ⟨F, _, he, _⟩ := h Q ν hQ 0 hc
  obtain ⟨u, hu⟩ := he.exists
  have hh := (F u).property
  have heq : ReadTree.read 0 (.leaf none) (.leaf none) = (F u).val := by simpa [rejected, realize] using hu
  rw [← heq] at hh
  norm_num [ReadTree.height] at hh

def evidence : Registration arena.{u} (type_of% (@RawRule.completion_normalization_bridge.{u})) where
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
    refine ⟨⟨ULift.{u} Unit, ULift.up ()⟩, (fun _ => ReadTree.leaf none), (fun _ => ReadTree.leaf (some (.a false))), ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@RawRule.completion_normalization_bridge.{u})
    (type_of% (realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletionBridge.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization.CompletionBridge.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization,
    definition := none,
    coordinates := #[0, 8],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end CompletionBridge

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
