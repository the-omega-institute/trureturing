import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section


namespace SpinMass

abbrev signature : Signature where
  Params := Σ _ : Bias, Finset ℤ
  State p := Set Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (q : ℤ) (hq : q ∈ V) (s : Bool), R.readout () ⟨β, V⟩ {S | S q = s} = β.π s

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.spin_prob

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β {0} 0 (by simp) false
  norm_num [rejected, realize, Bias.π, β] at hb

def evidence : Registration arena (type_of% (@SpinWindow.spin_prob)) where
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
    refine ⟨⟨β, ∅⟩, ∅, Set.univ, ?_⟩
    change SpinWindow.prob β ∅ ∅ ≠ SpinWindow.prob β ∅ Set.univ
    rw [SpinWindow.prob_univ]
    simp [SpinWindow.prob, FiniteSpinLaw.mass]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SpinWindow.spin_prob)
    (type_of% (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.SpinMass.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.SpinMass.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
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

end SpinMass

namespace CombOutput

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
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool),
    (R.readout () ts x).output = some (.a false) ∧
      ((ReadTree.stopComb ts).run x).paid = ts.length ∨
    ((ReadTree.stopComb ts).run x).output = some (.a true) ∧
      1 ≤ ((ReadTree.stopComb ts).run x).paid ∧ ((ReadTree.stopComb ts).run x).paid ≤ ts.length

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.stopComb_outcomes

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [] (fun _ => false)
  simpa [rejected, realize, ReadTree.stopComb, ReadTree.run] using hb

def evidence : Registration arena (type_of% (@ReadTree.stopComb_outcomes)) where
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
    (@ReadTree.stopComb_outcomes)
    (type_of% (realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.CombOutput.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.CombOutput.evidence,
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
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

end CombOutput

namespace ZeroFinal

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
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool), ReadTree.ZeroReplies ts ts.length x ↔ (R.readout () ts x).output = some (.a false) ∧ ((ReadTree.stopComb ts).run x).paid = ts.length

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.zero_prefix_final

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h [] (fun _ => false)).1 (by simp [ReadTree.ZeroReplies])
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.zero_prefix_final)) where
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
    (@ReadTree.zero_prefix_final)
    (type_of% (realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.ZeroFinal.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.ZeroFinal.evidence,
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg"],
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

end ZeroFinal

namespace EdgeZeroReplies

abbrev signature : Signature where
  Params := Bool
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ φ S => visible φ S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (φ : Bool) (S : Spins) (r : ℕ), ReadTree.ZeroReplies (es.map (fun e => 2 * e + φ.toInt)) r (R.readout () φ S) ↔ ∀ e ∈ (es.take r).toFinset, S e = S (e + 1)

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.edge_zero_prefix

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h [0] false (fun _ => false) 1).2 (by simp)
  simpa [ReadTree.ZeroReplies, rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.edge_zero_prefix)) where
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
    refine ⟨false, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    intro h
    have hb := congrFun h 0
    norm_num [actual, realize, visible] at hb

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.edge_zero_prefix)
    (type_of% (realize signature (fun _ φ S => visible φ S) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.EdgeZeroReplies.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.EdgeZeroReplies.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ φ S => visible φ S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"],
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

end EdgeZeroReplies

namespace CombSupport

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
  realize signature (fun _ _ T => T.support) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (φ : Bool), ∀ e ∈ es, e ∈ R.readout () () (ReadTree.edgeComb es φ) ∧ e + 1 ∈ (ReadTree.edgeComb es φ).support

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.edgeComb_support

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h [0] false 0 (by simp)).1
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.edgeComb_support)) where
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
    (@ReadTree.edgeComb_support)
    (type_of% (realize signature (fun _ _ T => T.support) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.CombSupport.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.CombSupport.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ T => T.support) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
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

end CombSupport

namespace RemoteSourceMass

abbrev signature : Signature where
  Params := Σ _ : Bias, Σ _ : Bool, ReadTree
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (j : Bool) (r : ℕ) (T : ReadTree), (sourceLaw β).real {s | ∃ a ∈ (T.run (visible s.1 s.2)).record, Far j r a.1} = R.readout () ⟨β, j, T⟩ r

private theorem actual_law : arena.Law actual := by
  exact @sourceLaw_remote

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β false 0 (.leaf none)
  norm_num [rejected, realize, ReadTree.run] at hb

def evidence : Registration arena (type_of% (@sourceLaw_remote)) where
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
    let T : ReadTree := .read 0 (.leaf none) (.leaf none)
    have he0 (φ : Bool) : remoteEvent T false 0 φ = Set.univ := by
      ext S
      cases hv : visible φ S 0 <;> simp [remoteEvent, T, ReadTree.run, hv, Execution.prepend, Far]
    have he1 (φ : Bool) : remoteEvent T false 1 φ = ∅ := by
      ext S
      cases hv : visible φ S 0 <;> simp [remoteEvent, T, ReadTree.run, hv, Execution.prepend, Far]
    refine ⟨⟨β, false, T⟩, 0, 1, ?_⟩
    change remoteMass β (lawWindow T) false 0 T ≠ remoteMass β (lawWindow T) false 1 T
    have hz : SpinWindow.prob β (lawWindow T) ∅ = 0 := by simp [SpinWindow.prob, FiniteSpinLaw.mass]
    simp [remoteMass, he0, he1, hz]


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceLaw_remote)
    (type_of% (realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.RemoteSourceMass.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.RemoteSourceMass.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
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

end RemoteSourceMass

namespace MassPhaseA

abbrev signature : Signature where
  Params := Σ _ : Bias, Finset ℤ
  State p := Set Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j s : Bool) (T : ReadTree) (o : Option Hidden) (n : ℕ), fullMass β V j T ⟨.a s, o, o.isSome, n⟩ = R.readout () ⟨β, V⟩ {S | S (targetIndex j j) = s ∧ (T.run (visible j S)).output = o ∧ (T.run (visible j S)).paid = n} / 2

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.fullMass_a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ false false (.leaf none) (some (.a false)) 0
  have hs := ReadTree.fullMass_a β ∅ false false (.leaf none) (some (.a false)) 0
  norm_num [ReadTree.run, SpinWindow.prob, FiniteSpinLaw.mass] at hs
  norm_num [rejected, realize] at hb
  rw [hs] at hb
  norm_num at hb

def evidence : Registration arena (type_of% (@ReadTree.fullMass_a)) where
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
    refine ⟨⟨β, ∅⟩, ∅, Set.univ, ?_⟩
    change SpinWindow.prob β ∅ ∅ ≠ SpinWindow.prob β ∅ Set.univ
    rw [SpinWindow.prob_univ]
    simp [SpinWindow.prob, FiniteSpinLaw.mass]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.fullMass_a)
    (type_of% (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.MassPhaseA.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.MassPhaseA.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"],
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

end MassPhaseA

namespace MassPhaseB

abbrev signature : Signature where
  Params := Σ _ : Bias, Finset ℤ
  State p := Set Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j s : Bool) (T : ReadTree) (o : Option Hidden) (n : ℕ), fullMass β V j T ⟨.b s, o, o.isSome, n⟩ = R.readout () ⟨β, V⟩ {S | S j.toInt = s ∧ (T.run (visible (!j) S)).output = o ∧ (T.run (visible (!j) S)).paid = n} / 2

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.fullMass_b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ false false (.leaf none) (some (.a false)) 0
  have hs := ReadTree.fullMass_b β ∅ false false (.leaf none) (some (.a false)) 0
  norm_num [ReadTree.run, SpinWindow.prob, FiniteSpinLaw.mass] at hs
  norm_num [rejected, realize] at hb
  rw [hs] at hb
  norm_num at hb

def evidence : Registration arena (type_of% (@ReadTree.fullMass_b)) where
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
    refine ⟨⟨β, ∅⟩, ∅, Set.univ, ?_⟩
    change SpinWindow.prob β ∅ ∅ ≠ SpinWindow.prob β ∅ Set.univ
    rw [SpinWindow.prob_univ]
    simp [SpinWindow.prob, FiniteSpinLaw.mass]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.fullMass_b)
    (type_of% (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.MassPhaseB.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.MassPhaseB.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"],
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

end MassPhaseB

namespace PrefixAntitone

abbrev signature : Signature where
  Params := Unit
  State p := Finset ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) {r t : ℕ} (hrt : r ≤ t), R.readout () () (es.take t).toFinset ⊆ SpinWindow.zeroEdges (es.take r).toFinset

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_prefix_antitone

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Spins := fun e => decide (e = 0)
  have hb := h [0] (r := 1) (t := 1) (by decide) (by trivial : S ∈ rejected.readout () () (([0] : List ℤ).take 1).toFinset)
  have hc := hb 0 (by simp)
  norm_num [S] at hc

def evidence : Registration arena (type_of% (@SpinWindow.zero_prefix_antitone)) where
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
    refine ⟨(), (∅ : Finset ℤ), {0}, ?_⟩
    let S : Spins := fun e => decide (e = 0)
    intro he
    have hm : S ∈ actual.readout () () ∅ := by simp [actual, realize, SpinWindow.zeroEdges]
    rw [he] at hm
    have hc := hm 0 (by simp)
    norm_num [S] at hc

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SpinWindow.zero_prefix_antitone)
    (type_of% (realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.PrefixAntitone.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.PrefixAntitone.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
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

end PrefixAntitone

namespace EdgeDifference

abbrev signature : Signature where
  Params := Unit
  State p := Finset ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (φ : Bool) (r : ℕ) (hr : r < es.length),
    R.readout () () (es.take r).toFinset \ SpinWindow.zeroEdges (es.take (r + 1)).toFinset =
      {S | ((ReadTree.edgeComb es φ).run (visible φ S)).output = some (.a true) ∧
        ((ReadTree.edgeComb es φ).run (visible φ S)).paid = r + 1}

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_edge_difference

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Spins := fun e => decide (e = 0)
  have hb := h [0] false 0 (by decide)
  have hm : S ∈ {S | ((ReadTree.edgeComb [0] false).run (visible false S)).output = some (.a true) ∧ ((ReadTree.edgeComb [0] false).run (visible false S)).paid = 0 + 1} := by
    norm_num [S, ReadTree.edgeComb, ReadTree.stopComb, ReadTree.run, visible, Execution.prepend, Execution.paid]
  rw [← hb] at hm
  simpa [rejected, realize] using hm

def evidence : Registration arena (type_of% (@SpinWindow.zero_edge_difference)) where
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
    refine ⟨(), (∅ : Finset ℤ), {0}, ?_⟩
    let S : Spins := fun e => decide (e = 0)
    intro he
    have hm : S ∈ actual.readout () () ∅ := by simp [actual, realize, SpinWindow.zeroEdges]
    rw [he] at hm
    have hc := hm 0 (by simp)
    norm_num [S] at hc

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SpinWindow.zero_edge_difference)
    (type_of% (realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.EdgeDifference.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.EdgeDifference.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
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

end EdgeDifference

namespace RemotePrefix

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
  Law R := ∀ (j : Bool) (r : ℕ) (pre : List ℤ) (t : ℤ) (post : List ℤ)
    (hn : ∀ a ∈ pre, ¬Far j r a) (hf : Far j r t) (x : ℤ → Bool),
    (∃ a ∈ ((R.readout () () (pre ++ t :: post)).run x).record, Far j r a.1) ↔ ReadTree.ZeroReplies pre pre.length x

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.remote_iff_first_prefix

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false 0 [] 0 [] (by simp) (by norm_num [Far]) (fun _ => false)
  simpa [rejected, realize, ReadTree.run, ReadTree.ZeroReplies] using hb

def evidence : Registration arena (type_of% (@ReadTree.remote_iff_first_prefix)) where
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
    (@ReadTree.remote_iff_first_prefix)
    (type_of% (realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.RemotePrefix.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.RemotePrefix.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg"],
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

end RemotePrefix

namespace OppositeRemote

abbrev signature : Signature where
  Params := Σ _ : Bool, ℕ
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p T => remoteEvent T p.1 p.2 p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (j : Bool) (r : ℕ) (hf : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j r t), R.readout () ⟨j, r⟩ (ReadTree.edgeComb es (!j)) = Set.univ

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.edgeComb_opposite_remote

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [0] false 0 ⟨1, by simp, by norm_num [Far]⟩
  have he : (∅ : Set Spins) = Set.univ := by simpa [rejected, realize] using hb
  have hc := congrArg (fun E : Set Spins => (fun _ => false) ∈ E) he
  simpa using hc


def evidence : Registration arena (type_of% (@ReadTree.edgeComb_opposite_remote)) where
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
    refine ⟨⟨false, 0⟩, .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    intro he
    have hm : (fun _ => false) ∈ actual.readout () ⟨false, 0⟩ (.read 0 (.leaf none) (.leaf none)) := by
      change ∃ a ∈ ((ReadTree.read 0 (.leaf none) (.leaf none)).run (visible false (fun _ => false))).record, Far false 0 a.1
      refine ⟨(0, false), ?_, by norm_num [Far]⟩
      simp [ReadTree.run, Execution.prepend, visible]
    rw [← he] at hm
    simpa [actual, realize, remoteEvent, ReadTree.run] using hm


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ReadTree.edgeComb_opposite_remote)
    (type_of% (realize signature (fun _ p T => remoteEvent T p.1 p.2 p.1) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.OppositeRemote.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.OppositeRemote.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p T => remoteEvent T p.1 p.2 p.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end OppositeRemote

namespace SourceObservationMass

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
  Law R := ∀ (β : Bias) (j : Bool) (T : ReadTree) (z : Observation), R.readout () β {s | observation j s.1 T s.2 = z} = fullMass β (lawWindow T) j T z

private theorem actual_law : arena.Law actual := by
  exact @sourceLaw_observation

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let z : Observation := ⟨.a false, some (.a false), true, 0⟩
  have hb := h β false (.leaf none) z
  have hs := sourceLaw_observation β false (.leaf none) z
  have he : {s : SourcePoint | observation false s.1 (.leaf none) s.2 = z} = ∅ := by
    ext s
    simp [observation, ReadTree.run, Execution.returned, z]
  rw [he, measureReal_empty] at hs
  rw [← hs] at hb
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@sourceLaw_observation)) where
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
    (@sourceLaw_observation)
    (type_of% (realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.SourceObservationMass.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.SourceObservationMass.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0],
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

end SourceObservationMass

namespace FiniteRigidity

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
  Law R := ∀ (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (T : ReadTree) (hh : T.height ≤ k) (hlaw : HasStoppingLaw β (lawWindow T) j k T),
    ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      T = R.readout () () (es.map (fun e => 2 * e + (!j).toInt)) ∧ es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k

private theorem actual_law : arena.Law actual := by
  exact @finite_full_law_forces_stopping_path

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  obtain ⟨es, _, _, L, he, _, _⟩ := h β false 1 (by decide) T hh hlaw
  change ReadTree.read 3 (.leaf (some (.a false))) (.leaf (some (.a true))) = ReadTree.leaf none at he
  cases he

def evidence : Registration arena (type_of% (@finite_full_law_forces_stopping_path)) where
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
    (@finite_full_law_forces_stopping_path)
    (type_of% (realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.FiniteRigidity.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.FiniteRigidity.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "fn", "arg", "arg"],
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

end FiniteRigidity

namespace ZeroPrefixMass

abbrev signature : Signature where
  Params := Σ _ : Bias, Finset ℤ
  State p := Set Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j : Bool) (es : List ℤ) (hq : j.toInt ∈ V) (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j))) (r : ℕ) (hr : r ≤ es.length), R.readout () ⟨β, V⟩ (SpinWindow.zeroEdges (es.take r).toFinset) = β.T (r + 1)

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_prefix_mass

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  have hq : false.toInt ∈ lawWindow T := by simp [lawWindow]
  have he : (witnessEdges false 1).length = 1 := by simp [witnessEdges]
  have hl : HasStoppingLaw β (lawWindow T) false (witnessEdges false 1).length (ReadTree.edgeComb (witnessEdges false 1) (!false)) := by simpa [he, T, witnessTree] using hlaw
  have hb := h β (lawWindow T) false (witnessEdges false 1) hq hl 0 (by omega)
  norm_num [rejected, realize, Bias.T] at hb

def evidence : Registration arena (type_of% (@SpinWindow.zero_prefix_mass)) where
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
    refine ⟨⟨β, ∅⟩, ∅, Set.univ, ?_⟩
    change SpinWindow.prob β ∅ ∅ ≠ SpinWindow.prob β ∅ Set.univ
    rw [SpinWindow.prob_univ]
    simp [SpinWindow.prob, FiniteSpinLaw.mass]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SpinWindow.zero_prefix_mass)
    (type_of% (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.ZeroPrefixMass.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.ZeroPrefixMass.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
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

end ZeroPrefixMass

namespace FiniteRemote

abbrev signature : Signature where
  Params := Σ _ : Bias, Σ _ : Bool, ReadTree
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (T : ReadTree) (hh : T.height ≤ k) (hlaw : HasStoppingLaw β (lawWindow T) j k T),
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ R.readout () ⟨β, j, T⟩ (2 * k + 1) = (1 + β.T m) / 2 ∧
      (1 + β.T k) / 2 ≤ remoteMass β (lawWindow T) j (2 * k + 1) T

private theorem actual_law : arena.Law actual := by
  exact @finite_remote_read_section

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  obtain ⟨m, hm, hm₁, he, _⟩ := h β false 1 (by decide) T hh hlaw
  have hm : m = 1 := by omega
  subst m
  rw [β.T_one] at he
  norm_num [rejected, realize] at he

def evidence : Registration arena (type_of% (@finite_remote_read_section)) where
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
    let T : ReadTree := .read 0 (.leaf none) (.leaf none)
    have he0 (φ : Bool) : remoteEvent T false 0 φ = Set.univ := by
      ext S
      cases hv : visible φ S 0 <;> simp [remoteEvent, T, ReadTree.run, hv, Execution.prepend, Far]
    have he1 (φ : Bool) : remoteEvent T false 1 φ = ∅ := by
      ext S
      cases hv : visible φ S 0 <;> simp [remoteEvent, T, ReadTree.run, hv, Execution.prepend, Far]
    refine ⟨⟨β, false, T⟩, 0, 1, ?_⟩
    change remoteMass β (lawWindow T) false 0 T ≠ remoteMass β (lawWindow T) false 1 T
    have hz : SpinWindow.prob β (lawWindow T) ∅ = 0 := by simp [SpinWindow.prob, FiniteSpinLaw.mass]
    simp [remoteMass, he0, he1, hz]


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_remote_read_section)
    (type_of% (realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.FiniteRemote.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.FiniteRemote.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 1, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"],
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

end FiniteRemote

namespace CappedLaw

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
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (T : ReadTree) (hh : T.height ≤ k), HasStoppingLaw β V j k T ↔ ∀ z : CappedObservation k, fullMass β V j T z.val = R.readout () ⟨β, k⟩ z.val

private theorem actual_law : arena.Law actual := by
  exact @hasStoppingLaw_iff_capped

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  let z : CappedObservation 1 := ⟨⟨.a false, none, false, 0⟩, by decide, rfl⟩
  have hb := ((h β (lawWindow T) false 1 T hh).1 hlaw) z
  have hs := sourceLaw_observation β false T z.val
  have hbnd : fullMass β (lawWindow T) false T z.val ≤ 1 := by rw [← hs]; exact measureReal_le_one
  norm_num [rejected, realize] at hb
  linarith

def evidence : Registration arena (type_of% (@hasStoppingLaw_iff_capped)) where
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
    (@hasStoppingLaw_iff_capped)
    (type_of% (realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.CappedLaw.audit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore.CappedLaw.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg"],
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

end CappedLaw

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
