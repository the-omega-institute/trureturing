import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
universe u v

structure System where
  State : Type u
  Letter : Type v
  states : Fintype State
  letters : Fintype Letter
  joint : @FiniteMarkovKernel State (Letter × State) (@instFintypeProd Letter State letters states)

attribute [instance] System.states System.letters

def wordSignature : Signature where
  Params := System.{u,v}
  State M := M.State × List M.Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ M z => wordProb M.joint z.1 z.2) (fun e => nomatch e)

def soundArena : Arena where
  signature := wordSignature
  Law R := ∀ (M : System.{u,v}) n x x', residual M.joint n x x' →
    ∀ w : List M.Letter, w.length ≤ n → R.readout () M (x,w) = R.readout () M (x',w)

private theorem sound_bridge :
    (type_of% (@residual_sound.{u,v})) ↔ soundArena.Law wordActual := by
  constructor
  · intro h M n x x' hr w hw
    exact h M.joint n x x' hr w hw
  · intro h S Y fs fy K n x x' hr w hw
    exact h ⟨S,Y,fs,fy,K⟩ n x x' hr w hw

def archiveSignature : Signature where
  Params := System.{u,v}
  State M := M.State × List M.Letter × (Σ n, Experiment M.Letter n)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def archiveActual : Realization archiveSignature :=
  realize archiveSignature (fun role M z =>
    if role then archiveProb M.joint z.2.2.2 z.1 z.2.1 else wordProb M.joint z.1 z.2.1)
    (fun e => nomatch e)

def stoppingArena : Arena where
  signature := archiveSignature
  Law R := ∀ (M : System.{u,v}) n x x',
    (∀ w : List M.Letter, w.length ≤ n →
      R.readout false M (x,w,⟨0,.stop⟩) = R.readout false M (x',w,⟨0,.stop⟩)) ↔
    (∀ k, k ≤ n → ∀ E : Experiment M.Letter k, ∀ w,
      R.readout true M (x,w,⟨k,E⟩) = R.readout true M (x',w,⟨k,E⟩))

private theorem stopping_bridge :
    (type_of% (@trace_iff_stopping.{u,v})) ↔ stoppingArena.Law archiveActual := by
  constructor
  · intro h M n x x'
    exact h M.joint n x x'
  · intro h S Y fs fy K n x x'
    exact h ⟨S,Y,fs,fy,K⟩ n x x'

def lawSignature : Signature where
  Params := System.{u,v}
  State M := M.State × List M.Letter × (Σ n, Experiment M.Letter n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def lawActual : Realization lawSignature :=
  realize lawSignature (fun _ M z => archiveProb M.joint z.2.2.2 z.1 z.2.1)
    (fun e => nomatch e)

def lawArena : Arena where
  signature := lawSignature
  Law R := ∀ (M : System.{u,v}) n (E : Experiment M.Letter n) x,
    (∀ w, 0 ≤ R.readout () M (x,w,⟨n,E⟩)) ∧
    (∀ w, n < w.length → R.readout () M (x,w,⟨n,E⟩) = 0) ∧
    (letI := Classical.decEq M.Letter; ∑ w ∈ leaves E, R.readout () M (x,w,⟨n,E⟩)) = 1

private theorem law_bridge :
    (type_of% (@archive_probability_law.{u,v})) ↔ lawArena.Law lawActual := by
  constructor
  · intro h M n E x
    exact h M.joint E x
  · intro h S Y fs fy K n E x
    exact h ⟨S,Y,fs,fy,K⟩ n E x

def demo : System.{u,v} where
  State := ULift.{u} Bool
  Letter := ULift.{v} Bool
  states := inferInstance
  letters := inferInstance
  joint := ⟨fun x e => if (ULift.up x.down,x) = e then 1 else 0, by
    constructor
    · intro x e; split_ifs <;> norm_num
    · intro x; simp⟩

private theorem demo_word_false : wordProb demo.joint (ULift.up false) [ULift.up true] = 0 := by
  simp [wordProb,demo]

private theorem demo_word_true : wordProb demo.joint (ULift.up true) [ULift.up true] = 1 := by
  simp [wordProb,demo]

def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ M z =>
    if h : Nonempty M.State then (if z.1 = Classical.choice h then 0 else 1) else 0)
    (fun e => nomatch e)

private theorem word_rejected_law : ¬ soundArena.Law wordRejected := by
  intro law
  have h := law demo 0 (ULift.up false) (ULift.up true) trivial [] (by simp)
  have hn : Nonempty demo.State := inferInstance
  let c : demo.State := Classical.choice hn
  have hc : c = ULift.up false ∨ c = ULift.up true := by
    obtain ⟨b⟩ := c
    cases b <;> simp
  dsimp [wordRejected,realize] at h
  simp only [dif_pos hn] at h
  change (if ULift.up false = c then (0:ℝ) else 1) =
    (if ULift.up true = c then 0 else 1) at h
  rcases hc with hc | hc <;> norm_num [hc] at h

def soundRecord : Registration soundArena (type_of% (@residual_sound.{u,v})) where
  actual := wordActual
  bridge := sound_bridge
  variation := ⟨sound_bridge.mp (@residual_sound.{u,v}), wordRejected, word_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected, ?_, rfl, word_rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨demo, (ULift.up false,[]), (ULift.up false,[ULift.up true]), ?_⟩
    change wordProb demo.joint (ULift.up false) [] ≠ wordProb demo.joint (ULift.up false) [ULift.up true]
    rw [demo_word_false]
    norm_num [wordProb]

def overwriteArchive (i : Bool) : Realization archiveSignature :=
  realize archiveSignature (fun j M z => if j = i then 0 else archiveActual.readout j M z)
    (fun e => nomatch e)

private theorem overwrite_archive_law (i : Bool) : ¬ stoppingArena.Law (overwriteArchive i) := by
  intro law
  have h := law demo 1 (ULift.up false) (ULift.up true)
  cases i with
  | false =>
    have hp : ∀ w : List demo.Letter, w.length ≤ 1 →
        (overwriteArchive false).readout false demo (ULift.up false,w,⟨0,.stop⟩) =
        (overwriteArchive false).readout false demo (ULift.up true,w,⟨0,.stop⟩) := by
      intro w _; rfl
    have hq := h.mp hp 1 (by rfl) (.step (fun _ => .stop)) [ULift.up true]
    change (∑ r, demo.joint.1 (ULift.up false) (ULift.up true,r) * 1) =
      ∑ r, demo.joint.1 (ULift.up true) (ULift.up true,r) * 1 at hq
    have h0 := demo_word_false
    have h1 := demo_word_true
    simp only [wordProb] at h0 h1
    rw [h0,h1] at hq
    norm_num at hq
  | true =>
    have hp : ∀ k, k ≤ 1 → ∀ E : Experiment demo.Letter k, ∀ w,
        (overwriteArchive true).readout true demo (ULift.up false,w,⟨k,E⟩) =
        (overwriteArchive true).readout true demo (ULift.up true,w,⟨k,E⟩) := by
      intro k _ E w; rfl
    have hq := h.mpr hp [ULift.up true] (by simp)
    change wordProb demo.joint (ULift.up false) [ULift.up true] =
      wordProb demo.joint (ULift.up true) [ULift.up true] at hq
    rw [demo_word_false,demo_word_true] at hq
    norm_num at hq

def stoppingRecord : Registration stoppingArena (type_of% (@trace_iff_stopping.{u,v})) where
  actual := archiveActual
  bridge := stopping_bridge
  variation := ⟨stopping_bridge.mp (@trace_iff_stopping.{u,v}), overwriteArchive false, overwrite_archive_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨overwriteArchive i, ?_, rfl, overwrite_archive_law i⟩
      intro j h
      funext M z
      simp [overwriteArchive,realize,h]
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨demo, (ULift.up false,[],⟨0,.stop⟩),
      (ULift.up false,[ULift.up true],⟨0,.stop⟩), ?_⟩
    cases i
    · change wordProb demo.joint (ULift.up false) [] ≠ wordProb demo.joint (ULift.up false) [ULift.up true]
      rw [demo_word_false]; norm_num [wordProb]
    · norm_num [archiveActual,realize,archiveProb]

def lawRejected : Realization lawSignature :=
  realize lawSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem law_rejected_law : ¬ lawArena.Law lawRejected := by
  intro law
  have h := (law demo 0 .stop (ULift.up false)).2.2
  norm_num [lawRejected,realize,leaves] at h

def lawRecord : Registration lawArena (type_of% (@archive_probability_law.{u,v})) where
  actual := lawActual
  bridge := law_bridge
  variation := ⟨law_bridge.mp (@archive_probability_law.{u,v}),lawRejected,law_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawRejected, ?_, rfl, law_rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨demo, (ULift.up false,[],⟨0,.stop⟩),
      (ULift.up false,[ULift.up true],⟨0,.stop⟩), ?_⟩
    norm_num [lawActual,realize,archiveProb]

def soundRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@residual_sound.{u,v}) (Realization wordSignature) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.sound,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.soundRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨soundArena⟩,
  objectArena := .source ⟨soundArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source soundArena ⟨soundRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize wordSignature (fun _ M z => wordProb M.joint z.1 z.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def stoppingRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_iff_stopping.{u,v}) (Realization archiveSignature) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.stopping,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.stoppingRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨stoppingArena⟩,
  objectArena := .source ⟨stoppingArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source stoppingArena ⟨stoppingRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize archiveSignature (fun role M z => if role then archiveProb M.joint z.2.2.2 z.1 z.2.1 else wordProb M.joint z.1 z.2.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def lawRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@archive_probability_law.{u,v}) (Realization lawSignature) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.law,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.lawRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨lawArena⟩,
  objectArena := .source ⟨lawArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source lawArena ⟨lawRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize lawSignature (fun _ M z => archiveProb M.joint z.2.2.2 z.1 z.2.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
