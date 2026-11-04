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

abbrev wordSignature : Signature where
  Params := System.{u,v}
  State M := M.State × List M.Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev wordActual : Realization wordSignature.{u,v} :=
  realize wordSignature.{u,v} (fun _ M z => wordProb M.joint z.1 z.2) (fun e => nomatch e)

abbrev soundArena : Arena where
  signature := wordSignature.{u,v}
  Law R := ∀ (M : System.{u,v}) n x x', residual M.joint n x x' →
    ∀ w : List M.Letter, w.length ≤ n → R.readout () M (x,w) = R.readout () M (x',w)

private theorem sound_bridge :
    (type_of% (@residual_sound.{u,v})) ↔ soundArena.{u,v}.Law wordActual.{u,v} := by
  constructor
  · intro h M n x x' hr w hw
    exact h M.joint n x x' hr w hw
  · intro h S Y fs fy K n x x' hr w hw
    exact h ⟨S,Y,fs,fy,K⟩ n x x' hr w hw

abbrev archiveSignature : Signature where
  Params := System.{u,v}
  State M := M.State × List M.Letter × (Σ n, Experiment M.Letter n)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev archiveActual : Realization archiveSignature.{u,v} :=
  realize archiveSignature.{u,v} (fun role M z =>
    if role then archiveProb M.joint z.2.2.2 z.1 z.2.1 else wordProb M.joint z.1 z.2.1)
    (fun e => nomatch e)

abbrev stoppingArena : Arena where
  signature := archiveSignature.{u,v}
  Law R := ∀ (M : System.{u,v}) n x x',
    (∀ w : List M.Letter, w.length ≤ n →
      R.readout false M (x,w,⟨0,.stop⟩) = R.readout false M (x',w,⟨0,.stop⟩)) ↔
    (∀ k, k ≤ n → ∀ E : Experiment M.Letter k, ∀ w,
      R.readout true M (x,w,⟨k,E⟩) = R.readout true M (x',w,⟨k,E⟩))

private theorem stopping_bridge :
    (type_of% (@trace_iff_stopping.{u,v})) ↔ stoppingArena.{u,v}.Law archiveActual.{u,v} := by
  constructor
  · intro h M n x x'
    exact h M.joint n x x'
  · intro h S Y fs fy K n x x'
    exact h ⟨S,Y,fs,fy,K⟩ n x x'

abbrev lawSignature : Signature where
  Params := System.{u,v}
  State M := M.State × List M.Letter × (Σ n, Experiment M.Letter n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev lawActual : Realization lawSignature.{u,v} :=
  realize lawSignature.{u,v} (fun _ M z => archiveProb M.joint z.2.2.2 z.1 z.2.1)
    (fun e => nomatch e)

abbrev lawArena : Arena where
  signature := lawSignature.{u,v}
  Law R := ∀ (M : System.{u,v}) n (E : Experiment M.Letter n) x,
    (∀ w, 0 ≤ R.readout () M (x,w,⟨n,E⟩)) ∧
    (∀ w, n < w.length → R.readout () M (x,w,⟨n,E⟩) = 0) ∧
    (letI := Classical.decEq M.Letter; ∑ w ∈ leaves E, R.readout () M (x,w,⟨n,E⟩)) = 1

private theorem law_bridge :
    (type_of% (@archive_probability_law.{u,v})) ↔ lawArena.{u,v}.Law lawActual.{u,v} := by
  constructor
  · intro h M n E x
    exact h M.joint E x
  · intro h S Y fs fy K n E x
    exact h ⟨S,Y,fs,fy,K⟩ n E x

abbrev demo : System.{u,v} where
  State := ULift.{u} Bool
  Letter := ULift.{v} Bool
  states := inferInstance
  letters := inferInstance
  joint := ⟨fun x e => if (ULift.up x.down,x) = e then 1 else 0, by
    constructor
    · intro x e; dsimp only; split_ifs <;> norm_num
    · intro x; simp⟩

private theorem demo_word_false : wordProb demo.{u,v}.joint (ULift.up false) [ULift.up true] = 0 := by
  simp [wordProb,demo]

private theorem demo_word_true : wordProb demo.{u,v}.joint (ULift.up true) [ULift.up true] = 1 := by
  simp [wordProb,demo]

abbrev wordRejected : Realization wordSignature.{u,v} :=
  realize wordSignature.{u,v} (fun _ M z =>
    if h : Nonempty M.State then (if z.1 = Classical.choice h then 0 else 1) else 0)
    (fun e => nomatch e)

private theorem word_rejected_law : ¬ soundArena.{u,v}.Law wordRejected.{u,v} := by
  intro law
  have h := law demo.{u,v} 0 (ULift.up false) (ULift.up true) trivial [] (by simp)
  have hn : Nonempty demo.{u,v}.State := inferInstance
  let c : demo.{u,v}.State := Classical.choice hn
  have hc : c = ULift.up false ∨ c = ULift.up true := by
    obtain ⟨b⟩ := c
    cases b <;> simp
  dsimp [wordRejected,realize] at h
  simp only [dif_pos hn] at h
  dsimp only [c] at hc
  rcases hc with hc | hc <;> norm_num [hc] at h

abbrev soundRecord : Registration soundArena.{u,v} (type_of% (@residual_sound.{u,v})) where
  actual := wordActual.{u,v}
  bridge := sound_bridge.{u,v}
  variation := ⟨sound_bridge.{u,v}.mp (@residual_sound.{u,v}), wordRejected.{u,v}, word_rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected.{u,v}, ?_, rfl, word_rejected_law.{u,v}⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨demo.{u,v}, (ULift.up false,[]), (ULift.up false,[ULift.up true]), ?_⟩
    change wordProb demo.{u,v}.joint (ULift.up false) [] ≠ wordProb demo.{u,v}.joint (ULift.up false) [ULift.up true]
    rw [demo_word_false.{u,v}]
    norm_num [wordProb]

abbrev overwriteArchive (i : Bool) : Realization archiveSignature.{u,v} :=
  realize archiveSignature.{u,v} (fun j M z => if j = i then 0 else archiveActual.{u,v}.readout j M z)
    (fun e => nomatch e)

private theorem overwrite_archive_law (i : Bool) : ¬ stoppingArena.{u,v}.Law (overwriteArchive.{u,v} i) := by
  intro law
  have h := law demo.{u,v} 1 (ULift.up false) (ULift.up true)
  cases i with
  | false =>
    have hp : ∀ w : List demo.{u,v}.Letter, w.length ≤ 1 →
        (overwriteArchive.{u,v} false).readout false demo.{u,v} (ULift.up false,w,⟨0,.stop⟩) =
        (overwriteArchive.{u,v} false).readout false demo.{u,v} (ULift.up true,w,⟨0,.stop⟩) := by
      intro w _; rfl
    have hq := h.mp hp 1 (by rfl) (.step (fun _ => .stop)) [ULift.up true]
    change (∑ r, demo.{u,v}.joint.1 (ULift.up false) (ULift.up true,r) * 1) =
      ∑ r, demo.{u,v}.joint.1 (ULift.up true) (ULift.up true,r) * 1 at hq
    have h0 := demo_word_false.{u,v}
    have h1 := demo_word_true.{u,v}
    simp only [wordProb] at h0 h1
    rw [h0,h1] at hq
    norm_num at hq
  | true =>
    have hp : ∀ k, k ≤ 1 → ∀ E : Experiment demo.{u,v}.Letter k, ∀ w,
        (overwriteArchive.{u,v} true).readout true demo.{u,v} (ULift.up false,w,⟨k,E⟩) =
        (overwriteArchive.{u,v} true).readout true demo.{u,v} (ULift.up true,w,⟨k,E⟩) := by
      intro k _ E w; rfl
    have hq := h.mpr hp [ULift.up true] (by simp)
    change wordProb demo.{u,v}.joint (ULift.up false) [ULift.up true] =
      wordProb demo.{u,v}.joint (ULift.up true) [ULift.up true] at hq
    rw [demo_word_false.{u,v},demo_word_true.{u,v}] at hq
    norm_num at hq

abbrev stoppingRecord : Registration stoppingArena.{u,v} (type_of% (@trace_iff_stopping.{u,v})) where
  actual := archiveActual.{u,v}
  bridge := stopping_bridge.{u,v}
  variation := ⟨stopping_bridge.{u,v}.mp (@trace_iff_stopping.{u,v}), overwriteArchive.{u,v} false, overwrite_archive_law.{u,v} false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨overwriteArchive.{u,v} i, ?_, rfl, overwrite_archive_law.{u,v} i⟩
      intro j h
      funext M z
      simp [overwriteArchive,realize,h]
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨demo.{u,v}, (ULift.up false,[],⟨0,.stop⟩),
      (ULift.up false,[ULift.up true],⟨0,.stop⟩), ?_⟩
    cases i
    · change wordProb demo.{u,v}.joint (ULift.up false) [] ≠ wordProb demo.{u,v}.joint (ULift.up false) [ULift.up true]
      rw [demo_word_false]; norm_num [wordProb]
    · norm_num [archiveActual,realize,archiveProb]

abbrev lawRejected : Realization lawSignature.{u,v} :=
  realize lawSignature.{u,v} (fun _ _ _ => 0) (fun e => nomatch e)

private theorem law_rejected_law : ¬ lawArena.{u,v}.Law lawRejected.{u,v} := by
  intro law
  have h := (law demo.{u,v} 0 .stop (ULift.up false)).2.2
  norm_num [lawRejected,realize,leaves] at h

abbrev lawRecord : Registration lawArena.{u,v} (type_of% (@archive_probability_law.{u,v})) where
  actual := lawActual.{u,v}
  bridge := law_bridge.{u,v}
  variation := ⟨law_bridge.{u,v}.mp (@archive_probability_law.{u,v}),lawRejected.{u,v},law_rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawRejected.{u,v}, ?_, rfl, law_rejected_law.{u,v}⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨demo.{u,v}, (ULift.up false,[],⟨0,.stop⟩),
      (ULift.up false,[ULift.up true],⟨0,.stop⟩), ?_⟩
    norm_num [lawActual,realize,archiveProb]

def soundRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@residual_sound.{u,v}) (Realization wordSignature.{u,v}) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.sound,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.soundRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨soundArena.{u,v}⟩,
  objectArena := .source ⟨soundArena.{u,v}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source soundArena.{u,v} ⟨soundRecord.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize wordSignature.{u,v} (fun _ M z => wordProb M.joint z.1 z.2) (fun e => nomatch e)),
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
    (@trace_iff_stopping.{u,v}) (Realization archiveSignature.{u,v}) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.stopping,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.stoppingRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨stoppingArena.{u,v}⟩,
  objectArena := .source ⟨stoppingArena.{u,v}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source stoppingArena.{u,v} ⟨stoppingRecord.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize archiveSignature.{u,v} (fun role M z => if role then archiveProb M.joint z.2.2.2 z.1 z.2.1 else wordProb M.joint z.1 z.2.1) (fun e => nomatch e)),
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
    (@archive_probability_law.{u,v}) (Realization lawSignature.{u,v}) (Type) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.law,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping.lawRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨lawArena.{u,v}⟩,
  objectArena := .source ⟨lawArena.{u,v}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source lawArena.{u,v} ⟨lawRecord.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize lawSignature.{u,v} (fun _ M z => archiveProb M.joint z.2.2.2 z.1 z.2.1) (fun e => nomatch e)),
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
