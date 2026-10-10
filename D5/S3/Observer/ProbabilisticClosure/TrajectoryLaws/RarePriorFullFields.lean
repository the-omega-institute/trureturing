/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full original event transcripts factor through the finite retained fields. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFullFields
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeFullResidual RarePriorFiniteMonitor

noncomputable section
open MeasureTheory ProbabilityTheory
instance : MeasurableSpace Runtime := ⊤
instance : MeasurableSingletonClass Runtime := ⟨fun _ => trivial⟩

/-- Off-permission rows are total but confer no source permission. -/
def actualUpdate (op : Operation) (z : Runtime) : PMF Runtime :=
  PMF.pure ((runtimeStep z op).getD z)

def actualObserver : NativeObserverJointLaw.Observer Runtime where
  project := Runtime.fields
  init := PMF.pure runtimeInitial
  update := actualUpdate
  init_refines := by
    intro z hz
    have he := (PMF.mem_support_pure_iff _ _).mp hz
    subst z
    rfl
  update_refines := by
    intro op z f hf d hd
    have he : d = (runtimeStep z op).getD z := by
      simpa [actualUpdate] using hd
    subst d
    simp [runtimeStep,hf]

private theorem advance_pure (z d : Runtime) (ops : List Operation)
    (he : runtimeExecute z ops = some d) :
    NativeObserverJointLaw.advance actualObserver (PMF.pure z) ops = PMF.pure d := by
  induction ops generalizing z with
  | nil => simpa [runtimeExecute,NativeObserverJointLaw.advance] using congrArg PMF.pure (Option.some.inj he)
  | cons op ops ih =>
    obtain ⟨q,hq,hd⟩ := Option.bind_eq_some_iff.mp he
    simp only [NativeObserverJointLaw.advance,PMF.pure_bind]
    change NativeObserverJointLaw.advance actualObserver (actualUpdate op z) ops = _
    simpa [actualUpdate,hq] using ih q hd

/-- Every original legal history has a single retained runtime; the same update
    row applies to every next letter, independently of synthetic probabilities. -/
theorem deterministic_actual_rows (ops : List Operation) (c : AcquiredNativeState)
    (hc : run ops = some c) :
    ∃ z : Runtime, runtimeRun ops = some z ∧ z.fields = c.source.finiteFields ∧
      NativeObserverJointLaw.row actualObserver ops = PMF.pure z ∧
      (∀ op : Operation, NativeObserverJointLaw.row actualObserver (ops ++ [op]) =
        actualUpdate op z) := by
  have hp := arbitrary_legal_projection ops ⟨c,hc⟩
  rw [hc,Option.map_some] at hp
  obtain ⟨z,hz,hf⟩ := Option.map_eq_some_iff.mp hp
  have hr : NativeObserverJointLaw.row actualObserver ops = PMF.pure z :=
    advance_pure runtimeInitial z ops hz
  refine ⟨z,hz,hf,hr,?_⟩
  intro op
  rw [(NativeObserverJointLaw.actual_row_refines actualObserver ops c hc).2.1 op,hr]
  simp [actualObserver]

/-- The source scheduler reads only retained control and the current letter. -/
def finiteOperation (f : FiniteFields) (x : Letter) : Option Operation :=
  match f.control with
  | .seed _ | .early _ _ | .fourth (.active _) => some (.read x)
  | .fourth (.pending b) => some (.stop b)
  | .fourth .delivered => none

def finiteNext (f : FiniteFields) (x : Letter) : Option (Operation × FiniteFields) :=
  (finiteOperation f x).bind fun op => (finiteStep f op).map fun d => (op,d)

/-- This execution contains neither source counts nor payload-return banks. -/
def finiteDrive (f : FiniteFields) (ω : Stream) :
    ℕ → Option (List Operation × FiniteFields × ℕ)
  | 0 => some ([],f,0)
  | n+1 => (finiteNext f (ω 0)).bind fun step =>
      (finiteDrive step.2 (rawTail ω (readCost step.1)) n).map fun result =>
        (step.1 :: result.1,result.2.1,readCost step.1+result.2.2)

private theorem next_projection (c : AcquiredNativeState) (ω : Stream) :
    (nextNative c ω).map (fun r => (r.1,r.2.source.finiteFields)) =
      finiteNext c.source.finiteFields (ω 0) := by
  have hs : nextOperation c ω = finiteOperation c.source.finiteFields (ω 0) := rfl
  simp only [nextNative, hs, finiteNext, Option.map_bind]
  congr 1
  funext op
  rw [← finite_projection_commutes]
  simp [Option.map_map, Function.comp_def]

private theorem drive_projection (c : AcquiredNativeState) (ω : Stream) (n : ℕ) :
    (nativeDrive c ω n).map (fun r => (r.1,r.2.1.source.finiteFields,r.2.2)) =
      finiteDrive c.source.finiteFields ω n := by
  induction n generalizing c ω with
  | zero => rfl
  | succ n ih =>
    have hn := next_projection c ω
    cases hc : nextNative c ω with
    | none => simp [hc] at hn; simp [nativeDrive,hc,finiteDrive,← hn]
    | some step =>
      have hf : finiteNext c.source.finiteFields (ω 0) =
          some (step.1,step.2.source.finiteFields) := by simpa [hc] using hn.symm
      simpa [nativeDrive,hc,finiteDrive,hf,Option.map_map,Function.comp_def] using
        congrArg (Option.map (fun r : List Operation × FiniteFields × ℕ =>
          (step.1 :: r.1,r.2.1,readCost step.1+r.2.2)))
          (ih step.2 (rawTail ω (readCost step.1)))

/-- Ordered operations and full event blocks are emitted, rather than retained. -/
def fieldsTranscript (f : FiniteFields) (ω : Stream) : FullTranscript := fun n =>
  (finiteDrive f ω n).map fun r => (r.1,r.2.1,eventBlocks f r.1)

/-- A fourth-phase renderer whose sole configuration input is finite fields. -/
def fieldsRenderer (f : FiniteFields) (s : ActivePhase) (t : ValidTail s) : FullTranscript :=
  fieldsTranscript f (tailStream s t.val)

/-- The complete original transcript factors at every cut, including infinite seed
    paths and all early, active, pending and delivered states. -/
theorem full_fields_factorization (c : AcquiredNativeState) (ω : Stream) :
    fullTranscript c ω = fieldsTranscript c.source.finiteFields ω ∧
    (∀ (d : AcquiredNativeState), c.source.finiteFields = d.source.finiteFields →
      fullTranscript c ω = fullTranscript d ω) ∧
    (∀ (s : ActivePhase) (t : ValidTail s),
      fullRenderer c s t = fieldsRenderer c.source.finiteFields s t) := by
  have h (e : AcquiredNativeState) (v : Stream) :
      fullTranscript e v = fieldsTranscript e.source.finiteFields v := by
    funext n
    unfold fullTranscript fieldsTranscript
    rw [← drive_projection]
    simp [Option.map_map,Function.comp_def]
  exact ⟨h c ω,fun d hd => (h c ω).trans (hd ▸ (h d ω).symm),
    fun s t => h c (tailStream s t.val)⟩

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFullFields
