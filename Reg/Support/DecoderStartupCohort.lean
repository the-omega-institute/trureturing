import D5.S3.ConceptDynamics.Coding.DecoderStartup
import Reg.Support.DecoderOperationTraceCohort
import Batteries.Tactic.OpenPrivate

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort

open private frame stop stream stopped_drain from Reg.Support.DecoderOperationTraceCohort

universe u v w
noncomputable section

abbrev ProcessingParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Type w

abbrev processingSignature : Signature where
  Params := ProcessingParams.{u,v,w}
  State p := p.1 → Op p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ((ℕ → p.2.2) → (ℕ → p.2.1) → Prop) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def processingAnchor : ∀ (_ : Empty) (p : ProcessingParams.{u,v,w}),
    p.1 → Op p.1 p.2.1 p.2.2 := fun e _ => nomatch e

def processingReadout : ∀ (_ : Unit) (p : ProcessingParams.{u,v,w}),
    (p.1 → Op p.1 p.2.1 p.2.2) →
      p.1 → ((ℕ → p.2.2) → (ℕ → p.2.1) → Prop) → Prop :=
  fun _ p action => Processing action

def processingActual : Realization processingSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u (max v w), 0, max u (max v w), 0}
    processingSignature.{u,v,w} processingReadout.{u,v,w} processingAnchor.{u,v,w}

def drainFalse : Realization drainSignature.{u,v,w} :=
  realize drainSignature (fun _ _ _ _ => False) drainAnchor

def processingFalse : Realization processingSignature.{u,v,w} :=
  realize processingSignature (fun _ _ _ _ _ => False) processingAnchor

abbrev initialDrainArena : Arena where
  signature := drainSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (r : ℕ → I) (t : Frame C O)
      (hr : Run action (full r) ⟨initial,0,[]⟩ t) (hp : 0 < t.acquired),
    ∃ u, R.readout () ⟨C,I,O,action⟩ ⟨initial,0,[]⟩ u

abbrev processingPairArena : Arena where
  signature := processingSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
      (safety : ∀ a r, Record a r → ∀ t,
        Run action (full r) ⟨initial,0,[]⟩ t →
        ∀ p (hp : p < t.output.length), t.output[p] = a p)
      (liveness : ∀ a r, Record a r → InD a → ∀ p,
        ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
      (a beta : ℕ → O) (r r' : ℕ → I)
      (ha : Record a r) (hb : Record beta r') (hd : InD a) (different : a 0 ≠ beta 0)
      (postprocessing : ∀ a r, Record a r → ∀ (c d : C) (q : ℕ) (o w : List O)
        (f : I → Option (C × List O)),
        Run action (full r) ⟨initial,0,[]⟩ ⟨c,q,o⟩ →
        action c = .acquire f → f (r q) = some (d,w) →
        ∃ t, Drain action ⟨d,q+1,o++w⟩ t),
    R.readout () ⟨C,I,O⟩ action initial Record

namespace Models

def echoEmit.{i,o} : ULift.{i} Bool → ULift.{o} Bool := fun x => ⟨x.down⟩

def boolStream (b : Bool) : ℕ → ULift.{v} Bool := fun _ => ⟨b⟩

def echoRecord (a : ℕ → ULift.{w} Bool) (r : ℕ → ULift.{v} Bool) : Prop :=
  ∃ b : Bool, a = boolStream b ∧ r = boolStream b

theorem echo_trace (b : Bool) {t : Frame (PUnit.{u + 1}) (ULift.{w} Bool)}
    {vertices : List (PUnit.{u + 1})}
    (h : Trace (acquirer.{u,v,w} echoEmit) (full (boolStream b))
      ⟨PUnit.unit,0,[]⟩ t vertices) : t.output = List.replicate t.acquired ⟨b⟩ := by
  induction h with
  | refl => rfl
  | @tail middle finish vertices h edge ih =>
    cases edge with
    | internal c d q old batch instruction =>
      simp [acquirer] at instruction
    | acquire c d q old batch f x instruction available result =>
      have hf : (fun x : ULift.{v} Bool =>
          some (PUnit.unit, [echoEmit.{v,w} x])) = f := Op.acquire.inj instruction
      subst f
      have hx : (ULift.up b : ULift.{v} Bool) = x := Option.some.inj available
      subst x
      have he : (PUnit.unit, [ULift.up b]) = (d, batch) := Option.some.inj result
      have hb : batch = [ULift.up b] := (congrArg Prod.snd he).symm
      dsimp only at ih ⊢
      rw [ih, hb]
      simp [List.replicate_add]

theorem echo_safe (a : ℕ → ULift.{w} Bool) (r : ℕ → ULift.{v} Bool)
    (record : echoRecord a r) (t : Frame (PUnit.{u + 1}) (ULift.{w} Bool))
    (hr : Run (acquirer.{u,v,w} echoEmit) (full r) ⟨PUnit.unit,0,[]⟩ t)
    (p : ℕ) (hp : p < t.output.length) : t.output[p] = a p := by
  rcases record with ⟨b, rfl, rfl⟩
  obtain ⟨vertices, hv⟩ := hr
  have equal := echo_trace b hv
  simp [equal, boolStream]

theorem echo_live (a : ℕ → ULift.{w} Bool) (r : ℕ → ULift.{v} Bool)
    (record : echoRecord a r) (_finite : True) (p : ℕ) :
    ∃ t, Run (acquirer.{u,v,w} echoEmit) (full r) ⟨PUnit.unit,0,[]⟩ t ∧
      p < t.output.length := by
  rcases record with ⟨b, rfl, rfl⟩
  refine ⟨_, acquirer_run echoEmit (boolStream b) ⟨b⟩ (fun _ => rfl) (p+1), ?_⟩
  simp

end Models

theorem initial_drain_rejected : ¬ initialDrainArena.{u,v,w}.Law drainFalse := by
  intro h
  obtain ⟨t, impossible⟩ := h (Models.acquirer.{u,v,w} Models.unitEmit) PUnit.unit stream
    ⟨PUnit.unit,1,[PUnit.unit]⟩
    (Models.acquirer_run Models.unitEmit stream PUnit.unit (fun _ => rfl) 1)
    (by decide)
  exact impossible

theorem processing_pair_rejected : ¬ processingPairArena.{u,v,w}.Law processingFalse := by
  intro h
  exact h (Models.acquirer.{u,v,w} Models.echoEmit) PUnit.unit Models.echoRecord
    (fun _ => True) Models.echo_safe Models.echo_live
    (Models.boolStream false) (Models.boolStream true)
    (Models.boolStream false) (Models.boolStream true)
    ⟨false, rfl, rfl⟩ ⟨true, rfl, rfl⟩ True.intro
    (by intro equal; have impossible := congrArg ULift.down equal; cases impossible)
    (Models.acquirer_processing Models.echoEmit Models.echoRecord).2

theorem processing_dependence :
    ObservationalDependence processingSignature.{u,v,w} processingActual := by
  intro i
  let loop : PUnit.{u + 1} → Op (PUnit.{u + 1}) (PUnit.{v + 1}) (PUnit.{w + 1}) :=
    fun c => .internal c []
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}⟩, stop, loop, ?_⟩
  intro h
  have positive : Processing stop.{u,v,w} PUnit.unit (fun _ _ => False) :=
    ⟨⟨frame 0, stopped_drain⟩, by intro a r impossible; exact impossible.elim⟩
  have equal : Processing stop.{u,v,w} PUnit.unit (fun _ _ => False) =
      Processing loop PUnit.unit (fun _ _ => False) :=
    congrFun (congrFun h PUnit.unit) (fun _ _ => False)
  obtain ⟨t, _, ready⟩ := (equal.mp positive).1
  rcases ready with stopped | ⟨f, acquire⟩
  · cases stopped
  · cases acquire

def initialDrainEvidence : Registration initialDrainArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.initial_drain_of_acquired_run.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    drainSignature.{u,v,w} drainReadout.{u,v,w} drainAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@initial_drain_of_acquired_run.{u,v,w}, drainFalse, initial_drain_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨drainFalse, ?_, rfl, initial_drain_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := drain_dependence

def processingPairEvidence : Registration processingPairArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.processing_of_safe_live_pair.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u (max v w), 0, max u (max v w), 0}
    processingSignature.{u,v,w} processingReadout.{u,v,w} processingAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@processing_of_safe_live_pair.{u,v,w}, processingFalse, processing_pair_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨processingFalse, ?_, rfl, processing_pair_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := processing_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort
