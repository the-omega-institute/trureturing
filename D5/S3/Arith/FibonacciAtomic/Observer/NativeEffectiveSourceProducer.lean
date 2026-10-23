/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Partial-recursive same-original acquisition with numeric workspace and lossless output. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout acquisitionTrace nodes)
open NativeSerialMachine NativeSerialEffective NativeFullSourceProducer

/-- Syntax names distinguish both leaf labels and the ordered binary tree. -/
def sourceName : Source → Nat
  | .of true => 0
  | .of false => 1
  | .mul s t => Nat.pair (sourceName s) (sourceName t) + 2

private theorem sourceName_injective : Function.Injective sourceName := by
  intro s
  induction s with
  | of b =>
      intro t h
      cases t with
      | of c => cases b <;> cases c <;> simp_all [sourceName]
      | mul t u => cases b <;> simp [sourceName] at h <;> omega
  | mul s t ihs iht =>
      intro v h
      cases v with
      | of b => cases b <;> simp [sourceName] at h <;> omega
      | mul v w =>
          have hp : Nat.pair (sourceName s) (sourceName t) =
              Nat.pair (sourceName v) (sourceName w) := by simpa [sourceName] using h
          have hu := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at hu
          exact congrArg₂ FreeMagma.mul (ihs hu.1) (iht hu.2)

/-- A semantic inverse only. No effective Source-valued decoder is asserted. -/
noncomputable def sourceDecoder (n : Nat) : Option Source := by
  classical
  exact if h : ∃ U : Source, sourceName U = n then some (Classical.choose h) else none

private theorem sourceDecoder_name (U : Source) : sourceDecoder (sourceName U) = some U := by
  classical
  simp only [sourceDecoder, dif_pos (show ∃ V, sourceName V = sourceName U from ⟨U,rfl⟩)]
  congr 1
  exact sourceName_injective (Classical.choose_spec (show ∃ V, sourceName V = sourceName U from ⟨U,rfl⟩))

/-- Right-child addresses and names of already acquired left subtrees. -/
abbrev NumericFrame := Address ⊕ Nat
abbrev NumericControl := (Address × List NumericFrame) ⊕ (Nat × List NumericFrame)

def numericInitial : NumericControl := .inl ([],[])
def initialWorkspace : Nat := Encodable.encode numericInitial

def nameFrame : Frame → NumericFrame
  | .left a => .inl a
  | .right T => .inr (sourceName T)

def nameControl : Control → NumericControl
  | .visit a k => .inl (a,k.map nameFrame)
  | .deliver T k => .inr (sourceName T,k.map nameFrame)

def workspace (c : Control) : Nat := Encodable.encode (nameControl c)

/-- Proof-side instruction correspondence. This does not encode an evaluator
program or identify its microsteps with producer instructions. -/
def nameInstruction : Op Control Source → OriginalAction Nat ⊕ Nat
  | .localStep c => .inr (workspace c)
  | .read a k => .inl (originalRead a
      (workspace (k .alpha),workspace (k .beta),workspace (k .branch),workspace (k .absent)))
  | .applyRho c => .inl (originalUpdate (workspace c))
  | .stop T => .inl (originalStop (sourceName T))

def visitContinuations (p : Address × List NumericFrame) : Nat × Nat × Nat × Nat :=
    (Encodable.encode (Sum.inr (0,p.2) : NumericControl),
     Encodable.encode (Sum.inr (1,p.2) : NumericControl),
     Encodable.encode (Sum.inl (p.1 ++ [false],Sum.inl (p.1 ++ [true]) :: p.2) : NumericControl),
     Encodable.encode (Sum.inr (0,p.2) : NumericControl))

def visitAction (p : Address × List NumericFrame) : OriginalAction Nat :=
  originalRead p.1 (visitContinuations p)

def deliverTick (p : Nat × List NumericFrame) : OriginalAction Nat ⊕ NumericControl :=
  List.casesOn p.2 (Sum.inl (originalStop p.1)) fun f k =>
    Sum.casesOn f
      (fun a => Sum.inr (Sum.inl (a,Sum.inr p.1 :: k)))
      (fun n => Sum.inr (Sum.inr (Nat.pair n p.1 + 2,k)))

/-- Only a literal numeric workspace is inspected; invalid encodings use the
same source-independent initial control. -/
def numericTick (n : Nat) : OriginalAction Nat ⊕ Nat :=
  let c := (@Encodable.decode NumericControl _ n).getD numericInitial
  let z : OriginalAction Nat ⊕ NumericControl :=
    Sum.casesOn c (fun p => Sum.inl (visitAction p)) deliverTick
  z.map id Encodable.encode

private theorem visitAction_primrec : Primrec visitAction := by
  unfold visitAction visitContinuations originalRead
  apply Primrec.sumInl.comp
  apply Primrec.pair Primrec.fst
  apply Primrec.pair
  · exact Primrec.encode.comp (Primrec.sumInr.comp ((Primrec.const 0).pair Primrec.snd))
  apply Primrec.pair
  · exact Primrec.encode.comp (Primrec.sumInr.comp ((Primrec.const 1).pair Primrec.snd))
  apply Primrec.pair
  · exact Primrec.encode.comp (Primrec.sumInl.comp
      ((Primrec.list_append.comp Primrec.fst (Primrec.const [false])).pair
        (Primrec.list_cons.comp
          (Primrec.sumInl.comp (Primrec.list_append.comp Primrec.fst (Primrec.const [true])))
          Primrec.snd)))
  · exact Primrec.encode.comp (Primrec.sumInr.comp ((Primrec.const 0).pair Primrec.snd))

private theorem deliverTick_primrec : Primrec deliverTick := by
  unfold deliverTick
  refine Primrec.list_casesOn (h := fun (p : Nat × List NumericFrame)
      (q : NumericFrame × List NumericFrame) =>
    Sum.casesOn q.1
      (fun a => Sum.inr (Sum.inl (a,Sum.inr p.1 :: q.2)))
      (fun n => Sum.inr (Sum.inr (Nat.pair n p.1 + 2,q.2)))) Primrec.snd
    (show Primrec (fun p : Nat × List NumericFrame =>
      (Sum.inl (originalStop p.1) : OriginalAction Nat ⊕ NumericControl)) from
      Primrec.sumInl.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.fst))) ?_
  change Primrec (fun p : (Nat × List NumericFrame) × (NumericFrame × List NumericFrame) =>
    (Sum.casesOn p.2.1
      (fun a => Sum.inr (Sum.inl (a,Sum.inr p.1.1 :: p.2.2)))
      (fun n => Sum.inr (Sum.inr (Nat.pair n p.1.1 + 2,p.2.2))) :
      OriginalAction Nat ⊕ NumericControl))
  apply Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd)
  · exact (Primrec.sumInr.comp (Primrec.sumInl.comp
      (Primrec.snd.pair (Primrec.list_cons.comp
        (Primrec.sumInr.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))).to₂
  · exact (Primrec.sumInr.comp (Primrec.sumInr.comp
      ((Primrec.nat_add.comp (Primrec₂.natPair.comp Primrec.snd
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 2)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂

private theorem numericTick_computable : Computable numericTick := by
  have hc : Primrec fun n : Nat => (@Encodable.decode NumericControl _ n).getD numericInitial :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const numericInitial)
  have ht : Primrec fun c : NumericControl =>
      (Sum.casesOn c (fun p => Sum.inl (visitAction p)) deliverTick :
        OriginalAction Nat ⊕ NumericControl) :=
    Primrec.sumCasesOn Primrec.id
      ((Primrec.sumInl.comp visitAction_primrec).comp Primrec.snd).to₂
      (deliverTick_primrec.comp Primrec.snd).to₂
  have hm : Primrec fun z : OriginalAction Nat ⊕ NumericControl =>
      z.map id Encodable.encode := by
    exact Primrec.sumCasesOn Primrec.id (Primrec.sumInl.comp Primrec.snd).to₂
      (Primrec.sumInr.comp (Primrec.encode.comp Primrec.snd)).to₂
  exact (hm.comp (ht.comp hc)).to_comp

/-- First return through genuine producer local steps, not an oracle. -/
noncomputable def selectWorkspace : Nat → Part (OriginalAction Nat) :=
  PFun.fix (fun n => Part.some (numericTick n))

/-- One fixed selector, ignoring common input, epoch, and retained history. -/
noncomputable def sourceService : OriginalEffectiveService Nat where
  select s := selectWorkspace s.2.1
  effective := (Partrec.fix numericTick_computable).comp
    (Computable.fst.comp Computable.snd)

def initialState (i : Nat) (H : List OriginalEvent) : OriginalState :=
  (i,initialWorkspace,0,H)

private theorem tick_encoded (c : NumericControl) :
    numericTick (Encodable.encode c) =
      (Sum.casesOn c (fun p => Sum.inl (visitAction p)) deliverTick :
        OriginalAction Nat ⊕ NumericControl).map id Encodable.encode := by
  simp only [numericTick, Encodable.encodek, Option.getD_some]

private theorem tick_visit (a : Address) (k : List Frame) :
    numericTick (workspace (.visit a k)) = .inl (visitAction (a,k.map nameFrame)) := by
  rw [workspace,tick_encoded]
  rfl

private theorem tick_local {c d : Control} (h : sourceControl c = .localStep d) :
    numericTick (workspace c) = .inr (workspace d) := by
  cases c with
  | visit a k => cases h
  | deliver T k =>
      cases k with
      | nil => cases h
      | cons f k => cases f <;> cases h <;>
          rw [workspace,tick_encoded] <;> rfl

private theorem tick_correspondence (c : Control) :
    numericTick (workspace c) = nameInstruction (sourceControl c) := by
  cases c with
  | visit a k => rw [tick_visit]; rfl
  | deliver T k =>
      cases k with
      | nil => rw [workspace,tick_encoded]; rfl
      | cons f k => cases f <;> rw [workspace,tick_encoded] <;> rfl

private theorem select_local {c d : Control} (h : sourceControl c = .localStep d) :
    selectWorkspace (workspace c) = selectWorkspace (workspace d) :=
  PFun.fix_fwd_eq (by simp [tick_local h])

private theorem visit_continuation (a : Address) (k : List Frame) (y : Reply) :
    originalContinuation (visitContinuations (a,k.map nameFrame)) y =
      workspace (match y with
        | .alpha => .deliver (.of true) k
        | .beta => .deliver (.of false) k
        | .branch => .visit (a ++ [false]) (.left (a ++ [true]) :: k)
        | .absent => .deliver (.of true) k) := by
  cases y <;> rfl

/-- Actual original transitions include the same acquired event and actual
register as OriginalRun. Selector computation itself has no external event. -/
inductive OriginalTransition : (OriginalState × Source) → (OriginalState × Source) → Prop
  | read {s r a k y} : originalRead a k ∈ sourceService.select s →
      readout a r = y →
      OriginalTransition (s,r) (afterOriginalRead s a y (originalContinuation k y),r)
  | update {s r w} : originalUpdate w ∈ sourceService.select s →
      OriginalTransition (s,r) (afterOriginalUpdate s w,GenealogicalFiberTransport.substitution r)

def acquiredEvents (t : List (Nat × Address × Reply)) : List OriginalEvent :=
  t.map (fun p => .inr (p.1,p.2.1,originalReplyCode p.2.2))

def externalTrace (U : Source) : Trace :=
  (acquisitionTrace [] U).map (fun a => .read 0 a.1 a.2)

private inductive Acquires :
    OriginalState → Source → List (Nat × Address × Reply) → OriginalState → Nat → Prop
  | stop {s r o} : originalStop o ∈ sourceService.select s → Acquires s r [] s o
  | read {s r t f o a k y} : originalRead a k ∈ sourceService.select s →
      readout a r = y →
      Acquires (afterOriginalRead s a y (originalContinuation k y)) r t f o →
      Acquires s r ((s.epoch,a,y) :: t) f o

private theorem acquires_properties {s f : OriginalState} {r : Source} {t : List (Nat × Address × Reply)} {o : Nat}
    (run : Acquires s r t f o) :
    OriginalRun sourceService s r (t.map (fun p => .read p.1 p.2.1 p.2.2)) o ∧
    Relation.ReflTransGen OriginalTransition (s,r) (f,r) ∧
    originalStop o ∈ sourceService.select f ∧
    f.input = s.input ∧ f.epoch = s.epoch ∧ f.history = s.history ++ acquiredEvents t := by
  induction run with
  | stop h => exact ⟨OriginalRun.stop h,Relation.ReflTransGen.refl,h,rfl,rfl,by simp [acquiredEvents,reads]⟩
  | read h hy run ih =>
      refine ⟨OriginalRun.read h hy ih.1,?_,ih.2.2.1,ih.2.2.2.1,ih.2.2.2.2.1,?_⟩
      · exact (Relation.ReflTransGen.single (OriginalTransition.read h hy)).trans ih.2.1
      · simpa only [afterOriginalRead,OriginalState.history,OriginalState.epoch,
          acquiredEvents,reads,List.map_cons,List.append_assoc,List.singleton_append]
          using ih.2.2.2.2.2

private theorem acquires_rebase {i e w v : Nat} {H : List OriginalEvent}
    {r : Source} {t : List (Nat × Address × Reply)} {f : OriginalState} {o : Nat}
    (he : selectWorkspace w = selectWorkspace v)
    (run : Acquires (i,v,e,H) r t f o) : ∃ g, Acquires (i,w,e,H) r t g o := by
  cases run with
  | stop h => exact ⟨_,Acquires.stop (by simpa only [sourceService,he] using h)⟩
  | read h hy next =>
      exact ⟨_,Acquires.read (by simpa only [sourceService,he] using h) hy next⟩

private theorem tick_stop {c : Control} {o : Source} (h : sourceControl c = .stop o) :
    numericTick (workspace c) = .inl (originalStop (sourceName o)) := by
  cases c with
  | visit a k => cases h
  | deliver T k =>
      cases k with
      | nil => cases h; rw [workspace,tick_encoded]; rfl
      | cons f k => cases f <;> cases h

private theorem transport_run {c : Control} {e : Nat} {U out : Source} {t : Trace}
    (run : Run sourceControl c e U t out) (i : Nat) (H : List OriginalEvent) :
    ∃ f, Acquires (i,workspace c,e,H) U (reads t) f (sourceName out) := by
  induction run generalizing i H with
  | stop h =>
      refine ⟨_,Acquires.stop ?_⟩
      exact PFun.fix_stop (by simp only [Part.mem_some_iff,tick_stop h])
  | localStep h run ih =>
      obtain ⟨f,hf⟩ := ih i H
      exact acquires_rebase (select_local h) hf
  | update h run ih =>
      rename_i c d e r t out
      cases c with
      | visit a k => cases h
      | deliver T k => cases k with
        | nil => cases h
        | cons f k => cases f <;> cases h
  | @read c e r a k y t out h hy run ih =>
      cases c with
      | deliver T fs => cases fs with
        | nil => cases h
        | cons f fs => cases f <;> cases h
      | visit b fs =>
          have eq := Op.read.inj h
          rcases eq with ⟨rfl,hk⟩
          subst k
          obtain ⟨f,hf⟩ := ih i (H ++ [.inr (e,b,originalReplyCode y)])
          refine ⟨f,Acquires.read (k := visitContinuations (b,fs.map nameFrame)) ?_ hy ?_⟩
          · exact PFun.fix_stop (by simp only [Part.mem_some_iff,tick_visit]; rfl)
          · cases y <;> simpa only [afterOriginalRead,OriginalState.input,OriginalState.epoch,
              OriginalState.history,visit_continuation] using hf

private theorem selector_no_update (w v : Nat) :
    originalUpdate v ∉ selectWorkspace w := by
  intro h
  apply PFun.fixInduction' h
    (C := fun _ => False)
    (fun n hn => ?_)
    (fun _ _ _ _ ih => ih)
  simp only [Part.mem_some_iff] at hn
  unfold numericTick at hn
  generalize (@Encodable.decode NumericControl _ n).getD numericInitial = c at hn
  cases c with
  | inl p => cases hn
  | inr p =>
      rcases p with ⟨o,fs⟩
      cases fs with
      | nil => cases hn
      | cons f fs => cases f <;> cases hn

private theorem original_stationary {x z : OriginalState × Source}
    (h : Relation.ReflTransGen OriginalTransition x z) :
    z.1.input = x.1.input ∧ z.1.epoch = x.1.epoch ∧ z.2 = x.2 := by
  induction h with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail h step ih =>
      cases step with
      | read _ _ => exact ⟨ih.1,ih.2.1,ih.2.2⟩
      | update hu => exact (selector_no_update _ _ hu).elim

/-- A single certified selector acquires every finite original. OriginalRun
retains external actions; the separate producer Run and replay retain genuine
producer local chronology. No evaluator microstep identification is made. -/
def FullSourceAcquisition (o : Nat) (U : Source) (i : Nat) (H : List OriginalEvent) : Prop :=
    Partrec sourceService.select ∧
    OriginalRun sourceService (initialState i H) U
      (externalTrace U) o ∧
    sourceDecoder o = some U ∧
    (∃ f : OriginalState,
      Relation.ReflTransGen OriginalTransition (initialState i H,U) (f,U) ∧
      originalStop o ∈ sourceService.select f ∧
      f.input = i ∧ f.epoch = 0 ∧
      f.history = H ++ (acquisitionTrace [] U).map
        (fun a => .inr (0,a.1,originalReplyCode a.2))) ∧
    (∀ x : OriginalState × Source,
      Relation.ReflTransGen OriginalTransition (initialState i H,U) x →
      x.1.input = i ∧ x.1.epoch = 0 ∧ x.2 = U) ∧
    Run sourceControl initialControl 0 U (productionTrace [] U) U ∧
    (∀ old : Trace, ∃ c : Control,
      StateTransition.Reaches (nativeStep sourceControl) (initialControl,0,U,old)
        (c,0,U,old ++ productionTrace [] U) ∧ sourceControl c = .stop U) ∧
    (∀ w : List Reply, w <+: answers (productionTrace [] U) →
      ∃ s b, Replay sourceControl initialControl 0 w s b ∧
        s <+: productionTrace [] U ∧ answers s = w ∧
        (w = answers (productionTrace [] U) ↔ b.2.2 = .inr U)) ∧
    reads (productionTrace [] U) =
      (acquisitionTrace [] U).map (fun a => (0,a.1,a.2)) ∧
    (reads (productionTrace [] U)).map (fun a => a.2.1) = nodes U ∧
    ((reads (productionTrace [] U)).map (fun a => a.2.1)).Nodup ∧
    (reads (productionTrace [] U)).length = (nodes U).length ∧
    (∀ (old : Trace) (x : Config Control),
      StateTransition.Reaches (nativeStep sourceControl) (initialControl,0,U,old) x →
        x.2.1 = 0 ∧ x.2.2.1 = U) ∧
    (∀ c : Control, numericTick (workspace c) = nameInstruction (sourceControl c))

theorem effective_source_producer (i : Nat) (H : List OriginalEvent) (U : Source) :
    FullSourceAcquisition (sourceName U) U i H := by
  have supply := native_source_producer U
  obtain ⟨f,hf⟩ := transport_run supply.1 i H
  have done := acquires_properties hf
  refine ⟨sourceService.effective,?_,sourceDecoder_name U,?_,?_,
    supply.1,supply.2.1,?_,supply.2.2.2.1,supply.2.2.2.2.1,
    supply.2.2.2.2.2.1,supply.2.2.2.2.2.2,supply.2.2.1,tick_correspondence⟩
  · simpa only [externalTrace,supply.2.2.2.1,List.map_map,Function.comp_def,
      initialState,initialWorkspace,numericInitial,workspace,initialControl,nameControl,List.map_nil] using done.1
  · refine ⟨f,done.2.1,done.2.2.1,done.2.2.2.1,done.2.2.2.2.1,?_⟩
    rw [done.2.2.2.2.2,acquiredEvents,supply.2.2.2.1,List.map_map]
    rfl
  · intro x hx
    exact original_stationary hx
  · intro w hw
    exact reached_prefix_replay supply.1 w hw

end D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer
