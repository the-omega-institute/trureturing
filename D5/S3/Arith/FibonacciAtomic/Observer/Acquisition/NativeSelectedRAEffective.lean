/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite encodings of the native selected machine and its total microsteps. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective

open ActualTreeReadoutAcquisition (Address Reply)
open NativeSelectedRA

private def workEquiv : Work ≃ Fin 100 × Address × Address × List Cell × Reply × Reply × Reply where
  toFun w := (w.pc,w.guardPath,w.operand,w.row,w.guardReply,w.leftReply,w.rightReply)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2⟩
  left_inv w := by cases w; rfl
  right_inv p := rfl

local instance workCoding : Primcodable Work := Primcodable.ofEquiv _ workEquiv

private theorem work_prim {α : Type} [Primcodable α] {pc : α → Fin 100}
    {g o : α → Address} {r : α → List Cell} {a b c : α → Reply}
    (hp : Primrec pc) (hg : Primrec g) (ho : Primrec o) (hr : Primrec r)
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun x => (⟨pc x,g x,o x,r x,a x,b x,c x⟩ : Work)) :=
  (Primrec.of_equiv_symm (e := workEquiv)).comp
    (hp.pair (hg.pair (ho.pair (hr.pair (ha.pair (hb.pair hc))))))

private theorem work_fields : Primrec Work.pc ∧ Primrec Work.guardPath ∧ Primrec Work.operand ∧
    Primrec Work.row ∧ Primrec Work.guardReply ∧ Primrec Work.leftReply ∧ Primrec Work.rightReply := by
  have h : Primrec workEquiv := Primrec.of_equiv
  exact ⟨Primrec.fst.comp h,Primrec.fst.comp (Primrec.snd.comp h),
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp h)),
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp h))),
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp h)))),
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp h))))),
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp h)))))⟩

private theorem pop_prim {α : Type} [Primcodable α] : Primrec (@pop α) :=
  (Primrec.list_take.comp (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
    Primrec.id).of_eq (by intro l; simp [pop,List.dropLast_eq_take])

private theorem last_prim : Primrec lastBit :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.list_reverse)
    (Primrec.const false)).of_eq (by intro l; simp [lastBit,List.head?_reverse])

private theorem local_go_prim (n : Fin 100) :
    Primrec (fun w : Work => localInstruction (go n w)) := by
  obtain ⟨_,g,o,r,a,b,c⟩ := work_fields
  exact Primrec.sumInr.comp (Primrec.sumInl.comp
    (work_prim (Primrec.const n) g o r a b c))

private theorem local_put_prim (n : Fin 100) (x : Cell) :
    Primrec (fun w : Work => localInstruction (put n x w)) := by
  obtain ⟨_,g,o,r,a,b,c⟩ := work_fields
  exact Primrec.sumInr.comp (Primrec.sumInl.comp
    (work_prim (Primrec.const n) g o (Primrec.list_append.comp r (Primrec.const [x])) a b c))

set_option maxHeartbeats 4000000 in
-- The program counter has a fixed finite domain; all data regions remain unbounded.
private theorem private_prim (q : Bool) : Primrec (privateStep q) := by
  obtain ⟨pcp,gp,op,rp,ap,bp,cp⟩ := work_fields
  have control : Primrec₂ (fun pc : Fin 100 => fun w : Work => privateStep q {w with pc := pc}) := by
    apply Primrec.fin_curry₁.mpr
    intro pc
    fin_cases pc <;>
      simp only [privateStep,receipt,localInstruction,go,put,switch]
    all_goals try simp only [Bool.false_eq_true,↓reduceIte,reduceCtorEq]
    all_goals
      first
        | exact local_go_prim _
        | exact local_put_prim _ _
        | skip
    all_goals
      repeat' first
        | exact Primrec.id
        | exact pcp
        | exact gp
        | exact op
        | exact rp
        | exact ap
        | exact bp
        | exact cp
        | apply Primrec.const
        | apply work_prim
        | apply Primrec.pair
        | apply Primrec.sumInl.comp
        | apply Primrec.sumInr.comp
        | apply Primrec.ite
        | apply Primrec.cond
        | apply PrimrecPred.and
        | apply PrimrecPred.or
        | apply PrimrecPred.not
        | apply Primrec.eq.comp
        | apply Primrec.list_cons.comp
        | apply Primrec.list_append.comp
        | apply pop_prim.comp
        | apply last_prim.comp
        | apply Primrec.list_tail.comp
  exact (control.comp pcp Primrec.id).of_eq (by intro w; cases w; rfl)

private def stateEquiv : State ≃ Unit ⊕ ((Bool × Work) ⊕ (Bool × List Cell)) where
  toFun s := match s with
    | .entry => .inl ()
    | .active q w => .inr (.inl (q,w))
    | .ready q r => .inr (.inr (q,r))
  invFun s := match s with
    | .inl _ => .entry
    | .inr (.inl (q,w)) => .active q w
    | .inr (.inr (q,r)) => .ready q r
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with ⟨⟩ | (⟨q,w⟩ | ⟨q,r⟩) <;> rfl

local instance stateCoding : Primcodable State := Primcodable.ofEquiv _ stateEquiv

/-- An injective natural code of the entire accessible configuration. -/
def encodeState (s : State) : Nat := Encodable.encode s

private theorem active_prim : Primrec₂ State.active :=
  Primrec.of_equiv_symm.comp (Primrec.sumInr.comp (Primrec.sumInl.comp Primrec.id))

private theorem ready_prim : Primrec₂ State.ready :=
  Primrec.of_equiv_symm.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.id))

private theorem private_all : Primrec₂ privateStep := by
  have h := Primrec.cond (Primrec.fst : Primrec (Prod.fst : Bool × Work → Bool))
    ((private_prim true).comp Primrec.snd) ((private_prim false).comp Primrec.snd)
  exact h.of_eq (by intro p; cases p.1 <;> rfl)

/-- The four Read continuations and every local instruction remain explicit. -/
def finiteInstruction : State → NativeIndependentExecution.Instruction
  | .entry => .inl ([],(encodeState (.active true emptyWork),
      encodeState (.active false emptyWork),encodeState (.active false emptyWork),
      encodeState (.active false emptyWork)))
  | .ready _ _ => .inr (.inr ())
  | .active q w => match privateStep q w with
    | .inl (p,k) => .inl (p,(encodeState (.active q k.1),encodeState (.active q k.2.1),
        encodeState (.active q k.2.2.1),encodeState (.active q k.2.2.2)))
    | .inr (.inl v) => .inr (.inl (encodeState (.active q v)))
    | .inr (.inr _) => .inr (.inl (encodeState (.ready q w.row)))

private theorem finite_prim : Primrec finiteInstruction := by
  have enc : Primrec encodeState := Primrec.encode
  have active : Primrec (fun p : (Bool × Work) × PrivateInstruction =>
      match p.2 with
      | .inl (a,k) => (Sum.inl (a,(encodeState (.active p.1.1 k.1),
          encodeState (.active p.1.1 k.2.1),encodeState (.active p.1.1 k.2.2.1),
          encodeState (.active p.1.1 k.2.2.2))) : NativeIndependentExecution.Instruction)
      | .inr (.inl v) => .inr (.inl (encodeState (.active p.1.1 v)))
      | .inr (.inr _) => .inr (.inl (encodeState (.ready p.1.1 p.1.2.row)))) := by
    suffices h : Primrec (fun p : (Bool × Work) × PrivateInstruction =>
      Sum.casesOn (motive := fun _ => NativeIndependentExecution.Instruction) p.2
        (fun k => (Sum.inl (k.1,(encodeState (.active p.1.1 k.2.1),
          encodeState (.active p.1.1 k.2.2.1),encodeState (.active p.1.1 k.2.2.2.1),
          encodeState (.active p.1.1 k.2.2.2.2))) : NativeIndependentExecution.Instruction))
        (fun r => Sum.casesOn (motive := fun _ => NativeIndependentExecution.Instruction) r
          (fun v => Sum.inr (Sum.inl (encodeState (.active p.1.1 v))))
          (fun _ => Sum.inr (Sum.inl (encodeState (.ready p.1.1 p.1.2.row)))))) by
      apply h.of_eq
      intro p
      rcases p.2 with ⟨a,k⟩ | (v | u) <;> rfl
    apply Primrec.sumCasesOn Primrec.snd
    · change Primrec₂ (fun p : (Bool × Work) × PrivateInstruction => fun k : Address × (Work × Work × Work × Work) =>
        (Sum.inl (k.1,(encodeState (.active p.1.1 k.2.1),encodeState (.active p.1.1 k.2.2.1),
          encodeState (.active p.1.1 k.2.2.2.1),encodeState (.active p.1.1 k.2.2.2.2))) : NativeIndependentExecution.Instruction))
      apply Primrec.sumInl.comp
      apply Primrec.pair (Primrec.fst.comp Primrec.snd)
      apply Primrec.pair
      · exact enc.comp (active_prim.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      apply Primrec.pair
      · exact enc.comp (active_prim.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      apply Primrec.pair
      · exact enc.comp (active_prim.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
      · exact enc.comp (active_prim.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    · apply Primrec.sumCasesOn Primrec.snd
      · exact (Primrec.sumInr.comp (Primrec.sumInl.comp (enc.comp
          (active_prim.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd)))).to₂
      · exact (Primrec.sumInr.comp (Primrec.sumInl.comp (enc.comp
          (ready_prim.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (work_fields.2.2.2.1.comp
              (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))))).to₂
  have body : Primrec (fun p : Bool × Work => finiteInstruction (.active p.1 p.2)) :=
    active.comp (Primrec.id.pair private_all)
  have h : Primrec (fun s : Unit ⊕ ((Bool × Work) ⊕ (Bool × List Cell)) =>
      finiteInstruction (stateEquiv.symm s)) := by
    suffices h : Primrec (fun s : Unit ⊕ ((Bool × Work) ⊕ (Bool × List Cell)) =>
      Sum.casesOn (motive := fun _ => NativeIndependentExecution.Instruction) s
        (fun _ => finiteInstruction .entry)
        (fun r => Sum.casesOn (motive := fun _ => NativeIndependentExecution.Instruction) r (fun p => finiteInstruction (.active p.1 p.2))
          (fun _ => (Sum.inr (Sum.inr ()) : NativeIndependentExecution.Instruction)))) by
      apply h.of_eq
      intro s
      rcases s with ⟨⟩ | (⟨q,w⟩ | ⟨q,r⟩) <;> rfl
    apply Primrec.sumCasesOn Primrec.id
    · exact (Primrec.const (finiteInstruction .entry)).to₂
    · apply Primrec.sumCasesOn Primrec.snd
      · exact (body.comp Primrec.snd).to₂
      · exact (Primrec.const (Sum.inr (Sum.inr ()) : NativeIndependentExecution.Instruction)).to₂
  exact (h.comp (Primrec.of_equiv (e := stateEquiv))).of_eq
    (by intro s; simp only [stateEquiv.symm_apply_apply])

/-- Invalid natural encodings use the fixed source-independent entry. -/
def numericInstruction (n : Nat) : NativeIndependentExecution.Instruction :=
  finiteInstruction ((Encodable.decode n).getD .entry)

private theorem numeric_prim : Primrec numericInstruction :=
  finite_prim.comp (Primrec.option_getD.comp Primrec.decode (Primrec.const State.entry))

/-- Re-encode just the complete control, preserving the instruction and address. -/
def encodedOp : NativeIndependentExecution.Op State → NativeIndependentExecution.Op Nat
  | .localStep s => .localStep (encodeState s)
  | .read p f => .read p (fun y => encodeState (f y))
  | .ret => .ret

private theorem finite_exact (s : State) :
    NativeIndependentExecution.instruction (finiteInstruction s) = encodedOp (step s) := by
  cases s with
  | entry =>
    simp [finiteInstruction,NativeIndependentExecution.instruction,encodedOp,step]
    funext y
    cases y <;> rfl
  | ready q row => rfl
  | active q w =>
    simp only [step,finiteInstruction]
    cases privateStep q w with
    | inl p =>
      rcases p with ⟨p,k⟩
      simp [NativeIndependentExecution.instruction,encodedOp,lift]
      funext y
      cases y <;> rfl
    | inr p => cases p <;> rfl

/-- One fixed recursive program computes every single actual microstep on the
whole configuration, including Read continuations and the separate Return. -/
theorem effective_selected_machine :
    Function.Injective encodeState ∧
    ∃ P : NativeIndependentExecution.EffectiveProgram,
      ∀ s : State, P.transition (encodeState s) = encodedOp (step s) := by
  have h : Nat.Primrec (fun n => Encodable.encode (numericInstruction n)) :=
    Primrec.nat_iff.mp (Primrec.encode.comp numeric_prim)
  obtain ⟨code,realizes⟩ := Nat.Partrec.Code.exists_code.mp (Nat.Partrec.of_primrec h)
  refine ⟨Encodable.encode_injective,⟨code,numericInstruction,?_⟩,?_⟩
  · intro n
    exact congrFun realizes n
  · intro s
    simpa only [NativeIndependentExecution.EffectiveProgram.transition,numericInstruction,
      encodeState,Encodable.encodek,Option.getD_some] using finite_exact s

private theorem run_boundary {c b : State} {u : GenealogicalFiberTransport.Source}
    {h : NativeIndependentExecution.Word} (run : NativeIndependentExecution.Run step c u h b) :
    ∃ (q : Bool) (row : List Cell), b = .ready q row := by
  induction run with
  | @ret c U hop =>
    cases c with
    | entry => simp [step] at hop
    | ready q row => exact ⟨q,row,rfl⟩
    | active q w =>
      cases hi : privateStep q w with
      | inl p => simp [step,hi,lift] at hop
      | inr p => cases p <;> simp [step,hi,lift] at hop
  | localStep _ _ ih => exact ih
  | read _ _ _ ih => exact ih
  | update _ ih => exact ih

/-- One source-independent effective program, authentic complete rows on every
returning history, return under every finite active interference schedule, and
exact invocation support of the whole selected root boundary. -/
theorem selected_producer_contract :
    (Function.Injective encodeState ∧
      ∃ P : NativeIndependentExecution.EffectiveProgram,
        ∀ s : State, P.transition (encodeState s) = encodedOp (step s)) ∧
    (∀ (u : GenealogicalFiberTransport.Source) (h : NativeIndependentExecution.Word) (b : State),
      NativeIndependentExecution.Run step .entry u h b →
        ∃ (q : Bool) (row : List Cell), b = .ready q row ∧
          NativeSelectedRARecordSoundness.Captured u
            (NativeSelectedRARecordSoundness.eventSchedule h) h.length q row) ∧
    (∀ (u : GenealogicalFiberTransport.Source) (σ : Nat → Bool),
      Set.Finite {n : Nat | σ n = true ∧
        (trajectory σ ⟨.entry,u,false⟩ n).returned = false} →
      ∃ m : Nat, (trajectory σ ⟨.entry,u,false⟩ m).returned = true) ∧
    (∀ u : GenealogicalFiberTransport.Source,
      (∃ h : NativeIndependentExecution.Word,
        NativeIndependentExecution.Run step .entry u h (.ready true rootBytes)) ↔ u = .of true) ∧
    (∀ (u : GenealogicalFiberTransport.Source) (j : Nat),
      ActualCutPartitionDecoder.literalRecord {[]} (GenealogicalFiberTransport.substitution^[j] u) =
        NativeFiveHoleFiber.rootLabel) := by
  refine ⟨effective_selected_machine,?_,NativeSelectedRAProgress.finite_interference_terminates,
    selected_root_support.1,selected_root_support.2.2.2.2.1⟩
  intro u h b run
  obtain ⟨q,row,rfl⟩ := run_boundary run
  exact ⟨q,row,rfl,NativeSelectedRARecordSoundness.all_returning_histories u h q row run⟩

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAEffective
