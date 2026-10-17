/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Reachable native scanner frontiers and continuation after independent updates. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeIndependentExecution (Op Run Word)
open NativeSelectedRA

private theorem root_present (U : Source) : readout [] U ≠ .absent := by
  cases U with
  | of b => cases b <;> simp [readout]
  | mul l r => simp [readout]

private theorem reply_transport (U : Source) (p : Address) :
    (readout p U ≠ .absent → readout p (substitution U) ≠ .absent) ∧
    (readout p U = .branch → readout p (substitution U) = .branch) := by
  have access := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have old := access p [] U
  simp only [List.append_nil] at old
  cases ht : subtree p U with
  | none => simp [ht] at old; simp [old]
  | some T =>
    have transported := NativeDepthPatterns.original_present_transport 1 p U T ht
    simp only [Function.iterate_one] at transported
    have fresh := access p [] (substitution U)
    simp only [List.append_nil,transported] at fresh
    rw [ht] at old
    simp only at old
    constructor
    · intro _; rw [fresh]; exact root_present _
    · intro branch
      rw [old] at branch
      cases T with
      | of b => cases b <;> simp [readout] at branch
      | mul l r => rw [fresh]; rfl

/-- Both actual positions named by a relative comparison cursor exist. -/
def PairPresent (U : Source) (z : Address) : Prop :=
  ∀ b : Bool, readout (b :: z) U ≠ .absent

/-- Both positions are branches, so either child is a legal next cursor. -/
def PairBranch (U : Source) (z : Address) : Prop :=
  ∀ b : Bool, readout (b :: z) U = .branch

/-- A saved reply remains nonabsent; a saved branch still denotes a branch.
Leaf labels need not be stable while the writer is active. -/
def Saved (U : Source) (p : Address) (y : Reply) : Prop :=
  y ≠ .absent ∧ (y = .branch → readout p U = .branch)

/-- Phase-specific concrete cursor conditions. Cleanup records which regions
have already been retracted; reset records when the guard region is empty. -/
def Frontier (U : Source) (q : Bool) (w : Work) : Prop :=
  match w.pc.val with
  | 1 => readout w.guardPath U ≠ .absent
  | 2 => readout w.guardPath U = .branch
  | 3 | 5 | 6 | 7 | 8 | 9 | 10 | 25 | 29 | 40 | 50 | 51 | 52 => True
  | 4 => q = false
  | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 =>
      q = false ∧ readout [] U = .branch
  | 20 => q = false ∧ ∃ z, w.operand = false :: z ∧ PairPresent U z
  | 21 => q = false ∧ ∃ z, w.operand = false :: z ∧ PairPresent U z ∧
      Saved U (false :: z) w.leftReply
  | 22 => q = false ∧ ∃ z, w.operand = true :: z ∧ PairPresent U z ∧
      Saved U (false :: z) w.leftReply
  | 23 => q = false ∧ ∃ z, w.operand = true :: z ∧ PairPresent U z ∧
      Saved U (false :: z) w.leftReply ∧ Saved U (true :: z) w.rightReply
  | 24 => q = false ∧ ∃ z, w.operand = true :: z ∧ PairBranch U z
  | 26 => q = false ∧ ∃ z, w.operand = false :: z ∧ PairBranch U z
  | 27 | 31 => q = false ∧ ∃ z, w.operand = true :: z ∧ PairPresent U z
  | 28 => q = false ∧ ∃ z, w.operand = true :: z ∧ PairBranch U z
  | 41 => w.operand = []
  | 42 => w.operand = [] ∧ w.guardPath = []
  | 43 => w.operand = [] ∧ w.guardPath = [] ∧ w.guardReply = .absent
  | 44 => w.operand = [] ∧ w.guardPath = [] ∧ w.guardReply = .absent ∧
      w.leftReply = .absent
  | 45 => w.operand = [] ∧ w.guardPath = [] ∧ w.guardReply = .absent ∧
      w.leftReply = .absent ∧ w.rightReply = .absent
  | 53 | 54 | 55 => w.guardPath = []
  | _ => False

/-- The condition concerns the actual source register and whole configuration. -/
def Safe (U : Source) : State → Prop
  | .entry | .ready _ _ => True
  | .active q w => Frontier U q w

set_option maxHeartbeats 2000000 in
-- The finite control split covers every concrete instruction code.
private theorem frontier_writer (U : Source) (q : Bool) (w : Work)
    (h : Frontier U q w) : Frontier (substitution U) q w := by
  have present (p : Address) := (reply_transport U p).1
  have branch (p : Address) := (reply_transport U p).2
  have pair (z : Address) (hz : PairPresent U z) : PairPresent (substitution U) z :=
    fun b => present _ (hz b)
  have forks (z : Address) (hz : PairBranch U z) : PairBranch (substitution U) z :=
    fun b => branch _ (hz b)
  have saved (p : Address) (y : Reply) (hy : Saved U p y) :
      Saved (substitution U) p y := ⟨hy.1,fun e => branch _ (hy.2 e)⟩
  rcases w with ⟨pc,g,o,r,a,b,c⟩
  fin_cases pc <;> simp only [Frontier] at h ⊢ <;>
    first
    | exact h
    | exact present _ h
    | exact branch _ h
    | exact ⟨h.1,branch _ h.2⟩
    | (rcases h with ⟨hq,z,ho,hz⟩; exact ⟨hq,z,ho,pair z hz⟩)
    | (rcases h with ⟨hq,z,ho,hz,hy⟩; exact ⟨hq,z,ho,pair z hz,saved _ _ hy⟩)
    | (rcases h with ⟨hq,z,ho,hz,hy,hy'⟩;
       exact ⟨hq,z,ho,pair z hz,saved _ _ hy,saved _ _ hy'⟩)
    | (rcases h with ⟨hq,z,ho,hz⟩; exact ⟨hq,z,ho,forks z hz⟩)

private theorem children (U : Source) (p : Address) :
    (readout p U = .branch → ∀ b : Bool, readout (p ++ [b]) U ≠ .absent) ∧
    (∀ b : Bool, readout (p ++ [b]) U ≠ .absent → readout p U = .branch) := by
  have access := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have root := access p [] U
  simp only [List.append_nil] at root
  cases ht : subtree p U with
  | none => simp [ht] at root; simp [root,access p _ U,ht]
  | some T =>
    rw [ht] at root
    simp only at root
    cases T with
    | of c =>
      cases c <;> simp [root,access p _ U,ht,readout]
    | mul l r =>
      constructor
      · intro _ b
        rw [access p [b] U,ht]
        cases b <;> exact root_present _
      · intro _ _; simpa [readout] using root

private theorem pair_descend (U : Source) (z : Address) (h : PairBranch U z)
    (b : Bool) : PairPresent U (z ++ [b]) := by
  intro c
  exact (children U (c :: z)).1 (h c) b

private theorem pair_retract (U : Source) (z : Address) (h : PairPresent U z)
    (hne : z ≠ []) : PairBranch U z.dropLast := by
  intro c
  apply (children U (c :: z.dropLast)).2 (z.getLast hne)
  simpa only [List.cons_append,List.dropLast_append_getLast hne] using h c

set_option maxHeartbeats 2000000 in
-- The finite control split covers every concrete instruction code.
private theorem active_observer (U : Source) (q : Bool) (w : Work)
    (h : Frontier U q w) :
    Safe U (worldEvent false ⟨.active q w,U,false⟩).config := by
  rcases w with ⟨pc,g,o,r,a,b,c⟩
  fin_cases pc <;>
    simp_all [Frontier,Safe,worldEvent,step,lift,privateStep,localInstruction,
      receipt,follow,go,put,switch]
  case «1» =>
    cases hy : readout g U <;> simp_all [Safe,Frontier]
  case «2» => exact (children U g).1 h false
  case «3» => cases q <;> simp [Safe,Frontier]
  case «4» =>
    cases U with
    | of d => cases d <;> simp [readout,Safe,Frontier]
    | mul l r => simp [readout,Safe,Frontier]
  case «19» =>
    exact fun d => (children U []).1 h.2 d
  case «20» =>
    rcases h with ⟨hq,z,rfl,hz⟩
    cases hy : readout (false :: z) U <;>
      simp_all [Safe,Frontier,Saved,PairPresent]
  case «21» =>
    rcases h with ⟨hq,z,rfl,hz,hy⟩
    simpa using And.intro hz hy
  case «22» =>
    rcases h with ⟨hq,z,rfl,hz,hy⟩
    cases he : readout (true :: z) U <;>
      simp_all [Safe,Frontier,Saved,PairPresent]
  case «23» =>
    rcases h with ⟨hq,z,rfl,hz,hb,hc⟩
    by_cases he : b = c
    · subst c
      cases b with
      | alpha => simpa [Safe,Frontier] using hz
      | beta => simpa [Safe,Frontier] using hz
      | branch =>
        have forks : PairBranch U z := by
          intro d
          cases d with
          | false => exact hb.2 rfl
          | true => exact hc.2 rfl
        simpa [Safe,Frontier] using forks
      | absent => exact (hb.1 rfl).elim
    · simp [he,Safe,Frontier]
  case «24» =>
    rcases h with ⟨hq,z,rfl,hz⟩
    exact hz
  case «25» => cases he : readout g U <;> cases a <;> simp [Safe,Frontier]
  case «26» =>
    rcases h with ⟨hq,z,rfl,hz⟩
    exact ⟨z ++ [false],rfl,pair_descend U z hz false⟩
  case «27» =>
    rcases h with ⟨hq,z,rfl,hz⟩
    by_cases he : z = []
    · simp [he,Safe,Frontier]
    · have hb := pair_retract U z hz he
      have hp : PairPresent U z.dropLast := fun d => by rw [hb d]; decide
      cases hl : lastBit (true :: z) <;>
        simp [he,hl,pop,List.dropLast_cons_of_ne_nil he,Safe,Frontier]
      · exact hb
      · exact hp
  case «28» =>
    rcases h with ⟨hq,z,rfl,hz⟩
    exact ⟨z ++ [true],rfl,pair_descend U z hz true⟩
  case «31» =>
    rcases h with ⟨hq,z,rfl,hz⟩
    exact hz
  case «40» => by_cases he : o = [] <;> simp [he,Safe,Frontier]
  case «41» => by_cases he : g = [] <;> simp [he,Safe,Frontier]
  case «50» => by_cases he : r = [] <;> simp [he,Safe,Frontier]
  case «51» => by_cases he : o = [] <;> simp [he,Safe,Frontier]
  case «52» => by_cases he : g = [] <;> simp [he,Safe,Frontier]
  case «55» => exact root_present U

private theorem safe_event (U : Source) (c : State) (r writer : Bool)
    (h : Safe U c) :
    Safe (worldEvent writer ⟨c,U,r⟩).source
      (worldEvent writer ⟨c,U,r⟩).config := by
  cases r with
  | true => simpa [worldEvent] using h
  | false =>
    cases writer with
    | true =>
      cases c with
      | entry => trivial
      | ready q row => trivial
      | active q w => exact frontier_writer U q w h
    | false =>
      cases c with
      | entry =>
        simpa [worldEvent,step,Safe,Frontier,emptyWork] using root_present U
      | ready q row => trivial
      | active q w =>
        have next := active_observer U q w h
        cases hs : step (.active q w) <;> simpa [worldEvent,hs] using next

private theorem trajectory_safe (u : Source) (σ : Nat → Bool) (n : Nat) :
    Safe (trajectory σ ⟨.entry,u,false⟩ n).source
      (trajectory σ ⟨.entry,u,false⟩ n).config := by
  induction n with
  | zero => trivial
  | succ n ih => exact safe_event _ _ _ _ ih

/-- Every finite independently interleaved prefix retains the actual cursor
conditions. In particular no such prefix enters the error control. -/
theorem reachable_scan_frontier (u : Source) (σ : Nat → Bool) (n : Nat) :
    Safe (trajectory σ ⟨.entry,u,false⟩ n).source
      (trajectory σ ⟨.entry,u,false⟩ n).config ∧
    ∀ (q : Bool) (v : Work),
      (trajectory σ ⟨.entry,u,false⟩ n).config = .active q v → v.pc.val ≠ 99 := by
  have safe := trajectory_safe u σ n
  refine ⟨safe,?_⟩
  intro q v hv error
  rw [hv] at safe
  simp only [Safe,Frontier,error] at safe

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
