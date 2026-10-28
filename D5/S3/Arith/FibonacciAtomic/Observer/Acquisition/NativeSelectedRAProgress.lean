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

/-- Guard search starts with empty row and operand regions and empty latches. -/
def GuardFresh (w : Work) : Prop :=
  w.row = [] ∧ w.operand = [] ∧ w.guardReply = .absent ∧
    w.leftReply = .absent ∧ w.rightReply = .absent

/-- Phase-specific concrete cursor conditions. Cleanup records which regions
have already been retracted; reset records when the guard region is empty. -/
def Frontier (U : Source) (q : Bool) (w : Work) : Prop :=
  match w.pc.val with
  | 1 => GuardFresh w ∧ readout w.guardPath U ≠ .absent
  | 2 => GuardFresh w ∧ readout w.guardPath U = .branch
  | 3 | 5 | 6 | 7 | 8 | 9 | 10 | 25 | 29 | 40 | 50 => True
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
  | 51 => w.row = []
  | 52 => w.row = [] ∧ w.operand = []
  | 53 => w.row = [] ∧ w.operand = [] ∧ w.guardPath = []
  | 54 => w.row = [] ∧ w.operand = [] ∧ w.guardPath = [] ∧ w.guardReply = .absent
  | 55 => w.row = [] ∧ w.operand = [] ∧ w.guardPath = [] ∧
      w.guardReply = .absent ∧ w.leftReply = .absent
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
    | exact ⟨h.1,present _ h.2⟩
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
    cases hy : readout g U <;> simp_all [Safe,Frontier,GuardFresh]
  case «2» => exact ⟨h.1,(children U g).1 h.2 false⟩
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
  case «55» => simpa [GuardFresh] using root_present U

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
        simpa [worldEvent,step,Safe,Frontier,emptyWork,GuardFresh] using root_present U
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
conditions. In particular no such lead enters the error control. -/
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

/-- A stationary comparison reaches its actual exit control, with a finite
update-free prefix that composes with every subsequent legal execution. -/
def ScanFinishes (U : Source) (c : State) : Prop :=
  ∃ v : Work, v.pc = 8 ∧ Continues U c (.active false v)

private theorem finish_prefix {U : Source} {c d : State}
    (lead : Continues U c d) (next : ScanFinishes U d) : ScanFinishes U c := by
  obtain ⟨v,hv,tail⟩ := next
  refine ⟨v,hv,?_⟩
  intro h b run
  obtain ⟨t,ht,rt⟩ := tail h b run
  obtain ⟨s,hs,rs⟩ := lead (t ++ h) b rt
  exact ⟨s ++ t,by simp [hs,ht],by simpa [List.append_assoc] using rs⟩

private theorem finish_local {U : Source} {c d : State}
    (hop : step c = .localStep d) (next : ScanFinishes U d) : ScanFinishes U c := by
  obtain ⟨v,hv,tail⟩ := next
  refine ⟨v,hv,?_⟩
  intro h b run
  obtain ⟨t,ht,rt⟩ := tail h b run
  exact ⟨.observer .localStep :: t,by simp [ht],Run.localStep hop rt⟩

private theorem finish_read {U : Source} {c : State} {p : Address} {f : Reply → State}
    (hop : step c = .read p f) (next : ScanFinishes U (f (readout p U))) :
    ScanFinishes U c := by
  obtain ⟨v,hv,tail⟩ := next
  refine ⟨v,hv,?_⟩
  intro h b run
  obtain ⟨t,ht,rt⟩ := tail h b run
  exact ⟨.observer (.read p (readout p U)) :: t,by simp [ht],Run.read hop rfl rt⟩

private theorem finish_eight (U : Source) (w : Work) (hp : w.pc = 8) :
    ScanFinishes U (.active false w) := by
  refine ⟨w,hp,?_⟩
  intro h b run
  exact ⟨[],by simp,run⟩

private theorem finish_twenty (U : Source) (w : Work) (z : Address)
    (present : PairPresent U z)
    (after : ∀ v : Work, v.pc = 27 → v.operand = true :: z →
      ScanFinishes U (.active false v)) :
    ScanFinishes U (.active false (pairStart w z)) := by
  have access := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have exists_at (p : Address) (hp : readout p U ≠ .absent) :
      ∃ T : Source, subtree p U = some T := by
    have hr := access p [] U
    simp only [List.append_nil] at hr
    cases he : subtree p U with
    | none => simp [he] at hr; exact (hp hr).elim
    | some T => exact ⟨T,rfl⟩
  obtain ⟨A,ha⟩ := exists_at (false :: z) (present false)
  obtain ⟨B,hb⟩ := exists_at (true :: z) (present true)
  have left (a : Address) : readout (false :: (z ++ a)) U = readout a A := by
    simpa only [List.cons_append,ha] using access (false :: z) a U
  have right (a : Address) : readout (true :: (z ++ a)) U = readout a B := by
    simpa only [List.cons_append,hb] using access (true :: z) a U
  by_cases root : z = []
  · subst z
    obtain ⟨v,hv,_,_,_,lead⟩ := pair_complete U A B w left right
    exact ⟨v,hv,lead⟩
  · by_cases equal : A = B
    · subst B
      exact finish_prefix (pair_equal_scan U A w z left right)
        (after (pairDone w z (rightLeafReply A)) rfl rfl)
    · obtain ⟨v,hv,_,_,_,lead⟩ := pair_unequal_scan U A B w z left right equal
      apply finish_prefix lead
      apply finish_local (d := .active false (put 8 9 v))
      · simp [step,lift,privateStep,localInstruction,hv,put]
      · exact finish_eight U _ rfl

private theorem finish_after (U : Source) (z : Address) :
    ∀ w : Work, w.pc = 27 → w.operand = true :: z → PairPresent U z →
      ScanFinishes U (.active false w) := by
  induction z using List.reverseRecOn with
  | nil =>
    intro w hp ho _
    apply finish_local (d := .active false (put 8 10 w))
    · simp [step,lift,privateStep,localInstruction,hp,ho,put]
    · exact finish_eight U _ rfl
  | append_singleton s d ih =>
    intro w hp ho present
    have forks : PairBranch U s := by
      simpa using pair_retract U (s ++ [d]) present (by simp)
    have parent : PairPresent U s := fun b => by rw [forks b]; decide
    cases d with
    | true =>
      apply finish_local (d := .active false {w with operand := true :: s})
      · simp [step,lift,privateStep,localInstruction,hp,ho,pop,lastBit,
          List.getLast?_cons,List.dropLast_cons_of_ne_nil]
      · exact ih _ hp rfl parent
    | false =>
      let a : Work := {w with pc := 28,operand := true :: s}
      let b : Work := {w with pc := 31,operand := true :: (s ++ [true])}
      apply finish_local (d := .active false a)
      · simp [step,lift,privateStep,localInstruction,hp,ho,pop,lastBit,a,
          List.getLast?_cons,List.dropLast_cons_of_ne_nil]
      apply finish_local (d := .active false b)
      · rfl
      apply finish_local (d := .active false (pairStart w (s ++ [true])))
      · rfl
      apply finish_twenty U w (s ++ [true]) (pair_descend U s forks true)
      intro v hv hvo
      apply finish_local (d := .active false {v with operand := true :: s})
      · simp [step,lift,privateStep,localInstruction,hv,hvo,pop,lastBit,
          List.getLast?_cons,List.dropLast_cons_of_ne_nil]
      · exact ih _ hv rfl parent

private theorem finish_start (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 20) (ho : w.operand = false :: z) (present : PairPresent U z) :
    ScanFinishes U (.active false w) := by
  have hw : pairStart w z = w := by cases w; simp_all [pairStart]
  have h := finish_twenty U w z present (fun v hv hvo => finish_after U z v hv hvo present)
  simpa only [hw] using h

private theorem finish_switch (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 31) (ho : w.operand = true :: z) (present : PairPresent U z) :
    ScanFinishes U (.active false w) := by
  apply finish_local (d := .active false (pairStart w z))
  · simp [step,lift,privateStep,localInstruction,hp,ho,switch,pairStart]
  · exact finish_start U _ z rfl rfl present

private theorem finish_child (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 26) (ho : w.operand = false :: z) (forks : PairBranch U z) :
    ScanFinishes U (.active false w) := by
  apply finish_local (d := .active false (pairStart w (z ++ [false])))
  · simp [step,lift,privateStep,localInstruction,hp,ho,pairStart]
  · exact finish_start U _ (z ++ [false]) rfl rfl (pair_descend U z forks false)

private theorem finish_descend (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 24) (ho : w.operand = true :: z) (forks : PairBranch U z) :
    ScanFinishes U (.active false w) := by
  let next : Work := {w with pc := 26,operand := false :: z}
  apply finish_local (d := .active false next)
  · simp [step,lift,privateStep,localInstruction,hp,ho,switch,next]
  · exact finish_child U next z rfl rfl forks

private theorem finish_sibling (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 28) (ho : w.operand = true :: z) (forks : PairBranch U z) :
    ScanFinishes U (.active false w) := by
  let next : Work := {w with pc := 31,operand := true :: (z ++ [true])}
  apply finish_local (d := .active false next)
  · simp [step,lift,privateStep,localInstruction,hp,ho,next]
  · exact finish_switch U next (z ++ [true]) rfl rfl (pair_descend U z forks true)

private theorem finish_decision (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 23) (ho : w.operand = true :: z) (present : PairPresent U z)
    (left : Saved U (false :: z) w.leftReply) (right : Saved U (true :: z) w.rightReply) :
    ScanFinishes U (.active false w) := by
  by_cases different : w.leftReply ≠ w.rightReply
  · apply finish_local (d := .active false (go 29 w))
    · simp [step,lift,privateStep,localInstruction,hp,different,go]
    apply finish_local (d := .active false (put 8 9 (go 29 w)))
    · rfl
    · exact finish_eight U _ rfl
  · have equal : w.leftReply = w.rightReply := not_ne_iff.mp different
    by_cases branch : w.leftReply = .branch
    · have rightBranch : w.rightReply = .branch := equal.symm.trans branch
      apply finish_local (d := .active false (go 24 w))
      · simp [step,lift,privateStep,localInstruction,hp,branch,rightBranch,go]
      apply finish_descend U (go 24 w) z rfl ho
      intro b
      cases b with
      | false => exact left.2 branch
      | true => exact right.2 (equal.symm.trans branch)
    · have leaf : w.leftReply = .alpha ∨ w.leftReply = .beta := by
        cases he : w.leftReply <;> simp_all [Saved]
      apply finish_local (d := .active false (go 27 w))
      · simp [step,lift,privateStep,localInstruction,hp,different,branch,leaf,go]
      · exact finish_after U z (go 27 w) rfl ho present

private theorem finish_right_read (U : Source) (w : Work) (z : Address)
    (hp : w.pc = 22) (ho : w.operand = true :: z) (present : PairPresent U z)
    (left : Saved U (false :: z) w.leftReply) : ScanFinishes U (.active false w) := by
  apply finish_read (p := w.operand)
    (f := fun y => .active false {w with pc := 23,rightReply := y})
  · simp [step,lift,privateStep,receipt,follow,hp]
    funext y
    cases y <;> rfl
  apply finish_decision U {w with pc := 23,rightReply := readout w.operand U}
    z rfl ho present left
  simpa only [ho] using
    (show Saved U (true :: z) (readout (true :: z) U) from ⟨present true,fun h => h⟩)

private theorem finish_frontier (U : Source) (q : Bool) (w : Work)
    (safe : Frontier U q w) (phase : w.pc.val ∈ [20,21,22,23,24,26,27,28,31]) :
    ScanFinishes U (.active q w) := by
  rcases w with ⟨⟨pc,hpc⟩,g,o,r,a,b,c⟩
  change pc ∈ [20,21,22,23,24,26,27,28,31] at phase
  simp only [List.mem_cons,List.not_mem_nil,or_false] at phase
  rcases phase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Frontier] at safe
  · rcases safe with ⟨rfl,z,ho,present⟩
    exact finish_start U _ z rfl ho present
  · rcases safe with ⟨rfl,z,ho,present,left⟩
    let next : Work := ⟨22,g,true :: z,r,a,b,c⟩
    apply finish_local (d := .active false next)
    · simp [step,lift,privateStep,localInstruction,ho,switch,next]
    · exact finish_right_read U next z rfl rfl present left
  · rcases safe with ⟨rfl,z,ho,present,left⟩
    exact finish_right_read U _ z rfl ho present left
  · rcases safe with ⟨rfl,z,ho,present,left,right⟩
    exact finish_decision U _ z rfl ho present left right
  · rcases safe with ⟨rfl,z,ho,forks⟩
    exact finish_descend U _ z rfl ho forks
  · rcases safe with ⟨rfl,z,ho,forks⟩
    exact finish_child U _ z rfl ho forks
  · rcases safe with ⟨rfl,z,ho,present⟩
    exact finish_after U z _ rfl ho present
  · rcases safe with ⟨rfl,z,ho,forks⟩
    exact finish_sibling U _ z rfl ho forks
  · rcases safe with ⟨rfl,z,ho,present⟩
    exact finish_switch U _ z rfl ho present

/-- An actual prefix can stop between either read, during descent or during
upward retraction. Its current comparison resumes on that same current source. -/
theorem reachable_scan_frontier_progress (u : Source) (σ : Nat → Bool) (n : Nat) :
    Safe (trajectory σ ⟨.entry,u,false⟩ n).source
      (trajectory σ ⟨.entry,u,false⟩ n).config ∧
    ∀ (q : Bool) (v : Work),
      (trajectory σ ⟨.entry,u,false⟩ n).config = .active q v →
      v.pc.val ∈ [20,21,22,23,24,26,27,28,31] →
      ScanFinishes (trajectory σ ⟨.entry,u,false⟩ n).source (.active q v) := by
  have safe := (reachable_scan_frontier u σ n).1
  refine ⟨safe,?_⟩
  intro q v hv phase
  rw [hv] at safe
  exact finish_frontier _ q v safe phase


/-- A stationary returning execution from the actual whole configuration. -/
def Halts (U : Source) (c : State) : Prop :=
  ∃ (h : Word) (b : State), .update ∉ h ∧ Run step c U h b

private theorem halt_prefix {U : Source} {c d : State}
    (lead : Continues U c d) (next : Halts U d) : Halts U c := by
  obtain ⟨h,b,hh,run⟩ := next
  obtain ⟨t,ht,rt⟩ := lead h b run
  exact ⟨t ++ h,b,by simp [ht,hh],rt⟩

private theorem halt_local {U : Source} {c d : State}
    (hop : step c = .localStep d) (next : Halts U d) : Halts U c := by
  obtain ⟨h,b,hh,run⟩ := next
  exact ⟨.observer .localStep :: h,b,by simp [hh],Run.localStep hop run⟩

private theorem halt_read {U : Source} {c : State} {p : Address} {f : Reply → State}
    (hop : step c = .read p f) (next : Halts U (f (readout p U))) : Halts U c := by
  obtain ⟨h,b,hh,run⟩ := next
  exact ⟨.observer (.read p (readout p U)) :: h,b,by simp [hh],Run.read hop rfl run⟩

private theorem halt_local_suffix {U : Source} {c d : State}
    (hop : step c = .localStep d) (h : Halts U c) : Halts U d := by
  obtain ⟨t,b,ht,run⟩ := h
  cases run with
  | ret he => simp [hop] at he
  | localStep he rest =>
    have eq : _ = d := Op.localStep.inj (he.symm.trans hop)
    subst eq
    exact ⟨_,_,by simpa using ht,rest⟩
  | read he _ _ => simp [hop] at he
  | update _ => simp at ht

private theorem cleanup_halts (U : Source) (q : Bool) (w : Work) :
    Halts U (.active q (go 40 w)) := by
  have none (n : Nat) : .update ∉ NativeIndependentExecution.expand
      (cleanupTiming n (fun _ => 0)) := by
    induction n with
    | zero => simp [cleanupTiming,NativeIndependentExecution.expand]
    | succ n ih => simpa [cleanupTiming,NativeIndependentExecution.expand] using ih
  exact ⟨_,_,none _,cleanup_every_schedule q w (fun _ => 0) U⟩

private theorem body_halts (U : Source) (q : Bool) (w : Work)
    (next : ∀ v : Work, v.pc = 25 → v.guardPath = w.guardPath →
      v.guardReply = w.guardReply → Halts U (.active q v)) :
    Halts U (.active q (go 3 w)) := by
  cases q with
  | true =>
    apply halt_local rfl
    apply halt_local rfl
    apply halt_local rfl
    apply halt_local rfl
    apply halt_local rfl
    exact next _ rfl rfl rfl
  | false =>
    apply halt_local rfl
    apply halt_read (p := [])
      (f := fun y => .active false {go 4 w with pc :=
        if y = .alpha then 9 else if y = .beta then 10 else if y = .branch then 11 else 99})
    · simp [step,lift,privateStep,receipt,follow,go]
      funext y
      cases y <;> rfl
    cases U with
    | of b =>
      cases b <;> simp only [readout,↓reduceIte,Bool.false_eq_true]
      all_goals
        apply halt_local rfl
        apply halt_local rfl
        apply halt_local rfl
        exact next _ rfl rfl rfl
    | mul A B =>
      simp only [readout,↓reduceIte]
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      let v := put 19 forkPrefix[7] (put 18 forkPrefix[6] (put 17 forkPrefix[5]
        (put 16 forkPrefix[4] (put 15 forkPrefix[3] (put 14 forkPrefix[2]
        (put 13 forkPrefix[1] (put 12 forkPrefix[0] (go 11 w))))))))
      change Halts (.mul A B) (.active false v)
      apply halt_local (d := .active false (pairStart v [])) rfl
      obtain ⟨d,hpc,_,hg,hr,lead⟩ := pair_complete (.mul A B) A B v
        (fun _ => rfl) (fun _ => rfl)
      apply halt_prefix lead
      apply halt_local (d := .active false (put 25 5 d))
      · simp [step,lift,privateStep,localInstruction,hpc,put]
      apply next _ rfl
      · simpa [v,put,go] using hg
      · simpa [v,put,go] using hr

private theorem fresh_halts (U T : Source) (q : Bool) (p : Address)
    (observed : ∀ z : Address, readout (p ++ z) U = readout z T) :
    Halts U (.active q {emptyWork with guardPath := p}) := by
  obtain ⟨g,ell,_,hy,lead⟩ := guard_search U T q p observed
  apply halt_prefix lead
  apply body_halts U q {emptyWork with pc := 3,guardPath := g,guardReply := ell}
  intro v hp hg hr
  apply halt_read (p := v.guardPath)
    (f := fun y => .active q (go (if y = v.guardReply then 40 else 50) v))
  · simp [step,lift,privateStep,receipt,follow,hp]
    funext y
    cases y <;> rfl
  have valid : readout v.guardPath U = v.guardReply := by simpa [hg,hr] using hy
  simpa only [valid,↓reduceIte] using cleanup_halts U q v


private theorem reset_guard_halts (U : Source) (q : Bool) (w : Work)
    (row : w.row = []) (operand : w.operand = []) :
    Halts U (.active q (go 52 w)) := by
  induction hn : w.guardPath.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases empty : w.guardPath = []
    · apply halt_local (d := .active q (go 53 w))
      · simp [step,lift,privateStep,localInstruction,go,empty]
      apply halt_local rfl
      apply halt_local rfl
      apply halt_local rfl
      simpa [emptyWork,go,row,operand,empty] using fresh_halts U U q [] (fun _ => rfl)
    · have shorter : (pop w.guardPath).length < n := by
        have pos := List.length_pos_iff.mpr empty
        simp only [pop,List.length_dropLast]
        omega
      apply halt_local (d := .active q (go 52 {w with guardPath := pop w.guardPath}))
      · simp [step,lift,privateStep,localInstruction,go,empty]
      exact ih _ shorter _ row operand rfl

private theorem reset_operand_halts (U : Source) (q : Bool) (w : Work)
    (row : w.row = []) : Halts U (.active q (go 51 w)) := by
  induction hn : w.operand.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases empty : w.operand = []
    · apply halt_local (d := .active q (go 52 w))
      · simp [step,lift,privateStep,localInstruction,go,empty]
      exact reset_guard_halts U q w row empty
    · have shorter : (pop w.operand).length < n := by
        have pos := List.length_pos_iff.mpr empty
        simp only [pop,List.length_dropLast]
        omega
      apply halt_local (d := .active q (go 51 {w with operand := pop w.operand}))
      · simp [step,lift,privateStep,localInstruction,go,empty]
      exact ih _ shorter _ row rfl

private theorem reset_halts (U : Source) (q : Bool) (w : Work) :
    Halts U (.active q (go 50 w)) := by
  induction hn : w.row.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases empty : w.row = []
    · apply halt_local (d := .active q (go 51 w))
      · simp [step,lift,privateStep,localInstruction,go,empty]
      exact reset_operand_halts U q w empty
    · have shorter : (pop w.row).length < n := by
        have pos := List.length_pos_iff.mpr empty
        simp only [pop,List.length_dropLast]
        omega
      apply halt_local (d := .active q (go 50 {w with row := pop w.row}))
      · simp [step,lift,privateStep,localInstruction,go,empty]
      exact ih _ shorter _ rfl

private theorem validation_halts (U : Source) (q : Bool) (w : Work) :
    Halts U (.active q (go 25 w)) := by
  apply halt_read (p := w.guardPath)
    (f := fun y => .active q (go (if y = w.guardReply then 40 else 50) w))
  · simp [step,lift,privateStep,receipt,follow,go]
    funext y
    cases y <;> rfl
  by_cases valid : readout w.guardPath U = w.guardReply
  · simpa only [valid,↓reduceIte] using cleanup_halts U q w
  · simpa only [valid,↓reduceIte] using reset_halts U q w

private theorem eight_halts (U : Source) (q : Bool) (w : Work) (hp : w.pc = 8) :
    Halts U (.active q w) := by
  apply halt_local (d := .active q (put 25 5 w))
  · simp [step,lift,privateStep,localInstruction,hp,put]
  exact validation_halts U q (put 25 5 w)

private theorem scan_halts (U : Source) (c : State) (h : ScanFinishes U c) :
    Halts U c := by
  obtain ⟨v,hp,lead⟩ := h
  exact halt_prefix lead (eight_halts U false v hp)


private theorem guard_halts (U : Source) (q : Bool) (w : Work) (hp : w.pc = 1)
    (fresh : GuardFresh w) (present : readout w.guardPath U ≠ .absent) :
    Halts U (.active q w) := by
  have access := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have root := access w.guardPath [] U
  simp only [List.append_nil] at root
  cases ht : subtree w.guardPath U with
  | none => simp [ht] at root; exact (present root).elim
  | some T =>
    have lead := fresh_halts U T q w.guardPath (by intro z; simpa [ht] using access w.guardPath z U)
    have shape : {emptyWork with guardPath := w.guardPath} = w := by
      rcases w with ⟨pc,g,o,r,a,b,c⟩
      simp_all [GuardFresh,emptyWork]
    simpa only [shape] using lead

set_option maxHeartbeats 2000000 in
-- The termination proof checks the same finite control table as preservation.
private theorem frontier_halts (U : Source) (q : Bool) (w : Work)
    (safe : Frontier U q w) : Halts U (.active q w) := by
  by_cases scan : w.pc.val ∈ [20,21,22,23,24,26,27,28,31]
  · exact scan_halts U _ (finish_frontier U q w safe scan)
  rcases w with ⟨pc,g,o,r,a,b,c⟩
  fin_cases pc <;> simp only [Frontier] at safe
  all_goals first
    | contradiction
    | exact validation_halts U q _
    | exact cleanup_halts U q _
    | exact reset_halts U q _
    | exact eight_halts U q _ rfl
    | skip
  case «1» => exact guard_halts U q _ rfl safe.1 safe.2
  case «2» =>
    apply halt_local rfl
    exact guard_halts U q _ rfl safe.1 ((children U g).1 safe.2 false)
  case «3» => exact body_halts U q ⟨3,g,o,r,a,b,c⟩ (fun v hp _ _ => by
    have hw : go 25 v = v := by cases v; simp_all [go]
    simpa [hw] using validation_halts U q v)
  case «4» =>
    subst q
    exact halt_local_suffix rfl (body_halts U false ⟨3,g,o,r,a,b,c⟩
      (fun v hp _ _ => by
        have hw : go 25 v = v := by cases v; simp_all [go]
        simpa [hw] using validation_halts U false v))
  case «5» =>
    apply halt_local rfl
    apply halt_local rfl
    apply halt_local rfl
    exact eight_halts U q _ rfl
  case «6» =>
    apply halt_local rfl
    apply halt_local rfl
    exact eight_halts U q _ rfl
  case «7» => apply halt_local rfl; exact eight_halts U q _ rfl
  case «9» =>
    apply halt_local rfl
    apply halt_local rfl
    exact eight_halts U q _ rfl
  case «10» =>
    apply halt_local rfl
    apply halt_local rfl
    exact eight_halts U q _ rfl
  all_goals try (simp only [List.mem_cons,List.not_mem_nil,or_false] at scan; contradiction)
  all_goals first
    | (rcases safe with ⟨rfl,branch⟩
       repeat' apply halt_local rfl
       apply scan_halts U
       apply finish_start U _ [] rfl rfl
       intro b
       exact (children U []).1 branch b)
    | skip
  case «25» => exact validation_halts U q ⟨25,g,o,r,a,b,c⟩
  case «40» => exact cleanup_halts U q ⟨40,g,o,r,a,b,c⟩
  case «50» => exact reset_halts U q ⟨50,g,o,r,a,b,c⟩
  case «29» => apply halt_local rfl; exact eight_halts U q _ rfl
  case «41» =>
    apply halt_local_suffix (c := .active q (go 40 ⟨41,g,o,r,a,b,c⟩))
    · simp [step,lift,privateStep,localInstruction,go,safe]
    exact cleanup_halts U q _
  case «42» =>
    have h := cleanup_halts U q ⟨42,g,o,r,a,b,c⟩
    have h := halt_local_suffix (d := .active q (go 41 ⟨42,g,o,r,a,b,c⟩))
      (by simp [step,lift,privateStep,localInstruction,go,safe.1]) h
    exact halt_local_suffix
      (by simp [step,lift,privateStep,localInstruction,go,safe.2]) h
  case «43» =>
    have h := cleanup_halts U q ⟨43,g,o,r,a,b,c⟩
    have h := halt_local_suffix (d := .active q (go 41 ⟨43,g,o,r,a,b,c⟩))
      (by simp [step,lift,privateStep,localInstruction,go,safe.1]) h
    have h := halt_local_suffix (d := .active q (go 42 ⟨43,g,o,r,a,b,c⟩))
      (by simp [step,lift,privateStep,localInstruction,go,safe.2.1]) h
    exact halt_local_suffix
      (by simp [step,lift,privateStep,localInstruction,go,safe.2.2]) h
  case «44» =>
    apply halt_local_suffix (c := .active q ⟨43,g,o,r,a,b,c⟩)
    · simp [step,lift,privateStep,localInstruction,go,safe.2.2.2]
    have h := cleanup_halts U q ⟨44,g,o,r,a,b,c⟩
    have h := halt_local_suffix (d := .active q (go 41 ⟨44,g,o,r,a,b,c⟩))
      (by simp [step,lift,privateStep,localInstruction,go,safe.1]) h
    have h := halt_local_suffix (d := .active q (go 42 ⟨44,g,o,r,a,b,c⟩))
      (by simp [step,lift,privateStep,localInstruction,go,safe.2.1]) h
    exact halt_local_suffix
      (by simp [step,lift,privateStep,localInstruction,go,safe.2.2.1]) h
  case «45» =>
    apply halt_local (d := .ready q r)
    · simp [step,lift,privateStep,localInstruction,safe]
    exact ⟨_,_,by simp,Run.ret rfl⟩
  case «51» => exact reset_operand_halts U q ⟨51,g,o,r,a,b,c⟩ safe
  case «52» => exact reset_guard_halts U q ⟨52,g,o,r,a,b,c⟩ safe.1 safe.2
  case «53» =>
    apply halt_local rfl
    apply halt_local rfl
    apply halt_local rfl
    simpa [emptyWork,safe.1,safe.2.1,safe.2.2] using fresh_halts U U q [] (fun _ => rfl)
  case «54» =>
    apply halt_local rfl
    apply halt_local rfl
    simpa [emptyWork,safe.1,safe.2.1,safe.2.2.1,safe.2.2.2] using fresh_halts U U q [] (fun _ => rfl)
  case «55» =>
    apply halt_local rfl
    simpa [emptyWork,safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2] using
      fresh_halts U U q [] (fun _ => rfl)


private theorem safe_halts (U : Source) (c : State) (h : Safe U c) : Halts U c := by
  cases c with
  | ready q row => exact ⟨_,_,by simp,Run.ret rfl⟩
  | active q w => exact frontier_halts U q w h
  | entry =>
    apply halt_read rfl
    exact guard_halts U _ emptyWork rfl (by simp [GuardFresh,emptyWork]) (root_present U)

private theorem observer_run {U : Source} {c b : State} {h : Word}
    (run : Run step c U h b) (none : .update ∉ h) :
    (worldEvent false)^[h.length] ⟨c,U,false⟩ = ⟨b,U,true⟩ := by
  induction run with
  | ret hop => simp [worldEvent,hop]
  | @localStep c d U h b hop run ih =>
    simp only [List.mem_cons,not_or] at none
    simpa only [List.length_cons,Function.iterate_succ_apply,worldEvent,
      Bool.false_eq_true,↓reduceIte,hop] using ih none.2
  | @read c U p f y h b hop hy run ih =>
    simp only [List.mem_cons,not_or] at none
    simpa only [List.length_cons,Function.iterate_succ_apply,worldEvent,
      Bool.false_eq_true,↓reduceIte,hop,hy] using ih none.2
  | update _ _ => simp at none

private theorem observer_trajectory (w : World) (n : Nat) :
    trajectory (fun _ => false) w n = (worldEvent false)^[n] w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [trajectory,ih,Function.iterate_succ_apply']

/-- Every source and schedule with finitely many active writer events returns.
All continuation arguments start at the actual interrupted configuration. -/
theorem finite_interference_terminates (u : Source) (σ : Nat → Bool)
    (finite : Set.Finite {n : Nat | σ n = true ∧
      (trajectory σ ⟨.entry,u,false⟩ n).returned = false}) :
    ∃ m : Nat, (trajectory σ ⟨.entry,u,false⟩ m).returned = true := by
  obtain ⟨N,bound⟩ := finite.bddAbove
  have event (k : Nat) :
      worldEvent (σ (N+1+k)) (trajectory σ ⟨.entry,u,false⟩ (N+1+k)) =
      worldEvent false (trajectory σ ⟨.entry,u,false⟩ (N+1+k)) := by
    cases returned : (trajectory σ ⟨.entry,u,false⟩ (N+1+k)).returned with
    | true => simp [worldEvent,returned]
    | false =>
      cases writer : σ (N+1+k) with
      | false => rfl
      | true => have impossible := bound ⟨writer,returned⟩; omega
  have suffix (k : Nat) : trajectory σ ⟨.entry,u,false⟩ (N+1+k) =
      trajectory (fun _ => false) (trajectory σ ⟨.entry,u,false⟩ (N+1)) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change worldEvent (σ (N+1+k)) (trajectory σ ⟨.entry,u,false⟩ (N+1+k)) =
        worldEvent false (trajectory (fun _ => false)
          (trajectory σ ⟨.entry,u,false⟩ (N+1)) k)
      rw [event k,ih]
  have safe := trajectory_safe u σ (N+1)
  cases hw : trajectory σ ⟨.entry,u,false⟩ (N+1) with
  | mk c U returned =>
    cases returned with
    | true => exact ⟨N+1,by simp [hw]⟩
    | false =>
      have hc : Safe U c := by simpa only [hw] using safe
      obtain ⟨h,b,none,run⟩ := safe_halts U c hc
      refine ⟨N+1+h.length,?_⟩
      rw [suffix,hw,observer_trajectory,observer_run run none]

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
