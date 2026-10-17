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

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
