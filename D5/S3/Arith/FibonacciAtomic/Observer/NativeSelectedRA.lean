/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Selected-cut cell transitions, paid cleanup and invocation-source support. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeIndependentExecution (Op Run Word)

/-- Cells use a fixed sixteen-letter alphabet. The used extent is the list
length, with no spare capacity or allocation identity beyond its fixed region. -/
abbrev Cell := Fin 16

/-- H, address letters, separators, constructor letters and partition bits. -/
def rootBytes : List Cell := [0,3,4,5]
def forkPrefix : List Cell := [6,0,1,3,0,2,3,4]
def leafBytes (b : Bool) : List Cell := [if b then 7 else 8,4,5]

/-- The complete private workspace. Regions have fixed identities; path heads
are at their ends. All finite control and reply latches are explicit. -/
structure Work where
  pc : Fin 100
  guardPath : Address
  operand : Address
  row : List Cell
  guardReply : Reply
  leftReply : Reply
  rightReply : Reply
  deriving DecidableEq

def emptyWork : Work := ⟨1,[],[],[],.absent,.absent,.absent⟩

/-- Only the selected cut and full row remain readable at the common ready
control. No private configuration or execution archive is retained there. -/
inductive State where
  | entry
  | active : Bool → Work → State
  | ready : Bool → List Cell → State
  deriving DecidableEq

/-- True selects the root; false selects the two child addresses. -/
def cut (q : Bool) : Finset Address := if q then {[]} else {[false],[true]}

/-- End-relative region operations change one cell. The first operand cell
is the selected base address and is protected from relative-path retraction. -/
def pop {α : Type} (a : List α) : List α := a.dropLast
def lastBit (a : Address) : Bool := a.getLast?.getD false
def switch (b : Bool) (a : Address) : Address := b :: a.tail

def go (n : Fin 100) (w : Work) : Work := {w with pc := n}
def put (n : Fin 100) (a : Cell) (w : Work) : Work :=
  {w with pc := n, row := w.row ++ [a]}

/-- One private instruction, with four concrete continuation configurations.
The unit case finishes a private subroutine, never an external Return. -/
abbrev PrivateInstruction := (Address × (Work × Work × Work × Work)) ⊕ (Work ⊕ Unit)

def localInstruction (w : Work) : PrivateInstruction := .inr (.inl w)
def receipt (p : Address) (f : Reply → Work) : PrivateInstruction :=
  .inl (p,(f .alpha,f .beta,f .branch,f .absent))

/-- The two fixed cuts permit finite unrolling of exterior and pair loops.
Guard search and relative preorder comparison retain their unbounded paths.
Every put, retraction, path change, latch reset and handoff is a local event. -/
def privateStep (q : Bool) (w : Work) : PrivateInstruction :=
  match w.pc.val with
  | 1 => receipt w.guardPath (fun y =>
      if y = .branch then go 2 w else
      if y = .alpha ∨ y = .beta then {w with pc := 3, guardReply := y}
      else go 99 w)
  | 2 => localInstruction {w with pc := 1, guardPath := w.guardPath ++ [false]}
  | 3 => localInstruction (go (if q then 5 else 4) w)
  | 4 => receipt [] (fun y => {w with pc :=
      if y = .alpha then 9 else if y = .beta then 10
      else if y = .branch then 11 else 99})
  | 5 => localInstruction (put 6 0 w)
  | 6 => localInstruction (put 7 3 w)
  | 7 => localInstruction (put 8 4 w)
  | 8 => localInstruction (put 25 5 w)
  | 9 => localInstruction (put 7 7 w)
  | 10 => localInstruction (put 7 8 w)
  | 11 => localInstruction (put 12 forkPrefix[0] w)
  | 12 => localInstruction (put 13 forkPrefix[1] w)
  | 13 => localInstruction (put 14 forkPrefix[2] w)
  | 14 => localInstruction (put 15 forkPrefix[3] w)
  | 15 => localInstruction (put 16 forkPrefix[4] w)
  | 16 => localInstruction (put 17 forkPrefix[5] w)
  | 17 => localInstruction (put 18 forkPrefix[6] w)
  | 18 => localInstruction (put 19 forkPrefix[7] w)
  | 19 => localInstruction {w with pc := 20, operand := [false]}
  | 20 => receipt w.operand (fun y => {w with pc := 21, leftReply := y})
  | 21 => localInstruction {w with pc := 22, operand := switch true w.operand}
  | 22 => receipt w.operand (fun y => {w with pc := 23, rightReply := y})
  | 23 => localInstruction (go (if w.leftReply ≠ w.rightReply then 29
      else if w.leftReply = .branch then 24
      else if w.leftReply = .alpha ∨ w.leftReply = .beta then 27 else 99) w)
  | 24 => localInstruction {w with pc := 26, operand := switch false w.operand}
  | 26 => localInstruction {w with pc := 20, operand := w.operand ++ [false]}
  | 27 => if w.operand.tail = [] then localInstruction (put 8 10 w)
      else if lastBit w.operand then localInstruction {w with operand := pop w.operand}
      else localInstruction {w with pc := 28, operand := pop w.operand}
  | 28 => localInstruction {w with pc := 31, operand := w.operand ++ [true]}
  | 31 => localInstruction {w with pc := 20, operand := switch false w.operand}
  | 29 => localInstruction (put 8 9 w)
  | 25 => receipt w.guardPath (fun y => go (if y = w.guardReply then 40 else 50) w)
  | 40 => if w.operand = [] then localInstruction (go 41 w)
      else localInstruction {w with operand := pop w.operand}
  | 41 => if w.guardPath = [] then localInstruction (go 42 w)
      else localInstruction {w with guardPath := pop w.guardPath}
  | 42 => localInstruction {w with pc := 43, guardReply := .absent}
  | 43 => localInstruction {w with pc := 44, leftReply := .absent}
  | 44 => localInstruction {w with pc := 45, rightReply := .absent}
  | 45 => if w.guardPath = [] ∧ w.operand = [] ∧
        w.guardReply = .absent ∧ w.leftReply = .absent ∧ w.rightReply = .absent
      then .inr (.inr ()) else localInstruction (go 99 w)
  | 50 => if w.row = [] then localInstruction (go 51 w) else localInstruction {w with row := pop w.row}
  | 51 => if w.operand = [] then localInstruction (go 52 w) else localInstruction {w with operand := pop w.operand}
  | 52 => if w.guardPath = [] then localInstruction (go 53 w) else localInstruction {w with guardPath := pop w.guardPath}
  | 53 => localInstruction {w with pc := 54, guardReply := .absent}
  | 54 => localInstruction {w with pc := 55, leftReply := .absent}
  | 55 => localInstruction {w with pc := 1, rightReply := .absent}
  | _ => localInstruction w

def follow (k : Work × Work × Work × Work) : Reply → Work
  | .alpha => k.1
  | .beta => k.2.1
  | .branch => k.2.2.1
  | .absent => k.2.2.2

def lift (q : Bool) (w : Work) : PrivateInstruction → Op State
  | .inl (p,k) => .read p (fun y => .active q (follow k y))
  | .inr (.inl v) => .localStep (.active q v)
  | .inr (.inr _) => .localStep (.ready q w.row)

/-- This single program has no source, epoch, schedule or advice argument.
The only outer Return occurs at the completely cleaned common ready state. -/
def step : State → Op State
  | .entry => .read [] (fun y => .active (decide (y = .alpha)) emptyWork)
  | .active q w => lift q w (privateStep q w)
  | .ready _ _ => .ret

def selected (s : State) : Option Bool :=
  match s with
  | .entry => none
  | .active q _ | .ready q _ => some q

private theorem lift_local_choice (q : Bool) (w : Work) (i : PrivateInstruction)
    (d : State) (h : lift q w i = .localStep d) : selected d = some q := by
  cases i with
  | inl p => simp [lift] at h
  | inr p => cases p with
    | inl v => cases h; rfl
    | inr u => cases h; rfl

private theorem lift_read_choice (q : Bool) (w : Work) (i : PrivateInstruction)
    (p : Address) (f : Reply → State) (h : lift q w i = .read p f) (y : Reply) :
    selected (f y) = some q := by
  cases i with
  | inl a =>
    rcases a with ⟨a,k⟩
    obtain ⟨rfl,rfl⟩ := Op.read.inj h
    rfl
  | inr a => cases a <;> simp [lift] at h

private theorem choice_preserved (s : State) (q : Bool) (u : Source)
    (h : Word) (b : State) (hs : selected s = some q) (r : Run step s u h b) :
    selected b = some q := by
  induction r with
  | ret _ => exact hs
  | @localStep s d u h b hop run ih =>
    apply ih
    cases s with
    | entry => simp [selected] at hs
    | ready q row => simp [step] at hop
    | active q' w =>
      have he : q' = q := by simpa [selected] using hs
      subst q'
      exact lift_local_choice q w _ d hop
  | @read s u p f y h b hop hy run ih =>
    apply ih
    cases s with
    | entry => simp [selected] at hs
    | ready q row => simp [step] at hop
    | active q' w =>
      have he : q' = q := by simpa [selected] using hs
      subst q'
      exact lift_read_choice q w _ p f hop y
  | update run ih => exact ih hs

/-- A proof-side finite quiescent prefix. This is not observer storage. -/
def Continues (U : Source) (c d : State) : Prop :=
  ∀ (h : Word) (b : State), Run step d U h b →
    ∃ w : Word, (.update ∉ w) ∧ Run step c U (w ++ h) b

private theorem continues_trans (U : Source) (c d e : State)
    (a : Continues U c d) (b : Continues U d e) : Continues U c e := by
  intro h z r
  obtain ⟨v,hv,rv⟩ := b h z r
  obtain ⟨w,hw,rw⟩ := a (v ++ h) z rv
  exact ⟨w ++ v, by simp [hw,hv], by simpa [List.append_assoc] using rw⟩

private theorem continues_local (U : Source) (c d : State)
    (hop : step c = .localStep d) : Continues U c d := by
  intro h b r
  exact ⟨[.observer .localStep], by simp, Run.localStep hop r⟩

private theorem continues_read (U : Source) (c d : State) (p : Address)
    (y : Reply) (hop : ∃ f : Reply → State, step c = .read p f ∧ f y = d)
    (hy : readout p U = y) : Continues U c d := by
  obtain ⟨f,hf,rfl⟩ := hop
  intro h b r
  exact ⟨[.observer (.read p y)], by simp, Run.read hf hy r⟩

/-- A proof-side chain of actual local transitions, counted individually. -/
private inductive LocalSteps : Nat → State → State → Prop
  | refl (c : State) : LocalSteps 0 c c
  | cons {n : Nat} {c d e : State} : step c = .localStep d →
      LocalSteps n d e → LocalSteps (n+1) c e

private theorem local_steps_continues {n : Nat} {c d : State}
    (s : LocalSteps n c d) (U : Source) : Continues U c d := by
  induction s with
  | refl c => intro h b r; exact ⟨[],by simp,r⟩
  | cons hop rest ih =>
    exact continues_trans U _ _ _ (continues_local U _ _ hop) ih

private theorem clean_latches (q : Bool) (w : Work)
    (hg : w.guardPath = []) (ho : w.operand = []) :
    LocalSteps 4 (.active q (go 42 w)) (.ready q w.row) := by
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons (d := .ready q w.row)
  · simp [step,lift,privateStep,localInstruction,go,hg,ho]
  · exact LocalSteps.refl _

private theorem clean_guard (q : Bool) (w : Work) (ho : w.operand = []) :
    LocalSteps (w.guardPath.length+5) (.active q (go 41 w)) (.ready q w.row) := by
  induction hn : w.guardPath.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hg : w.guardPath = []
    · have hn0 : n = 0 := by simpa [hg] using hn.symm
      subst n
      simpa [hg] using LocalSteps.cons
        (show step (.active q (go 41 w)) = .localStep (.active q (go 42 w)) by
          simp [step,lift,privateStep,localInstruction,go,hg])
        (clean_latches q w hg ho)
    · have shorter : (pop w.guardPath).length < n := by
        have hp : 0 < w.guardPath.length := List.length_pos_iff.mpr hg
        simp only [pop,List.length_dropLast]
        omega
      have hc := ih _ shorter {w with guardPath := pop w.guardPath} ho rfl
      have hs := LocalSteps.cons
        (show step (.active q (go 41 w)) =
          .localStep (.active q (go 41 {w with guardPath := pop w.guardPath})) by
          simp [step,lift,privateStep,localInstruction,go,hg]) hc
      convert hs using 1
      have hp : 0 < w.guardPath.length := List.length_pos_iff.mpr hg
      simp only [pop,List.length_dropLast]
      omega

private theorem cleanup_local_steps (q : Bool) (w : Work) :
    LocalSteps (w.operand.length+w.guardPath.length+6)
      (.active q (go 40 w)) (.ready q w.row) := by
  induction hn : w.operand.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases ho : w.operand = []
    · have hn0 : n = 0 := by simpa [ho] using hn.symm
      subst n
      have hs := LocalSteps.cons
        (show step (.active q (go 40 w)) = .localStep (.active q (go 41 w)) by
          simp [step,lift,privateStep,localInstruction,go,ho])
        (clean_guard q w ho)
      simpa [ho,Nat.add_assoc] using hs
    · have shorter : (pop w.operand).length < n := by
        have hp : 0 < w.operand.length := List.length_pos_iff.mpr ho
        simp only [pop,List.length_dropLast]
        omega
      have hc := ih _ shorter {w with operand := pop w.operand} rfl
      have hs := LocalSteps.cons
        (show step (.active q (go 40 w)) =
          .localStep (.active q (go 40 {w with operand := pop w.operand})) by
          simp [step,lift,privateStep,localInstruction,go,ho]) hc
      convert hs using 1
      have hp : 0 < w.operand.length := List.length_pos_iff.mpr ho
      simp only [pop,List.length_dropLast]
      omega

/-- Burst counts describe the independent writer, not the producer's input. -/
def cleanupTiming : Nat → (Nat → Nat) → NativeIndependentExecution.TimedWord
  | 0, σ => [(σ 0,.ret)]
  | n+1, σ => (σ 0,.localStep) :: cleanupTiming n (fun i => σ (i+1))

private theorem local_steps_scheduled {n : Nat} {c d : State}
    (s : LocalSteps n c d) (ret : step d = .ret) (σ : Nat → Nat) (U : Source) :
    Run step c U (NativeIndependentExecution.expand (cleanupTiming n σ)) d := by
  induction s generalizing σ U with
  | refl c =>
    exact (NativeIndependentExecution.updates_iff step (σ 0) _ _ _ _).mpr (Run.ret ret)
  | @cons n c d e hop rest ih =>
    apply (NativeIndependentExecution.updates_iff step (σ 0) _ _ _ _).mpr
    exact Run.localStep hop (ih ret (fun i => σ (i+1)) (substitution^[σ 0] U))

/-- Every cleanup microstep and the separate Return admit arbitrary independent
finite writer bursts. Exactly one local event retracts each private path cell;
the six further local events clear latches, change phases and hand off the row. -/
theorem cleanup_every_schedule (q : Bool) (w : Work) (σ : Nat → Nat) (U : Source) :
    Run step (.active q (go 40 w)) U
      (NativeIndependentExecution.expand
        (cleanupTiming (w.operand.length+w.guardPath.length+6) σ))
      (.ready q w.row) := by
  exact local_steps_scheduled (cleanup_local_steps q w) rfl σ U

/-- A proof-side execution world. The authentic source register and Return
flag belong to the operational semantics, not to the observer configuration. -/
structure World where
  config : State
  source : Source
  returned : Bool

/-- True is an independent writer update; false executes the pending observer
microstep. After the separate Return the execution world is absorbing. -/
def worldEvent (writer : Bool) (w : World) : World :=
  if w.returned then w else
  if writer then {w with source := substitution w.source} else
  match step w.config with
  | .ret => {w with returned := true}
  | .localStep c => {w with config := c}
  | .read p f => {w with config := f (readout p w.source)}

/-- Natural indices enumerate active events, excluding idle waiting. -/
def trajectory (schedule : Nat → Bool) (w : World) : Nat → World
  | 0 => w
  | n+1 => worldEvent (schedule n) (trajectory schedule w n)

/-- Every pending observer event eventually gets its turn. -/
def Progressing (schedule : Nat → Bool) (w : World) : Prop :=
  ∀ n : Nat, (trajectory schedule w n).returned = false →
    ∃ m : Nat, n ≤ m ∧ schedule m = false

theorem trajectory_add (schedule : Nat → Bool) (w : World) (m k : Nat) :
    trajectory schedule w (m+k) =
      trajectory (fun i => schedule (m+i)) (trajectory schedule w m) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change worldEvent (schedule (m+k)) (trajectory schedule w (m+k)) =
        worldEvent (schedule (m+k))
          (trajectory (fun i => schedule (m+i)) (trajectory schedule w m) k)
      rw [ih]

private theorem progressing_shift (schedule : Nat → Bool) (m : Nat) (w : World)
    (h : Progressing schedule w) :
    Progressing (fun i => schedule (m+i)) (trajectory schedule w m) := by
  intro n hn
  have pending : (trajectory schedule w (m+n)).returned = false := by
    simpa only [trajectory_add] using hn
  obtain ⟨k,hk,he⟩ := h (m+n) pending
  refine ⟨k-m,by omega,?_⟩
  have hm : m ≤ k := by omega
  simpa [Nat.add_sub_of_le hm] using he

private theorem writer_prefix (schedule : Nat → Bool) (n : Nat) (c : State) (U : Source)
    (h : ∀ i : Nat, i < n → schedule i = true) :
    ∃ V : Source, trajectory schedule ⟨c,U,false⟩ n = ⟨c,V,false⟩ := by
  induction n with
  | zero => exact ⟨U,rfl⟩
  | succ n ih =>
    obtain ⟨V,hv⟩ := ih (fun i hi => h i (by omega))
    refine ⟨substitution V,?_⟩
    simp only [trajectory,hv,h n (by omega),worldEvent,Bool.false_eq_true,↓reduceIte]

private theorem first_observer (schedule : Nat → Bool) (c : State) (U : Source)
    (h : Progressing schedule ⟨c,U,false⟩) :
    ∃ (n : Nat) (V : Source), trajectory schedule ⟨c,U,false⟩ (n+1) =
      worldEvent false ⟨c,V,false⟩ := by
  have hex : ∃ n : Nat, schedule n = false := by
    obtain ⟨n,_,hn⟩ := h 0 rfl
    exact ⟨n,hn⟩
  let n := Nat.find hex
  have hn : schedule n = false := Nat.find_spec hex
  have before : ∀ i : Nat, i < n → schedule i = true := by
    intro i hi
    cases he : schedule i with
    | false => exact False.elim ((Nat.not_le_of_lt hi) (Nat.find_min' hex he))
    | true => rfl
  obtain ⟨V,hv⟩ := writer_prefix schedule n c U before
  exact ⟨n,V,by simp only [trajectory,hv,hn]⟩

private theorem local_steps_progressing {n : Nat} {c d : State}
    (s : LocalSteps n c d) (ret : step d = .ret) (schedule : Nat → Bool)
    (U : Source) (h : Progressing schedule ⟨c,U,false⟩) :
    ∃ m : Nat, (trajectory schedule ⟨c,U,false⟩ m).returned = true ∧
      (trajectory schedule ⟨c,U,false⟩ m).config = d := by
  induction s generalizing schedule U with
  | refl c =>
    obtain ⟨m,V,hm⟩ := first_observer schedule c U h
    refine ⟨m+1,?_,?_⟩ <;> simp [hm,worldEvent,ret]
  | @cons n c d e hop rest ih =>
    obtain ⟨m,V,hm⟩ := first_observer schedule c U h
    have first : trajectory schedule ⟨c,U,false⟩ (m+1) = ⟨d,V,false⟩ := by
      simpa [worldEvent,hop] using hm
    obtain ⟨k,hk,he⟩ := ih ret (fun i => schedule (m+1+i)) V
      (by
        have shifted := progressing_shift schedule (m+1) ⟨c,U,false⟩ h
        simpa only [first] using shifted)
    refine ⟨m+1+k,?_⟩
    simpa [trajectory_add,first] using (And.intro hk he)

/-- Cleanup terminates on every progressing active schedule, even without a
finite-interference premise. The Return flag is set by its separate event. -/
theorem cleanup_progressing (q : Bool) (w : Work) (schedule : Nat → Bool)
    (U : Source) (h : Progressing schedule ⟨.active q (go 40 w),U,false⟩) :
    ∃ m : Nat,
      (trajectory schedule ⟨.active q (go 40 w),U,false⟩ m).returned = true ∧
      (trajectory schedule ⟨.active q (go 40 w),U,false⟩ m).config = .ready q w.row := by
  exact local_steps_progressing (cleanup_local_steps q w) rfl schedule U h

def rootCandidate (w : Work) : Work := put 25 5 (put 8 4 (put 7 3 (put 6 0 w)))

private theorem root_candidate_steps (w : Work) :
    LocalSteps 5 (.active true (go 3 w)) (.active true (rootCandidate w)) := by
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  exact LocalSteps.refl _

/-- The actual guard follows the left spine and ends with an authentic leaf
reply, retaining its materialized address for later validation. -/
theorem guard_search (U T : Source) (q : Bool) (p : Address)
    (observed : ∀ z : Address, readout (p ++ z) U = readout z T) :
    ∃ (g : Address) (ell : Reply), (ell = .alpha ∨ ell = .beta) ∧
      readout g U = ell ∧
      Continues U (.active q {emptyWork with guardPath := p})
        (.active q {emptyWork with pc := 3, guardPath := g, guardReply := ell}) := by
  induction T generalizing p with
  | of b =>
    let ell : Reply := if b then .alpha else .beta
    refine ⟨p,ell,by cases b <;> simp [ell],?_,?_⟩
    · cases b <;> simpa [ell,readout] using observed []
    · apply continues_read U _ _ p ell
      · refine ⟨_,rfl,?_⟩
        cases b <;> rfl
      · cases b <;> simpa [ell,readout] using observed []
  | mul l r ihl ihr =>
    obtain ⟨g,ell,he,hy,hc⟩ := ihl (p ++ [false])
      (by intro z; simpa [List.append_assoc,readout] using observed (false :: z))
    refine ⟨g,ell,he,hy,?_⟩
    apply continues_trans _ _ (.active q {emptyWork with pc := 2, guardPath := p})
    · apply continues_read U _ _ p .branch
      · exact ⟨_,rfl,rfl⟩
      · simpa [readout] using observed []
    exact continues_trans U _ _ _ (continues_local U _ _ rfl) hc

private theorem root_guard (U T : Source) (p : Address)
    (observed : ∀ z : Address, readout (p ++ z) U = readout z T) :
    ∃ (g : Address) (ell : Reply) (a : Word), .update ∉ a ∧
      (ell = .alpha ∨ ell = .beta) ∧ readout g U = ell ∧
      Run step (.active true {emptyWork with guardPath := p}) U
        (a ++ .observer (.read g ell) ::
          NativeIndependentExecution.expand (cleanupTiming (g.length+6) (fun _ => 0)))
        (.ready true rootBytes) := by
  obtain ⟨g,ell,he,hy,hs⟩ := guard_search U T true p observed
  let w : Work := {emptyWork with pc := 3, guardPath := g, guardReply := ell}
  let v := rootCandidate w
  have cleanup : Run step (.active true (go 40 v)) U
      (NativeIndependentExecution.expand (cleanupTiming (g.length+6) (fun _ => 0)))
      (.ready true rootBytes) := by
    simpa [v,w,rootCandidate,put,emptyWork,rootBytes] using
      cleanup_every_schedule true v (fun _ => 0) U
  have validated : Run step (.active true v) U
      (.observer (.read g ell) ::
        NativeIndependentExecution.expand (cleanupTiming (g.length+6) (fun _ => 0)))
      (.ready true rootBytes) := by
    apply Run.read (f := fun y => .active true (go (if y = ell then 40 else 50) v))
    · change Op.read g _ = Op.read g _
      congr 1
      funext y
      cases y <;> rfl
    · exact hy
    · simpa using cleanup
  have hc := continues_trans U _ _ _ hs (local_steps_continues (root_candidate_steps w) U)
  obtain ⟨a,ha,ra⟩ := hc _ _ validated
  exact ⟨g,ell,a,ha,he,hy,ra⟩

/-- Reaching any root-selected terminal configuration forces the invocation
source alpha. This quantifies every independent-writer returning history,
without a finite-interference assumption or a projected final state. -/
private theorem root_selected_origin (u : Source) (h : Word) (row : List Cell)
    (r : Run step .entry u h (.ready true row)) :
    u = .of true ∧ ∃ tail : Word, h = .observer (.read [] .alpha) :: tail := by
  generalize hc : State.entry = c at r
  generalize hb : State.ready true row = b at r
  induction r with
  | ret hop => rw [← hc] at hop; simp [step] at hop
  | localStep hop run ih => rw [← hc] at hop; simp [step] at hop
  | @read c U p f y h b hop hy run ih =>
    subst c
    have he : p = [] ∧ f = (fun y => .active (decide (y = .alpha)) emptyWork) :=
      Op.read.inj hop.symm
    obtain ⟨rfl,rfl⟩ := he
    have q := choice_preserved _ _ _ _ _ rfl run
    rw [← hb] at q
    have ha : y = .alpha := by simpa [selected,eq_comm] using q
    rw [ha] at hy
    refine ⟨?_,?_⟩
    · cases U with
      | of b => cases b <;> simp_all [readout]
      | mul l r => simp [readout] at hy
    · exact ⟨h,by rw [ha]⟩
  | @update c U h b run ih =>
    have ht := ih hc hb
    exact False.elim (SourceCoordinates.IntrinsicSubstitutionCoordinates.no_alpha U ht.1)

/-- A complete finite execution with j updates after the first root Read.
The final guard reply is authentic at the specified iterate, all other events
in the acquisition prefix are quiescent, and cleanup and Return are explicit. -/
def PostSelectionWitness (j : Nat) : Prop :=
  ∃ (g : Address) (ell : Reply) (a : Word), .update ∉ a ∧
    (ell = .alpha ∨ ell = .beta) ∧ readout g (substitution^[j] (.of true)) = ell ∧
    Run step .entry (.of true)
      (.observer (.read [] .alpha) :: (List.replicate j .update ++
        (a ++ .observer (.read g ell) ::
          NativeIndependentExecution.expand (cleanupTiming (g.length+6) (fun _ => 0)))))
      (.ready true rootBytes)

/-- The actual selected machine has exactly alpha as the source support of
its root boundary. Every post-selection update count has a quiescent root
acquisition witness with that same entire boundary. Beta instead has a
literal blocked two-address row, while the root row fits every source. -/
theorem selected_root_support :
    (∀ u : Source, (∃ h : Word, Run step .entry u h (.ready true rootBytes)) ↔
      u = .of true) ∧
    (∀ j : Nat, PostSelectionWitness j) ∧
    (∃ h : Word, .update ∉ h ∧
      Run step .entry (.of false) h (.ready false (leafBytes false)) ∧
      ActualCutPartitionDecoder.literalRecord (cut false) (.of false) =
        (.of (.inl false), ∅) ∧
      ∀ p ∈ cut false, [].IsPrefix p ∧ p ≠ [] ∧
        ActualLeafHistoryRigidity.subtree p (.of false) = none) ∧
    (∀ (h : Word) (row : List Cell),
      ¬ Run step .entry (.of false) h (.ready true row)) ∧
    (∀ (u : Source) (j : Nat),
      ActualCutPartitionDecoder.literalRecord {[]} (substitution^[j] u) =
        NativeFiveHoleFiber.rootLabel) ∧
    (∀ (u : Source) (h : Word) (row : List Cell),
      Run step .entry u h (.ready true row) →
        ∃ tail : Word, h = .observer (.read [] .alpha) :: tail) := by
  have witnesses (j : Nat) : PostSelectionWitness j := by
    let U := substitution^[j] (.of true)
    obtain ⟨g,ell,a,ha,he,hy,r⟩ := root_guard U U [] (by intro z; rfl)
    refine ⟨g,ell,a,ha,he,hy,?_⟩
    apply Run.read rfl rfl
    exact (NativeIndependentExecution.updates_iff step j _ _ _ _).mpr r
  refine ⟨?_,witnesses,?_,?_,fun u j => NativeFiveHoleFiber.root_record _,
    fun u h row r => (root_selected_origin u h row r).2⟩
  · intro u
    constructor
    · rintro ⟨h,r⟩
      exact (root_selected_origin u h rootBytes r).1
    · rintro rfl
      obtain ⟨g,ell,a,_,_,_,r⟩ := witnesses 0
      exact ⟨_,r⟩
  · let w : Work := {emptyWork with pc := 3, guardReply := .beta}
    have leafPhase : Continues (.of false) (.active false w)
        (.ready false (leafBytes false)) := by
      apply continues_trans _ _ (.active false (go 4 w))
      · apply continues_local; rfl
      apply continues_trans _ _ (.active false (go 10 w))
      · apply continues_read _ _ _ [] .beta
        · exact ⟨_,rfl,rfl⟩
        · rfl
      apply continues_trans _ _ (.active false (put 7 8 w))
      · apply continues_local; rfl
      apply continues_trans _ _ (.active false (put 8 4 (put 7 8 w)))
      · apply continues_local; rfl
      let v := put 25 5 (put 8 4 (put 7 8 w))
      apply continues_trans _ _ (.active false v)
      · apply continues_local; rfl
      apply continues_trans _ _ (.active false (go 40 v))
      · apply continues_read _ _ _ [] .beta
        · exact ⟨_,rfl,rfl⟩
        · rfl
      · simpa [v,w,emptyWork,put,leafBytes] using local_steps_continues (cleanup_local_steps false v) (.of false)
    have initial : Continues (.of false) .entry (.active false emptyWork) := by
      apply continues_read _ _ _ [] .beta
      · exact ⟨_,rfl,rfl⟩
      · rfl
    have guard : Continues (.of false) (.active false emptyWork) (.active false w) := by
      apply continues_read _ _ _ [] .beta
      · exact ⟨_,rfl,rfl⟩
      · rfl
    have whole := continues_trans _ _ _ _ initial (continues_trans _ _ _ _ guard leafPhase)
    obtain ⟨v,hv,rv⟩ := whole [.observer .ret] _ (Run.ret rfl)
    refine ⟨v ++ [.observer .ret],by simp [hv],rv,?_,?_⟩
    · simp [cut,ActualCutPartitionDecoder.literalRecord,
        ActualCutPartitionDecoder.cutExterior,ActualCutPartitionDecoder.actualPartition,
        ActualCutPartitionRecovery.orderedHoles,ActualCutPartitionRecovery.reachedHoles,
        ActualLeafHistoryRigidity.subtree]
    · intro p hp
      simp only [cut,Bool.false_eq_true,↓reduceIte,Finset.mem_insert,
        Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> simp [ActualLeafHistoryRigidity.subtree]
  · intro h row r
    have no := (root_selected_origin (.of false) h row r).1
    cases no


def pairStart (w : Work) (z : Address) : Work :=
  {w with pc := 20, operand := false :: z}

def pairDone (w : Work) (z : Address) (ell : Reply) : Work :=
  {w with pc := 27, operand := true :: z, leftReply := ell, rightReply := ell}

def rightLeafReply : Source → Reply
  | .of b => if b then .alpha else .beta
  | .mul _ r => rightLeafReply r

private theorem pair_reads (U : Source) (w : Work) (z : Address) (a b : Reply)
    (ha : readout (false :: z) U = a) (hb : readout (true :: z) U = b) :
    Continues U (.active false (pairStart w z))
      (.active false {w with pc := 23, operand := true :: z, leftReply := a, rightReply := b}) := by
  apply continues_trans _ _ (.active false {w with pc := 21, operand := false :: z, leftReply := a})
  · apply continues_read U _ _ (false :: z) a
    · refine ⟨_,rfl,?_⟩
      cases a <;> rfl
    · exact ha
  apply continues_trans _ _ (.active false {w with pc := 22, operand := true :: z, leftReply := a})
  · apply continues_local; rfl
  apply continues_read U _ _ (true :: z) b
  · refine ⟨_,rfl,?_⟩
    cases b <;> rfl
  · exact hb

theorem pair_equal_scan (U T : Source) (w : Work) (z : Address)
    (hl : ∀ a : Address, readout (false :: (z ++ a)) U = readout a T)
    (hr : ∀ a : Address, readout (true :: (z ++ a)) U = readout a T) :
    Continues U (.active false (pairStart w z))
      (.active false (pairDone w z (rightLeafReply T))) := by
  induction T generalizing w z with
  | of b =>
    let ell : Reply := if b then .alpha else .beta
    apply continues_trans _ _ (.active false {w with pc := 23, operand := true :: z, leftReply := ell, rightReply := ell})
    · apply pair_reads
      · cases b <;> simpa [ell,readout] using hl []
      · cases b <;> simpa [ell,readout] using hr []
    apply continues_local
    cases b <;> rfl
  | mul l r ihl ihr =>
    let w0 : Work := {w with leftReply := .branch, rightReply := .branch}
    apply continues_trans _ _ (.active false {w0 with pc := 23, operand := true :: z})
    · apply pair_reads
      · simpa [readout] using hl []
      · simpa [readout] using hr []
    apply continues_trans _ _ (.active false {w0 with pc := 24, operand := true :: z})
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false {w0 with pc := 26, operand := false :: z})
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false (pairStart w0 (z ++ [false])))
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false (pairDone w0 (z ++ [false]) (rightLeafReply l)))
    · apply ihl
      · intro a; simpa [List.append_assoc,readout] using hl (false :: a)
      · intro a; simpa [List.append_assoc,readout] using hr (false :: a)
    let w1 : Work := {w with leftReply := rightLeafReply l, rightReply := rightLeafReply l}
    apply continues_trans _ _ (.active false {w1 with pc := 28, operand := true :: z})
    · apply continues_local
      simp only [step,lift,privateStep,localInstruction,pairDone,w0,w1,lastBit,pop]
      simp [List.getLast?_cons, List.dropLast_cons_of_ne_nil]
    apply continues_trans _ _ (.active false {w1 with pc := 31, operand := true :: (z ++ [true])})
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false (pairStart w1 (z ++ [true])))
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false (pairDone w1 (z ++ [true]) (rightLeafReply r)))
    · apply ihr
      · intro a; simpa [List.append_assoc,readout] using hl (true :: a)
      · intro a; simpa [List.append_assoc,readout] using hr (true :: a)
    apply continues_local
    simp only [step,lift,privateStep,localInstruction,pairDone,w1,lastBit,pop,rightLeafReply]
    simp [List.getLast?_cons, List.dropLast_cons_of_ne_nil]

private theorem pair_mismatch (U : Source) (w : Work) (z : Address) (a b : Reply)
    (ha : readout (false :: z) U = a) (hb : readout (true :: z) U = b)
    (hne : a ≠ b) :
    Continues U (.active false (pairStart w z))
      (.active false {w with pc := 29, operand := true :: z, leftReply := a, rightReply := b}) := by
  apply continues_trans _ _ (.active false {w with pc := 23, operand := true :: z, leftReply := a, rightReply := b})
  · exact pair_reads U w z a b ha hb
  apply continues_local
  simp [step,lift,privateStep,localInstruction,go,hne]

theorem pair_unequal_scan (U A B : Source) (w : Work) (z : Address)
    (hl : ∀ a : Address, readout (false :: (z ++ a)) U = readout a A)
    (hr : ∀ a : Address, readout (true :: (z ++ a)) U = readout a B)
    (hne : A ≠ B) :
    ∃ v : Work, v.pc = 29 ∧ v.row = w.row ∧ v.guardPath = w.guardPath ∧
      v.guardReply = w.guardReply ∧
      Continues U (.active false (pairStart w z)) (.active false v) := by
  induction A generalizing B w z with
  | of a =>
    cases B with
    | of b =>
      refine ⟨{w with pc := 29, operand := true :: z, leftReply := if a then .alpha else .beta, rightReply := if b then .alpha else .beta},rfl,rfl,rfl,rfl,?_⟩
      apply pair_mismatch
      · cases a <;> simpa [readout] using hl []
      · cases b <;> simpa [readout] using hr []
      · cases a <;> cases b <;> simp_all
    | mul l r =>
      refine ⟨{w with pc := 29, operand := true :: z, leftReply := if a then .alpha else .beta, rightReply := .branch},rfl,rfl,rfl,rfl,?_⟩
      apply pair_mismatch
      · cases a <;> simpa [readout] using hl []
      · simpa [readout] using hr []
      · cases a <;> decide
  | mul l r ihl ihr =>
    cases B with
    | of b =>
      refine ⟨{w with pc := 29, operand := true :: z, leftReply := .branch, rightReply := if b then .alpha else .beta},rfl,rfl,rfl,rfl,?_⟩
      apply pair_mismatch
      · simpa [readout] using hl []
      · cases b <;> simpa [readout] using hr []
      · cases b <;> decide
    | mul l' r' =>
      let w0 : Work := {w with leftReply := .branch, rightReply := .branch}
      have beginLeft : Continues U (.active false (pairStart w z))
          (.active false (pairStart w0 (z ++ [false]))) := by
        apply continues_trans _ _ (.active false {w0 with pc := 23, operand := true :: z})
        · apply pair_reads
          · simpa [readout] using hl []
          · simpa [readout] using hr []
        apply continues_trans _ _ (.active false {w0 with pc := 24, operand := true :: z})
        · apply continues_local; rfl
        apply continues_trans _ _ (.active false {w0 with pc := 26, operand := false :: z})
        · apply continues_local; rfl
        apply continues_local; rfl
      by_cases sameLeft : l = l'
      · subst l'
        have scanLeft := pair_equal_scan U l w0 (z ++ [false])
          (by intro a; simpa [List.append_assoc,readout] using hl (false :: a))
          (by intro a; simpa [List.append_assoc,readout] using hr (false :: a))
        let w1 : Work := {w with leftReply := rightLeafReply l, rightReply := rightLeafReply l}
        have advance : Continues U (.active false (pairDone w0 (z ++ [false]) (rightLeafReply l)))
            (.active false (pairStart w1 (z ++ [true]))) := by
          apply continues_trans _ _ (.active false {w1 with pc := 28, operand := true :: z})
          · apply continues_local
            simp [step,lift,privateStep,localInstruction,pairDone,w0,w1,lastBit,pop,
              List.getLast?_cons,List.dropLast_cons_of_ne_nil]
          apply continues_trans _ _ (.active false {w1 with pc := 31, operand := true :: (z ++ [true])})
          · apply continues_local; rfl
          apply continues_local; rfl
        have differentRight : r ≠ r' := by intro e; exact hne (by rw [e])
        obtain ⟨v,hpc,hrow,hpath,hreply,scanRight⟩ := ihr r' w1 (z ++ [true])
          (by intro a; simpa [List.append_assoc,readout] using hl (true :: a))
          (by intro a; simpa [List.append_assoc,readout] using hr (true :: a)) differentRight
        refine ⟨v,hpc,hrow,hpath,hreply,?_⟩
        exact continues_trans U _ _ _ beginLeft
          (continues_trans U _ _ _ scanLeft (continues_trans U _ _ _ advance scanRight))
      · obtain ⟨v,hpc,hrow,hpath,hreply,scanLeft⟩ := ihl l' w0 (z ++ [false])
          (by intro a; simpa [List.append_assoc,readout] using hl (false :: a))
          (by intro a; simpa [List.append_assoc,readout] using hr (false :: a)) sameLeft
        exact ⟨v,hpc,hrow,hpath,hreply,continues_trans U _ _ _ beginLeft scanLeft⟩

private def forkCandidate (w : Work) : Work :=
  let v := put 19 forkPrefix[7] (put 18 forkPrefix[6] (put 17 forkPrefix[5]
    (put 16 forkPrefix[4] (put 15 forkPrefix[3] (put 14 forkPrefix[2]
      (put 13 forkPrefix[1] (put 12 forkPrefix[0] w)))))))
  {v with pc := 20, operand := [false]}

private theorem fork_candidate_steps (w : Work) :
    LocalSteps 9 (.active false (go 11 w)) (.active false (forkCandidate w)) := by
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  apply LocalSteps.cons rfl
  exact LocalSteps.refl _

theorem pair_complete (U A B : Source) (w : Work)
    (hl : ∀ a : Address, readout (false :: a) U = readout a A)
    (hr : ∀ a : Address, readout (true :: a) U = readout a B) :
    ∃ v : Work, v.pc = 8 ∧ v.row = w.row ++ [if A = B then 10 else 9] ∧
      v.guardPath = w.guardPath ∧ v.guardReply = w.guardReply ∧
      Continues U (.active false (pairStart w [])) (.active false v) := by
  by_cases same : A = B
  · subst B
    let d := pairDone w [] (rightLeafReply A)
    refine ⟨put 8 10 d,rfl,by simp [put,d,pairDone],rfl,rfl,?_⟩
    apply continues_trans _ _ (.active false d)
    · exact pair_equal_scan U A w [] (by simpa using hl) (by simpa using hr)
    apply continues_local; rfl
  · obtain ⟨v,hpc,hrow,hpath,hreply,hscan⟩ := pair_unequal_scan U A B w []
      (by simpa using hl) (by simpa using hr) same
    refine ⟨put 8 9 v,rfl,by simpa [put,same] using hrow,hpath,hreply,?_⟩
    apply continues_trans U _ (.active false v) _ hscan
    apply continues_local
    simp [step,lift,privateStep,localInstruction,hpc,put]

/-- The two addressed holes and their complete partition. Both diagonal
pairs are retained, and the bit supplies both off-diagonal memberships. -/
def forkRecord (bit : Bool) :
    ActualCutPartitionDecoder.HoleExterior × Finset (Address × Address) :=
  (.mul (.of (.inr [false])) (.of (.inr [true])),
    ((cut false).product (cut false)).filter (fun pq => pq.1 = pq.2 ∨ bit = true))

/-- Every finite pair of hidden subtrees is actually compared during an
entire quiescent invocation, including both signs of its partition bit. -/
theorem quiescent_two_hole (A B : Source) :
    ∃ h : Word, .update ∉ h ∧
      Run step .entry (.mul A B) h
        (.ready false (forkPrefix ++ [if A = B then 10 else 9,5])) ∧
      ActualCutPartitionDecoder.literalRecord (cut false) (.mul A B) =
        forkRecord (decide (A = B)) := by
  let U : Source := .mul A B
  obtain ⟨g,ell,he,hy,hg⟩ := guard_search U U false [] (by intro z; rfl)
  let w : Work := {emptyWork with pc := 3, guardPath := g, guardReply := ell}
  let v := forkCandidate w
  obtain ⟨d,hpc,hrow,hpath,hreply,hscan⟩ := pair_complete U A B v
    (by intro a; rfl) (by intro a; rfl)
  have suffix : Continues U (.active false (go 3 w))
      (.ready false (forkPrefix ++ [if A = B then 10 else 9,5])) := by
    apply continues_trans _ _ (.active false (go 4 w))
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false (go 11 w))
    · apply continues_read U _ _ [] .branch
      · exact ⟨_,rfl,rfl⟩
      · rfl
    apply continues_trans _ _ (.active false v)
    · exact local_steps_continues (fork_candidate_steps w) U
    apply continues_trans _ _ (.active false d)
    · simpa [pairStart,v,forkCandidate] using hscan
    have dp : d.guardPath = g := by simpa [v,forkCandidate,w,put] using hpath
    have dr : d.guardReply = ell := by simpa [v,forkCandidate,w,put] using hreply
    have db : d.row = forkPrefix ++ [if A = B then 10 else 9] := by
      simpa [v,forkCandidate,w,emptyWork,put,forkPrefix,List.append_assoc] using hrow
    rcases d with ⟨pc,path,operand,row,reply,left,right⟩
    dsimp only at hpc dp dr db
    subst pc path reply row
    let d : Work := ⟨8,g,operand,forkPrefix ++ [if A = B then 10 else 9],ell,left,right⟩
    let f := put 25 5 d
    apply continues_trans _ _ (.active false f)
    · apply continues_local; rfl
    apply continues_trans _ _ (.active false (go 40 f))
    · apply continues_read U _ _ g ell
      · refine ⟨_,rfl,?_⟩
        cases ell <;> simp [f,d,put,go,follow]
      · exact hy
    · have hc := local_steps_continues (cleanup_local_steps false f) U
      simpa [f,d,put,List.append_assoc] using hc
  have initial : Continues U .entry (.active false emptyWork) := by
    apply continues_read U _ _ [] .branch
    · exact ⟨_,rfl,rfl⟩
    · rfl
  have whole := continues_trans U _ _ _ initial (continues_trans U _ _ _ hg suffix)
  obtain ⟨a,ha,ra⟩ := whole [.observer .ret] _ (Run.ret rfl)
  refine ⟨a ++ [.observer .ret],by simp [ha],ra,?_⟩
  apply Prod.ext
  · change ActualCutPartitionDecoder.cutExterior (cut false) [] (.mul A B) = _
    cases A <;> cases B <;> simp [ActualCutPartitionDecoder.cutExterior,cut,forkRecord]
  · have holes : (ActualCutPartitionRecovery.orderedHoles (cut false) (.mul A B)).toFinset =
        cut false := by
      cases A <;> cases B <;>
        simp [ActualCutPartitionRecovery.orderedHoles,ActualCutPartitionRecovery.reachedHoles,cut]
    change (ActualCutPartitionDecoder.actualPartition (cut false) (.mul A B)) = _
    rw [ActualCutPartitionDecoder.actualPartition,holes]
    apply Finset.filter_congr
    intro pq hp
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hp
    rcases pq with ⟨p,q⟩
    simp only [cut,Bool.false_eq_true,↓reduceIte,Finset.mem_insert,Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
      simp [ActualLeafHistoryRigidity.subtree,eq_comm]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
