/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Authentic guard epochs and complete selected rows at successful validation. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeIndependentExecution (Op Run Word)
open NativeSelectedRA
open NativeSelectedRAProgress

/-- The complete byte rows for the two fixed selected cuts. -/
def recordBytes (q : Bool) (U : Source) : List Cell :=
  if q then rootBytes else match U with
  | .of b => leafBytes b
  | .mul A B => forkPrefix ++ [if A = B then 10 else 9,5]

/-- The fixed byte decoder retains the literal exterior and full hole partition. -/
def decodeRow (q : Bool) (row : List Cell) :
    Option (ActualCutPartitionDecoder.HoleExterior × Finset (Address × Address)) :=
  if q then if row = rootBytes then some NativeFiveHoleFiber.rootLabel else none
  else if row = leafBytes true then some (.of (.inl true),∅)
  else if row = leafBytes false then some (.of (.inl false),∅)
  else if row = forkPrefix ++ [10,5] then some (forkRecord true)
  else if row = forkPrefix ++ [9,5] then some (forkRecord false) else none

private theorem bytes_meaning (q : Bool) (U : Source) :
    decodeRow q (recordBytes q U) = some (ActualCutPartitionDecoder.literalRecord (cut q) U) := by
  cases q with
  | true =>
    have root := selected_root_support.2.2.2.2.1 U 0
    simpa [recordBytes,decodeRow,cut] using congrArg some root.symm
  | false =>
    cases U with
    | of b =>
      cases b <;> simp [recordBytes,decodeRow,leafBytes,forkPrefix,cut,
        ActualCutPartitionDecoder.literalRecord,ActualCutPartitionDecoder.cutExterior,
        ActualCutPartitionDecoder.actualPartition,ActualCutPartitionRecovery.orderedHoles,
        ActualCutPartitionRecovery.reachedHoles]
    | mul A B =>
      obtain ⟨_,_,_,meaning⟩ := quiescent_two_hole A B
      rw [meaning]
      by_cases equal : A = B <;>
        simp [recordBytes,decodeRow,equal,leafBytes,forkPrefix]

private theorem guard_epoch (V : Source) (p : Address) (ell : Reply) (k : Nat)
    (leaf : ell = .alpha ∨ ell = .beta) (old : readout p V = ell)
    (now : readout p (substitution^[k] V) = ell) : k = 0 := by
  let depth := SourceCoordinates.IntrinsicSubstitutionCoordinates.depth
  have increment (T : Source) : depth (substitution T) = depth T + 1 :=
    congrArg Prod.fst (SourceCoordinates.IntrinsicSubstitutionCoordinates.all_source_coordinate_law.2.1 T)
  have iterated (T : Source) (j : Nat) : depth (substitution^[j] T) = depth T + j := by
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply',increment,ih]; omega
  have leafNode := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases leaf with he | he
  all_goals
    have before := leafNode V p (decide (ell = .alpha)) (by simpa [he] using old)
    have after := leafNode (substitution^[k] V) p (decide (ell = .alpha)) (by simpa [he] using now)
    have transported := NativeDepthPatterns.original_present_transport k p V _ before
    have eq := Option.some.inj (transported.symm.trans after)
    have count := congrArg depth eq
    rw [iterated] at count
    omega

/-- A pending candidate remembers its authentic guard source only in the proof.
If no update has occurred since that guard, its actual body has a stationary
prefix from the fresh guard exit. Positive epochs do not assert row accuracy. -/
def Candidate (U : Source) (q : Bool) (w : Work) : Prop :=
  ∃ (V : Source) (k : Nat), U = substitution^[k] V ∧
    (w.guardReply = .alpha ∨ w.guardReply = .beta) ∧
    readout w.guardPath V = w.guardReply ∧
    (k = 0 → Continues V
      (.active q {emptyWork with pc := 3,guardPath := w.guardPath,guardReply := w.guardReply})
      (.active q w))

private theorem candidate_writer (U : Source) (q : Bool) (w : Work)
    (h : Candidate U q w) : Candidate (substitution U) q w := by
  obtain ⟨V,k,rfl,leaf,auth,lead⟩ := h
  refine ⟨V,k+1,by rw [Function.iterate_succ_apply'],leaf,auth,?_⟩
  intro impossible
  omega

private theorem candidate_local (U : Source) (q : Bool) (w v : Work)
    (h : Candidate U q w) (hg : v.guardPath = w.guardPath)
    (hr : v.guardReply = w.guardReply) (hop : step (.active q w) = .localStep (.active q v)) :
    Candidate U q v := by
  obtain ⟨V,k,source,leaf,auth,lead⟩ := h
  refine ⟨V,k,source,by simpa [hr] using leaf,by simpa [hg,hr] using auth,?_⟩
  intro zero
  subst k
  simp only [Function.iterate_zero_apply] at source
  subst U
  intro t b run
  obtain ⟨s,hs,rs⟩ := lead rfl (.observer .localStep :: t) b (Run.localStep hop run)
  refine ⟨s ++ [.observer .localStep],by simp [hs],?_⟩
  simpa [hg,hr,List.append_assoc] using rs

private theorem candidate_read (U : Source) (q : Bool) (w : Work) (p : Address)
    (f : Reply → Work) (h : Candidate U q w)
    (hg : ∀ y, (f y).guardPath = w.guardPath)
    (hr : ∀ y, (f y).guardReply = w.guardReply)
    (hop : step (.active q w) = .read p (fun y => .active q (f y))) :
    Candidate U q (f (readout p U)) := by
  obtain ⟨V,k,source,leaf,auth,lead⟩ := h
  refine ⟨V,k,source,by simpa [hr] using leaf,by simpa [hg,hr] using auth,?_⟩
  intro zero
  subst k
  simp only [Function.iterate_zero_apply] at source
  subst U
  intro t b run
  obtain ⟨s,hs,rs⟩ := lead rfl
    (.observer (.read p (readout p V)) :: t) b (Run.read hop rfl run)
  refine ⟨s ++ [.observer (.read p (readout p V))],by simp [hs],?_⟩
  simpa [hg,hr,List.append_assoc] using rs

private theorem candidate_guard (U : Source) (q : Bool) (w : Work) (ell : Reply)
    (fresh : GuardFresh w) (leaf : ell = .alpha ∨ ell = .beta)
    (auth : readout w.guardPath U = ell) :
    Candidate U q {w with pc := 3,guardReply := ell} := by
  refine ⟨U,0,rfl,leaf,auth,?_⟩
  intro _ h b run
  have shape : {w with pc := 3,guardReply := ell} =
      {emptyWork with pc := 3,guardPath := w.guardPath,guardReply := ell} := by
    rcases w with ⟨pc,g,o,r,a,b,c⟩
    simp_all [GuardFresh,emptyWork]
  exact ⟨[],by simp,by simpa only [List.nil_append,shape] using run⟩

private theorem validation_run (U : Source) (q : Bool) (w : Work)
    (valid : readout w.guardPath U = w.guardReply) :
    ∃ h : Word, .update ∉ h ∧ Run step (.active q (go 25 w)) U h (.ready q w.row) := by
  have none (n : Nat) : .update ∉ NativeIndependentExecution.expand
      (cleanupTiming n (fun _ => 0)) := by
    induction n with
    | zero => simp [cleanupTiming,NativeIndependentExecution.expand]
    | succ n ih => simpa [cleanupTiming,NativeIndependentExecution.expand] using ih
  let tail := NativeIndependentExecution.expand
    (cleanupTiming (w.operand.length+w.guardPath.length+6) (fun _ => 0))
  refine ⟨.observer (.read w.guardPath w.guardReply) :: tail,by simp [tail,none],?_⟩
  apply Run.read (f := fun y => .active q (go (if y = w.guardReply then 40 else 50) w))
  · simp [step,lift,privateStep,receipt,follow,go]
    funext y
    cases y <;> rfl
  · exact valid
  simpa using cleanup_every_schedule q w (fun _ => 0) U

private theorem canonical_body_run (U : Source) (q : Bool) (w : Work)
    (valid : readout w.guardPath U = w.guardReply) :
    ∃ h : Word, .update ∉ h ∧
      Run step (.active q (go 3 w)) U h (.ready q (w.row ++ recordBytes q U)) := by
  cases q with
  | true =>
    obtain ⟨h,hh,run⟩ := validation_run U true (rootCandidate w) valid
    refine ⟨.observer .localStep :: .observer .localStep :: .observer .localStep ::
      .observer .localStep :: .observer .localStep :: h,by simp [hh],?_⟩
    apply Run.localStep (δ := step) rfl
    apply Run.localStep (δ := step) rfl
    apply Run.localStep (δ := step) rfl
    apply Run.localStep (δ := step) rfl
    apply Run.localStep (δ := step) rfl
    simpa [rootCandidate,put,go,recordBytes,rootBytes,List.append_assoc] using run
  | false =>
    have body : ∃ h : Word, .update ∉ h ∧
        Run step (.active false (go 4 w)) U h (.ready false (w.row ++ recordBytes false U)) := by
      cases U with
      | of b =>
        let v := put 25 5 (put 8 4 (put 7 (if b then 7 else 8) w))
        obtain ⟨h,hh,run⟩ := validation_run (.of b) false v valid
        refine ⟨.observer (.read [] (readout [] (.of b))) :: .observer .localStep ::
          .observer .localStep :: .observer .localStep :: h,by simp [hh],?_⟩
        apply Run.read (f := fun y => .active false {go 4 w with pc :=
          if y = .alpha then 9 else if y = .beta then 10 else if y = .branch then 11 else 99})
        · simp [step,lift,privateStep,receipt,follow,go]
          funext y
          cases y <;> rfl
        · rfl
        cases b <;> simp only [readout,↓reduceIte,Bool.false_eq_true] <;> apply Run.localStep (δ := step) rfl <;> apply Run.localStep (δ := step) rfl <;> apply Run.localStep (δ := step) rfl
        all_goals simpa [v,put,go,recordBytes,leafBytes,List.append_assoc] using run
      | mul A B =>
        let v : Work := {w with pc := 20,operand := [false],row := w.row ++ forkPrefix}
        obtain ⟨d,hpc,hrow,hg,hr,lead⟩ := pair_complete (.mul A B) A B v
          (fun _ => rfl) (fun _ => rfl)
        have accepted := validation_run (.mul A B) false (put 25 5 d)
          (by simpa [put,hg,hr,v] using valid)
        obtain ⟨h,hh,run⟩ := accepted
        have next : Run step (.active false d) (.mul A B)
            (.observer .localStep :: h) (.ready false (w.row ++ recordBytes false (.mul A B))) := by
          apply Run.localStep (d := .active false (put 25 5 d))
          · simp [step,lift,privateStep,localInstruction,hpc,put]
          simpa [put,go,hrow,v,recordBytes,List.append_assoc] using run
        obtain ⟨s,hs,rs⟩ := lead _ _ next
        refine ⟨.observer (.read [] .branch) :: List.replicate 9 (.observer .localStep) ++
          s ++ .observer .localStep :: h,by simp [hs,hh],?_⟩
        apply Run.read (f := fun y => .active false {go 4 w with pc :=
          if y = .alpha then 9 else if y = .beta then 10 else if y = .branch then 11 else 99})
        · simp [step,lift,privateStep,receipt,follow,go]
          funext y
          cases y <;> rfl
        · rfl
        change Run step (.active false (go 11 w)) (.mul A B)
          (List.replicate 9 (.observer .localStep) ++ s ++ .observer .localStep :: h) _
        repeat' apply Run.localStep (δ := step) rfl
        simpa [v,pairStart,put,go,forkPrefix,List.append_assoc] using rs
    obtain ⟨h,hh,run⟩ := body
    exact ⟨.observer .localStep :: h,by simp [hh],Run.localStep (δ := step) rfl run⟩


private theorem stationary_unique {U : Source} {c b d : State} {h t : Word}
    (r : Run step c U h b) (s : Run step c U t d)
    (rh : .update ∉ h) (sh : .update ∉ t) : b = d := by
  induction r generalizing d t with
  | ret hop =>
    cases s with
    | ret _ => rfl
    | localStep he _ => simp [hop] at he
    | read he _ _ => simp [hop] at he
    | update _ => simp at sh
  | @localStep c e U h b hop run ih =>
    cases s with
    | ret he => simp [hop] at he
    | @localStep _ e' _ t _ he rest =>
      have same := Op.localStep.inj (hop.symm.trans he)
      subst e'
      exact ih rest (by simpa using rh) (by simpa using sh)
    | read he _ _ => simp [hop] at he
    | update _ => simp at sh
  | @read c U p f y h b hop hy run ih =>
    cases s with
    | ret he => simp [hop] at he
    | localStep he _ => simp [hop] at he
    | @read _ _ p' f' y' t _ he hy' rest =>
      obtain ⟨rfl,rfl⟩ := Op.read.inj (hop.symm.trans he)
      have same : y' = y := hy'.symm.trans hy
      subst y'
      exact ih (by simpa only [hy] using rest) (by simpa using rh) (by simpa using sh)
    | update _ => simp at sh
  | update _ _ => simp at rh

private theorem candidate_accepted (U : Source) (q : Bool) (w : Work)
    (h : Candidate U q w) (hp : w.pc = 25)
    (valid : readout w.guardPath U = w.guardReply) : w.row = recordBytes q U := by
  obtain ⟨V,k,source,leaf,auth,lead⟩ := h
  have zero : k = 0 := guard_epoch V w.guardPath w.guardReply k leaf auth (by simpa [source] using valid)
  subst k
  simp only [Function.iterate_zero_apply] at source
  subst U
  let seed : Work := {emptyWork with pc := 3,guardPath := w.guardPath,guardReply := w.guardReply}
  obtain ⟨t,ht,rt⟩ := validation_run V q w valid
  have shape : go 25 w = w := by cases w; simp_all [go]
  rw [shape] at rt
  obtain ⟨s,hs,rs⟩ := lead rfl t _ rt
  obtain ⟨v,hv,rv⟩ := canonical_body_run V q seed auth
  have eq := stationary_unique rs rv (by simp [hs,ht]) hv
  have row := State.ready.inj eq
  simpa [seed,emptyWork,go] using row.2

/-- The actual validation event and its complete retained row. -/
def Captured (u : Source) (σ : Nat → Bool) (n : Nat) (q : Bool) (row : List Cell) : Prop :=
  ∃ (v : Nat) (w : Work), v < n ∧ σ v = false ∧
    (trajectory σ ⟨.entry,u,false⟩ v).returned = false ∧
    (trajectory σ ⟨.entry,u,false⟩ v).config = .active q w ∧
    w.pc = 25 ∧ w.row = row ∧
    readout w.guardPath (trajectory σ ⟨.entry,u,false⟩ v).source = w.guardReply ∧
    row = recordBytes q (trajectory σ ⟨.entry,u,false⟩ v).source ∧
    decodeRow q row = some (ActualCutPartitionDecoder.literalRecord (cut q)
      (trajectory σ ⟨.entry,u,false⟩ v).source) ∧
    ∀ k : Nat, v < k → k < n → σ k = false →
      (∃ d : State, step (trajectory σ ⟨.entry,u,false⟩ k).config = .localStep d) ∨
      step (trajectory σ ⟨.entry,u,false⟩ k).config = .ret

/-- Body phases retain an authentic guard; cleanup and ready retain only the
certificate of their actual successful validation. Reset clears the candidate. -/
def Certified (u : Source) (σ : Nat → Bool) (n : Nat) : State → Prop
  | .entry => True
  | .ready q row => Captured u σ n q row
  | .active q w => match w.pc.val with
    | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 |
      20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 31 =>
        Candidate (trajectory σ ⟨.entry,u,false⟩ n).source q w
    | 40 | 41 | 42 | 43 | 44 | 45 => Captured u σ n q w.row
    | _ => True

private theorem captured_succ (u : Source) (σ : Nat → Bool) (n : Nat) (q : Bool)
    (row : List Cell) (h : Captured u σ n q row)
    (event : σ n = false →
      (∃ d : State, step (trajectory σ ⟨.entry,u,false⟩ n).config = .localStep d) ∨
      step (trajectory σ ⟨.entry,u,false⟩ n).config = .ret) :
    Captured u σ (n+1) q row := by
  obtain ⟨v,w,hv,hw,hr,hc,hp,hrow,hguard,bytes,meaning,tail⟩ := h
  refine ⟨v,w,by omega,hw,hr,hc,hp,hrow,hguard,bytes,meaning,?_⟩
  intro k low high observer
  by_cases earlier : k < n
  · exact tail k low earlier observer
  · have same : k = n := by omega
    subst k
    exact event observer


private theorem cleanup_event (q : Bool) (w : Work)
    (phase : w.pc.val ∈ [40,41,42,43,44,45]) :
    ∃ d : State, step (.active q w) = .localStep d := by
  rcases w with ⟨⟨pc,hpc⟩,g,o,r,a,b,c⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at phase
  rcases phase with rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases h : o = [] <;> simp [step,lift,privateStep,localInstruction,h]
  · by_cases h : g = [] <;> simp [step,lift,privateStep,localInstruction,h]
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · by_cases h : g = [] ∧ o = [] ∧ a = .absent ∧ b = .absent ∧ c = .absent
    all_goals simp [step,lift,privateStep,localInstruction,h]

private theorem accepted_capture (u : Source) (σ : Nat → Bool) (n : Nat)
    (q : Bool) (w : Work) (U : Source)
    (current : trajectory σ ⟨.entry,u,false⟩ n = ⟨.active q w,U,false⟩)
    (observer : σ n = false) (candidate : Candidate U q w) (hp : w.pc = 25)
    (valid : readout w.guardPath U = w.guardReply) : Captured u σ (n+1) q w.row := by
  refine ⟨n,w,by omega,observer,by simp [current],by simp [current],hp,rfl,?_,?_,?_,?_⟩
  · simpa [current] using valid
  · simpa [current] using candidate_accepted U q w candidate hp valid
  · have row := candidate_accepted U q w candidate hp valid
    simpa [current,row] using bytes_meaning q U
  · intro k low high _
    omega

set_option maxHeartbeats 2000000 in
-- Each control is checked against the actual source-independent instruction.
private theorem certified_observer (u : Source) (σ : Nat → Bool) (n : Nat)
    (q : Bool) (w : Work) (U : Source)
    (current : trajectory σ ⟨.entry,u,false⟩ n = ⟨.active q w,U,false⟩)
    (observer : σ n = false) (h : Certified u σ n (.active q w)) :
    Certified u σ (n+1) (worldEvent false ⟨.active q w,U,false⟩).config := by
  have source : (trajectory σ ⟨.entry,u,false⟩ (n+1)).source = U := by
    cases hop : step (.active q w) <;> simp [trajectory,current,observer,worldEvent,hop]
  have fresh (hp : w.pc = 1) : GuardFresh w := by
    have safe := (reachable_scan_frontier u σ n).1
    rw [current] at safe
    change Frontier U q w at safe
    have shape : GuardFresh w ∧ readout w.guardPath U ≠ .absent := by
      simpa [Frontier,hp] using safe
    exact shape.1
  have clean : w.pc.val ∈ [40,41,42,43,44,45] →
      Captured u σ n q w.row → Captured u σ (n+1) q w.row := by
    intro phase cap
    apply captured_succ u σ n q w.row cap
    intro _
    exact Or.inl (by simpa [current] using cleanup_event q w phase)
  rcases w with ⟨pc,g,o,r,a,b,c⟩
  fin_cases pc <;> simp only [Certified,current] at h
  all_goals simp only [worldEvent,Bool.false_eq_true,↓reduceIte,step,lift,privateStep,
    localInstruction,receipt,follow,go,put,switch]
  all_goals simp only [Certified,source,current]
  all_goals first
    | trivial
    | exact candidate_local U q _ _ h rfl rfl rfl
    | skip
  case «1» =>
    have hf := fresh rfl
    cases reply : readout g U <;> simp [Certified,source]
    · exact candidate_guard U q _ .alpha hf (Or.inl rfl) reply
    · exact candidate_guard U q _ .beta hf (Or.inr rfl) reply
  case «3» =>
    cases q <;> simp only [Bool.false_eq_true,↓reduceIte,Certified,source]
    all_goals exact candidate_local U _ _ _ h rfl rfl rfl
  case «4» =>
    have move := candidate_read U q ⟨4,g,o,r,a,b,c⟩ [] (fun y => {(⟨4,g,o,r,a,b,c⟩ : Work) with pc :=
      if y = .alpha then 9 else if y = .beta then 10 else if y = .branch then 11 else 99}) h
      (fun _ => rfl) (fun _ => rfl) (by
        simp [step,lift,privateStep,receipt,follow]
        funext y
        cases y <;> rfl)
    cases reply : readout [] U <;> simp [Certified,source]
    all_goals first | trivial | simpa [reply] using move
  case «20» =>
    have move := candidate_read U q ⟨20,g,o,r,a,b,c⟩ o (fun y => ⟨21,g,o,r,a,y,c⟩) h
      (fun _ => rfl) (fun _ => rfl) (by
        simp [step,lift,privateStep,receipt,follow]; funext y; cases y <;> rfl)
    cases reply : readout o U <;> simpa [Certified,source,reply] using move
  case «22» =>
    have move := candidate_read U q ⟨22,g,o,r,a,b,c⟩ o (fun y => ⟨23,g,o,r,a,b,y⟩) h
      (fun _ => rfl) (fun _ => rfl) (by
        simp [step,lift,privateStep,receipt,follow]; funext y; cases y <;> rfl)
    cases reply : readout o U <;> simpa [Certified,source,reply] using move
  case «23» =>
    cases b <;> cases c <;> simp [Certified,source]
    all_goals first
      | trivial
      | exact candidate_local U q _ _ h rfl rfl rfl
  case «25» =>
    have accepted (valid : readout g U = a) :=
      accepted_capture u σ n q ⟨25,g,o,r,a,b,c⟩ U current observer h rfl valid
    cases a <;> cases reply : readout g U <;> simp [Certified,source]
    all_goals exact accepted reply
  case «27» =>
    by_cases root : o.tail = []
    · simp [root,Certified,source]
      exact candidate_local U q _ _ h rfl rfl (by simp [step,lift,privateStep,localInstruction,root,put])
    · cases last : lastBit o <;> simp [root,last,Certified,source]
      all_goals exact (candidate_local U q _ _ h rfl rfl
        (by simp [step,lift,privateStep,localInstruction,root,last,pop]))
  case «40» =>
    by_cases empty : o = [] <;> simp [empty,Certified]
    all_goals exact clean (by simp) h
  case «41» =>
    by_cases empty : g = [] <;> simp [empty,Certified]
    all_goals exact clean (by simp) h
  case «42» => exact clean (by simp) h
  case «43» => exact clean (by simp) h
  case «44» => exact clean (by simp) h
  case «45» =>
    by_cases empty : g = [] ∧ o = [] ∧ a = .absent ∧ b = .absent ∧ c = .absent
    · simp [empty,Certified]
      exact clean (by simp) h
    · simp [empty,Certified]

  case «50» => by_cases empty : r = [] <;> simp [empty,Certified]
  case «51» => by_cases empty : o = [] <;> simp [empty,Certified]
  case «52» => by_cases empty : g = [] <;> simp [empty,Certified]


set_option maxHeartbeats 2000000 in
-- Unchanged control permits only source transport or certificate extension.
private theorem certified_stay (u : Source) (σ : Nat → Bool) (n : Nat) (c : State)
    (h : Certified u σ n c)
    (config : (trajectory σ ⟨.entry,u,false⟩ n).config = c)
    (source : (trajectory σ ⟨.entry,u,false⟩ (n+1)).source =
        (trajectory σ ⟨.entry,u,false⟩ n).source ∨
      (trajectory σ ⟨.entry,u,false⟩ (n+1)).source =
        substitution (trajectory σ ⟨.entry,u,false⟩ n).source) :
    Certified u σ (n+1) c := by
  have clean (q : Bool) (w : Work)
      (config : (trajectory σ ⟨.entry,u,false⟩ n).config = .active q w)
      (phase : w.pc.val ∈ [40,41,42,43,44,45])
      (cap : Captured u σ n q w.row) : Captured u σ (n+1) q w.row := by
    apply captured_succ u σ n q w.row cap
    intro _
    exact Or.inl (by simpa [config] using cleanup_event q w phase)
  cases c with
  | entry => trivial
  | ready q row =>
    apply captured_succ u σ n q row h
    intro _
    exact Or.inr (by simp [config,step])
  | active q w =>
    rcases w with ⟨pc,g,o,r,a,b,c⟩
    fin_cases pc <;> simp only [Certified] at h ⊢
    all_goals first
      | trivial
      | (rcases source with same | updated
         · simpa only [same] using h
         · simpa only [updated] using candidate_writer _ q _ h)
      | exact clean q _ config (by simp) h

private theorem trajectory_certified (u : Source) (σ : Nat → Bool) (n : Nat) :
    Certified u σ n (trajectory σ ⟨.entry,u,false⟩ n).config := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases current : trajectory σ ⟨.entry,u,false⟩ n with
    | mk c U returned =>
      have before : Certified u σ n c := by simpa only [current] using ih
      cases returned with
      | true =>
        have after : trajectory σ ⟨.entry,u,false⟩ (n+1) = ⟨c,U,true⟩ := by
          simp [trajectory,current,worldEvent]
        have next := certified_stay u σ n c before (by simp [current])
          (Or.inl (by simp [current,after]))
        simpa only [after] using next
      | false =>
        cases writer : σ n with
        | true =>
          have after : trajectory σ ⟨.entry,u,false⟩ (n+1) = ⟨c,substitution U,false⟩ := by
            simp [trajectory,current,writer,worldEvent]
          have next := certified_stay u σ n c before (by simp [current])
            (Or.inr (by simp [current,after]))
          simpa only [after] using next
        | false =>
          cases c with
          | entry =>
            simp [trajectory,current,writer,worldEvent,step,Certified,emptyWork]
          | ready q row =>
            have after : trajectory σ ⟨.entry,u,false⟩ (n+1) = ⟨.ready q row,U,true⟩ := by
              simp [trajectory,current,writer,worldEvent,step]
            have next := certified_stay u σ n (.ready q row) before (by simp [current])
              (Or.inl (by simp [current,after]))
            simpa only [after] using next
          | active q w =>
            have next := certified_observer u σ n q w U current writer before
            simpa only [trajectory,writer,current] using next

/-- Every actually reached ready row has its authentic successful validation.
Only local observer instructions and the separate Return follow that Read. -/
theorem returning_capture (u : Source) (σ : Nat → Bool) (n : Nat)
    (q : Bool) (row : List Cell)
    (ready : (trajectory σ ⟨.entry,u,false⟩ n).config = .ready q row) :
    Captured u σ n q row := by
  have certified := trajectory_certified u σ n
  simpa only [ready,Certified] using certified


/-- The independent writer flags of a raw word; indices after it are observers. -/
def eventSchedule (h : Word) (n : Nat) : Bool :=
  match h[n]? with
  | some .update => true
  | _ => false

private theorem event_tail (e : NativeIndependentExecution.Event) (h : Word)
    (w : World) (n : Nat) :
    trajectory (eventSchedule (e :: h)) w (n+1) =
      trajectory (eventSchedule h) (worldEvent (eventSchedule (e :: h) 0) w) n := by
  rw [Nat.add_comm n 1,trajectory_add]
  have shifted : (fun i => eventSchedule (e :: h) (1+i)) = eventSchedule h := by
    funext i
    simp [eventSchedule,Nat.add_comm]
  rw [shifted]
  rfl

private theorem run_trajectory {c b : State} {U : Source} {h : Word}
    (run : Run step c U h b) :
    ∃ V : Source, trajectory (eventSchedule h) ⟨c,U,false⟩ h.length = ⟨b,V,true⟩ := by
  induction run with
  | @ret c U hop => exact ⟨U,by simp [eventSchedule,trajectory,worldEvent,hop]⟩
  | @localStep c d U h b hop rest ih =>
    obtain ⟨V,hv⟩ := ih
    refine ⟨V,?_⟩
    simpa [event_tail,eventSchedule,worldEvent,hop] using hv
  | @read c U p f y h b hop hy rest ih =>
    obtain ⟨V,hv⟩ := ih
    refine ⟨V,?_⟩
    simpa [event_tail,eventSchedule,worldEvent,hop,hy] using hv
  | update rest ih =>
    obtain ⟨V,hv⟩ := ih
    refine ⟨V,?_⟩
    simpa [event_tail,eventSchedule,worldEvent] using hv

/-- Every finite legal returning raw history has a last successful validation
on its actual register, followed by cleanup, independent writes and Return. -/
theorem all_returning_histories (u : Source) (h : Word) (q : Bool) (row : List Cell)
    (run : Run step .entry u h (.ready q row)) :
    Captured u (eventSchedule h) h.length q row := by
  obtain ⟨V,returned⟩ := run_trajectory run
  exact returning_capture u (eventSchedule h) h.length q row (by rw [returned])

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRARecordSoundness
