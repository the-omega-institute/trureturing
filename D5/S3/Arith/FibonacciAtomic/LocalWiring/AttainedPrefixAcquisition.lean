/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/AttainedPrefixAcquisition
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/AttainedPrefixAcquisition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attained native prefix acquisition, local work and the exact joint coordinates. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier

/-! Acquire exactly the mature prefix on the installed native service,
then use the corresponding finite source synthesizer. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition

open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock OrderedBirthPrefix
open PublicRowSeedReadiness LawfulSourceReadiness NativePastAcquisitionBarrier

/-- The public constraints, not the private source parameters. The entire supplied row
is fixed when its as yet unknown seed varies. -/
inductive Promise
  | lawful (C : LawfulClass)
  | row (r : Nat) (coeff : Fin r → Bool)

def Promise.Valid : Promise → Prop
  | .lawful C => ValidClass C
  | .row _ _ => True

def Promise.Legal : Promise → OutputStream → Prop
  | .lawful C, s => ClassLegal C s
  | .row _ c, s => ∃ seed, rowStream c seed = s

def Promise.target : Promise → Nat
  | .lawful C => requiredBits C
  | .row r _ => r

private theorem mature_eq (n : Nat) (hn : 2 ≤ n) : matureSize n = Nat.fib n - 1 :=
  (lawful_source_readiness (.binary 0) trivial n hn).2.2.1

private theorem exists_mature_ge (m : Nat) : ∃ n, 2 ≤ n ∧ m ≤ matureSize n := by
  refine ⟨m+5, by omega, ?_⟩
  rw [mature_eq _ (by omega)]
  have h := Nat.le_fib_self (n := m+5) (by omega)
  omega

/-- The least mature cut with enough available bits. In particular m=0 yields 2. -/
def deadline (m : Nat) : Nat := Nat.find (exists_mature_ge m)

theorem deadline_minimal (m : Nat) :
    2 ≤ deadline m ∧ m ≤ matureSize (deadline m) ∧
    ∀ n, 2 ≤ n → m ≤ matureSize n → deadline m ≤ n := by
  exact ⟨(Nat.find_spec (exists_mature_ge m)).1, (Nat.find_spec (exists_mature_ge m)).2,
    fun _ hn hm => Nat.find_min' (exists_mature_ge m) ⟨hn,hm⟩⟩

theorem deadline_zero : deadline 0 = 2 :=
  le_antisymm ((deadline_minimal 0).2.2 2 (by omega) (Nat.zero_le _)) (deadline_minimal 0).1

theorem deadline_pos (m : Nat) (hm : 0 < m) :
    3 ≤ deadline m ∧ m ≤ Nat.fib (deadline m) - 1 ∧
    ∀ n, 3 ≤ n → m ≤ Nat.fib n - 1 → deadline m ≤ n := by
  obtain ⟨hn,hv,hmin⟩ := deadline_minimal m
  have hz : matureSize 2 = 0 := by decide
  have hne : deadline m ≠ 2 := by
    intro h
    rw [h,hz] at hv
    omega
  exact ⟨by omega, mature_eq _ hn ▸ hv, fun n hn' hv' =>
    hmin n (by omega) ((mature_eq n (by omega)).symm ▸ hv')⟩

/-- Actual finite replay of the required prefix. No service access is used by synthesis. -/
def generate (P : Promise) (word : List Bool) : Option OutputStream :=
  match P with
  | .lawful C => synthesizeClass C word
  | .row _ c => some (rowStream c (seedFromPrefix word))

private theorem prefix_get {s : OutputStream} {k i : Nat} (hi : i < k) :
    (prefixBits (birthOf s) k)[i]? = some (s i) := by
  simp [prefixBits, consume, birthOf, hi]

private theorem prefix_take_eq (s : OutputStream) {a b : Nat} (h : a ≤ b) :
    (prefixBits (birthOf s) b).take a = prefixBits (birthOf s) a := by
  simp only [prefixBits, ← List.map_take, List.take_range, Nat.min_eq_left h]

private theorem synthesize_take (C : LawfulClass) (xs : List Bool) :
    synthesizeClass C (xs.take (requiredBits C)) = synthesizeClass C xs := by
  cases C with
  | binary d =>
    change (BoundedBinaryRecurrence.synthesize d ((xs.take (2*d)).take (2*d))).map _ =
      (BoundedBinaryRecurrence.synthesize d (xs.take (2*d))).map _
    simp only [requiredBits, List.take_take, Nat.min_self]
  | moore K =>
    change (UnaryMooreSeparation.synthesize K ((xs.take (2*K-1)).take (2*K-1))).map _ =
      (UnaryMooreSeparation.synthesize K (xs.take (2*K-1))).map _
    simp only [List.take_take, Nat.min_self]

private theorem generated_exact (P : Promise) (hP : P.Valid) (s : OutputStream)
    (hs : P.Legal s) : generate P (prefixBits (birthOf s) P.target) = some s := by
  cases P with
  | lawful C =>
    change ValidClass C at hP
    change ClassLegal C s at hs
    let n := deadline (requiredBits C)
    obtain ⟨hn,hv,_⟩ := deadline_minimal (requiredBits C)
    have hI := ((lawful_source_readiness C hP n hn).2.2.2.2.2.2
      .incidence s hs hv).1
    have hGeom := exact_ordered_birth_prefix (birthOf s) n hn
    change ((shapeFromIncidence
      (incidenceAddresses (shape (physicalBirthClock (birthOf s) n).tree))).bind
        maturePrefix).bind (fun w => (synthesizeClass C w.2).map (fun t => (w.1,t))) =
      some (n,s) at hI
    rw [hGeom.2.2.2.1, Option.bind_some, hGeom.2.2.2.2.2.2.2.2.1, Option.bind_some] at hI
    change synthesizeClass C (prefixBits (birthOf s) (requiredBits C)) = some s
    rw [← prefix_take_eq s hv, synthesize_take]
    simpa [matureSize] using hI
  | row r c =>
    obtain ⟨seed,rfl⟩ := hs
    change some (rowStream c (seedFromPrefix (prefixBits (birthOf (rowStream c seed)) r))) =
      some (rowStream c seed)
    congr 2
    funext i
    have hp := prefix_get (s := rowStream c seed) i.isLt
    have hseed := (public_row_seed_readiness r c seed 2 (by decide)).2.2.2.2.2.2.1 i
    simp [seedFromPrefix, hp, hseed]

open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock OrderedBirthPrefix
open PublicRowSeedReadiness LawfulSourceReadiness

/-- Local computation blocks are recorded separately from native service requests.
A block is not a paid Read, an Update, or an uncharged prerequisite. -/
inductive LocalWork
  | traverse (old : Labelled) (parents : List Address)
  | write (literal : Address)
  | retain (digit : Bool)
  | synthesize (word : List Bool)
  | reconstruct (cut : Nat)

/-- Locally installed generator, zero-based next-source index and all task answers.
This payload is part of the accessible final register, never a source reply. -/
structure Completion where
  generator : Option OutputStream
  nextIndex : Nat
  answers : Option Answers

/-- Reconstruct from the installed generator rather than from unobserved service data. -/
def buildCompletion (generator : Option OutputStream) (e : Nat) : Completion :=
  ⟨generator, clockSum e, generator.map fun s =>
    (physicalTree e s, fun p => queryNext e p s, future e s)⟩

/-- A source-blind program: the only branch affected by the native service
takes one Boolean Read reply. The fixed Update acknowledgement reveals nothing. -/
inductive Plan
  | stop (earned : List Bool) (result : Completion)
  | localStep (work : LocalWork) (next : Plan)
  | update (next : Plan)
  | read (literal : Address) (next : Bool → Plan)

/-- Complete actual service effects with local-work blocks in execution order. -/
inductive AcquisitionEvent
  | localStep (work : LocalWork)
  | update (cut : Nat) (response : Reply)
  | read (cut : Nat) (literal : Address) (answer : Bool)
  | stop

structure Acquisition where
  cut : Nat
  earned : List Bool
  events : List AcquisitionEvent
  result : Completion

private def push (event : AcquisitionEvent) (a : Acquisition) : Acquisition :=
  {a with events := event :: a.events}

/-- The only source calls are the frozen serial service's literal Read and Update. -/
def execute (z : BirthStream) (e : Nat) : Plan → Acquisition
  | .stop w result => ⟨e,w,[.stop],result⟩
  | .localStep op k => push (.localStep op) (execute z e k)
  | .update k => push (.update (e+1) (reply z e .update)) (execute z (e+1) k)
  | .read p k =>
      let b := match reply z e (.read p) with
        | .answer b => b
        | .ack => false
      push (.read e p b) (execute z e (k b))

/-- The observer writes each literal and retains the actual reply, before proceeding. -/
def readBatch (parents : List Address) (finish : List Bool → Plan) : Plan :=
  match parents with
  | [] => finish []
  | p::ps =>
    let literal := p ++ [false,false]
    .localStep (.write literal) (.read literal fun b =>
      .localStep (.retain b) (readBatch ps fun bs => finish (b::bs)))

/-- Once the first mature cut is reached, start each next batch by replaying
the old labelled tree from the bits actually retained before the batch. -/
def acquireBatches (P : Promise) (m : Nat) : Nat → Nat → List Bool → Plan
  | 0, e, word => .localStep (.synthesize word) <|
      let installed := generate P word
      .localStep (.reconstruct e) (.stop word (buildCompletion installed e))
  | k+1, e, word =>
    .update <| let t := labelsOfPrefix (e-1) word
      let parents := oldBetaAddresses [] t
      .localStep (.traverse t parents)
        (readBatch (parents.take (m-word.length))
          (fun received => acquireBatches P m k (e+1) (word++received)))

/-- The paid update primitive happens exactly twice before any mature batch. -/
def acquisitionPlan (P : Promise) (m N : Nat) : Plan :=
  .update (.update (acquireBatches P m (N-2) 2 []))

def AcquisitionEvent.literal? : AcquisitionEvent → Option Address
  | .read _ p _ => some p
  | _ => none

def AcquisitionEvent.update? : AcquisitionEvent → Bool
  | .update _ _ => true
  | _ => false

def Acquisition.addresses (a : Acquisition) : List Address :=
  a.events.filterMap AcquisitionEvent.literal?

def Acquisition.updates (a : Acquisition) : Nat :=
  (a.events.filter AcquisitionEvent.update?).length

def Acquisition.reads (a : Acquisition) : Nat := a.addresses.length

def Acquisition.weight (a : Acquisition) : Nat := (a.addresses.map List.length).sum

def Acquisition.maximum (a : Acquisition) : Nat := (a.addresses.map List.length).foldl max 0

private def literalOf (e : BirthEvent) : Address := e.parent ++ [false,false]

private theorem exec_batch (z : BirthStream) (e : Nat) (es : List BirthEvent)
    (h : ∀ b ∈ es, reply z e (.read (literalOf b)) = .answer b.mark)
    (next : List Bool → Plan) :
    let a := execute z e (readBatch (es.map BirthEvent.parent) next)
    let r := execute z e (next (es.map BirthEvent.mark))
    a.cut = r.cut ∧ a.earned = r.earned ∧
    a.addresses = es.map literalOf ++ r.addresses ∧ a.updates = r.updates := by
  induction es generalizing next with
  | nil => simp [readBatch]
  | cons b bs ih =>
    have hb := h b (by simp)
    have hs : ∀ b' ∈ bs, reply z e (.read (literalOf b')) = .answer b'.mark :=
      fun b' hb' => h b' (by simp [hb'])
    have hh := ih hs (fun ds => next (b.mark :: ds))
    simp only [literalOf] at hb
    simpa [readBatch, execute, push, hb, Acquisition.addresses, AcquisitionEvent.literal?,
      Acquisition.updates, AcquisitionEvent.update?, List.filterMap_cons, List.filter_cons,
      literalOf] using hh

open NativePastAcquisitionBarrier

abbrev Register := Plan × Nat

private def pick (r : Record Register) : Move Register :=
  let (p, last) := r.register
  if r.log.length = last then
    match p with
    | .stop _ _ => .stop
    | .localStep _ k => .compute (k, last + 1)
    | .update _ => .service .update
    | .read a _ => .service (.read a)
  else
    match p, r.log.getLast? with
    | .update k, some (.service .update .ack) => .compute (k, r.log.length + 1)
    | .read _ k, some (.service (.read _) (.answer b)) => .compute (k b, r.log.length + 1)
    | _, _ => .stop

/-- Initial plan and every subsequent choice depend only on the accessible record. -/
def planObserver : Observer Plan Unit Register where
  startState p _ := (p, 0)
  choose _ _ := pick

def nativeService : Event Register → Option (Action × Reply)
  | .service a r => some (a, r)
  | _ => none

def planService : AcquisitionEvent → Option (Action × Reply)
  | .read _ p b => some (.read p, .answer b)
  | .update _ r => some (.update, r)
  | _ => none

private theorem follow (p : Plan) (s : OutputStream) (p₀ : Plan) (j : Nat)
    (e : Nat) (log : List (Event Register))
    (h : run planObserver p₀ () s j = ⟨e, log, (p, log.length), [], false⟩) :
    ∃ k w c l, run planObserver p₀ () s k = ⟨(execute (birthOf s) e p).cut,
        log ++ l, (.stop w c, log.length + l.length - 1), [], true⟩ ∧
      w = (execute (birthOf s) e p).earned ∧
      c = (execute (birthOf s) e p).result ∧
      l.filterMap nativeService = (execute (birthOf s) e p).events.filterMap planService := by
  induction p generalizing j e log with
  | stop w c =>
    refine ⟨j + 1, w, c, [.stop], ?_, rfl, rfl, rfl⟩
    rw [run, h]
    simp [advance, planObserver, pick, execute]
  | localStep op p ih =>
    let l₁ := log ++ [.compute (p, log.length + 1)]
    have h₁ : run planObserver p₀ () s (j + 1) =
        ⟨e, l₁, (p, l₁.length), [], false⟩ := by
      rw [run, h]
      simp [advance, planObserver, pick, l₁]
    obtain ⟨k, w, c, l, hr, hw, hc, hl⟩ := ih (j+1) e l₁ h₁
    refine ⟨k, w, c, .compute (p, log.length + 1) :: l, ?_, ?_, ?_, ?_⟩
    · have he : (execute (birthOf s) e (.localStep op p)).cut =
          (execute (birthOf s) e p).cut := rfl
      simpa [he, l₁, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
    · exact hw
    · exact hc
    · exact hl
  | update p ih =>
    let l₁ := log ++ [.service .update .ack]
    let l₂ := l₁ ++ [.compute (p, l₁.length + 1)]
    have h₁ : run planObserver p₀ () s (j + 1) =
        ⟨e + 1, l₁, (.update p, log.length), [], false⟩ := by
      rw [run, h]
      simp [advance, planObserver, pick, l₁, nextEpoch, reply]
    have h₂ : run planObserver p₀ () s (j + 1 + 1) =
        ⟨e + 1, l₂, (p, l₂.length), [], false⟩ := by
      rw [run, h₁]
      simp [advance, planObserver, pick, l₂, l₁]
    obtain ⟨k, w, c, l, hr, hw, hc, hl⟩ := ih (j+1+1) (e+1) l₂ h₂
    refine ⟨k, w, c, .service .update .ack :: .compute (p, l₁.length + 1) :: l,
      ?_, ?_, ?_, ?_⟩
    · have he : (execute (birthOf s) e (.update p)).cut =
          (execute (birthOf s) (e + 1) p).cut := rfl
      simpa [he, l₂, l₁, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hr
    · exact hw
    · exact hc
    · exact congrArg ((Action.update, Reply.ack) :: ·) hl
  | read a next ih =>
    let b := KnownSeedCurrentFibers.present (physicalTree e s) a
    have hb : reply (birthOf s) e (.read a) = .answer b := rfl
    let l₁ := log ++ [.service (.read a) (.answer b)]
    let l₂ := l₁ ++ [.compute (next b, l₁.length + 1)]
    have h₁ : run planObserver p₀ () s (j + 1) =
        ⟨e, l₁, (.read a next, log.length), [], false⟩ := by
      rw [run, h]
      simp [advance, planObserver, pick, l₁, nextEpoch, hb]
    have h₂ : run planObserver p₀ () s (j + 1 + 1) =
        ⟨e, l₂, (next b, l₂.length), [], false⟩ := by
      rw [run, h₁]
      simp [advance, planObserver, pick, l₂, l₁]
    obtain ⟨k, w, c, l, hr, hw, hc, hl⟩ := ih b (j+1+1) e l₂ h₂
    refine ⟨k, w, c, .service (.read a) (.answer b) :: .compute (next b, l₁.length + 1) :: l,
      ?_, ?_, ?_, ?_⟩
    · have he : (execute (birthOf s) e (.read a next)).cut =
          (execute (birthOf s) e (next b)).cut := by rw [execute, hb]; rfl
      simpa [he, l₂, l₁, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hr
    · rw [execute, hb]; exact hw
    · rw [execute, hb]; exact hc
    · rw [execute, hb]
      exact congrArg ((Action.read a, Reply.answer b) :: ·) hl

theorem realize_plan (p : Plan) (s : OutputStream) :
    ∃ k, let r := run planObserver p () s k
         let a := execute (birthOf s) 0 p
         r.stopped = true ∧ r.cut = a.cut ∧ r.register.1 = .stop a.earned a.result ∧
           r.log.filterMap nativeService = a.events.filterMap planService := by
  obtain ⟨k, w, c, l, hr, hw, hc, hl⟩ := follow p s p 0 0 [] rfl
  exact ⟨k, by rw [hr]; simp [hw, hc, hl]⟩

-- The frozen clock exposes event membership; this local structural equation keeps
-- the traversal's exact order without opening the private clock proof.
private theorem round_parent_list (z : BirthStream) (n c : Nat) (p : Address) (t : Labelled) :
    (birthRound z n c p t).births.map BirthEvent.parent = oldBetaAddresses p t := by
  induction t generalizing c p with
  | of b => cases b <;> rfl
  | mul l r il ir => simp only [birthRound, oldBetaAddresses, List.map_append, il, ir]

private theorem oldTreeOfEarnedPrefix (z : BirthStream) (n : Nat) :
    labelsOfPrefix n (prefixBits z (clockSum n)) = (physicalBirthClock z n).tree := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | n+2 =>
    exact (exact_ordered_birth_prefix z (n+2) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem earned_batch_parents (z : BirthStream) (n : Nat) :
    let old := physicalBirthClock z n
    let batch := birthRound z (n + 1) old.cursor [] old.tree
    oldBetaAddresses [] (labelsOfPrefix n (prefixBits z (clockSum n))) =
      batch.births.map BirthEvent.parent := by
  rw [oldTreeOfEarnedPrefix]
  exact (round_parent_list _ _ _ _ _).symm

private theorem step_atTree {x y : Labelled} (h : Step x y)
    (p : Address) {u : Labelled} (hu : atTree x p = some u) :
    ∃ v, atTree y p = some v ∧ Step u v := by
  induction h generalizing p u with
  | alphaToBeta =>
    cases p with
    | nil => cases hu; exact ⟨_, rfl, .alphaToBeta⟩
    | cons b p => cases b <;> cases hu
  | betaLeft =>
    cases p with
    | nil => cases hu; exact ⟨_, rfl, .betaLeft⟩
    | cons b p => cases b <;> cases hu
  | betaRight =>
    cases p with
    | nil => cases hu; exact ⟨_, rfl, .betaRight⟩
    | cons b p => cases b <;> cases hu
  | branch a b il ir =>
    cases p with
    | nil => cases hu; exact ⟨_, rfl, .branch a b⟩
    | cons bit p =>
      cases bit
      · exact il p hu
      · exact ir p hu

private theorem lookup_append {A : Type} (t : FreeMagma A) (p q : Address) :
    atTree t (p ++ q) = (atTree t p).bind (fun u => atTree u q) := by
  induction p generalizing t with
  | nil => simp [atTree]
  | cons b p ih => cases t <;> cases b <;> first | rfl | exact ih _

private theorem read_marked_cherry {x y : Labelled} (h : Step x y) (p : Address) (mark : Bool)
    (hp : atTree x p = some (if mark then .mul beta alpha else .mul alpha beta)) :
    present y (p ++ [false, false]) = mark := by
  obtain ⟨v, hv, hs⟩ := step_atTree h p hp
  simp only [present, lookup_append, hv, Option.bind_some]
  cases mark with
  | false =>
    cases hs with
    | branch ha hb => cases ha; cases hb <;> rfl
  | true =>
    cases hs with
    | branch ha hb => cases ha <;> cases hb <;> rfl

private theorem actual_batch_read (z : BirthStream) (n : Nat) :
    let old := physicalBirthClock z n
    let batch := birthRound z (n + 1) old.cursor [] old.tree
    ∀ e ∈ batch.births,
      present (physicalBirthClock z (n+2)).tree (e.parent ++ [false,false]) = e.mark := by
  intro old batch e he
  have hc := physical_birth_clock z n
  have hm := hc.2.2.2.2.2.2.2.2.2.1.2.2.2 e he
  have hs := (physical_birth_clock z (n+1)).2.2.1
  exact read_marked_cherry hs e.parent e.mark hm.2

private def oldHeight : Labelled → Nat
  | .of _ => 0
  | .mul a b => max (oldHeight a) (oldHeight b) + 1

private theorem step_height {x y : Labelled} (h : Step x y) :
    oldHeight y ≤ oldHeight x + 1 := by
  induction h with
  | alphaToBeta => decide
  | betaLeft => decide
  | betaRight => decide
  | branch _ _ ia ib =>
    simp only [oldHeight]
    omega

private theorem clock_height (z : BirthStream) (n : Nat) :
    oldHeight (physicalBirthClock z (n+1)).tree ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact (step_height (physical_birth_clock z (n+1)).2.2.1).trans (Nat.add_le_add_right ih 1)

private theorem lookup_height {t u : Labelled} (p : Address) (hp : atTree t p = some u) :
    p.length ≤ oldHeight t := by
  induction p generalizing t with
  | nil => exact Nat.zero_le _
  | cons b p ih =>
    cases t with
    | of a => cases b <;> cases hp
    | mul l r =>
      cases b
      · have h := ih (t := l) hp
        have hl := Nat.le_max_left (oldHeight l) (oldHeight r)
        simp only [List.length_cons, oldHeight]
        omega
      · have h := ih (t := r) hp
        have hl := Nat.le_max_right (oldHeight l) (oldHeight r)
        simp only [List.length_cons, oldHeight]
        omega

private theorem actual_batch_depth (z : BirthStream) (n : Nat) :
    let old := physicalBirthClock z n
    let batch := birthRound z (n + 1) old.cursor [] old.tree
    ∀ e ∈ batch.births, e.parent.length ≤ n - 1 := by
  intro old batch e he
  have hm := (physical_birth_clock z n).2.2.2.2.2.2.2.2.2.1.2.2.1 e.parent
  have hmem : e.parent ∈ batch.births.map BirthEvent.parent := List.mem_map_of_mem he
  have hb := hm.mp hmem
  have hlook : atTree old.tree e.parent = some beta := of_decide_eq_true hb
  have hdepth := lookup_height e.parent hlook
  cases n with
  | zero => exact hdepth
  | succ n => exact hdepth.trans (clock_height z n)

private theorem marks_are_prefix (z : BirthStream) (n : Nat) :
    prefixBits z (clockSum n) = (physicalBirthClock z n).births.map BirthEvent.mark := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | k+2 =>
    have h := (exact_ordered_birth_prefix z (k+2) (by omega)).2.2.2.2.2.2.2.2.2.2.1
    have hp := (exact_ordered_birth_prefix z (k+2) (by omega)).2.2.2.2.2.2.2.2.2.2.2.1
    unfold completePrefix at hp
    rw [h, Option.map_some] at hp
    exact (congrArg Prod.snd (Option.some.inj hp)).symm

private theorem clock_birth_append (z : BirthStream) (n : Nat) :
    let old := physicalBirthClock z n
    (physicalBirthClock z (n+1)).births = old.births ++
      (birthRound z (n + 1) old.cursor [] old.tree).births := rfl

private theorem all_query_depth (z : BirthStream)
    (batchDepth : ∀ n, let old := physicalBirthClock z n
      let batch := birthRound z (n + 1) old.cursor [] old.tree
      ∀ e ∈ batch.births, e.parent.length ≤ n - 1)
    (n : Nat) (e : BirthEvent) (he : e ∈ (physicalBirthClock z n).births) :
    (e.parent ++ [false,false]).length ≤ n := by
  induction n with
  | zero => cases he
  | succ n ih =>
    rw [clock_birth_append, List.mem_append] at he
    rcases he with ho | hb
    · exact (ih ho).trans (Nat.le_succ _)
    · cases n with
      | zero => cases hb
      | succ n =>
        have hh := batchDepth (n+1) e hb
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega

private theorem take_append_drop_left {A : Type} (xs ys : List A) (m : Nat) :
    ((xs ++ ys).take m).drop xs.length = ys.take (m - xs.length) := by
  rw [List.drop_take, List.drop_left]

private theorem prefix_take_clock {A : Type} (xs ys : List A) (m : Nat) (h : xs.length ≤ m) :
    (xs ++ ys).take m = xs ++ ys.take (m - xs.length) := by
  rw [List.take_append, List.take_of_length_le h]

private def birthsAt (z : BirthStream) (n : Nat) : List BirthEvent :=
  (physicalBirthClock z n).births

private def matureBirths (z : BirthStream) (n : Nat) : List BirthEvent := birthsAt z (n-1)

private theorem matureBirths_length (z : BirthStream) (n : Nat) :
    (matureBirths z n).length = matureSize n :=
  (physical_birth_clock z (n-1)).2.2.2.2.1

private theorem birth_prefix (z : BirthStream) {n N : Nat} (h : n ≤ N) :
    ∃ extra, birthsAt z N = birthsAt z n ++ extra := by
  induction N, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ N _ ih =>
    obtain ⟨tail,h⟩ := ih
    refine ⟨tail ++ (birthRound z (N+1) (physicalBirthClock z N).cursor []
      (physicalBirthClock z N).tree).births,?_⟩
    unfold birthsAt at *
    rw [clock_birth_append, h, List.append_assoc]

private theorem slices {T : Type} (old batch extra : List T) (m : Nat) :
    (((old ++ batch ++ extra).take m).drop old.length) =
    batch.take (m-old.length) ++
      (((old ++ batch ++ extra).take m).drop (old ++ batch).length) := by
  rw [List.append_assoc, take_append_drop_left, ← List.append_assoc, take_append_drop_left,
    List.take_append]
  simp only [List.length_append]
  rw [show m - old.length - batch.length = m - (old.length + batch.length) by omega]

private theorem exec_mature_batches (P : Promise) (z : BirthStream) (m e k : Nat) (he : 2 ≤ e)
    (hend : e + k = deadline m) :
    let bs := (matureBirths z e).take m
    let word := bs.map BirthEvent.mark
    let got := execute z e (acquireBatches P m k e word)
    let expected := (matureBirths z (deadline m)).take m
    got.cut = deadline m ∧ got.earned = expected.map BirthEvent.mark ∧
      got.addresses = (expected.drop (matureBirths z e).length).map literalOf ∧
      got.updates = k := by
  induction k generalizing e with
  | zero =>
    obtain rfl : e = deadline m := by omega
    simp [acquireBatches, execute, push, Acquisition.addresses, Acquisition.updates,
      AcquisitionEvent.literal?, AcquisitionEvent.update?, List.filterMap_cons,
      List.drop_take, List.drop_length]
  | succ k ih =>
    let old := physicalBirthClock z (e-1)
    let batch := (birthRound z e old.cursor [] old.tree).births
    let earlier := matureBirths z e
    let part := batch.take (m-earlier.length)
    obtain hsmall : earlier.length < m := by
      rw [show earlier.length = matureSize e from matureBirths_length z e]
      by_contra! h
      have hc := (deadline_minimal m).2.2 e he h
      omega
    have hclock : (matureBirths z (e+1)) = earlier ++ batch := by
      dsimp only [matureBirths, birthsAt, earlier, batch, old]
      simpa only [Nat.add_sub_cancel, show e-1+1=e by omega] using clock_birth_append z (e-1)
    have hword : ((matureBirths z (e+1)).take m).map BirthEvent.mark =
        earlier.map BirthEvent.mark ++ part.map BirthEvent.mark := by
      rw [hclock, prefix_take_clock _ _ _ hsmall.le, List.map_append]
    have hparents : oldBetaAddresses [] (labelsOfPrefix (e-1) (earlier.map BirthEvent.mark)) =
        batch.map BirthEvent.parent := by
      change oldBetaAddresses [] (labelsOfPrefix (e-1)
        ((physicalBirthClock z (e-1)).births.map BirthEvent.mark)) = _
      rw [← marks_are_prefix]
      simpa only [show e-1+1=e by omega] using earned_batch_parents z (e-1)
    have hreply : ∀ b ∈ part, reply z (e+1) (.read (literalOf b)) = .answer b.mark := by
      intro b hb
      have h := actual_batch_read z (e-1) b (show b ∈
        (birthRound z (e-1+1) old.cursor [] old.tree).births from by
          rw [show e-1+1=e by omega]
          exact List.mem_of_mem_take hb)
      change Reply.answer (present (physicalBirthClock z (e+1)).tree (literalOf b)) =
        Reply.answer b.mark
      rw [show e+1=e-1+2 by omega]
      exact congrArg Reply.answer h
    have hLater := ih (e+1) (by omega) (by omega)
    dsimp only at hLater
    rw [hword] at hLater
    have hRun := exec_batch z (e+1) part hreply
      (fun w => acquireBatches P m k (e+1) (earlier.map BirthEvent.mark ++ w))
    have hpath :
        (((matureBirths z (deadline m)).take m).drop earlier.length).map literalOf =
        part.map literalOf ++
        (((matureBirths z (deadline m)).take m).drop (matureBirths z (e+1)).length).map
          literalOf := by
      obtain ⟨extra,hx⟩ := birth_prefix z
        (Nat.sub_le_sub_right (show e+1 ≤ deadline m by omega) 1)
      change matureBirths z (deadline m) = matureBirths z (e+1) ++ extra at hx
      rw [hx, hclock, slices, List.map_append]
    have hstage : (oldBetaAddresses [] (labelsOfPrefix (e-1)
        (earlier.map BirthEvent.mark))).take (m-(earlier.map BirthEvent.mark).length) =
          part.map BirthEvent.parent := by
      rw [hparents, List.length_map, ← List.map_take]
    dsimp only
    have htake : (matureBirths z e).take m = earlier := List.take_of_length_le hsmall.le
    rw [htake]
    simp only [acquireBatches]
    rw [hstage]
    obtain ⟨hc,hw,ha,hu⟩ := hRun
    obtain ⟨hfc,hfw,hfa,hfu⟩ := hLater
    refine ⟨hc.trans hfc, hw.trans hfw, ?_, ?_⟩
    · change (execute z (e+1) (readBatch (part.map BirthEvent.parent)
        (fun w => acquireBatches P m k (e+1) (earlier.map BirthEvent.mark ++ w)))).addresses = _
      exact ha.trans (by rw [hfa]; exact hpath.symm)
    · change (execute z (e+1) (readBatch (part.map BirthEvent.parent)
        (fun w => acquireBatches P m k (e+1) (earlier.map BirthEvent.mark ++ w)))).updates + 1 = _
      exact congrArg (·+1) (hu.trans hfu)

private theorem exec_acquisition (P : Promise) (z : BirthStream) (m : Nat) :
    let N := deadline m
    let got := execute z 0 (acquisitionPlan P m N)
    got.cut = N ∧ got.earned = prefixBits z m ∧
      got.addresses = ((matureBirths z N).take m).map literalOf ∧ got.updates = N := by
  obtain ⟨hN,hm,_⟩ := deadline_minimal m
  have h := exec_mature_batches P z m 2 (deadline m-2) (by decide) (by omega)
  have hempty : matureBirths z 2 = [] := rfl
  have htake : prefixBits z m = ((matureBirths z (deadline m)).take m).map BirthEvent.mark := by
    have he : m ≤ clockSum (deadline m-1) := hm
    rw [List.map_take, ← show prefixBits z (clockSum (deadline m-1)) =
        (matureBirths z (deadline m)).map BirthEvent.mark from marks_are_prefix z _]
    simp only [prefixBits, ← List.map_take, List.take_range, Nat.min_eq_left he]
  simp only [hempty, List.take_nil, List.map_nil, List.length_nil, List.drop_zero] at h
  rcases h with ⟨hc,hd,ha,hu⟩
  simp only [acquisitionPlan, execute, push, Acquisition.addresses, Acquisition.updates,
    List.filterMap_cons, List.filter_cons, AcquisitionEvent.literal?, AcquisitionEvent.update?,
    ite_true, List.length_cons, Nat.zero_add]
  refine ⟨hc,hd.trans htake.symm,ha,?_⟩
  change (execute z 2 (acquireBatches P m (deadline m-2) 2 [])).updates + 1 + 1 = _
  omega

#print axioms exec_acquisition
/-- A joint transcript from the common initial alpha root, for the actual one source. -/
def acquire (P : Promise) (s : OutputStream) : Acquisition :=
  execute (birthOf s) 0 (acquisitionPlan P P.target (deadline P.target))

/-- The actual output law installed using only the already earned bits. -/
def installEarned (a : Acquisition) : Option OutputStream :=
  a.result.generator

/-- Current labels and the two behavior projections are reconstructed and predicted
locally from the installed generator; unqueried actual bits are not treated as replies. -/
def acquiredAnswers (a : Acquisition) : Option Answers :=
  a.result.answers

/-- The native receipt explicitly charges a synthesis and a reconstruction
local phase before stop. The generator and reconstruction themselves are
the computations `installEarned` and `acquiredAnswers`; no numerical
machine-level cost is inferred from the count of local blocks. -/
def Acquisition.completionRecorded (P : Promise) (a : Acquisition) : Prop :=
  (∃ before, a.events = before ++ [.localStep (.synthesize a.earned),
    .localStep (.reconstruct a.cut), .stop]) ∧
  a.result = buildCompletion (generate P a.earned) a.cut

private theorem completion_push {P : Promise} {a : Acquisition} (h : a.completionRecorded P)
    (e : AcquisitionEvent) : (push e a).completionRecorded P := by
  obtain ⟨⟨before,hb⟩,hr⟩ := h
  exact ⟨⟨e::before, congrArg (e :: ·) hb⟩,hr⟩

private theorem completion_readBatch (P : Promise) (z : BirthStream) (e : Nat)
    (parents : List Address) (next : List Bool → Plan)
    (h : ∀ w, (execute z e (next w)).completionRecorded P) :
    (execute z e (readBatch parents next)).completionRecorded P := by
  induction parents generalizing next with
  | nil => exact h []
  | cons p ps ih =>
    simp only [readBatch, execute]
    apply completion_push
    split
    all_goals
      apply completion_push
      apply completion_push
      apply ih
      intro w
      apply h

private theorem completion_batches (P : Promise) (z : BirthStream) (m k e : Nat)
    (word : List Bool) :
    (execute z e (acquireBatches P m k e word)).completionRecorded P := by
  induction k generalizing e word with
  | zero => exact ⟨⟨[],rfl⟩,rfl⟩
  | succ k ih =>
    simp only [acquireBatches, execute]
    apply completion_push
    apply completion_push
    apply completion_readBatch
    intro w
    apply ih

private theorem completion_acquire (P : Promise) (s : OutputStream) :
    (acquire P s).completionRecorded P :=
  completion_push (completion_push
    (completion_batches P (birthOf s) _ _ 2 []) _) _

private theorem zero_target_law (P : Promise) (hP : P.Valid) (s : OutputStream)
    (hs : P.Legal s) (hm : P.target = 0) : ∀ i, s i = false := by
  cases P with
  | lawful C =>
    cases C with
    | moore K =>
      change 1 ≤ K at hP
      change 2*K-1 = 0 at hm
      omega
    | binary d =>
      change 2*d = 0 at hm
      have hd : d = 0 := by omega
      subst d
      obtain ⟨r,hr,c,h⟩ := hs
      have hz : r = 0 := by omega
      subst r
      intro i
      have eq := h i
      cases hb : s i
      · rfl
      · simp [hb, bitNat] at eq
  | row r c =>
    change r = 0 at hm
    subst r
    obtain ⟨seed,rfl⟩ := hs
    intro i
    rw [rowStream]
    simp

private theorem sum_literal_bound (xs : List Address) (b : Nat) (h : ∀ x ∈ xs, x.length ≤ b) :
    (xs.map List.length).sum ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    omega

private theorem max_literal_bound (xs : List Address) (b v : Nat)
    (h : ∀ x ∈ xs, x.length ≤ b) (hv : v ≤ b) :
    (xs.map List.length).foldl max v ≤ b := by
  induction xs generalizing v with
  | nil => exact hv
  | cons x xs ih =>
    apply ih (max v x.length) (fun y hy => h y (by simp [hy]))
    exact max_le hv (h x (by simp))

/-- The native acquisition attains all four coordinates jointly on its one source.
Only the update deadline, not the Read coordinates or local work, is minimized. -/
theorem attained_prefix_acquisition (P : Promise) (hP : P.Valid)
    (s : OutputStream) (hs : P.Legal s) :
    (acquire P s).earned = prefixBits (birthOf s) P.target ∧
    let m := P.target
    let N := deadline m
    let a := acquire P s
    let addresses := ((matureBirths (birthOf s) N).take m).map literalOf
    a.cut = N ∧ installEarned a = some s ∧
    acquiredAnswers a = some (physicalTree N s, fun p => queryNext N p s, future N s) ∧
    a.addresses = addresses ∧ a.reads = m ∧ a.updates = N ∧
    a.weight = (addresses.map List.length).sum ∧
    a.maximum = (addresses.map List.length).foldl max 0 ∧
    a.weight ≤ m * (N-1) ∧ a.maximum ≤ N-1 ∧
    (m = 0 → N = 2 ∧ a.reads = 0 ∧ a.weight = 0 ∧ a.maximum = 0 ∧ ∀ i, s i = false) ∧
    (0 < m → 3 ≤ N ∧ m ≤ Nat.fib N - 1 ∧
      ∀ n, 3 ≤ n → m ≤ Nat.fib n - 1 → N ≤ n) ∧
    a.completionRecorded P ∧ a.result.nextIndex = clockSum N ∧
    (∃ k, let r := run planObserver (acquisitionPlan P m N) () s k
      r.stopped = true ∧ r.cut = a.cut ∧ r.register.1 = .stop a.earned a.result ∧
        r.log.filterMap nativeService = a.events.filterMap planService) := by
  dsimp only
  let N := deadline P.target
  let zs := birthOf s
  let a := acquire P s
  let addr := ((matureBirths zs N).take P.target).map literalOf
  change a.earned = prefixBits zs P.target ∧ a.cut = N ∧ _ ∧ _ ∧
    a.addresses = addr ∧ _
  obtain ⟨hc,hw,hA,hU⟩ := exec_acquisition P zs P.target
  have hR : a.reads = P.target := by
    change a.addresses.length = P.target
    change a.addresses = addr at hA
    rw [hA]
    have hlen := matureBirths_length zs N
    have hle : P.target ≤ matureSize N := (deadline_minimal P.target).2.1
    simp only [addr, List.length_map, List.length_take, hlen, Nat.min_eq_left hle]
  have hDone := completion_acquire P s
  have hResult := hDone.2
  have hg : generate P a.earned = some s := by
    change a.earned = prefixBits zs P.target at hw
    rw [hw]
    exact generated_exact P hP s hs
  have hG : installEarned a = some s := by
    rw [installEarned, hResult, hg]
    rfl
  have answers : acquiredAnswers a =
      some (physicalTree N s, fun p => queryNext N p s, future N s) := by
    change a.cut = N at hc
    rw [acquiredAnswers,hResult,hg,hc]
    rfl
  have hCursor : a.result.nextIndex = clockSum N := by
    change a.cut = N at hc
    rw [hResult,hc]
    rfl
  have hB : ∀ p ∈ a.addresses, p.length ≤ N-1 := by
    change a.addresses = addr at hA
    rw [hA]
    intro p hp
    obtain ⟨ev,he,rfl⟩ := List.mem_map.mp hp
    exact all_query_depth zs (actual_batch_depth zs) (N-1) ev (List.mem_of_mem_take he)
  refine ⟨hw,hc,hG,answers,hA,hR,hU,?_,?_,?_,?_,?_,deadline_pos P.target,
    hDone, hCursor, realize_plan (acquisitionPlan P P.target N) s⟩
  · change a.addresses = addr at hA
    rw [Acquisition.weight, hA]
  · change a.addresses = addr at hA
    rw [Acquisition.maximum, hA]
  · change a.weight ≤ P.target * (N-1)
    rw [← hR]
    exact sum_literal_bound a.addresses (N-1) hB
  · exact max_literal_bound a.addresses (N-1) 0 hB (Nat.zero_le _)
  · intro hz
    have hzero : a.addresses = [] := by
      apply List.length_eq_zero_iff.mp
      exact hR.trans hz
    refine ⟨by rw [hz, deadline_zero], hR.trans hz, ?_, ?_, zero_target_law P hP s hs hz⟩
    · change a.weight = 0
      simp [Acquisition.weight, hzero]
    · change a.maximum = 0
      simp [Acquisition.maximum, hzero]

#print axioms attained_prefix_acquisition

end D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition
