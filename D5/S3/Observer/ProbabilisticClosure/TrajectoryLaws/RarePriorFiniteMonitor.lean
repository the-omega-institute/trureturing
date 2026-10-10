/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A saturating whole-word monitor lifts the original partial native transactions. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open FourthSegmentStoppedLaw NativeAcquiredPrefixState

def blockWord : List Letter := [0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1]
def latchWord : List Letter := [1,0,1,1,0,0]
def blocks : ℕ → List Letter
  | 0 => []
  | n+1 => blocks n ++ blockWord

def sat (n : ℕ) : Fin 376 := ⟨min n 375, by omega⟩
def increment (c : Fin 376) : Fin 376 := sat (c.val+1)

inductive Monitor where
  | block (count : Fin 376) (position : Fin 16)
  | suffix (position : Fin 5)
  | accepted
  | sink
  deriving DecidableEq, Fintype

def monitorInitial : Monitor := .block 0 0

/-- The first input letter is processed at block position zero. -/
def scan : Monitor → Letter → Monitor
  | .block c p, x =>
      if p = 0 ∧ x = 1 then
        if c = 375 then .suffix 0 else .sink
      else if x = (if p.val < 6 then 0 else 1) then
        if h : p.val < 15 then .block c ⟨p.val+1, by omega⟩
        else .block (increment c) 0
      else .sink
  | .suffix p, x =>
      if x = (if p.val = 0 ∨ p.val ≥ 3 then 0 else 1) then
        if h : p.val < 4 then .suffix ⟨p.val+1, by omega⟩ else .accepted
      else .sink
  | .accepted, _ | .sink, _ => .sink

def scanWord (m : Monitor) (w : List Letter) : Monitor := w.foldl scan m

def Represents (m : Monitor) (w : List Letter) : Prop :=
  match m with
  | .block c p => ∃ n, c = sat n ∧ w = blocks n ++ blockWord.take p.val
  | .suffix p => ∃ n, 375 ≤ n ∧ w = blocks n ++ latchWord.take (p.val+1)
  | .accepted => ∃ n, 375 ≤ n ∧ w = blocks n ++ latchWord
  | .sink => True

private theorem sat_increment (n : ℕ) : increment (sat n) = sat (n+1) := by
  apply Fin.ext
  simp only [increment, sat, Fin.val_mk]
  omega

private theorem step_represents (m : Monitor) (w : List Letter) (x : Letter)
    (h : Represents m w) : Represents (scan m x) (w ++ [x]) := by
  cases m with
  | sink => trivial
  | accepted => trivial
  | suffix p =>
      obtain ⟨n, hn, rfl⟩ := h
      fin_cases p <;> fin_cases x <;>
        simp [scan, Represents, latchWord, List.append_assoc] <;>
        exact ⟨n, hn, rfl⟩
  | block c p =>
      obtain ⟨n, hc, rfl⟩ := h
      subst c
      fin_cases p <;> fin_cases x
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · by_cases hn : 375 ≤ n
        · have he : sat n = 375 := by apply Fin.ext; simp [sat]; omega
          simp [scan, he, Represents, latchWord]
          exact ⟨n, hn, rfl⟩
        · have he : sat n ≠ 375 := by intro he; have hv := congrArg Fin.val he; simp [sat] at hv; omega
          simp [scan, he, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents, blockWord, List.append_assoc]
        exact ⟨n, rfl, rfl⟩
      · simp [scan, Represents]
      · simp [scan, Represents]
        exact ⟨n+1, sat_increment n, by simp [blocks, blockWord, List.append_assoc]⟩

private theorem scan_append (m : Monitor) (u v : List Letter) :
    scanWord m (u ++ v) = scanWord (scanWord m u) v := by
  exact List.foldl_append

private theorem represents_run (w : List Letter) : Represents (scanWord monitorInitial w) w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨0, rfl, rfl⟩
  | append_singleton w x ih =>
      simpa [scan_append, scanWord] using step_represents _ w x ih

private theorem scan_block (c : Fin 376) :
    scanWord (.block c 0) blockWord = .block (increment c) 0 := by
  simp [scanWord, blockWord, scan]

private theorem scan_blocks (n : ℕ) :
    scanWord monitorInitial (blocks n) = .block (sat n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [blocks, scan_append, ih, scan_block, sat_increment]

/-- Exact language from the first Read, with saturation rather than an unbounded runtime count. -/
theorem whole_word_recognition (w : List Letter) :
    scanWord monitorInitial w = .accepted ↔
      ∃ n : ℕ, 375 ≤ n ∧ w = blocks n ++ latchWord := by
  constructor
  · intro h
    have hr := represents_run w
    rwa [h] at hr
  · rintro ⟨n, hn, rfl⟩
    have he : sat n = 375 := by apply Fin.ext; simp [sat]; omega
    rw [scan_append, scan_blocks, he]
    simp [scanWord, latchWord, scan]

inductive Mode where
  | watching | ordinary | g | gBeta
  deriving DecidableEq

instance : Fintype Mode := ⟨{.watching, .ordinary, .g, .gBeta}, by intro m; cases m <;> simp⟩

structure Runtime where
  fields : FiniteFields
  monitor : Monitor
  mode : Mode
  deriving DecidableEq, Fintype

def runtimeInitial : Runtime := ⟨initial.source.finiteFields, monitorInitial, .watching⟩

/-- Mode changes occur after the original transaction, including its third write and latch. -/
def nextMode (m : Mode) (mon : Monitor) (op : Operation) : Mode :=
  match m, op with
  | .ordinary, _ => .ordinary
  | .g, .read x => if x = 0 then .ordinary else .gBeta
  | .gBeta, .read _ => .ordinary
  | .g, .stop _ | .gBeta, .stop _ => .ordinary
  | .watching, .stop _ => .ordinary
  | .watching, .read _ =>
      match mon with
      | .accepted => .g
      | .sink => .ordinary
      | _ => .watching

def runtimeStep (z : Runtime) (op : Operation) : Option Runtime :=
  (finiteStep z.fields op).map fun f =>
    let mon := match op with | .read x => scan z.monitor x | .stop _ => .sink
    ⟨f, mon, nextMode z.mode mon op⟩

def runtimeExecute (z : Runtime) : List Operation → Option Runtime
  | [] => some z
  | op::ops => (runtimeStep z op).bind (fun d => runtimeExecute d ops)

def runtimeRun : List Operation → Option Runtime := runtimeExecute runtimeInitial

/-- All legal successors and all failures project to the original finite transaction. -/
theorem runtime_projection (z : Runtime) (ops : List Operation) :
    (runtimeExecute z ops).map Runtime.fields = executeFinite z.fields ops := by
  induction ops generalizing z with
  | nil => rfl
  | cons op ops ih =>
      cases hf : finiteStep z.fields op with
      | none => simp [runtimeExecute, runtimeStep, executeFinite, hf]
      | some f => simp [runtimeExecute, runtimeStep, executeFinite, hf, ih]

/-- The full native histories retain their numeric source coordinates externally. -/
theorem arbitrary_legal_projection (ops : List Operation) (h : Legal ops) :
    (runtimeRun ops).map Runtime.fields = (run ops).map (fun c => c.source.finiteFields) := by
  obtain ⟨nf, hf, _⟩ := (native_acquired_prefix_reconstruction ops).1.mp h
  obtain ⟨hr, _, hfin⟩ := (native_acquired_prefix_reconstruction ops).2 nf hf
  rw [hr, Option.map_some]
  exact (runtime_projection runtimeInitial ops).trans hfin

/-- Total matrices may use this row off permission; runtimeStep still forbids terminal Reads. -/
def queryMode (z : Runtime) : Mode :=
  match z.fields.control, z.mode with
  | .fourth (.active .p), .g => .g
  | .fourth (.active .beta), .gBeta => .gBeta
  | _, _ => .ordinary

/-- Exhaustive finite classification; no counter bank or history is queried. -/
theorem query_mode_classification (z : Runtime) :
    (queryMode z = .g ↔ z.fields.control = .fourth (.active .p) ∧ z.mode = .g) ∧
    (queryMode z = .gBeta ↔ z.fields.control = .fourth (.active .beta) ∧ z.mode = .gBeta) ∧
    (queryMode z = .ordinary ↔
      ¬(z.fields.control = .fourth (.active .p) ∧ z.mode = .g) ∧
      ¬(z.fields.control = .fourth (.active .beta) ∧ z.mode = .gBeta)) := by
  cases z with | mk f mon m =>
    cases f with | mk c r =>
      cases c with
      | seed first => cases m <;> simp [queryMode]
      | early t s => cases m <;> simp [queryMode]
      | fourth c => cases c with
        | active s => cases s <;> cases m <;> simp [queryMode]
        | pending b => cases m <;> simp [queryMode]
        | delivered => cases m <;> simp [queryMode]

private theorem runtime_append (z : Runtime) (u v : List Operation) :
    runtimeExecute z (u ++ v) =
      (runtimeExecute z u).bind (fun d => runtimeExecute d v) := by
  induction u generalizing z with
  | nil => rfl
  | cons op u ih =>
    simp only [List.cons_append, runtimeExecute]
    cases runtimeStep z op <;> simp [ih]

private theorem runtime_block (c : Fin 376) :
    runtimeExecute ⟨initial.source.finiteFields, .block c 0, .watching⟩ (reads blockWord) =
      some ⟨initial.source.finiteFields, .block (increment c) 0, .watching⟩ := by
  simp [blockWord, reads, runtimeExecute, runtimeStep, finiteStep, finiteRead,
    initial, emptyRegisters, scan, nextMode]

private theorem runtime_blocks (n : ℕ) :
    runtimeRun (reads (blocks n)) =
      some ⟨initial.source.finiteFields, .block (sat n) 0, .watching⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [blocks, reads, List.map_append]
      rw [runtimeRun, runtime_append]
      change (runtimeRun (reads (blocks n))).bind _ = _
      rw [ih]
      simpa [sat_increment, reads] using runtime_block (sat n)

def latchedFields : FiniteFields :=
  ⟨.fourth (.active .p), markerRegisters 1 [1,0,0]⟩

def beforeLatchFields : FiniteFields :=
  ⟨.early 2 .p, markerRegisters 1 [1,0]⟩

/-- Every selected word activates after the third original write and its bare latch. -/
theorem original_latch_activation (n : ℕ) (hn : 375 ≤ n) :
    runtimeRun (reads (blocks n ++ latchWord)) =
      some ⟨latchedFields, .accepted, .g⟩ ∧
    runtimeRun (reads (blocks n ++ latchWord.take 5)) =
      some ⟨beforeLatchFields, .suffix 4, .watching⟩ ∧
    beforeLatchFields.registers.snapshot = none ∧
    latchedFields.registers.snapshot = some ⟨1,1,1⟩ ∧
    finiteStep beforeLatchFields (.read 0) = some latchedFields := by
  have hs : sat n = 375 := by apply Fin.ext; simp [sat]; omega
  have hr (w : List Letter) : runtimeRun (reads (blocks n ++ w)) =
      runtimeExecute ⟨initial.source.finiteFields, .block 375 0, .watching⟩ (reads w) := by
    simp only [reads, List.map_append, runtimeRun, runtime_append]
    change (runtimeRun (reads (blocks n))).bind _ = _
    rw [runtime_blocks, hs]
    rfl
  rw [hr latchWord, hr (latchWord.take 5)]
  norm_num [latchWord, reads, runtimeExecute, runtimeStep, finiteStep, finiteRead,
    payloadRead, completionControl, payloadControl, writeMarker, writeRecords,
    initial, emptyRegisters, scan, nextMode, latchedFields, beforeLatchFields,
    markerRegisters, foldMarkers, acquiredRegisters] <;> decide

/-- G completes on alpha; beta enters Gbeta, whose alpha performs the original return. -/
theorem special_transactions (r : Registers) (mon : Monitor) :
    runtimeStep ⟨⟨.fourth (.active .p), r⟩, mon, .g⟩ (.read 0) =
      some ⟨⟨.fourth (.pending 0), writeMarker r 3 0⟩, scan mon 0, .ordinary⟩ ∧
    runtimeStep ⟨⟨.fourth (.active .p), r⟩, mon, .g⟩ (.read 1) =
      some ⟨⟨.fourth (.active .beta), r⟩, scan mon 1, .gBeta⟩ ∧
    runtimeStep ⟨⟨.fourth (.active .beta), r⟩, mon, .gBeta⟩ (.read 0) =
      some ⟨⟨.fourth (.active .p), r⟩, scan mon 0, .ordinary⟩ ∧
    runtimeStep ⟨⟨.fourth (.active .beta), r⟩, mon, .gBeta⟩ (.read 1) =
      some ⟨⟨.fourth (.pending 1), writeMarker r 3 1⟩, scan mon 1, .ordinary⟩ := by
  simp [runtimeStep, finiteStep, finiteRead, payloadRead, payloadControl,
    completionControl, nextMode]

/-- Both terminal branches retain the original partial operation menu. -/
theorem terminal_permissions (r : Registers) (mon : Monitor) (m : Mode) (a b x : Letter) :
    runtimeStep ⟨⟨.fourth (.pending a), r⟩, mon, m⟩ (.read x) = none ∧
    (runtimeStep ⟨⟨.fourth (.pending a), r⟩, mon, m⟩ (.stop b)).map Runtime.fields =
      (if b = a then some ⟨.fourth .delivered, r⟩ else none) ∧
    runtimeStep ⟨⟨.fourth .delivered, r⟩, mon, m⟩ (.read x) = none ∧
    runtimeStep ⟨⟨.fourth .delivered, r⟩, mon, m⟩ (.stop b) = none := by
  simp [runtimeStep, finiteStep, finiteRead, finiteStop]

def ModeHistory (z : Runtime) (ops : List Operation) : Prop :=
  match z.mode with
  | .watching => ∃ w, ops = reads w ∧ z.monitor = scanWord monitorInitial w
  | .g => ∃ n, 375 ≤ n ∧ ops = reads (blocks n ++ latchWord)
  | .gBeta => ∃ n, 375 ≤ n ∧ ops = reads (blocks n ++ latchWord ++ [1])
  | .ordinary => True

private theorem mode_history_step (z d : Runtime) (ops : List Operation)
    (op : Operation) (hh : ModeHistory z ops) (hd : runtimeStep z op = some d) :
    ModeHistory d (ops ++ [op]) := by
  cases z with | mk f mon m =>
    cases hf : finiteStep f op with
    | none => simp [runtimeStep, hf] at hd
    | some f' =>
      simp only [runtimeStep, hf, Option.map_some, Option.some.injEq] at hd
      subst d
      cases m with
      | ordinary => trivial
      | gBeta => cases op <;> trivial
      | g =>
        obtain ⟨n, hn, hops⟩ := hh
        cases op with
        | stop b => trivial
        | read x =>
          fin_cases x
          · trivial
          · exact ⟨n, hn, by simp [hops, reads, List.map_append]⟩
      | watching =>
        obtain ⟨w, hops, hm⟩ := hh
        change mon = scanWord monitorInitial w at hm
        cases op with
        | stop b => trivial
        | read x =>
          have hscan : scan mon x = scanWord monitorInitial (w ++ [x]) := by
            rw [hm, scan_append]; rfl
          cases he : scan mon x with
          | sink => simp [nextMode, he, ModeHistory]
          | accepted =>
            simp only [nextMode, he, ModeHistory]
            have hw := (whole_word_recognition (w ++ [x])).mp (hscan.symm.trans he)
            obtain ⟨n, hn, hw⟩ := hw
            exact ⟨n, hn, by simp [hops, reads, List.map_append, ← hw]⟩
          | block c p =>
            simp only [nextMode, he, ModeHistory]
            refine ⟨w ++ [x], by simp [hops, reads, List.map_append], ?_⟩
            exact he.symm.trans hscan
          | suffix p =>
            simp only [nextMode, he, ModeHistory]
            refine ⟨w ++ [x], by simp [hops, reads, List.map_append], ?_⟩
            exact he.symm.trans hscan

private theorem run_mode_history (ops : List Operation) (z : Runtime)
    (hz : runtimeRun ops = some z) : ModeHistory z ops := by
  induction ops using List.reverseRecOn generalizing z with
  | nil => simp [runtimeRun, runtimeExecute] at hz; subst z; exact ⟨[],rfl,rfl⟩
  | append_singleton ops op ih =>
    rw [runtimeRun, runtime_append] at hz
    cases hp : runtimeRun ops with
    | none => simp [runtimeRun] at hp; rw [hp] at hz; contradiction
    | some d =>
      change runtimeExecute runtimeInitial ops = some d at hp
      rw [hp] at hz
      simp only [Option.bind_some, runtimeExecute, Option.bind_some,
        Option.bind_fun_some] at hz
      exact mode_history_step d z ops op (ih d hp) hz

/-- G and Gbeta are reached only by the two selected whole paid-word classes. -/
theorem exhaustive_history_modes (ops : List Operation) (z : Runtime)
    (hz : runtimeRun ops = some z) :
    (z.mode = .g → ∃ n, 375 ≤ n ∧ ops = reads (blocks n ++ latchWord)) ∧
    (z.mode = .gBeta → ∃ n, 375 ≤ n ∧ ops = reads (blocks n ++ latchWord ++ [1])) ∧
    ((¬∃ n, 375 ≤ n ∧ ops = reads (blocks n ++ latchWord)) →
      (¬∃ n, 375 ≤ n ∧ ops = reads (blocks n ++ latchWord ++ [1])) →
      queryMode z = .ordinary) := by
  have hh := run_mode_history ops z hz
  refine ⟨?_,?_,?_⟩
  · intro hm; simpa [ModeHistory, hm] using hh
  · intro hm; simpa [ModeHistory, hm] using hh
  · intro hng hnb
    have hg : z.mode ≠ .g := by intro hm; exact hng (by simpa [ModeHistory, hm] using hh)
    have hb : z.mode ≠ .gBeta := by intro hm; exact hnb (by simpa [ModeHistory, hm] using hh)
    exact (query_mode_classification z).2.2.mpr ⟨fun h => hg h.2, fun h => hb h.2⟩

private theorem ordinary_execution (z d : Runtime) (ops : List Operation)
    (hm : z.mode = .ordinary) (h : runtimeExecute z ops = some d) : d.mode = .ordinary := by
  induction ops generalizing z with
  | nil => simp only [runtimeExecute, Option.some.injEq] at h; subst d; exact hm
  | cons op ops ih =>
    cases hs : runtimeStep z op with
    | none => simp [runtimeExecute, hs] at h
    | some q =>
      have hq : q.mode = .ordinary := by
        unfold runtimeStep at hs
        cases hf : finiteStep z.fields op with
        | none => simp [hf] at hs
        | some f =>
          simp only [hf, Option.bind_some, Option.map_some, Option.some.injEq] at hs
          subst q
          simp [nextMode, hm]
      exact ih q hq (by simpa only [runtimeExecute, hs, Option.bind_some] using h)

/-- The original Gbeta alpha return disables the monitor for every subsequent legal suffix. -/
theorem special_return_permanence (r : Registers) (mon : Monitor) (ops : List Operation)
    (d : Runtime) (h : runtimeExecute ⟨⟨.fourth (.active .beta),r⟩,mon,.gBeta⟩
      (.read 0 :: ops) = some d) : d.mode = .ordinary := by
  have hs := (special_transactions r mon).2.2.1
  have he : runtimeExecute ⟨⟨.fourth (.active .p),r⟩,scan mon 0,.ordinary⟩ ops = some d := by
    simpa only [runtimeExecute, hs, Option.bind_some] using h
  exact ordinary_execution _ d ops rfl he

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
