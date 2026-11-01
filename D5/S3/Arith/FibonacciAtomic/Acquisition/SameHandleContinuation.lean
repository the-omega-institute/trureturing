/- GID: D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation
   mirror-E: none(waiver:unbounded-symbolic-construction)
   anchors: []
   utility: none
   digest: Earned acquisition installs a serial same-binding continuation protocol. -/

import D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution

/-! Actual bound-service acquisition and serial continued arithmetic use. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation

open TerminalGcdAcquisitionCost (step runWord quantity terminalGcd residueSource costBound)
open ContinuousAcquisitionTransport (Controller Instruction Event Run paidReads)

/-- Semantic laws of the supplied bound arithmetic service. The projection
`value` is for specification only, never an input of the local controller.
Rights, backing and successful service completion are supplied separately.
Every operation below addresses the very handle passed to it. -/
structure SourceService (Handle World : Type) where
  value : Handle → World → ℕ × ℕ
  lawful : Handle → World → Prop
  action : Handle → Bool → World → World → Prop
  read : Handle → ℕ → World → ℕ → World → Prop
  action_effect : ∀ h b x y, lawful h x → action h b x y →
    value h y = step b (value h x) ∧ lawful h y
  read_effect : ∀ h H x g y, lawful h x → read h H x g y →
    value h y = value h x ∧ g = Nat.gcd (quantity (value h x)) H ∧ lawful h y

/-- Completion under retained authority and adequate provision. This is a
service/material premise, not a consequence of finite code or residue size.
Only the actual fixed public modulus is required to be readable. World may
include changing finite allocations; no fixed capacity is asserted. -/
structure Completion {Handle World : Type}
    (B : SourceService Handle World) (h : Handle) (H : ℕ) : Prop where
  action : ∀ b x, B.lawful h x → ∃ y, B.action h b x y
  read : ∀ x, B.lawful h x → ∃ g y, B.read h H x g y

/-- External service-work tariffs. They are not controller observations. -/
structure Tariffs where
  read : (ℕ × ℕ) → ℕ
  replacement : (ℕ × ℕ) → ℕ
  graft : (ℕ × ℕ) → ℕ

/-- The same-run sum at actual pre-call arithmetic states, including closing. -/
def serviceBill (p : Tariffs) : List Event → (ℕ × ℕ) → ℕ
  | [], _ => 0
  | .compute :: es, v => serviceBill p es v
  | .action b :: es, v =>
      (if b then p.replacement v else p.graft v) + serviceBill p es (step b v)
  | .reply _ :: es, v => p.read v + serviceBill p es v

/-- Actual service execution with one fixed bound handle. The work index is
external to code. Only a paid reply can enter a read continuation. Completed
actions have a fixed acknowledgement and cannot change the bound handle. -/
inductive ServiceRun {Handle World : Type} {S L : Type*} (B : SourceService Handle World)
    (h : Handle) (p : Tariffs) (P : Controller S L) (H : ℕ) :
    S → World → List Event → S → World → L → ℕ → Prop where
  | halt {s x l} : P.code s = .halt l → ServiceRun B h p P H s x [] s x l 0
  | compute {s s' x es t y l n} : P.code s = .compute s' →
      ServiceRun B h p P H s' x es t y l n →
      ServiceRun B h p P H s x (.compute :: es) t y l n
  | action {s s' x x' b es t y l n} : P.code s = .action b s' →
      B.action h b x x' → ServiceRun B h p P H s' x' es t y l n →
      ServiceRun B h p P H s x (.action b :: es) t y l
        ((if b then p.replacement (B.value h x) else p.graft (B.value h x)) + n)
  | read {s k x x' g es t y l n} : P.code s = .read k →
      B.read h H x g x' → ServiceRun B h p P H (k g) x' es t y l n →
      ServiceRun B h p P H s x (.reply g :: es) t y l (p.read (B.value h x) + n)

private theorem lift_run {Handle World : Type} {S L : Type*} (B : SourceService Handle World)
    (h : Handle) {H : ℕ} (complete : Completion B h H) (p : Tariffs) {P : Controller S L}
    {s t : S} {v u : ℕ × ℕ} {es : List Event} {l : L}
    (hr : Run P H s v es t u l) :
    ∀ x, B.lawful h x → B.value h x = v →
      ∃ y, ServiceRun B h p P H s x es t y l (serviceBill p es v) ∧
        B.value h y = u ∧ B.lawful h y := by
  induction hr with
  | halt hs =>
    intro x hx hv
    exact ⟨x, .halt hs, hv, hx⟩
  | compute hs hr ih =>
    intro x hx hv
    obtain ⟨y, hy, hu, hl⟩ := ih x hx hv
    exact ⟨y, .compute hs hy, hu, hl⟩
  | @action s s' v b es t u l hs hr ih =>
    intro x hx hv
    obtain ⟨x', ha⟩ := complete.action b x hx
    have he := B.action_effect h b x x' hx ha
    obtain ⟨y, hy, hu, hl⟩ := ih x' he.2 (he.1.trans (congrArg (step b) hv))
    refine ⟨y, ?_, hu, hl⟩
    simpa only [serviceBill, hv] using ServiceRun.action hs ha hy
  | @read s k v es t u l hs hr ih =>
    intro x hx hv
    obtain ⟨g, x', ha⟩ := complete.read x hx
    obtain ⟨he, hg, hl⟩ := B.read_effect h H x g x' hx ha
    have hg' : g = Nat.gcd (quantity v) H := by simpa only [hv] using hg
    obtain ⟨y, hy, hu, hl'⟩ := ih x' hl (he.trans hv)
    refine ⟨y, ?_, hu, hl'⟩
    rw [hg'] at ha
    simpa only [serviceBill, hv] using ServiceRun.read hs ha hy

/-- All successful backend choices follow the same source-blind run, with
its exact tape, result, arithmetic endpoint and pre-call tariff sum. -/
private theorem service_agrees {Handle World : Type} {S L : Type*}
    (B : SourceService Handle World) (h : Handle) (p : Tariffs)
    {P : Controller S L} {H : ℕ} {s t : S} {v u : ℕ × ℕ}
    {es : List Event} {l : L} (hr : Run P H s v es t u l) :
    ∀ x, B.lawful h x → B.value h x = v →
      ∀ {rs t' y l' n}, ServiceRun B h p P H s x rs t' y l' n →
        rs = es ∧ t' = t ∧ B.value h y = u ∧ l' = l ∧
          n = serviceBill p es v ∧ B.lawful h y := by
  induction hr with
  | halt hs =>
    intro x hx hv rs t' y l' n actual
    cases actual with
    | halt ht =>
      cases Instruction.halt.inj (hs.symm.trans ht)
      exact ⟨rfl, rfl, hv, rfl, rfl, hx⟩
    | compute ht _ => cases hs.symm.trans ht
    | action ht _ _ => cases hs.symm.trans ht
    | read ht _ _ => cases hs.symm.trans ht
  | compute hs _ ih =>
    intro x hx hv rs t' y l' n actual
    cases actual with
    | halt ht => cases hs.symm.trans ht
    | compute ht tail =>
      cases Instruction.compute.inj (hs.symm.trans ht)
      obtain ⟨rfl, rfl, hu, rfl, hn, hl⟩ := ih x hx hv tail
      exact ⟨rfl, rfl, hu, rfl, hn, hl⟩
    | action ht _ _ => cases hs.symm.trans ht
    | read ht _ _ => cases hs.symm.trans ht
  | @action s s' v b es t u l hs _ ih =>
    intro x hx hv rs t' y l' n actual
    cases actual with
    | halt ht => cases hs.symm.trans ht
    | compute ht _ => cases hs.symm.trans ht
    | action ht ha tail =>
      obtain ⟨rfl, rfl⟩ := Instruction.action.inj (hs.symm.trans ht)
      have he := B.action_effect _ _ _ _ hx ha
      obtain ⟨rfl, rfl, hu, rfl, hn, hl⟩ :=
        ih _ he.2 (he.1.trans (congrArg (step b) hv)) tail
      refine ⟨rfl, rfl, hu, rfl, ?_, hl⟩
      simp only [serviceBill, hv, hn]
    | read ht _ _ => cases hs.symm.trans ht
  | @read s k v es t u l hs _ ih =>
    intro x hx hv rs t' y l' n actual
    cases actual with
    | halt ht => cases hs.symm.trans ht
    | compute ht _ => cases hs.symm.trans ht
    | action ht _ _ => cases hs.symm.trans ht
    | @read _ k' _ x' g _ _ _ _ _ ht ha tail =>
      cases Instruction.read.inj (hs.symm.trans ht)
      obtain ⟨he, hg, hl⟩ := B.read_effect _ _ _ _ _ hx ha
      rw [hv] at hg
      subst g
      obtain ⟨rfl, rfl, hu, rfl, hn, hl'⟩ := ih x' hl (he.trans hv) tail
      refine ⟨rfl, rfl, hu, rfl, ?_, hl'⟩
      simp only [serviceBill, hv, hn]

private theorem empty_service {Handle World : Type} {S L : Type*} {B : SourceService Handle World}
    {h : Handle} {p : Tariffs} {P : Controller S L} {H : ℕ}
    {s t : S} {x y : World} {l : L} {n : ℕ}
    (hr : ServiceRun B h p P H s x [] t y l n) : y = x := by
  cases hr
  rfl

/-- The local update is the supplied original-alpha residue action. -/
def update (H : ℕ) (b : Bool) (c : ZMod H × ZMod H) : ZMod H × ZMod H :=
  if b then GraftAffineClosure.step c else c + (1, 0)

/-- Source-free scratch evaluation of the caller's finite chronological word.
The complement translates the two suppliers' opposite Boolean conventions. -/
def scratch (H : ℕ) (c : ZMod H × ZMod H) (w : List Bool) : ZMod H × ZMod H :=
  GraftAffineClosure.run (1, 0) (w.map Bool.not) c

def predict (H : ℕ) (c : ZMod H × ZMod H) (w : List Bool) : ℕ :=
  GraftAffineClosure.residueReadout H (scratch H c w)

private theorem arithmetic (H : ℕ) (hH : 1 ≤ H) :
    GraftAffineClosure.Autonomous H (1, 0) (GraftAffineClosure.residue H)
      GraftAffineClosure.step (fun c => c + GraftAffineClosure.residue H (1, 0))
      (GraftAffineClosure.residueReadout H) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ha, _⟩ :=
    GraftAffineClosure.result.2 H (by omega) (1, 0)
  exact ha

private theorem update_sound (H : ℕ) (hH : 1 ≤ H) (b : Bool) (v : ℕ × ℕ) :
    update H b (residueSource H v) = residueSource H (step b v) := by
  have ha := arithmetic H hH
  cases b
  · change GraftAffineClosure.residue H v + (1, 0) =
      GraftAffineClosure.residue H (v + (1, 0))
    simpa only [GraftAffineClosure.residue, Nat.cast_one, Nat.cast_zero]
      using (ha.2.1 v).symm
  · exact (ha.1 v).symm

private theorem scratch_cons (H : ℕ) (c : ZMod H × ZMod H) (b : Bool) (w : List Bool) :
    scratch H c (b :: w) = scratch H (update H b c) w := by
  cases b <;> rfl

theorem scratch_sound (H : ℕ) (w : List Bool) (v : ℕ × ℕ) :
    scratch H (residueSource H v) w = residueSource H (runWord w v) := by
  exact (PositiveClosingExecution.residue_run H w v).symm

theorem predict_sound (H : ℕ) (hH : 1 ≤ H) (w : List Bool) (v : ℕ × ℕ) :
    predict H (residueSource H v) w = terminalGcd H w v := by
  unfold predict
  rw [scratch_sound]
  exact (arithmetic H hH).2.2 (runWord w v)

/-- Only ready states expose the callable reader and predictor. -/
inductive Phase where
  | ready
  | requested : Bool → Phase
  | completed : Bool → Phase
  | acknowledged : Bool → Phase
  deriving DecidableEq

structure Memory (H : ℕ) where
  entry : ZMod H × ZMod H
  current : ZMod H × ZMod H
  phase : Phase

structure Frame (World : Type) (H : ℕ) where
  world : World
  memory : Memory H

/-- All acknowledgements are the same event, with no numeric payload. -/
inductive Signal where
  | request : Bool → Signal
  | complete
  | acknowledge
  | commit
  deriving DecidableEq

/-- Local request, actual service completion, fixed acknowledgement and local
commit are distinct steps. There is no source allocation, rebind or read rule. -/
inductive MicroStep {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (H : ℕ) : Frame World H → Signal → Frame World H → Prop where
  | request (x e c b) :
      MicroStep B h H ⟨x, e, c, .ready⟩ (.request b) ⟨x, e, c, .requested b⟩
  | complete {x y e c b} : B.action h b x y →
      MicroStep B h H ⟨x, e, c, .requested b⟩ .complete ⟨y, e, c, .completed b⟩
  | acknowledge (x e c b) :
      MicroStep B h H ⟨x, e, c, .completed b⟩ .acknowledge ⟨x, e, c, .acknowledged b⟩
  | commit (x e c b) :
      MicroStep B h H ⟨x, e, c, .acknowledged b⟩ .commit ⟨x, e, update H b c, .ready⟩

inductive ProtocolRun {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (H : ℕ) : Frame World H → List Signal → Frame World H → Prop where
  | nil (f) : ProtocolRun B h H f [] f
  | cons {f g k a es} : MicroStep B h H f a g → ProtocolRun B h H g es k →
      ProtocolRun B h H f (a :: es) k

def continuationEvents (w : List Bool) : List Signal :=
  w.flatMap (fun b => [.request b, .complete, .acknowledge, .commit])

/-- The local current is synchronized at callable cuts. Between completion
and commit its pending update, rather than its old value, matches the source. -/
def Aligned {Handle World : Type} (B : SourceService Handle World) (h : Handle)
    (H : ℕ) (f : Frame World H) : Prop :=
  B.lawful h f.world ∧
  match f.memory.phase with
  | .ready | .requested _ => f.memory.current = residueSource H (B.value h f.world)
  | .completed b | .acknowledged b =>
      update H b f.memory.current = residueSource H (B.value h f.world)

private theorem micro_invariant {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (H : ℕ) (hH : 1 ≤ H) {f g : Frame World H} {a : Signal}
    (hs : MicroStep B h H f a g) (hf : Aligned B h H f) :
    Aligned B h H g ∧ g.memory.entry = f.memory.entry := by
  cases hs with
  | request x e c b => exact ⟨hf, rfl⟩
  | @complete x y e c b ha =>
    obtain ⟨hv, hy⟩ := B.action_effect h b x y hf.1 ha
    refine ⟨⟨hy, ?_⟩, rfl⟩
    change update H b c = residueSource H (B.value h y)
    rw [hv, ← update_sound H hH, ← hf.2]
  | acknowledge x e c b => exact ⟨hf, rfl⟩
  | commit x e c b => exact ⟨hf, rfl⟩

private theorem protocol_invariant {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (H : ℕ) (hH : 1 ≤ H) {f g : Frame World H} {es : List Signal}
    (hr : ProtocolRun B h H f es g) (hf : Aligned B h H f) :
    Aligned B h H g ∧ g.memory.entry = f.memory.entry := by
  induction hr with
  | nil f => exact ⟨hf, rfl⟩
  | cons hs hr ih =>
    have hi := micro_invariant B h H hH hs hf
    have ht := ih hi.1
    exact ⟨ht.1, ht.2.trans hi.2⟩

theorem continuation_exists {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (H : ℕ) (complete : Completion B h H) (w : List Bool)
    (x : World) (e c : ZMod H × ZMod H) (hx : B.lawful h x) :
    ∃ y, ProtocolRun B h H ⟨x, e, c, .ready⟩ (continuationEvents w)
        ⟨y, e, scratch H c w, .ready⟩ ∧
      B.value h y = runWord w (B.value h x) ∧ B.lawful h y := by
  induction w generalizing x c with
  | nil => exact ⟨x, .nil _, rfl, hx⟩
  | cons b w ih =>
    obtain ⟨x', ha⟩ := complete.action b x hx
    obtain ⟨hv, hl⟩ := B.action_effect h b x x' hx ha
    obtain ⟨y, hr, hy, hl'⟩ := ih x' (update H b c) hl
    refine ⟨y, ?_, ?_, hl'⟩
    · rw [scratch_cons]
      exact .cons (.request x e c b)
        (.cons (.complete ha) (.cons (.acknowledge x' e c b) (.cons (.commit x' e c b) hr)))
    · simpa only [runWord, hv] using hy

private theorem continuation_endpoint {Handle World : Type}
    (B : SourceService Handle World) (h : Handle) (H : ℕ) (w : List Bool)
    (x : World) (e c : ZMod H × ZMod H) {f : Frame World H}
    (hr : ProtocolRun B h H ⟨x, e, c, .ready⟩ (continuationEvents w) f)
    (hx : B.lawful h x) :
    f.memory = ⟨e, scratch H c w, .ready⟩ ∧
      B.value h f.world = runWord w (B.value h x) ∧ B.lawful h f.world := by
  induction w generalizing x c with
  | nil =>
    cases hr
    exact ⟨rfl, rfl, hx⟩
  | cons b w ih =>
    cases hr with
    | cons request tail =>
      cases request
      cases tail with
      | cons completed tail =>
        cases completed with
        | complete ha =>
          cases tail with
          | cons acknowledged tail =>
            cases acknowledged
            cases tail with
            | cons committed tail =>
              cases committed
              have he := B.action_effect _ _ _ _ hx ha
              have ht := ih _ _ tail he.2
              refine ⟨?_, ?_, ht.2.2⟩
              · simpa only [scratch_cons] using ht.1
              · simpa only [runWord, he.1] using ht.2.1

/-- The complete installed continuation interface, including all actual
prefixes, all reachable callable cuts and every finite future word. -/
def Continued {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (H : ℕ) (v : ℕ × ℕ) (e : ZMod H × ZMod H) (y : World) : Prop :=
  let start : Frame World H := ⟨y, e, e, .ready⟩
  Aligned B h H start ∧
  (∀ signals f, ProtocolRun B h H start signals f →
    f.memory.entry = e ∧ Aligned B h H f ∧
    (f.memory.phase = .ready →
      f.memory.current = residueSource H (B.value h f.world) ∧
      (∀ W, predict H f.memory.current W = terminalGcd H W (B.value h f.world)) ∧
      ∀ V, ∃ z, ProtocolRun B h H f (continuationEvents V)
          ⟨z, e, scratch H f.memory.current V, .ready⟩ ∧
        B.value h z = runWord V (B.value h f.world) ∧
        scratch H f.memory.current V = residueSource H (B.value h z) ∧
        ∀ W, predict H (scratch H f.memory.current V) W =
          terminalGcd H (V ++ W) (B.value h f.world))) ∧
  (∀ V, ∃ z, ProtocolRun B h H start (continuationEvents V)
      ⟨z, e, scratch H e V, .ready⟩ ∧
    B.value h z = runWord V (B.value h y) ∧
    scratch H e V = residueSource H (B.value h z) ∧
    ∀ W, predict H (scratch H e V) W = terminalGcd H (V ++ W) v) ∧
  (∀ V f, ProtocolRun B h H start (continuationEvents V) f →
    f.memory.phase = .ready ∧ f.memory.current = scratch H e V ∧
    B.value h f.world = runWord V (B.value h y) ∧
    ∀ W, predict H f.memory.current W = terminalGcd H (V ++ W) v) ∧
  (∀ W, predict H e W = terminalGcd H W (B.value h y) ∧
    terminalGcd H W (B.value h y) = terminalGcd H W v)

private theorem continued_return {Handle World : Type} (H : ℕ) (hH : 1 ≤ H)
    (B : SourceService Handle World) (h : Handle) (complete : Completion B h H)
    (v : ℕ × ℕ) (y : World) (hl : B.lawful h y)
    (he : residueSource H (B.value h y) = residueSource H v) :
    Continued B h H v (residueSource H v) y := by
  dsimp only [Continued]
  have aligned : Aligned B h H
      (⟨y, residueSource H v, residueSource H v, .ready⟩ : Frame World H) :=
    ⟨hl, he.symm⟩
  refine ⟨aligned, ?_, ?_, ?_, ?_⟩
  · intro signals f run
    have hi := protocol_invariant B h H hH run aligned
    refine ⟨hi.2, hi.1, ?_⟩
    intro hf
    have hc : f.memory.current = residueSource H (B.value h f.world) := by
      have hc := hi.1.2
      simpa only [hf] using hc
    refine ⟨hc, fun W => hc ▸ predict_sound H hH W (B.value h f.world), ?_⟩
    intro V
    obtain ⟨z, hz, hvz, hlz⟩ := continuation_exists B h H complete V f.world
      f.memory.entry f.memory.current hi.1.1
    have hfeta : (⟨f.world, f.memory.entry, f.memory.current, .ready⟩ : Frame World H) = f := by
      cases f with
      | mk world memory =>
        cases memory with
        | mk entry current phase => cases hf; rfl
    rw [hfeta, hi.2] at hz
    have hcz : scratch H f.memory.current V = residueSource H (B.value h z) := by
      rw [hc, scratch_sound, hvz]
    refine ⟨z, hz, hvz, hcz, ?_⟩
    intro W
    rw [hc, scratch_sound, predict_sound H hH]
    unfold terminalGcd
    rw [SourceCoordinates.PositiveProbeCompiler.run_append]
  · intro V
    obtain ⟨z, hz, hvz, hlz⟩ := continuation_exists B h H complete V y
      (residueSource H v) (residueSource H v) hl
    have hi := protocol_invariant B h H hH hz aligned
    have hc : scratch H (residueSource H v) V = residueSource H (B.value h z) := hi.1.2
    refine ⟨z, hz, hvz, hc, ?_⟩
    intro W
    rw [scratch_sound, predict_sound H hH]
    unfold terminalGcd
    rw [SourceCoordinates.PositiveProbeCompiler.run_append]
  · intro V f run
    have ht := continuation_endpoint B h H V y (residueSource H v) (residueSource H v) run hl
    have phase := congrArg Memory.phase ht.1
    have current := congrArg Memory.current ht.1
    refine ⟨phase, current, ht.2.1, ?_⟩
    intro W
    rw [current, scratch_sound, predict_sound H hH]
    unfold terminalGcd
    rw [SourceCoordinates.PositiveProbeCompiler.run_append]
  · intro W
    have hp := predict_sound H hH W (B.value h y)
    rw [he] at hp
    exact ⟨hp, hp.symm.trans (predict_sound H hH W v)⟩


/-- Full same-binding return, earned labels, every intermediate protocol cut,
all finite continuations, every admitted completed backend outcome and the read
optimum for the unrestricted continuous competitor class. Completion and lawful authority remain supplied premises.
The external bill is exact; no polynomial local-work/space bound is asserted. -/
theorem same_handle_return {Handle World : Type} (H : ℕ) (hH : 1 ≤ H)
    (B : SourceService Handle World) (h : Handle) (complete : Completion B h H)
    (p : Tariffs) (x : World) (hx : B.lawful h x) :
    let v := B.value h x
    let w := PositiveClosingExecution.executionWord H v
    let es := PositiveClosingExecution.executionEvents H v
    let e := residueSource H v
    ∃ t y,
      ServiceRun B h p (PositiveClosingExecution.controller H) H
        (PositiveClosingExecution.controller H).initial x es t y e (serviceBill p es v) ∧
      B.value h y = runWord w v ∧ B.lawful h y ∧
      paidReads es = (if H = 1 then 0 else 2 * costBound H) ∧
      (H = 1 → y = x) ∧
      (∀ (S : Type*) (P : Controller S (ZMod H × ZMod H)) (J : ℕ),
        (∀ z : ℕ × ℕ, ∃ rs s u,
          Run P H P.initial z rs s u (residueSource H z) ∧ paidReads rs ≤ J) →
        paidReads es ≤ J) ∧
      Continued B h H v e y ∧
      (∀ rs t' y' l' n',
        ServiceRun B h p (PositiveClosingExecution.controller H) H
          (PositiveClosingExecution.controller H).initial x rs t' y' l' n' →
        rs = es ∧ t' = t ∧ l' = e ∧
        B.value h y' = runWord w v ∧ B.lawful h y' ∧
        n' = serviceBill p es v ∧ (H = 1 → y' = x) ∧ Continued B h H v e y') := by
  dsimp only
  let v := B.value h x
  have hd := PositiveClosingExecution.positive_execution H hH v
  obtain ⟨t, hr⟩ := hd.1
  obtain ⟨y, hy, hv, hl⟩ := lift_run B h complete p hr x hx rfl
  have he : residueSource H (B.value h y) = residueSource H v := hv ▸ hd.2.2.1
  have reads := hd.2.2.2.2.2.2.2.2.1
  refine ⟨t, y, hy, hv, hl, reads, ?_, ?_,
    continued_return H hH B h complete v y hl he, ?_⟩
  · intro h1
    have hes := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h1).2
    rw [hes] at hy
    exact empty_service hy
  · intro S P J successful
    rw [reads]
    exact ContinuousAcquisitionTransport.continuous_acquisition_lower_bound H hH P J successful
  · intro rs t' y' l' n' actual
    obtain ⟨hes, ht, hu, he', hn, hl'⟩ := service_agrees B h p hr x hx rfl actual
    refine ⟨hes, ht, he', hu, hl', hn, ?_,
      continued_return H hH B h complete v y' hl' (hu ▸ hd.2.2.1)⟩
    intro h1
    have hempty := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h1).2
    rw [hes, hempty] at actual
    exact empty_service actual

#print axioms same_handle_return

end D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
