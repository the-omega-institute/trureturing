/- GID: D5/S3/Arith/FibonacciAtomic/Acquisition/OnlineCommonOriginalArchive
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Acquisition/OnlineCommonOriginalArchive
   mirror-E: none(waiver:unbounded-symbolic-construction)
   anchors: []
   utility: none
   digest: Adaptive precision upgrades retain one earned common-original arithmetic archive. -/

import D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
import Mathlib.Data.Nat.Log

/-! Actual varying-modulus acquisition preserves one common-original archive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive

open TerminalGcdAcquisitionCost (step runWord quantity terminalGcd residueSource costBound)
open ContinuousAcquisitionTransport (Controller Instruction Event Run paidReads)
open SameHandleContinuation

/-- Public prime axes of the finite envelope. -/
def primes (b : ℕ) : Finset ℕ := (Finset.range (b + 2)).filter Nat.Prime

/-- The exact finite prime-power envelope, also at budget zero. -/
def envelope (b : ℕ) : ℕ := ∏ p ∈ primes b, p ^ (b / (p - 1))

private theorem envelope_pos (b : ℕ) : 0 < envelope b := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Finset.mem_filter.mp hp).2.pos _

private theorem envelope_factorization (b p : ℕ) :
    (envelope b).factorization p = if p ∈ primes b then b / (p - 1) else 0 := by
  rw [envelope, Nat.factorization_prod_apply (fun q hq =>
    pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero)]
  have terms (q : ℕ) (hq : q ∈ primes b) :
      (q ^ (b / (q - 1))).factorization p = if q = p then b / (p - 1) else 0 := by
    rw [(Finset.mem_filter.mp hq).2.factorization_pow]
    by_cases he : q = p
    · subst q
      simp
    · simp [he]
  simp_rw [Finset.sum_congr rfl terms]
  simp

private theorem cost_le (H b : ℕ) :
    costBound H ≤ b ↔ ∀ p, H.factorization p * (p - 1) ≤ b := by
  constructor
  · intro h p
    by_cases hp : p ∈ H.primeFactors
    · exact (Finset.le_sup (f := fun q => H.factorization q * (q - 1)) hp).trans h
    · have hz : H.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
      simp [hz]
  · intro h
    exact Finset.sup_le (fun p _ => h p)

private theorem envelope_covers (H b : ℕ) (hH : 0 < H) :
    H ∣ envelope b ↔ costBound H ≤ b := by
  rw [← Nat.factorization_prime_le_iff_dvd hH.ne' (envelope_pos b).ne', cost_le]
  constructor
  · intro h p
    by_cases hp : p.Prime
    · have hp2 := hp.two_le
      have he := h p hp
      rw [envelope_factorization] at he
      split_ifs at he with hm
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < p - 1)).mp he
      · simp only [Nat.le_zero] at he
        simp [he]
    · simp [Nat.factorization_eq_zero_of_not_prime H hp]
  · intro h p hp
    have hp2 := hp.two_le
    rw [envelope_factorization]
    by_cases hm : p ∈ primes b
    · rw [ite_eq_left hm]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < p - 1)).mpr (h p)
    · rw [ite_eq_right hm]
      have hsmall : b < p - 1 := by
        have : ¬p < b + 2 := by simpa [primes, hp] using hm
        omega
      have hh := h p
      by_contra hn
      have : 1 ≤ H.factorization p := by omega
      have := Nat.mul_le_mul_right (p - 1) this
      omega

private theorem envelope_cost (b : ℕ) : costBound (envelope b) = b := by
  have upper := (envelope_covers (envelope b) b (envelope_pos b)).mp (dvd_refl _)
  apply le_antisymm upper
  have lower := (cost_le (envelope b) (costBound (envelope b))).mp le_rfl 2
  have hf : (envelope b).factorization 2 = b := by
    rw [envelope_factorization]
    by_cases hb : b = 0
    · simp [hb]
    · have : 2 ∈ primes b := by simp [primes, Nat.prime_two]; omega
      simp [this]
  simpa [hf] using lower

private theorem envelope_mono {b c : ℕ} (h : b ≤ c) : envelope b ∣ envelope c :=
  (envelope_covers _ _ (envelope_pos b)).mpr ((envelope_cost b).le.trans h)

private theorem envelope_zero : envelope 0 = 1 := by simp [envelope]

/-- Integer ceiling logarithm computes the least covering dyadic budget. -/
def budget (m : ℕ) : ℕ := if m = 0 then 0 else 2 ^ Nat.clog 2 m

private theorem budget_spec {m : ℕ} (hm : 0 < m) :
    m ≤ budget m ∧ budget m < 2 * m ∧
    ∀ k, m ≤ 2 ^ k → budget m ≤ 2 ^ k := by
  rw [budget, ite_eq_right hm.ne']
  refine ⟨Nat.le_pow_clog (by decide) m, ?_, ?_⟩
  · by_cases h1 : m = 1
    · simp [h1]
    · have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < m)
      have hc := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < m)
      have he : Nat.clog 2 m = (Nat.clog 2 m).pred + 1 :=
        (Nat.succ_pred_eq_of_pos hc).symm
      rw [he, pow_succ]
      omega
  · intro k hk
    exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow hk)

private theorem budget_mono {m n : ℕ} (h : m ≤ n) : budget m ≤ budget n := by
  by_cases hm : m = 0
  · simp [budget, hm]
  · have hn : n ≠ 0 := by omega
    simp only [budget, ite_eq_right hm, ite_eq_right hn]
    exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

private theorem cost_lcm {H K : ℕ} (hH : 0 < H) (hK : 0 < K) :
    costBound (Nat.lcm H K) = max (costBound H) (costBound K) := by
  apply le_antisymm
  · apply (cost_le _ _).mpr
    intro p
    rw [Nat.factorization_lcm hH.ne' hK.ne']
    change max (H.factorization p) (K.factorization p) * (p - 1) ≤ _
    rw [← max_mul_mul_right]
    exact max_le_max ((cost_le H _).mp le_rfl p) ((cost_le K _).mp le_rfl p)
  · apply max_le
    · apply (cost_le _ _).mpr
      intro p
      have h := (cost_le (Nat.lcm H K) _).mp le_rfl p
      rw [Nat.factorization_lcm hH.ne' hK.ne'] at h
      change max (H.factorization p) (K.factorization p) * (p - 1) ≤ _ at h
      exact (Nat.mul_le_mul_right (p - 1) (le_max_left _ _)).trans h
    · apply (cost_le _ _).mpr
      intro p
      have h := (cost_le (Nat.lcm H K) _).mp le_rfl p
      rw [Nat.factorization_lcm hH.ne' hK.ne'] at h
      change max (H.factorization p) (K.factorization p) * (p - 1) ≤ _ at h
      exact (Nat.mul_le_mul_right (p - 1) (le_max_right _ _)).trans h

/-- Local arithmetic inverse of a recorded original letter; never a source call. -/
def unupdate (H : ℕ) (b : Bool) (c : ZMod H × ZMod H) : ZMod H × ZMod H :=
  if b then (c.2 - c.1, c.1) else (c.1 - 1, c.2)

def rewind (H : ℕ) : List Bool → (ZMod H × ZMod H) → ZMod H × ZMod H
  | [], c => c
  | b :: w, c => unupdate H b (rewind H w c)

private theorem rewind_scratch (H : ℕ) (w : List Bool) (c : ZMod H × ZMod H) :
    rewind H w (scratch H c w) = c := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih =>
    have hc : scratch H c (b :: w) = scratch H (update H b c) w := by cases b <;> rfl
    rw [hc, rewind, ih]
    cases b <;> ext <;> simp [unupdate, update, GraftAffineClosure.step]

/-- A paid reply retains its chosen modulus; actions are completed calls with
their fixed acknowledgement. Only replies contain source-dependent data. -/
inductive TapeEvent where
  | compute
  | action : Bool → TapeEvent
  | reply : ℕ → ℕ → TapeEvent

def stamp (H : ℕ) : Event → TapeEvent
  | .compute => .compute
  | .action b => .action b
  | .reply g => .reply H g

def letters : List TapeEvent → List Bool
  | [] => []
  | .action b :: es => b :: letters es
  | _ :: es => letters es

def reads : List TapeEvent → ℕ
  | [] => 0
  | .reply _ _ :: es => reads es + 1
  | _ :: es => reads es

/-- An authentic cut is a prefix position in the actual retained tape. -/
def cutWord (tape : List TapeEvent) (t : ℕ) : List Bool := (letters tape).take t

def reduce (D E : ℕ) (h : D ∣ E) (c : ZMod E × ZMod E) : ZMod D × ZMod D :=
  ((ZMod.castHom h (ZMod D)) c.1, (ZMod.castHom h (ZMod D)) c.2)

private theorem reduce_source (D E : ℕ) (h : D ∣ E) (v : ℕ × ℕ) :
    reduce D E h (residueSource E v) = residueSource D v := by
  ext <;> simp [reduce, residueSource]

/-- The full variable-modulus source menu. No arithmetic source value is
passed to the program; these are successful-service and material premises. -/
def VariableCompletion {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) : Prop := ∀ H, 0 < H → Completion B h H

/-- The chronological record is generated by actual completed calls at this
one binding. Compute events denote charged local intervals, with no reply. -/
inductive TapeRun {Handle World : Type} (B : SourceService Handle World) (h : Handle) :
    World → List TapeEvent → World → Prop where
  | nil (x) : TapeRun B h x [] x
  | compute {x es y} : TapeRun B h x es y → TapeRun B h x (.compute :: es) y
  | action {x z es y b} : B.action h b x z → TapeRun B h z es y →
      TapeRun B h x (.action b :: es) y
  | read {x z es y H g} : B.read h H x g z → TapeRun B h z es y →
      TapeRun B h x (.reply H g :: es) y

private theorem tape_append {Handle World : Type} {B : SourceService Handle World}
    {h : Handle} {x y z : World} {es fs : List TapeEvent}
    (he : TapeRun B h x es y) (hf : TapeRun B h y fs z) :
    TapeRun B h x (es ++ fs) z := by
  induction he with
  | nil => exact hf
  | compute _ ih => exact .compute (ih hf)
  | action ha _ ih => exact .action ha (ih hf)
  | read ha _ ih => exact .read ha (ih hf)

private theorem tape_endpoint {Handle World : Type} {B : SourceService Handle World}
    {h : Handle} {x y : World} {es : List TapeEvent}
    (hr : TapeRun B h x es y) (hx : B.lawful h x) :
    B.value h y = runWord (letters es) (B.value h x) ∧ B.lawful h y := by
  revert hx
  induction hr with
  | nil => intro hx; exact ⟨rfl, hx⟩
  | compute _ ih => intro hx; exact ih hx
  | action ha _ ih =>
    intro hx
    have he := B.action_effect _ _ _ _ hx ha
    have ht := ih he.2
    exact ⟨by simpa only [letters, runWord, he.1] using ht.1, ht.2⟩
  | read ha _ ih =>
    intro hx
    have he := B.read_effect _ _ _ _ _ hx ha
    have ht := ih he.2.2
    exact ⟨by simpa only [letters, he.1] using ht.1, ht.2⟩

private theorem tape_cuts {Handle World : Type} {B : SourceService Handle World}
    {h : Handle} {x y : World} {es : List TapeEvent}
    (hr : TapeRun B h x es y) (hx : B.lawful h x) :
    ∀ t, t ≤ (letters es).length → ∃ z, B.lawful h z ∧
      B.value h z = runWord (cutWord es t) (B.value h x) := by
  revert hx
  induction hr with
  | nil =>
    intro hx t ht
    have : t = 0 := by simpa [letters] using ht
    subst t
    exact ⟨_, hx, rfl⟩
  | compute _ ih => intro hx; exact ih hx
  | @action x z es y b ha hr ih =>
    intro hx t ht
    cases t with
    | zero => exact ⟨x, hx, rfl⟩
    | succ t =>
      have he := B.action_effect _ _ _ _ hx ha
      obtain ⟨z', hl, hv⟩ := ih he.2 t (by simpa [letters] using ht)
      exact ⟨z', hl, by simpa [cutWord, letters, runWord, he.1] using hv⟩
  | read ha _ ih =>
    intro hx
    have he := B.read_effect _ _ _ _ _ hx ha
    intro t ht
    obtain ⟨z, hl, hv⟩ := ih he.2.2 t ht
    exact ⟨z, hl, by simpa [cutWord, letters, he.1] using hv⟩

private theorem service_tape {Handle World : Type} {S L : Type*}
    {B : SourceService Handle World} {h : Handle} {p : Tariffs}
    {P : Controller S L} {H : ℕ} {s t : S} {x y : World} {es : List Event} {l : L} {n : ℕ}
    (hr : ServiceRun B h p P H s x es t y l n) :
    TapeRun B h x (es.map (stamp H)) y := by
  induction hr with
  | halt => exact .nil _
  | compute hs hr ih => exact .compute ih
  | action hs ha hr ih => exact .action ha ih
  | read hs ha hr ih => exact .read ha ih

private theorem protocol_tape {Handle World : Type} {B : SourceService Handle World}
    {h : Handle} {H : ℕ} (w : List Bool) (x y : World) (e c : ZMod H × ZMod H)
    (hr : ProtocolRun B h H ⟨x, e, c, .ready⟩ (continuationEvents w)
      ⟨y, e, scratch H c w, .ready⟩) : TapeRun B h x (w.map TapeEvent.action) y := by
  induction w generalizing x c with
  | nil => cases hr; exact .nil _
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
              have hs : scratch H c (b :: w) = scratch H (update H b c) w := by cases b <;> rfl
              rw [hs] at tail
              exact .action ha (ih _ _ tail)

private theorem reads_append (es fs : List TapeEvent) : reads (es ++ fs) = reads es + reads fs := by
  induction es with
  | nil => simp [reads]
  | cons e es ih => cases e <;> simp [reads, ih, Nat.add_comm, Nat.add_left_comm]

private theorem reads_stamp (H : ℕ) (es : List Event) :
    reads (es.map (stamp H)) = paidReads es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [reads, paidReads, stamp, ih]

private theorem letters_actions (w : List Bool) : letters (w.map TapeEvent.action) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [letters, ih]

private theorem reads_actions (w : List Bool) : reads (w.map TapeEvent.action) = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [reads, ih]

/-- Accessible local memory. Original and current are separate registers;
the opaque binding is an external fixed parameter of every execution rule. -/
structure Memory where
  precision : ℕ
  joint : ℕ
  requests : List ℕ
  tape : List TapeEvent
  original : ZMod (envelope precision) × ZMod (envelope precision)
  current : ZMod (envelope precision) × ZMod (envelope precision)

def initial : Memory := ⟨0, 1, [], [], 0, 0⟩

def hit (a : Memory) (H : ℕ) : Memory :=
  { a with joint := Nat.lcm a.joint H, requests := a.requests ++ [H] }

/-- This commit consumes only the old record, the delivered public modulus,
the actual acquired tape and the earned reply-decoded stage-entry label. -/
def install (a : Memory) (H : ℕ) (es : List Event)
    (d : ZMod (envelope (budget (costBound H))) ×
      ZMod (envelope (budget (costBound H)))) : Memory :=
  { precision := budget (costBound H)
    joint := Nat.lcm a.joint H
    requests := a.requests ++ [H]
    tape := a.tape ++ es.map (stamp (envelope (budget (costBound H))))
    original := rewind _ (letters a.tape) d
    current := d }

def advanceMemory (a : Memory) (w : List Bool) : Memory :=
  { a with current := scratch _ a.current w, tape := a.tape ++ w.map TapeEvent.action }

/-- One delivered request runs the same fixed acquisition code on a miss.
Its current source is the actual input world. Nothing supplies a pre-earned
archive or an assumed acquisition certificate. -/
inductive RequestRun {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (p : Tariffs) (a : Memory) (H : ℕ) (x : World) : Memory → World → Prop where
  | covered : costBound H ≤ a.precision → RequestRun B h p a H x (hit a H) x
  | upgrade {es t y d n} : a.precision < costBound H →
      ServiceRun B h p (PositiveClosingExecution.controller (envelope (budget (costBound H))))
        (envelope (budget (costBound H)))
        (PositiveClosingExecution.controller (envelope (budget (costBound H)))).initial
        x es t y d n → RequestRun B h p a H x (install a H es d) y

/-- No read occurs in this source-synchronized continuation interface. -/
def ContinueRun {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (a : Memory) (w : List Bool) (x y : World) : Prop :=
  ProtocolRun B h (envelope a.precision) ⟨x, a.original, a.current, .ready⟩
    (continuationEvents w) ⟨y, a.original, scratch _ a.current w, .ready⟩

/-- Successive environment inputs are admitted only at completed cuts.
The environment may choose these from all information it has exposed so far. -/
inductive Input where
  | request : (H : ℕ) → 0 < H → Input
  | continuation : List Bool → Input

inductive OnlineRun {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (p : Tariffs) : Memory → World → List Input → Memory → World → Prop where
  | nil (a x) : OnlineRun B h p a x [] a x
  | request {a x H hH b y is c z} : RequestRun B h p a H x b y →
      OnlineRun B h p b y is c z → OnlineRun B h p a x (.request H hH :: is) c z
  | continuation {a x w y is b z} : ContinueRun B h a w x y →
      OnlineRun B h p (advanceMemory a w) y is b z →
      OnlineRun B h p a x (.continuation w :: is) b z

def joint (hs : List ℕ) : ℕ := hs.foldl Nat.lcm 1
def maximum (hs : List ℕ) : ℕ := (hs.map costBound).foldl max 0

/-- The invariant prices actual paid events and identifies both registers
with one original source. Its tape is an executed chronology, not an arbitrary
word asserted to have occurred. -/
structure Sound {Handle World : Type} (B : SourceService Handle World) (h : Handle)
    (x₀ : World) (a : Memory) (x : World) : Prop where
  tape : TapeRun B h x₀ a.tape x
  lawful : B.lawful h x
  positive : 0 < a.joint
  joint_eq : a.joint = joint a.requests
  maximum_eq : costBound a.joint = maximum a.requests
  precision_eq : a.precision = budget (costBound a.joint)
  original_eq : a.original = residueSource (envelope a.precision) (B.value h x₀)
  current_eq : a.current = residueSource (envelope a.precision) (B.value h x)
  covered : ∀ H ∈ a.requests, 0 < H ∧ H ∣ envelope a.precision
  payment : if costBound a.joint = 0 then reads a.tape = 0 else
    reads a.tape ≤ 4 * a.precision - 2 ∧ 4 * a.precision - 2 < 8 * costBound a.joint

private theorem budget_ge (m : ℕ) : m ≤ budget m := by
  by_cases hm : m = 0
  · simp [hm, budget]
  · exact (budget_spec (Nat.pos_of_ne_zero hm)).1

private theorem budget_covered (m k : ℕ) (hk : k ≤ budget m) :
    budget (max m k) = budget m := by
  apply le_antisymm _ (budget_mono (le_max_left _ _))
  by_cases hm : m = 0
  · simp [hm, budget] at hk ⊢
    simp [hk]
  · have hn : 0 < max m k := lt_of_lt_of_le (Nat.pos_of_ne_zero hm) (le_max_left _ _)
    have hb : max m k ≤ 2 ^ Nat.clog 2 m := by
      have := budget_ge m
      simp only [budget, ite_eq_right hm] at hk this
      exact max_le this hk
    simpa only [budget, ite_eq_right hm] using (budget_spec hn).2.2 (Nat.clog 2 m) hb

private theorem budget_jump {m k : ℕ} (hm : 0 < m) (hk : budget m < k) :
    2 * budget m ≤ budget k := by
  have hk0 : k ≠ 0 := by omega
  have hx : Nat.clog 2 m < Nat.clog 2 k :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simpa [budget, hm.ne'] using hk)
  simp only [budget, ite_eq_right hm.ne', ite_eq_right hk0]
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : Nat.clog 2 m + 1 ≤ Nat.clog 2 k)
  simpa [pow_succ, Nat.mul_comm] using hpow

private theorem initial_sound {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (x₀ : World) (hx : B.lawful h x₀) : Sound B h x₀ initial x₀ := by
  refine ⟨.nil _, hx, by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initial, costBound, maximum]
  · simp [initial, costBound, budget]
  · change (0 : ZMod (envelope 0) × ZMod (envelope 0)) =
      residueSource (envelope 0) (B.value h x₀)
    rw [envelope_zero]
    exact Subsingleton.elim _ _
  · change (0 : ZMod (envelope 0) × ZMod (envelope 0)) =
      residueSource (envelope 0) (B.value h x₀)
    rw [envelope_zero]
    exact Subsingleton.elim _ _
  · simp [initial]
  · simp [initial, costBound, reads]

private theorem acquisition_agrees {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (E : ℕ) (hE : 0 < E) (x : World) (hx : B.lawful h x)
    {es t y d n} (hr : ServiceRun B h p (PositiveClosingExecution.controller E) E
      (PositiveClosingExecution.controller E).initial x es t y d n) :
    d = residueSource E (B.value h x) ∧ B.lawful h y ∧
    residueSource E (B.value h y) = residueSource E (B.value h x) ∧
    paidReads es = (if E = 1 then 0 else 2 * costBound E) := by
  obtain ⟨t₀, y₀, hr₀, hv₀, hl₀, count, h1, lower, continued, all⟩ :=
    same_handle_return.{0} E (by omega) B h (complete E hE) p x hx
  obtain ⟨hes, ht, hd, hv, hl, hn, h1, hc⟩ := all es t y d n hr
  refine ⟨hd, hl, ?_, hes ▸ count⟩
  exact hc.1.2.symm

private theorem request_exists {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (a : Memory) (H : ℕ) (x : World) (hx : B.lawful h x) :
    ∃ b y, RequestRun B h p a H x b y := by
  by_cases hc : costBound H ≤ a.precision
  · exact ⟨_, _, .covered hc⟩
  · let E := envelope (budget (costBound H))
    obtain ⟨t, y, hr, rest⟩ := same_handle_return.{0} E
      (by have := envelope_pos (budget (costBound H)); omega)
      B h (complete E (envelope_pos _)) p x hx
    exact ⟨_, y, .upgrade (by omega) hr⟩

private theorem request_deterministic {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (a : Memory) (H : ℕ) (x : World) (hx : B.lawful h x)
    {b y c z} (first : RequestRun B h p a H x b y)
    (second : RequestRun B h p a H x c z) :
    b = c ∧ B.value h y = B.value h z := by
  cases first with
  | covered hc =>
    cases second with
    | covered => exact ⟨rfl, rfl⟩
    | upgrade hm _ => omega
  | @upgrade es t y d n hm actual =>
    cases second with
    | covered hc => omega
    | @upgrade fs u z e k hm' actual' =>
      let E := envelope (budget (costBound H))
      obtain ⟨t₀, y₀, hr₀, hv₀, hl₀, count, h1, lower, continued, all⟩ :=
        same_handle_return.{0} E (by have := envelope_pos (budget (costBound H)); omega)
          B h (complete E (envelope_pos _)) p x hx
      obtain ⟨hes, ht, hd, hv, rest⟩ := all es t y d n actual
      obtain ⟨hfs, hu, he, hz, rest'⟩ := all fs u z e k actual'
      refine ⟨?_, hv.trans hz.symm⟩
      rw [hes, hfs, hd, he]

/-- Recovery after any positive-modulus physical upgrade of an authentic
prefix, independently of the online envelope policy. Old labels at a divisor
are recovered by reduction from the same original pair and actual cuts. -/
def UpgradeRecovery {Handle World : Type} (B : SourceService Handle World) (h : Handle)
    (x₀ : World) (old : List TapeEvent) (x : World) (E : ℕ) (es : List Event)
    (d : ZMod E × ZMod E) (y : World) : Prop :=
  let tape := old ++ es.map (stamp E)
  let original := rewind E (letters old) d
  TapeRun B h x₀ tape y ∧
  original = residueSource E (B.value h x₀) ∧
  d = residueSource E (B.value h x) ∧
  d = residueSource E (B.value h y) ∧
  paidReads es = (if E = 1 then 0 else 2 * costBound E) ∧
  Continued B h E (B.value h x) d y ∧
  ∀ D, 0 < D → ∀ div : D ∣ E,
    reduce D E div original = residueSource D (B.value h x₀) ∧
    reduce D E div d = residueSource D (B.value h x) ∧
    ∀ t, t ≤ (letters tape).length → ∃ z,
      B.lawful h z ∧ B.value h z = runWord (cutWord tape t) (B.value h x₀) ∧
      scratch D (reduce D E div original) (cutWord tape t) = residueSource D (B.value h z) ∧
      (∀ W, predict D (scratch D (reduce D E div original) (cutWord tape t)) W =
        terminalGcd D W (B.value h z)) ∧
      ∀ j, GraftAffineClosure.quantity
          (scratch D (scratch D (reduce D E div original) (cutWord tape t))
            (List.replicate j true)) =
        (quantity (runWord (List.replicate j true) (B.value h z)) : ZMod D)

private theorem upgrade_transport {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (x₀ x : World) (hx₀ : B.lawful h x₀) (old : List TapeEvent)
    (oldrun : TapeRun B h x₀ old x) (E : ℕ) (hE : 0 < E)
    {es t y d n} (hr : ServiceRun B h p (PositiveClosingExecution.controller E) E
      (PositiveClosingExecution.controller E).initial x es t y d n) :
    UpgradeRecovery B h x₀ old x E es d y := by
  have old_endpoint := tape_endpoint oldrun hx₀
  obtain ⟨t₀, y₀, hr₀, hv₀, hl₀, count, h1, lower, continued, all⟩ :=
    same_handle_return.{0} E (by omega) B h (complete E hE) p x old_endpoint.2
  obtain ⟨hes, ht, hd, hv, hl, hn, h1, hc⟩ := all es t y d n hr
  have horig : rewind E (letters old) d = residueSource E (B.value h x₀) := by
    rw [hd, old_endpoint.1, ← scratch_sound, rewind_scratch]
  have actual := tape_append oldrun (service_tape hr)
  have he : d = residueSource E (B.value h y) := by
    rw [hd]
    exact hc.1.2
  refine ⟨actual, horig, hd, he, hes ▸ count, ?_, ?_⟩
  · simpa only [hd] using hc
  · intro D hD div
    have ho : reduce D E div (rewind E (letters old) d) = residueSource D (B.value h x₀) := by
      rw [horig, reduce_source]
    refine ⟨ho, by rw [hd, reduce_source], ?_⟩
    intro t ht
    obtain ⟨z, hlz, hvz⟩ := tape_cuts actual hx₀ t ht
    have hp : scratch D (reduce D E div (rewind E (letters old) d))
        (cutWord (old ++ es.map (stamp E)) t) = residueSource D (B.value h z) := by
      rw [ho, scratch_sound, hvz]
    refine ⟨z, hlz, hvz, hp, ?_, ?_⟩
    · intro W
      rw [hp]
      exact predict_sound D (by omega) W _
    · intro j
      rw [hp, scratch_sound]
      simp [GraftAffineClosure.quantity, residueSource, quantity]

private theorem request_sound {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (x₀ x : World) (a : Memory) (H : ℕ) (hH : 0 < H)
    (s : Sound B h x₀ a x) (hx₀ : B.lawful h x₀)
    {b y} (hr : RequestRun B h p a H x b y) : Sound B h x₀ b y := by
  have hj : 0 < Nat.lcm a.joint H := Nat.pos_of_ne_zero (Nat.lcm_ne_zero s.positive.ne' hH.ne')
  have hc := cost_lcm s.positive hH
  have hmax : maximum (a.requests ++ [H]) = max (maximum a.requests) (costBound H) := by
    simp [maximum, List.foldl_append]
  have hjoint : joint (a.requests ++ [H]) = Nat.lcm a.joint H := by
    rw [joint, List.foldl_append]
    change Nat.lcm (joint a.requests) H = Nat.lcm a.joint H
    rw [← s.joint_eq]
  cases hr with
  | covered covered =>
    have hp : budget (costBound (Nat.lcm a.joint H)) = a.precision := by
      rw [hc, budget_covered _ _ (s.precision_eq ▸ covered), ← s.precision_eq]
    refine ⟨s.tape, s.lawful, hj, hjoint.symm, ?_, hp.symm,
      s.original_eq, s.current_eq, ?_, ?_⟩
    · simp [hit, hmax, hc, s.maximum_eq]
    · intro K hK
      rcases List.mem_append.mp hK with old | new
      · exact s.covered K old
      · have : K = H := by simpa using new
        subst K
        exact ⟨hH, (envelope_covers _ _ hH).mpr covered⟩
    · change (if costBound (Nat.lcm a.joint H) = 0 then reads a.tape = 0 else
        reads a.tape ≤ 4 * a.precision - 2 ∧
          4 * a.precision - 2 < 8 * costBound (Nat.lcm a.joint H))
      rw [hc]
      by_cases hm : costBound a.joint = 0
      · have hp0 : a.precision = 0 := by simp [s.precision_eq, hm, budget]
        have hh0 : costBound H = 0 := by omega
        simpa [hm, hh0] using s.payment
      · have pay := s.payment
        rw [ite_eq_right hm] at pay
        rw [ite_eq_right (by omega : max (costBound a.joint) (costBound H) ≠ 0)]
        exact ⟨pay.1, pay.2.trans_le (Nat.mul_le_mul_left 8 (le_max_left _ _))⟩
  | @upgrade es t y d n miss actual =>
    let k := costBound H
    let q := budget k
    let E := envelope q
    have hk : 0 < k := by dsimp [k]; omega
    have hq : 0 < q := lt_of_lt_of_le hk (budget_ge k)
    have hE : 0 < E := envelope_pos _
    have hE1 : E ≠ 1 := by
      intro he
      have ec := envelope_cost q
      rw [← show E = envelope q from rfl, he] at ec
      simp [costBound] at ec
      omega
    obtain ⟨tape, horig, hd, he, count, continued, recovery⟩ :=
      upgrade_transport B h complete p x₀ x hx₀ a.tape s.tape E hE actual
    have hl := (tape_endpoint tape hx₀).2
    have hjcost : costBound (Nat.lcm a.joint H) = k := by
      rw [hc, max_eq_right]
      exact (budget_ge _).trans (s.precision_eq ▸ (le_of_lt miss))
    have pq : a.precision ≤ q := by
      rw [s.precision_eq]
      exact budget_mono ((budget_ge _).trans (s.precision_eq ▸ (le_of_lt miss)))
    have hcount : paidReads es = 2 * q := by
      rw [ite_eq_right hE1] at count
      simpa only [E, envelope_cost] using count
    refine ⟨tape, hl, hj, hjoint.symm, ?_, ?_, horig, he, ?_, ?_⟩
    · simp [install, hmax, hc, s.maximum_eq]
    · change q = budget (costBound (Nat.lcm a.joint H))
      rw [hjcost]
    · intro K hK
      rcases List.mem_append.mp hK with old | new
      · have ho := s.covered K old
        exact ⟨ho.1, ho.2.trans (envelope_mono pq)⟩
      · have : K = H := by simpa using new
        subst K
        exact ⟨hH, (envelope_covers _ _ hH).mpr (budget_ge k)⟩
    · change (if costBound (Nat.lcm a.joint H) = 0 then
        reads (a.tape ++ es.map (stamp E)) = 0 else
        reads (a.tape ++ es.map (stamp E)) ≤ 4 * q - 2 ∧
          4 * q - 2 < 8 * costBound (Nat.lcm a.joint H))
      rw [hjcost, ite_eq_right hk.ne']
      rw [reads_append, reads_stamp, hcount]
      constructor
      · by_cases hm : costBound a.joint = 0
        · have pay := s.payment
          rw [ite_eq_left hm] at pay
          rw [pay]
          omega
        · have pay := s.payment
          rw [ite_eq_right hm] at pay
          have jump : 2 * a.precision ≤ q := by
            rw [s.precision_eq]
            exact budget_jump (Nat.pos_of_ne_zero hm) (s.precision_eq ▸ miss)
          omega
      · have small := (budget_spec hk).2.1
        change q < 2 * k at small
        omega

private theorem continue_sound {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (x₀ x : World) (a : Memory) (w : List Bool)
    (s : Sound B h x₀ a x) {y} (hr : ContinueRun B h a w x y) :
    Sound B h x₀ (advanceMemory a w) y := by
  have actual := protocol_tape w x y a.original a.current hr
  have endpoint := tape_endpoint actual s.lawful
  refine ⟨tape_append s.tape actual, endpoint.2, s.positive, s.joint_eq, s.maximum_eq,
    s.precision_eq, s.original_eq, ?_, s.covered, ?_⟩
  · change scratch (envelope a.precision) a.current w =
      residueSource (envelope a.precision) (B.value h y)
    rw [s.current_eq, scratch_sound, endpoint.1, letters_actions]
  · simpa only [advanceMemory, reads_append, reads_actions, Nat.add_zero] using s.payment

private theorem run_sound {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (x₀ : World) (hx₀ : B.lawful h x₀) {a x is b y}
    (hr : OnlineRun B h p a x is b y) (s : Sound B h x₀ a x) : Sound B h x₀ b y := by
  revert s
  induction hr with
  | nil => intro s; exact s
  | request hs tail ih =>
    intro s
    exact ih (request_sound B h complete p x₀ _ _ _ (by assumption) s hx₀ hs)
  | continuation hs tail ih => intro s; exact ih (continue_sound B h x₀ _ _ _ s hs)

private theorem run_exists {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (x₀ : World) (hx₀ : B.lawful h x₀) (is : List Input) :
    ∀ a x, Sound B h x₀ a x → ∃ b y, OnlineRun B h p a x is b y := by
  induction is with
  | nil => intro a x _; exact ⟨a, x, .nil _ _⟩
  | cons i is ih =>
    intro a x s
    cases i with
    | request H hH =>
      obtain ⟨b, y, hr⟩ := request_exists B h complete p a H x s.lawful
      obtain ⟨c, z, tail⟩ := ih b y (request_sound B h complete p x₀ x a H hH s hx₀ hr)
      exact ⟨c, z, .request hr tail⟩
    | continuation w =>
      obtain ⟨y, hr, hv, hl⟩ := continuation_exists B h _ (complete _ (envelope_pos _))
        w x a.original a.current s.lawful
      obtain ⟨b, z, tail⟩ := ih (advanceMemory a w) y (continue_sound B h x₀ x a w s hr)
      exact ⟨b, z, .continuation hr tail⟩

/-- Recovery from earned memory at a covered modulus. A past label takes an
authentic prefix position; a further word passed to `predict` is hypothetical. -/
def past (a : Memory) (D : ℕ) (hD : D ∣ envelope a.precision) (t : ℕ) : ZMod D × ZMod D :=
  scratch D (reduce D _ hD a.original) (cutWord a.tape t)

def Compatible (a b : Memory) : Prop :=
  ∃ d : envelope a.precision ∣ envelope b.precision,
    reduce _ _ d b.original = a.original ∧
    reduce _ _ d b.current = a.current ∧
    ∀ t, t ≤ (letters a.tape).length →
      reduce _ _ d (scratch _ b.original (cutWord a.tape t)) =
        scratch _ a.original (cutWord a.tape t)

private theorem request_compatible {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (x₀ x : World) (a : Memory) (H : ℕ) (hH : 0 < H)
    (s : Sound B h x₀ a x) (hx₀ : B.lawful h x₀)
    {b y} (hr : RequestRun B h p a H x b y) : Compatible a b := by
  have next := request_sound B h complete p x₀ x a H hH s hx₀ hr
  have hp : a.precision ≤ b.precision := by
    rw [s.precision_eq, next.precision_eq]
    cases hr with
    | covered hc =>
      apply budget_mono
      rw [show (hit a H).joint = Nat.lcm a.joint H from rfl, cost_lcm s.positive hH]
      exact le_max_left _ _
    | upgrade hc actual =>
      apply budget_mono
      rw [show (install a H _ _).joint = Nat.lcm a.joint H from rfl, cost_lcm s.positive hH]
      exact le_max_left _ _
  let d := envelope_mono hp
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [next.original_eq, reduce_source, s.original_eq]
  · cases hr with
    | covered hc =>
      have d' : envelope a.precision ∣ envelope a.precision := d
      change reduce (envelope a.precision) (envelope a.precision) d' a.current = a.current
      rw [s.current_eq]
      exact reduce_source _ _ d' _
    | @upgrade es t y e n hc actual =>
      have earned := (acquisition_agrees B h complete p _ (envelope_pos _) x s.lawful actual).1
      have d' : envelope a.precision ∣ envelope (budget (costBound H)) := d
      change reduce (envelope a.precision) (envelope (budget (costBound H))) d' e = a.current
      rw [earned]
      exact (reduce_source _ _ d' _).trans s.current_eq.symm
  · intro t ht
    rw [next.original_eq, s.original_eq, scratch_sound, reduce_source, scratch_sound]

/-- Arithmetic services read only retained residues and public words. The
actual synchronized continuation has a tape with no additional read event. -/
def ArchiveService {Handle World : Type} (B : SourceService Handle World) (h : Handle)
    (x₀ : World) (a : Memory) (x : World) : Prop :=
  (∀ D, 0 < D → ∀ hD : D ∣ envelope a.precision,
    reduce D _ hD a.original = residueSource D (B.value h x₀) ∧
    reduce D _ hD a.current = residueSource D (B.value h x) ∧
    (∀ W, predict D (reduce D _ hD a.current) W = terminalGcd D W (B.value h x)) ∧
    ∀ t, t ≤ (letters a.tape).length → ∃ z,
      B.lawful h z ∧ B.value h z = runWord (cutWord a.tape t) (B.value h x₀) ∧
      past a D hD t = residueSource D (B.value h z) ∧
      (∀ W, predict D (past a D hD t) W = terminalGcd D W (B.value h z)) ∧
      ∀ j, GraftAffineClosure.quantity (scratch D (past a D hD t) (List.replicate j true)) =
        (quantity (runWord (List.replicate j true) (B.value h z)) : ZMod D)) ∧
  (∀ w, ∃ y, ContinueRun B h a w x y ∧
    reads (advanceMemory a w).tape = reads a.tape ∧
    (advanceMemory a w).original = a.original ∧
    (advanceMemory a w).current = residueSource (envelope a.precision) (B.value h y)) ∧
  (costBound a.joint ≠ 0 →
    (∃ k, a.precision = 2 ^ k) ∧ costBound a.joint ≤ a.precision ∧
    a.precision < 2 * costBound a.joint ∧
    (∀ k, costBound a.joint ≤ 2 ^ k → a.precision ≤ 2 ^ k) ∧
    8 * costBound a.joint = 4 * (if a.joint = 1 then 0 else 2 * costBound a.joint)) ∧
  (∀ p H, (∃ b y, RequestRun B h p a H x b y) ∧
    ∀ b y c z, RequestRun B h p a H x b y → RequestRun B h p a H x c z →
      b = c ∧ B.value h y = B.value h z)

private theorem archive_service {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (x₀ x : World)
    (a : Memory) (hx₀ : B.lawful h x₀) (s : Sound B h x₀ a x) :
    ArchiveService B h x₀ a x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D hD div
    have ho : reduce D _ div a.original = residueSource D (B.value h x₀) := by
      rw [s.original_eq, reduce_source]
    have hc : reduce D _ div a.current = residueSource D (B.value h x) := by
      rw [s.current_eq, reduce_source]
    refine ⟨ho, hc, ?_, ?_⟩
    · intro W
      rw [hc]
      exact predict_sound D (by omega) W _
    · intro t ht
      obtain ⟨z, hl, hv⟩ := tape_cuts s.tape hx₀ t ht
      have hp : past a D div t = residueSource D (B.value h z) := by
        rw [past, ho, scratch_sound, hv]
      refine ⟨z, hl, hv, hp, ?_, ?_⟩
      · intro W
        rw [hp]
        exact predict_sound D (by omega) W _
      · intro j
        rw [hp, scratch_sound]
        simp [GraftAffineClosure.quantity, residueSource, quantity]
  · intro w
    obtain ⟨y, hr, hv, hl⟩ := continuation_exists B h _ (complete _ (envelope_pos _))
      w x a.original a.current s.lawful
    have next := continue_sound B h x₀ x a w s hr
    exact ⟨y, hr, by simp [advanceMemory, reads_append, reads_actions], rfl, next.current_eq⟩
  · intro hm
    have hs := budget_spec (Nat.pos_of_ne_zero hm)
    have hj : a.joint ≠ 1 := by intro hj; simp [hj, costBound] at hm
    refine ⟨⟨Nat.clog 2 (costBound a.joint), ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp [s.precision_eq, budget, hm]
    · rw [s.precision_eq]; exact hs.1
    · rw [s.precision_eq]; exact hs.2.1
    · rw [s.precision_eq]; exact hs.2.2
    · simp [hj]; omega
  · intro p H
    refine ⟨request_exists B h complete p a H x s.lawful, ?_⟩
    intro b y c z first second
    exact request_deterministic B h complete p a H x s.lawful first second

/-- One uniform online program runs on the same bound natural-pair source
for every finite delivered input sequence. Every completed execution has the
earned common-original archive, authentic past-cut services, exact joint
precision and cumulative actual-read bound. Every upgrade preserves all old
labels and returns current behavior at that upgrade's entry. -/
theorem complete_online_archive {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (complete : VariableCompletion B h) (p : Tariffs)
    (x₀ : World) (hx₀ : B.lawful h x₀) :
    (∀ is : List Input, ∃ a x, OnlineRun B h p initial x₀ is a x) ∧
    (∀ is a x, OnlineRun B h p initial x₀ is a x →
      Sound B h x₀ a x ∧ ArchiveService B h x₀ a x) ∧
    (∀ is a x H, 0 < H → OnlineRun B h p initial x₀ is a x →
      ∀ b y, RequestRun B h p a H x b y → Compatible a b) ∧
    (∀ old x E, 1 < E → TapeRun B h x₀ old x →
      ∀ es t y d n, ServiceRun B h p (PositiveClosingExecution.controller E) E
        (PositiveClosingExecution.controller E).initial x es t y d n →
      UpgradeRecovery B h x₀ old x E es d y) := by
  have start := initial_sound B h x₀ hx₀
  refine ⟨fun is => run_exists B h complete p x₀ hx₀ is initial x₀ start, ?_, ?_, ?_⟩
  · intro is a x hr
    have s := run_sound B h complete p x₀ hx₀ hr start
    exact ⟨s, archive_service B h complete x₀ x a hx₀ s⟩
  · intro is a x H hH hr b y request
    exact request_compatible B h complete p x₀ x a H hH
      (run_sound B h complete p x₀ hx₀ hr start) hx₀ request
  · intro old x E hE oldrun es t y d n actual
    exact upgrade_transport B h complete p x₀ x hx₀ old oldrun E (by omega) actual

#print axioms complete_online_archive

end D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive
