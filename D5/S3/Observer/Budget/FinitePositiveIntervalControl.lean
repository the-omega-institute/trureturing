/- GID: D5/S3/Observer/Budget/FinitePositiveIntervalControl
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/FinitePositiveIntervalControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite memory executes positive sensing through a stationary unit table. -/

import D5.S3.Observer.Budget.PositiveIntervalAcquisition
import D5.S3.ObserverMemory.Algorithms.ActualControlSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.FinitePositiveIntervalControl

open PositiveIntervalAcquisition
open DyadicForwardWaitingOptimality (Protocol execute threshold)
open D5.S3.ObserverMemory.Algorithms.ActualControlSlots (Action Controller digit)

/-- All changing registers are part of this finite memory, including the
remaining wait and the complete accumulated source-step count. -/
structure Memory (p P B : Nat) where
  first : Fin p
  interval : {i : Fin P × Fin P // i.1.val ≤ i.2.val}
  elapsed : Fin (B + 1)
  remaining : Fin P
  mode : Fin 3

/-- The common initial control is distinct from every initialized memory. -/
inductive Control (p P B : Nat) where
  | start
  | stored (memory : Memory p P B)

private theorem control_finite (p P B : Nat) : Finite (Control p P B) := by
  let encode : Control p P B →
      Option (Fin p × (Fin P × Fin P) × Fin (B + 1) × Fin P × Fin 3) := fun q =>
    match q with
    | .start => none
    | .stored f => some (f.first, f.interval.val, f.elapsed, f.remaining, f.mode)
  apply Finite.of_injective encode
  intro q q' he
  cases q with
  | start => cases q' <;> simp_all [encode]
  | stored f =>
    cases q' with
    | start => simp [encode] at he
    | stored g =>
      cases f
      cases g
      simp_all [encode, Prod.mk.injEq, Subtype.ext_iff]

/-- List semantics checks each actual action against the stationary table. -/
def Follows {p P : Nat} {Q : Type} (C : Controller p P Q)
    (hp : 2 ≤ p) (hP : 0 < P) :
    (ZMod (p * P) × Q) → List Action → (ZMod (p * P) × Q) → Prop
  | c, [], z => c = z
  | c, a :: word, z => C.action c.2 = a ∧ Follows C hp hP (C.step hp hP c) word z

/-- Expand each waiting increment into charged unit waits followed by a read. -/
def unitWord : List Nat → List Action
  | [] => []
  | w :: tail => List.replicate w Action.wait ++ Action.read :: unitWord tail

private theorem follows_append {p P : Nat} {Q : Type} (C : Controller p P Q)
    (hp : 2 ≤ p) (hP : 0 < P) (word : List Action)
    (c z terminal : ZMod (p * P) × Q) (tail : List Action)
    (first : Follows C hp hP c word z) (second : Follows C hp hP z tail terminal) :
    Follows C hp hP c (word ++ tail) terminal := by
  induction word generalizing c with
  | nil => simpa only [Follows, List.nil_append] using first ▸ second
  | cons a word ih =>
    exact ⟨first.1, ih _ first.2⟩

private def ready {p P B : Nat} (hP : 0 < P) (b : Fin p)
    (lo hi E : Nat) (hlo : lo < hi) (hhi : hi ≤ P) (hE : E ≤ B) : Memory p P B :=
  let m := (lo + hi) / 2
  let w := waitTo P E (P - m)
  { first := b
    interval := ⟨(⟨lo, by omega⟩, ⟨hi - 1, by omega⟩), by simp; omega⟩
    elapsed := ⟨E, by omega⟩
    remaining := ⟨(w - 1) % P, Nat.mod_lt _ hP⟩
    mode := if hi ≤ lo + 1 then 2 else 0 }

private def action {p P B : Nat} : Control p P B → Action
  | .start => .read
  | .stored f =>
      if f.mode = 2 then .halt
      else if f.mode = 0 ∧ f.elapsed.val < B then .wait else .read

private def advanced {p P B : Nat} (f : Memory p P B) (h : f.elapsed.val < B) :
    Memory p P B :=
  { f with
    elapsed := ⟨f.elapsed.val + 1, by omega⟩
    remaining := ⟨f.remaining.val - 1, by have := f.remaining.isLt; omega⟩
    mode := if f.remaining.val = 0 then 1 else 0 }

private def waitNext {p P B : Nat} : Control p P B → Control p P B
  | .start => .start
  | .stored f =>
      if h : f.elapsed.val < B then .stored (advanced f h) else .stored f

private def readNext {p P B : Nat} (hP : 0 < P) :
    Control p P B → Fin p → Control p P B
  | .start, y => .stored (ready hP y 0 P 0 hP le_rfl (Nat.zero_le _))
  | .stored f, y =>
      let lo := f.interval.val.1.val
      let hi := f.interval.val.2.val + 1
      let E := f.elapsed.val
      let m := (lo + hi) / 2
      if live : f.mode = 1 ∧ lo + 1 < hi ∧ E % P = P - m then
        if y.val = (f.first.val + E / P) % p then
          .stored (ready hP f.first lo m E (by dsimp [m] at *; omega)
            (by have := f.interval.val.2.isLt; dsimp [hi, m] at *; omega)
            (by have := f.elapsed.isLt; dsimp [E]; omega))
        else if y.val = (f.first.val + E / P + 1) % p then
          .stored (ready hP f.first m hi E (by dsimp [m] at *; omega)
            (by have := f.interval.val.2.isLt; dsimp [hi]; omega)
            (by have := f.elapsed.isLt; dsimp [E]; omega))
        else .stored { f with mode := 2 }
      else .stored { f with mode := 2 }

/-- Each table entry is total, including unreachable memories and answers. -/
def table {p P B : Nat} (hP : 0 < P) : Controller p P (Control p P B) where
  initial := .start
  action := action
  waitNext := waitNext
  readNext := readNext hP
  output := fun q => match q with
    | .start => 0
    | .stored f => (f.first.val * P + f.interval.val.1.val : Nat)

/-- The current-state output is also a fixed function of the same control. -/
def currentOutput {p P B : Nat} : Control p P B → ZMod (p * P)
  | .start => 0
  | .stored f => (f.first.val * P + f.interval.val.1.val + f.elapsed.val : Nat)


private def atRead {p P B : Nat} (hP : 0 < P) (f : Memory p P B)
    (n : Nat) (bound : f.elapsed.val + n ≤ B) : Memory p P B :=
  { f with
    elapsed := ⟨f.elapsed.val + n, by omega⟩
    remaining := ⟨0, hP⟩
    mode := 1 }

private theorem wait_segment {p P B : Nat} (hp : 2 ≤ p) (hP : 0 < P)
    (n : Nat) : ∀ (f : Memory p P B) (s : ZMod (p * P)),
    f.mode = 0 → f.remaining.val + 1 = n →
    ∀ bound : f.elapsed.val + n ≤ B,
    Follows (table hP) hp hP (s, .stored f) (List.replicate n Action.wait)
      (s + (n : ZMod (p * P)), .stored (atRead hP f n bound)) := by
  induction n with
  | zero => intro f s mode count; omega
  | succ n ih =>
    intro f s mode count bound
    have guard : f.elapsed.val < B := by omega
    have first : (table hP).action (.stored f) = .wait := by
      simp [table, action, mode, guard]
    have step : (table hP).step hp hP (s, .stored f) =
        (s + 1, .stored (advanced f guard)) := by
      unfold Controller.step
      rw [first]
      change (s + 1, waitNext (.stored f)) = _
      simp [waitNext, guard]
    rw [List.replicate_succ, Follows]
    refine ⟨first, ?_⟩
    rw [step]
    cases n with
    | zero =>
      have rem : f.remaining.val = 0 := by omega
      simp only [List.replicate_zero, Follows]
      congr 1
      · simp
      · apply congrArg Control.stored
        simp [advanced, atRead, rem]
    | succ n =>
      have rem : f.remaining.val ≠ 0 := by omega
      have nextmode : (advanced f guard).mode = 0 := by simp [advanced, rem]
      have nextcount : (advanced f guard).remaining.val + 1 = n + 1 := by
        simp only [advanced]; omega
      have nextbound : (advanced f guard).elapsed.val + (n + 1) ≤ B := by
        simp only [advanced]; omega
      have rest := ih (advanced f guard) (s + 1) nextmode nextcount nextbound
      convert rest using 1 <;> simp [atRead, advanced, Nat.cast_add, add_assoc]
      constructor
      · ring
      · omega

private theorem waits_sum_clock {d : Nat} (T : Protocol d)
    (read : Nat → Nat → Fin 2) (now r : Nat) :
    (execute read T now r).2 = now + (waits read T now r).sum := by
  induction T generalizing now with
  | stop answer => simp [execute, waits]
  | query w next ih =>
    simpa [execute, waits, List.sum_cons, Nat.add_assoc] using ih (read (now + w) r) (now + w)


private theorem physical_digit {p P : Nat} (hp : 2 ≤ p) (hP : 0 < P)
    (b r E : Nat) (hr : r < P) :
    (digit hp hP ((b * P + r + E : Nat) : ZMod (p * P))).val =
      (b + E / P + (threshold P E r).val) % p := by
  letI : NeZero (p * P) := ⟨by positivity⟩
  change (((b * P + r + E : Nat) : ZMod (p * P)).val / P) = _
  rw [ZMod.val_natCast]
  exact (PositiveIntervalAcquisition.result p P hp hP).choose_spec.2.1 b E r hr |>.1

private theorem drive {p P B : Nat} (hp : 2 ≤ p) (hP : 0 < P) (b : Fin p)
    (d : Nat) : ∀ lo hi E (hlo : lo < hi) (hhi : hi ≤ P)
    (hE : E ≤ B), hi - lo ≤ 2 ^ d →
    (E % P = (P - lo) % P ∨ E % P = (P - hi) % P) →
    E + d * (P - 1) ≤ B → ∀ r, lo ≤ r → r < hi →
    ∃ q : Control p P B,
      Follows (table hP) hp hP
        (((b.val * P + r + E : Nat) : ZMod (p * P)),
          .stored (ready hP b lo hi E hlo hhi hE))
        (unitWord (waits (decodedRead p P b.val) (acquire P d lo hi E) E r))
        (((b.val * P + r + (execute (decodedRead p P b.val)
          (acquire P d lo hi E) E r).2 : Nat) : ZMod (p * P)), q) ∧
      (table hP).action q = .halt ∧
      (table hP).output q = ((b.val * P + r : Nat) : ZMod (p * P)) ∧
      currentOutput q = ((b.val * P + r + (execute (decodedRead p P b.val)
        (acquire P d lo hi E) E r).2 : Nat) : ZMod (p * P)) := by
  induction d with
  | zero =>
    intro lo hi E hlo hhi hE size align budget r hrlo hrhi
    have hr : r = lo := by simp only [Nat.pow_zero] at size; omega
    have stop : hi ≤ lo + 1 := by simp only [Nat.pow_zero] at size; omega
    refine ⟨.stored (ready hP b lo hi E hlo hhi hE), ?_, ?_, ?_, ?_⟩
    · simp [acquire, waits, unitWord, execute, Follows]
    · simp [table, action, ready, stop]
    · simp [table, ready, hr]
    · simp [currentOutput, ready, execute, acquire, hr]
  | succ d ih =>
    intro lo hi E hlo hhi hE size align budget r hrlo hrhi
    by_cases stop : hi ≤ lo + 1
    · have hr : r = lo := by omega
      refine ⟨.stored (ready hP b lo hi E hlo hhi hE), ?_, ?_, ?_, ?_⟩
      · simp [acquire, stop, waits, unitWord, execute, Follows]
      · simp [table, action, ready, stop]
      · simp [table, ready, hr]
      · simp [currentOutput, ready, execute, acquire, stop, hr]
    · let m := (lo + hi) / 2
      let w := waitTo P E (P - m)
      obtain ⟨hmlo, hmhi, wpos, wlt, phase⟩ := interval_wait hlo hhi (by omega) align
      change lo < m at hmlo
      change m < hi at hmhi
      change 0 < w at wpos
      change w < P at wlt
      change (E + w) % P = P - m at phase
      have halves : m - lo ≤ 2 ^ d ∧ hi - m ≤ 2 ^ d := by
        dsimp [m]
        rw [Nat.pow_succ] at size
        omega
      have nextbudget : E + w + d * (P - 1) ≤ B := by
        rw [Nat.add_mul, Nat.one_mul] at budget
        omega
      have hE' : E + w ≤ B := by omega
      have nextalign : (E + w) % P = (P - m) % P := by
        rw [phase, Nat.mod_eq_of_lt (show P - m < P by omega)]
      let f := ready hP b lo hi E hlo hhi hE
      have initialmode : f.mode = 0 := by simp [f, ready, stop]
      have countdown : f.remaining.val + 1 = w := by
        dsimp [f, ready]
        change (w - 1) % P + 1 = w
        rw [Nat.mod_eq_of_lt (show w - 1 < P by omega)]
        omega
      have waitbound : f.elapsed.val + w ≤ B := hE'
      let after := atRead hP f w waitbound
      let source : ZMod (p * P) := ((b.val * P + r + E : Nat) : ZMod (p * P))
      let shifted : ZMod (p * P) := ((b.val * P + r + (E + w) : Nat) : ZMod (p * P))
      have shifted_eq : source + (w : ZMod (p * P)) = shifted := by
        simp [source, shifted, Nat.cast_add, add_assoc]
      have waitrun : Follows (table hP) hp hP (source, .stored f)
          (List.replicate w Action.wait) (shifted, .stored after) := by
        simpa only [shifted_eq] using wait_segment hp hP w f source initialmode countdown waitbound
      have readaction : (table hP).action (.stored after) = .read := by
        simp [table, action, after, atRead]
      let y := digit hp hP shifted
      have digitval := physical_digit hp hP b.val r (E + w) (by omega)
      change y.val = _ at digitval
      have decoded := (PositiveIntervalAcquisition.result p P hp hP).choose_spec.2.1
        b.val (E + w) r (by omega) |>.2
      rw [threshold, phase, Nat.sub_sub_self (show m ≤ P by omega)] at digitval decoded
      have endpoint : hi - 1 + 1 = hi := by omega
      by_cases left : r < m
      · have bit : decodedRead p P b.val (E + w) r = 0 := by
          simpa only [if_pos left] using decoded
        have value : y.val = (b.val + (E + w) / P) % p := by
          simpa only [if_pos left, Fin.val_zero, Nat.add_zero] using digitval
        dsimp only [m, w] at bit value
        have row : readNext hP (.stored after) y =
            .stored (ready hP b lo m (E + w) hmlo (by omega) hE') := by
          simp [readNext, after, atRead, f, ready, endpoint, stop, phase, value,
            show lo + 1 < hi by omega, m, w]
        have step : (table hP).step hp hP (shifted, .stored after) =
            (shifted, .stored (ready hP b lo m (E + w) hmlo (by omega) hE')) := by
          unfold Controller.step
          rw [readaction]
          change (shifted, readNext hP (.stored after) y) = _
          rw [row]
        obtain ⟨q, tail, halt, output, current⟩ := ih lo m (E + w) hmlo (by omega) hE'
          halves.1 (Or.inr nextalign) nextbudget r hrlo left
        refine ⟨q, ?_, halt, output, ?_⟩
        · simp only [acquire, if_neg stop, waits, m, w, bit, ite_true, unitWord]
          change Follows (table hP) hp hP (source, .stored f)
            (List.replicate w Action.wait ++ Action.read :: unitWord
              (waits (decodedRead p P b.val) (acquire P d lo m (E + w)) (E + w) r)) _
          apply follows_append (table hP) hp hP (List.replicate w Action.wait)
            (source, .stored f) (shifted, .stored after) _ _ waitrun
          refine ⟨readaction, ?_⟩
          rw [step]
          simpa only [acquire, if_neg stop, execute, m, w, bit, ite_true] using tail
        · simpa only [acquire, if_neg stop, execute, m, w, bit, ite_true] using current
      · have bit : decodedRead p P b.val (E + w) r = 1 := by
          simpa only [if_neg left] using decoded
        have value : y.val = (b.val + (E + w) / P + 1) % p := by
          simpa only [if_neg left, Fin.val_one] using digitval
        have different : y.val ≠ (b.val + (E + w) / P) % p := by
          intro same
          have raw : ((b.val * P + r + (E + w)) / P) % p = y.val := by
            rw [value]
            have port := (PositiveIntervalAcquisition.result p P hp hP).choose_spec.2.1
              b.val (E + w) r (by omega) |>.1
            rw [Nat.mul_comm p P, Nat.mod_mul_right_div_self] at port
            simpa only [threshold, phase, Nat.sub_sub_self (show m ≤ P by omega),
              if_neg left, Fin.val_one] using port
          unfold decodedRead at bit
          rw [raw, same, if_pos rfl] at bit
          exact (by decide : (0 : Fin 2) ≠ 1) bit
        rw [value] at different
        dsimp only [m, w] at bit value different
        have row : readNext hP (.stored after) y =
            .stored (ready hP b m hi (E + w) hmhi hhi hE') := by
          simp [readNext, after, atRead, f, ready, endpoint, stop, phase, different,
            value, show lo + 1 < hi by omega, m, w]
        have step : (table hP).step hp hP (shifted, .stored after) =
            (shifted, .stored (ready hP b m hi (E + w) hmhi hhi hE')) := by
          unfold Controller.step
          rw [readaction]
          change (shifted, readNext hP (.stored after) y) = _
          rw [row]
        obtain ⟨q, tail, halt, output, current⟩ := ih m hi (E + w) hmhi hhi hE'
          halves.2 (Or.inl nextalign) nextbudget r (by omega) hrhi
        have bitne : (1 : Fin 2) ≠ 0 := by decide
        refine ⟨q, ?_, halt, output, ?_⟩
        · simp only [acquire, if_neg stop, waits, m, w, bit, if_neg bitne, unitWord]
          change Follows (table hP) hp hP (source, .stored f)
            (List.replicate w Action.wait ++ Action.read :: unitWord
              (waits (decodedRead p P b.val) (acquire P d m hi (E + w)) (E + w) r)) _
          apply follows_append (table hP) hp hP (List.replicate w Action.wait)
            (source, .stored f) (shifted, .stored after) _ _ waitrun
          refine ⟨readaction, ?_⟩
          rw [step]
          simpa only [acquire, if_neg stop, execute, m, w, bit, if_neg bitne] using tail
        · simpa only [acquire, if_neg stop, execute, m, w, bit, if_neg bitne] using current

end D5.S3.Observer.Budget.FinitePositiveIntervalControl
