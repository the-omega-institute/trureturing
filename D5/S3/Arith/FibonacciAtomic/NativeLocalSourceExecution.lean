/- GID: D5/S3/Arith/FibonacciAtomic/NativeLocalSourceExecution
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Guarded addressed growth realizes sealed old frontiers and native leftmost splits. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution

open GenealogicalFiberTransport (Source substitution composition)

abbrev Address := List Bool
abbrev Event := Address × Bool

/-- The Boolean tag is true for P at alpha and false for S at beta.
False address bits select left children. Wrong tags and nonleaves reject. -/
def edit : Source → Address → Bool → Option Source
  | .of b, [], k => if b = k then some (substitution (.of b)) else none
  | .mul l r, false :: p, k => (edit l p k).map (fun l' => .mul l' r)
  | .mul l r, true :: p, k => (edit r p k).map (fun r' => .mul l r')
  | _, _, _ => none

def replay : Source → List Event → Option Source
  | t, [] => some t
  | t, (p,k) :: es => (edit t p k).bind (fun u => replay u es)

/-- The entry frontier is computed once, with acquired leaf tags and order. -/
def oldFrontier : Source → List Event
  | .of b => [([],b)]
  | .mul l r =>
      (oldFrontier l).map (fun e => (false :: e.1,e.2)) ++
      (oldFrontier r).map (fun e => (true :: e.1,e.2))

/-- Birth sort true allows alpha; sort false is born beta. -/
def native : Bool → Source → Bool
  | a, .of b => a || !b
  | _, .mul l r => native false l && native true r

def Native (t : Source) : Prop := native false t = true
instance (t : Source) : Decidable (Native t) := inferInstanceAs (Decidable (_ = _))

/-- Current left descent, independently acquired at each call. -/
def leftmost : Source → Address
  | .of _ => []
  | .mul l _ => false :: leftmost l

def splitLeft : Source → Source
  | .of false => .mul (.of false) (.of true)
  | .of true => .of true
  | .mul l r => .mul (splitLeft l) r

/-- Exact alpha-origin successful-event count. -/
def eventIndex (t : Source) : Nat := (composition t).1 + 2 * (composition t).2 - 1

private theorem weight_pos (t : Source) :
    0 < (composition t).1 + 2 * (composition t).2 := by
  have := Observer.ActualObserverAbsorbingNormalization.composition_total t
  have := t.length_pos
  omega

private theorem replay_append (t : Source) (es fs : List Event) :
    replay t (es ++ fs) = (replay t es).bind (fun u => replay u fs) := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨p,k⟩
    simp only [List.cons_append, replay, ih, Option.bind_assoc]

private theorem replay_left (l r : Source) (es : List Event) :
    replay (.mul l r) (es.map (fun e => (false :: e.1,e.2))) =
      (replay l es).map (fun l' => .mul l' r) := by
  induction es generalizing l with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨p,k⟩
    simp only [List.map_cons, replay, edit]
    cases h : edit l p k with
    | none => rfl
    | some v => simpa only [Option.map_some,Option.bind_some,FreeMagma.mul_eq] using ih v

private theorem replay_right (l r : Source) (es : List Event) :
    replay (.mul l r) (es.map (fun e => (true :: e.1,e.2))) =
      (replay r es).map (fun r' => .mul l r') := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨p,k⟩
    simp only [List.map_cons, replay, edit]
    cases h : edit r p k with
    | none => rfl
    | some v => simpa only [Option.map_some,Option.bind_some,FreeMagma.mul_eq] using ih v

private theorem frontier_replay (t : Source) :
    replay t (oldFrontier t) = some (substitution t) := by
  induction t with
  | of b => simp [oldFrontier, replay, edit]
  | mul l r ihl ihr =>
    rw [oldFrontier, replay_append, replay_left, ihl]
    simp only [Option.map_some, Option.bind_some]
    rw [replay_right, ihr]
    rfl

private theorem frontier_length (t : Source) : (oldFrontier t).length = t.length := by
  induction t with
  | of b => rfl
  | mul l r ihl ihr => simp [oldFrontier, FreeMagma.length, ihl, ihr]

private theorem native_right (t : Source) (h : Native t) : native true t = true := by
  cases t with
  | of b => simp [native]
  | mul l r => exact h

private theorem native_beta_count (t : Source) (h : Native t) : 0 < (composition t).2 := by
  induction t with
  | of b => cases b <;> simp_all [Native, native, composition]
  | mul l r ihl ihr =>
    have hl : Native l := (Bool.and_eq_true_iff.mp h).1
    have := ihl hl
    simp only [composition, Prod.snd_add]
    omega

private theorem native_split (t : Source) (h : Native t) :
    edit t (leftmost t) false = some (splitLeft t) ∧ Native (splitLeft t) ∧
      composition (splitLeft t) = composition t + (1,0) := by
  induction t with
  | of b => cases b <;> simp_all [Native, native, leftmost, splitLeft, edit,
      substitution, FreeMagma.lift_of, composition]
  | mul l r ihl ihr =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨eq,hn,hc⟩ := ihl hl
    refine ⟨?_, ?_, ?_⟩
    · simp only [leftmost, edit, eq, Option.map_some, splitLeft]
    · exact Bool.and_eq_true_iff.mpr ⟨hn,hr⟩
    · simp only [splitLeft, composition, hc]
      ext <;> simp [add_assoc, add_comm, add_left_comm]

private theorem substitution_native (t : Source) : Native (substitution t) := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r ihl ihr =>
    exact Bool.and_eq_true_iff.mpr ⟨ihl,native_right _ ihr⟩

private theorem substitution_composition (t : Source) :
    composition (substitution t) = ((composition t).2,
      (composition t).1 + (composition t).2) := by
  exact (GenealogicalFiberTransport.fiberMap (composition t) 1 ⟨t,rfl⟩).property

private theorem event_edit (t u : Source) (p : Address) (k : Bool)
    (h : edit t p k = some u) : eventIndex u = eventIndex t + 1 := by
  induction p generalizing t u with
  | nil =>
    cases t with
    | of b =>
      simp only [edit] at h
      split_ifs at h with eq
      · cases b <;> cases h <;> rfl
    | mul l r => cases h
  | cons d p ih =>
    cases t with
    | of b => cases h
    | mul l r =>
      cases d with
      | false =>
        obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
        have step := ih l v hv
        have pl := weight_pos l
        have pv := weight_pos v
        have pr := weight_pos r
        simp only [eventIndex, composition, Prod.fst_add, Prod.snd_add] at step ⊢
        omega
      | true =>
        obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
        have step := ih r v hv
        have pl := weight_pos l
        have pv := weight_pos v
        have pr := weight_pos r
        simp only [eventIndex, composition, Prod.fst_add, Prod.snd_add] at step ⊢
        omega

private theorem replay_event_index (t u : Source) (es : List Event)
    (h : replay t es = some u) : eventIndex u = eventIndex t + es.length := by
  induction es generalizing t with
  | nil => cases h; rfl
  | cons e es ih =>
    rcases e with ⟨p,k⟩
    obtain ⟨v,hv,hu⟩ := Option.bind_eq_some_iff.mp h
    have := event_edit t v p k hv
    have := ih v hu
    simp only [List.length_cons]
    omega

private theorem edit_preserves_sort (a : Bool) (t u : Source) (p : Address) (k : Bool)
    (hn : native a t = true) (h : edit t p k = some u) : native a u = true := by
  induction p generalizing a t u with
  | nil =>
    cases t with
    | of b =>
      simp only [edit] at h
      split_ifs at h with eq
      · cases h
        cases b <;> cases a <;> rfl
    | mul l r => cases h
  | cons d p ih =>
    cases t with
    | of b => cases h
    | mul l r =>
      obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hn
      cases d with
      | false =>
        obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
        exact Bool.and_eq_true_iff.mpr ⟨ih false l v hl hv,hr⟩
      | true =>
        obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
        exact Bool.and_eq_true_iff.mpr ⟨hl,ih true r v hr hv⟩

private theorem replay_preserves_sort (a : Bool) (t u : Source) (es : List Event)
    (hn : native a t = true) (h : replay t es = some u) : native a u = true := by
  induction es generalizing t with
  | nil => cases h; exact hn
  | cons e es ih =>
    rcases e with ⟨p,k⟩
    obtain ⟨v,hv,hu⟩ := Option.bind_eq_some_iff.mp h
    exact ih v (edit_preserves_sort a t v p k hn hv) hu

private theorem construct_from_birth (t : Source) (a : Bool) (hn : native a t = true) :
    ∃ es : List Event, replay (.of a) es = some t := by
  induction t generalizing a with
  | of b =>
    cases a <;> cases b
    · exact ⟨[],rfl⟩
    · simp [native] at hn
    · exact ⟨[([],true)],rfl⟩
    · exact ⟨[],rfl⟩
  | mul l r ihl ihr =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hn
    obtain ⟨es,he⟩ := ihl false hl
    obtain ⟨fs,hf⟩ := ihr true hr
    let rootEvents : List Event := if a then [([],true),([],false)] else [([],false)]
    have start : replay (.of a) rootEvents = some (.mul (.of false) (.of true)) := by
      cases a <;> rfl
    refine ⟨rootEvents ++ es.map (fun e => (false :: e.1,e.2)) ++
      fs.map (fun e => (true :: e.1,e.2)),?_⟩
    rw [replay_append,replay_append,start]
    simp only [Option.bind_some]
    rw [replay_left,he]
    simp only [Option.map_some,Option.bind_some]
    rw [replay_right,hf]
    rfl

private theorem attained_iff (t : Source) :
    (∃ es : List Event, replay (.of true) es = some t) ↔ native true t = true := by
  constructor
  · rintro ⟨es,he⟩
    exact replay_preserves_sort true (.of true) t es rfl he
  · exact construct_from_birth t true

private theorem positive_attained_iff (t : Source) :
    Native t ↔ (∃ es : List Event, replay (.of true) es = some t) ∧ t ≠ .of true := by
  rw [attained_iff]
  cases t with
  | of b => cases b <;> simp [Native,native] <;> intro bad <;> cases bad
  | mul l r => simp only [Native,native]; simp

/-- Full old-frontier execution and current-leftmost execution use the original
guarded source edits. Each accepted primitive adds exactly one event. -/
theorem native_execution :
    (∀ t : Source, replay t (oldFrontier t) = some (substitution t) ∧
      (oldFrontier t).length = t.length ∧ Native (substitution t)) ∧
    (∀ t : Source, Native t →
      edit t (leftmost t) false = some (splitLeft t) ∧ Native (splitLeft t) ∧
      composition (splitLeft t) = composition t + (1,0)) ∧
    (∀ (t u : Source) (es : List Event), replay t es = some u →
      eventIndex u = eventIndex t + es.length) ∧
    (∀ t : Source, Native t →
      eventIndex (substitution t) = eventIndex t + t.length ∧
      eventIndex (splitLeft t) = eventIndex t + 1 ∧
      (eventIndex t = 1 ↔ t = .of false)) ∧
    (∀ t : Source, (∃ es : List Event, replay (.of true) es = some t) ↔
      native true t = true) ∧
    (∀ t : Source, Native t ↔
      (∃ es : List Event, replay (.of true) es = some t) ∧ t ≠ .of true) := by
  refine ⟨fun t => ⟨frontier_replay t,frontier_length t,substitution_native t⟩,
    native_split, replay_event_index, ?_,attained_iff,positive_attained_iff⟩
  intro t hn
  have beta := native_beta_count t hn
  have len := Observer.ActualObserverAbsorbingNormalization.composition_total t
  have pos := weight_pos t
  have compF := substitution_composition t
  have compG := (native_split t hn).2.2
  refine ⟨?_, ?_, ?_⟩
  · simp only [eventIndex, compF]
    omega
  · simp only [eventIndex, compG, Prod.fst_add, Prod.snd_add]
    omega
  · constructor
    · intro he
      have length_one : t.length = 1 := by dsimp [eventIndex] at he; omega
      cases t with
      | of b => cases b <;> simp_all [Native, native]
      | mul l r =>
        have := l.length_pos
        have := r.length_pos
        simp only [FreeMagma.length] at length_one
        omega
    · rintro rfl
      rfl

#print axioms native_execution

end D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
