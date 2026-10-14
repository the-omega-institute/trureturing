/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Independent writer realization of finite adaptive native skeleton constraints. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints
import Mathlib.Computability.PartrecCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeLiteralPathConstraints (Formula compile compile_exact original value)

/-- An arbitrary accessible configuration takes one source-blind microstep.
Return hands off this whole configuration; there is no output projection. -/
inductive Op (C : Type) where
  | localStep : C → Op C
  | read : Address → (Reply → C) → Op C
  | ret : Op C

inductive ObserverEvent where
  | localStep
  | read : Address → Reply → ObserverEvent
  | ret

inductive Event where
  | update
  | observer : ObserverEvent → Event

abbrev Word := List Event
abbrev TimedWord := List (Nat × ObserverEvent)

/-- Each natural number is a finite independent writer burst immediately before
one observer event, including the first event and the separate Return. -/
def expand : TimedWord → Word
  | [] => []
  | (k,a) :: t => List.replicate k .update ++ .observer a :: expand t

/-- Source-blind skeletons follow the actual transition at every microstep;
only the four replies are hypothetically supplied. -/
inductive Skeleton {C : Type} (δ : C → Op C) : C → TimedWord → C → Prop
  | ret {c k} : δ c = .ret → Skeleton δ c [(k,.ret)] c
  | localStep {c d k t b} : δ c = .localStep d →
      Skeleton δ d t b → Skeleton δ c ((k,.localStep)::t) b
  | read {c p f y k t b} : δ c = .read p f →
      Skeleton δ (f y) t b → Skeleton δ c ((k,.read p y)::t) b

/-- Independent operational rules act on one actual register. The writer rule
neither inspects nor changes control and is not an instruction issued by δ. -/
inductive Run {C : Type} (δ : C → Op C) : C → Source → Word → C → Prop
  | ret {c U} : δ c = .ret → Run δ c U [.observer .ret] c
  | localStep {c d U t b} : δ c = .localStep d →
      Run δ d U t b → Run δ c U (.observer .localStep::t) b
  | read {c U p f y t b} : δ c = .read p f → readout p U = y →
      Run δ (f y) U t b → Run δ c U (.observer (.read p y)::t) b
  | update {c U t b} : Run δ c (substitution U) t b →
      Run δ c U (.update::t) b

/-- This syntax depends only on the erased skeleton. Each event has its own
unknown epoch variable, including local steps and Return. -/
def constraint (i : Nat) : List ObserverEvent → Formula
  | [] => .equal (.of (.inl true)) (.of (.inl true))
  | .read p y::t => .both (compile p y (original i)) (constraint (i+1) t)
  | _::t => constraint (i+1) t

/-- Exact cumulative counts of the supplied finite bursts; η is not observer
input. Counts at all observer events are retained, even when no Read occurs. -/
def Chronology (e i : Nat) : TimedWord → (Nat → Nat) → Prop
  | [], _ => True
  | (k,_)::t, η => η i = e+k ∧ Chronology (e+k) (i+1) t η

private theorem chronology_congr (e i : Nat) (t : TimedWord) (η ζ : Nat → Nat)
    (same : ∀ n, i ≤ n → η n = ζ n) (h : Chronology e i t η) :
    Chronology e i t ζ := by
  induction t generalizing e i with
  | nil => trivial
  | cons a t ih =>
    rcases a with ⟨k,a⟩
    exact ⟨(same i le_rfl).symm.trans h.1,
      ih (e+k) (i+1) (fun n hn => same n (by omega)) h.2⟩

private theorem chronology_exists (e i : Nat) (t : TimedWord) :
    ∃ η : Nat → Nat, Chronology e i t η := by
  induction t generalizing e i with
  | nil => exact ⟨fun _ => 0, trivial⟩
  | cons a t ih =>
    rcases a with ⟨k,a⟩
    obtain ⟨η,hη⟩ := ih (e+k) (i+1)
    let ζ := fun n => if n = i then e+k else η n
    refine ⟨ζ, by simp [ζ], ?_⟩
    apply chronology_congr (e+k) (i+1) t η ζ _ hη
    intro n hn
    simp only [ζ, if_neg (show n ≠ i by omega)]

theorem updates_iff {C : Type} (δ : C → Op C) (k : Nat)
    (c : C) (U : Source) (t : Word) (b : C) :
    Run δ c U (List.replicate k .update ++ t) b ↔
      Run δ c (substitution^[k] U) t b := by
  induction k generalizing U with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append]
      constructor
      · intro h
        cases h with
        | update h =>
          simpa only [Function.iterate_succ_apply] using (ih (substitution U)).mp h
      · intro h
        apply Run.update
        apply (ih (substitution U)).mpr
        simpa only [Function.iterate_succ_apply] using h

/-- Satisfied finite native constraints construct an actual independently
scheduled execution, and actual expansion is sufficient for those constraints.
Every local step, literal reply and separate Return is retained. -/
private theorem exact_execution {C : Type} {δ : C → Op C} {c b : C} {t : TimedWord}
    (s : Skeleton δ c t b) (u : Source) (e i : Nat) (η : Nat → Nat)
    (x : Nat → Source) (hc : Chronology e i t η) :
    (constraint i (t.map Prod.snd)).Holds u η x ↔
      Run δ c (substitution^[e] u) (expand t) b := by
  induction s generalizing e i with
  | @ret c k h =>
      simp only [List.map_cons, List.map_nil, constraint, Formula.Holds, expand,
        updates_iff, value]
      constructor
      · intro _; exact Run.ret h
      · intro _; trivial
  | @localStep c d k t b h s ih =>
      simp only [List.map_cons, constraint, expand, updates_iff,
        ih (e+k) (i+1) hc.2]
      rw [← Function.iterate_add_apply, Nat.add_comm k e]
      constructor
      · intro q; exact Run.localStep h q
      · intro q
        cases q with
        | localStep h' q =>
          have hd := Op.localStep.inj (h.symm.trans h')
          cases hd
          exact q
  | @read c p f y k t b h s ih =>
      simp only [List.map_cons, constraint, Formula.Holds, compile_exact, value,
        original, expand, updates_iff, ih (e+k) (i+1) hc.2, hc.1]
      rw [← Function.iterate_add_apply, Nat.add_comm k e]
      constructor
      · rintro ⟨hy,q⟩; exact Run.read h hy q
      · intro q
        cases q with
        | read h' hy q =>
          obtain ⟨hp,hf⟩ := Op.read.inj (h.symm.trans h')
          cases hp
          cases hf
          exact ⟨hy,q⟩

/-- Finite chronology imposes no upper bound and constrains no coordinate
outside the supplied finite skeleton. -/
def Ordered (e i : Nat) : List ObserverEvent → (Nat → Nat) → Prop
  | [], _ => True
  | _::t, η => e ≤ η i ∧ Ordered (η i) (i+1) t η

/-- Insert the successive epoch differences immediately before each event. -/
def retime (e i : Nat) : List ObserverEvent → (Nat → Nat) → TimedWord
  | [], _ => []
  | a::t, η => (η i-e,a) :: retime (η i) (i+1) t η

private theorem retime_correct {C : Type} {δ : C → Op C} {c b : C} {t : TimedWord}
    (s : Skeleton δ c t b) (e i : Nat) (η : Nat → Nat)
    (ho : Ordered e i (t.map Prod.snd) η) :
    Skeleton δ c (retime e i (t.map Prod.snd) η) b ∧
      Chronology e i (retime e i (t.map Prod.snd) η) η ∧
      (retime e i (t.map Prod.snd) η).map Prod.snd = t.map Prod.snd := by
  induction s generalizing e i with
  | ret h =>
    refine ⟨Skeleton.ret h, ⟨?_, trivial⟩, rfl⟩
    have he := ho.1
    omega
  | localStep h s ih =>
    obtain ⟨s',hc,hm⟩ := ih (η i) (i+1) ho.2
    refine ⟨Skeleton.localStep h s', ⟨?_, ?_⟩, ?_⟩
    · have he := ho.1; omega
    · simpa only [Nat.add_sub_of_le ho.1] using hc
    · simpa only [List.map_cons, retime] using congrArg (ObserverEvent.localStep::·) hm
  | read h s ih =>
    obtain ⟨s',hc,hm⟩ := ih (η i) (i+1) ho.2
    refine ⟨Skeleton.read h s', ⟨?_, ?_⟩, ?_⟩
    · have he := ho.1; omega
    · simpa only [Nat.add_sub_of_le ho.1] using hc
    · simpa only [List.map_cons, retime] using congrArg (ObserverEvent.read _ _::·) hm

/-- Every finite chronological epoch vector is realized by independent finite
writer bursts. The finite native formula depends only on observer events and
retains one unknown epoch variable per event, including the separate Return. -/
theorem chronological_execution {C : Type} {δ : C → Op C} {c b : C} {t : TimedWord}
    (s : Skeleton δ c t b) (u : Source) (e i : Nat) (η : Nat → Nat)
    (x : Nat → Source) (ho : Ordered e i (t.map Prod.snd) η) :
    (constraint i (t.map Prod.snd)).Holds u η x ↔
      Run δ c (substitution^[e] u) (expand (retime e i (t.map Prod.snd) η)) b := by
  obtain ⟨s',hc,hm⟩ := retime_correct s e i η ho
  simpa only [hm] using exact_execution s' u e i η x hc

/-- Erasure counts every update since the preceding observer event. -/
def erase : Word → TimedWord
  | [] => []
  | .observer a :: t => (0,a) :: erase t
  | .update :: t => match erase t with
    | [] => []
    | (k,a)::s => (k+1,a)::s

private theorem erase_burst (k : Nat) (a : ObserverEvent) (t : Word) :
    erase (List.replicate k .update ++ .observer a :: t) = (k,a)::erase t := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, erase, ih]

private theorem erase_expand (t : TimedWord) : erase (expand t) = t := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    rcases a with ⟨k,a⟩
    simp only [expand, erase_burst, ih]

private theorem recover_word {C : Type} {δ : C → Op C} {c b : C}
    {U : Source} {h : Word} (r : Run δ c U h b) :
    Skeleton δ c (erase h) b ∧ expand (erase h) = h := by
  induction r with
  | ret h => exact ⟨Skeleton.ret h, rfl⟩
  | localStep h r ih =>
    exact ⟨Skeleton.localStep h ih.1, by simpa [erase, expand] using
      (congrArg (Event.observer .localStep :: ·) ih.2)⟩
  | @read c U p f y t b h hy r ih =>
    exact ⟨Skeleton.read h ih.1, by simpa [erase, expand] using
      (congrArg (Event.observer (.read p y) :: ·) ih.2)⟩
  | @update c U t b r ih =>
    rcases ih with ⟨hs,he⟩
    cases ht : erase t with
    | nil => rw [ht] at hs; cases hs
    | cons a tail =>
      rcases a with ⟨k,a⟩
      rw [ht] at hs he
      simp only [erase, ht]
      refine ⟨?_, ?_⟩
      · cases hs with
        | ret h => exact Skeleton.ret h
        | localStep h s => exact Skeleton.localStep h s
        | read h s => exact Skeleton.read h s
      · simp only [expand, List.replicate_succ, List.cons_append]
        exact congrArg (Event.update :: ·) he

/-- All-source active histories are recovered exactly, including update placement
before local steps and Return. The syntax retains the same original source. -/
private theorem active_history_relation {C : Type} (δ : C → Op C) (c b : C)
    (u : Source) (h : Word) (x : Nat → Source) :
    Run δ c u h b ↔ ∃ (t : TimedWord) (η : Nat → Nat), Skeleton δ c t b ∧
      Chronology 0 0 t η ∧ (constraint 0 (t.map Prod.snd)).Holds u η x ∧
      expand t = h ∧ erase h = t := by
  constructor
  · intro r
    obtain ⟨s,he⟩ := recover_word r
    obtain ⟨η,hη⟩ := chronology_exists 0 0 (erase h)
    refine ⟨erase h,η,s,hη,?_,he,rfl⟩
    apply (exact_execution s u 0 0 η x hη).mpr
    simpa only [Function.iterate_zero_apply, he] using r
  · rintro ⟨t,η,s,hη,hc,he,_⟩
    have r := (exact_execution s u 0 0 η x hη).mp hc
    simpa only [Function.iterate_zero_apply, he] using r

/-- Exact raw-history recovery also gives every source/designated-epoch
projection. The projection may retain any fixed finite set of event roles. -/
theorem native_history_correspondence {C : Type} (δ : C → Op C) (c b : C)
    (u : Source) (x : Nat → Source) :
    (∀ t : TimedWord, erase (expand t) = t) ∧
    (∀ h : Word, Run δ c u h b ↔
      ∃ (t : TimedWord) (η : Nat → Nat), Skeleton δ c t b ∧ Chronology 0 0 t η ∧
        (constraint 0 (t.map Prod.snd)).Holds u η x ∧ expand t = h ∧ erase h = t) ∧
    (∀ (D : Type) (π : TimedWord → D) (d : D),
      (∃ h : Word, Run δ c u h b ∧ π (erase h) = d) ↔
      ∃ (t : TimedWord) (η : Nat → Nat), Skeleton δ c t b ∧ Chronology 0 0 t η ∧
        (constraint 0 (t.map Prod.snd)).Holds u η x ∧ π t = d) := by
  refine ⟨erase_expand, fun h => active_history_relation δ c b u h x, ?_⟩
  intro D π d
  constructor
  · rintro ⟨h,r,hπ⟩
    obtain ⟨t,η,s,hη,hc,he,hr⟩ := (active_history_relation δ c b u h x).mp r
    exact ⟨t,η,s,hη,hc,by simpa only [hr] using hπ⟩
  · rintro ⟨t,η,s,hη,hc,hπ⟩
    refine ⟨expand t,?_,by simpa only [erase_expand] using hπ⟩
    simpa only [Function.iterate_zero_apply] using
      (exact_execution s u 0 0 η x hη).mp hc

/-- Finite instruction data retain all four continuations. A natural control
encodes the entire accessible finite configuration, with no size bound. -/
abbrev Instruction := (Address × (Nat × Nat × Nat × Nat)) ⊕ (Nat ⊕ Unit)

def continuation (k : Nat × Nat × Nat × Nat) : Reply → Nat
  | .alpha => k.1
  | .beta => k.2.1
  | .branch => k.2.2.1
  | .absent => k.2.2.2

def instruction : Instruction → Op Nat
  | .inl (p,k) => .read p (continuation k)
  | .inr (.inl c) => .localStep c
  | .inr (.inr _) => .ret

/-- A finite recursive code realizes each single microstep, rather than the
next external action after a potentially divergent sequence of local steps. -/
structure EffectiveProgram where
  code : Nat.Partrec.Code
  step : Nat → Instruction
  realizes : ∀ c, code.eval c = Part.some (Encodable.encode (step c))

def EffectiveProgram.transition (P : EffectiveProgram) (c : Nat) : Op Nat :=
  instruction (P.step c)

def evalInstruction (code : Nat.Partrec.Code) (fuel c : Nat) : Option Instruction :=
  (code.evaln fuel c).bind Encodable.decode

private theorem eval_instruction_sound (P : EffectiveProgram) (fuel c : Nat)
    (a : Instruction) (h : evalInstruction P.code fuel c = some a) : a = P.step c := by
  obtain ⟨n,hn,hd⟩ := Option.bind_eq_some_iff.mp h
  have hm := Nat.Partrec.Code.evaln_sound (show n ∈ P.code.evaln fuel c from hn)
  rw [P.realizes] at hm
  have he : n = Encodable.encode (P.step c) := by simpa using hm
  subst n
  simpa only [Encodable.encodek, Option.some.injEq] using hd.symm

private theorem eval_instruction_eventual (P : EffectiveProgram) (c : Nat) :
    ∃ n, ∀ fuel, n ≤ fuel → evalInstruction P.code fuel c = some (P.step c) := by
  have hm : Encodable.encode (P.step c) ∈ P.code.eval c := by rw [P.realizes]; simp
  obtain ⟨n,hn⟩ := Nat.Partrec.Code.evaln_complete.mp hm
  refine ⟨n, fun fuel hf => ?_⟩
  have he := Nat.Partrec.Code.evaln_mono hf hn
  simp only [evalInstruction, show P.code.evaln fuel c =
    some (Encodable.encode (P.step c)) from he, Option.bind_some, Encodable.encodek]

def replies : List Reply := [.alpha,.beta,.branch,.absent]

/-- Every call is finite, even on a divergent hypothetical branch. The two
independent bounds limit evaluator work per microstep and branch depth. -/
def enumerate (code : Nat.Partrec.Code) (fuel : Nat) :
    Nat → Nat → List (List ObserverEvent × Nat)
  | 0, _ => []
  | n+1, c => match evalInstruction code fuel c with
    | none => []
    | some (.inr (.inr _)) => [([.ret],c)]
    | some (.inr (.inl d)) =>
        (enumerate code fuel n d).map (fun q => (.localStep::q.1,q.2))
    | some (.inl (p,k)) => replies.flatMap (fun y =>
        (enumerate code fuel n (continuation k y)).map
          (fun q => (.read p y::q.1,q.2)))

private theorem enumerate_sound (P : EffectiveProgram) (fuel n c : Nat)
    (w : List ObserverEvent) (b : Nat)
    (h : (w,b) ∈ enumerate P.code fuel n c) :
    Skeleton P.transition c (w.map (fun a => (0,a))) b := by
  induction n generalizing c w b with
  | zero => simp [enumerate] at h
  | succ n ih =>
    cases ha : evalInstruction P.code fuel c with
    | none => simp [enumerate,ha] at h
    | some a =>
      have hs := eval_instruction_sound P fuel c a ha
      have ht : P.transition c = instruction a := by rw [EffectiveProgram.transition,← hs]
      cases a with
      | inl a =>
        rcases a with ⟨p,k⟩
        simp only [enumerate,ha] at h
        obtain ⟨y,_,hy⟩ := List.mem_flatMap.mp h
        obtain ⟨q,hq,he⟩ := List.mem_map.mp hy
        cases he
        exact Skeleton.read ht (ih _ _ _ hq)
      | inr a => cases a with
        | inl d =>
          simp only [enumerate,ha] at h
          obtain ⟨q,hq,he⟩ := List.mem_map.mp h
          cases he
          exact Skeleton.localStep ht (ih _ _ _ hq)
        | inr r =>
          have he : (w,b) = ([.ret],c) := by simpa [enumerate,ha] using h
          cases he
          exact Skeleton.ret ht

private theorem enumerate_complete (P : EffectiveProgram) {c b : Nat} {t : TimedWord}
    (s : Skeleton P.transition c t b) :
    ∃ n, ∀ fuel, n ≤ fuel →
      (t.map Prod.snd,b) ∈ enumerate P.code fuel t.length c := by
  induction s with
  | @ret c k h =>
    obtain ⟨n,hn⟩ := eval_instruction_eventual P c
    refine ⟨n, fun fuel hf => ?_⟩
    cases ha : P.step c with
    | inl a => simp [EffectiveProgram.transition,instruction,ha] at h
    | inr a => cases a with
      | inl d => simp [EffectiveProgram.transition,instruction,ha] at h
      | inr r => simp [enumerate,hn fuel hf,ha]
  | @localStep c d k t b h s ih =>
    obtain ⟨n,hn⟩ := eval_instruction_eventual P c
    obtain ⟨m,hm⟩ := ih
    refine ⟨max n m, fun fuel hf => ?_⟩
    have hn' := hn fuel (le_trans (le_max_left n m) hf)
    have hm' := hm fuel (le_trans (le_max_right n m) hf)
    cases ha : P.step c with
    | inl a => simp [EffectiveProgram.transition,instruction,ha] at h
    | inr a => cases a with
      | inl d' =>
        have hd : d' = d := by simpa [EffectiveProgram.transition,instruction,ha] using h
        subst d'
        simpa [enumerate,hn',ha] using hm'
      | inr r => simp [EffectiveProgram.transition,instruction,ha] at h
  | @read c p f y k t b h s ih =>
    obtain ⟨n,hn⟩ := eval_instruction_eventual P c
    obtain ⟨m,hm⟩ := ih
    refine ⟨max n m, fun fuel hf => ?_⟩
    have hn' := hn fuel (le_trans (le_max_left n m) hf)
    have hm' := hm fuel (le_trans (le_max_right n m) hf)
    cases ha : P.step c with
    | inl a =>
      rcases a with ⟨p',k'⟩
      have he : p' = p ∧ continuation k' = f := by
        simpa [EffectiveProgram.transition,instruction,ha] using h
      rcases he with ⟨rfl,rfl⟩
      simp only [List.length_cons,List.map_cons,enumerate,hn',ha]
      apply List.mem_flatMap.mpr
      refine ⟨y,by cases y <;> simp [replies],List.mem_map.mpr ?_⟩
      exact ⟨(t.map Prod.snd,b),hm',rfl⟩
    | inr a => cases a <;> simp [EffectiveProgram.transition,instruction,ha] at h

/-- Zero bursts mark an erased word; chronology supplies its actual scheduling. -/
def untimed (w : List ObserverEvent) : TimedWord := w.map (fun a => (0,a))

/-- Bounded code exploration enumerates exactly the returning skeletons, and
every enumerated skeleton has the exact independent-writer native semantics.
Neither code fuel nor microstep depth has a uniform bound. -/
theorem effective_native_correspondence (P : EffectiveProgram) (c b : Nat)
    (w : List ObserverEvent) :
    (∃ fuel n, (w,b) ∈ enumerate P.code fuel n c) ↔
    Skeleton P.transition c (untimed w) b ∧
      ∀ (u : Source) (η : Nat → Nat) (x : Nat → Source), Ordered 0 0 w η →
        ((constraint 0 w).Holds u η x ↔
          Run P.transition c u (expand (retime 0 0 w η)) b) := by
  constructor
  · rintro ⟨fuel,n,h⟩
    have s := enumerate_sound P fuel n c w b h
    refine ⟨s, fun u η x ho => ?_⟩
    simpa [List.map_map,Function.comp_def]
      using chronological_execution s u 0 0 η x (by simpa using ho)
  · rintro ⟨s,_⟩
    obtain ⟨n,hn⟩ := enumerate_complete P s
    refine ⟨n,w.length,?_⟩
    simpa [untimed] using hn n le_rfl

end D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution
