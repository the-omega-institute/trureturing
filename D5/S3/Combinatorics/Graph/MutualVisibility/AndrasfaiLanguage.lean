/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: The four-state partial automaton reads exactly the finite words avoiding the full forbidden family. -/

import Mathlib.Computability.DFA
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! State four is an absorbing rejection state used to present the original
partial four-state machine as a standard Mathlib DFA. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage

/-- The Kleene star of the wildcard triple language Sigma Sigma 1. -/
inductive Triples : List Bool → Prop
  | nil : Triples []
  | snoc {w : List Bool} : Triples w → (a b : Bool) → Triples (w ++ [a,b,true])

/-- An occurrence of 11 (Sigma Sigma 1)* 1, with arbitrary prefix and suffix. -/
def ContainsForbidden (w : List Bool) : Prop :=
  ∃ p t s : List Bool, Triples t ∧ w = p ++ [true,true] ++ t ++ [true] ++ s

private def step (q : Fin 5) (b : Bool) : Fin 5 :=
  if q=0 then if b then 1 else 0 else
  if q=1 then if b then 2 else 0 else
  if q=2 then if b then 4 else 3 else
  if q=3 then 1 else 4

/-- The original four-state transition table with one explicit absorbing failure state. -/
def machine : DFA Bool (Fin 5) where
  step := step
  start := 0
  accept := {q | q ≠ 4}

private theorem reject_absorbing (w : List Bool) : machine.evalFrom 4 w = 4 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simpa [DFA.evalFrom_cons, machine, step] using ih

private theorem two_ones (q : Fin 5) :
    machine.evalFrom q [true,true] = 2 ∨ machine.evalFrom q [true,true] = 4 := by
  fin_cases q <;> decide

private theorem triples_from_two {w : List Bool} (hw : Triples w) :
    machine.evalFrom 2 w = 2 ∨ machine.evalFrom 2 w = 4 := by
  induction hw with
  | nil => exact Or.inl rfl
  | @snoc w hw a b ih =>
    rw [DFA.evalFrom_of_append]
    rcases ih with h | h
    · rw [h]; cases a <;> cases b <;> decide
    · rw [h, reject_absorbing]; exact Or.inr rfl

private theorem forbidden_rejected (w : List Bool) (hw : ContainsForbidden w)
    (q : Fin 5) : machine.evalFrom q w = 4 := by
  obtain ⟨p,t,s,ht,rfl⟩ := hw
  simp only [DFA.evalFrom_of_append]
  rcases two_ones (machine.evalFrom q p) with h | h
  · rw [h]
    rcases triples_from_two ht with h | h
    · rw [h]
      change machine.evalFrom 4 s = 4
      exact reject_absorbing s
    · rw [h, reject_absorbing, reject_absorbing]
  · rw [h, reject_absorbing, reject_absorbing, reject_absorbing]

private def Marked (w : List Bool) : Prop :=
  ∃ p t : List Bool, Triples t ∧ w = p ++ [true,true] ++ t

private def Invariant (w : List Bool) (q : Fin 5) : Prop :=
  if q=1 then (∃ p, w=p++[true]) ∨ (∃ p, Marked p ∧ w=p++[false,false]) else
  if q=2 then Marked w else
  if q=3 then ∃ p, Marked p ∧ w=p++[false] else
  if q=4 then ContainsForbidden w else True

private theorem marked_append (w : List Bool) (hw : Marked w) (a b : Bool) :
    Marked (w++[a,b,true]) := by
  obtain ⟨p,t,ht,rfl⟩ := hw
  exact ⟨p,t++[a,b,true],Triples.snoc ht a b, by simp [List.append_assoc]⟩

private theorem forbidden_append (w : List Bool) (hw : ContainsForbidden w) (b : Bool) :
    ContainsForbidden (w++[b]) := by
  obtain ⟨p,t,s,ht,rfl⟩ := hw
  exact ⟨p,t,s++[b],ht,by simp [List.append_assoc]⟩

private theorem invariant_step (w : List Bool) (q : Fin 5) (b : Bool)
    (h : Invariant w q) : Invariant (w++[b]) (step q b) := by
  fin_cases q <;> cases b
  · trivial
  · exact Or.inl ⟨w,rfl⟩
  · trivial
  · change (∃ p, w=p++[true]) ∨ (∃ p, Marked p ∧ w=p++[false,false]) at h
    change Marked (w++[true])
    rcases h with ⟨p,rfl⟩ | ⟨p,hp,rfl⟩
    · exact ⟨p,[],Triples.nil,by simp [List.append_assoc]⟩
    · simpa [List.append_assoc] using marked_append p hp false false
  · exact ⟨w,h,rfl⟩
  · change Marked w at h
    change ContainsForbidden (w++[true])
    obtain ⟨p,t,ht,rfl⟩ := h
    exact ⟨p,t,[],ht,by simp [List.append_assoc]⟩
  · change ∃ p, Marked p ∧ w=p++[false] at h
    obtain ⟨p,hp,rfl⟩ := h
    exact Or.inr ⟨p,hp,by simp [List.append_assoc]⟩
  · exact Or.inl ⟨w,rfl⟩
  · exact forbidden_append w h false
  · exact forbidden_append w h true

private theorem run_invariant (w : List Bool) : Invariant w (machine.eval w) := by
  induction w using List.reverseRecOn with
  | nil => trivial
  | append_singleton w b ih =>
    rw [DFA.eval_append_singleton]
    exact invariant_step w (machine.eval w) b ih

/-- Finite readability is exactly avoidance of the entire Kleene-star family. -/
theorem accepts_iff_avoids (w : List Bool) :
    w ∈ machine.accepts ↔ ¬ ContainsForbidden w := by
  change machine.eval w ≠ 4 ↔ ¬ ContainsForbidden w
  constructor
  · intro h hf
    exact h (forbidden_rejected w hf 0)
  · intro h he
    have hi := run_invariant w
    rw [he] at hi
    exact h hi

private def pairRank (q r : Fin 5) : ℕ :=
  if (q=2 ∧ r=3) ∨ (q=3 ∧ r=2) then 2 else
  if (q=0 ∧ r=2) ∨ (q=2 ∧ r=0) ∨ (q=1 ∧ r=3) ∨ (q=3 ∧ r=1) then 1 else 0

private def pairPhase (q r : Fin 5) : ZMod 3 :=
  if (q=0 ∧ r=1) ∨ (q=1 ∧ r=0) then 0 else
  if (q=1 ∧ r=2) ∨ (q=2 ∧ r=1) then 1 else 2

private theorem pair_step_properties : ∀ (q r : Fin 5) (b : Bool),
    q ≠ 4 → r ≠ 4 → q ≠ r → step q b ≠ 4 → step r b ≠ 4 → step q b ≠ step r b →
    pairRank (step q b) (step r b) ≤ pairRank q r ∧
    (pairRank (step q b) (step r b) = pairRank q r → pairRank q r = 0) ∧
    (pairRank q r = 0 → pairPhase (step q b) (step r b) = pairPhase q r+1) := by
  decide +kernel

private theorem initial_not_reject (w : List Bool) (q : Fin 5)
    (h : machine.evalFrom q w ≠ 4) : q ≠ 4 := by
  intro he
  subst q
  exact h (reject_absorbing w)

private theorem initial_distinct (w : List Bool) (q r : Fin 5)
    (h : machine.evalFrom q w ≠ machine.evalFrom r w) : q ≠ r := by
  intro he
  subst r
  exact h rfl

private theorem pair_rank_mono (w : List Bool) (q r : Fin 5)
    (hq : machine.evalFrom q w ≠ 4) (hr : machine.evalFrom r w ≠ 4)
    (hqr : machine.evalFrom q w ≠ machine.evalFrom r w) :
    pairRank (machine.evalFrom q w) (machine.evalFrom r w) ≤ pairRank q r := by
  induction w generalizing q r with
  | nil => exact le_rfl
  | cons b w ih =>
    change machine.evalFrom (step q b) w ≠ 4 at hq
    change machine.evalFrom (step r b) w ≠ 4 at hr
    change machine.evalFrom (step q b) w ≠ machine.evalFrom (step r b) w at hqr
    have hqs := initial_not_reject w _ hq
    have hrs := initial_not_reject w _ hr
    have hqrs := initial_distinct w _ _ hqr
    have hq0 := initial_not_reject (b::w) q hq
    have hr0 := initial_not_reject (b::w) r hr
    have hqr0 := initial_distinct (b::w) q r hqr
    exact (ih _ _ hq hr hqr).trans
      (pair_step_properties q r b hq0 hr0 hqr0 hqs hrs hqrs).1

private theorem pair_phase_run (w : List Bool) (q r : Fin 5)
    (hq : machine.evalFrom q w ≠ 4) (hr : machine.evalFrom r w ≠ 4)
    (hqr : machine.evalFrom q w ≠ machine.evalFrom r w) (hzero : pairRank q r = 0) :
    pairPhase (machine.evalFrom q w) (machine.evalFrom r w) =
      pairPhase q r + (w.length : ZMod 3) := by
  induction w generalizing q r with
  | nil => simp
  | cons b w ih =>
    change machine.evalFrom (step q b) w ≠ 4 at hq
    change machine.evalFrom (step r b) w ≠ 4 at hr
    change machine.evalFrom (step q b) w ≠ machine.evalFrom (step r b) w at hqr
    have hs := pair_step_properties q r b
      (initial_not_reject (b::w) q hq) (initial_not_reject (b::w) r hr)
      (initial_distinct (b::w) q r hqr)
      (initial_not_reject w _ hq) (initial_not_reject w _ hr)
      (initial_distinct w _ _ hqr)
    have hz : pairRank (step q b) (step r b) = 0 := by omega
    have hi := ih _ _ hq hr hqr hz
    change pairPhase (machine.evalFrom (step q b) w) (machine.evalFrom (step r b) w) = _
    rw [hi,hs.2.2 hzero]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

/-- At lengths not divisible by three, a labelled word admits at most one
nonrejecting closed lift. The starting position is fixed, with no rotation quotient. -/
theorem closed_run_unique (w : List Bool) (hlen : w.length % 3 ≠ 0)
    (q r : Fin 5) (hq : q ≠ 4) (hr : r ≠ 4)
    (hqc : machine.evalFrom q w = q) (hrc : machine.evalFrom r w = r) : q = r := by
  by_contra hne
  have hqe : machine.evalFrom q w ≠ 4 := by rwa [hqc]
  have hre : machine.evalFrom r w ≠ 4 := by rwa [hrc]
  have he : machine.evalFrom q w ≠ machine.evalFrom r w := by rwa [hqc,hrc]
  have hz : pairRank q r = 0 := by
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have hqs := initial_not_reject w (step q b) hqe
      have hrs := initial_not_reject w (step r b) hre
      have hqrs := initial_distinct w (step q b) (step r b) he
      have hs := pair_step_properties q r b hq hr hne hqs hrs hqrs
      have hm := pair_rank_mono w (step q b) (step r b) hqe hre he
      change pairRank (machine.evalFrom q (b::w)) (machine.evalFrom r (b::w)) ≤ _ at hm
      rw [hqc,hrc] at hm
      exact hs.2.1 (Nat.le_antisymm hs.1 hm)
  have hp := pair_phase_run w q r hqe hre he hz
  rw [hqc,hrc] at hp
  have hcast : (w.length : ZMod 3) = 0 := by linear_combination -hp
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast,ZMod.val_zero] at hv
  exact hlen hv

private def HasDouble (w : List Bool) : Prop :=
  ∃ p s, w = p ++ [true,true] ++ s

private theorem double_append {w : List Bool} (h : HasDouble w) (s : List Bool) :
    HasDouble (w++s) := by
  obtain ⟨p,t,rfl⟩ := h
  exact ⟨p,t++s,by simp [List.append_assoc]⟩

private theorem marked_double {w : List Bool} (h : Marked w) : HasDouble w := by
  obtain ⟨p,t,ht,rfl⟩ := h
  exact ⟨p,t,rfl⟩

private theorem forbidden_double {w : List Bool} (h : ContainsForbidden w) : HasDouble w := by
  obtain ⟨p,t,s,ht,rfl⟩ := h
  exact ⟨p,t++[true]++s,by simp [List.append_assoc]⟩

private theorem run_low_of_no_double (w : List Bool) (hn : ¬ HasDouble w) :
    machine.eval w = 0 ∨ machine.eval w = 1 := by
  have hi := run_invariant w
  generalize he : machine.eval w = q at hi ⊢
  fin_cases q
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (hn (marked_double hi)).elim
  · change ∃ p, Marked p ∧ w=p++[false] at hi
    obtain ⟨p,hp,rfl⟩ := hi
    exact (hn (double_append (marked_double hp) [false])).elim
  · exact (hn (forbidden_double hi)).elim

private theorem run_one_ends_one (w : List Bool) (hn : ¬ HasDouble w)
    (he : machine.eval w = 1) : ∃ p, w=p++[true] := by
  have hi := run_invariant w
  rw [he] at hi
  change (∃ p, w=p++[true]) ∨ (∃ p, Marked p ∧ w=p++[false,false]) at hi
  rcases hi with h | ⟨p,hp,rfl⟩
  · exact h
  · exact (hn (double_append (marked_double hp) [false,false])).elim

private theorem last_one_not_zero (w : List Bool) : machine.eval (w++[true]) ≠ 0 := by
  rw [DFA.eval_append_singleton]
  generalize machine.eval w = q
  fin_cases q <;> decide

private theorem double_synchronizes (w : List Bool) (hw : HasDouble w)
    (q r : Fin 5) (hq : machine.evalFrom q w ≠ 4)
    (hr : machine.evalFrom r w ≠ 4) : machine.evalFrom q w = machine.evalFrom r w := by
  obtain ⟨p,s,rfl⟩ := hw
  simp only [DFA.evalFrom_of_append] at hq hr ⊢
  rcases two_ones (machine.evalFrom q p) with hq2 | hq4
  · rcases two_ones (machine.evalFrom r p) with hr2 | hr4
    · rw [hq2,hr2]
    · exact (hr (by rw [hr4,reject_absorbing])).elim
  · exact (hq (by rw [hq4,reject_absorbing])).elim

private def copies (w : List Bool) : ℕ → List Bool
  | 0 => []
  | k+1 => copies w k ++ w

/-- Every finite block of repeated periods avoids the original full forbidden family. -/
def PeriodicAvoidance (w : List Bool) : Prop := ∀ k, ¬ ContainsForbidden (copies w k)

private theorem periodic_has_closed_run (w : List Bool) (hp : PeriodicAvoidance w) :
    ∃ q : Fin 5, q ≠ 4 ∧ machine.evalFrom q w = q := by
  have hg (k : ℕ) : machine.evalFrom 0 (copies w k) ≠ 4 := by
    exact (accepts_iff_avoids _).mpr (hp k)
  by_cases hd : HasDouble (w++w)
  · let q := machine.evalFrom 0 (w++w)
    have hq : q ≠ 4 := by simpa [q,copies] using hg 2
    have hq4 : machine.evalFrom q (w++w) ≠ 4 := by
      simpa [q,copies,DFA.evalFrom_of_append] using hg 4
    have hqq : machine.evalFrom q (w++w) = q :=
      double_synchronizes (w++w) hd q 0 hq4 hq
    have ht : machine.evalFrom q w ≠ 4 := by
      simpa [q,copies,DFA.evalFrom_of_append] using hg 3
    have htf : machine.evalFrom (machine.evalFrom q w) (w++w) =
        machine.evalFrom q w := by
      have hh := congrArg (fun z => machine.evalFrom z w) hqq
      simpa only [DFA.evalFrom_of_append] using hh
    have htfne : machine.evalFrom (machine.evalFrom q w) (w++w) ≠ 4 := by
      rw [htf]
      exact ht
    have hfix := double_synchronizes (w++w) hd (machine.evalFrom q w) 0 htfne hq
    rw [htf] at hfix
    exact ⟨q,hq,hfix⟩
  · have hn : ¬ HasDouble w := fun h => hd (double_append h w)
    rcases run_low_of_no_double w hn with h0 | h1
    · exact ⟨0,by decide,h0⟩
    · obtain ⟨p,he⟩ := run_one_ends_one w hn h1
      have heval : machine.eval (w++w) = 1 := by
        rcases run_low_of_no_double (w++w) hd with h0 | h11
        · have hl := last_one_not_zero (w++p)
          have ha : w++w = (w++p)++[true] := by rw [he]; simp [List.append_assoc]
          rw [ha] at h0
          exact (hl h0).elim
        · exact h11
      refine ⟨1,by decide,?_⟩
      change machine.evalFrom 0 (w++w) = 1 at heval
      rw [DFA.evalFrom_of_append] at heval
      change machine.evalFrom (machine.eval w) w = 1 at heval
      rwa [h1] at heval

/-- Periodic avoidance is equivalent to a unique nonrejecting closed lift
when the period length is not divisible by three; the labelled origin is fixed. -/
theorem exists_unique_closed_run (w : List Bool) (hlen : w.length % 3 ≠ 0) :
    PeriodicAvoidance w ↔ ∃! q : Fin 5, q ≠ 4 ∧ machine.evalFrom q w = q := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqc⟩ := periodic_has_closed_run w hp
    refine ⟨q,⟨hq,hqc⟩,?_⟩
    intro r hr
    exact closed_run_unique w hlen r q hr.1 hq hr.2 hqc
  · rintro ⟨q,⟨hq,hqc⟩,_⟩
    have hc (k : ℕ) : machine.evalFrom q (copies w k) = q := by
      induction k with
      | zero => rfl
      | succ k ih => rw [copies,DFA.evalFrom_of_append,ih,hqc]
    intro k hk
    exact hq ((hc k).symm.trans (forbidden_rejected _ hk q))

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
