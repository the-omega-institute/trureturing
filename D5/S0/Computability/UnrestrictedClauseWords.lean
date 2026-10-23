/- GID: D5/S0/Computability/UnrestrictedClauseWords
   generality: G
   mirror-B: D5/B/S0/Computability/UnrestrictedClauseWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S0/Computability/UnrestrictedClauseWords.parser_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: Unrestricted original binary-name CNF decoding and charged finite parsing. -/

import D5.S0.Computability.ConventionalClauseWords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic.Unrestricted
open Conventional Turing StateTransition

/-- The original positive binary spellings, with no bound on their lengths. -/
def Canonical (F : Formula) : Prop :=
  ∀ c ∈ F, ∀ l ∈ c, l.1.head? = some true

/-- A cursor retains ordered clauses, literals, and the original name bits. -/
inductive Cursor
  | body (done : Formula)
  | bodyTag (done : Formula)
  | clause (done : Formula) (lits : Std.Sat.CNF.Clause Name)
  | clauseTag (done : Formula) (lits : Std.Sat.CNF.Clause Name)
  | polarity (done : Formula) (lits : Std.Sat.CNF.Clause Name)
  | firstTag (done : Formula) (lits : Std.Sat.CNF.Clause Name) (sign : Bool)
  | firstBit (done : Formula) (lits : Std.Sat.CNF.Clause Name) (sign : Bool)
  | nameTag (done : Formula) (lits : Std.Sat.CNF.Clause Name) (sign : Bool) (name : Name)
  | nameBit (done : Formula) (lits : Std.Sat.CNF.Clause Name) (sign : Bool) (name : Name)
  | ending (done : Formula)
  | dead
  deriving DecidableEq

def next : Cursor → Bool → Cursor
  | .body d, false => .bodyTag d
  | .bodyTag d, false => .ending d
  | .bodyTag d, true => .clause d .empty
  | .clause d c, true => .clauseTag d c
  | .clauseTag d c, false => .body (d ++ [c])
  | .clauseTag d c, true => .polarity d c
  | .polarity d c, b => .firstTag d c b
  | .firstTag d c p, true => .firstBit d c p
  | .firstBit d c p, true => .nameTag d c p [true]
  | .nameTag d c p n, false => .clause d (c ++ .ofLiterals [(n,p)])
  | .nameTag d c p n, true => .nameBit d c p n
  | .nameBit d c p n, b => .nameTag d c p (n ++ [b])
  | _, _ => .dead

def scan : Cursor → List Bool → Cursor
  | q, [] => q
  | q, b :: w => scan (next q b) w

def finish : Cursor → Option Formula
  | .ending d => some d
  | _ => none

/-- Total unrestricted decoder for exactly the unchanged conventional bytes. -/
def readWord (w : List Bool) : Option Formula := finish (scan (.body []) w)

private def consumed : Cursor → List Bool
  | .body d => d.flatMap clauseWord
  | .bodyTag d => d.flatMap clauseWord ++ [false]
  | .clause d c => d.flatMap clauseWord ++ [false,true] ++ c.literals.flatMap literalWord
  | .clauseTag d c => d.flatMap clauseWord ++ [false,true] ++ c.literals.flatMap literalWord ++ [true]
  | .polarity d c => d.flatMap clauseWord ++ [false,true] ++ c.literals.flatMap literalWord ++ [true,true]
  | .firstTag d c p => d.flatMap clauseWord ++ [false,true] ++
      c.literals.flatMap literalWord ++ [true,true,p]
  | .firstBit d c p => d.flatMap clauseWord ++ [false,true] ++
      c.literals.flatMap literalWord ++ [true,true,p,true]
  | .nameTag d c p n => d.flatMap clauseWord ++ [false,true] ++ c.literals.flatMap literalWord ++
      [true,true,p] ++ n.flatMap (fun b => [true,b])
  | .nameBit d c p n => d.flatMap clauseWord ++ [false,true] ++ c.literals.flatMap literalWord ++
      [true,true,p] ++ n.flatMap (fun b => [true,b]) ++ [true]
  | .ending d => formulaWord d
  | .dead => []

private def legal : Cursor → Prop
  | .body d | .bodyTag d | .ending d => Canonical d
  | .clause d c | .clauseTag d c | .polarity d c | .firstTag d c _ | .firstBit d c _ =>
      Canonical d ∧ ∀ l ∈ c, l.1.head? = some true
  | .nameTag d c _ n | .nameBit d c _ n =>
      (Canonical d ∧ ∀ l ∈ c, l.1.head? = some true) ∧ n.head? = some true
  | .dead => True

private theorem next_consumed (q : Cursor) (b : Bool) (h : next q b ≠ .dead) :
    consumed (next q b) = consumed q ++ [b] := by
  cases q <;> cases b <;>
    simp_all [next, consumed, formulaWord, clauseWord, literalWord, nameWord,
      List.flatMap_append, List.append_assoc]

private theorem next_legal (q : Cursor) (b : Bool) (h : legal q) : legal (next q b) := by
  cases q with
  | body d => cases b <;> first | exact h | trivial
  | bodyTag d =>
      cases b with
      | false => exact h
      | true => exact ⟨h, by simp⟩
  | clause d c => cases b <;> first | exact h | trivial
  | clauseTag d c =>
      cases b with
      | false =>
          intro e he l hl
          rcases List.mem_append.mp he with he | he
          · exact h.1 e he l hl
          · have he' : e = c := by simpa using he
            subst e
            exact h.2 l hl
      | true => exact h
  | polarity d c => cases b <;> exact h
  | firstTag d c p => cases b <;> first | exact h | trivial
  | firstBit d c p =>
      cases b with
      | false => trivial
      | true => exact ⟨h,rfl⟩
  | nameTag d c p n =>
      cases b with
      | false =>
          refine ⟨h.1.1, ?_⟩
          intro l hl
          change l ∈ (c ++ .ofLiterals [(n,p)]).literals at hl
          simp only [Std.Sat.CNF.Clause.literals_append,
            Std.Sat.CNF.Clause.literals_ofLiterals] at hl
          rcases List.mem_append.mp hl with hl | hl
          · exact h.1.2 l hl
          · have hl' : l = (n,p) := by simpa using hl
            subst l
            exact h.2
      | true => exact h
  | nameBit d c p n =>
      refine ⟨h.1, ?_⟩
      cases n with
      | nil => cases h.2
      | cons a n => simpa only [List.cons_append, List.head?_cons] using h.2
  | ending d => cases b <;> trivial
  | dead => cases b <;> trivial

private theorem scan_dead (w : List Bool) : scan .dead w = .dead := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [scan, next] using ih

private theorem scan_sound (w : List Bool) (q : Cursor) (F : Formula)
    (h : finish (scan q w) = some F) :
    consumed q ++ w = formulaWord F ∧ (legal q → Canonical F) := by
  induction w generalizing q with
  | nil =>
      cases q <;> simp_all [scan, finish, consumed, legal]
  | cons b w ih =>
      have hn : next q b ≠ .dead := by
        intro hn
        simp [scan, hn, scan_dead, finish] at h
      have ht := ih (next q b) h
      rw [next_consumed q b hn] at ht
      constructor
      · simpa [List.append_assoc] using ht.1
      · exact fun hq => ht.2 (next_legal q b hq)

private theorem scan_name_bits (d : Formula) (c : Std.Sat.CNF.Clause Name)
    (p : Bool) (n bits tail : List Bool) :
    scan (.nameTag d c p n) (bits.flatMap (fun b => [true,b]) ++ false :: tail) =
      scan (.clause d (c ++ .ofLiterals [(n ++ bits,p)])) tail := by
  induction bits generalizing n with
  | nil => simp [scan, next]
  | cons b bits ih =>
      simpa [List.flatMap_cons, scan, next, List.append_assoc] using ih (n ++ [b])

private theorem scan_name (d : Formula) (c : Std.Sat.CNF.Clause Name)
    (p : Bool) (n tail : List Bool) (h : n.head? = some true) :
    scan (.firstTag d c p) (nameWord n ++ tail) =
      scan (.clause d (c ++ .ofLiterals [(n,p)])) tail := by
  cases n with
  | nil => cases h
  | cons b bits =>
      cases b with
      | false => cases h
      | true =>
          simpa [nameWord, List.flatMap_cons, scan, next, List.append_assoc] using
            scan_name_bits d c p [true] bits tail

private theorem scan_clause (d : Formula) (c lits : Std.Sat.CNF.Clause Name)
    (tail : List Bool) (h : ∀ l ∈ lits, l.1.head? = some true) :
    scan (.clause d c) (lits.literals.flatMap literalWord ++ [true,false] ++ tail) =
      scan (.body (d ++ [c ++ lits])) tail := by
  have auxiliary (literals : List (Name × Bool)) (c : Std.Sat.CNF.Clause Name)
      (h : ∀ l ∈ literals, l.1.head? = some true) :
      scan (.clause d c) (literals.flatMap literalWord ++ [true,false] ++ tail) =
        scan (.body (d ++ [c ++ .ofLiterals literals])) tail := by
    induction literals generalizing c with
    | nil => simp [scan, next, Std.Sat.CNF.Clause.ofLiterals]
    | cons l literals ih =>
        obtain ⟨n,p⟩ := l
        have hn : n.head? = some true := h (n,p) (by simp)
        have ht : ∀ l ∈ literals, l.1.head? = some true := fun l hl => h l (by simp [hl])
        simp only [List.flatMap_cons, literalWord, List.append_assoc, List.cons_append,
          List.nil_append, scan, next]
        rw [scan_name d c p n _ hn]
        simpa [Std.Sat.CNF.Clause.append_assoc, ← Std.Sat.CNF.Clause.ofLiterals_append] using
          ih (c ++ .ofLiterals [(n,p)]) ht
  simpa using auxiliary lits.literals c h

private theorem scan_formula (d F : Formula) (h : Canonical F) :
    scan (.body d) (formulaWord F) = .ending (d ++ F) := by
  induction F generalizing d with
  | nil => simp [formulaWord, scan, next]
  | cons c F ih =>
      have hc : ∀ l ∈ c, l.1.head? = some true := h c (by simp)
      have ht : Canonical F := fun c hc => h c (by simp [hc])
      simp only [formulaWord, List.flatMap_cons, clauseWord, List.append_assoc,
        List.cons_append, List.nil_append, scan, next]
      have hs := scan_clause d .empty c (formulaWord F) hc
      simp only [Std.Sat.CNF.Clause.empty_append] at hs
      simpa [formulaWord, List.append_assoc] using hs.trans (ih (d ++ [c]) ht)

/-- Decoding succeeds exactly on original encodings with canonical positive
names. All finite clause lengths, repetitions, tautologies and empty cases are
included without a width or numeric-magnitude hypothesis. -/
theorem word_codec (w : List Bool) (F : Formula) :
    readWord w = some F ↔ Canonical F ∧ w = formulaWord F := by
  constructor
  · intro h
    have hs := scan_sound w (.body []) F h
    exact ⟨hs.2 (by simp [legal, Canonical]), by simpa [consumed] using hs.1⟩
  · rintro ⟨h, rfl⟩
    simpa [readWord, finish] using congrArg finish (scan_formula [] F h)

/-- Erasing the unbounded mathematical buffers leaves finite lexical control. -/
def phase : Cursor → ParsePhase
  | .body _ => .bodyFirst
  | .bodyTag _ => .bodySecond
  | .clause _ _ => .clauseFirst
  | .clauseTag _ _ => .clauseSecond
  | .polarity _ _ => .polarity
  | .firstTag _ _ _ => .firstTag
  | .firstBit _ _ _ => .firstBit
  | .nameTag _ _ _ _ => .nameTag
  | .nameBit _ _ _ _ => .nameBit
  | .ending _ => .ending
  | .dead => .dead

/-- Width is discarded at each lexical step; no clause counter is installed. -/
def nextPhase (p : ParsePhase) (b : Bool) : ParsePhase := (advance p 0 b).phase

def scanPhase : ParsePhase → List Bool → ParsePhase
  | p, [] => p
  | p, b :: w => scanPhase (nextPhase p b) w

private theorem phase_next (q : Cursor) (b : Bool) :
    phase (next q b) = nextPhase (phase q) b := by
  cases q <;> cases b <;> rfl

theorem phase_scan (q : Cursor) (w : List Bool) :
    phase (scan q w) = scanPhase (phase q) w := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih => simpa only [scan, scanPhase, phase_next] using ih (next q b)

/-- A rejected word returns a zero flag; success returns one and the exact
original encoding of the decoded formula. -/
def resultWord : Option Formula → List Bool
  | none => [false]
  | some F => true :: formulaWord F

inductive Stack
  | input | saved | output | frame
  deriving DecidableEq, Fintype, Inhabited

inductive Label
  | scan | copy | clear | finish
  deriving DecidableEq, Fintype, Inhabited

structure Control where
  phase : ParsePhase := .bodyFirst
  held : Option Bool := none
  accepted : Bool := false
  deriving DecidableEq, Fintype, Inhabited

/-- All tests inspect finite control, and each stack instruction moves one bit. -/
def parser : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .scan
  σ := Control
  initialState := ⟨.bodyFirst,none,false⟩
  m
    | .scan => .pop .input (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none, accepted := decide (s.phase = .ending) }) <|
            .branch (fun s => s.accepted)
              (.goto fun _ => .copy) (.goto fun _ => .clear))
          (.push .saved (fun s => s.held.getD false) <|
            .load (fun s => ⟨nextPhase s.phase (s.held.getD false),none,false⟩) <|
              .goto fun _ => .scan)
    | .copy => .pop .saved (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .finish)
          (.push .output (fun s => s.held.getD false) <|
            .load (fun s => { s with held := none }) <| .goto fun _ => .copy)
    | .clear => .pop .saved (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .finish)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .clear)
    | .finish => .push .output (fun s => s.accepted) <|
        .load (fun _ => ⟨.bodyFirst,none,false⟩) .halt

def parserStacks (input saved output frame : List Bool) : Stack → List Bool
  | .input => input
  | .saved => saved
  | .output => output
  | .frame => frame

def cfg (label : Option Label) (p : ParsePhase)
    (input saved output frame : List Bool) (accepted : Bool := false) : parser.Cfg :=
  ⟨label,⟨p,none,accepted⟩,parserStacks input saved output frame⟩

private def one_step (a : parser.Cfg) (b : Option parser.Cfg)
    (h : parser.step a = b) : EvalsToInTime parser.step a b 1 :=
  { steps := 1, evals_in_steps := h, steps_le_m := by decide }

private def scan_run (w saved output frame : List Bool) (p : ParsePhase) :
    EvalsToInTime parser.step (cfg (some .scan) p w saved output frame)
      (some (cfg (some .scan) (scanPhase p w) [] (w.reverse ++ saved) output frame))
      w.length := by
  induction w generalizing saved p with
  | nil => exact EvalsToInTime.refl _ _
  | cons b w ih =>
      have hs : parser.step (cfg (some .scan) p (b :: w) saved output frame) =
          some (cfg (some .scan) (nextPhase p b) w (b :: saved) output frame) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        simp only [Function.update_apply, Bool.cond_false]
        congr 1
        funext k
        cases k <;> simp [parserStacks, Function.update_apply]
      have run := EvalsToInTime.trans _ 1 w.length _ _ _ (one_step _ _ hs)
        (ih (b :: saved) (nextPhase p b))
      simpa [scanPhase, List.reverse_cons, List.append_assoc, Nat.add_comm] using run

private def copy_run (saved output frame : List Bool) (p : ParsePhase) :
    EvalsToInTime parser.step (cfg (some .copy) p [] saved output frame true)
      (some (cfg none .bodyFirst [] [] (true :: (saved.reverse ++ output)) frame))
      (saved.length + 2) := by
  induction saved generalizing output with
  | nil =>
      have hs : parser.step (cfg (some .copy) p [] [] output frame true) =
          some (cfg (some .finish) p [] [] output frame true) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        simp [parserStacks]
      have ht : parser.step (cfg (some .finish) p [] [] output frame true) =
          some (cfg none .bodyFirst [] [] (true :: output) frame) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        congr 1
        funext k
        cases k <;> simp [parserStacks]
      exact EvalsToInTime.trans _ 1 1 _ _ _ (one_step _ _ hs) (one_step _ _ ht)
  | cons b saved ih =>
      have hs : parser.step (cfg (some .copy) p [] (b :: saved) output frame true) =
          some (cfg (some .copy) p [] saved (b :: output) frame true) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        simp only [Function.update_apply, Bool.cond_false]
        congr 1
        funext k
        cases k <;> simp [parserStacks]
      have run := EvalsToInTime.trans _ 1 (saved.length + 2) _ _ _ (one_step _ _ hs)
        (ih (b :: output))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using run

private def clear_run (saved frame : List Bool) (p : ParsePhase) :
    EvalsToInTime parser.step (cfg (some .clear) p [] saved [] frame)
      (some (cfg none .bodyFirst [] [] [false] frame)) (saved.length + 2) := by
  induction saved with
  | nil =>
      have hs : parser.step (cfg (some .clear) p [] [] [] frame) =
          some (cfg (some .finish) p [] [] [] frame) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        simp [parserStacks]
      have ht : parser.step (cfg (some .finish) p [] [] [] frame) =
          some (cfg none .bodyFirst [] [] [false] frame) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        congr 1
        funext k
        cases k <;> simp [parserStacks]
      exact EvalsToInTime.trans _ 1 1 _ _ _ (one_step _ _ hs) (one_step _ _ ht)
  | cons b saved ih =>
      have hs : parser.step (cfg (some .clear) p [] (b :: saved) [] frame) =
          some (cfg (some .clear) p [] saved [] frame) := by
        apply congrArg some
        dsimp [parser, TM2.stepAux, cfg, parserStacks]
        simp only [Bool.cond_false]
        congr 1
        funext k
        cases k <;> rfl
      simpa [Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (saved.length + 2) _ _ _ (one_step _ _ hs) ih

/-- The fixed finite parser validates and returns the original typed formula
encoding, or the rejection flag, in a linear number of actual TM2 transitions. -/
theorem parser_run (w : List Bool) :
    Nonempty (TM2OutputsInTime parser w (some (resultWord (readWord w)))
      (2 * w.length + 3)) := by
  let p := scanPhase .bodyFirst w
  let accepted := decide (p = .ending)
  have hs : parser.step (cfg (some .scan) p [] w.reverse [] []) =
      some (cfg (some (if p = .ending then .copy else .clear)) p [] w.reverse [] [] accepted) := by
    dsimp only [accepted]
    cases p <;> apply congrArg some <;>
      dsimp [parser, TM2.stepAux, cfg, parserStacks, FinTM2.decidableEqK] <;>
      simp only [reduceCtorEq, decide_false, decide_true, cond_false, cond_true] <;>
      congr 1 <;> funext k <;> cases k <;> rfl
  have tail : EvalsToInTime parser.step
      (cfg (some .scan) p [] w.reverse [] [])
      (some (cfg none .bodyFirst [] [] (if p = .ending then true :: w else [false]) []))
      (w.length + 3) := by
    by_cases hp : p = .ending
    · simp only [hp, accepted, decide_true, if_true] at hs
      have hcopy := copy_run w.reverse [] [] p
      simp only [hp] at hcopy
      simpa [hp, accepted, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (w.reverse.length + 2) _ _ _ (one_step _ _ hs) hcopy
    · simp only [accepted, hp, decide_false] at hs
      have hclear := clear_run w.reverse [] p
      simpa [hp, accepted, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (w.reverse.length + 2) _ _ _ (one_step _ _ hs) hclear
  have output : (if p = .ending then true :: w else [false]) = resultWord (readWord w) := by
    have phaseEq : phase (scan (.body []) w) = p := phase_scan (.body []) w
    cases hq : scan (.body []) w
    case ending F =>
        have hp : p = .ending := by simpa [hq, phase] using phaseEq.symm
        have hr : readWord w = some F := by simp [readWord, hq, finish]
        have hw := (word_codec w F).mp hr
        simp only [hr, resultWord, if_pos hp]
        exact congrArg (List.cons true) hw.2
    all_goals
      have hp : p ≠ .ending := by
        intro hp
        simp [hq, phase, hp] at phaseEq
      simp [hp, readWord, hq, finish, resultWord]
  have head := scan_run w [] [] [] .bodyFirst
  simp only [List.append_nil] at head
  have run := EvalsToInTime.trans _ w.length (w.length + 3) _ _ _ head tail
  rw [output] at run
  refine ⟨?_⟩
  change EvalsToInTime parser.step (initList parser w)
    (some (haltList parser (resultWord (readWord w)))) (2 * w.length + 3)
  have initEq : initList parser w = cfg (some .scan) .bodyFirst w [] [] [] := by
    dsimp [initList, parser, cfg, parserStacks, FinTM2.decidableEqK]
    congr 1
    funext k
    cases k <;> rfl
  have haltEq : haltList parser (resultWord (readWord w)) =
      cfg none .bodyFirst [] [] (resultWord (readWord w)) [] := by
    dsimp [haltList, parser, cfg, parserStacks, FinTM2.decidableEqK]
    congr 1
    funext k
    cases k <;> rfl
  rw [initEq,haltEq]
  simpa [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end PredictiveThermodynamic.Unrestricted
