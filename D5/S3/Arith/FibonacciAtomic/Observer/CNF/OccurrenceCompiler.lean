/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Installed CNF occurrences and charged native continuation prefixes. -/

import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
import D5.S0.Computability.DenseClauseConversion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSixSourceMoore (Controller)
open StateTransition (EvalsToInTime)

namespace Bank
export FiniteMenu.NativeBooleanAssignmentBanks
  (literal assignment branchBit localIndex localCount)
end Bank

abbrev Formula (n : Nat) := List (Std.Sat.CNF.Clause (Fin n))

/-- The two external labels designate supplied continuations, not instructions. -/
inductive Target where
  | internal : Nat → Target
  | success | failure
  deriving DecidableEq, Repr

/-- A complete occurrence record has one literal and all four successors. -/
structure Read where
  address : Address
  next : Reply → Target

abbrev Records := List (Nat × Read)

def accepts (polarity : Bool) (reply : Reply) : Bool := Bank.branchBit reply == polarity

def clauseEntry {n : Nat} (base : Nat) (c : Std.Sat.CNF.Clause (Fin n))
    (no : Target) : Target :=
  match c with
  | [] => no
  | _ :: _ => .internal base

def entry {n : Nat} (base : Nat) : Formula n → Target
  | [] => .success
  | c :: _ => clauseEntry base c .failure

def clause {n : Nat} (base : Nat) (yes no : Target) :
    Std.Sat.CNF.Clause (Fin n) → Records
  | [] => []
  | l :: ls => (base, ⟨Bank.literal n l.1,
      fun r => if accepts l.2 r then yes else clauseEntry (base + 1) ls no⟩) ::
      clause (base + 1) yes no ls

def records {n : Nat} (base : Nat) : Formula n → Records
  | [] => []
  | c :: cs => clause base (entry (base + c.length) cs) .failure c ++
      records (base + c.length) cs

def occurrences {n : Nat} (f : Formula n) : Nat := (f.map List.length).sum

def evaluate {n : Nat} (f : Formula n) (u : Source) : Bool :=
  f.all (Std.Sat.CNF.Clause.eval (Bank.assignment n u))

/-- Each transition charges precisely one native Read; Halt has no successor. -/
def step {Q H : Type} (C : Controller Q H) (u : Source) : Q ⊕ H → Option (Q ⊕ H)
  | .inl q => some (C.next q (readout (C.addr q) (substitution u)))
  | .inr _ => none

def resolve {K : Type} (place : Nat → K) (S F : K) : Target → K
  | .internal i => place i
  | .success => S
  | .failure => F

/-- Installation refers to the actual Controller fields. All records, including
unreachable ones, must be present. No behavior is required after the endpoint. -/
def Installed {Q H : Type} (C : Controller Q H) (place : Nat → Q ⊕ H)
    (S F : Q ⊕ H) (rs : Records) : Prop :=
  ∀ i r, (i,r) ∈ rs → ∃ q, place i = .inl q ∧ C.addr q = r.address ∧
    ∀ reply, C.next q reply = resolve place S F (r.next reply)

private theorem clause_ids {n : Nat} (base : Nat) (yes no : Target)
    (c : Std.Sat.CNF.Clause (Fin n)) :
    (clause base yes no c).map Prod.fst = List.range' base c.length := by
  induction c generalizing base with
  | nil => rfl
  | cons l ls ih => simp only [clause,List.map_cons,List.length_cons,List.range'_succ,ih]

private theorem record_ids {n : Nat} (base : Nat) (f : Formula n) :
    (records base f).map Prod.fst = List.range' base (occurrences f) := by
  induction f generalizing base with
  | nil => rfl
  | cons c cs ih =>
    simp only [records,List.map_append,clause_ids,ih,occurrences,List.map_cons,List.sum_cons]
    exact List.range'_append_1

/-- All internal labels name installed records, and every internal successor
strictly advances its occurrence index. External continuations are unrestricted. -/
def Valid (e : Target) (rs : Records) : Prop :=
  (∀ j, e = .internal j → j < rs.length) ∧
  ∀ i r, (i,r) ∈ rs → ∀ reply j, r.next reply = .internal j → i < j ∧ j < rs.length

private theorem entry_bounds {n : Nat} (base : Nat) (f : Formula n) :
    ∀ j, entry base f = .internal j → base ≤ j ∧ j < base + occurrences f := by
  cases f with
  | nil => intro j h; cases h
  | cons c cs =>
    cases c with
    | nil => intro j h; cases h
    | cons l ls =>
      intro j h
      have eq : base = j := Target.internal.inj h
      subst j
      simp only [occurrences,List.map_cons,List.sum_cons,List.length_cons]
      omega

private theorem clause_forward {n : Nat} (base : Nat) (yes : Target)
    (c : Std.Sat.CNF.Clause (Fin n))
    (after : ∀ j, yes = .internal j → base + c.length ≤ j) :
    ∀ i r, (i,r) ∈ clause base yes .failure c →
      ∀ reply j, r.next reply = .internal j →
        i < j ∧ (j < base + c.length ∨ yes = .internal j) := by
  induction c generalizing base with
  | nil => intro i r h; cases h
  | cons l ls ih =>
    intro i r hr reply j hnext
    rcases List.mem_cons.mp hr with h | h
    · cases h
      dsimp only at hnext
      split at hnext
      · exact ⟨by have h := after j hnext; simp only [List.length_cons] at h; omega,
          Or.inr hnext⟩
      · cases ls with
        | nil => cases hnext
        | cons l' ls' =>
          have hj : base + 1 = j := Target.internal.inj hnext
          subst j
          exact ⟨by omega,Or.inl (by simp)⟩
    · have after' : ∀ j, yes = .internal j → base + 1+ls.length ≤ j := by
        intro j hj
        have h := after j hj
        simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using h
      obtain ⟨lt,upper⟩ := ih (base + 1) after' i r h reply j hnext
      exact ⟨lt,upper.imp (by simp only [List.length_cons]; omega) id⟩

private theorem record_forward {n : Nat} (base : Nat) (f : Formula n) :
    ∀ i r, (i,r) ∈ records base f → ∀ reply j, r.next reply = .internal j →
      i < j ∧ j < base + occurrences f := by
  induction f generalizing base with
  | nil => intro i r h; cases h
  | cons c cs ih =>
    intro i r hr reply j hnext
    rcases List.mem_append.mp hr with hc | ht
    · obtain ⟨lt,upper⟩ := clause_forward base (entry (base + c.length) cs) c
        (fun j hj => (entry_bounds _ _ j hj).1) i r hc reply j hnext
      refine ⟨lt,?_⟩
      rcases upper with h | h
      · simp only [occurrences,List.map_cons,List.sum_cons]
        omega
      · have h' := (entry_bounds (base + c.length) cs j h).2
        simpa only [occurrences,List.map_cons,List.sum_cons,Nat.add_assoc] using h'
    · have h := ih (base + c.length) i r ht reply j hnext
      simpa only [occurrences,List.map_cons,List.sum_cons,Nat.add_assoc] using h

private theorem records_valid {n : Nat} (f : Formula n) : Valid (entry 0 f) (records 0 f) := by
  have len : (records 0 f).length = occurrences f := by
    simpa using congrArg List.length (record_ids 0 f)
  refine ⟨fun j hj => ?_,fun i r hr reply j hj => ?_⟩
  · simpa only [len,Nat.zero_add] using (entry_bounds 0 f j hj).2
  · simpa only [len,Nat.zero_add] using record_forward 0 f i r hr reply j hj

private theorem prefix_clause {n : Nat} {Q H : Type} (C : Controller Q H)
    (place : Nat → Q ⊕ H) (S F : Q ⊕ H) (u : Source)
    (base : Nat) (yes no : Target) (c : Std.Sat.CNF.Clause (Fin n))
    (installed : Installed C place S F (clause base yes no c)) :
    Nonempty (EvalsToInTime (step C u) (resolve place S F (clauseEntry base c no))
      (some (if c.eval (Bank.assignment n u) then resolve place S F yes else
        resolve place S F no)) c.length) := by
  induction c generalizing base with
  | nil => exact ⟨EvalsToInTime.refl _ _⟩
  | cons l ls ih =>
    obtain ⟨q,hq,ha,hn⟩ := installed base _ List.mem_cons_self
    have hs : step C u (place base) = some
        (if accepts l.2 (readout (Bank.literal n l.1) (substitution u)) then
          resolve place S F yes else resolve place S F (clauseEntry (base + 1) ls no)) := by
      rw [hq]
      simp only [step,ha,hn]
      split <;> rfl
    have one : EvalsToInTime (step C u) (place base) _ 1 := ⟨⟨1,hs⟩,le_rfl⟩
    have he : accepts l.2 (readout (Bank.literal n l.1) (substitution u)) =
        (Bank.assignment n u l.1 == l.2) := rfl
    cases hb : (Bank.assignment n u l.1 == l.2) with
    | true =>
      have bound : 1 ≤ (l::ls).length := by simp
      refine ⟨⟨⟨one.steps, ?_⟩,one.steps_le_m.trans bound⟩⟩
      simpa only [he,hb,Bool.true_or,Std.Sat.CNF.Clause.eval_cons,
        clauseEntry,resolve,ite_true] using one.evals_in_steps
    | false =>
      obtain ⟨tail⟩ := ih (base + 1) (fun i r h => installed i r (List.mem_cons_of_mem _ h))
      have one' : EvalsToInTime (step C u) (place base)
          (some (resolve place S F (clauseEntry (base + 1) ls no))) 1 := by
        simpa only [he,hb,Bool.false_eq_true,ite_false] using one
      have run := EvalsToInTime.trans _ 1 ls.length _ _ _ one' tail
      exact ⟨by simpa only [Std.Sat.CNF.Clause.eval_cons,hb,Bool.false_or,
        List.length_cons,clauseEntry,resolve] using run⟩

private theorem prefix_formula {n : Nat} {Q H : Type} (C : Controller Q H)
    (place : Nat → Q ⊕ H) (S F : Q ⊕ H) (u : Source)
    (base : Nat) (f : Formula n)
    (installed : Installed C place S F (records base f)) :
    Nonempty (EvalsToInTime (step C u) (resolve place S F (entry base f))
      (some (if evaluate f u then S else F)) (occurrences f)) := by
  induction f generalizing base with
  | nil => exact ⟨EvalsToInTime.refl _ _⟩
  | cons c cs ih =>
    obtain ⟨first⟩ := prefix_clause C place S F u base (entry (base + c.length) cs) .failure c
      (fun i r h => installed i r (List.mem_append_left _ h))
    cases hc : c.eval (Bank.assignment n u) with
    | false =>
      have bound : c.length ≤ occurrences (c::cs) := by simp [occurrences]
      refine ⟨⟨⟨first.steps, ?_⟩,first.steps_le_m.trans bound⟩⟩
      simpa only [hc,resolve,ite_false,entry,evaluate,List.all_cons,
        Bool.false_and,Bool.false_eq_true]
        using first.evals_in_steps
    | true =>
      obtain ⟨tail⟩ := ih (base + c.length)
        (fun i r h => installed i r (List.mem_append_right _ h))
      have first' : EvalsToInTime (step C u)
          (resolve place S F (entry base (c::cs)))
          (some (resolve place S F (entry (base + c.length) cs))) c.length := by
        simpa only [hc,ite_true,entry] using first
      have run := EvalsToInTime.trans _ c.length (occurrences cs) _ _ _ first' tail
      refine ⟨?_⟩
      convert run using 1 <;> simp only [evaluate,List.all_cons,hc,Bool.true_and,
        occurrences,List.map_cons,List.sum_cons,Nat.add_comm]
      all_goals rfl

/-- The full finite occurrence list is installed and reaches exactly the selected
supplied endpoint. The endpoint may itself be a Read, a Halt, or a loop. -/
theorem installed_prefix {n : Nat} {Q H : Type} (C : Controller Q H)
    (place : Nat → Q ⊕ H) (S F : Q ⊕ H) (u : Source) (f : Formula n)
    (installed : Installed C place S F (records 0 f)) :
    (records 0 f).length = occurrences f ∧
    (records 0 f).map Prod.fst = List.range (occurrences f) ∧
    Nonempty (EvalsToInTime (step C u) (resolve place S F (entry 0 f))
      (some (if evaluate f u then S else F)) (occurrences f)) := by
  have ids := record_ids 0 f
  refine ⟨?_,by simpa only [List.range_eq_range'] using ids,
    prefix_formula C place S F u 0 f installed⟩
  have lengths := congrArg List.length ids
  simpa using lengths

#print axioms installed_prefix

/-- The ambient table embeds without changing a literal, successor, or Halt row. -/
def embed {m : Nat} {Q H : Type} : Q ⊕ H → (Fin m ⊕ Q) ⊕ H
  | .inl q => .inl (.inr q)
  | .inr h => .inr h

/-- Out-of-fragment indices use the failure label. Compiled internal references
are in range; the total extension makes linking independent of ambient size. -/
def placement (rs : Records) {Q H : Type} (F : Q ⊕ H) (i : Nat) :
    (Fin rs.length ⊕ Q) ⊕ H :=
  if hi : i < rs.length then .inl (.inl ⟨i,hi⟩) else embed F

/-- Exactly one new running state per record, disjoint from the entire original
table. Both supplied labels may be Reads or Halts and may coincide. -/
def plug (rs : Records) {Q H : Type} (C : Controller Q H) (S F : Q ⊕ H) :
    Controller (Fin rs.length ⊕ Q) H where
  addr := fun q => match q with
    | .inl i => (rs.get i).2.address
    | .inr q => C.addr q
  next := fun q reply => match q with
    | .inl i => resolve (placement rs F) (embed S) (embed F) ((rs.get i).2.next reply)
    | .inr q => embed (C.next q reply)
  out := C.out

private theorem plug_installed {n : Nat} (f : Formula n) {Q H : Type}
    (C : Controller Q H) (S F : Q ⊕ H) :
    Installed (plug (records 0 f) C S F) (placement (records 0 f) F)
      (embed S) (embed F) (records 0 f) := by
  intro i r hr
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hr
  have ids := record_ids 0 f
  have ith := congrArg (fun l : List Nat => l[j]?) ids
  have len : (records 0 f).length = occurrences f := by
    simpa using congrArg List.length ids
  have bound : j < occurrences f := by omega
  have id : i = j := by
    simpa [List.getElem?_map,List.getElem?_eq_getElem,hj,hget,List.getElem?_range',bound] using ith
  subst i
  refine ⟨.inl ⟨j,hj⟩,by simp [placement,hj],?_,?_⟩
  · change ((records 0 f)[j]).2.address = r.address
    rw [hget]
  · intro reply
    change resolve _ _ _ (((records 0 f)[j]).2.next reply) = _
    rw [hget]

/-- The source-defined assignment uses the original appearing-name index and
the original fixed lexicographic RLL literal, with no Boolean-source premise. -/
def sourceAssignment (f : PredictiveThermodynamic.Conventional.Formula) (u : Source) :
    PredictiveThermodynamic.Conventional.Appearing f → Bool :=
  fun name => Bank.assignment (PredictiveThermodynamic.Conventional.dictionary f).length u
    (Bank.localIndex (PredictiveThermodynamic.Conventional.occurrences f) name)

private theorem dense_evaluation (f : PredictiveThermodynamic.Conventional.Formula)
    (u : Source) :
    evaluate (PredictiveThermodynamic.BinaryNames.denseFormula f) u =
      PredictiveThermodynamic.Conventional.evaluate f (sourceAssignment f u) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evaluate,PredictiveThermodynamic.BinaryNames.denseFormula,
    PredictiveThermodynamic.Conventional.evaluate,List.all_map,Function.comp_def,
    List.all_eq_true,List.mem_attach,forall_const,Subtype.forall]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  simp only [Std.Sat.CNF.Clause.eval,List.any_map,Function.comp_def,List.any_eq_true,
    List.mem_attach,true_and,Subtype.exists]
  apply exists_congr
  intro l
  by_cases hl : l ∈ c
  · have hm : l.1 ∈ PredictiveThermodynamic.Conventional.occurrences f :=
      List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨l,hl,rfl⟩⟩
    simp [hl,PredictiveThermodynamic.Conventional.extendAssignment,
      sourceAssignment,Bank.localIndex,hm,PredictiveThermodynamic.Conventional.dictionary]
    all_goals rfl
  · simp [hl]

private theorem dense_occurrences (f : PredictiveThermodynamic.Conventional.Formula) :
    occurrences (PredictiveThermodynamic.BinaryNames.denseFormula f) =
      (PredictiveThermodynamic.Conventional.occurrences f).length := by
  simp [occurrences,PredictiveThermodynamic.BinaryNames.denseFormula,
    PredictiveThermodynamic.Conventional.occurrences,List.map_map]

/-- Every unrestricted finite CNF has all M occurrence Reads installed, even
when an earlier empty clause makes them unreachable. The unchanged arbitrary
ambient table and its complete Halt outputs are preserved. On each actual
source the charged native prefix reaches the selected supplied label in at most
M calls, without executing a continuation transition. -/
theorem native_occurrence_compiler (f : PredictiveThermodynamic.Conventional.Formula)
    {Q H : Type} (C : Controller Q H) (S F : Q ⊕ H) (u : Source) :
    let dense := PredictiveThermodynamic.BinaryNames.denseFormula f
    let rs := records 0 dense
    let linked := plug rs C S F
    rs.length = (PredictiveThermodynamic.Conventional.occurrences f).length ∧
    rs.map Prod.fst = List.range rs.length ∧
    Valid (entry 0 dense) rs ∧
    Function.Injective (fun i : Fin rs.length => placement rs F i.val) ∧
    Installed linked (placement rs F) (embed S) (embed F) rs ∧
    (∀ q, linked.addr (.inr q) = C.addr q ∧
      ∀ r, linked.next (.inr q) r = embed (C.next q r)) ∧
    linked.out = C.out ∧
    Nonempty (EvalsToInTime (step linked u)
      (resolve (placement rs F) (embed S) (embed F) (entry 0 dense))
      (some (embed (if PredictiveThermodynamic.Conventional.evaluate f
        (sourceAssignment f u) then S else F)))
      (PredictiveThermodynamic.Conventional.occurrences f).length) := by
  dsimp only
  have installed := plug_installed (PredictiveThermodynamic.BinaryNames.denseFormula f) C S F
  obtain ⟨len,ids,execution⟩ := installed_prefix _ _ _ _ u _ installed
  refine ⟨len.trans (dense_occurrences f),by simpa only [len] using ids,
    records_valid _,?_,
    installed,fun q => ⟨rfl,fun r => rfl⟩,rfl,?_⟩
  · intro i j h
    have eq : i.val = j.val := by
      simpa only [placement,i.isLt,j.isLt,dif_pos,Sum.inl.injEq,Fin.mk.injEq] using h
    exact Fin.ext eq
  · rw [dense_evaluation,dense_occurrences] at execution
    split <;> simp_all

#print axioms native_occurrence_compiler

end D5.S3.Arith.FibonacciAtomic.Observer.CNF.OccurrenceCompiler
