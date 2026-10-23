/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite passive controllers realized by effective original instruction tables with exact paid traces. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine (Event Trace reads answers)
open NativeSerialEffective
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

abbrev PaidHistory := Hist (fun _ : Address => Reply)

/-- Four explicit continuations contain only finite common data. -/
inductive Dialogue (O : Type) where
  | stop : O → Dialogue O
  | read : Address → Dialogue O → Dialogue O → Dialogue O → Dialogue O → Dialogue O

/-- Stop is inspected even at depth zero. Further reads at that depth use the
common fallback, while every terminating path within the bound is preserved. -/
def unfold {L O : Type} (π : PaidHistory → Sum Address L) (enc : L → O)
    (fallback : O) : Nat → PaidHistory → Dialogue O
  | 0, h => match π h with
    | .inr o => .stop (enc o)
    | .inl _ => .stop fallback
  | k+1, h => match π h with
    | .inr o => .stop (enc o)
    | .inl a => .read a
        (unfold π enc fallback k (h ++ [⟨a,.alpha⟩]))
        (unfold π enc fallback k (h ++ [⟨a,.beta⟩]))
        (unfold π enc fallback k (h ++ [⟨a,.branch⟩]))
        (unfold π enc fallback k (h ++ [⟨a,.absent⟩]))

/-- Preorder installation uses absolute natural workspace indices. -/
def flatten {O : Type} : Nat → Dialogue O → List (OriginalAction O)
  | _, .stop o => [originalStop o]
  | i, .read a A B C D =>
    let aa := flatten (i+1) A
    let bb := flatten (i+1+aa.length) B
    let cc := flatten (i+1+aa.length+bb.length) C
    let dd := flatten (i+1+aa.length+bb.length+cc.length) D
    originalRead a (i+1,i+1+aa.length,i+1+aa.length+bb.length,
      i+1+aa.length+bb.length+cc.length) :: (aa ++ bb ++ cc ++ dd)

/-- No source is an input to this finite materializer. -/
def materialize {L O : Type} (π : PaidHistory → Sum Address L) (enc : L → O)
    (fallback : O) (K : Nat) (h : PaidHistory) : List (OriginalAction O) :=
  flatten 0 (unfold π enc fallback K h)

/-- The installed original selector is total list lookup on workspace. -/
def tableAction {O : Type} (table : List (OriginalAction O)) (fallback : O)
    (s : OriginalState) : OriginalAction O :=
  (table[s.2.1]?).getD (originalStop fallback)

private theorem tableAction_computable {O : Type} [Primcodable O]
    (table : List (OriginalAction O)) (fallback : O) :
    Computable (tableAction table fallback) := by
  exact Computable.option_getD
    (Computable.list_getElem?.comp (Computable.const table)
      (Computable.fst.comp Computable.snd)) (Computable.const (originalStop fallback))

def tableService {O : Type} [Primcodable O]
    (table : List (OriginalAction O)) (fallback : O) : OriginalEffectiveService O :=
  ⟨fun s => Part.some (tableAction table fallback s),
    (tableAction_computable table fallback).partrec⟩

/-- A physical trace retains every address/reply occurrence at the fixed epoch. -/
def paidTrace (N : Nat) (t : PaidHistory) : Trace :=
  t.map (fun a => Event.read N a.1 a.2)

/-- Executable interpreter of the first-order table. Reads use the same
register and append their actual events; Stop returns without another action. -/
def executeTable {O : Type} (table : List (OriginalAction O)) (fallback : O) :
    Nat → OriginalState → Source → Option (Trace × OriginalState × O)
  | 0, _, _ => none
  | fuel+1, s, r => match tableAction table fallback s with
    | .inl (a,k) =>
      let y := readout a r
      (executeTable table fallback fuel
        (afterOriginalRead s a y (originalContinuation k y)) r).map
        (fun result => (Event.read s.epoch a y :: result.1, result.2))
    | .inr (.inl workspace) =>
      (executeTable table fallback fuel (afterOriginalUpdate s workspace)
        (GenealogicalFiberTransport.substitution r)).map
        (fun result => (Event.update s.epoch :: result.1,result.2))
    | .inr (.inr o) => some ([],s,o)

def recordReads (N : Nat) (t : PaidHistory) : List OriginalEvent :=
  t.map (fun a => .inr (N,a.1,originalReplyCode a.2))

private inductive Represents {O : Type} (table : List (OriginalAction O)) :
    Nat → Dialogue O → Prop
  | stop {i o} : table[i]? = some (originalStop o) → Represents table i (.stop o)
  | read {i a A B C D k} : table[i]? = some (originalRead a k) →
      Represents table k.1 A → Represents table k.2.1 B →
      Represents table k.2.2.1 C → Represents table k.2.2.2 D →
      Represents table i (.read a A B C D)

set_option maxHeartbeats 2000000 in
-- Preorder placements normalize four child offsets and their list prefixes.
private theorem flatten_represents {O : Type} (tree : Dialogue O)
    (pre post : List (OriginalAction O)) :
    Represents (pre ++ flatten pre.length tree ++ post) pre.length tree := by
  induction tree generalizing pre post with
  | stop o =>
      apply Represents.stop
      simp [flatten]
  | read a A B C D ihA ihB ihC ihD =>
      let i := pre.length
      let aa := flatten (i+1) A
      let bb := flatten (i+1+aa.length) B
      let cc := flatten (i+1+aa.length+bb.length) C
      let dd := flatten (i+1+aa.length+bb.length+cc.length) D
      let root : OriginalAction O := originalRead a (i+1,i+1+aa.length,i+1+aa.length+bb.length,
        i+1+aa.length+bb.length+cc.length)
      change Represents (pre ++ (root :: (aa ++ bb ++ cc ++ dd)) ++ post) i _
      apply Represents.read (k := (i+1,i+1+aa.length,i+1+aa.length+bb.length,
        i+1+aa.length+bb.length+cc.length))
      · simp [i, root]
      · have ha := ihA (pre ++ [root]) (bb ++ cc ++ dd ++ post)
        simpa [aa,i,List.append_assoc] using ha
      · have hb := ihB (pre ++ [root] ++ aa) (cc ++ dd ++ post)
        simpa [bb,i,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
      · have hc := ihC (pre ++ [root] ++ aa ++ bb) (dd ++ post)
        simpa [cc,i,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
      · have hd := ihD (pre ++ [root] ++ aa ++ bb ++ cc) post
        simpa [dd,i,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hd

set_option maxHeartbeats 2000000 in
-- The actual-run induction also reconstructs the terminal chronological state.
private theorem unfold_run {L O : Type} [Primcodable O]
    (π : PaidHistory → Sum Address L) (enc : L → O) (fallback : O)
    (K fuel : Nat) (h : PaidHistory) (r : Source) (t : PaidHistory) (o : L)
    (run : execute readout π fuel h r = some (t, o)) (bound : t.length ≤ K)
    (table : List (OriginalAction O)) (i : Nat)
    (rep : Represents table i (unfold π enc fallback K h))
    (s : OriginalState) (workspace : s.2.1 = i) :
    OriginalRun (tableService table fallback) s r (paidTrace s.epoch t) (enc o) ∧
    ∃ final : OriginalState,
      executeTable table fallback fuel s r = some (paidTrace s.epoch t,final,enc o) ∧
      final.input = s.input ∧ final.epoch = s.epoch ∧
      final.history = s.history ++ recordReads s.epoch t := by
  induction fuel generalizing K h t o i s with
  | zero => simp [execute] at run
  | succ fuel ih =>
      cases hp : π h with
      | inr output =>
          have result : t = [] ∧ o = output := by simpa [execute,hp] using run.symm
          rcases result with ⟨rfl,rfl⟩
          have rep' : Represents table i (.stop (enc o)) := by
            cases K <;> simpa [unfold,hp] using rep
          cases rep' with
          | stop lookup =>
              constructor
              · apply OriginalRun.stop
                simp [tableService,tableAction,workspace,lookup]
              · refine ⟨s,?_,rfl,rfl,?_⟩
                · simp [executeTable,tableAction,workspace,lookup,originalStop,paidTrace]
                · simp [recordReads]
      | inl a =>
          cases hr : execute readout π fuel (h ++ [⟨a,readout a r⟩]) r with
          | none => simp [execute,hp,hr] at run
          | some result =>
              rcases result with ⟨rest,output⟩
              have result : t = ⟨a,readout a r⟩ :: rest ∧ o = output := by
                simpa [execute,hp,hr] using run.symm
              rcases result with ⟨rfl,rfl⟩
              cases K with
              | zero => simp at bound
              | succ K =>
                  have rep' : Represents table i (.read a
                      (unfold π enc fallback K (h ++ [⟨a,.alpha⟩]))
                      (unfold π enc fallback K (h ++ [⟨a,.beta⟩]))
                      (unfold π enc fallback K (h ++ [⟨a,.branch⟩]))
                      (unfold π enc fallback K (h ++ [⟨a,.absent⟩]))) := by
                    simpa [unfold,hp] using rep
                  cases rep' with
                  | @read _ _ _ _ _ _ k lookup hA hB hC hD =>
                      have mem : originalRead a k ∈ (tableService table fallback).select s := by
                        simp [tableService,tableAction,workspace,lookup]
                      have small : rest.length ≤ K := by simpa using bound
                      have tailRep : Represents table (originalContinuation k (readout a r))
                          (unfold π enc fallback K (h ++ [⟨a,readout a r⟩])) := by
                        cases hy : readout a r
                        · simpa [originalContinuation,hy] using hA
                        · simpa [originalContinuation,hy] using hB
                        · simpa [originalContinuation,hy] using hC
                        · simpa [originalContinuation,hy] using hD
                      have tail := ih K (h ++ [⟨a,readout a r⟩]) rest o hr small
                        (originalContinuation k (readout a r)) tailRep
                        (afterOriginalRead s a (readout a r) (originalContinuation k (readout a r))) rfl
                      constructor
                      · simpa [paidTrace,afterOriginalRead,OriginalState.epoch] using
                          OriginalRun.read mem rfl tail.1
                      · obtain ⟨final,exec,inp,epoch,hist⟩ := tail.2
                        refine ⟨final,?_,inp,epoch,?_⟩
                        · simp only [executeTable,tableAction,workspace,lookup,
                            Option.getD_some,originalRead]
                          rw [exec]
                          rfl
                        · simpa [afterOriginalRead,OriginalState.history,
                            OriginalState.epoch,recordReads,List.append_assoc] using hist

private theorem reads_paidTrace (N : Nat) (t : PaidHistory) :
    reads (paidTrace N t) = t.map (fun a => (N,a.1,a.2)) := by
  induction t with
  | nil => rfl
  | cons a t ih => simpa [paidTrace,reads] using congrArg (List.cons (N,a.1,a.2)) ih

/-- Every bounded actual passive execution is realized by the materialized
original service on the same register, preserving the full paid trace.
Common input, certified epoch and arbitrary prior chronological record are
carried through the original read transition without source-dependent fields. -/
theorem bounded_passive_realization {L O : Type} [Primcodable O]
    (π : PaidHistory → Sum Address L) (enc : L → O) (fallback : O)
    (K fuel : Nat) (h : PaidHistory) (input N : Nat) (prior : List OriginalEvent)
    (r : Source) (t : PaidHistory) (o : L)
    (run : execute readout π fuel h r = some (t, o)) (bound : t.length ≤ K) :
    let table := materialize π enc fallback K h
    OriginalRun (tableService table fallback) (input,0,N,prior) r
      (paidTrace N t) (enc o) ∧
    (∃ final : OriginalState,
      executeTable table fallback fuel (input,0,N,prior) r =
        some (paidTrace N t,final,enc o) ∧
      final.input = input ∧ final.epoch = N ∧
      final.history = prior ++ recordReads N t) ∧
    reads (paidTrace N t) = t.map (fun a => (N,a.1,a.2)) ∧
    answers (paidTrace N t) = t.map Sigma.snd ∧
    (answers (paidTrace N t)).length = t.length := by
  dsimp only
  have rep := flatten_represents (unfold π enc fallback K h) [] []
  have real := unfold_run π enc fallback K fuel h r t o run bound
    (materialize π enc fallback K h) 0 (by simpa [materialize] using rep)
    (input,0,N,prior) rfl
  have rd := reads_paidTrace N t
  have ans : answers (paidTrace N t) = t.map Sigma.snd := by
    simp only [answers,rd,List.map_map]
    rfl
  exact ⟨real.1,real.2,rd,ans,by simp [ans]⟩

/-- Source-free finite installation for the existing complete whole-row
controller. The budget is independent of N; physical addresses may depend on N.
This executable definition does not assert a uniform encoded Computable proof
for the infinite family of common inputs. -/
def materializeWholeRow
    (old : ActualCutPartitionRecovery.LiteralRow)
    (Q : ActualCutPartitionRecovery.CutSet) (H : NativeDepthPatterns.History) (N : Nat) :
    List (OriginalAction NativeSerialDepth.RowWord) :=
  materialize (NativeWholeRowService.controller
    (NativeWholeRowService.compileService old Q H N))
    (fun record => NativeSerialDepth.rowWord (NativeWholeRowService.recordRow record))
    (NativeSerialDepth.rowWord (.of (.inl true))) (NativeWholeRowService.K0 old Q H) []

end D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization
