/- GID: D5/S0/Certificates/SkeletonSlotCNF
   generality: G
   mirror-B: D5/B/S0/Certificates/SkeletonSlotCNF
   mirror-E: none(waiver:constructive-cnf-compiler)
   anchors: []
   digest: Concrete finite slot clauses admit every total first-return skeleton fitting the trace and signature budget; unused capacity is permitted. -/

import Std.Sat.CNF.Basic
import D5.S0.Automata.FiniteSampleSkeletonTotalization

/- Library-first audit:
   Std.Sat.CNF owns literals, clauses, formula evaluation and unsatisfiability.
   M17 owns Skeleton and its only evaluation function. M19.2 owns IsTotal,
   ReturnPairFiber and the optional-return equivalence. No second DFAO or SAT
   checker is defined. Existing DFAIdentificationCNF only packages an encoding
   supplied by its caller; this module actually enumerates clauses.

   Proposed escape content: slot-budget allocation plus compilation of local
   trace equations into explicit one-hot and implication clauses. Consumers:
   the M19 fixed-capacity refutation instance and its later DIMACS/LRAT bridge.
   No reachability or state-ordering condition is imposed on allocated slots.
   This source is submitted for pinned Lean validation; no acceptance is implied. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SkeletonSlotCNF

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Automata.FiniteSampleSkeletonTotalization

/-- Variables are finite coordinates, independent of any model. -/
inductive Variable (nodes recurrent signatures : Nat)
  | atNode : Fin nodes → Fin recurrent → Variable nodes recurrent signatures
  | viaNode : Fin nodes → Fin signatures → Variable nodes recurrent signatures
  | zero : Fin recurrent → Fin recurrent → Variable nodes recurrent signatures
  | select : Fin recurrent → Fin signatures → Variable nodes recurrent signatures
  | recurrentOutput : Fin recurrent → Fin 4 → Variable nodes recurrent signatures
  | returnTo : Fin signatures → Fin recurrent → Variable nodes recurrent signatures
  | transientOutput : Fin signatures → Fin 4 → Variable nodes recurrent signatures
  deriving DecidableEq, Repr

/-- The finite clause templates emitted below. -/
inductive Requirement (Var : Type*)
  | oneOf : List Var → Requirement Var
  | apart : Var → Var → Requirement Var
  | unit : Var → Requirement Var
  | implies : Var → Var → Requirement Var
  | triangle : Var → Var → Var → Requirement Var

namespace Requirement

variable {Var : Type*}

/-- Model obligations for each syntactic clause template. -/
def Holds (v : Var → Bool) : Requirement Var → Prop
  | .oneOf xs => ∃ x ∈ xs, v x = true
  | .apart x y => v x = true → v y = true → False
  | .unit x => v x = true
  | .implies x y => v x = true → v y = true
  | .triangle x y z => v x = true → v y = true → v z = true

/-- Compile templates to the upstream literal convention `(variable, polarity)`. -/
def toClause : Requirement Var → Std.Sat.CNF.Clause Var
  | .oneOf xs => xs.map fun x => (x, true)
  | .apart x y => [(x, false), (y, false)]
  | .unit x => [(x, true)]
  | .implies x y => [(x, false), (y, true)]
  | .triangle x y z => [(x, false), (y, false), (z, true)]

/-- Every satisfied template compiles to a satisfied native CNF clause. -/
theorem toClause_sound (v : Var → Bool) (req : Requirement Var)
    (h : Holds v req) : (toClause req).eval v = true := by
  cases req with
  | oneOf xs =>
      obtain ⟨x, hx, hv⟩ := h
      simp only [toClause, Std.Sat.CNF.Clause.eval, List.any_eq_true]
      exact ⟨(x, true), List.mem_map.mpr ⟨x, hx, rfl⟩, by simp [hv]⟩
  | apart x y =>
      cases hx : v x <;> cases hy : v y <;>
        simp_all [Holds, toClause, Std.Sat.CNF.Clause.eval]
  | unit x => simpa [toClause, Std.Sat.CNF.Clause.eval] using h
  | implies x y =>
      cases hx : v x <;> cases hy : v y <;>
        simp_all [Holds, toClause, Std.Sat.CNF.Clause.eval]
  | triangle x y z =>
      cases hx : v x <;> cases hy : v y <;> cases hz : v z <;>
        simp_all [Holds, toClause, Std.Sat.CNF.Clause.eval]

end Requirement

/-- An at-least-one clause and all unequal-index at-most-one clauses. -/
def oneHot {Var : Type*} {n : Nat} (name : Fin n → Var) : List (Requirement Var) :=
  [.oneOf ((List.finRange n).map name)] ++
    (List.finRange n).flatMap fun i =>
      (List.finRange n).flatMap fun j =>
        if i = j then [] else [.apart (name i) (name j)]

private theorem oneHot_holds {Var : Type*} {n : Nat} (v : Var → Bool)
    (name : Fin n → Var) (chosen : Fin n)
    (values : ∀ i, v (name i) = decide (i = chosen)) :
    ∀ req ∈ oneHot name, req.Holds v := by
  intro req member
  simp only [oneHot, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | member
  · exact ⟨name chosen, List.mem_map.mpr ⟨chosen, by simp, rfl⟩,
      by rw [values]; simp⟩
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp member
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hi
    split_ifs at hj with different
    · simp at hj
    · have eqReq : req = .apart (name i) (name j) := by simpa using hj
      subst req
      intro vi vj
      have ei : i = chosen := of_decide_eq_true ((values i).symm.trans vi)
      have ej : j = chosen := of_decide_eq_true ((values j).symm.trans vj)
      exact different (ei.trans ej.symm)

/-- A bounded trace edge; node allocation and reachability are separate. -/
structure Edge (nodes : Nat) where
  source : Fin nodes
  block : ReturnBlock
  target : Fin nodes
  deriving DecidableEq, Repr

/-- A terminal observation at a trace node. -/
structure Observation (nodes : Nat) where
  node : Fin nodes
  channel : TerminalChannel
  label : Fin 4
  deriving DecidableEq, Repr

/-- Finite trace data. Roots can share a node or occur independently. -/
structure Trace (nodes : Nat) where
  roots : List (Fin nodes)
  edges : List (Edge nodes)
  observations : List (Observation nodes)
  deriving Repr

/-- The block action already implicit in M17 evaluation. -/
def blockStep {State : Type*} (K : Skeleton (Fin 4) State) :
    ReturnBlock → State → Option State
  | .zero, q => K.zeroStep q
  | .oneZero, q => (K.oneSignature q).bind Prod.snd

/-- Local equations witnessed by the runs in a finite sample presentation. -/
structure FitsTrace {nodes : Nat} {State : Type*}
    (K : Skeleton (Fin 4) State) (T : Trace nodes) (color : Fin nodes → State) : Prop where
  roots : ∀ u ∈ T.roots, color u = K.start
  edges : ∀ e ∈ T.edges, blockStep K e.block (color e.source) = some (color e.target)
  observations : ∀ o ∈ T.observations,
    K.evalFrom (color o.node) [] o.channel = some o.label

/-- A serialization witness on signature slots, with equations to the existing
Skeleton. It supplies no alternate evaluation semantics and need not use all slots. -/
structure SlotWitness {r : Nat} (K : Skeleton (Fin 4) (Fin r)) (s : Nat) where
  zeroTarget : Fin r → Fin r
  slotOf : Fin r → Fin s
  returnTarget : Fin s → Fin r
  transientOutput : Fin s → Fin 4
  zero_eq : ∀ q, K.zeroStep q = some (zeroTarget q)
  one_eq : ∀ q, K.oneSignature q =
    some (transientOutput (slotOf q), some (returnTarget (slotOf q)))

/-- Every total skeleton fitting the used-pair budget has a slot serialization.
Unused slots repeat an existing pair and are not required to be reachable. -/
noncomputable def slotsOfBudget {r s : Nat} (K : Skeleton (Fin 4) (Fin r))
    (total : IsTotal K) (budget : Fintype.card (ReturnPairFiber K) ≤ s) :
    SlotWitness K s := by
  classical
  have available : ∀ q, ∃ p : ReturnPairFiber K,
      K.oneSignature q = some (p.1.1, some p.1.2) := by
    intro q
    obtain ⟨o, t, h⟩ := total.2 q
    exact ⟨⟨(o, t), ⟨q, h⟩⟩, h⟩
  let pairAt (q : Fin r) : ReturnPairFiber K := Classical.choose (available q)
  have pairAt_eq (q : Fin r) :
      K.oneSignature q = some ((pairAt q).1.1, some (pairAt q).1.2) :=
    Classical.choose_spec (available q)
  let enumeration := Fintype.equivFin (ReturnPairFiber K)
  let index (p : ReturnPairFiber K) : Fin s :=
    ⟨(enumeration p).val, lt_of_lt_of_le (enumeration p).isLt budget⟩
  let select (j : Fin s) : ReturnPairFiber K :=
    if h : j.val < Fintype.card (ReturnPairFiber K) then
      enumeration.symm ⟨j.val, h⟩ else pairAt K.start
  have select_index (p : ReturnPairFiber K) : select (index p) = p := by
    dsimp only [select, index]
    rw [dif_pos (enumeration p).isLt]
    exact enumeration.symm_apply_apply p
  refine {
    zeroTarget := fun q => Classical.choose (total.1 q)
    slotOf := fun q => index (pairAt q)
    returnTarget := fun j => (select j).1.2
    transientOutput := fun j => (select j).1.1
    zero_eq := fun q => Classical.choose_spec (total.1 q)
    one_eq := ?_ }
  intro q
  rw [select_index]
  exact pairAt_eq q

section Encoding

variable {n r s : Nat}

/-- One-hot recurrent and transient-slot colors for every trace node. -/
def nodeRows (n r s : Nat) : List (Requirement (Variable n r s)) :=
  (List.finRange n).flatMap fun u =>
    oneHot (Variable.atNode u) ++ oneHot (Variable.viaNode u)

/-- Total zero rows, signature selection rows and four-valued recurrent outputs. -/
def recurrentRows (n r s : Nat) : List (Requirement (Variable n r s)) :=
  (List.finRange r).flatMap fun q =>
    (oneHot (Variable.zero q) ++ oneHot (Variable.select q)) ++
      oneHot (Variable.recurrentOutput q)

/-- Total return rows and four-valued transient outputs, including unused slots. -/
def signatureRows (n r s : Nat) : List (Requirement (Variable n r s)) :=
  (List.finRange s).flatMap fun j =>
    oneHot (Variable.returnTo j) ++ oneHot (Variable.transientOutput j)

/-- Factor each node's one-channel through its recurrent state's signature slot. -/
def linkRows (n r s : Nat) : List (Requirement (Variable n r s)) :=
  (List.finRange n).flatMap fun u =>
    (List.finRange r).flatMap fun q =>
      (List.finRange s).map fun j =>
        .triangle (.atNode u q) (.select q j) (.viaNode u j)

/-- A 10 edge uses the intermediate signature slot, avoiding a cubic product. -/
def edgeRows (r s : Nat) (e : Edge n) : List (Requirement (Variable n r s)) :=
  match e.block with
  | .zero => (List.finRange r).flatMap fun q =>
      (List.finRange r).map fun t =>
        .triangle (.atNode e.source q) (.zero q t) (.atNode e.target t)
  | .oneZero => (List.finRange s).flatMap fun j =>
      (List.finRange r).map fun t =>
        .triangle (.viaNode e.source j) (.returnTo j t) (.atNode e.target t)

/-- Keep all four output labels distinct on both terminal channels. -/
def observationRows (r s : Nat) (o : Observation n) :
    List (Requirement (Variable n r s)) :=
  match o.channel with
  | .recurrent => (List.finRange r).map fun q =>
      .implies (.atNode o.node q) (.recurrentOutput q o.label)
  | .transient => (List.finRange s).map fun j =>
      .implies (.viaNode o.node j) (.transientOutput j o.label)

/-- Fully concrete finite templates. No reachability or state-ordering axiom. -/
def requirements (T : Trace n) (start : Fin r) (s : Nat) :
    List (Requirement (Variable n r s)) :=
  ((((((nodeRows n r s ++ recurrentRows n r s) ++ signatureRows n r s) ++
    linkRows n r s) ++ T.edges.flatMap (edgeRows r s)) ++
    T.observations.flatMap (observationRows r s)) ++
    T.roots.map (fun u => .unit (.atNode u start))) ++
    [.unit (.zero start start), .unit (.recurrentOutput start 0)]

/-- Build the upstream CNF by pushing compiled clauses. The resulting array
has the reverse of template order; that order is part of the serialization contract. -/
def compile {Var : Type*} : List (Requirement Var) → Std.Sat.CNF Var
  | [] => .empty
  | req :: rest => (compile rest).add req.toClause

/-- The executable fixed-capacity formula. -/
def encode (T : Trace n) (start : Fin r) (s : Nat) : Std.Sat.CNF (Variable n r s) :=
  compile (requirements T start s)

/-- Explicit satisfying assignment induced by the skeleton and its trace runs. -/
def modelValuation (K : Skeleton (Fin 4) (Fin r)) (W : SlotWitness K s)
    (color : Fin n → Fin r) : Variable n r s → Bool
  | .atNode u q => decide (color u = q)
  | .viaNode u j => decide (W.slotOf (color u) = j)
  | .zero q t => decide (W.zeroTarget q = t)
  | .select q j => decide (W.slotOf q = j)
  | .recurrentOutput q o => decide (K.zeroOutput q = o)
  | .returnTo j t => decide (W.returnTarget j = t)
  | .transientOutput j o => decide (W.transientOutput j = o)

private theorem compile_sound {Var : Type*} (v : Var → Bool)
    (reqs : List (Requirement Var)) (holds : ∀ req ∈ reqs, req.Holds v) :
    (compile reqs).eval v = true := by
  induction reqs with
  | nil => simp [compile]
  | cons req rest ih =>
      have first := Requirement.toClause_sound v req (holds req (by simp))
      have tail := ih (fun q hq => holds q (by simp [hq]))
      simp [compile, Std.Sat.CNF.eval_add, first, tail]

private theorem rows_hold (K : Skeleton (Fin 4) (Fin r)) (W : SlotWitness K s)
    (color : Fin n → Fin r) :
    ∀ req ∈ (nodeRows n r s ++ recurrentRows n r s) ++ signatureRows n r s,
      req.Holds (modelValuation K W color) := by
  intro req member
  simp only [List.mem_append] at member
  rcases member with (hn | hr) | hs
  · obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hn
    rcases List.mem_append.mp hu with ha | hv
    · exact oneHot_holds _ _ (color u)
        (by intro q; simp [modelValuation, eq_comm]) req ha
    · exact oneHot_holds _ _ (W.slotOf (color u))
        (by intro j; simp [modelValuation, eq_comm]) req hv
  · obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hr
    simp only [List.mem_append] at hq
    rcases hq with (hz | hc) | hf
    · exact oneHot_holds _ _ (W.zeroTarget q)
        (by intro t; simp [modelValuation, eq_comm]) req hz
    · exact oneHot_holds _ _ (W.slotOf q)
        (by intro j; simp [modelValuation, eq_comm]) req hc
    · exact oneHot_holds _ _ (K.zeroOutput q)
        (by intro o; simp [modelValuation, eq_comm]) req hf
  · obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hj with ht | hg
    · exact oneHot_holds _ _ (W.returnTarget j)
        (by intro t; simp [modelValuation, eq_comm]) req ht
    · exact oneHot_holds _ _ (W.transientOutput j)
        (by intro o; simp [modelValuation, eq_comm]) req hg

private theorem links_hold (K : Skeleton (Fin 4) (Fin r)) (W : SlotWitness K s)
    (color : Fin n → Fin r) :
    ∀ req ∈ linkRows n r s, req.Holds (modelValuation K W color) := by
  intro req member
  obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp member
  obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hu
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
  simp only [Requirement.Holds, modelValuation, decide_eq_true_eq]
  intro hc hj
  simpa only [hc] using hj

private theorem edge_rows_hold (K : Skeleton (Fin 4) (Fin r)) (W : SlotWitness K s)
    (color : Fin n → Fin r) (e : Edge n)
    (edge : blockStep K e.block (color e.source) = some (color e.target)) :
    ∀ req ∈ edgeRows r s e, req.Holds (modelValuation K W color) := by
  cases hb : e.block with
  | zero =>
      have htarget : W.zeroTarget (color e.source) = color e.target := by
        simpa only [hb, blockStep, W.zero_eq, Option.some.injEq] using edge
      intro req member
      rw [edgeRows, hb] at member
      obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp member
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
      simp only [Requirement.Holds, modelValuation, decide_eq_true_eq]
      intro hc ht
      calc
        color e.target = W.zeroTarget (color e.source) := htarget.symm
        _ = W.zeroTarget q := congrArg W.zeroTarget hc
        _ = t := ht
  | oneZero =>
      have htarget : W.returnTarget (W.slotOf (color e.source)) = color e.target := by
        simpa only [hb, blockStep, W.one_eq, Option.bind_some, Option.some.injEq]
          using edge
      intro req member
      rw [edgeRows, hb] at member
      obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp member
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hj
      simp only [Requirement.Holds, modelValuation, decide_eq_true_eq]
      intro hc ht
      calc
        color e.target = W.returnTarget (W.slotOf (color e.source)) := htarget.symm
        _ = W.returnTarget j := congrArg W.returnTarget hc
        _ = t := ht

private theorem observation_rows_hold (K : Skeleton (Fin 4) (Fin r))
    (W : SlotWitness K s) (color : Fin n → Fin r) (o : Observation n)
    (observed : K.evalFrom (color o.node) [] o.channel = some o.label) :
    ∀ req ∈ observationRows r s o, req.Holds (modelValuation K W color) := by
  cases hc : o.channel with
  | recurrent =>
      have ho : K.zeroOutput (color o.node) = o.label := by
        simpa only [hc, Skeleton.evalFrom, Option.some.injEq] using observed
      intro req member
      rw [observationRows, hc] at member
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
      simp only [Requirement.Holds, modelValuation, decide_eq_true_eq]
      intro eqColor
      simpa only [eqColor] using ho
  | transient =>
      have ho : W.transientOutput (W.slotOf (color o.node)) = o.label := by
        simpa only [hc, Skeleton.evalFrom, W.one_eq, Option.map_some, Option.some.injEq]
          using observed
      intro req member
      rw [observationRows, hc] at member
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
      simp only [Requirement.Holds, modelValuation, decide_eq_true_eq]
      intro eqSlot
      simpa only [eqSlot] using ho

/-- Main compiler theorem. All clauses are generated here; no model-to-SAT
implication or CNF formula is taken as an assumed field. -/
theorem model_to_sat (K : Skeleton (Fin 4) (Fin r)) (W : SlotWitness K s)
    (T : Trace n) (color : Fin n → Fin r) (fits : FitsTrace K T color)
    (zeroLoop : K.zeroStep K.start = some K.start)
    (zeroAnchor : K.zeroOutput K.start = 0) :
    Std.Sat.CNF.Sat (modelValuation K W color) (encode T K.start s) := by
  apply compile_sound
  intro req member
  have rows := rows_hold K W color
  have links := links_hold K W color
  have hz : W.zeroTarget K.start = K.start :=
    Option.some.inj ((W.zero_eq K.start).symm.trans zeroLoop)
  simp only [requirements, List.mem_append] at member
  rcases member with ((((((hn | hr) | hs) | hl) | he) | ho) | ha) | hb
  · exact rows req (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hn))))
  · exact rows req (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr))))
  · exact rows req (List.mem_append.mpr (Or.inr hs))
  · exact links req hl
  · obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp he
    exact edge_rows_hold K W color e (fits.edges e he) req hr
  · obtain ⟨o, ho, hr⟩ := List.mem_flatMap.mp ho
    exact observation_rows_hold K W color o (fits.observations o ho) req hr
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    simpa only [Requirement.Holds, modelValuation, decide_eq_true_eq] using fits.roots u hu
  · simp only [List.mem_cons, List.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simpa only [Requirement.Holds, modelValuation, decide_eq_true_eq] using hz
    · simpa only [Requirement.Holds, modelValuation, decide_eq_true_eq] using zeroAnchor

/-- Used-signature budget plus totality now imply satisfiability of an actual
finite CNF, via a constructed allocation of the signature slots. -/
theorem budget_model_has_satisfying_assignment (K : Skeleton (Fin 4) (Fin r))
    (T : Trace n) (color : Fin n → Fin r) (total : IsTotal K)
    (budget : Fintype.card (ReturnPairFiber K) ≤ s) (fits : FitsTrace K T color)
    (zeroLoop : K.zeroStep K.start = some K.start)
    (zeroAnchor : K.zeroOutput K.start = 0) :
    ∃ v, Std.Sat.CNF.Sat v (encode T K.start s) := by
  exact ⟨modelValuation K (slotsOfBudget K total budget) color,
    model_to_sat K (slotsOfBudget K total budget) T color fits zeroLoop zeroAnchor⟩

/-- A refutation of this concrete formula rules out every model covered by the
compiler theorem. A concrete refutation and oracle-to-trace transport remain separate. -/
theorem model_excluded_by_unsat (K : Skeleton (Fin 4) (Fin r))
    (T : Trace n) (color : Fin n → Fin r) (total : IsTotal K)
    (budget : Fintype.card (ReturnPairFiber K) ≤ s) (fits : FitsTrace K T color)
    (zeroLoop : K.zeroStep K.start = some K.start)
    (zeroAnchor : K.zeroOutput K.start = 0)
    (unsat : Std.Sat.CNF.Unsat (encode T K.start s)) : False := by
  obtain ⟨v, hv⟩ := budget_model_has_satisfying_assignment K T color total budget
    fits zeroLoop zeroAnchor
  have hu := unsat v
  change (encode T K.start s).eval v = true at hv
  rw [hv] at hu
  cases hu

#print axioms model_to_sat
#print axioms budget_model_has_satisfying_assignment
#print axioms model_excluded_by_unsat

end Encoding
end D5.S0.Certificates.SkeletonSlotCNF
