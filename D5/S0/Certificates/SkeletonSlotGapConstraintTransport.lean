/- GID: D5/S0/Certificates/SkeletonSlotGapConstraintTransport
   generality: G
   mirror-B: D5/B/S0/Certificates/SkeletonSlotGapConstraintTransport
   mirror-E: none(waiver:finite-gap-trace-transport)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   digest: Actual slot runs induce solutions of the existing shared-selection constraints, with terminal domains derived from fitted observations. -/

import D5.S0.Certificates.SkeletonSlotZeroResponse
import D5.S0.Certificates.FiniteDomainSelectionRefutation
import Mathlib.Logic.Equiv.Fin.Basic

/- This closes the slot-run to finite-selection-system connection. A gap index k
   means k+1 zeroes between two ones. The actual binary expansion is owned by
   BinaryZeckendorfBlockSkeleton.expandCode. No new automaton is introduced.
   The concrete external B/L parser, color normalization, and acceptance of the
   stored million-node certificate in Lean remain separate obligations.
   These proof bodies have not been compiled in this authoring runtime. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SkeletonSlotGapConstraintTransport

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Certificates.SkeletonSlotCNF
open D5.S0.Certificates.SkeletonSlotZeroResponse
open D5.S0.Certificates.FiniteDomainSelectionRefutation

variable {r s : Nat} {K : Skeleton (Fin 4) (Fin r)}

/-- Return blocks preceding the final one of a nonzero gap-coded word. -/
def gapBlocks : List Nat → List ReturnBlock
  | [] => []
  | k :: rest => .oneZero :: (List.replicate k .zero ++ gapBlocks rest)

private def finishBlocks : TerminalChannel → List ReturnBlock
  | .transient => []
  | .recurrent => [.oneZero]

/-- Transient termination means a final one; recurrent termination appends zero. -/
def gapCode (gaps : List Nat) (channel : TerminalChannel) : BlockCode :=
  ⟨gapBlocks gaps ++ finishBlocks channel, channel⟩

/-- Read either the transient digit or the digit after its zero return. -/
def slotReadout (W : SlotWitness K s) : TerminalChannel → Fin s → Fin 4
  | .transient, t => W.transientOutput t
  | .recurrent, t => K.zeroOutput (W.returnTarget t)

/-- Finite composition of the gap maps already derived from the slot witness. -/
def traceFrom (W : SlotWitness K s) (t : Fin s) (gaps : List Nat) : Fin s :=
  gaps.foldl (fun u k => gapSlot W k u) t

private theorem consume_gap (W : SlotWitness K s) (q : Fin r) (k : Nat)
    (rest : List ReturnBlock) (channel : TerminalChannel) :
    K.evalFrom q (.oneZero :: (List.replicate k .zero ++ rest)) channel =
      K.evalFrom (advance W k (W.returnTarget (W.slotOf q))) rest channel := by
  change (K.oneSignature q).bind (fun pair => pair.2.bind
    (fun next => K.evalFrom next (List.replicate k .zero ++ rest) channel)) = _
  rw [W.one_eq]
  simp only [Option.bind_some]
  exact evalFrom_zero_prefix W k (W.returnTarget (W.slotOf q)) rest channel

/-- Arbitrary gap lists and both terminal channels agree with the existing
Option-valued skeleton evaluation. This is not a finite regression assertion. -/
theorem eval_gapCode (W : SlotWitness K s) (q : Fin r)
    (gaps : List Nat) (channel : TerminalChannel) :
    K.evalFrom q (gapCode gaps channel).blocks channel =
      some (slotReadout W channel (traceFrom W (W.slotOf q) gaps)) := by
  induction gaps generalizing q with
  | nil =>
      cases channel <;>
        simp [gapCode, gapBlocks, finishBlocks, traceFrom, slotReadout,
          Skeleton.evalFrom, W.one_eq]
  | cons k gaps ih =>
      simp only [gapCode, gapBlocks, List.cons_append, List.append_assoc]
      rw [consume_gap]
      simpa only [gapCode, traceFrom, List.foldl_cons, gapSlot] using
        ih (advance W k (W.returnTarget (W.slotOf q)))

/-- Standard row-major numbering: table coordinates first, then trace nodes. -/
def variableIndex (letters colors nodes : Nat) :
    ((Fin letters × Fin colors) ⊕ Fin nodes) ≃ Fin (letters * colors + nodes) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin nodes))).trans finSumFinEquiv

/-- A gap edge is encoded in the existing table-selection constraint type. -/
def gapSelection {letters nodes : Nat} (colors : Nat)
    (parent child : Fin nodes) (letter : Fin letters) :
    Selection colors (letters * colors + nodes) where
  parent := variableIndex letters colors nodes (.inr parent)
  child := variableIndex letters colors nodes (.inr child)
  row := fun t => variableIndex letters colors nodes (.inl (letter, t))

/-- The actual transient state at a recorded gap prefix. -/
def traceColor {letters nodes : Nat} (W : SlotWitness K s)
    (lengths : Fin letters → Nat) (paths : Fin nodes → List (Fin letters))
    (i : Fin nodes) : Fin s :=
  traceFrom W (W.slotOf K.start) ((paths i).map lengths)

/-- Both shared tables and trace coordinates are filled by actual machine values. -/
def inducedAssignment {letters nodes : Nat} (W : SlotWitness K s)
    (lengths : Fin letters → Nat) (paths : Fin nodes → List (Fin letters)) :
    Assignment s (letters * s + nodes) := fun v =>
  match (variableIndex letters s nodes).symm v with
  | .inl (g, t) => gapSlot W (lengths g) t
  | .inr i => traceColor W lengths paths i

private theorem assigned_table {letters nodes : Nat} (W : SlotWitness K s)
    (lengths : Fin letters → Nat) (paths : Fin nodes → List (Fin letters))
    (g : Fin letters) (t : Fin s) :
    inducedAssignment W lengths paths (variableIndex letters s nodes (.inl (g,t))) =
      gapSlot W (lengths g) t := by simp [inducedAssignment]

private theorem assigned_trace {letters nodes : Nat} (W : SlotWitness K s)
    (lengths : Fin letters → Nat) (paths : Fin nodes → List (Fin letters))
    (i : Fin nodes) :
    inducedAssignment W lengths paths (variableIndex letters s nodes (.inr i)) =
      traceColor W lengths paths i := by simp [inducedAssignment]

/-- A checked path-incidence identity gives the exact shared local equation. -/
theorem induced_selection_holds {letters nodes : Nat} (W : SlotWitness K s)
    (lengths : Fin letters → Nat) (paths : Fin nodes → List (Fin letters))
    (parent child : Fin nodes) (letter : Fin letters)
    (incidence : paths child = paths parent ++ [letter]) :
    (gapSelection s parent child letter).Holds (inducedAssignment W lengths paths) := by
  simp only [Selection.Holds, gapSelection, assigned_trace, assigned_table]
  simp only [traceColor, incidence, List.map_append, List.map_cons, List.map_nil,
    traceFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Allowed trace values come solely from the terminal observations. The
candidate's readouts remain parameters until a proved normalization fixes them. -/
def observationDomains {letters nodes : Nat} (W : SlotWitness K s)
    (observations : List (Observation nodes)) : Domains s (letters * s + nodes) :=
  fun v => match (variableIndex letters s nodes).symm v with
  | .inl _ => Finset.univ
  | .inr i => Finset.univ.filter fun t =>
      ∀ o ∈ observations, o.node = i → slotReadout W o.channel t = o.label

/-- Fitting actual encoded words implies the induced values meet their domains. -/
theorem induced_assignment_in_domains {letters nodes : Nat} (W : SlotWitness K s)
    (lengths : Fin letters → Nat) (paths : Fin nodes → List (Fin letters))
    (observations : List (Observation nodes))
    (fits : ∀ o ∈ observations,
      K.evalFrom K.start (gapCode ((paths o.node).map lengths) o.channel).blocks
        o.channel = some o.label) :
    InDomains (observationDomains (letters := letters) W observations)
      (inducedAssignment W lengths paths) := by
  intro v
  cases hv : (variableIndex letters s nodes).symm v with
  | inl pair => simp [observationDomains, hv]
  | inr i =>
      simp only [observationDomains, inducedAssignment, hv,
        Finset.mem_filter, Finset.mem_univ, true_and]
      intro o ho hi
      subst i
      have h := fits o ho
      rw [eval_gapCode] at h
      exact Option.some.inj h

/-- Every fitted slot witness induces a solution of the actual selection CSP.
Only finite syntactic incidence and the original sample-fitting equations are
premises. No correctness field for a replacement automaton is assumed. -/
theorem fitted_slots_induce_selection_solution {letters nodes edges : Nat}
    (W : SlotWitness K s) (lengths : Fin letters → Nat)
    (paths : Fin nodes → List (Fin letters))
    (parent child : Fin edges → Fin nodes) (letter : Fin edges → Fin letters)
    (incidence : ∀ j, paths (child j) = paths (parent j) ++ [letter j])
    (observations : List (Observation nodes))
    (fits : ∀ o ∈ observations,
      K.evalFrom K.start (gapCode ((paths o.node).map lengths) o.channel).blocks
        o.channel = some o.label) :
    ∃ x : Assignment s (letters * s + nodes),
      InDomains (observationDomains (letters := letters) W observations) x ∧
      Solves (fun j => gapSelection s (parent j) (child j) (letter j)) x := by
  refine ⟨inducedAssignment W lengths paths,
    induced_assignment_in_domains W lengths paths observations fits, ?_⟩
  intro j
  exact induced_selection_holds W lengths paths (parent j) (child j) (letter j)
    (incidence j)

#print axioms eval_gapCode
#print axioms fitted_slots_induce_selection_solution

end D5.S0.Certificates.SkeletonSlotGapConstraintTransport
