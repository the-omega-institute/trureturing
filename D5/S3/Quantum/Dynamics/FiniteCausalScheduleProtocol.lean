/- GID: D5/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Actual finite causal schedules compile to normalized adaptive quantum programs. -/

import D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
import D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
open D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

/-- Every cut has its actual finite interface and decidable matrix coordinates. -/
structure Interface where
  carrier : Type
  finite : Fintype carrier
  decidable : DecidableEq carrier

instance (I : Interface) : Fintype I.carrier := I.finite
instance (I : Interface) : DecidableEq I.carrier := I.decidable
abbrev CutState (I : Interface) := State I.carrier

/-- An executable finite quantum program. Outcomes control the actual next instruction;
hidden Kraus indices are summed and are never supplied to the child function. -/
inductive Program : Interface → Type 1
  | stop (I : Interface) : Program I
  | node {I O : Interface}
      (J : Instrument I.carrier O.carrier) (child : Fin J.outcomes → Program O) : Program I

/-- An independently assigned relation-graph state at every observed prefix. -/
inductive Assignment : {I : Interface} → Program I → Type 1
  | stop {I : Interface} (X : CutState I) : Assignment (.stop I)
  | node {I O : Interface}
      {J : Instrument I.carrier O.carrier} {child : Fin J.outcomes → Program O}
      (X : CutState I) (below : ∀ a, Assignment (child a)) : Assignment (.node J child)

def rootValue : {I : Interface} → {P : Program I} → Assignment P → CutState I
  | _, .stop _, .stop X => X
  | _, .node _ _, .node X _ => X

def GraphLaw : {I : Interface} → {P : Program I} → Assignment P → Prop
  | _, .stop _, .stop _ => True
  | _, .node J _, .node X below => ∀ a,
      rootValue (below a) = branch (J.kraus a) X ∧ GraphLaw (below a)

def evaluate : {I : Interface} → (P : Program I) → CutState I → Assignment P
  | _, .stop _, X => .stop X
  | _, .node J child, X => .node X (fun a => evaluate (child a) (branch (J.kraus a) X))

/-- Actual records and full retained matrices, allowing outcome-dependent termination. -/
structure Terminal where
  history : List ℕ
  interface : Interface
  state : CutState interface

def leaves : {I : Interface} → {P : Program I} → Assignment P → List Terminal
  | I, .stop _, .stop X => [⟨[],I,X⟩]
  | _, .node _ _, .node _ below =>
      (List.ofFn (fun a => (leaves (below a)).map
        (fun z => {z with history := a.val :: z.history}))).flatten

private theorem evaluate_root {I : Interface} (P : Program I) (X : CutState I) :
    rootValue (evaluate P X) = X := by cases P <;> rfl

private theorem evaluate_law {I : Interface} (P : Program I) (X : CutState I) :
    GraphLaw (evaluate P X) := by
  induction P with
  | stop => trivial
  | node J child ih => exact fun a => ⟨evaluate_root _ _, ih a _⟩

private theorem law_unique {I : Interface} (P : Program I) (φ ψ : Assignment P)
    (hφ : GraphLaw φ) (hψ : GraphLaw ψ) (hr : rootValue φ = rootValue ψ) : φ = ψ := by
  induction P with
  | stop => cases φ; cases ψ; exact congrArg Assignment.stop hr
  | node J child ih =>
    cases φ with | node X below =>
      cases ψ with | node Y below' =>
        have hxy : X = Y := hr
        subst Y
        have hb : below = below' := by
          funext a
          exact ih a _ _ (hφ a).2 (hψ a).2 ((hφ a).1.trans (hψ a).1.symm)
        cases hb
        rfl

private theorem instrument_trace (I O : Interface) (J : Instrument I.carrier O.carrier)
    (X : CutState I) : ∑ a, Matrix.trace (branch (J.kraus a) X) = Matrix.trace X := by
  let K (p : Fin J.outcomes × Fin J.hidden) := J.kraus p.1 p.2
  obtain ⟨C,hC⟩ := D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    K (by simpa [K,Fintype.sum_prod_type] using J.normalized)
  have ht := C.trace_preserving (CStarMatrix.ofMatrix X)
  change Matrix.trace (CStarMatrix.ofMatrix.symm
    (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = Matrix.trace X at ht
  rw [hC] at ht
  simpa only [K,Fintype.sum_prod_type,branch,Matrix.trace_sum] using ht

private theorem evaluate_total_trace {I : Interface} (P : Program I) (X : CutState I) :
    ((leaves (evaluate P X)).map (fun z => Matrix.trace z.state)).sum = Matrix.trace X := by
  induction P with
  | stop => simp [evaluate,leaves]
  | @node I O J child ih =>
    simp only [evaluate,leaves,List.map_flatten,List.sum_flatten,List.map_ofFn,
      List.map_map,List.sum_ofFn,Function.comp_def]
    change (∑ a, ((leaves (evaluate (child a) (branch (J.kraus a) X))).map
      (fun z => Matrix.trace z.state)).sum) = _
    simp_rw [ih]
    exact instrument_trace I O J X

/-- Every finite adaptive program is precisely a static relation-graph solution.
The assigned terminal matrices retain every correlation. Local CPTP normalization conserves
terminal probability on all input matrices, including early termination. -/
theorem program_graph_correspondence {I : Interface} (P : Program I) (X : CutState I) :
    ∃! φ : Assignment P, GraphLaw φ ∧ rootValue φ = X ∧
      ((leaves φ).map (fun z => Matrix.trace z.state)).sum = Matrix.trace X := by
  refine ⟨evaluate P X,⟨evaluate_law P X,evaluate_root P X,evaluate_total_trace P X⟩,?_⟩
  intro φ hφ
  exact law_unique P φ (evaluate P X) hφ.1 (evaluate_law P X)
    (hφ.2.1.trans (evaluate_root P X).symm)

variable {E : Type} [PartialOrder E]

abbrev LocalRecords (G : QuantumPortGraph E) (K : Set E) :=
  ∀ d : K, Fin (G.outcomes d)

/-- Extend only the actual observed record; no future or hidden label is available. -/
def extendRecord (G : QuantumPortGraph E) {K : Set E} {e : E}
    (h : LocalRecords G K) (a : Fin (G.outcomes e)) : LocalRecords G (insert e K) := by
  classical
  intro d
  by_cases hd : d.1 = e
  · exact Eq.mpr (congrArg (fun x => Fin (G.outcomes x)) hd) a
  · exact h ⟨d.1, (Set.mem_insert_iff.mp d.2).resolve_left hd⟩

def cutInterface (G : QuantumPortGraph E) (K : Set E) : Interface :=
  ⟨G.cut K,G.finiteCut K,G.decidableCut K⟩

/-- The compiler consumes one positive event occurrence per recursive level.
Its depth is bounded by the finite schedule length, even when outcome sets are empty. -/
def compile (G : QuantumPortGraph E) :
    ∀ {K L : Set E} (l : List E), Exec K l L → LocalRecords G K → Program (cutInterface G K)
  | K, _, [], _, _ => .stop (cutInterface G K)
  | K, _, e :: l, hl, h =>
    let J : Instrument (cutInterface G K).carrier (cutInterface G (insert e K)).carrier := {
      outcomes := G.outcomes e
      hidden := G.hidden e
      kraus := G.kraus hl.1 h
      normalized := G.normalized hl.1 h }
    .node (I := cutInterface G K) (O := cutInterface G (insert e K)) J (fun a => compile G l hl.2 (extendRecord G h a))

private theorem extend_restrict (G : QuantumPortGraph E) {K : Set E} {e : E}
    (h : Records G.outcomes) :
    extendRecord G (fun d : K => h d) (h e) = (fun d : ↥(insert e K) => h d) := by
  classical
  funext d
  by_cases hd : d.1 = e
  · have cast_apply {a b : E} (heq : a = b) :
        Eq.mpr (congrArg (fun x => Fin (G.outcomes x)) heq) (h b) = h a := by
      cases heq
      rfl
    simpa only [extendRecord,dif_pos hd] using cast_apply hd
  · simp [extendRecord,hd]

/-- Every fixed event-indexed outcome record is realized by the compiler's corresponding
observed branch, with exactly the original full joint cut matrix. -/
private theorem compiled_branch_contains (G : QuantumPortGraph E) {K L : Set E}
    (l : List E) (hl : Exec K l L) (h : Records G.outcomes) (X : State (G.cut K)) :
    (⟨l.map (fun e => (h e).val),cutInterface G L,pathMap (G.readout h) l hl X⟩ : Terminal) ∈
      leaves (evaluate (compile G l hl (fun d : K => h d)) X) := by
  induction l generalizing K with
  | nil => cases hl; simp [compile,evaluate,leaves,pathMap]
  | cons e l ih =>
    letI := G.finiteCut K
    letI := G.finiteCut (insert e K)
    change (⟨(e :: l).map (fun d => (h d).val),cutInterface G L,
      pathMap (G.readout h) (e :: l) hl X⟩ : Terminal) ∈
      (List.ofFn (fun a : Fin (G.outcomes e) =>
        (leaves (evaluate (compile G l hl.2 (extendRecord G (fun d : K => h d) a))
          (branch (G.kraus hl.1 (fun d : K => h d) a) X))).map
          (fun z => {z with history := a.val :: z.history}))).flatten
    simp only [List.mem_flatten,List.mem_ofFn]
    refine ⟨_,⟨h e,rfl⟩,?_⟩
    apply List.mem_map.mpr
    refine ⟨⟨l.map (fun d => (h d).val),cutInterface G L,
      pathMap (G.readout h) l hl.2 ((G.readout h).edge hl.1 X)⟩,?_,rfl⟩
    rw [extend_restrict]
    exact ih hl.2 _

private theorem compiled_history_length (G : QuantumPortGraph E) {K L : Set E}
    (l : List E) (hl : Exec K l L) (h : LocalRecords G K) (X : State (G.cut K)) :
    ∀ z ∈ leaves (evaluate (compile G l hl h) X), z.history.length = l.length := by
  induction l generalizing K with
  | nil =>
    cases hl
    intro z hz
    simp [compile,evaluate,leaves] at hz
    subst z
    rfl
  | cons e l ih =>
    intro z hz
    letI := G.finiteCut K
    letI := G.finiteCut (insert e K)
    change z ∈ (List.ofFn (fun a : Fin (G.outcomes e) =>
      (leaves (evaluate (compile G l hl.2 (extendRecord G h a))
        (branch (G.kraus hl.1 h a) X))).map
        (fun z => {z with history := a.val :: z.history}))).flatten at hz
    simp only [List.mem_flatten,List.mem_ofFn] at hz
    obtain ⟨_,⟨a,rfl⟩,hz⟩ := hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact congrArg Nat.succ (ih hl.2 _ _ w hw)

private theorem execution_occurrence_count {K L : Set E} (l : List E) (hl : Exec K l L)
    (hK : IsLowerSet K) (hL : IsLowerSet L) (hfin : L.Finite) :
    l.length = (L \ K).ncard := by
  classical
  have hs : K ⊆ L := (exec_exists_iff_subset hK hL hfin).mp ⟨l,hl⟩
  have hfk := hfin.subset hs
  let C := hfk.toFinset
  let D := hfin.toFinset
  obtain ⟨p,hp,hplen,hall,_⟩ := finite_history_clocks C D D
    (by simpa [C] using hK) (by simpa [D] using hL)
    (by simpa [C,D] using hs) (by rfl) (fun _ => False) (fun _ => 0)
    (fun _ h => h.elim)
  have hh := hall l (by simpa [C,D] using hl)
  rw [Set.ncard_eq_toFinset_card _ (hfin.sdiff),Set.Finite.toFinset_sdiff hfin hfk]
  exact hh

/-- Compilation gives a genuine normalized relation graph, realizes each observed branch
with its full joint matrix, and preserves that matrix under every legal topological ordering. -/
theorem causal_schedule_realization (G : QuantumPortGraph E) {K L : Set E}
    (l : List E) (hl : Exec K l L) (h : Records G.outcomes) (X : State (G.cut K))
    (hK : IsLowerSet K) (hL : IsLowerSet L) (hfin : L.Finite) :
    letI := G.finiteCut K
    ∃! φ : Assignment (compile G l hl (fun d : K => h d)),
      (GraphLaw φ ∧ rootValue φ = X ∧
        ((leaves φ).map (fun z => Matrix.trace z.state)).sum = Matrix.trace X) ∧
      (⟨l.map (fun e => (h e).val),cutInterface G L,pathMap (G.readout h) l hl X⟩ : Terminal) ∈ leaves φ ∧
      (∀ (m : List E) (hm : Exec K m L),
        pathMap (G.readout h) l hl X = pathMap (G.readout h) m hm X) ∧
      (∀ z ∈ leaves φ, z.history.length = (L \ K).ncard) := by
  letI := G.finiteCut K
  let P := compile G l hl (fun d : K => h d)
  obtain ⟨φ,hφ,huniq⟩ := program_graph_correspondence P X
  have heval : evaluate P X = φ := huniq (evaluate P X)
    ⟨evaluate_law P X,evaluate_root P X,evaluate_total_trace P X⟩
  refine ⟨φ,⟨hφ,?_,?_,?_⟩,?_⟩
  · rw [← heval]
    exact compiled_branch_contains G l hl h X
  · exact fun m hm => quantum_schedule_independence G h hK hL hfin l m hl hm X
  · rw [← heval]
    intro z hz
    exact (compiled_history_length G l hl _ X z hz).trans
      (execution_occurrence_count l hl hK hL hfin)
  · intro ψ hψ
    exact huniq ψ hψ.1

#print axioms program_graph_correspondence
#print axioms compiled_branch_contains
#print axioms causal_schedule_realization
end D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
