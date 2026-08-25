/- GID: D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/WorstCaseDepthInformationLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed B-ary trees satisfy leaf, clog, necessity, and degenerate bounds. -/

import Mathlib

/- Library-search audit trail (2026-08-25):
   * The residue-specialized `adaptiveProtocol`, `adaptiveTranscript`, and
     `ExactAtDepth` shapes were read in full, but that module is not imported here.
   * Exact pinned-Mathlib hits `Finset.card_biUnion_le` and `Finset.card_image_le`
     support the induction bounding the leaves of an arbitrary finite decision tree.
   * Exact pinned-Mathlib hit `Fintype.card_le_of_injective` supplies the injection
     count, and `Nat.clog_le_of_le_pow` supplies the logarithmic conclusion.
     `Nat.clog_le_iff_le_pow` was found but needs `1 < B`, excluding `B = 1`.
   * `Nat.le_pow_iff_clog_le` was not found, while `Nat.pow_log_le_self` concerns
     the floor logarithm and has the opposite role, so neither is used below.
   * `Nat.clog_zero_right` and `Nat.clog_one_left` confirm that empty carriers and
     unary branching have upper logarithm zero. No general adaptive protocol hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound

universe u v

/- The source's `B` is read as a fixed number of possible answers per question.
If the branching factor varied by round, the uniform bound `B ^ h` would not apply. -/

/-- A deterministic protocol with depth at most the index. A leaf may occur under
any remaining budget; a query has one continuation for each answer in `Fin B`. -/
inductive AdaptiveProtocol (State : Type u) (B : Nat) : Nat -> Type u
  | leaf {depth : Nat} : AdaptiveProtocol State B depth
  | query {depth : Nat} (question : State -> Fin B)
      (next : Fin B -> AdaptiveProtocol State B depth) :
      AdaptiveProtocol State B (depth + 1)

/-- The answer path followed by a state until the protocol reaches a leaf. -/
def adaptiveTranscript {State : Type u} {B depth : Nat} :
    AdaptiveProtocol State B depth -> State -> List (Fin B)
  | .leaf, _ => []
  | .query question next, state =>
      let answer := question state
      answer :: adaptiveTranscript (next answer) state

/-- Every question at every reachable node comes from the supplied readout family. -/
def UsesReadoutFamily {Question : Type v} {State : Type u} {B depth : Nat}
    (readout : Question -> State -> Fin B) : AdaptiveProtocol State B depth -> Prop
  | .leaf => True
  | .query question next =>
      (exists selected, question = readout selected) ∧
        forall answer, UsesReadoutFamily readout (next answer)

/-- Exact identification at a depth budget, following the residue-specialized shape. -/
def ExactAtDepth {Question : Type v} {State : Type u} {B : Nat}
    (readout : Question -> State -> Fin B) (depth : Nat) : Prop :=
  exists protocol : AdaptiveProtocol State B depth,
    UsesReadoutFamily readout protocol ∧
      Function.Injective (adaptiveTranscript protocol)

/-- The terminal answer paths, regarded as the leaves of a protocol tree. -/
def adaptiveLeaves {State : Type u} {B depth : Nat} :
    AdaptiveProtocol State B depth -> Finset (List (Fin B))
  | .leaf => {[]}
  | .query _ next =>
      (Finset.univ : Finset (Fin B)).biUnion fun answer =>
        (adaptiveLeaves (next answer)).image (List.cons answer)

/-- The source does not define `D_ad` in this item. This module supplies it as the
least exact-identification depth, with existence passed explicitly to avoid assigning
a finite depth to a family that cannot identify the state space. -/
noncomputable def adaptiveIdentificationDepth
    {Question : Type v} {State : Type u} {B : Nat}
    (readout : Question -> State -> Fin B)
    (identifiable : exists depth, ExactAtDepth readout depth) : Nat := by
  classical
  exact Nat.find identifiable

private theorem adaptive_transcript_mem_leaves
    {State : Type u} {B depth : Nat}
    (protocol : AdaptiveProtocol State B depth) (state : State) :
    adaptiveTranscript protocol state ∈ adaptiveLeaves protocol := by
  induction protocol with
  | leaf => simp [adaptiveTranscript, adaptiveLeaves]
  | query question next ih =>
      simp only [adaptiveTranscript, adaptiveLeaves]
      apply Finset.mem_biUnion.mpr
      refine ⟨question state, Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨adaptiveTranscript (next (question state)) state,
        ih (question state), rfl⟩

/- The premise `1 ≤ B` completes an omitted source-side reasonableness condition:
one question has at least one possible answer. It is necessary because a leaf may
occur while positive depth budget remains; this is not a change to the intended claim. -/
/-- Any deterministic protocol of depth at most `h` has at most `B ^ h` leaves. -/
theorem adaptive_leaf_count_le_pow
    {State : Type u} {B h : Nat} (protocol : AdaptiveProtocol State B h)
    (hB : 1 ≤ B) :
    (adaptiveLeaves protocol).card ≤ B ^ h := by
  induction protocol with
  | @leaf depth =>
      simp only [adaptiveLeaves, Finset.card_singleton]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos hB))
  | @query depth question next ih =>
      calc
        (adaptiveLeaves (.query question next)).card ≤
            ∑ answer ∈ (Finset.univ : Finset (Fin B)),
              ((adaptiveLeaves (next answer)).image (List.cons answer)).card := by
          simpa only [adaptiveLeaves] using Finset.card_biUnion_le
        _ ≤ ∑ _answer ∈ (Finset.univ : Finset (Fin B)), B ^ depth := by
          apply Finset.sum_le_sum
          intro answer _answer_mem
          exact Finset.card_image_le.trans (ih answer)
        _ = B ^ (depth + 1) := by
          simp [Nat.pow_succ, Nat.mul_comm]
#print axioms adaptive_leaf_count_le_pow

/-- Exact identification by a protocol of depth at most `h` injects the state
space into its leaves, and hence into at most `B ^ h` possibilities. -/
theorem exact_identification_card_le_pow
    {Question : Type v} {State : Type u} [Fintype State] {B h : Nat}
    (readout : Question -> State -> Fin B) (hB : 1 ≤ B)
    (exact : ExactAtDepth readout h) :
    Fintype.card State ≤ B ^ h := by
  classical
  rcases exact with ⟨protocol, _usesReadouts, injective⟩
  let leafOf : State -> {leaf // leaf ∈ adaptiveLeaves protocol} := fun state =>
    ⟨adaptiveTranscript protocol state,
      adaptive_transcript_mem_leaves protocol state⟩
  have leafOf_injective : Function.Injective leafOf := by
    intro left right sameLeaf
    apply injective
    exact congrArg Subtype.val sameLeaf
  calc
    Fintype.card State ≤
        Fintype.card {leaf // leaf ∈ adaptiveLeaves protocol} :=
      Fintype.card_le_of_injective leafOf leafOf_injective
    _ = (adaptiveLeaves protocol).card := by simp
    _ ≤ B ^ h := adaptive_leaf_count_le_pow protocol hB
#print axioms exact_identification_card_le_pow

/-- The worst-case exact adaptive depth is at least the upper logarithm to base `B`
of the number of states. The explicit `1 ≤ B` premise is the fixed-branching
reasonableness condition needed by the source's at-most-depth leaf count. -/
theorem worst_case_depth_information_lower_bound
    {Question : Type v} {State : Type u} [Fintype State] {B : Nat}
    (readout : Question -> State -> Fin B) (hB : 1 ≤ B)
    (identifiable : exists depth, ExactAtDepth readout depth) :
    Nat.clog B (Fintype.card State) ≤
      adaptiveIdentificationDepth readout identifiable := by
  classical
  have exact : ExactAtDepth readout
      (adaptiveIdentificationDepth readout identifiable) :=
    Nat.find_spec identifiable
  exact Nat.clog_le_of_le_pow (exact_identification_card_le_pow readout hB exact)
#print axioms worst_case_depth_information_lower_bound

/-- The positive-branching premise is necessary: at `B = 0`, the root leaf
identifies `Unit` under depth budget one, but `1` is not at most `0 ^ 1`. -/
theorem positive_branching_factor_is_necessary :
    let readout : Empty -> Unit -> Fin 0 := fun question => Empty.elim question
    ExactAtDepth readout 1 ∧ ¬Fintype.card Unit ≤ 0 ^ 1 := by
  let readout : Empty -> Unit -> Fin 0 := fun question => Empty.elim question
  refine ⟨?_, by decide⟩
  refine ⟨AdaptiveProtocol.leaf, trivial, ?_⟩
  intro left right _
  exact Subsingleton.elim left right
#print axioms positive_branching_factor_is_necessary

/-- A canonical no-question protocol under any depth budget. -/
def zeroQuestionProtocol (State : Type u) (B depth : Nat) :
    AdaptiveProtocol State B depth := .leaf

/-- Empty and singleton state carriers are exactly identifiable without asking a
question, and their upper logarithms have the mathlib value zero. -/
theorem empty_and_singleton_depth_zero_audit
    {Question : Type v} {B : Nat}
    (emptyReadout : Question -> Empty -> Fin B)
    (singletonReadout : Question -> Unit -> Fin B) :
    ExactAtDepth emptyReadout 0 ∧ ExactAtDepth singletonReadout 0 ∧
      Nat.clog B (Fintype.card Empty) = 0 ∧
      Nat.clog B (Fintype.card Unit) = 0 := by
  refine ⟨?_, ?_, by simp, by simp⟩
  · refine ⟨zeroQuestionProtocol Empty B 0, trivial, ?_⟩
    intro state
    exact Empty.elim state
  · refine ⟨zeroQuestionProtocol Unit B 0, trivial, ?_⟩
    intro left right _
    exact Subsingleton.elim left right
#print axioms empty_and_singleton_depth_zero_audit

/-- With unary branching, exact identification at any depth forces at most one state. -/
theorem unary_exact_identification_card_le_one
    {Question : Type v} {State : Type u} [Fintype State] {depth : Nat}
    (readout : Question -> State -> Fin 1) (exact : ExactAtDepth readout depth) :
    Fintype.card State ≤ 1 := by
  simpa using exact_identification_card_le_pow readout (by decide) exact
#print axioms unary_exact_identification_card_le_one

/-- For binary answers, the general bound specializes to the standard ceiling
binary-logarithm lower bound. -/
theorem binary_exact_identification_depth_lower_bound
    {Question : Type v} {State : Type u} [Fintype State] {depth : Nat}
    (readout : Question -> State -> Fin 2) (exact : ExactAtDepth readout depth) :
    Nat.clog 2 (Fintype.card State) ≤ depth := by
  apply Nat.clog_le_of_le_pow
  exact exact_identification_card_le_pow readout (by decide) exact
#print axioms binary_exact_identification_depth_lower_bound

/-- At depth zero, exact identification forces the state carrier to have at most
one element, without any assumption on the branching factor. -/
theorem zero_depth_exact_identification_card_le_one
    {Question : Type v} {State : Type u} [Fintype State] {B : Nat}
    (readout : Question -> State -> Fin B) (exact : ExactAtDepth readout 0) :
    Fintype.card State ≤ 1 := by
  rcases exact with ⟨protocol, _usesReadouts, injective⟩
  cases protocol with
  | leaf =>
      apply Fintype.card_le_one_iff.mpr
      intro left right
      apply injective
      rfl
#print axioms zero_depth_exact_identification_card_le_one

/-- Compile a fixed-length answer code into an adaptive tree that asks its
coordinates from last to first. Branch continuations may choose later questions,
although this canonical construction uses the same continuation on every branch. -/
def adaptiveProtocol {State : Type u} (B : Nat) :
    (depth : Nat) -> (State -> Fin depth -> Fin B) -> AdaptiveProtocol State B depth
  | 0, _code => .leaf
  | depth + 1, code =>
      .query (fun state => code state (Fin.last depth)) fun _answer =>
        adaptiveProtocol B depth fun state coordinate => code state coordinate.castSucc

private theorem adaptiveTranscript_adaptiveProtocol_eq_iff
    {State : Type u} {B depth : Nat} (code : State -> Fin depth -> Fin B)
    (left right : State) :
    adaptiveTranscript (adaptiveProtocol B depth code) left =
        adaptiveTranscript (adaptiveProtocol B depth code) right ↔
      code left = code right := by
  induction depth with
  | zero =>
      constructor
      · intro _sameTranscript
        funext coordinate
        exact Fin.elim0 coordinate
      · intro _sameCode
        rfl
  | succ depth ih =>
      simp only [adaptiveProtocol, adaptiveTranscript, List.cons.injEq, ih]
      constructor
      · rintro ⟨last_equal, prefix_equal⟩
        funext coordinate
        exact Fin.lastCases last_equal
          (fun earlier => congrFun prefix_equal earlier) coordinate
      · intro code_equal
        exact ⟨congrFun code_equal (Fin.last depth), by
          funext coordinate
          exact congrFun code_equal coordinate.castSucc⟩

private theorem adaptiveProtocol_uses_identity_readout
    {State : Type u} {B depth : Nat} (protocol : AdaptiveProtocol State B depth) :
    UsesReadoutFamily
      (id : (State -> Fin B) -> State -> Fin B) protocol := by
  induction protocol with
  | leaf => trivial
  | query question next ih => exact ⟨⟨question, rfl⟩, ih⟩

private theorem adaptiveTranscript_constant_zero
    {depth : Nat} (protocol : AdaptiveProtocol Bool 2 depth) :
    UsesReadoutFamily (fun _ : Unit => fun _ : Bool => (0 : Fin 2)) protocol →
      adaptiveTranscript protocol false = adaptiveTranscript protocol true := by
  induction protocol with
  | leaf =>
      intro _usesReadouts
      rfl
  | query question next ih =>
      rintro ⟨⟨selected, hquestion⟩, nextUsesReadouts⟩
      have false_answer : question false = 0 := by
        rw [hquestion]
      have true_answer : question true = 0 := by
        rw [hquestion]
      simp only [adaptiveTranscript, false_answer, true_answer, List.cons.injEq, true_and]
      exact ih 0 (nextUsesReadouts 0)

/-- A constant zero readout cannot identify the two Boolean states at any depth. -/
theorem constant_zero_readout_not_exact_on_bool (depth : Nat) :
    ¬ExactAtDepth (fun _ : Unit => fun _ : Bool => (0 : Fin 2)) depth := by
  rintro ⟨protocol, usesReadouts, injective⟩
  exact Bool.false_ne_true
    (injective (adaptiveTranscript_constant_zero protocol usesReadouts))
#print axioms constant_zero_readout_not_exact_on_bool

/-- The full transcript state space realizes equality: it has exactly `B ^ h`
states and the compiled coordinate protocol identifies it in depth `h`. -/
theorem full_transcript_space_attains_leaf_bound (B h : Nat) :
    Fintype.card (Fin h -> Fin B) = B ^ h ∧
      ExactAtDepth
        (id : ((Fin h -> Fin B) -> Fin B) -> (Fin h -> Fin B) -> Fin B) h := by
  constructor
  · simp
  · let protocol := adaptiveProtocol B h (id : (Fin h -> Fin B) -> Fin h -> Fin B)
    refine ⟨protocol, adaptiveProtocol_uses_identity_readout protocol, ?_⟩
    intro left right sameTranscript
    simpa using
      (adaptiveTranscript_adaptiveProtocol_eq_iff
        (id : (Fin h -> Fin B) -> Fin h -> Fin B) left right).mp sameTranscript
#print axioms full_transcript_space_attains_leaf_bound

end D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
