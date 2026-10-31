/- GID: D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact minimal-window classification for complete ordered actual paid records. -/

import D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion
import D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Experiment.KBonacciFixedPaidRecord

open D5.S0.Automata.TypedPartialDFAOOverBase
open KBonacciPrefixCompletion
open scoped BigOperators Matrix

/-- The actual live-tail automaton; rejection is absorbing. -/
def base (k : ℕ) (hk : 2 ≤ k) : PartialDFA Bool (Fin k) :=
  { start := ⟨0, by omega⟩
    step := fun s b => if b then
      if h : s.val + 1 < k then some ⟨s.val + 1,h⟩ else none
      else some ⟨0, by omega⟩ }

/-- Transfer on the actual automaton, without treating a zero reader value as rejection. -/
def live {k : ℕ} (hk : 2 ≤ k) (word : List Bool) : Matrix (Fin k) (Fin k) ℝ :=
  fun i s => if (base k hk).evalFrom s word = some i then 1 else 0

private def endpoint {k : ℕ} (p t : Fin k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i s => if i = t ∧ s.val + p.val < k then 1 else 0

/-- Internal legality of the complete k+1 bit window, starting its test at tail zero. -/
abbrev Window (k : ℕ) (hk : 2 ≤ k) :=
  {word : List Bool // word.length = k+1 ∧ (base k hk).evalFrom (base k hk).start word ≠ none}

/-- Each list starts a fresh preparation and is abandoned after its last window.
Empty lists are paid empty preparations. Both list orders are fixed before reading. -/
abbrev Arrangement (k : ℕ) (hk : 2 ≤ k) := List (List (Window k hk))

/-- Every actual window, including killing and repeated windows, is charged once. -/
def windows {k : ℕ} {hk : 2 ≤ k} (A : Arrangement k hk) : ℕ :=
  (A.map List.length).sum

/-- Sequential physical evolution and its compulsory terminal readings. -/
def terminalReads {k : ℕ} {hk : 2 ≤ k} (ell : Fin k → ℝ) :
    (Fin k → ℝ) → List (Window k hk) → List ℝ
  | _, [] => []
  | x, a :: rest =>
    let y := live hk a.val *ᵥ x
    (ell ⬝ᵥ y) :: terminalReads ell y rest

/-- The arrangement itself retains the literal action history. Each run retains its
paid initial reading and every paid terminal reading, including all zero entries. -/
def paidRecord {k : ℕ} {hk : 2 ≤ k} (A : Arrangement k hk) (w : World k) :=
  (A, A.map (fun run => (initial w, terminalReads w.ell w.c run)))

private def wordPrefixes {k : ℕ} {hk : 2 ≤ k} : List (Window k hk) → List (List Bool)
  | [] => []
  | a :: rest => a.val :: (wordPrefixes rest).map (fun word => a.val ++ word)

private lemma prefix_lengths {k : ℕ} {hk : 2 ≤ k} (run : List (Window k hk)) :
    (wordPrefixes run).length = run.length ∧
    ∀ word ∈ wordPrefixes run, k ≤ word.length := by
  induction run with
  | nil => simp [wordPrefixes]
  | cons a rest ih =>
    constructor
    · simp [wordPrefixes, ih.1]
    · intro word hw
      simp only [wordPrefixes, List.mem_cons, List.mem_map] at hw
      rcases hw with rfl | ⟨v, hv, rfl⟩
      · omega
      · simp only [List.length_append]
        have := ih.2 v hv
        omega

private lemma append_live {k : ℕ} (hk : 2 ≤ k) (u v : List Bool) :
    live hk (u ++ v) = live hk v * live hk u := by
  exact (D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators.actual_endpoint_operators
    (K := ℝ) k hk).2.2.2.2.2.2.2.1 u v

private lemma sequential_readings {k : ℕ} {hk : 2 ≤ k} (ell x : Fin k → ℝ)
    (run : List (Window k hk)) : terminalReads ell x run =
      (wordPrefixes run).map (fun word => ell ⬝ᵥ (live hk word *ᵥ x)) := by
  induction run generalizing x with
  | nil => rfl
  | cons a rest ih =>
    simp only [terminalReads, wordPrefixes, List.map_cons, List.map_map]
    congr 1
    rw [ih]
    apply List.map_congr_left
    intro word _
    rw [append_live, Matrix.mulVec_mulVec]

/-- The label is extracted from the actual word operator, before selecting a world.
Its first coordinate r denotes source prefix length j=r+1. -/
def label {k : ℕ} (hk : 2 ≤ k) (word : List Bool) : Option (Fin k × Fin k) :=
  if h : ∃ q : Fin k × Fin k, live hk word = endpoint q.1 q.2 then
    let q := Classical.choose h
    some (⟨k - 1 - q.1.val, by have := q.1.isLt; omega⟩, q.2)
  else none

private lemma endpoint_action {k : ℕ} (c : Fin k → ℝ) (p t : Fin k) :
    endpoint p t *ᵥ c = fun i =>
      if i = t then cumulative c (k-p.val) else 0 := by
  classical
  funext i
  by_cases hi : i = t
  · subst i
    simp only [Matrix.mulVec, dotProduct, endpoint, true_and, ite_mul, one_mul, zero_mul,
      cumulative]
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    omega
  · simp [Matrix.mulVec, dotProduct, endpoint, hi]

private lemma actual_label {k : ℕ} (hk : 2 ≤ k) (word : List Bool)
    (length : k ≤ word.length) :
    match label hk word with
    | none => live hk word = 0
    | some q => ∀ c : Fin k → ℝ, live hk word *ᵥ c =
        fun i => if i = q.2 then cumulative c (q.1.val+1) else 0 := by
  classical
  have facts := D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators.actual_endpoint_operators
    (K := ℝ) k hk
  by_cases he : ∃ q : Fin k × Fin k, live hk word = endpoint q.1 q.2
  · simp only [label, dif_pos he]
    intro c
    rw [Classical.choose_spec he, endpoint_action]
    congr 1
    funext i
    congr 1
    congr 1
    have := (Classical.choose he).1.isLt
    omega
  · simp only [label, dif_neg he]
    by_cases dead : (base k hk).evalFrom (base k hk).start word = none
    · funext i s
      have all := facts.2.2.2.2.2.1 word dead s
      simp [live, all]
    · have zero := facts.2.2.2.2.2.2.1 word length dead
      obtain ⟨p,t,_,_,_,_,normal⟩ := facts.2.2.2.2.1 word zero dead
      exact (he ⟨(p,t),normal⟩).elim

private lemma reading_label {k : ℕ} (hk : 2 ≤ k) (word : List Bool)
    (length : k ≤ word.length) (w : World k) :
    w.ell ⬝ᵥ (live hk word *ᵥ w.c) =
      match label hk word with
      | none => 0
      | some q => cumulative w.c (q.1.val+1) * w.ell q.2 := by
  have shape := actual_label hk word length
  cases he : label hk word with
  | none => simp only [he] at shape; simp [shape]
  | some q =>
    simp only [he] at shape
    rw [shape]
    simp [dotProduct, mul_ite, mul_comm, he]

/-- Distinct surviving object labels, regardless of whether the reader reports zero. -/
def surviving {k : ℕ} {hk : 2 ≤ k} (A : Arrangement k hk) : Finset (Fin k × Fin k) :=
  ((A.flatMap wordPrefixes).filterMap (label hk)).toFinset

private lemma surviving_budget {k : ℕ} {hk : 2 ≤ k} (A : Arrangement k hk) :
    (surviving A).card ≤ windows A := by
  have first := List.toFinset_card_le ((A.flatMap wordPrefixes).filterMap (label hk))
  have second := List.length_filterMap_le (label hk) (A.flatMap wordPrefixes)
  have count : (A.flatMap wordPrefixes).length = windows A := by
    induction A with
    | nil => rfl
    | cons run rest ih => simp [List.flatMap_cons, windows, (prefix_lengths run).1] at *; omega
  exact first.trans (second.trans count.le)

private lemma record_bridge {k : ℕ} {hk : 2 ≤ k} (A : Arrangement k hk)
    (nonempty : A ≠ []) (w v : World k) :
    paidRecord A w = paidRecord A v ↔ SameData (surviving A) w v := by
  classical
  have perword (run : List (Window k hk)) (word : List Bool) (hw : word ∈ wordPrefixes run) :=
    (prefix_lengths run).2 word hw
  constructor
  · intro he
    have runs := List.map_inj_left.mp (Prod.mk.inj he).2
    obtain ⟨run, hr⟩ := List.exists_mem_of_ne_nil A nonempty
    refine ⟨(Prod.mk.inj (runs run hr)).1, ?_⟩
    intro q hq
    simp only [surviving, List.mem_toFinset, List.mem_filterMap, List.mem_flatMap] at hq
    obtain ⟨word, ⟨run, hr, hw⟩, hlabel⟩ := hq
    have reads := (Prod.mk.inj (runs run hr)).2
    rw [sequential_readings, sequential_readings] at reads
    have value := List.map_inj_left.mp reads word hw
    rw [reading_label hk word (perword run word hw) w,
      reading_label hk word (perword run word hw) v, hlabel] at value
    exact value
  · intro hd
    apply Prod.ext rfl
    apply List.map_congr_left
    intro run hr
    apply Prod.ext hd.1
    rw [sequential_readings, sequential_readings]
    apply List.map_congr_left
    intro word hw
    rw [reading_label hk word (perword run word hw) w,
      reading_label hk word (perword run word hw) v]
    cases hl : label hk word with
    | none => rfl
    | some q =>
      apply hd.2 q
      simp only [surviving, List.mem_toFinset, List.mem_filterMap, List.mem_flatMap]
      exact ⟨word, ⟨run,hr,hw⟩, hl⟩

/-- Complete source 12.2: every legal fixed finite arrangement with exactly k(k-1)
actual windows identifies the initial relation from its full ordered paid record
if and only if its surviving endpoint pattern is exactly the off-diagonal set.
The decoder is an arbitrary function on complete records. -/
theorem complete_source_12_2 (k : ℕ) (hk : 3 ≤ k)
    (A : Arrangement k (by omega)) (budget : windows A = k*(k-1)) :
    (∃ decode : (Arrangement k (by omega) × List (ℝ × List ℝ)) →
        Matrix (Fin k) (Fin k) ℝ,
      ∀ w : World k, decode (paidRecord A w) = target w) ↔
    surviving A = offDiagonal k := by
  classical
  have nonempty : A ≠ [] := by
    intro he
    simp [he, windows] at budget
    omega
  letI : Nonempty (World k) := ⟨{
    c := fun _ => 1, ell := fun _ => 1, c_pos := by intro i; norm_num,
    ell_nonneg := by intro i; norm_num,
    ell_ne_zero := by intro he; have h := congrFun he ⟨0,by omega⟩; norm_num at h }⟩
  have factor := (D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization.universal_sufficiency_factorization
    (paidRecord A) target).2
  have fiber : (∃ decode : (Arrangement k (by omega) × List (ℝ × List ℝ)) →
        Matrix (Fin k) (Fin k) ℝ,
      ∀ w : World k, decode (paidRecord A w) = target w) ↔ Identifies (surviving A) := by
    constructor
    · rintro ⟨decode,correct⟩ w v data
      have he := (record_bridge A nonempty w v).mpr data
      rw [← correct w, ← correct v, he]
    · intro ident
      have constant : ∀ ⦃w v : World k⦄, paidRecord A w = paidRecord A v → target w = target v :=
        fun {w v} he => ident w v ((record_bridge A nonempty w v).mp he)
      obtain ⟨f,hf⟩ := factor.mpr constant
      refine ⟨fun record => (f record).val, ?_⟩
      intro w
      exact (congrArg Subtype.val (congrFun hf w)).symm
  rw [fiber]
  exact endpoint_pattern_classification k hk (surviving A) (by
    simpa [budget] using surviving_budget A)

#print axioms complete_source_12_2

end D5.S3.ConceptDynamics.Experiment.KBonacciFixedPaidRecord
