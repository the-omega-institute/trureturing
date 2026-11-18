/- GID: D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact automata, bounded circuit polynomials and finite-grid support estimates. -/

/-
proof_shape: per-declaration rows below; definitions carry no theorem novelty claim.
escape_witness: gridSupportBound, via reducedGridSupport and its leading-coefficient induction.
admission_basis: escape-witness
Direct frozen dependencies: B = D5/S3/Observer/Separation/BooleanRankThreeK4.bit2; statement_id = sha256:53632b1f9446d59ef22ddbbb7d61d5c3f0f40af1c067d7b9c67e6b47379da9cb.
Each row gives name | proof_shape | frozen dependencies | escape_witness | consumers.
B denotes that exact declaration identity; none denotes no frozen D5 dependency.
Definition rows describe constructions, not additional mathematical content.
exactlyAccepts | bind-only | none | none | realizesStateCount, realizesWordLengthSucc, realizesStateCountMapIff, realizesConstantWord, exactLoopsCommute, loopTripleShort, exactEqualLoopPump, closeEqualLoops, noRepeatsStateBound
realizesStateCount | bind-only | none | none | A_Ne, complexityTotal, realizesWordLengthSucc, minimumAttained, complexityTotalProof, realizesStateCountMapIff, ANeMap, realizesConstantWord, ANeLeOfRealizes, constantWordMemLq, noRepeatsStateBound, lowImpliesRepeat
A_Ne | bind-only | none | none | Lq, complexityTotal, minimumAttained, ANeMap, memLqMapIff, ANeLeOfRealizes, constantWordMemLq, lowImpliesRepeat
Lq | bind-only | none | none | memLqMapIff, claim, constantWordMemLq, lowImpliesRepeat, lowLanguageSparse, claimOfSparse
Circuit | bind-only | none | none | bounded, evalRounds, evaluate, arithmeticRecognizable, booleanRecognizable, polynomialRounds, circuitPolynomial, polynomialRoundsEval, circuitPolynomialEval, polynomialRoundsDegreeLe, circuitPolynomialDegreeLe, sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, booleanPolynomialFamily
bounded | bind-only | none | none | arithmeticRecognizable, booleanRecognizable, polynomialRoundsDegreeLe, circuitPolynomialDegreeLe, sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, booleanPolynomialFamily
evalRounds | bind-only | none | none | evaluate, polynomialRoundsEval
evaluate | bind-only | none | none | arithmeticRecognizable, booleanRecognizable, circuitPolynomialEval, sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, booleanPolynomialFamily
arithmeticRecognizable | bind-only | none | none | sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, claim, claimOfSparse
booleanRecognizable | bind-only | none | none | booleanPolynomialFamily, sparseBooleanNotRecognizable, sparseBooleanComplementNotRecognizable, claim, claimOfSparse
complexityTotal | bind-only | none | none | complexityTotalProof, claim, claimOfSparse
wordChain | bind-only | none | none | wordChainPathDrop, wordChainPathOfDrop, wordChainAcceptsIff, realizesWordLengthSucc
wordChainPathDrop | content | none | wordChainPathDrop | wordChainAcceptsIff
wordChainPathOfDrop | content | none | wordChainPathOfDrop | wordChainAcceptsIff
wordChainAcceptsIff | content | none | wordChainAcceptsIff | realizesWordLengthSucc
realizesWordLengthSucc | content | none | realizesWordLengthSucc | complexityTotalProof, lowImpliesRepeat
minimumAttained | bind-only | none | none | complexityTotalProof, constantWordMemLq, lowImpliesRepeat
complexityTotalProof | content | none | complexityTotalProof | claimOfSparse
pullbackNFA | bind-only | none | none | pullbackNFAEvalFrom, pullbackNFAAccepts, realizesStateCountMapIff
pushforwardNFA | bind-only | none | none | pushforwardNFAPath, pushforwardNFAPathLift, pushforwardNFAAccepts, realizesStateCountMapIff
pullbackNFAEvalFrom | bind-only | none | none | pullbackNFAAccepts
pullbackNFAAccepts | bind-only | none | none | realizesStateCountMapIff
pushforwardNFAPath | bind-only | none | none | pushforwardNFAAccepts
pushforwardNFAPathLift | content | none | pushforwardNFAPathLift | pushforwardNFAAccepts
pushforwardNFAAccepts | content | none | pushforwardNFAAccepts | realizesStateCountMapIff
realizesStateCountMapIff | content | none | realizesStateCountMapIff | ANeMap
ANeMap | content | none | ANeMap | memLqMapIff
memLqMapIff | content | none | memLqMapIff | claimOfSparse
polynomialRounds | bind-only | none | none | circuitPolynomial, polynomialRoundsEval, polynomialRoundsDegreeLe
circuitPolynomial | bind-only | none | none | circuitPolynomialEval, circuitPolynomialDegreeLe, sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, booleanPolynomialFamily
polynomialRoundsEval | content | none | polynomialRoundsEval | circuitPolynomialEval
circuitPolynomialEval | content | none | circuitPolynomialEval | sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, booleanPolynomialFamily
polynomialSumDegreeLe | bind-only | none | none | polynomialRoundsDegreeLe
polynomialProdDegreeLe | bind-only | none | none | polynomialRoundsDegreeLe
polynomialRoundsDegreeLe | content | none | polynomialRoundsDegreeLe | circuitPolynomialDegreeLe
circuitPolynomialDegreeLe | content | none | circuitPolynomialDegreeLe | sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, booleanPolynomialFamily
existsGridReduction | bind-only | none | none | gridSupportBound
gridSupport | bind-only | none | none | gridSupportCardSplit, reducedGridSupport, gridSupportBound, gridSupportImageCard, sparsePolynomialObstruction
nonzeroValuesCard | bind-only | none | none | reducedGridSupport
gridSupportCardSplit | bind-only | none | none | reducedGridSupport
reducedGridSupport | content | none | reducedGridSupport | gridSupportBound
gridSupportBound | content | none | gridSupportBound | sparsePolynomialObstruction
languageCount | bind-only | none | none | sparseNonempty, sparsePolynomialObstruction, lowLanguageSparse
sparseNonempty | bind-only | none | none | sparsePolynomialObstruction, sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, sparseBooleanNotRecognizable, sparseBooleanComplementNotRecognizable, lowLanguageSparse, claimOfSparse
gridSupportImageCard | bind-only | none | none | sparsePolynomialObstruction
sparsePolynomialObstruction | content | none | sparsePolynomialObstruction | sparseArithmeticNotRecognizable, sparseArithmeticComplementNotRecognizable, sparseBooleanNotRecognizable, sparseBooleanComplementNotRecognizable
sparseArithmeticNotRecognizable | content | none | sparseArithmeticNotRecognizable | claimOfSparse
complementTransform | bind-only | none | none | sparseArithmeticComplementNotRecognizable, sparseBooleanComplementNotRecognizable
sparseArithmeticComplementNotRecognizable | content | none | sparseArithmeticComplementNotRecognizable | claimOfSparse
substituteEval | bind-only | none | none | booleanPolynomialFamily
substituteDegreeLe | bind-only | none | none | booleanPolynomialFamily
blockSubstitution | bind-only | B | none | blockSubstitutionDegree, blockSubstitutionEval, booleanPolynomialFamily
blockSubstitutionDegree | bind-only | B | none | booleanPolynomialFamily
blockSubstitutionEval | bind-only | B | none | booleanPolynomialFamily
bit2Injective | bind-only | B | none | sparseBooleanNotRecognizable, sparseBooleanComplementNotRecognizable
booleanPolynomialFamily | content | B | booleanPolynomialFamily | sparseBooleanNotRecognizable, sparseBooleanComplementNotRecognizable
sparseBooleanNotRecognizable | content | B | sparseBooleanNotRecognizable | claimOfSparse
sparseBooleanComplementNotRecognizable | content | B | sparseBooleanComplementNotRecognizable | claimOfSparse
Circuit.nodes | bind-only | none | none | Circuit and its consumers
Circuit.gate | bind-only | none | none | Circuit and its consumers
Circuit.output | bind-only | none | none | Circuit and its consumers
Circuit.level | bind-only | none | none | Circuit and its consumers
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30628
-/

import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! Exact automata and polynomial obstructions for sparse languages. -/

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

/-- Definition 1.1: accept w and reject every other word of its length. -/
def exactlyAccepts {Alphabet : Type} {k : ℕ} (M : NFA Alphabet (Fin k)) (w : List Alphabet) : Prop :=
  w ∈ M.accepts ∧ ∀ y : List Alphabet, y.length = w.length → y ∈ M.accepts → y = w

/-- A k-state epsilon-free NFA with a single initial state exactly accepts w. -/
def realizesStateCount {Alphabet : Type} (w : List Alphabet) (k : ℕ) : Prop :=
  ∃ M : NFA Alphabet (Fin k), ∃ initial : Fin k,
    M.start = {initial} ∧ exactlyAccepts M w

/-- Definition 1.6: the minimum number of states, with infinity for an empty set. -/
noncomputable def A_Ne {Alphabet : Type} (w : List Alphabet) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ k : ℕ, v = (k : ℕ∞) ∧ realizesStateCount w k}

/-- Definition 1.8: the threshold is strict and length counts original symbols. -/
def Lq {Alphabet : Type} (q : ℚ) : Set (List Alphabet) :=
  {w | ∃ k : ℕ, A_Ne w = (k : ℕ∞) ∧ (k : ℚ) < q * (w.length : ℚ)}

/-- A finite circuit graph, with a proposed level labelling for its gates. -/
structure Circuit (R : Type) (I : Type) where
  nodes : ℕ
  gate : Fin nodes → ((I × Bool) ⊕ (R ⊕ (List (Fin nodes) ⊕ List (Fin nodes))))
  output : Fin nodes
  level : Fin nodes → ℕ

/-- Definition 4.4: uniformly bounded depth and multiplication fan-in.
Addition fan-in is finite at each gate but has no uniform upper bound. -/
def bounded {R I : Type} (C : Circuit R I) (h b : ℕ) : Prop :=
  ∀ v : Fin C.nodes, C.level v ≤ h ∧
    match C.gate v with
    | .inl _ => True
    | .inr (.inl _) => True
    | .inr (.inr (.inl inputs)) => ∀ u ∈ inputs, C.level u < C.level v
    | .inr (.inr (.inr inputs)) =>
        inputs.length ≤ b ∧ ∀ u ∈ inputs, C.level u < C.level v

/-- Synchronous evaluation; bounded circuits are acyclic, so nodes+1 rounds suffice. -/
def evalRounds {R I : Type} [CommRing R] (C : Circuit R I) (x : I → R) :
    ℕ → Fin C.nodes → R
  | 0 => fun _ => 0
  | t + 1 => fun v =>
      match C.gate v with
      | .inl (i, negative) => if negative then 1 - x i else x i
      | .inr (.inl a) => a
      | .inr (.inr (.inl inputs)) => (inputs.map (evalRounds C x t)).sum
      | .inr (.inr (.inr inputs)) => (inputs.map (evalRounds C x t)).prod

def evaluate {R I : Type} [CommRing R] (C : Circuit R I) (x : I → R) : R :=
  evalRounds C x (C.nodes + 1) C.output

/-- The paper's arithmetic interpretation, on an embedded alphabet only.
The prime and embedding are fixed for the entire family. -/
def arithmeticRecognizable {Alphabet : Type} (p : ℕ) (e : Alphabet → ZMod p)
    (L : Set (List Alphabet)) : Prop :=
  ∃ h b : ℕ, ∀ n : ℕ, ∃ C : Circuit (ZMod p) (Fin n),
    bounded C h b ∧ ∀ x : Fin n → Alphabet,
      (List.ofFn x ∈ L ↔ evaluate C (fun i => e (x i)) ≠ 0)

/-- Literal Boolean Definition 4.4, with one fixed injective block encoding.
Only valid encoded words are constrained. Over F2, addition is XOR and multiplication AND. -/
def booleanRecognizable {Alphabet : Type} (t : ℕ) (e : Alphabet → Fin t → Bool)
    (L : Set (List Alphabet)) : Prop :=
  ∃ h b : ℕ, ∀ n : ℕ, ∃ C : Circuit (ZMod 2) (Fin n × Fin t),
    bounded C h b ∧ ∀ x : Fin n → Alphabet,
      (List.ofFn x ∈ L ↔
        evaluate C (fun i => if e (x i.1) i.2 then 1 else 0) ≠ 0)

/-- The minimum defining A_Ne exists and is attained; this is a conclusion,
not an existence hypothesis on the universal lower-bound statement. -/
def complexityTotal (Alphabet : Type) : Prop :=
  ∀ w : List Alphabet, ∃ k : ℕ, realizesStateCount w k ∧ A_Ne w = (k : ℕ∞)



end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

private def wordChain {Alphabet : Type} (w : List Alphabet) : NFA Alphabet (Fin (w.length + 1)) where
  step s a := {t | t.val = s.val + 1 ∧ w.drop s.val = a :: w.drop t.val}
  start := {⟨0, Nat.zero_lt_succ _⟩}
  accept := {⟨w.length, Nat.lt_succ_self _⟩}

private theorem wordChainPathDrop {Alphabet : Type} (w y : List Alphabet)
    (s t : Fin (w.length + 1)) (p : (wordChain w).Path s t y) :
    w.drop s.val = y ++ w.drop t.val := by
  induction p with
  | nil s => simp
  | cons u s t a y h p ih =>
    change u.val = s.val + 1 ∧ w.drop s.val = a :: w.drop u.val at h
    rw [h.2, ih, List.cons_append]

private theorem wordChainPathOfDrop {Alphabet : Type} (w y : List Alphabet)
    (s t : Fin (w.length + 1)) (hlen : t.val = s.val + y.length)
    (hdrop : w.drop s.val = y ++ w.drop t.val) :
    Nonempty ((wordChain w).Path s t y) := by
  induction y generalizing s with
  | nil =>
    have hst : s = t := Fin.ext (by simpa using hlen.symm)
    subst t
    exact ⟨.nil s⟩
  | cons a y ih =>
    have hslt : s.val < w.length := by simp only [List.length_cons] at hlen; omega
    let u : Fin (w.length + 1) := ⟨s.val + 1, by omega⟩
    have htail : w.drop u.val = y ++ w.drop t.val := by
      have h := congrArg (List.drop 1) hdrop
      simpa [List.drop_drop, Nat.add_comm, u] using h
    obtain ⟨p⟩ := ih u (by simp only [List.length_cons] at hlen; dsimp [u]; omega) htail
    refine ⟨.cons u s t a y ?_ p⟩
    change u.val = s.val + 1 ∧ w.drop s.val = a :: w.drop u.val
    exact ⟨rfl, by simpa only [List.cons_append, ← htail] using hdrop⟩

private theorem wordChainAcceptsIff {Alphabet : Type} (w y : List Alphabet) :
    y ∈ (wordChain w).accepts ↔ y = w := by
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨s, hs, t, ht, ⟨p⟩⟩
    have hs' : s = ⟨0, Nat.zero_lt_succ _⟩ := hs
    have ht' : t = ⟨w.length, Nat.lt_succ_self _⟩ := ht
    subst s
    subst t
    simpa using (wordChainPathDrop w y _ _ p).symm
  · intro hy
    subst y
    refine ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, ⟨w.length, Nat.lt_succ_self _⟩, rfl, ?_⟩
    apply wordChainPathOfDrop <;> simp

theorem realizesWordLengthSucc {Alphabet : Type} (w : List Alphabet) :
    realizesStateCount w (w.length + 1) := by
  refine ⟨wordChain w, ⟨0, Nat.zero_lt_succ _⟩, rfl, ?_, ?_⟩
  · exact (wordChainAcceptsIff w w).mpr rfl
  · intro y _ hy
    exact (wordChainAcceptsIff w y).mp hy

theorem minimumAttained {Alphabet : Type} (w : List Alphabet)
    (h : ∃ k, realizesStateCount w k) :
    ∃ k, realizesStateCount w k ∧ A_Ne w = (k : ℕ∞) := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, le_antisymm ?_ ?_⟩
  · exact sInf_le ⟨Nat.find h, rfl, Nat.find_spec h⟩
  · apply le_sInf
    rintro v ⟨k, rfl, hk⟩
    exact_mod_cast Nat.find_min' h hk

theorem complexityTotalProof (Alphabet : Type) : complexityTotal Alphabet := by
  intro w
  exact minimumAttained w ⟨w.length + 1, realizesWordLengthSucc w⟩

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

private def pullbackNFA {A B S : Type} (f : A → B) (M : NFA B S) : NFA A S where
  step s a := M.step s (f a)
  start := M.start
  accept := M.accept

private def pushforwardNFA {A B S : Type} (f : A → B) (M : NFA A S) : NFA B S where
  step s b := {t | ∃ a, f a = b ∧ t ∈ M.step s a}
  start := M.start
  accept := M.accept

private theorem pullbackNFAEvalFrom {A B S : Type} (f : A → B) (M : NFA B S)
    (s : Set S) (w : List A) :
    (pullbackNFA f M).evalFrom s w = M.evalFrom s (w.map f) := by
  simp only [NFA.evalFrom, List.foldl_map]
  rfl

private theorem pullbackNFAAccepts {A B S : Type} (f : A → B) (M : NFA B S) (w : List A) :
    w ∈ (pullbackNFA f M).accepts ↔ w.map f ∈ M.accepts := by
  simp only [NFA.mem_accepts, pullbackNFAEvalFrom]
  rfl

private noncomputable def pushforwardNFAPath {A B S : Type} (f : A → B) (M : NFA A S)
    {s t : S} {w : List A} (p : M.Path s t w) :
    (pushforwardNFA f M).Path s t (w.map f) := by
  induction p with
  | nil s => exact .nil s
  | cons u s t a w h p ih => exact .cons u s t (f a) (w.map f) ⟨a, rfl, h⟩ ih

private theorem pushforwardNFAPathLift {A B S : Type} (f : A → B) (M : NFA A S)
    {s t : S} {w : List B} (p : (pushforwardNFA f M).Path s t w) :
    ∃ y : List A, y.map f = w ∧ Nonempty (M.Path s t y) := by
  induction p with
  | nil s => exact ⟨[], rfl, ⟨.nil s⟩⟩
  | cons u s t b w h p ih =>
    obtain ⟨a, ha, hstep⟩ := h
    obtain ⟨y, hy, ⟨q⟩⟩ := ih
    exact ⟨a :: y, by simp [ha, hy], ⟨.cons u s t a y hstep q⟩⟩

private theorem pushforwardNFAAccepts {A B S : Type} (f : A → B) (M : NFA A S) (w : List B) :
    w ∈ (pushforwardNFA f M).accepts ↔ ∃ y, y.map f = w ∧ y ∈ M.accepts := by
  simp only [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨s, hs, t, ht, ⟨p⟩⟩
    obtain ⟨y, hy, hpath⟩ := pushforwardNFAPathLift f M p
    exact ⟨y, hy, s, hs, t, ht, hpath⟩
  · rintro ⟨y, hy, s, hs, t, ht, ⟨p⟩⟩
    subst w
    exact ⟨s, hs, t, ht, ⟨pushforwardNFAPath f M p⟩⟩

private theorem realizesStateCountMapIff {A B : Type} (f : A → B) (hf : Function.Injective f)
    (w : List A) (k : ℕ) : realizesStateCount (w.map f) k ↔ realizesStateCount w k := by
  constructor
  · rintro ⟨M, initial, hi, hw, huniq⟩
    refine ⟨pullbackNFA f M, initial, hi, (pullbackNFAAccepts f M w).mpr hw, ?_⟩
    intro y hlen hy
    apply List.map_injective_iff.mpr hf
    exact huniq (y.map f) (by simpa using hlen) ((pullbackNFAAccepts f M y).mp hy)
  · rintro ⟨M, initial, hi, hw, huniq⟩
    refine ⟨pushforwardNFA f M, initial, hi, ?_, ?_⟩
    · exact (pushforwardNFAAccepts f M (w.map f)).mpr ⟨w, rfl, hw⟩
    · intro y hlen hy
      obtain ⟨z, hz, hacc⟩ := (pushforwardNFAAccepts f M y).mp hy
      have hlenz : z.length = w.length := by
        rw [← hz, List.length_map, List.length_map] at hlen
        exact hlen
      rw [huniq z hlenz hacc] at hz
      exact hz.symm

private theorem ANeMap {A B : Type} (f : A → B) (hf : Function.Injective f) (w : List A) :
    A_Ne (w.map f) = A_Ne w := by
  unfold A_Ne
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, realizesStateCountMapIff f hf]

theorem memLqMapIff {A B : Type} (f : A → B) (hf : Function.Injective f)
    (q : ℚ) (w : List A) : w.map f ∈ Lq q ↔ w ∈ Lq q := by
  simp only [Lq, Set.mem_ofPred_eq, ANeMap f hf, List.length_map]

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial

private noncomputable def polynomialRounds {R I : Type} [CommRing R]
    (C : Circuit R I) : ℕ → Fin C.nodes → MvPolynomial I R
  | 0 => fun _ => 0
  | t + 1 => fun v =>
    match C.gate v with
    | .inl (i, negative) => if negative then 1 - X i else X i
    | .inr (.inl a) => MvPolynomial.C a
    | .inr (.inr (.inl inputs)) => (inputs.map (polynomialRounds C t)).sum
    | .inr (.inr (.inr inputs)) => (inputs.map (polynomialRounds C t)).prod

private noncomputable def circuitPolynomial {R I : Type} [CommRing R]
    (C : Circuit R I) : MvPolynomial I R :=
  polynomialRounds C (C.nodes + 1) C.output

private theorem polynomialRoundsEval {R I : Type} [CommRing R]
    (C : Circuit R I) (x : I → R) (t : ℕ) (v : Fin C.nodes) :
    MvPolynomial.eval x (polynomialRounds C t v) = evalRounds C x t v := by
  induction t generalizing v with
  | zero => simp [polynomialRounds, evalRounds]
  | succ t ih =>
    simp only [polynomialRounds, evalRounds]
    rcases hg : C.gate v with ⟨i, negative⟩ | (a | (inputs | inputs))
    · cases negative <;> simp
    · simp
    · simp only [map_list_sum, List.map_map]
      congr 1
      exact List.map_congr_left (fun u _ => ih u)
    · simp only [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left (fun u _ => ih u)

private theorem circuitPolynomialEval {R I : Type} [CommRing R]
    (C : Circuit R I) (x : I → R) :
    MvPolynomial.eval x (circuitPolynomial C) = evaluate C x := by
  exact polynomialRoundsEval C x (C.nodes + 1) C.output

private theorem polynomialSumDegreeLe {R I : Type} [CommRing R]
    (l : List (MvPolynomial I R)) (d : ℕ) (hd : ∀ p ∈ l, p.totalDegree ≤ d) :
    l.sum.totalDegree ≤ d := by
  have h : (∑ i : Fin l.length, l[i.val]).totalDegree ≤ d :=
    MvPolynomial.totalDegree_finsetSum_le (fun i _ => hd l[i.val] (List.getElem_mem _))
  rw [← List.sum_ofFn, List.ofFn_getElem] at h
  exact h

private theorem polynomialProdDegreeLe {R I : Type} [CommRing R]
    (l : List (MvPolynomial I R)) (d : ℕ) (hd : ∀ p ∈ l, p.totalDegree ≤ d) :
    l.prod.totalDegree ≤ l.length * d := by
  apply (MvPolynomial.totalDegree_list_prod l).trans
  have hsum := List.sum_le_length_nsmul (l.map MvPolynomial.totalDegree) d (by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact hd p hp)
  simpa using hsum

private theorem polynomialRoundsDegreeLe {R I : Type} [CommRing R] [Nontrivial R]
    (C : Circuit R I) (h b : ℕ) (hb : bounded C h b) (l t : ℕ)
    (v : Fin C.nodes) (hv : C.level v ≤ l) :
    (polynomialRounds C t v).totalDegree ≤ max 1 b ^ l := by
  have hB : 1 ≤ max 1 b := le_max_left _ _
  induction l generalizing t v with
  | zero =>
    cases t with
    | zero => simp [polynomialRounds]
    | succ t =>
      have hz : C.level v = 0 := by exact Nat.eq_zero_of_le_zero hv
      have hgate := (hb v).2
      simp only [polynomialRounds, pow_zero]
      rcases hg : C.gate v with ⟨i, negative⟩ | (a | (inputs | inputs))
      · cases negative
        · simp
        · exact (totalDegree_sub 1 (X i)).trans (by simp)
      · simp
      · have hempty : inputs = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro u hu
          simp only [hg] at hgate
          have := hgate u hu
          omega
        simp [hempty]
      · have hempty : inputs = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro u hu
          simp only [hg] at hgate
          have := hgate.2 u hu
          omega
        simp [hempty]
  | succ l ih =>
    cases t with
    | zero => simp [polynomialRounds]
    | succ t =>
      have hgate := (hb v).2
      simp only [polynomialRounds]
      rcases hg : C.gate v with ⟨i, negative⟩ | (a | (inputs | inputs))
      · have hone : 1 ≤ max 1 b ^ (l + 1) := one_le_pow₀ hB
        cases negative
        · exact (by simpa using hone)
        · exact ((totalDegree_sub 1 (X i)).trans (by simp)).trans hone
      · simp
      · simp only [hg] at hgate
        apply polynomialSumDegreeLe
        intro p hp
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
        have hlt : C.level u < C.level v := hgate u hu
        exact (ih t u (by omega)).trans (Nat.pow_le_pow_right hB (Nat.le_succ l))
      · have hinputs : inputs.length ≤ b ∧ ∀ u ∈ inputs, C.level u < C.level v := by
          simpa only [hg] using hgate
        calc
          _ ≤ (inputs.map (polynomialRounds C t)).length * max 1 b ^ l := by
            apply polynomialProdDegreeLe
            intro p hp
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
            exact ih t u (by have := hinputs.2 u hu; omega)
          _ = inputs.length * max 1 b ^ l := by rw [List.length_map]
          _ ≤ max 1 b * max 1 b ^ l := Nat.mul_le_mul_right _ (hinputs.1.trans (le_max_right _ _))
          _ = max 1 b ^ (l + 1) := by rw [pow_succ, Nat.mul_comm]

private theorem circuitPolynomialDegreeLe {R I : Type} [CommRing R] [Nontrivial R]
    (C : Circuit R I) (h b : ℕ) (hb : bounded C h b) :
    (circuitPolynomial C).totalDegree ≤ max 1 b ^ h := by
  exact polynomialRoundsDegreeLe C h b hb h (C.nodes + 1) C.output (hb C.output).1
end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial MonomialOrder Finsupp
open scoped Finset

/-- Grid reduction preserves every grid evaluation and does not increase total degree. -/
private theorem existsGridReduction {K : Type} [Field K] {n : ℕ}
    (S : Finset K) (hS : S.Nonempty) (P : MvPolynomial (Fin n) K) :
    ∃ R : MvPolynomial (Fin n) K,
      R.totalDegree ≤ P.totalDegree ∧ (∀ i, R.degreeOf i < S.card) ∧
      ∀ x : Fin n → K, (∀ i, x i ∈ S) → MvPolynomial.eval x R = MvPolynomial.eval x P := by
  classical
  let g : Fin n → MvPolynomial (Fin n) K := fun i => ∏ s ∈ S, (X i - C s)
  have hm (i : Fin n) : degLex.Monic (g i) :=
    MonomialOrder.Monic.prod (fun s _ => degLex.monic_X_sub_C i s)
  have hg (i : Fin n) : degLex.degree (g i) = Finsupp.single i S.card := by
    dsimp [g]
    rw [MonomialOrder.degree_prod_of_regular]
    · simp [degLex.degree_X_sub_C]
    · intro s _
      rw [(degLex.monic_X_sub_C i s).leadingCoeff_eq_one]
      exact isRegular_one
  obtain ⟨a, R, hPR, ha, hR⟩ := degLex.div (fun i => by rw [(hm i).leadingCoeff_eq_one]; exact isUnit_one) P
  have hsum : (Finsupp.linearCombination (MvPolynomial (Fin n) K) g a).totalDegree ≤ P.totalDegree := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    change (a i * g i).totalDegree ≤ P.totalDegree
    rw [mul_comm]
    exact degLex_totalDegree_monotone (ha i)
  refine ⟨R, ?_, ?_, ?_⟩
  · have heq : R = P - Finsupp.linearCombination (MvPolynomial (Fin n) K) g a := by
      rw [hPR]; simp
    rw [heq]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le le_rfl hsum)
  · intro i
    rw [MvPolynomial.degreeOf_eq_sup, Finset.sup_lt_iff (Finset.card_pos.mpr hS)]
    intro c hc
    have hnot := hR c hc i
    rw [hg] at hnot
    by_contra! hci
    apply hnot
    intro j
    by_cases hij : i = j
    · subst j; simpa using hci
    · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
  · intro x hx
    have hz : MvPolynomial.eval x (Finsupp.linearCombination (MvPolynomial (Fin n) K) g a) = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [smul_eq_mul, map_mul]
      have hgi : MvPolynomial.eval x (g i) = 0 := by
        dsimp [g]
        rw [map_prod]
        apply Finset.prod_eq_zero (hx i)
        simp
      rw [hgi, mul_zero]
    rw [hPR, map_add, hz, zero_add]

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial
open scoped Finset

private noncomputable def gridSupport {K : Type} [CommRing K] [DecidableEq K] {n : ℕ}
    (S : Finset K) (P : MvPolynomial (Fin n) K) : Finset (Fin n → K) :=
  (Fintype.piFinset (fun _ => S)).filter (fun x => MvPolynomial.eval x P ≠ 0)

private theorem nonzeroValuesCard {K : Type} [Field K] [DecidableEq K]
    (S : Finset K) (P : Polynomial K) (hP : P ≠ 0) :
    S.card - P.natDegree ≤ (S.filter (fun x => P.eval x ≠ 0)).card := by
  have hz : (S.filter (fun x => P.eval x = 0)).card ≤ P.natDegree := by
    calc
      _ ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr (Finset.mem_filter.mp hx).2)
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' _
  have hs := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => P.eval x = 0)
  simp only [ne_eq] at ⊢
  omega

private theorem gridSupportCardSplit {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (S : Finset K) (P : MvPolynomial (Fin (n + 1)) K) :
    (gridSupport S P).card = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => S),
      (S.filter (fun a => MvPolynomial.eval (Fin.cons a x) P ≠ 0)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Fin.tail)
    (t := Fintype.piFinset (fun _ : Fin n => S))]
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.card_bij (fun y _ => y 0)
    · intro y hy
      simp only [Finset.mem_filter, gridSupport, Fintype.mem_piFinset] at hy
      simp only [Finset.mem_filter]
      refine ⟨hy.1.1 0, ?_⟩
      have heq : Fin.cons (y 0) x = y := by rw [← hy.2]; exact Fin.cons_self_tail y
      simpa only [heq] using hy.1.2
    · intro a ha b hb hab
      have hatail := (Finset.mem_filter.mp ha).2
      have hbtail := (Finset.mem_filter.mp hb).2
      rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, hatail, hbtail, hab]
    · intro a ha
      refine ⟨Fin.cons a x, ?_, by simp⟩
      simp only [Finset.mem_filter, gridSupport, Fintype.mem_piFinset]
      refine ⟨⟨?_, (Finset.mem_filter.mp ha).2⟩, by simp⟩
      intro i
      refine Fin.cases (Finset.mem_filter.mp ha).1 (fun j => ?_) i
      exact (Fintype.mem_piFinset.mp hx) j
  · intro x hx
    exact Fintype.mem_piFinset.mpr (fun j => (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) j.succ)

private theorem reducedGridSupport {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (S : Finset K) (hS : 2 ≤ S.card) (P : MvPolynomial (Fin n) K) (hP : P ≠ 0)
    (hred : ∀ i, P.degreeOf i < S.card) :
    S.card ^ n ≤ (gridSupport S P).card * S.card ^ P.totalDegree := by
  induction n with
  | zero =>
    have heval (x : Fin 0 → K) : MvPolynomial.eval x P ≠ 0 := by
      rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eval_C]
      intro h
      apply hP
      rw [MvPolynomial.eq_C_of_isEmpty P, h, MvPolynomial.C_0]
    have hcard : (gridSupport S P).card = 1 := by
      simp [gridSupport, heval]
    rw [pow_zero, hcard, one_mul]
    exact Nat.one_le_pow _ _ (by omega)
  | succ n ih =>
    let Q := MvPolynomial.finSuccEquiv K n P
    let k := Q.natDegree
    let A : MvPolynomial (Fin n) K := Q.leadingCoeff
    have hQ : Q ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hP
    have hA : A ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have hdegA : A.totalDegree + k ≤ P.totalDegree :=
      MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P k hA
    have hk : k < S.card := by
      simpa [k, Q, MvPolynomial.natDegree_finSuccEquiv] using hred 0
    have hredA : ∀ i, A.degreeOf i < S.card := by
      intro i
      exact (MvPolynomial.degreeOf_coeff_finSuccEquiv P i k).trans_lt (hred i.succ)
    have htail := ih A hA hredA
    have hcount : (gridSupport S A).card * (S.card - k) ≤ (gridSupport S P).card := by
      rw [gridSupportCardSplit]
      calc
        _ = ∑ _x ∈ gridSupport S A, (S.card - k) := by simp
        _ ≤ ∑ x ∈ gridSupport S A,
          (S.filter (fun a => MvPolynomial.eval (Fin.cons a x) P ≠ 0)).card := by
          apply Finset.sum_le_sum
          intro x hx
          have hAx : MvPolynomial.eval x A ≠ 0 := (Finset.mem_filter.mp hx).2
          let Qx := Q.map (MvPolynomial.eval x)
          have hQxdeg : Qx.natDegree = k :=
            Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hAx
          have hQx : Qx ≠ 0 := by
            apply Polynomial.leadingCoeff_ne_zero.mp
            rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hAx]
            exact hAx
          have hb := nonzeroValuesCard S Qx hQx
          rw [hQxdeg] at hb
          have heval (a : K) : Qx.eval a = MvPolynomial.eval (Fin.cons a x) P :=
            (MvPolynomial.eval_eq_eval_mv_eval' x a P).symm
          simpa only [heval] using hb
        _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin n => S),
          (S.filter (fun a => MvPolynomial.eval (Fin.cons a x) P ≠ 0)).card := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
    have hfactor : S.card ≤ (S.card - k) * S.card ^ k := by
      by_cases hkzero : k = 0
      · simp [hkzero]
      · calc
          S.card ≤ S.card ^ k := by
            simpa using Nat.pow_le_pow_right (by omega : 1 ≤ S.card) (Nat.one_le_iff_ne_zero.mpr hkzero)
          _ ≤ (S.card - k) * S.card ^ k := by
            exact Nat.le_mul_of_pos_left _ (by omega)
    calc
      S.card ^ (n + 1) = S.card ^ n * S.card := pow_succ _ _
      _ ≤ ((gridSupport S A).card * S.card ^ A.totalDegree) *
          ((S.card - k) * S.card ^ k) := Nat.mul_le_mul htail hfactor
      _ = ((gridSupport S A).card * (S.card - k)) * S.card ^ (A.totalDegree + k) := by
        rw [pow_add]; ac_rfl
      _ ≤ (gridSupport S P).card * S.card ^ P.totalDegree :=
        Nat.mul_le_mul hcount (Nat.pow_le_pow_right (by omega) hdegA)

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial

private theorem gridSupportBound {K : Type} [Field K] [DecidableEq K] {n D : ℕ}
    (S : Finset K) (hS : 2 ≤ S.card) (P : MvPolynomial (Fin n) K)
    (hdeg : P.totalDegree ≤ D)
    (hne : ∃ x : Fin n → K, (∀ i, x i ∈ S) ∧ MvPolynomial.eval x P ≠ 0) :
    S.card ^ n ≤ (gridSupport S P).card * S.card ^ D := by
  classical
  obtain ⟨R, hRdeg, hRred, hReval⟩ := existsGridReduction S (Finset.card_pos.mp (by omega)) P
  have hR : R ≠ 0 := by
    intro hzero
    obtain ⟨x, hx, hPx⟩ := hne
    apply hPx
    rw [← hReval x hx, hzero, map_zero]
  have hcard : gridSupport S R = gridSupport S P := by
    ext x
    simp only [gridSupport, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hx, hRx⟩
      exact ⟨hx, by rwa [← hReval x hx]⟩
    · rintro ⟨hx, hPx⟩
      exact ⟨hx, by rwa [hReval x hx]⟩
  calc
    _ ≤ (gridSupport S R).card * S.card ^ R.totalDegree := reducedGridSupport S hS R hR hRred
    _ ≤ (gridSupport S P).card * S.card ^ D := by
      rw [hcard]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (hRdeg.trans hdeg))

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial

noncomputable def languageCount {A : Type} [Fintype A] (L : Set (List A)) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Fin n → A => List.ofFn x ∈ L)).card

def sparseNonempty {A : Type} [Fintype A] (L : Set (List A)) : Prop :=
  ∀ D : ℕ, ∃ n : ℕ, (∃ x : Fin n → A, List.ofFn x ∈ L) ∧
    languageCount L n * Fintype.card A ^ D < Fintype.card A ^ n

private theorem gridSupportImageCard {A K : Type} [Fintype A] [Field K] [DecidableEq K]
    (e : A → K) (he : Function.Injective e) {n : ℕ} (P : MvPolynomial (Fin n) K) :
    (gridSupport (Finset.univ.image e) P).card =
      (Finset.univ.filter (fun x : Fin n → A => MvPolynomial.eval (e ∘ x) P ≠ 0)).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => e ∘ x)
  · intro x hx
    simp only [gridSupport, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => Finset.mem_image.mpr ⟨x i, Finset.mem_univ _, rfl⟩, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    funext i
    exact he (congrFun hxy i)
  · intro y hy
    have hgrid := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hy).1
    have hpre : ∀ i, ∃ a : A, e a = y i := by
      intro i
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hgrid i)
      exact ⟨a, ha⟩
    choose x hx using hpre
    have heq : e ∘ x = y := funext hx
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    rw [heq]
    exact (Finset.mem_filter.mp hy).2

private theorem sparsePolynomialObstruction {A K : Type} [Fintype A] [Field K] [DecidableEq K]
    (e : A → K) (he : Function.Injective e) (hA : 2 ≤ Fintype.card A)
    (L : Set (List A)) (hsparse : sparseNonempty L) (D : ℕ)
    (family : ∀ n : ℕ, ∃ P : MvPolynomial (Fin n) K,
      P.totalDegree ≤ D ∧ ∀ x : Fin n → A,
        (List.ofFn x ∈ L ↔ MvPolynomial.eval (e ∘ x) P ≠ 0)) : False := by
  classical
  obtain ⟨n, ⟨x, hx⟩, hsmall⟩ := hsparse D
  obtain ⟨P, hPdeg, hPL⟩ := family n
  let S : Finset K := Finset.univ.image e
  have hScard : S.card = Fintype.card A := by
    simpa only [S, Finset.card_univ] using Finset.card_image_of_injective Finset.univ he
  have hsupp := gridSupportBound S (by rw [hScard]; exact hA) P hPdeg
    ⟨e ∘ x, (fun i => Finset.mem_image.mpr ⟨x i, Finset.mem_univ _, rfl⟩), (hPL x).mp hx⟩
  have hcount : (gridSupport S P).card = languageCount L n := by
    rw [gridSupportImageCard e he]
    unfold languageCount
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hPL y]
  rw [hcount, hScard] at hsupp
  omega

theorem sparseArithmeticNotRecognizable {A : Type} [Fintype A]
    (hA : 2 ≤ Fintype.card A) (L : Set (List A)) (hsparse : sparseNonempty L)
    (p : ℕ) (hp : p.Prime) (e : A → ZMod p) (he : Function.Injective e) :
    ¬ arithmeticRecognizable p e L := by
  intro hrec
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, b, hrec⟩ := hrec
  apply sparsePolynomialObstruction e he hA L hsparse (max 1 b ^ h)
  intro n
  obtain ⟨C, hC, hCL⟩ := hrec n
  refine ⟨circuitPolynomial C, circuitPolynomialDegreeLe C h b hC, ?_⟩
  intro x
  simpa only [circuitPolynomialEval, Function.comp_def] using hCL x

private theorem complementTransform {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    1 - x ^ (p - 1) ≠ 0 ↔ x = 0 := by
  rw [ZMod.pow_card_sub_one]
  by_cases hx : x = 0 <;> simp [hx]

theorem sparseArithmeticComplementNotRecognizable {A : Type} [Fintype A]
    (hA : 2 ≤ Fintype.card A) (L : Set (List A)) (hsparse : sparseNonempty L)
    (p : ℕ) (hp : p.Prime) (e : A → ZMod p) (he : Function.Injective e) :
    ¬ arithmeticRecognizable p e Lᶜ := by
  intro hrec
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, b, hrec⟩ := hrec
  apply sparsePolynomialObstruction e he hA L hsparse ((p - 1) * max 1 b ^ h)
  intro n
  obtain ⟨C, hC, hCL⟩ := hrec n
  refine ⟨1 - circuitPolynomial C ^ (p - 1), ?_, ?_⟩
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    simp only [MvPolynomial.totalDegree_one, zero_le, max_eq_right]
    exact (MvPolynomial.totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left _ (circuitPolynomialDegreeLe C h b hC))
  · intro x
    rw [map_sub, map_one, map_pow, circuitPolynomialEval, complementTransform]
    have hc := hCL x
    simpa only [Set.mem_compl_iff, not_iff_comm, not_not, Function.comp_def] using hc.not

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial

private theorem substituteEval {R I J : Type} [CommRing R]
    (f : I → MvPolynomial J R) (P : MvPolynomial I R) (x : J → R) :
    MvPolynomial.eval x ((MvPolynomial.eval₂Hom MvPolynomial.C) f P) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (f i)) P :=
  (MvPolynomial.eval_assoc f x P).symm

private theorem substituteDegreeLe {R I J : Type} [CommRing R]
    (f : I → MvPolynomial J R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial I R) : ((MvPolynomial.eval₂Hom MvPolynomial.C) f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hf i))
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

private noncomputable def blockSubstitution {A : Type} {n t : ℕ}
    (labels : Bool → A) (e : A → Fin t → Bool) : (Fin n × Fin t) → MvPolynomial (Fin n) (ZMod 2) :=
  fun ij => AffineMap.lineMap (k := MvPolynomial (Fin n) (ZMod 2))
    (MvPolynomial.C (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 (e (labels false) ij.2)))
    (MvPolynomial.C (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 (e (labels true) ij.2)))
    (X ij.1)

private theorem blockSubstitutionDegree {A : Type} {n t : ℕ}
    (labels : Bool → A) (e : A → Fin t → Bool) (ij : Fin n × Fin t) :
    (blockSubstitution labels e ij).totalDegree ≤ 1 := by
  rw [blockSubstitution, AffineMap.lineMap_apply_ring', ← map_sub]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; decide)
  · simp

private theorem blockSubstitutionEval {A : Type} {n t : ℕ}
    (labels : Bool → A) (e : A → Fin t → Bool) (x : Fin n → Bool) (ij : Fin n × Fin t) :
    MvPolynomial.eval (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 ∘ x) (blockSubstitution labels e ij) =
      D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 (e (labels (x ij.1)) ij.2) := by
  simp only [blockSubstitution, AffineMap.lineMap_apply_ring', ← map_sub, map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Function.comp_apply]
  cases h : x ij.1 <;> simp [D5.S3.Observer.Separation.BooleanRankThreeK4.bit2]

private theorem bit2Injective : Function.Injective D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 := by
  exact Bool.injective_iff.mpr (by simp [D5.S3.Observer.Separation.BooleanRankThreeK4.bit2])

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
open MvPolynomial

private theorem booleanPolynomialFamily {A : Type} {t : ℕ} (e : A → Fin t → Bool)
    (L : Set (List A)) (labels : Bool → A) (hrec : booleanRecognizable t e L) :
    ∃ D : ℕ, ∀ n : ℕ, ∃ P : MvPolynomial (Fin n) (ZMod 2), P.totalDegree ≤ D ∧
      ∀ x : Fin n → Bool, (List.ofFn x).map labels ∈ L ↔
        MvPolynomial.eval (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 ∘ x) P ≠ 0 := by
  obtain ⟨h, b, hrec⟩ := hrec
  refine ⟨max 1 b ^ h, ?_⟩
  intro n
  obtain ⟨C, hC, hCL⟩ := hrec n
  refine ⟨(MvPolynomial.eval₂Hom MvPolynomial.C) (blockSubstitution labels e) (circuitPolynomial C), ?_, ?_⟩
  · exact (substituteDegreeLe _ (blockSubstitutionDegree labels e) _).trans
      (circuitPolynomialDegreeLe C h b hC)
  · intro x
    simp only [substituteEval, blockSubstitutionEval, circuitPolynomialEval]
    simpa only [List.map_ofFn, Function.comp_def, D5.S3.Observer.Separation.BooleanRankThreeK4.bit2] using hCL (labels ∘ x)

theorem sparseBooleanNotRecognizable {A : Type} {t : ℕ} (e : A → Fin t → Bool)
    (L : Set (List A)) (labels : Bool → A)
    (hsparse : sparseNonempty {w : List Bool | w.map labels ∈ L}) :
    ¬ booleanRecognizable t e L := by
  intro hrec
  obtain ⟨D, hD⟩ := booleanPolynomialFamily e L labels hrec
  exact sparsePolynomialObstruction D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 bit2Injective (by simp)
    {w : List Bool | w.map labels ∈ L} hsparse D hD

theorem sparseBooleanComplementNotRecognizable {A : Type} {t : ℕ}
    (e : A → Fin t → Bool) (L : Set (List A)) (labels : Bool → A)
    (hsparse : sparseNonempty {w : List Bool | w.map labels ∈ L}) :
    ¬ booleanRecognizable t e Lᶜ := by
  intro hrec
  obtain ⟨D, hD⟩ := booleanPolynomialFamily e Lᶜ labels hrec
  apply sparsePolynomialObstruction D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 bit2Injective (by simp)
    {w : List Bool | w.map labels ∈ L} hsparse D
  intro n
  obtain ⟨P, hPdeg, hPL⟩ := hD n
  refine ⟨1 - P, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simpa using hPdeg)
  · intro x
    simp only [map_sub, map_one]
    have ht : 1 - MvPolynomial.eval (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 ∘ x) P ≠ 0 ↔
        MvPolynomial.eval (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 ∘ x) P = 0 := by
      simpa using complementTransform (p := 2) (MvPolynomial.eval (D5.S3.Observer.Separation.BooleanRankThreeK4.bit2 ∘ x) P)
    rw [ht]
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using (hPL x).not

end D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure
