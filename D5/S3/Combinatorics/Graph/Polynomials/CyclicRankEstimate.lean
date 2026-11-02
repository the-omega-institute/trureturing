/-! GID: D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff,
     mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: The signed rank-state coefficient splits into forest and cyclic states,
     and graph ranks control the support and the individual coefficient growth.
-/

import D5.S3.Combinatorics.Graph.Jacobi.LeafPruningRanks
import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate

open scoped BigOperators Polynomial Classical

/-! The exponent is defined from the actual integer rank/nullity expression and
    is converted to `Nat` only under an explicit nonnegativity proof. -/

def stateExponentInteger (v : ℕ) (q : ℕ) (s : ℕ) : ℤ :=
  (v : ℤ) - 1 + (s : ℤ) - 2 * (q : ℤ)

def stateExponent (v : ℕ) (q : ℕ) (s : ℕ)
    (h : 0 ≤ stateExponentInteger v q s) : ℕ :=
  (stateExponentInteger v q s).toNat

theorem stateExponent_cast_eq_integer {v q s : ℕ}
    (h : 0 ≤ stateExponentInteger v q s) :
    (stateExponent v q s h : ℤ) = stateExponentInteger v q s := by
  unfold stateExponent
  exact Int.toNat_of_nonneg h

def stateTerm {E : Type*} [DecidableEq E]
    (v : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (S : Finset E) : ℤ[X] :=
  Polynomial.C ((-1 : ℤ) ^ S.card) * Polynomial.X ^ q S *
    (1 + Polynomial.X) ^ stateExponent v (q S) S.card (hExp S)

def statePolynomial {E : Type*} [Fintype E] [DecidableEq E]
    (v : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) : ℤ[X] :=
  ∑ S : Finset E, stateTerm v q hExp S

def forestStates {E : Type*} [Fintype E] [DecidableEq E]
    (q : Finset E → ℕ) : Finset (Finset E) :=
  Finset.univ.filter (fun S => q S = S.card)

def cyclicStates {E : Type*} [Fintype E] [DecidableEq E]
    (q : Finset E → ℕ) : Finset (Finset E) :=
  Finset.univ.filter (fun S => q S < S.card)

def termCoefficient {E : Type*} [DecidableEq E]
    (v k : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (S : Finset E) : ℤ :=
  if q S ≤ k then
    (-1 : ℤ) ^ S.card *
      (stateExponent v (q S) S.card (hExp S)).choose (k - q S)
  else 0

def idealCoefficient (b k : ℕ) : ℤ :=
  Ring.choose (-(b : ℤ)) k

theorem idealCoefficient_formula (b k : ℕ) :
    idealCoefficient b k = (-1 : ℤ) ^ k * (b + k - 1).choose k := by
  by_cases hzero : b = 0 ∧ k = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [idealCoefficient]
  · unfold idealCoefficient
    rw [Ring.choose_neg]
    have h : 1 ≤ b + k := by
      by_contra hnot
      have : b + k = 0 := by omega
      have hb : b = 0 := by omega
      have hk : k = 0 := by omega
      exact hzero ⟨hb, hk⟩
    rw [show (↑b + ↑k - 1 : ℤ) = ((b + k - 1 : ℕ) : ℤ) by
      norm_num [Nat.cast_sub h]]
    rw [Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.coe_negOnePow_natCast,
      Int.cast_natCast]

theorem coeff_stateTerm {E : Type*} [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ}
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (S : Finset E) :
    (stateTerm v q hExp S).coeff k = termCoefficient v k q hExp S := by
  unfold stateTerm termCoefficient
  by_cases hq : q S ≤ k
  · simp only [hq, ↓reduceIte]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    rw [Polynomial.coeff_one_add_X_pow]
    simp [hq]
  · simp only [hq, ↓reduceIte]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp [hq]

theorem coeff_statePolynomial {E : Type*} [Fintype E] [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ}
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) :
    (statePolynomial v q hExp).coeff k =
      ∑ S : Finset E, termCoefficient v k q hExp S := by
  unfold statePolynomial
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_stateTerm hExp]

def forestCoefficient {E : Type*} [Fintype E] [DecidableEq E]
    (v k : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) : ℤ :=
  Finset.sum (forestStates q) (fun S => termCoefficient v k q hExp S)

def cyclicCoefficient {E : Type*} [Fintype E] [DecidableEq E]
    (v k : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) : ℤ :=
  Finset.sum (cyclicStates q) (fun S => termCoefficient v k q hExp S)

theorem coeff_split {E : Type*} [Fintype E] [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ}
    (hRank : ∀ S : Finset E, q S ≤ S.card)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) :
    (statePolynomial v q hExp).coeff k =
      forestCoefficient v k q hExp + cyclicCoefficient v k q hExp := by
  rw [coeff_statePolynomial hExp]
  unfold forestCoefficient cyclicCoefficient forestStates cyclicStates
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset E))
    (fun S => q S = S.card)]
  have hcyc : Finset.filter (fun S : Finset E => ¬ q S = S.card) Finset.univ =
      cyclicStates q := by
    ext S
    simp only [cyclicStates, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hn
      exact (Nat.lt_or_eq_of_le (hRank S)).resolve_right hn
    · intro hlt heq
      omega
  rw [hcyc]
  congr 1

/-! The state graph retains all vertices, including isolated vertices. -/

def graphEdgePredicate {n : ℕ} (G : SimpleGraph (Fin n)) :
    Sym2 (Fin n) → Prop :=
  Sym2.lift ⟨fun u v => G.Adj u v, fun u v => propext (G.adj_comm u v)⟩

abbrev graphEdge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {e : Sym2 (Fin n) // graphEdgePredicate G e}

noncomputable def graphOfState {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) : SimpleGraph (Fin n) := by
  classical
  exact SimpleGraph.fromEdgeSet (S.image (fun e => e.1) : Set (Sym2 (Fin n)))

noncomputable def graphRank {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) : ℕ :=
  n - Nat.card (graphOfState G S).ConnectedComponent

private theorem graph_edge_mem {n : ℕ} (G : SimpleGraph (Fin n)) (e : graphEdge G) :
    e.val ∈ G.edgeSet := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf a b => exact he

private theorem state_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) :
    (graphOfState G S).edgeFinset = S.image (fun e => e.val) := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  rw [graphOfState, SimpleGraph.edgeSet_fromEdgeSet]
  change (e ∈ S.image (fun e => e.val) ∧ ¬ e.IsDiag) ↔
    e ∈ S.image (fun e => e.val)
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact G.not_isDiag_of_mem_edgeSet (graph_edge_mem G f)

private theorem state_edge_card {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) :
    Nat.card (graphOfState G S).edgeSet = S.card := by
  classical
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, state_edgeFinset]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/- The existing frozen cycle-space theorem supplies the spanning-forest count.
   These consumed projections do not count as new mathematical content. -/
private theorem spanning_forest_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.Reachable = G.Reachable ∧
      Nat.card T.edgeSet + Nat.card G.ConnectedComponent = Fintype.card V ∧
      Fintype.card V ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
  classical
  letI : MeasurableSpace (ZMod 2) := ⊤
  letI : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have h := D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.finite_graph_cycle_space G
  obtain ⟨T, hle, ha, hr⟩ := h.2.1
  obtain ⟨cycles, hc, hp, hd, basis, hb, ht, hbound, rest⟩ := h.2.2 T hle ha hr
  refine ⟨T, hle, hr, ?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card] using ht
  · simpa only [Nat.card_eq_fintype_card] using hbound

private theorem component_card_le {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective G.connectedComponentMk (fun c => c.exists_rep)

/-- All nonisolated vertices are supported on at most twice the graph rank. -/
theorem support_card_le_twice_rank {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    G.support.ncard ≤ 2 * (Fintype.card V - Nat.card G.ConnectedComponent) := by
  classical
  obtain ⟨T, hTG, hreach, hcard, _⟩ := spanning_forest_card G
  have hsupp : G.support = T.support := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw⟩ := G.mem_support.mp hv
      have hr : T.Reachable v w := by rw [hreach]; exact hw.reachable
      exact SimpleGraph.mem_support_of_reachable (G.ne_of_adj hw) hr
    · intro v hv
      obtain ⟨w, hw⟩ := T.mem_support.mp hv
      exact G.mem_support.mpr ⟨w, hTG hw⟩
  have ht : T.support.ncard ≤ 2 * Nat.card T.edgeSet := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      ← T.sum_degrees_support_eq_twice_card_edges, Set.ncard_eq_toFinset_card']
    calc
      T.support.toFinset.card = ∑ _v ∈ T.support.toFinset, 1 := by simp
      _ ≤ ∑ v ∈ T.support.toFinset, T.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact (T.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv)
  rw [hsupp]
  have hc := component_card_le G
  have he : Nat.card T.edgeSet = Fintype.card V - Nat.card G.ConnectedComponent := by omega
  exact he ▸ ht

/-- Rank and nonnegative state exponents follow from the actual component count. -/
theorem graph_rank_bounds {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) :
    graphRank G S ≤ S.card ∧ graphRank G S ≤ n - 1 ∧
      0 ≤ stateExponentInteger n (graphRank G S) S.card := by
  classical
  have hc := component_card_le (graphOfState G S)
  obtain ⟨T, hT, hr, ht, he⟩ := spanning_forest_card (graphOfState G S)
  rw [state_edge_card] at he
  have hpos : 0 < Nat.card (graphOfState G S).ConnectedComponent := by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Nat.card_pos
  simp only [Fintype.card_fin] at hc he
  dsimp [graphRank, stateExponentInteger]
  omega

noncomputable def graphStatePolynomial {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) : ℤ[X] := by
  classical
  exact statePolynomial n (graphRank G) (fun S => (graph_rank_bounds hn G S).2.2)

/-- A state of rank `j` has at most `2j` nonisolated vertices. -/
theorem graph_state_support_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) :
    (graphOfState G S).support.ncard ≤ 2 * graphRank G S := by
  simpa only [graphRank, Fintype.card_fin] using support_card_le_twice_rank (graphOfState G S)

private theorem reachable_support_iff {V : Type*} {H : SimpleGraph V}
    {u v : V} (h : H.Reachable u v) : u ∈ H.support ↔ v ∈ H.support := by
  by_cases heq : u = v
  · subst v; rfl
  · exact ⟨fun _ => SimpleGraph.mem_support_of_reachable (Ne.symm heq) h.symm,
      fun _ => SimpleGraph.mem_support_of_reachable heq h⟩

/-- Removing isolated vertices preserves graph rank. -/
private theorem rank_induce_support {V : Type*} [Fintype V] (H : SimpleGraph V) :
    Fintype.card V - Nat.card H.ConnectedComponent =
      H.support.ncard - Nat.card (H.induce H.support).ConnectedComponent := by
  classical
  let K := H.induce H.support
  let incl : K →g H := (SimpleGraph.Embedding.induce H.support).toHom
  let m := SimpleGraph.ConnectedComponent.map incl
  have hm : Function.Injective m := by
    intro C C'
    refine C.ind (fun a => ?_)
    refine C'.ind (fun b => ?_)
    intro heq
    apply SimpleGraph.ConnectedComponent.sound
    have hr : H.Reachable a.val b.val := SimpleGraph.ConnectedComponent.exact heq
    obtain ⟨p⟩ := hr
    have hp : ∀ v ∈ p.support, v ∈ H.support := by
      intro v hv
      by_cases hnil : p.Nil
      · rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at hv
        simpa only [List.mem_singleton.mp hv] using a.property
      · exact SimpleGraph.mem_support_of_mem_walk_support p hnil hv
    exact ⟨p.induce H.support hp⟩
  let I := {v : V // v ∉ H.support}
  have hdisj (C : K.ConnectedComponent) (v : I) :
      m C ≠ H.connectedComponentMk v.val := by
    refine C.ind (fun a => ?_)
    intro heq
    have hr : H.Reachable a.val v.val := SimpleGraph.ConnectedComponent.exact heq
    exact v.property ((reachable_support_iff hr).mp a.property)
  let f : K.ConnectedComponent ⊕ I → H.ConnectedComponent :=
    Sum.elim m (fun v => H.connectedComponentMk v.val)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      cases x with
      | inl C =>
        cases y with
        | inl C' => exact congrArg Sum.inl (hm hxy)
        | inr v => exact False.elim (hdisj C v hxy)
      | inr v =>
        cases y with
        | inl C => exact False.elim (hdisj C v hxy.symm)
        | inr w =>
          apply congrArg Sum.inr
          apply Subtype.ext
          by_contra hne
          have hr : H.Reachable v.val w.val := SimpleGraph.ConnectedComponent.exact hxy
          exact v.property (SimpleGraph.mem_support_of_reachable hne hr)
    · intro C
      obtain ⟨v, hv⟩ := C.exists_rep
      by_cases hs : v ∈ H.support
      · exact ⟨Sum.inl (K.connectedComponentMk ⟨v, hs⟩), hv⟩
      · exact ⟨Sum.inr ⟨v, hs⟩, hv⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  have hi : Fintype.card I = Fintype.card V - H.support.ncard := by
    simp only [I, Fintype.card_subtype_compl, Set.ncard_eq_toFinset_card',
      Set.toFinset_card]
  have hK := component_card_le K
  have hsc : H.support.ncard = Fintype.card H.support := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hsupport : H.support.ncard ≤ Fintype.card V := by
    rw [hsc]
    exact Fintype.card_subtype_le (· ∈ H.support)
  simp only [Fintype.card_sum, hi] at hc
  simp only [Nat.card_eq_fintype_card] at hK ⊢
  rw [hsc]
  change Fintype.card V - Fintype.card H.ConnectedComponent =
    Fintype.card H.support - Fintype.card K.ConnectedComponent
  omega

/-- Sources in the orientation induced by the vertex order. -/
def orderedSources {t : ℕ} (P : SimpleGraph (Fin t)) : Finset (Fin t) :=
  Finset.univ.filter (fun v => ¬ ∃ u, u < v ∧ P.Adj u v)

private theorem cyclic_source_count {t : ℕ} (P : SimpleGraph (Fin t))
    (hnoiso : ∀ v, ∃ w, P.Adj v w) (hcyc : ¬ P.IsAcyclic) :
    (orderedSources P).card + Nat.card P.ConnectedComponent + 1 ≤ t := by
  classical
  let N := {v : Fin t // ∃ u, u < v ∧ P.Adj u v}
  let f : N → P.ConnectedComponent := fun v => P.connectedComponentMk v.val
  have hsurj : Function.Surjective f := by
    intro C
    obtain ⟨v, hv⟩ := C.exists_rep
    obtain ⟨w, hw⟩ := hnoiso v
    by_cases hlt : w < v
    · refine ⟨⟨v, w, hlt, hw.symm⟩, hv⟩
    · have hvw : v < w := lt_of_le_of_ne (le_of_not_gt hlt) (P.ne_of_adj hw)
      refine ⟨⟨w, v, hvw, hw⟩, ?_⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hw).symm.trans hv
  have hle := Fintype.card_le_of_surjective f hsurj
  have hstrict : Fintype.card P.ConnectedComponent < Fintype.card N := by
    by_contra hnot
    have heq : Fintype.card N = Fintype.card P.ConnectedComponent := by omega
    have hinj : Function.Injective f :=
      (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq heq)).mpr hsurj
    apply hcyc
    let ranks : D5.S3.Combinatorics.Graph.Jacobi.Pruning.LeafRanks P := {
      rank := fun v => v.val
      cut := t
      later_unique := by
        intro v hv a b hva hvb hla hlb
        have hna : a ∈ (Finset.univ : Finset (Fin t)).filter
            (fun a => ∃ u, u < a ∧ P.Adj u a) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, lt_of_le_of_ne hla (P.ne_of_adj hva), hva⟩
        have hnb : ∃ u, u < b ∧ P.Adj u b :=
          ⟨v, lt_of_le_of_ne hlb (P.ne_of_adj hvb), hvb⟩
        have hna' : ∃ u, u < a ∧ P.Adj u a := (Finset.mem_filter.mp hna).2
        have he : f ⟨a, hna'⟩ = f ⟨b, hnb⟩ :=
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hva).symm.trans
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvb)
        exact congrArg Subtype.val (hinj he) }
    let embedding : P →g P.induce {v | ranks.rank v < ranks.cut} := {
      toFun := fun v => ⟨v, v.isLt⟩
      map_rel' := fun h => h }
    exact (D5.S3.Combinatorics.Graph.Jacobi.Pruning.deleted_acyclic ranks).comap embedding (fun a b h => congrArg Subtype.val h)
  have hsplit : (orderedSources P).card + Fintype.card N = t := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin t)))
      (fun v => ¬ ∃ u, u < v ∧ P.Adj u v)
    simpa only [orderedSources, not_not, Fintype.card_subtype, Fintype.card_fin,
      Finset.card_univ, N] using h
  rw [Nat.card_eq_fintype_card]
  omega

/-- Later neighbors in the specified vertex order. -/
abbrev forwardNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :=
  {v : Fin n // u < v ∧ G.Adj u v}

/-- A genuine bounded-forward-degree ordering, independent of any subset counts. -/
def boundedForwardDegree {n : ℕ} (D : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u, Nat.card (forwardNeighbors G u) ≤ D

/-- Increasing embeddings preserve every edge of the actual support pattern. -/
abbrev orderedEmbeddings {t n : ℕ} (P : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) :=
  {f : Fin t → Fin n // StrictMono f ∧ ∀ u v, P.Adj u v → G.Adj (f u) (f v)}

private theorem ordered_embedding_count {t n D : ℕ}
    (P : SimpleGraph (Fin t)) (G : SimpleGraph (Fin n))
    (hD : boundedForwardDegree D G) :
    Nat.card (orderedEmbeddings P G) ≤
      n ^ (orderedSources P).card * D ^ (t - (orderedSources P).card) := by
  classical
  let A := {i : Fin t // i ∈ orderedSources P}
  let B := {i : Fin t // i ∉ orderedSources P}
  have hp (i : B) : ∃ p, p < i.val ∧ P.Adj p i.val := by
    simpa only [orderedSources, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      using i.property
  choose parent hparent using hp
  have hslots (u : Fin n) : Nonempty (forwardNeighbors G u ↪ Fin D) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hD u
  let slot := fun u => Classical.choice (hslots u)
  have hslot_unique {u v a b : Fin n}
      (ha : u < a ∧ G.Adj u a) (hb : v < b ∧ G.Adj v b) (huv : u = v)
      (hs : slot u ⟨a, ha⟩ = slot v ⟨b, hb⟩) : a = b := by
    subst v
    exact congrArg Subtype.val ((slot u).injective hs)
  let code : orderedEmbeddings P G → (A → Fin n) × (B → Fin D) := fun f =>
    (fun i => f.val i.val, fun i =>
      slot (f.val (parent i)) ⟨f.val i.val, f.property.1 (hparent i).1,
        f.property.2 _ _ (hparent i).2⟩)
  have hinj : Function.Injective code := by
    intro f g hcode
    apply Subtype.ext
    funext i
    have heval : ∀ m : ℕ, ∀ a : Fin t, a.val = m → f.val a = g.val a := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro a ha
        by_cases hs : a ∈ orderedSources P
        · exact congrFun (congrArg Prod.fst hcode) ⟨a, hs⟩
        · let b : B := ⟨a, hs⟩
          have hpar : f.val (parent b) = g.val (parent b) :=
            ih (parent b).val (by have hlt := (hparent b).1; change (parent b).val < a.val at hlt; omega)
              (parent b) rfl
          have hc := congrFun (congrArg Prod.snd hcode) b
          dsimp only [code] at hc
          exact hslot_unique _ _ hpar hc
    exact heval i.val i rfl
  have hA : Fintype.card A = (orderedSources P).card := Fintype.card_coe _
  have hB : Fintype.card B = t - (orderedSources P).card := by
    rw [Fintype.card_subtype_compl, hA, Fintype.card_fin]
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, hA, hB] using hc

/-- A cyclic pattern of rank `j` has only `j-1` unconstrained vertex choices.
    The proof uses a finite injection into source images and forward-neighbor slots. -/
theorem cyclic_ordered_embedding_count {t n D : ℕ}
    (P : SimpleGraph (Fin t)) (G : SimpleGraph (Fin n))
    (hnoiso : ∀ v, ∃ w, P.Adj v w) (hcyc : ¬ P.IsAcyclic)
    (hD : boundedForwardDegree D G) :
    Nat.card (orderedEmbeddings P G) ≤
      (D + 1) ^ (2 * (t - Nat.card P.ConnectedComponent)) *
        (n + 1) ^ (t - Nat.card P.ConnectedComponent - 1) := by
  classical
  let j := t - Nat.card P.ConnectedComponent
  have hsource := cyclic_source_count P hnoiso hcyc
  have hs : (orderedSources P).card ≤ j - 1 := by dsimp [j]; omega
  have ht : t ≤ 2 * j := by
    have hsupport : P.support = Set.univ := by ext v; simp only [Set.mem_univ, iff_true]; exact hnoiso v
    have h := support_card_le_twice_rank P
    dsimp [j]
    simpa only [hsupport, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using h
  calc
    Nat.card (orderedEmbeddings P G) ≤
        n ^ (orderedSources P).card * D ^ (t - (orderedSources P).card) :=
      ordered_embedding_count P G hD
    _ ≤ (n + 1) ^ (j - 1) * (D + 1) ^ (2 * j) := by
      apply Nat.mul_le_mul
      · exact (Nat.pow_le_pow_left (Nat.le_succ n) _).trans
          (Nat.pow_le_pow_right (by omega) hs)
      · exact (Nat.pow_le_pow_left (Nat.le_succ D) _).trans
          (Nat.pow_le_pow_right (by omega) ((Nat.sub_le _ _).trans ht))
    _ = (D + 1) ^ (2 * j) * (n + 1) ^ (j - 1) := Nat.mul_comm _ _

private theorem graphOfState_le {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) : graphOfState G S ≤ G := by
  classical
  unfold graphOfState
  apply (G.fromEdgeSet_le).mpr
  intro e he
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he.1
  exact hfe ▸ graph_edge_mem G f

private theorem graphOfState_injective {n : ℕ} (G : SimpleGraph (Fin n)) :
    Function.Injective (graphOfState G) := by
  classical
  intro S T h
  apply Finset.image_injective Subtype.val_injective
  rw [← state_edgeFinset G S, ← state_edgeFinset G T, h]

private theorem acyclic_edge_rank {V : Type*} [Fintype V] (P : SimpleGraph V)
    (ha : P.IsAcyclic) :
    Nat.card P.edgeSet = Fintype.card V - Nat.card P.ConnectedComponent := by
  classical
  letI : MeasurableSpace (ZMod 2) := ⊤
  letI : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
  letI : Fintype P.edgeSet := Fintype.ofFinite _
  letI : Fintype P.ConnectedComponent := Fintype.ofFinite _
  have h := D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.finite_graph_cycle_space P
  obtain ⟨cycles, hc, hp, hd, basis, hb, ht, rest⟩ := h.2.2 P le_rfl ha rfl
  have hcc : Nat.card P.ConnectedComponent = Fintype.card P.ConnectedComponent :=
    Nat.card_eq_fintype_card
  omega

/-- The finite family of simple support patterns of a specified graph rank. -/
abbrev cyclicPatterns (t j : ℕ) :=
  {P : SimpleGraph (Fin t) //
    (∀ v, ∃ w, P.Adj v w) ∧ ¬ P.IsAcyclic ∧ t - Nat.card P.ConnectedComponent = j}

/-- Only edge subsets of this exact graph rank occur in the filter. -/
def cyclicRankStates {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) :
    Finset (Finset (graphEdge G)) :=
  Finset.univ.filter (fun S => graphRank G S = j ∧ j < S.card)

private theorem state_pattern_representation {n j : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (graphEdge G))
    (hrank : graphRank G S = j) (hcyclic : j < S.card) :
    ∃ d : (Σ t : Fin (2 * j + 1), Σ P : cyclicPatterns t.val j,
        orderedEmbeddings P.val G),
      d.2.1.val.map d.2.2.val = graphOfState G S := by
  classical
  let H := graphOfState G S
  let A := H.support.toFinset
  let t := A.card
  let f : Fin t ↪o Fin n := A.orderEmbOfFin rfl
  let e : Fin t ≃ H.support := (A.orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight (fun _ => Set.mem_toFinset))
  let P := H.comap f
  let K := H.induce H.support
  let iso : P ≃g K := { toEquiv := e, map_rel_iff' := by intro a b; rfl }
  have ht : t = H.support.ncard := by
    dsimp [t, A]
    symm
    exact Set.ncard_eq_toFinset_card' H.support
  have hsize : t < 2 * j + 1 := by
    have hs := graph_state_support_bound G S
    change H.support.ncard ≤ 2 * graphRank G S at hs
    omega
  have hnoiso : ∀ a, ∃ b, P.Adj a b := by
    intro a
    obtain ⟨w, hw⟩ := H.mem_support.mp (e a).property
    let b := e.symm ⟨w, hw.mem_support_right⟩
    refine ⟨b, ?_⟩
    change H.Adj (e a).val (e b).val
    simpa only [b, Equiv.apply_symm_apply] using hw
  have hmap : P.map f.toEmbedding = H := by
    apply le_antisymm (SimpleGraph.map_comap_le f.toEmbedding H)
    intro u v huv
    have hu : u ∈ Set.range f := by
      rw [Finset.range_orderEmbOfFin]
      exact Set.mem_toFinset.mpr huv.mem_support_left
    have hv : v ∈ Set.range f := by
      rw [Finset.range_orderEmbOfFin]
      exact Set.mem_toFinset.mpr huv.mem_support_right
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    refine ⟨huv.ne, a, b, ?_, ha, hb⟩
    change H.Adj (f a) (f b)
    simpa only [ha, hb] using huv
  have hj : t - Nat.card P.ConnectedComponent = j := by
    have hr := rank_induce_support H
    have hc := Nat.card_congr iso.connectedComponentEquiv
    change Nat.card P.ConnectedComponent = Nat.card K.ConnectedComponent at hc
    change n - Nat.card H.ConnectedComponent = j at hrank
    simp only [Fintype.card_fin] at hr
    change n - Nat.card H.ConnectedComponent =
      H.support.ncard - Nat.card K.ConnectedComponent at hr
    rw [← ht] at hr
    rw [hc]
    exact hr.symm.trans hrank
  have he : Nat.card P.edgeSet = S.card := by
    rw [← state_edge_card G S]
    change Nat.card P.edgeSet = Nat.card H.edgeSet
    have hcMap : Nat.card (P.map f.toEmbedding).edgeSet = Nat.card P.edgeSet := by
      have h := SimpleGraph.card_edgeFinset_map f.toEmbedding P
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h
    exact hcMap.symm.trans (congrArg (fun L : SimpleGraph (Fin n) => Nat.card L.edgeSet) hmap)
  have hcyc : ¬ P.IsAcyclic := by
    intro ha
    have h := acyclic_edge_rank P ha
    simp only [Fintype.card_fin] at h
    omega
  let hemb : orderedEmbeddings P G :=
    ⟨f, f.strictMono, fun a b h => graphOfState_le G S h⟩
  exact ⟨⟨⟨t, hsize⟩, ⟨P, hnoiso, hcyc, hj⟩, hemb⟩, hmap⟩

/-- A cyclic edge subset in a simple graph has actual graph rank at least two. -/
theorem cyclic_graph_rank_ge_two {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) (hcyc : graphRank G S < S.card) :
    2 ≤ graphRank G S := by
  classical
  obtain ⟨d, hd⟩ := state_pattern_representation G S rfl hcyc
  have hs := cyclic_source_count d.2.1.val d.2.1.property.1 d.2.1.property.2.1
  have hr := d.2.1.property.2.2
  have ht : 0 < d.1.val := by
    by_contra hnot
    have ht0 : d.1.val = 0 := by omega
    have he : d.2.1.val = ⊥ := by
      ext u v
      exact Fin.elim0 (Fin.cast ht0 u)
    apply d.2.1.property.2.1
    rw [he]
    exact SimpleGraph.isAcyclic_bot
  have hsource : 0 < (orderedSources d.2.1.val).card := by
    apply Finset.card_pos.mpr
    refine ⟨⟨0, ht⟩, ?_⟩
    simp only [orderedSources, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨u, hu, _⟩
    exact Nat.not_lt_zero u.val hu
  omega

/-- A finite constant depending only on forward degree and graph rank. -/
noncomputable def cyclicPatternConstant (D j : ℕ) : ℕ :=
  (D + 1) ^ (2 * j) * ∑ t : Fin (2 * j + 1), Nat.card (cyclicPatterns t.val j)

/-- Actual rank-`j` cyclic states inject into finitely many ordered support patterns. -/
theorem cyclic_rank_state_count_vertices {n D j : ℕ}
    (G : SimpleGraph (Fin n)) (hD : boundedForwardDegree D G) :
    (cyclicRankStates G j).card ≤
      cyclicPatternConstant D j * (n + 1) ^ (j - 1) := by
  classical
  let R := {S : Finset (graphEdge G) // S ∈ cyclicRankStates G j}
  let T := Σ t : Fin (2 * j + 1), Σ P : cyclicPatterns t.val j, orderedEmbeddings P.val G
  let decode : T → SimpleGraph (Fin n) := fun d =>
    d.2.1.val.map d.2.2.val
  have hrepr (S : R) : ∃ d : T, decode d = graphOfState G S.val := by
    obtain ⟨hr, hc⟩ := (Finset.mem_filter.mp S.property).2
    exact state_pattern_representation G S.val hr hc
  choose code hcode using hrepr
  have hinj : Function.Injective code := by
    intro S S' h
    apply Subtype.ext
    apply graphOfState_injective G
    rw [← hcode S, ← hcode S', h]
  have hcount : (cyclicRankStates G j).card ≤ Fintype.card T := by
    simpa only [R, Fintype.card_coe] using Fintype.card_le_of_injective code hinj
  have hT : Fintype.card T ≤ cyclicPatternConstant D j * (n + 1) ^ (j - 1) := by
    simp only [T, Fintype.card_sigma]
    change (∑ t : Fin (2 * j + 1), ∑ P : cyclicPatterns t.val j,
      Fintype.card (orderedEmbeddings P.val G)) ≤ _
    calc
      _ ≤ ∑ t : Fin (2 * j + 1), ∑ _P : cyclicPatterns t.val j,
          (D + 1) ^ (2 * j) * (n + 1) ^ (j - 1) := by
        apply Finset.sum_le_sum
        intro t _
        apply Finset.sum_le_sum
        intro P _
        have h := cyclic_ordered_embedding_count P.val G P.property.1 P.property.2.1 hD
        rw [P.property.2.2] at h
        simpa only [Nat.card_eq_fintype_card] using h
      _ = cyclicPatternConstant D j * (n + 1) ^ (j - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cyclicPatternConstant,
          Nat.card_eq_fintype_card]
        simp_rw [← Nat.mul_assoc]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
  exact hcount.trans hT

/-- The cyclic state count is uniform in connected graphs and the carrier size. -/
theorem cyclic_rank_state_count {n D j : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (hD : boundedForwardDegree D G) :
    (cyclicRankStates G j).card ≤
      (2 ^ j * cyclicPatternConstant D j) * (Nat.card G.edgeSet + 1) ^ (j - 1) := by
  have hvertices := hG.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hvertices
  have hcard : Nat.card G.edgeSet = Fintype.card G.edgeSet := Nat.card_eq_fintype_card
  have hn : n + 1 ≤ 2 * (Nat.card G.edgeSet + 1) := by omega
  calc
    _ ≤ cyclicPatternConstant D j * (n + 1) ^ (j - 1) :=
      cyclic_rank_state_count_vertices G hD
    _ ≤ cyclicPatternConstant D j * (2 * (Nat.card G.edgeSet + 1)) ^ (j - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
    _ ≤ cyclicPatternConstant D j * (2 ^ j * (Nat.card G.edgeSet + 1) ^ (j - 1)) := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))
    _ = _ := by ring

/-- State exponents are bounded in terms of the total edge count. -/
private theorem graph_state_exponent_le {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (S : Finset (graphEdge G)) :
    stateExponent n (graphRank G S) S.card (graph_rank_bounds hn G S).2.2 ≤
      2 * Nat.card G.edgeSet := by
  classical
  have hv := hG.card_vert_le_card_edgeSet_add_one
  have hs : S.card ≤ Nat.card G.edgeSet := by
    letI : Fintype G.edgeSet := Fintype.ofFinite _
    have hi : Function.Injective (fun e : graphEdge G =>
        (⟨e.val, graph_edge_mem G e⟩ : G.edgeSet)) := by
      intro a b hab
      exact Subtype.ext (congrArg Subtype.val hab)
    have hE := Fintype.card_le_of_injective _ hi
    exact (S.card_le_univ).trans (by simpa only [Nat.card_eq_fintype_card] using hE)
  have he := stateExponent_cast_eq_integer (graph_rank_bounds hn G S).2.2
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hv
  have hEc : Nat.card G.edgeSet = Fintype.card G.edgeSet := Nat.card_eq_fintype_card
  dsimp [stateExponentInteger] at he
  omega

/-- The rank-`j` coefficient growth is derived from the actual graph state. -/
theorem graph_term_coefficient_bound {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ)
    (S : Finset (graphEdge G)) :
    (termCoefficient n k (graphRank G)
      (fun S => (graph_rank_bounds hn G S).2.2) S).natAbs ≤
      2 ^ k * (Nat.card G.edgeSet + 1) ^ (k - graphRank G S) := by
  classical
  let a := stateExponent n (graphRank G S) S.card (graph_rank_bounds hn G S).2.2
  by_cases hk : graphRank G S ≤ k
  · have ha : a ≤ 2 * (Nat.card G.edgeSet + 1) :=
      (graph_state_exponent_le hn G hG S).trans (by omega)
    simp only [termCoefficient, hk, ↓reduceIte, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_neg, Int.natAbs_one, one_pow, Int.natAbs_natCast, one_mul]
    calc
      a.choose (k - graphRank G S) ≤ a ^ (k - graphRank G S) := Nat.choose_le_pow _ _
      _ ≤ (2 * (Nat.card G.edgeSet + 1)) ^ (k - graphRank G S) :=
        Nat.pow_le_pow_left ha _
      _ = 2 ^ (k - graphRank G S) *
          (Nat.card G.edgeSet + 1) ^ (k - graphRank G S) := mul_pow _ _ _
      _ ≤ 2 ^ k * (Nat.card G.edgeSet + 1) ^ (k - graphRank G S) := by
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  · simp [termCoefficient, hk]

end D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate
