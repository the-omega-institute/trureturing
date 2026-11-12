/- GID: D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot
   mirror-E: none(waiver:exact-symbolic-independent-subset-counting)
   anchors: []
   utility: none
   digest: An actual finite graph has an irrational purely imaginary independence root. -/

import D5.S3.StatisticalMechanics.HardCore.PartitionJoin
import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration

/-! Native independent-subset counting and an irrational imaginary root. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot

open Finset Polynomial
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.PartitionJoin
open D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
open D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration

attribute [local instance] Classical.propDecidable

private lemma partition_complete {α R : Type*} [DecidableEq α] [CommRing R]
    [DecidableRel (⊤ : SimpleGraph α).Adj]
    (V : Finset α) (z : R) :
    partition (⊤ : SimpleGraph α) V (fun _ => z) = 1 + V.card * z := by
  classical
  induction V using Finset.induction_on with
  | empty => simp [partition_empty]
  | @insert a V ha ih =>
      have hc : closedComplement (⊤ : SimpleGraph α) (insert a V) a = ∅ := by
        ext x
        simp [closedComplement, SimpleGraph.top_adj, ne_comm]
        tauto
      have h := partition_delete (⊤ : SimpleGraph α) (insert a V) a (by simp) (fun _ => z)
      rw [erase_insert ha, hc, partition_empty, ih] at h
      rw [h, card_insert_of_notMem ha]
      push_cast
      ring

private lemma partition_edgeless {α R : Type*} [DecidableEq α] [CommRing R]
    [DecidableRel (⊥ : SimpleGraph α).Adj]
    (V : Finset α) (z : R) :
    partition (⊥ : SimpleGraph α) V (fun _ => z) = (1 + z) ^ V.card := by
  have hc : configurations (⊥ : SimpleGraph α) V = V.powerset := by
    simp [configurations, SimpleGraph.IsIndepSet, Set.Pairwise]
  rw [partition, hc, ← Finset.prod_one_add]
  simp

/-- A finite sequence of tagged copies, with a separate empty terminal type. -/
def Copies (α : Type) : ℕ → Type
  | 0 => Empty
  | n + 1 => α ⊕ Copies α n

instance copiesFintype {α : Type} [Fintype α] : (n : ℕ) → Fintype (Copies α n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n + 1 => by
      letI := copiesFintype (α := α) n
      exact inferInstanceAs (Fintype (α ⊕ Copies α n))

instance copiesDecidableEq {α : Type} [DecidableEq α] : (n : ℕ) → DecidableEq (Copies α n)
  | 0 => inferInstanceAs (DecidableEq Empty)
  | n + 1 => by
      letI := copiesDecidableEq (α := α) n
      exact inferInstanceAs (DecidableEq (α ⊕ Copies α n))

/-- Distinct copies are completely joined; each copy retains its original edges. -/
def joinedCopies {α : Type} (G : SimpleGraph α) : (n : ℕ) → SimpleGraph (Copies α n)
  | 0 => ⊥
  | n + 1 => join G (joinedCopies G n)

private lemma partition_joinedCopies {α R : Type} [Fintype α] [DecidableEq α] [CommRing R]
    (G : SimpleGraph α) [DecidableRel G.Adj] (n : ℕ) (z : R) :
    partition (joinedCopies G n) univ (fun _ => z) =
      1 + n * (partition G univ (fun _ => z) - 1) := by
  classical
  induction n with
  | zero =>
      have h : (univ : Finset (Copies α 0)) = ∅ := by ext x; exact Empty.elim x
      simp [h, partition_empty]
  | succ n ih =>
      change partition (join G (joinedCopies G n)) univ (fun _ => z) = _
      rw [← univ_disjSum_univ, partition_join, ih]
      push_cast
      ring

abbrev FourCliqueVertices := ((Fin 4 ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4

/-- Four disjoint copies of the complete graph on four vertices. -/
def fourCliques : SimpleGraph FourCliqueVertices :=
  (((⊤ : SimpleGraph (Fin 4)) ⊕g ⊤) ⊕g ⊤) ⊕g ⊤

private lemma partition_fourCliques {R : Type} [CommRing R] (z : R) :
    partition fourCliques univ (fun _ => z) = (1 + 4 * z) ^ 4 := by
  classical
  unfold fourCliques
  rw [← univ_disjSum_univ, partition_sum,
    ← univ_disjSum_univ, partition_sum,
    ← univ_disjSum_univ, partition_sum]
  simp only [partition_complete, card_univ, Fintype.card_fin, Nat.cast_ofNat]
  ring

abbrev Vertex := (FourCliqueVertices ⊕ Copies (Fin 2) 34) ⊕ Fin 44

/-- Join the four-clique union, thirty-four independent pairs, and a 44-clique.
The pairs are mutually joined, so vertices from different pairs cannot coexist
in an independent configuration. -/
def graph : SimpleGraph Vertex :=
  join (join fourCliques (joinedCopies (⊥ : SimpleGraph (Fin 2)) 34)) ⊤

private lemma partition_graph {R : Type} [CommRing R] (z : R) :
    partition graph univ (fun _ => z) =
      1 + 128 * z + 130 * z ^ 2 + 256 * z ^ 3 + 256 * z ^ 4 := by
  classical
  unfold graph
  rw [← univ_disjSum_univ, partition_join,
    ← univ_disjSum_univ, partition_join,
    partition_fourCliques, partition_joinedCopies, partition_edgeless,
    partition_complete]
  norm_num only [card_univ, Fintype.card_fin, Nat.cast_ofNat]
  ring

private lemma coefficient_count {α : Type} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (k : ℕ) :
    (independencePolynomial G V).coeff k =
      (((configurations G V).filter (fun S => S.card = k)).card : ℤ) := by
  simp [independencePolynomial, partition, Finset.prod_const,
    Polynomial.coeff_X_pow, eq_comm]

/-- The integer polynomial, its actual degree, and all independent-subset counts,
including the empty subset and the entire zero tail. -/
theorem native_polynomial :
    independencePolynomial graph univ =
      (1 + 2 * X ^ 2) * (1 + 128 * X + 128 * X ^ 2) ∧
    (independencePolynomial graph univ).natDegree = 4 ∧
    (∀ k : ℕ, ((configurations graph univ).filter (fun S => S.card = k)).card =
      if k = 0 then 1 else if k = 1 then 128 else if k = 2 then 130
      else if k = 3 then 256 else if k = 4 then 256 else 0) := by
  have hp : independencePolynomial graph univ =
      1 + 128 * X + 130 * X ^ 2 + 256 * X ^ 3 + 256 * X ^ 4 :=
    partition_graph (X : Polynomial ℤ)
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    ring
  · rw [hp]
    compute_degree <;> norm_num
  · intro k
    have hc := coefficient_count graph univ k
    rw [hp] at hc
    generalize hN : ((configurations graph univ).filter (fun S => S.card = k)).card = N at hc ⊢
    by_cases h0 : k = 0
    · subst k; norm_num [Polynomial.coeff_one, Polynomial.coeff_X] at hc ⊢; exact_mod_cast hc.symm
    by_cases h1 : k = 1
    · subst k; norm_num [Polynomial.coeff_one, Polynomial.coeff_X] at hc ⊢; exact_mod_cast hc.symm
    by_cases h2 : k = 2
    · subst k; norm_num [Polynomial.coeff_one, Polynomial.coeff_X] at hc ⊢; exact_mod_cast hc.symm
    by_cases h3 : k = 3
    · subst k; norm_num [Polynomial.coeff_one, Polynomial.coeff_X] at hc ⊢; exact_mod_cast hc.symm
    by_cases h4 : k = 4
    · subst k; norm_num [Polynomial.coeff_one, Polynomial.coeff_X] at hc ⊢; exact_mod_cast hc.symm
    simp [coeff_one, coeff_X, coeff_X_pow, h0, h1, Ne.symm h1, h2, h3, h4] at hc ⊢
    exact_mod_cast hc.symm

private lemma vertex_card : Fintype.card Vertex = 128 := by
  have hc (n : ℕ) : Fintype.card (Copies (Fin 2) n) = 2 * n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change Fintype.card (Fin 2 ⊕ Copies (Fin 2) n) = _
        rw [Fintype.card_sum, ih, Fintype.card_fin]
        omega
  simp [Vertex, FourCliqueVertices, Fintype.card_sum, hc]

/-- A graph on the standard finite domain, transported by an actual vertex equivalence. -/
def finGraph : SimpleGraph (Fin 128) :=
  graph.map (Fintype.equivFinOfCardEq vertex_card).toEmbedding

private lemma fin_polynomial :
    independencePolynomial finGraph univ = independencePolynomial graph univ := by
  classical
  let e : Vertex ≃ Fin 128 := Fintype.equivFinOfCardEq vertex_card
  have he : ∀ u v, finGraph.Adj (e u) (e v) ↔ graph.Adj u v := by
    intro u v
    exact SimpleGraph.map_adj_apply
  have h := partition_relabel graph finGraph e he univ (fun _ => (X : Polynomial ℤ))
  rw [image_univ_equiv] at h
  exact h

/-- Brown–Cameron Question 2: no order, connectivity, independence-number, or
modulus restriction is imposed on the existential statement. -/
theorem result : ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (b : ℝ),
    Irrational b ∧
      Polynomial.eval₂ (Int.castRingHom ℂ) (Complex.I * (b : ℂ))
        (independencePolynomial G univ) = 0 := by
  classical
  refine ⟨128, finGraph, (Real.sqrt 2)⁻¹, irrational_sqrt_two.inv, ?_⟩
  rw [fin_polynomial, native_polynomial.1]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hz : 1 + 2 * (Complex.I * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 = 0 := by
    push_cast
    rw [mul_pow, Complex.I_sq, inv_pow]
    rw [hs]
    norm_num
  simp only [eval₂_mul, eval₂_add, eval₂_one, eval₂_pow, eval₂_X, eval₂_ofNat]
  rw [hz, zero_mul]

#print axioms native_polynomial
#print axioms result

end D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot
