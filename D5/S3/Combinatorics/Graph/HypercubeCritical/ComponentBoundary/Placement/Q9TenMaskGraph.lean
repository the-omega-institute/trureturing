import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-! Relabel the six-axis contact graphs with ten edges. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph

open Finset
open scoped BigOperators
open Q9SquareMaskGraph (activeAxes maskGraph card_edges distance_two_mask_graph_constraints)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9MinimumDistanceOperator (minimumDisplacements)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

universe u v

abbrev Pair := Fin 6 × Fin 6

def graphOfPairs (E : Finset Pair) : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun i j => (i, j) ∈ E

instance (E : Finset Pair) : DecidableRel (graphOfPairs E).Adj :=
  fun i j => inferInstanceAs
    (Decidable (i ≠ j ∧ ((i, j) ∈ E ∨ (j, i) ∈ E)))

def isolatedC5 : Finset Pair := {(1, 2), (2, 3), (3, 4), (4, 5), (1, 5)}
def edgeAndC4 : Finset Pair := {(0, 1), (2, 3), (3, 4), (4, 5), (2, 5)}
def pathAndTriangle : Finset Pair := {(0, 2), (1, 2), (3, 4), (3, 5), (4, 5)}
def path6 : Finset Pair := {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)}

/-- The hub is 0 and the rim in cyclic order is 1, 3, 5, 2, 4. -/
abbrev wheel : SimpleGraph (Fin 6) := (graphOfPairs isolatedC5)ᶜ

/-- The shores are {0,1,2} and {3,4,5}. The extra edge is 01. -/
abbrev k33Extra : SimpleGraph (Fin 6) := (graphOfPairs pathAndTriangle)ᶜ

variable {V : Type u} [Fintype V] [DecidableEq V]

def SquareCompletion (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ ⦃a v c : V⦄, G.Adj a v → G.Adj a c → v ≠ c →
    G.degree a = 3 → G.degree v = 3 →
    ∃ d, d ≠ a ∧ G.Adj v d ∧ G.Adj c d

/-- The first two rows of the ordered complement edge set. -/
def firstPairs (kind : Fin 4) : Finset Pair :=
  ![{(1, 2), (1, 3)}, {(0, 1)}, {(0, 2), (1, 2)}, {(0, 2), (1, 3)}] kind

def expectedDegree (kind : Fin 4) (i : Fin 6) : ℕ :=
  if kind = 0 then (if i = 0 then 0 else 2)
  else if i < 2 then 1 else 2

private def remainingPairs : Finset Pair :=
  {(2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)}

private abbrev template (kind : Fin 4) : SimpleGraph (Fin 6) :=
  graphOfPairs (![isolatedC5, edgeAndC4, pathAndTriangle, path6] kind)

private def place (kind : Fin 4) (choice : Fin 3) (i : Fin 6) : Fin 6 :=
  let j : Fin 6 :=
    if kind = 0 then ![0, 1, 2, 4, 5, 3] i
    else if kind = 3 then ![0, 2, 4, 5, 3, 1] i
    else i
  if choice = 1 then Equiv.swap (4 : Fin 6) 5 j
  else if choice = 2 then Equiv.swap (3 : Fin 6) 4 j
  else j

private theorem upper_pairs :
    (∀ (kind : Fin 4) (i j : Fin 6), (i, j) ∈ firstPairs kind → i < 2 ∧ i < j) ∧
      (∀ i j : Fin 6, (i, j) ∈ remainingPairs ↔ 2 ≤ i ∧ i < j) := by
  decide +kernel

private def incident (E : Finset Pair) (i : Fin 6) : Finset Pair :=
  E.filter fun p => p.1 = i ∨ p.2 = i

private theorem degree_eq_incident (E : Finset Pair)
    (hE : ∀ p ∈ E, p.1 < p.2) (i : Fin 6) :
    (graphOfPairs E).degree i = (incident E i).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij'
    (fun j _ => if i < j then (i, j) else (j, i))
    (fun p _ => if p.1 = i then p.2 else p.1) ?_ ?_ ?_ ?_
  · intro j hj
    have ha := ((graphOfPairs E).mem_neighborFinset i j).mp hj
    obtain ⟨hne, hmem⟩ := (SimpleGraph.fromRel_adj _ _ _).mp ha
    rcases hmem with h | h
    · simp [incident, h, hE _ h]
    · simp [incident, h, not_lt_of_gt (hE _ h)]
  · rintro ⟨a, b⟩ hp
    obtain ⟨he, ha | hb⟩ := mem_filter.mp hp
    · change a = i at ha
      subst a
      simp only [Prod.fst, Prod.snd, ite_true]
      apply ((graphOfPairs E).mem_neighborFinset i b).mpr
      simp [graphOfPairs, (hE _ he).ne, he]
    · change b = i at hb
      subst b
      have hne : a ≠ i := (hE _ he).ne
      rw [if_neg hne]
      apply ((graphOfPairs E).mem_neighborFinset i a).mpr
      simp [graphOfPairs, hne.symm, he]
  · intro j hj
    have hne := (((graphOfPairs E).mem_neighborFinset i j).mp hj).ne
    by_cases h : i < j <;> simp [h, hne.symm]
  · rintro ⟨a, b⟩ hp
    obtain ⟨he, ha | hb⟩ := mem_filter.mp hp
    · change a = i at ha
      subst a
      simp [hE _ he]
    · change b = i at hb
      subst b
      have hlt := hE _ he
      simp [hlt.ne, not_lt_of_gt hlt]

private def admissibleTails (kind : Fin 4) : Finset (Finset Pair) :=
  (remainingPairs.powerset).filter fun tail =>
    ∀ i : Fin 6, (incident (firstPairs kind ∪ tail) i).card = expectedDegree kind i

private def tailCatalog (kind : Fin 4) : Finset (Finset Pair) :=
  ![{{(2, 5), (3, 4), (4, 5)}, {(2, 4), (3, 5), (4, 5)}},
    {{(2, 4), (2, 5), (3, 4), (3, 5)}, {(2, 3), (2, 5), (3, 4), (4, 5)},
      {(2, 3), (2, 4), (3, 5), (4, 5)}},
    {{(3, 4), (3, 5), (4, 5)}},
    {{(2, 5), (3, 4), (4, 5)}, {(2, 4), (3, 5), (4, 5)}}] kind

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
private theorem admissible_eq_catalog (kind : Fin 4) :
    admissibleTails kind = tailCatalog kind := by
  fin_cases kind <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 700000 in
/-- Check the relabelings only after reducing to the eight concrete tails. -/
private theorem classify_admissible_tails :
    ∀ kind : Fin 4, ∀ tail ∈ admissibleTails kind,
      ∃ choice : Fin 3, Function.Bijective (place kind choice) ∧
        ∀ i j : Fin 6,
          (graphOfPairs (firstPairs kind ∪ tail)).Adj
              (place kind choice i) (place kind choice j) ↔ (template kind).Adj i j := by
  intro kind tail ht
  rw [admissible_eq_catalog] at ht
  fin_cases kind
  · change tail ∈ ({{(2, 5), (3, 4), (4, 5)}, {(2, 4), (3, 5), (4, 5)}} :
      Finset (Finset Pair)) at ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide +kernel
  · change tail ∈ ({{(2, 4), (2, 5), (3, 4), (3, 5)}, {(2, 3), (2, 5), (3, 4), (4, 5)},
      {(2, 3), (2, 4), (3, 5), (4, 5)}} : Finset (Finset Pair)) at ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide +kernel
  · change tail ∈ ({{(3, 4), (3, 5), (4, 5)}} : Finset (Finset Pair)) at ht
    rw [mem_singleton] at ht
    subst tail
    decide +kernel
  · change tail ∈ ({{(2, 5), (3, 4), (4, 5)}, {(2, 4), (3, 5), (4, 5)}} :
      Finset (Finset Pair)) at ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide +kernel

private theorem normalized_complement_table (kind : Fin 4) (tail : Finset Pair)
    (htail : tail ∈ remainingPairs.powerset)
    (hdegree : ∀ i : Fin 6, (graphOfPairs (firstPairs kind ∪ tail)).degree i =
      expectedDegree kind i) :
    ∃ choice : Fin 3, Function.Bijective (place kind choice) ∧
      ∀ i j : Fin 6,
        (graphOfPairs (firstPairs kind ∪ tail)).Adj
            (place kind choice i) (place kind choice j) ↔ (template kind).Adj i j := by
  apply classify_admissible_tails kind tail
  refine mem_filter.mpr ⟨htail, fun i => ?_⟩
  rw [← degree_eq_incident]
  · exact hdegree i
  · rintro ⟨a, b⟩ hab
    rcases mem_union.mp hab with hfirst | hlast
    · exact (upper_pairs.1 kind a b hfirst).2
    · exact ((upper_pairs.2 a b).mp (mem_powerset.mp htail hlast)).2

def ComplementDegreeProfile (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  (∃ h, H.degree h = 0 ∧ ∀ a, a ≠ h → H.degree a = 2) ∨
    (∃ p q, p ≠ q ∧ H.degree p = 1 ∧ H.degree q = 1 ∧
      ∀ a, a ≠ p → a ≠ q → H.degree a = 2)

private theorem complement_degree_profile (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 6) (hE : G.edgeFinset.card = 10)
    (hmin : ∀ a, 3 ≤ G.degree a) :
    ComplementDegreeProfile Gᶜ := by
  have hsum : (∑ a, G.degree a) = 20 := by
    rw [G.sum_degrees_eq_twice_card_edges, hE]
  let excess (a : V) := G.degree a - 3
  have hsplit (a : V) : G.degree a = 3 + excess a := by
    have h := hmin a
    dsimp only [excess]
    omega
  have hexcess : (∑ a, excess a) = 2 := by
    have h : (∑ a, G.degree a) = (∑ _ : V, 3) + (∑ a, excess a) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ => hsplit a
    rw [hsum, sum_const, card_univ, hV] at h
    change 20 = 18 + (∑ a, excess a) at h
    omega
  have hcompl (a : V) : Gᶜ.degree a = 2 - excess a := by
    rw [G.degree_compl, hV, hsplit]
    omega
  by_cases hhub : ∃ h, excess h = 2
  · obtain ⟨h, hh⟩ := hhub
    refine Or.inl ⟨h, by rw [hcompl, hh], ?_⟩
    intro a ha
    have hle := sum_le_sum_of_subset_of_nonneg (f := excess)
      (show ({a, h} : Finset V) ⊆ univ from subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
    rw [hexcess, sum_pair ha, hh] at hle
    rw [hcompl]
    omega
  · have h01 (a : V) : excess a = 0 ∨ excess a = 1 := by
      have hle := single_le_sum (f := excess) (fun a _ => Nat.zero_le (excess a)) (mem_univ a)
      rw [hexcess] at hle
      have hne : excess a ≠ 2 := fun h => hhub ⟨a, h⟩
      omega
    let S := univ.filter (fun a => excess a = 1)
    have hS : S.card = 2 := by
      calc
        S.card = ∑ _ ∈ S, (1 : ℕ) := by simp
        _ = ∑ a ∈ S, excess a := sum_congr rfl fun _ ha => ((mem_filter.mp ha).2).symm
        _ = ∑ a, excess a := by
          apply sum_subset (subset_univ S)
          intro a _ ha
          rcases h01 a with h | h
          · exact h
          · exact (ha (mem_filter.mpr ⟨mem_univ _, h⟩)).elim
        _ = 2 := hexcess
    obtain ⟨p, q, hpq, hpair⟩ := card_eq_two.mp hS
    have hmem (a : V) : excess a = 1 ↔ a ∈ S := by simp [S]
    have hp := (hmem p).mpr (by simp [hpair])
    have hq := (hmem q).mpr (by simp [hpair])
    refine Or.inr ⟨p, q, hpq, by rw [hcompl, hp], by rw [hcompl, hq], ?_⟩
    intro a hap haq
    have hn : excess a ≠ 1 := fun h => by simpa [hpair, hap, haq] using (hmem a).mp h
    have h := h01 a
    rw [hcompl]
    omega

/-- The exact intermediate lemma still to translate. It chooses the first two
rows and extends their specified labels to an equivalence.

* Kind 0. Put the isolated vertex at 0 and any other vertex at 1.
  Put the two H-neighbors of 1 at 2,3. They are distinct from 0 because
  0 is isolated, and from 1 by looplessness.
* Kind 1. Put the two degree-one vertices at 0,1. If adjacent, the only
  upper-triangular edge involving either is 01.
* Kind 2. If the endpoints are nonadjacent with a common neighbor, put it at 2.
  The only upper-triangular edges involving 0 or 1 are 02 and 12.
* Kind 3. If the endpoints have distinct neighbors, put the neighbors
  of 0 and 1 at 2 and 3 respectively. The two upper edges are 02 and 13.

Use card_eq_one and card_eq_two on neighborFinset to obtain the forced rows.
Use Finset.exists_equiv_extend_of_card_eq with t = univ to extend each
specified injection. The resulting subtype is equivalent to V by Equiv.Set.univ.
For an actual mask family one can also extend directly with t = activeAxes F.
The unspecified vertices have degree two in each case. To prove this for
a label i, use injectivity of e to separate e i from the specified
exceptional labels. For the upper rows, i < 2 gives i = 0 or i = 1.
Use the neighbor-finset equalities and e.injective to rewrite each row,
then use the listed pairs in firstPairs.

The finite table above implements the following remaining graph argument.
In kinds 0 and 3, vertices 2 and 3 still need one neighbor each, while 4
and 5 need two each. Vertices 2 and 3 cannot be adjacent because then
4 and 5 would have only each other available. Vertices 4 and 5 must be
adjacent since otherwise all four remaining incidences at 4 and 5
would require endpoints in {2,3}, which has only two available.
The remaining two edges match {2,3} to {4,5}. This completes C5 for
kind 0 and P6 for kind 3. In kind 1 the last four vertices have
degree two on those four labels, giving C4 by deleting a perfect
matching from K4. In kind 2, vertex 2 is saturated and the last
three vertices must form a triangle, giving P3 + C3.
-/
def ComplementNormalization : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
    Fintype.card V = 6 → ComplementDegreeProfile H →
    ∃ (e : Fin 6 ≃ V) (kind : Fin 4),
      (∀ i : Fin 6, H.degree (e i) = expectedDegree kind i) ∧
      ∀ i j : Fin 6, i < j → i < 2 →
        (H.Adj (e i) (e j) ↔ (i, j) ∈ firstPairs kind)

/-- A list of distinct vertices prescribes the initial labels of an equivalence. -/
private theorem extend_labels (hV : Fintype.card V = 6)
    (labels : List V) (hdistinct : labels.Nodup) (hlen : labels.length ≤ 6) :
    ∃ e : Fin 6 ≃ V, ∀ k : Fin labels.length, e (Fin.castLE hlen k) = labels.get k := by
  let s : Finset (Fin 6) := univ.filter fun i => i.val < labels.length
  let f (i : Fin 6) : V :=
    if hi : i.val < labels.length then labels.get ⟨i.val, hi⟩
    else (Fintype.equivFinOfCardEq hV).symm i
  have hcard : Fintype.card (Fin 6) = (univ : Finset V).card := by
    rw [Fintype.card_fin, card_univ, hV]
  have hinj : Set.InjOn f (s : Set (Fin 6)) := by
    intro i hi j hj hij
    have hi' : i.val < labels.length := (mem_filter.mp (show i ∈ s from hi)).2
    have hj' : j.val < labels.length := (mem_filter.mp (show j ∈ s from hj)).2
    have hget : labels.get ⟨i.val, hi'⟩ = labels.get ⟨j.val, hj'⟩ := by
      simpa only [f, dif_pos hi', dif_pos hj'] using hij
    exact Fin.ext (congrArg (fun k : Fin labels.length => k.val) (hdistinct.injective_get hget))
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard
    (s := s) (f := f) (subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), ?_⟩
  intro k
  have hk : (Fin.castLE hlen k).val < labels.length := k.isLt
  change (g (Fin.castLE hlen k) : V) = labels.get k
  calc
    _ = f (Fin.castLE hlen k) := hg _ (mem_filter.mpr ⟨mem_univ _, hk⟩)
    _ = labels.get k := dif_pos hk

/-- Full neighbor lists at labels 0 and 1, including the backward edge in kind 1. -/
private def neighborRows (kind : Fin 4) : Finset (Fin 6) × Finset (Fin 6) :=
  ![(∅, {2, 3}), ({1}, {0}), ({2}, {2}), ({2}, {3})] kind

private theorem firstPairs_rows :
    ∀ (kind : Fin 4) (j : Fin 6),
      ((0, j) ∈ firstPairs kind ↔ j ∈ (neighborRows kind).1) ∧
      (1 < j → ((1, j) ∈ firstPairs kind ↔ j ∈ (neighborRows kind).2)) := by
  decide +kernel

private theorem first_rows_of_neighbors (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : Fin 6 ≃ V) (kind : Fin 4)
    (h0 : H.neighborFinset (e 0) = (neighborRows kind).1.map e.toEmbedding)
    (h1 : H.neighborFinset (e 1) = (neighborRows kind).2.map e.toEmbedding) :
    ∀ i j : Fin 6, i < j → i < 2 →
      (H.Adj (e i) (e j) ↔ (i, j) ∈ firstPairs kind) := by
  intro i j hij hi
  have hi01 : i = 0 ∨ i = 1 := by omega
  rcases hi01 with rfl | rfl
  · rw [← H.mem_neighborFinset (e 0) (e j), h0]
    exact (Finset.mem_map' e.toEmbedding).trans (firstPairs_rows kind j).1.symm
  · rw [← H.mem_neighborFinset (e 1) (e j), h1]
    exact (Finset.mem_map' e.toEmbedding).trans ((firstPairs_rows kind j).2 hij).symm

theorem exists_normalized_complement : ComplementNormalization.{u} := by
  unfold ComplementNormalization
  intro V _ _ H _ hV hprofile
  unfold ComplementDegreeProfile at hprofile
  rcases hprofile with ⟨h, hh, hrest⟩ | ⟨p, q, hpq, hp, hq, hrest⟩
  · haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, hah⟩ := exists_ne h
    have hIso := (H.degree_eq_zero h).mp hh
    have hcard : (H.neighborFinset a).card = 2 :=
      (H.card_neighborFinset_eq_degree a).trans (hrest a hah)
    obtain ⟨b, c, hbc, hNa⟩ := card_eq_two.mp hcard
    have hab : H.Adj a b := (H.mem_neighborFinset a b).mp (by simp [hNa])
    have hac : H.Adj a c := (H.mem_neighborFinset a c).mp (by simp [hNa])
    have hhb : h ≠ b := by
      rintro rfl
      exact hIso a hab.symm
    have hhc : h ≠ c := by
      rintro rfl
      exact hIso a hac.symm
    obtain ⟨e, he⟩ := extend_labels hV [h, a, b, c]
      (by simp [List.nodup_cons, hah.symm, hhb, hhc, hab.ne, hac.ne, hbc]) (by simp)
    have he0 : e 0 = h := he 0
    have he1 : e 1 = a := he 1
    have he2 : e 2 = b := he 2
    have he3 : e 3 = c := he 3
    refine ⟨e, 0, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i
        rw [he0]
        simpa [expectedDegree] using hh
      · have hne : e i ≠ h := fun hEq => hi (e.injective (hEq.trans he0.symm))
        simpa [expectedDegree, hi] using hrest (e i) hne
    · apply first_rows_of_neighbors H e 0
      · change H.neighborFinset (e 0) = (∅ : Finset (Fin 6)).map e.toEmbedding
        rw [he0, map_empty]
        exact (H.neighborFinset_eq_empty h).mpr hIso
      · change H.neighborFinset (e 1) = ({2, 3} : Finset (Fin 6)).map e.toEmbedding
        rw [he1]
        simpa only [map_insert, map_singleton, Equiv.coe_toEmbedding, he2, he3] using hNa
  · have hpCard : (H.neighborFinset p).card = 1 :=
      (H.card_neighborFinset_eq_degree p).trans hp
    have hqCard : (H.neighborFinset q).card = 1 :=
      (H.card_neighborFinset_eq_degree q).trans hq
    obtain ⟨x, hNp⟩ := card_eq_one.mp hpCard
    obtain ⟨y, hNq⟩ := card_eq_one.mp hqCard
    have hpAdj (z : V) : H.Adj p z ↔ z = x := by
      rw [← H.mem_neighborFinset p z, hNp, mem_singleton]
    have hqAdj (z : V) : H.Adj q z ↔ z = y := by
      rw [← H.mem_neighborFinset q z, hNq, mem_singleton]
    have hdegree (e : Fin 6 ≃ V) (he0 : e 0 = p) (he1 : e 1 = q)
        (kind : Fin 4) (hk : kind ≠ 0) (i : Fin 6) :
        H.degree (e i) = expectedDegree kind i := by
      by_cases hi : i < 2
      · have hi01 : i = 0 ∨ i = 1 := by omega
        rcases hi01 with rfl | rfl
        · rw [expectedDegree, if_neg hk, if_pos hi, he0, hp]
        · rw [expectedDegree, if_neg hk, if_pos hi, he1, hq]
      · have hi0 : i ≠ 0 := by omega
        have hi1 : i ≠ 1 := by omega
        rw [expectedDegree, if_neg hk, if_neg hi]
        exact hrest (e i) (fun hEq => hi0 (e.injective (hEq.trans he0.symm)))
          (fun hEq => hi1 (e.injective (hEq.trans he1.symm)))
    by_cases hxq : x = q
    · have hyp : y = p := ((hqAdj p).mp ((hpAdj q).mpr hxq.symm).symm).symm
      obtain ⟨e, he⟩ := extend_labels hV [p, q] (by simp [List.nodup_cons, hpq]) (by simp)
      have he0 : e 0 = p := he 0
      have he1 : e 1 = q := he 1
      refine ⟨e, 1, hdegree e he0 he1 1 (by omega), ?_⟩
      apply first_rows_of_neighbors H e 1
      · change H.neighborFinset (e 0) = ({1} : Finset (Fin 6)).map e.toEmbedding
        rw [he0]
        simpa only [map_singleton, Equiv.coe_toEmbedding, he1, hxq] using hNp
      · change H.neighborFinset (e 1) = ({0} : Finset (Fin 6)).map e.toEmbedding
        rw [he1]
        simpa only [map_singleton, Equiv.coe_toEmbedding, he0, hyp] using hNq
    · have hqx : q ≠ x := Ne.symm hxq
      have hpx : p ≠ x := ((hpAdj x).mpr rfl).ne
      have hqy : q ≠ y := ((hqAdj y).mpr rfl).ne
      have hpy : p ≠ y := by
        intro hEq
        exact hxq ((hpAdj q).mp ((hqAdj p).mpr hEq).symm).symm
      by_cases hxy : x = y
      · subst y
        obtain ⟨e, he⟩ := extend_labels hV [p, q, x]
          (by simp [List.nodup_cons, hpq, hpx, hqx]) (by simp)
        have he0 : e 0 = p := he 0
        have he1 : e 1 = q := he 1
        have he2 : e 2 = x := he 2
        refine ⟨e, 2, hdegree e he0 he1 2 (by omega), ?_⟩
        apply first_rows_of_neighbors H e 2
        · change H.neighborFinset (e 0) = ({2} : Finset (Fin 6)).map e.toEmbedding
          rw [he0]
          simpa only [map_singleton, Equiv.coe_toEmbedding, he2] using hNp
        · change H.neighborFinset (e 1) = ({2} : Finset (Fin 6)).map e.toEmbedding
          rw [he1]
          simpa only [map_singleton, Equiv.coe_toEmbedding, he2] using hNq
      · obtain ⟨e, he⟩ := extend_labels hV [p, q, x, y]
          (by simp [List.nodup_cons, hpq, hpx, hpy, hqx, hqy, hxy]) (by simp)
        have he0 : e 0 = p := he 0
        have he1 : e 1 = q := he 1
        have he2 : e 2 = x := he 2
        have he3 : e 3 = y := he 3
        refine ⟨e, 3, hdegree e he0 he1 3 (by omega), ?_⟩
        apply first_rows_of_neighbors H e 3
        · change H.neighborFinset (e 0) = ({2} : Finset (Fin 6)).map e.toEmbedding
          rw [he0]
          simpa only [map_singleton, Equiv.coe_toEmbedding, he2] using hNp
        · change H.neighborFinset (e 1) = ({3} : Finset (Fin 6)).map e.toEmbedding
          rw [he1]
          simpa only [map_singleton, Equiv.coe_toEmbedding, he3] using hNq

private theorem complement_shape_of_normalization (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : Fin 6 ≃ V) (kind : Fin 4)
    (hdegree : ∀ i : Fin 6, H.degree (e i) = expectedDegree kind i)
    (hfirst : ∀ i j : Fin 6, i < j → i < 2 →
      (H.Adj (e i) (e j) ↔ (i, j) ∈ firstPairs kind)) :
    Nonempty (template kind ≃g H) := by
  let tail := remainingPairs.filter fun p => H.Adj (e p.1) (e p.2)
  let E := firstPairs kind ∪ tail
  have upperOnly (i j : Fin 6) (h : (i, j) ∈ E) : i < j := by
    rcases mem_union.mp h with h | h
    · exact (upper_pairs.1 kind i j h).2
    · exact ((upper_pairs.2 i j).mp (mem_filter.mp h).1).2
  have memUpper (i j : Fin 6) (hij : i < j) :
      (i, j) ∈ E ↔ H.Adj (e i) (e j) := by
    by_cases hi : i < 2
    · have htail : (i, j) ∉ tail := fun hm =>
        (not_le_of_gt hi) ((upper_pairs.2 i j).mp (mem_filter.mp hm).1).1
      simpa only [E, mem_union, htail, or_false] using (hfirst i j hij hi).symm
    · have hpref : (i, j) ∉ firstPairs kind := fun hm =>
        hi (upper_pairs.1 kind i j hm).1
      have htail := (upper_pairs.2 i j).mpr ⟨le_of_not_gt hi, hij⟩
      simp only [E, mem_union, hpref, false_or, tail, mem_filter, htail, true_and]
  have adjUpper (i j : Fin 6) (hij : i < j) :
      (graphOfPairs E).Adj i j ↔ H.Adj (e i) (e j) := by
    have hrev : (j, i) ∉ E := fun hm => (not_lt_of_ge hij.le) (upperOnly j i hm)
    have hne : i ≠ j := hij.ne
    rw [graphOfPairs, SimpleGraph.fromRel_adj]
    change (i ≠ j ∧ ((i, j) ∈ E ∨ (j, i) ∈ E)) ↔ H.Adj (e i) (e j)
    rw [or_iff_left hrev, and_iff_right hne]
    exact memUpper i j hij
  let phi : graphOfPairs E ≃g H := {
    toEquiv := e
    map_rel_iff' := by
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (adjUpper i j hij).symm
      · simp
      · rw [H.adj_comm (e i) (e j), (graphOfPairs E).adj_comm i j]
        exact (adjUpper j i hji).symm }
  have hdeg (i : Fin 6) : (graphOfPairs E).degree i = expectedDegree kind i :=
    (phi.degree_eq i).symm.trans (hdegree i)
  obtain ⟨choice, hb, hmap⟩ :=
    normalized_complement_table kind tail (mem_powerset.mpr (filter_subset _ _)) hdeg
  let p := Equiv.ofBijective (place kind choice) hb
  exact ⟨{
    toEquiv := p.trans e
    map_rel_iff' := fun {i j} =>
      (phi.map_adj_iff (v := place kind choice i) (w := place kind choice j)).trans (hmap i j)
  }⟩

private def complementIso {W : Type v} {G : SimpleGraph V} {T : SimpleGraph W}
    (e : T ≃g G) : Tᶜ ≃g Gᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro i j
    change Gᶜ.Adj (e i) (e j) ↔ Tᶜ.Adj i j
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj, e.map_adj_iff]
    change (e.toEquiv i ≠ e.toEquiv j ∧ ¬ T.Adj i j) ↔ (i ≠ j ∧ ¬ T.Adj i j)
    simp only [Ne, e.toEquiv.apply_eq_iff_eq]

private theorem square_of_iso {W : Type v} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {T : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel T.Adj] (e : T ≃g G) (h : SquareCompletion G) :
    SquareCompletion T := by
  intro a v c hav hac hvc ha hv
  obtain ⟨d, hda, hvd, hcd⟩ := h (e.map_adj_iff.mpr hav) (e.map_adj_iff.mpr hac)
    (e.injective.ne hvc) ((e.degree_eq a).trans ha) ((e.degree_eq v).trans hv)
  refine ⟨e.symm d, ?_, e.map_adj_iff.mp ?_, e.map_adj_iff.mp ?_⟩
  · intro he
    exact hda (by simpa using congrArg e he)
  · simpa using hvd
  · simpa using hcd

/-- In the complement of path6, N(4) = {0,1,2} and N(0) = {2,3,4,5}.
Vertices 2 and 4 are cubic, and N(4) ∩ N(0) = {2}. -/
private theorem not_square_path6 : ¬ SquareCompletion (graphOfPairs path6)ᶜ := by
  intro h
  obtain ⟨d, hd⟩ := h (a := 2) (v := 4) (c := 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have no_d : ∀ d : Fin 6, ¬ (d ≠ 2 ∧
      (graphOfPairs path6)ᶜ.Adj 4 d ∧ (graphOfPairs path6)ᶜ.Adj 0 d) := by
    decide +kernel
  exact no_d d hd

/-- In the complement of edgeAndC4, N(4) = {0,1,2} and N(0) = {2,3,4,5}.
Vertices 2 and 4 are again cubic. -/
private theorem not_square_edgeAndC4 : ¬ SquareCompletion (graphOfPairs edgeAndC4)ᶜ := by
  intro h
  obtain ⟨d, hd⟩ := h (a := 2) (v := 4) (c := 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have no_d : ∀ d : Fin 6, ¬ (d ≠ 2 ∧
      (graphOfPairs edgeAndC4)ᶜ.Adj 4 d ∧ (graphOfPairs edgeAndC4)ᶜ.Adj 0 d) := by
    decide +kernel
  exact no_d d hd

/-- Apply the complement classification before imposing the square condition.
The square law excludes the two remaining complements with cubic-edge obstructions. -/
theorem ten_edges_on_six_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 6) (hE : G.edgeFinset.card = 10)
    (hmin : ∀ a, 3 ≤ G.degree a) (hsquare : SquareCompletion G) :
    Nonempty (wheel ≃g G) ∨ Nonempty (k33Extra ≃g G) := by
  obtain ⟨e, kind, hdegree, hfirst⟩ := exists_normalized_complement Gᶜ hV (complement_degree_profile G hV hE hmin)
  obtain ⟨phi⟩ := complement_shape_of_normalization Gᶜ e kind hdegree hfirst
  have psi : (template kind)ᶜ ≃g G := by
    simpa only [compl_compl] using complementIso phi
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by
    fin_cases kind <;> decide +kernel
  rcases hk with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨psi⟩
  · exact (not_square_edgeAndC4 (square_of_iso psi hsquare)).elim
  · exact Or.inr ⟨psi⟩
  · exact (not_square_path6 (square_of_iso psi hsquare)).elim

/-- For distinct labels, the displayed adjacency is equivalent to membership
of the pair of actual coordinates in F by the definition of maskGraph. -/
def Relabels (T : SimpleGraph (Fin 6)) (F : Finset (Finset (Fin 9))) : Prop :=
  ∃ e : Fin 6 ≃ activeAxes F, ∀ i j : Fin 6,
    (maskGraph F).Adj (e i) (e j) ↔ T.Adj i j

open Classical in
theorem distance_two_ten_masks_on_six_axes
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 6)
    (hmask : (minimumDisplacements C D b 2).card = 10) :
    let F := minimumDisplacements C D b 2
    Relabels wheel F ∨ Relabels k33Extra F := by
  let F := minimumDisplacements C D b 2
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hV : Fintype.card (activeAxes F) = 6 := (Fintype.card_coe _).trans haxes
  have hE : (maskGraph F).edgeFinset.card = 10 := (card_edges F hsize).trans hmask
  obtain ⟨hmin, hsquare⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  have hsq : SquareCompletion (maskGraph F) := by
    intro a v c
    exact hsquare
  rcases ten_edges_on_six_vertices (maskGraph F) hV hE hmin hsq with hw | hk
  · obtain ⟨e⟩ := hw
    exact Or.inl ⟨e.toEquiv, fun _ _ => e.map_adj_iff⟩
  · obtain ⟨e⟩ := hk
    exact Or.inr ⟨e.toEquiv, fun _ _ => e.map_adj_iff⟩

open Classical in
/-- Ten masks with at least three partners per active axis occupy six axes
or form the entire family of pairs on five axes. -/
theorem six_axes_or_complete_five (F : Finset (Finset (Fin 9)))
    (hmask : F.card = 10) (hsize : ∀ T ∈ F, T.card = 2)
    (hmin : ∀ a, 3 ≤ (maskGraph F).degree a) :
    (activeAxes F).card = 6 ∨
      ((activeAxes F).card = 5 ∧ F = (activeAxes F).powersetCard 2) := by
  let A := activeAxes F
  let G := maskGraph F
  have hsub : F ⊆ A.powersetCard 2 := fun T hT =>
    mem_powersetCard.mpr ⟨fun i hi => mem_axes.mpr ⟨T, hT, hi⟩, hsize T hT⟩
  have hcap := card_le_card hsub
  rw [card_powersetCard, hmask] at hcap
  have hlower : 5 ≤ A.card := by
    by_contra! h
    have hmono := Nat.choose_le_choose 2 (show A.card ≤ 4 by omega)
    have hfour : Nat.choose 4 2 = 6 := by decide
    omega
  have hupper : A.card ≤ 6 := by
    have hsum : (∑ a : A, 3) ≤ ∑ a : A, G.degree a :=
      sum_le_sum fun a _ => hmin a
    rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul,
      G.sum_degrees_eq_twice_card_edges, card_edges F hsize, hmask] at hsum
    change A.card * 3 ≤ 2 * 10 at hsum
    omega
  by_cases hsix : A.card = 6
  · exact Or.inl hsix
  have hfive : A.card = 5 := by omega
  refine Or.inr ⟨hfive, eq_of_subset_of_card_le hsub ?_⟩
  rw [card_powersetCard, hfive, hmask]
  decide

#print axioms distance_two_ten_masks_on_six_axes

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph
