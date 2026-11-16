/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.claim
   digest: A finite bipartite degree-two/three graph with independent degree-two vertices and girth at least eight cannot have its degree-three vertices as an induced spanning C16. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Batteries.Tactic.OpenPrivate

/-! The induced high C16 branch is impossible in every finite bipartite
degree-two/three graph of girth at least eight with independent low vertices.
The low matching and its restrictions are derived from the actual graph.
The displacement-word contradiction uses finite kernel computation.
The external f2(Q9) problem remains open. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixteenCycleExclusion

open SimpleGraph GirthSliceCounting

attribute [local instance] Classical.propDecidable

private def evenIndex (i : Fin 8) : Fin 16 :=
  ⟨2 * i.val, by omega⟩

private def oddIndex (i : Fin 8) : Fin 16 := evenIndex i + 1

private def displacement (a : Fin 3) : Fin 16 :=
  ⟨6 + 2 * a.val, by omega⟩

private def jump (i : Fin 8) (a : Fin 3) : Fin 8 :=
  i + 3 + (⟨a.val, by omega⟩ : Fin 8)

private abbrev twoStepAllowed (a b : Fin 3) : Prop :=
  (a = 0 ∧ (b = 0 ∨ b = 2)) ∨
  (a = 1 ∧ b = 0) ∨
  (a = 2 ∧ (b = 1 ∨ b = 2))

private theorem evenIndex_injective : Function.Injective evenIndex := by
  decide +kernel

private theorem index_identities :
    (∀ i : Fin 8, oddIndex i + 1 = evenIndex (i + 1)) ∧
    (∀ (i : Fin 8) (a : Fin 3),
      evenIndex (jump i a) = evenIndex i + displacement a) := by
  decide +kernel

/- The two adjacent edges i--(i+1)--(i+2) impose this relation on the
   two even displacement labels, after quantifying over the middle label. -/
private theorem two_step_constraint :
    ∀ (i : Fin 8) (a b c : Fin 3),
      (oddIndex i + displacement c ≠ (evenIndex i + displacement a) + 1 ∧
        oddIndex i + displacement c ≠ (evenIndex i + displacement a) + 15) →
      (evenIndex (i + 1) + displacement b ≠ (oddIndex i + displacement c) + 1 ∧
        evenIndex (i + 1) + displacement b ≠ (oddIndex i + displacement c) + 15) →
      twoStepAllowed a b := by
  intro i a b c
  fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

/- Only 3^8 assignments.  Involutivity is checked before the local
   transition condition, so only the seven matching words reach it. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The kernel checks all 6561 displacement words in this declaration only.
private theorem even_words_excluded :
    ∀ d : Fin 8 → Fin 3,
      (∀ i, jump (jump i (d i)) (d (jump i (d i))) = i) →
      (∀ i, twoStepAllowed (d i) (d (i + 1))) → False := by
  decide +kernel

/-- No involution on C16 can have only displacements 6,8,10 while the
images of adjacent vertices are never adjacent.  `+15` denotes `-1`. -/
private theorem impossible
    (p : Fin 16 → Fin 16)
    (hstep : ∀ i, p i = i + 6 ∨ p i = i + 8 ∨ p i = i + 10)
    (hinv : ∀ i, p (p i) = i)
    (hsep : ∀ i, p (i + 1) ≠ p i + 1 ∧ p (i + 1) ≠ p i + 15) :
    False := by
  have hdisplacement (i : Fin 16) :
      ∃ a : Fin 3, p i = i + displacement a := by
    rcases hstep i with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  choose d hd using fun i : Fin 8 => hdisplacement (evenIndex i)
  have heven (i : Fin 8) :
      p (evenIndex i) = evenIndex (jump i (d i)) := by
    rw [hd i, index_identities.2]
  have hdInv (i : Fin 8) :
      jump (jump i (d i)) (d (jump i (d i))) = i := by
    apply evenIndex_injective
    calc
      evenIndex (jump (jump i (d i)) (d (jump i (d i)))) =
          p (evenIndex (jump i (d i))) := (heven _).symm
      _ = p (p (evenIndex i)) := by rw [heven i]
      _ = evenIndex i := hinv _
  have hdLocal (i : Fin 8) : twoStepAllowed (d i) (d (i + 1)) := by
    obtain ⟨c, hc⟩ := hdisplacement (oddIndex i)
    apply two_step_constraint i (d i) (d (i + 1)) c
    · have hs := hsep (evenIndex i)
      change p (oddIndex i) ≠ p (evenIndex i) + 1 ∧
        p (oddIndex i) ≠ p (evenIndex i) + 15 at hs
      rw [hc, hd i] at hs
      exact hs
    · have hs := hsep (oddIndex i)
      rw [index_identities.1, hd (i + 1), hc] at hs
      exact hs
  exact even_words_excluded d hdInv hdLocal

/-- Equivalent statement using ordinary subtraction in `Fin 16`. -/
private theorem impossible_sub
    (p : Fin 16 → Fin 16)
    (hstep : ∀ i, p i = i + 6 ∨ p i = i + 8 ∨ p i = i + 10)
    (hinv : ∀ i, p (p i) = i)
    (hsep : ∀ i, p (i + 1) ≠ p i + 1 ∧ p (i + 1) ≠ p i - 1) :
    False := by
  have hminus : ∀ a : Fin 16, a - 1 = a + 15 := by decide +kernel
  apply impossible p hstep hinv
  intro i
  simpa only [hminus] using hsep i



open private lowPair low_pair_excluded_by_common_high
  low_pair_excluded_by_short_paths from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private unique_low_partner from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners

private theorem same_parity_short_path_witness :
    ∀ i j : Fin 16, i ≠ j → i.val % 2 = j.val % 2 →
      j ≠ i + 6 → j ≠ i + 8 → j ≠ i + 10 →
      (∃ k : Fin 16, (cycleGraph 16).Adj i k ∧ (cycleGraph 16).Adj j k) ∨
      ∃ p m q : Fin 16, (cycleGraph 16).Adj i p ∧ (cycleGraph 16).Adj p m ∧
        (cycleGraph 16).Adj m q ∧ (cycleGraph 16).Adj j q ∧
        i ≠ m ∧ p ≠ q := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem opposite_side_low_pair_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {a b : V} (ha : a ∈ L) (hb : b ∈ R) : ¬ lowPair G a b := by
  rintro ⟨w, _hw, haw, hbw⟩
  have hwR := hpart.mem_of_mem_adj ha haw
  have hbL := hpart.symm.mem_of_mem_adj hwR hbw.symm
  exact Set.disjoint_left.mp hpart.disjoint hbL hb

/-- The C16 counterpart of the existing C12 short-path exclusion. -/
private theorem short_displacement_low_pair_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 16 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 16).Adj i j → G.Adj (c i) (c j))
    {i j : Fin 16} (hij : i ≠ j) (hpar : i.val % 2 = j.val % 2)
    (h6 : j ≠ i + 6) (h8 : j ≠ i + 8) (h10 : j ≠ i + 10)
    (hiR : c i ∈ R) : ¬ lowPair G (c i) (c j) := by
  have hcij : c i ≠ c j := fun he => hij (hc he)
  rcases same_parity_short_path_witness i j hij hpar h6 h8 h10 with
    ⟨k, hik, hjk⟩ | ⟨p, m, q, hip, hpm, hmq, hjq, him, hpq⟩
  · exact low_pair_excluded_by_common_high hpart hg hiR (hc3 k)
      (hcycle i k hik) (hcycle j k hjk) hcij
  · exact low_pair_excluded_by_short_paths hpart hg hiR (hc3 p) (hc3 q)
      (hcycle i p hip) (hcycle p m hpm) (hcycle m q hmq) (hcycle j q hjq)
      hcij (fun he => him (hc he)) (fun he => hpq (hc he))

/-- With an oriented bipartition, actual distinct low-paired C16 vertices
have precisely one of the three remaining even displacements. -/
private theorem low_pair_displacement_of_orientation
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 16 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 16).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    {i j : Fin 16} (hij : i ≠ j) (hp : lowPair G (c i) (c j)) :
    j = i + 6 ∨ j = i + 8 ∨ j = i + 10 := by
  by_contra hs
  have h6 : j ≠ i + 6 := fun he => hs (Or.inl he)
  have h8 : j ≠ i + 8 := fun he => hs (Or.inr (Or.inl he))
  have h10 : j ≠ i + 10 := fun he => hs (Or.inr (Or.inr he))
  by_cases hpar : i.val % 2 = j.val % 2
  · by_cases hi0 : i.val % 2 = 0
    · exact short_displacement_low_pair_excluded hpart.symm hg c hc hc3 hcycle
        hij hpar h6 h8 h10 (hcL i hi0) hp
    · have hi1 : i.val % 2 = 1 := by omega
      exact short_displacement_low_pair_excluded hpart hg c hc hc3 hcycle
        hij hpar h6 h8 h10 (hcR i hi1) hp
  · by_cases hi0 : i.val % 2 = 0
    · have hj1 : j.val % 2 = 1 := by omega
      exact opposite_side_low_pair_excluded hpart (hcL i hi0) (hcR j hj1) hp
    · have hi1 : i.val % 2 = 1 := by omega
      have hj0 : j.val % 2 = 0 := by omega
      exact opposite_side_low_pair_excluded hpart.symm (hcR i hi1) (hcL j hj0) hp

private theorem cycle_parity_membership
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (c : Fin 16 → V)
    (hcycle : ∀ i j, (cycleGraph 16).Adj i j → G.Adj (c i) (c j))
    (h0 : c 0 ∈ L) :
    (∀ i, i.val % 2 = 0 → c i ∈ L) ∧
      (∀ i, i.val % 2 = 1 → c i ∈ R) := by
  have h1 := hpart.mem_of_mem_adj h0 (hcycle 0 1 (by decide +kernel))
  have h2 := hpart.symm.mem_of_mem_adj h1 (hcycle 1 2 (by decide +kernel))
  have h3 := hpart.mem_of_mem_adj h2 (hcycle 2 3 (by decide +kernel))
  have h4 := hpart.symm.mem_of_mem_adj h3 (hcycle 3 4 (by decide +kernel))
  have h5 := hpart.mem_of_mem_adj h4 (hcycle 4 5 (by decide +kernel))
  have h6 := hpart.symm.mem_of_mem_adj h5 (hcycle 5 6 (by decide +kernel))
  have h7 := hpart.mem_of_mem_adj h6 (hcycle 6 7 (by decide +kernel))
  have h8 := hpart.symm.mem_of_mem_adj h7 (hcycle 7 8 (by decide +kernel))
  have h9 := hpart.mem_of_mem_adj h8 (hcycle 8 9 (by decide +kernel))
  have h10 := hpart.symm.mem_of_mem_adj h9 (hcycle 9 10 (by decide +kernel))
  have h11 := hpart.mem_of_mem_adj h10 (hcycle 10 11 (by decide +kernel))
  have h12 := hpart.symm.mem_of_mem_adj h11 (hcycle 11 12 (by decide +kernel))
  have h13 := hpart.mem_of_mem_adj h12 (hcycle 12 13 (by decide +kernel))
  have h14 := hpart.symm.mem_of_mem_adj h13 (hcycle 13 14 (by decide +kernel))
  have h15 := hpart.mem_of_mem_adj h14 (hcycle 14 15 (by decide +kernel))
  constructor
  · intro i hi
    fin_cases i <;>
      first
      | exact h0
      | exact h2
      | exact h4
      | exact h6
      | exact h8
      | exact h10
      | exact h12
      | exact h14
      | norm_num at hi
  · intro i hi
    fin_cases i <;>
      first
      | exact h1
      | exact h3
      | exact h5
      | exact h7
      | exact h9
      | exact h11
      | exact h13
      | exact h15
      | norm_num at hi

/-- Orientation-free version: the bipartition orientation is derived from
the actual first cycle edge, rather than supplied as a classification premise. -/
private theorem low_pair_displacement
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 16 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 16).Adj i j → G.Adj (c i) (c j))
    {i j : Fin 16} (hij : i ≠ j) (hp : lowPair G (c i) (c j)) :
    j = i + 6 ∨ j = i + 8 ∨ j = i + 10 := by
  rcases hpart.mem_of_adj (hcycle 0 1 (by decide +kernel)) with hs | hs
  · obtain ⟨hcL, hcR⟩ := cycle_parity_membership hpart c hcycle hs.1
    exact low_pair_displacement_of_orientation hpart hg c hc hc3 hcycle hcL hcR hij hp
  · obtain ⟨hcR, hcL⟩ := cycle_parity_membership hpart.symm c hcycle hs.1
    exact low_pair_displacement_of_orientation hpart.symm hg c hc hc3 hcycle hcR hcL hij hp

private theorem cycle_adj_iff_successor_predecessor :
    ∀ i j : Fin 16,
      (cycleGraph 16).Adj i j ↔ j = i + 1 ∨ j = i + 15 := by
  decide +kernel

private theorem cycle_successor_ne_predecessor :
    ∀ i : Fin 16, i + 1 ≠ i + 15 := by
  decide +kernel

private theorem high_neighbor_set
    (c : Fin 16 → V)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hhigh : ∀ i j, G.Adj (c i) (c j) ↔ (cycleGraph 16).Adj i j)
    (hcover : ∀ v, G.degree v = 3 → ∃ i, c i = v) :
    ∀ i, degreeThree G (G.neighborFinset (c i)) =
      {c (i + 1), c (i + 15)} := by
  intro i
  ext v
  constructor
  · intro hv
    have hvN := (Finset.mem_filter.mp hv).1
    have hv3 := (Finset.mem_filter.mp hv).2
    obtain ⟨j, hj⟩ := hcover v hv3
    have hvN' : c j ∈ G.neighborFinset (c i) := by simpa [hj] using hvN
    have hadj : G.Adj (c i) (c j) :=
      (G.mem_neighborFinset _ _).mp hvN'
    have hcy := (hhigh i j).mp hadj
    rw [cycle_adj_iff_successor_predecessor] at hcy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcy with hcy | hcy
    · left
      rw [← hj, hcy]
    · right
      rw [← hj, hcy]
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · subst v
      apply Finset.mem_filter.mpr
      constructor
      · apply (G.mem_neighborFinset _ _).mpr
        exact (hhigh i (i + 1)).mpr
          ((cycle_adj_iff_successor_predecessor i (i + 1)).2 (Or.inl rfl))
      · exact hc3 _
    · subst v
      apply Finset.mem_filter.mpr
      constructor
      · apply (G.mem_neighborFinset _ _).mpr
        exact (hhigh i (i + 15)).mpr
          ((cycle_adj_iff_successor_predecessor i (i + 15)).2 (Or.inr rfl))
      · exact hc3 _

private theorem adjacent_partner_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 16 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 16).Adj i j → G.Adj (c i) (c j))
    (p : Fin 16 → Fin 16)
    (hne : ∀ i, p i ≠ i)
    (hlow : ∀ i, lowPair G (c i) (c (p i)))
    {i : Fin 16} (hi : c i ∈ L)
    (hadj : (cycleGraph 16).Adj (p i) (p (i + 1))) : False := by
  rcases hlow i with ⟨w, hw2, hiw, hpiw⟩
  rcases hlow (i + 1) with ⟨w', hw'2, hi1w, hp1w⟩
  have hfirst : G.Adj (c i) (c (i + 1)) :=
    hcycle i (i + 1) ((cycle_adj_iff_successor_predecessor _ _).2 (Or.inl rfl))
  have hlast : G.Adj (c (p i)) (c (p (i + 1))) := hcycle _ _ hadj
  have h02 : c i ≠ c (p i) := by
    intro he
    apply hne i
    exact (hc he).symm
  have h13 : w ≠ c (p (i + 1)) := by
    intro he
    rw [he, hc3] at hw2
    omega
  have h02' : c i ≠ w' := by
    intro he
    rw [← he, hc3] at hw'2
    omega
  have h13' : c (i + 1) ≠ c (p (i + 1)) := by
    intro he
    apply hne (i + 1)
    exact (hc he).symm
  obtain ⟨_, hmid, _, _⟩ :=
    three_walk_endpoint_injective hpart hg hi hi
      hiw hpiw.symm hlast hfirst hi1w hp1w.symm h02 h13 h02' h13'
      ⟨rfl, rfl⟩
  have hmid' : w = c (i + 1) := hmid
  rw [hmid', hc3] at hw2
  omega

private theorem no_graph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlowdeg : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 16 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hhigh : ∀ i j, G.Adj (c i) (c j) ↔ (cycleGraph 16).Adj i j)
    (hcover : ∀ v, G.degree v = 3 → ∃ i, c i = v) : False := by
  have hneighbors := high_neighbor_set (G := G) c hc3 hhigh hcover
  have hpartner : ∀ i : Fin 16, ∃ w j,
      G.degree w = 2 ∧ c i ≠ c j ∧
      G.Adj (c i) w ∧ G.Adj (c j) w ∧
      (∀ z, c i ≠ z → lowPair G (c i) z → z = c j) := by
    intro i
    obtain ⟨w, y, hw, hy, hiy, hiw, hyw, _, huniq, _⟩ :=
      unique_low_partner hdeg hlowdeg (hc3 i) (by
        rw [hneighbors i]
        have hneigh : c (i + 1) ≠ c (i + 15) :=
          fun he => (cycle_successor_ne_predecessor i) (hc he)
        simp [hneigh])
    obtain ⟨j, hj⟩ := hcover y hy
    subst y
    exact ⟨w, j, hw, hiy, hiw, hyw, huniq⟩
  choose w p hw2 hne hxi hpi huniq using hpartner
  have hlow : ∀ i, lowPair G (c i) (c (p i)) := by
    intro i
    exact ⟨w i, hw2 i, hxi i, hpi i⟩
  have hpne : ∀ i, p i ≠ i := by
    intro i he
    apply hne i
    rw [he]
  have hinv : ∀ i, p (p i) = i := by
    intro i
    have hneq : c (p i) ≠ c i := by
      intro he
      apply hpne i
      exact hc he
    have hpair : lowPair G (c (p i)) (c i) := by
      rcases hlow i with ⟨l, hl, hil, hpil⟩
      exact ⟨l, hl, hpil, hil⟩
    have heq : c i = c (p (p i)) := huniq (p i) (c i) hneq hpair
    exact (hc heq).symm
  have hcycle : ∀ a b, (cycleGraph 16).Adj a b → G.Adj (c a) (c b) :=
    fun a b hab => (hhigh a b).mpr hab
  have hstep : ∀ i, p i = i + 6 ∨ p i = i + 8 ∨ p i = i + 10 := by
    intro i
    exact low_pair_displacement hpart hg c hc hc3
      hcycle (hpne i).symm (hlow i)
  have hside : ∀ i, c i ∈ L ∨ c i ∈ R := by
    intro i
    have hnext : G.Adj (c i) (c (i + 1)) :=
      hcycle i (i + 1) ((cycle_adj_iff_successor_predecessor i (i + 1)).2 (Or.inl rfl))
    rcases hpart.mem_of_adj hnext with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hsep : ∀ i, p (i + 1) ≠ p i + 1 ∧ p (i + 1) ≠ p i - 1 := by
    intro i
    constructor
    · intro he
      have hadj : (cycleGraph 16).Adj (p i) (p (i + 1)) := by
        rw [he]
        exact (cycle_adj_iff_successor_predecessor (p i) (p i + 1)).2 (Or.inl rfl)
      rcases hside i with hi | hi
      · exact adjacent_partner_excluded hpart hg c hc hc3 hcycle p hpne hlow hi hadj
      · exact adjacent_partner_excluded hpart.symm hg c hc hc3 hcycle p hpne hlow hi hadj
    · intro he
      have hadj : (cycleGraph 16).Adj (p i) (p (i + 1)) := by
        rw [he]
        have hminus : ∀ a : Fin 16, a - 1 = a + 15 := by decide +kernel
        rw [hminus]
        exact (cycle_adj_iff_successor_predecessor (p i) (p i + 15)).2 (Or.inr rfl)
      rcases hside i with hi | hi
      · exact adjacent_partner_excluded hpart hg c hc hc3 hcycle p hpne hlow hi hadj
      · exact adjacent_partner_excluded hpart.symm hg c hc hc3 hcycle p hpne hlow hi hadj
  exact impossible_sub p hstep hinv hsep

/-- An actual finite graph whose degree-three induced graph is one spanning C16. -/
def claim : Prop :=
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), ∃ L R : Finset (Fin n),
    G.IsBipartiteWith (L : Set (Fin n)) (R : Set (Fin n)) ∧
    (∀ v, G.degree v = 2 ∨ G.degree v = 3) ∧
    (∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) ∧
    (8 : ℕ∞) ≤ G.egirth ∧
    ∃ c : Fin 16 → Fin n,
      Function.Injective c ∧
      (∀ i, G.degree (c i) = 3) ∧
      (∀ i j, G.Adj (c i) (c j) ↔ (cycleGraph 16).Adj i j) ∧
      (∀ v, G.degree v = 3 → ∃ i, c i = v)

/-- The C16 high-cycle branch is impossible under the original graph conditions. -/
theorem result : ¬ claim := by
  rintro ⟨n, G, L, R, hpart, hdeg, hlowdeg, hg, c, hc, hc3, hhigh, hcover⟩
  exact no_graph hpart hdeg hlowdeg hg c hc hc3 hhigh hcover

#print axioms result

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixteenCycleExclusion
