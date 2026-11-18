/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSlicePairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSlicePairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim
   digest: Actual low-pair restrictions and complete indexed slice labels. -/


import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
import Batteries.Tactic.OpenPrivate

set_option linter.style.longLine false

open private rootThreeWeight root_three_paths_card root_weight_add_two root_paths_card_of_coverage root_weight_low root_weight_high root_three_paths_two_connectors saturation_count_equalities saturation_local_equality right_high_neighbor_rigidity saturation_endpoint_union high_root_endpoint_coverage low_vertex_high_neighbor_card asymmetric_right_type_counts asymmetric_left_connector_count neighbors_eq_pair complete_pairing c6_core_of_distinguished_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
open private High connectors core high_left high_degree connector_right connector_degree connector_card high_neighbor_mem connector_filter_eq connector_third other_high middle_unique different_middle core_degree_two core_triangle_free low_vertex_anchor compressed_core_package high_skeleton_labels lowPair low_pair_excluded_by_common_high low_pair_excluded_by_short_paths low_pair_excluded_by_fixed_pair coverage_forces_low_pair connector_high_table ne_of_high_tables high_right_connector_labels stub_neighbor_table_three third_neighbor stub_actual_saturation stub_of_two_connectors stub_singleton_ne stub_adj_of_high_table stub_low_high_ne right_labels_assembly from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

/- An internal bridge for the actual asymmetric-slice classification.
Only positive high incidences are assumed. The finite lemma checks short-path
witnesses, not a catalog of low pairings or of graphs. -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairAllowed

open SimpleGraph AsymmetricLowPairing
open private low_pair_excluded_by_common_high low_pair_excluded_by_short_paths from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

-- Right labels: z, a, b, c, d, e, f, X1, X2, Y1, Y2.
-- High labels: u, v, x1, x2, y1, y2.
private def highIncidence (i : Fin 11) (p : Fin 6) : Prop :=
  (i, p) ∈ ([(0, 0), (0, 1), (1, 0), (1, 2), (2, 0), (2, 3),
    (3, 1), (3, 4), (4, 1), (4, 5), (5, 2), (5, 4), (6, 3), (6, 5),
    (7, 2), (8, 3), (9, 4), (10, 5)] : List (Fin 11 × Fin 6))

private instance (i : Fin 11) (p : Fin 6) : Decidable (highIncidence i p) := by
  unfold highIncidence
  infer_instance

/-- The fifteen allowed unordered pairs, expressed in both orientations. -/
private def allowedPair (i j : Fin 11) : Prop :=
  (i, j) ∈ ([(1, 4), (1, 10), (2, 3), (2, 9), (3, 8), (4, 7), (5, 6),
    (5, 8), (5, 10), (6, 7), (6, 9), (7, 8), (7, 10), (8, 9), (9, 10)] :
      List (Fin 11 × Fin 11)) ∨
  (j, i) ∈ ([(1, 4), (1, 10), (2, 3), (2, 9), (3, 8), (4, 7), (5, 6),
    (5, 8), (5, 10), (6, 7), (6, 9), (7, 8), (7, 10), (8, 9), (9, 10)] :
      List (Fin 11 × Fin 11))

private instance (i j : Fin 11) : Decidable (allowedPair i j) := by
  unfold allowedPair
  infer_instance

-- The witnesses are common high neighbors or actual four-edge high paths.
-- All quantifiers are finite, and `decide +kernel` builds an ordinary kernel proof.
private theorem forbidden_pair_witness :
    ∀ i j : Fin 11, i ≠ 0 → j ≠ 0 → i ≠ j → ¬ allowedPair i j →
      (∃ p : Fin 6, highIncidence i p ∧ highIncidence j p) ∨
      ∃ (p : Fin 6) (m : Fin 11) (q : Fin 6),
        highIncidence i p ∧ highIncidence m p ∧ highIncidence m q ∧
          highIncidence j q ∧ i ≠ m ∧ p ≠ q := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

omit [DecidableEq V] in
/-- Actual adjacency and girth exclude every pair outside the fifteen-pair list.
No exhaustive neighbor table or low-pair classification is assumed. -/
private theorem actual_low_pair_allowed
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hh3 : ∀ p, G.degree (h p) = 3)
    (hz2 : G.degree (r 0) = 2)
    (hinc : ∀ i p, highIncidence i p → G.Adj (r i) (h p))
    {i j : Fin 11} (hij : i ≠ j) (hpair : lowPair G (r i) (r j)) :
    allowedPair i j := by
  classical
  have hi0 : i ≠ 0 := by
    intro hi
    obtain ⟨w, hw2, hiw, _⟩ := hpair
    exact hlow hiw (by rw [hi]; exact hz2) hw2
  have hj0 : j ≠ 0 := by
    intro hj
    obtain ⟨w, hw2, _, hjw⟩ := hpair
    exact hlow hjw (by rw [hj]; exact hz2) hw2
  have hrij : r i ≠ r j := fun he => hij (hr he)
  by_contra hbad
  rcases forbidden_pair_witness i j hi0 hj0 hij hbad with
    ⟨p, hip, hjp⟩ | ⟨p, m, q, hip, hmp, hmq, hjq, him, hpq⟩
  · exact (low_pair_excluded_by_common_high hpart hg (hrR i) (hh3 p)
      (hinc i p hip) (hinc j p hjp) hrij) hpair
  · exact (low_pair_excluded_by_short_paths hpart hg (hrR i) (hh3 p) (hh3 q)
      (hinc i p hip) (hinc m p hmp).symm (hinc m q hmq) (hinc j q hjq)
      hrij (fun he => him (hr he)) (fun he => hpq (hh he))) hpair

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairAllowed

end

/- Internal proof source for the actual asymmetric-slice refutation. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairForced

open SimpleGraph GirthSliceCounting AsymmetricLowPairing AsymmetricLowPairAllowed
open private coverage_forces_low_pair from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private high_root_endpoint_coverage from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
open private stub_actual_saturation from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem first_four_low_pairs
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hhL : ∀ p, h p ∈ L)
    (hh3 : ∀ p, G.degree (h p) = 3) (hz2 : G.degree (r 0) = 2)
    (hinc : ∀ i p, G.Adj (r i) (h p) ↔ highIncidence i p)
    (Nu : G.neighborFinset (h 0) = {r 1, r 2, r 0})
    (Nv : G.neighborFinset (h 1) = {r 3, r 4, r 0})
    (Tz : degreeThree G (G.neighborFinset (r 0)) = {h 0, h 1})
    (Ta : degreeThree G (G.neighborFinset (r 1)) = {h 0, h 2})
    (Tb : degreeThree G (G.neighborFinset (r 2)) = {h 0, h 3})
    (Tc : degreeThree G (G.neighborFinset (r 3)) = {h 1, h 4})
    (Td : degreeThree G (G.neighborFinset (r 4)) = {h 1, h 5}) :
    lowPair G (r 1) (r 10) ∧ lowPair G (r 2) (r 9) ∧
      lowPair G (r 3) (r 8) ∧ lowPair G (r 4) (r 7) := by
  classical
  have hsat := stub_actual_saturation hdeg hL hR hL2 hR2
  have cover (p : Fin 6) (i : Fin 11) :=
    high_root_endpoint_coverage hpart hdeg hlow hg hsat
      (Finset.mem_filter.mpr ⟨hhL p, hh3 p⟩) (hrR i)
  have nAdj (i : Fin 11) (p : Fin 6) (hn : ¬ highIncidence i p) :
      ¬ G.Adj (h p) (r i) := fun ha => hn ((hinc i p).mp ha.symm)
  have allowed {i j : Fin 11} (hne : i ≠ j) (hp : lowPair G (r i) (r j)) :=
    actual_low_pair_allowed hpart hlow hg r h hr hh hrR hh3 hz2
      (fun i p hi => (hinc i p).mpr hi) hne hp
  have h10 := coverage_forces_low_pair hdeg hlow Nu hz2 Ta Tb Tz
    (nAdj 10 0 (by decide +kernel)) (nAdj 10 1 (by decide +kernel))
    (nAdj 10 2 (by decide +kernel)) (nAdj 10 3 (by decide +kernel)) (cover 0 10)
  have h9 := coverage_forces_low_pair hdeg hlow Nu hz2 Ta Tb Tz
    (nAdj 9 0 (by decide +kernel)) (nAdj 9 1 (by decide +kernel))
    (nAdj 9 2 (by decide +kernel)) (nAdj 9 3 (by decide +kernel)) (cover 0 9)
  have h8 := coverage_forces_low_pair hdeg hlow Nv hz2 Tc Td
    (by simpa only [Finset.pair_comm] using Tz)
    (nAdj 8 1 (by decide +kernel)) (nAdj 8 0 (by decide +kernel))
    (nAdj 8 4 (by decide +kernel)) (nAdj 8 5 (by decide +kernel)) (cover 1 8)
  have h7 := coverage_forces_low_pair hdeg hlow Nv hz2 Tc Td
    (by simpa only [Finset.pair_comm] using Tz)
    (nAdj 7 1 (by decide +kernel)) (nAdj 7 0 (by decide +kernel))
    (nAdj 7 4 (by decide +kernel)) (nAdj 7 5 (by decide +kernel)) (cover 1 7)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases h10 with hp | hp
    · exact hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 2 10) (allowed (by decide) hp))
  · rcases h9 with hp | hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 1 9) (allowed (by decide) hp))
    · exact hp
  · rcases h8 with hp | hp
    · exact hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 4 8) (allowed (by decide) hp))
  · rcases h7 with hp | hp
    · exact False.elim ((by decide +kernel : ¬ allowedPair 3 7) (allowed (by decide) hp))
    · exact hp

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairForced

end

/- Internal pairing-completion bridge for the actual asymmetric slice.
The two-partner hypothesis is an explicit interface to the actual stub-degree
argument. The finite index checks below belong to the eventual exclusion host;
this source is not a standalone frozen classification result. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairCompletion

open SimpleGraph AsymmetricLowPairing AsymmetricLowPairAllowed
open private low_pair_excluded_by_fixed_pair from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

private theorem allowed_five :
    ∀ j : Fin 11, allowedPair 5 j → j = 6 ∨ j = 8 ∨ j = 10 := by
  decide +kernel

private theorem allowed_seven :
    ∀ j : Fin 11, allowedPair 7 j → j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by
  decide +kernel

private theorem allowed_nine :
    ∀ j : Fin 11, allowedPair 9 j → j = 2 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by
  decide +kernel

private theorem two_partners_force_second
    (P : Fin 11 → Fin 11 → Prop) (i a b : Fin 11)
    (hchoice : ∀ j, i ≠ j → P i j → j = a ∨ j = b)
    (htwo : ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧ P i j ∧ P i k) :
    P i b := by
  obtain ⟨j, k, hjk, hij, hik, hpj, hpk⟩ := htwo
  rcases hchoice j hij hpj with hj | hj
  · rcases hchoice k hik hpk with hk | hk
    · exact False.elim (hjk (hj.trans hk.symm))
    · simpa only [hk] using hpk
  · simpa only [hj] using hpj

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem low_pair_symm {a b : V} (hp : lowPair G a b) : lowPair G b a := by
  obtain ⟨w, hw2, haw, hbw⟩ := hp
  exact ⟨w, hw2, hbw, haw⟩

/-- Four forced pairings, actual girth, and the actual stub two-partner property
force the remaining three pairings. The two-partner premise is not a pairing
classification: its witnesses may be any of the eleven actual right labels. -/
private theorem actual_low_pair_completion
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hh3 : ∀ p, G.degree (h p) = 3)
    (hz2 : G.degree (r 0) = 2)
    (hinc : ∀ i p, highIncidence i p → G.Adj (r i) (h p))
    (hexists : ∀ i : Fin 11, i ≠ 0 → ∃ j, i ≠ j ∧ lowPair G (r i) (r j))
    (htwo : ∀ i ∈ ({7, 8, 9, 10} : Finset (Fin 11)),
      ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧
        lowPair G (r i) (r j) ∧ lowPair G (r i) (r k))
    (haY2 : lowPair G (r 1) (r 10))
    (hbY1 : lowPair G (r 2) (r 9))
    (hcX2 : lowPair G (r 3) (r 8))
    (hdX1 : lowPair G (r 4) (r 7)) :
    lowPair G (r 5) (r 6) ∧
      lowPair G (r 7) (r 8) ∧ lowPair G (r 9) (r 10) := by
  classical
  have hallowed {i j : Fin 11} (hij : i ≠ j)
      (hp : lowPair G (r i) (r j)) : allowedPair i j :=
    actual_low_pair_allowed hpart hlow hg r h hr hh hrR hh3 hz2 hinc hij hp
  have hfixed_excludes {a s t : Fin 11} {q : Fin 6}
      (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
      (hsq : highIncidence s q) (haq : highIncidence a q)
      (hp : lowPair G (r a) (r t)) : ¬ lowPair G (r s) (r t) := by
    exact low_pair_excluded_by_fixed_pair hpart hg (hrR s) (hh3 q)
      (fun he => has (hr he)) (fun he => hat (hr he)) (fun he => hst (hr he))
      (hinc s q hsq) (hinc a q haq) hp

  -- c-X2 and the common y1 exclude e-X2.
  have hno58 : ¬ lowPair G (r 5) (r 8) :=
    hfixed_excludes (a := 3) (q := 4)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hcX2
  -- a-Y2 and the common x1 exclude e-Y2.
  have hno510 : ¬ lowPair G (r 5) (r 10) :=
    hfixed_excludes (a := 1) (q := 2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) haY2
  have hef : lowPair G (r 5) (r 6) := by
    obtain ⟨j, h5j, hp⟩ := hexists 5 (by decide +kernel)
    rcases allowed_five j (hallowed h5j hp) with rfl | rfl | rfl
    · exact hp
    · exact False.elim (hno58 hp)
    · exact False.elim (hno510 hp)

  -- d-X1 and the common y2 exclude f-X1.
  have hno67 : ¬ lowPair G (r 6) (r 7) :=
    hfixed_excludes (a := 4) (q := 5)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdX1
  -- a-Y2 and the common x1 exclude X1-Y2.
  have hno710 : ¬ lowPair G (r 7) (r 10) :=
    hfixed_excludes (a := 1) (q := 2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) haY2
  have hXchoice (j : Fin 11) (h7j : (7 : Fin 11) ≠ j)
      (hp : lowPair G (r 7) (r j)) : j = 4 ∨ j = 8 := by
    rcases allowed_seven j (hallowed h7j hp) with hj | rfl | hj | rfl
    · exact Or.inl hj
    · exact False.elim (hno67 (low_pair_symm hp))
    · exact Or.inr hj
    · exact False.elim (hno710 hp)
  have hXX : lowPair G (r 7) (r 8) :=
    two_partners_force_second (fun i j => lowPair G (r i) (r j)) 7 4 8
      hXchoice (htwo 7 (by simp))

  -- b-Y1 and the common x2 exclude f-Y1.
  have hno69 : ¬ lowPair G (r 6) (r 9) :=
    hfixed_excludes (a := 2) (q := 3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hbY1
  -- c-X2 and the common y1 exclude Y1-X2.
  have hno98 : ¬ lowPair G (r 9) (r 8) :=
    hfixed_excludes (a := 3) (q := 4)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hcX2
  have hYchoice (j : Fin 11) (h9j : (9 : Fin 11) ≠ j)
      (hp : lowPair G (r 9) (r j)) : j = 2 ∨ j = 10 := by
    rcases allowed_nine j (hallowed h9j hp) with hj | rfl | rfl | hj
    · exact Or.inl hj
    · exact False.elim (hno69 (low_pair_symm hp))
    · exact False.elim (hno98 hp)
    · exact Or.inr hj
  have hYY : lowPair G (r 9) (r 10) :=
    two_partners_force_second (fun i j => lowPair G (r i) (r j)) 9 2 10
      hYchoice (htwo 9 (by simp))
  exact ⟨hef, hXX, hYY⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairCompletion

end

/- Internal bridge for the actual asymmetric-slice refutation. -/

/- Actual complete indexed labels for the asymmetric parameter branch. -/

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels

open SimpleGraph GirthSliceCounting AsymmetricCompressedCore AsymmetricLowPairAllowed
open private high_right_connector_labels right_labels_assembly from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private high_left high_degree connector_right connector_degree from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rows in the order z,a,b,c,d,e,f,X1,X2,Y1,Y2. -/
private def highRow (h : Fin 6 → V) : Fin 11 → Finset V :=
  ![{h 0, h 1}, {h 0, h 2}, {h 0, h 3}, {h 1, h 4},
    {h 1, h 5}, {h 2, h 4}, {h 3, h 5}, {h 2}, {h 3}, {h 4}, {h 5}]

/-- Actual vertices, complete side and high-side enumerations, and actual tables.
This is an internal proof package, not an added classification assumption. -/
private structure IndexedLabels (G : SimpleGraph V) (L R : Finset V) where
  r : Fin 11 → V
  h : Fin 6 → V
  r_injective : Function.Injective r
  h_injective : Function.Injective h
  r_mem : ∀ i, r i ∈ R
  h_mem : ∀ p, h p ∈ L
  h_degree : ∀ p, G.degree (h p) = 3
  r_zero_degree : G.degree (r 0) = 2
  r_nonzero_degree : ∀ i, i ≠ 0 → G.degree (r i) = 3
  r_complete : ∀ w ∈ R, ∃ i, r i = w
  h_complete : ∀ w ∈ degreeThree G L, ∃ p, h p = w
  incidence : ∀ i p, G.Adj (r i) (h p) ↔ highIncidence i p
  u_neighbors : G.neighborFinset (h 0) = {r 1, r 2, r 0}
  v_neighbors : G.neighborFinset (h 1) = {r 3, r 4, r 0}
  high_neighbors : ∀ i, degreeThree G (G.neighborFinset (r i)) = highRow h i

set_option maxHeartbeats 400000 in
private theorem indexed_labels_of_parameters
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1) :
    Nonempty (IndexedLabels G L R) := by
  classical
  obtain ⟨z, hz, u, v, x1, x2, y1, y2, huz, hvz, hhigh, hhigh_all,
    a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hmiddle, hM,
    Ta, Tb, Tc, Td, Te, Tf⟩ :=
    high_right_connector_labels hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨X1, X2, Y1, Y2, hX1R, hX2R, hY1R, hY2R,
    hX13, hX23, hY13, hY23, TX1, TX2, TY1, TY2,
    Nz, Nu, Nv, Nx1, Nx2, Ny1, Ny2, hright, hR_all⟩ :=
    right_labels_assembly hpart hdeg hlow hg hL hR hL2 hR2 hz
      u v x1 x2 y1 y2 huz hvz hhigh ha hb hc hd he hf hmiddle hM
      Ta Tb Tc Td Te Tf
  let r : Fin 11 → V := ([z, a, b, c, d, e, f, X1, X2, Y1, Y2] : List V).get
  let h : Fin 6 → V := ([u.val, v.val, x1.val, x2.val, y1.val, y2.val] : List V).get
  have hr : Function.Injective r := hright.injective_get
  have hhd : ([u.val, v.val, x1.val, x2.val, y1.val, y2.val] : List V).Nodup :=
    hhigh.map Subtype.val_injective
  have hh : Function.Injective h := hhd.injective_get
  have hzR : z ∈ R := (Finset.mem_filter.mp hz).1
  have hz2 : G.degree z = 2 := (Finset.mem_filter.mp hz).2
  have hrR : ∀ i, r i ∈ R := by
    intro i
    fin_cases i <;> simp only [r, List.get_eq_getElem]
    · exact hzR
    · exact connector_right ha
    · exact connector_right hb
    · exact connector_right hc
    · exact connector_right hd
    · exact connector_right he
    · exact connector_right hf
    · exact hX1R
    · exact hX2R
    · exact hY1R
    · exact hY2R
  have hhL : ∀ p, h p ∈ L := by
    intro p
    fin_cases p <;> simp only [h, List.get_eq_getElem]
    · exact high_left u
    · exact high_left v
    · exact high_left x1
    · exact high_left x2
    · exact high_left y1
    · exact high_left y2
  have hh3 : ∀ p, G.degree (h p) = 3 := by
    intro p
    fin_cases p <;> simp only [h, List.get_eq_getElem]
    · exact high_degree u
    · exact high_degree v
    · exact high_degree x1
    · exact high_degree x2
    · exact high_degree y1
    · exact high_degree y2
  have hr3 : ∀ i, i ≠ 0 → G.degree (r i) = 3 := by
    intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · exact connector_degree ha
    · exact connector_degree hb
    · exact connector_degree hc
    · exact connector_degree hd
    · exact connector_degree he
    · exact connector_degree hf
    · exact hX13
    · exact hX23
    · exact hY13
    · exact hY23
  have hr_all : ∀ w ∈ R, ∃ i, r i = w := by
    intro w hw
    rw [hR_all] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    · exact ⟨0, hw.symm⟩
    · exact ⟨1, hw.symm⟩
    · exact ⟨2, hw.symm⟩
    · exact ⟨3, hw.symm⟩
    · exact ⟨4, hw.symm⟩
    · exact ⟨5, hw.symm⟩
    · exact ⟨6, hw.symm⟩
    · exact ⟨7, hw.symm⟩
    · exact ⟨8, hw.symm⟩
    · exact ⟨9, hw.symm⟩
    · exact ⟨10, hw.symm⟩
  have hh_all : ∀ w ∈ degreeThree G L, ∃ p, h p = w := by
    intro w hw
    let w' : High G L := ⟨w, hw⟩
    rcases hhigh_all w' with hw' | hw' | hw' | hw' | hw' | hw'
    · exact ⟨0, (congrArg Subtype.val hw').symm⟩
    · exact ⟨1, (congrArg Subtype.val hw').symm⟩
    · exact ⟨2, (congrArg Subtype.val hw').symm⟩
    · exact ⟨3, (congrArg Subtype.val hw').symm⟩
    · exact ⟨4, (congrArg Subtype.val hw').symm⟩
    · exact ⟨5, (congrArg Subtype.val hw').symm⟩
  have Tz : degreeThree G (G.neighborFinset z) = {u.val, v.val} := by
    rw [Nz]
    ext w
    simp only [degreeThree, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hw
      refine ⟨hw, ?_⟩
      rcases hw with rfl | rfl
      · exact high_degree u
      · exact high_degree v
  have htables : ∀ i, degreeThree G (G.neighborFinset (r i)) = highRow h i := by
    intro i
    fin_cases i
    · simpa [r, h, highRow] using Tz
    · simpa [r, h, highRow] using Ta
    · simpa [r, h, highRow] using Tb
    · simpa [r, h, highRow] using Tc
    · simpa [r, h, highRow] using Td
    · simpa [r, h, highRow] using Te
    · simpa [r, h, highRow] using Tf
    · simpa [r, h, highRow] using TX1
    · simpa [r, h, highRow] using TX2
    · simpa [r, h, highRow] using TY1
    · simpa [r, h, highRow] using TY2
  have hinc : ∀ i p, G.Adj (r i) (h p) ↔ highIncidence i p := by
    intro i p
    have hm : G.Adj (r i) (h p) ↔
        h p ∈ degreeThree G (G.neighborFinset (r i)) := by
      simp [degreeThree, hh3 p]
    rw [hm, htables i]
    fin_cases i <;> fin_cases p <;>
      simp [highRow, highIncidence, hh.eq_iff]
  refine ⟨{
    r := r
    h := h
    r_injective := hr
    h_injective := hh
    r_mem := hrR
    h_mem := hhL
    h_degree := hh3
    r_zero_degree := hz2
    r_nonzero_degree := hr3
    r_complete := hr_all
    h_complete := hh_all
    incidence := hinc
    u_neighbors := ?_
    v_neighbors := ?_
    high_neighbors := htables
  }⟩
  · change G.neighborFinset u.val = {a, b, z}
    rw [Nu]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    simp only [or_comm, or_left_comm, or_assoc]
  · change G.neighborFinset v.val = {c, d, z}
    rw [Nv]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    simp only [or_comm, or_left_comm, or_assoc]

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels

end

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairPartners

open SimpleGraph GirthSliceCounting AsymmetricLowPairing
open private neighbor_parts_card one_three_cross_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private lemma other_right_of_low_neighbor
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (r : Fin 11 → V) (hcover : ∀ x ∈ R, ∃ i, r i = x)
    (i : Fin 11) (hriR : r i ∈ R)
    {w : V} (hw2 : G.degree w = 2) (hriw : G.Adj (r i) w) :
    ∃ j, i ≠ j ∧ G.Adj (r j) w := by
  have hwL : w ∈ L := hpart.mem_of_mem_adj' hriR hriw.symm
  have hcard : 1 < (G.neighborFinset w).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hw2]
    omega
  obtain ⟨v, hvN, hvne⟩ := Finset.exists_mem_ne hcard (r i)
  have hwv : G.Adj w v := (G.mem_neighborFinset _ _).mp hvN
  have hvR : v ∈ R := hpart.mem_of_mem_adj hwL hwv
  obtain ⟨j, hj⟩ := hcover v hvR
  refine ⟨j, ?_, ?_⟩
  · intro hij
    have hriv : r i = v := by simpa only [← hij] using hj
    exact hvne hriv.symm
  · rw [hj]
    exact hwv.symm

private theorem low_pair_partner_exists
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (r : Fin 11 → V) (hcover : ∀ x ∈ R, ∃ i, r i = x)
    (i : Fin 11) (hriR : r i ∈ R) (hri3 : G.degree (r i) = 3)
    (hhigh : (degreeThree G (G.neighborFinset (r i))).card ≤ 2) :
    ∃ j, i ≠ j ∧ lowPair G (r i) (r j) := by
  have hparts := neighbor_parts_card hdeg (r i)
  have hpos : 0 < (degreeTwo G (G.neighborFinset (r i))).card := by
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hw with ⟨hwN, hw2⟩
  have hriw : G.Adj (r i) w := (G.mem_neighborFinset _ _).mp hwN
  obtain ⟨j, hij, hrjw⟩ :=
    other_right_of_low_neighbor hpart r hcover i hriR hw2 hriw
  exact ⟨j, hij, w, hw2, hriw, hrjw⟩

private theorem two_low_pair_partners_exists
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (r : Fin 11 → V) (hrinj : Function.Injective r)
    (hcover : ∀ x ∈ R, ∃ i, r i = x)
    (i : Fin 11) (hriR : r i ∈ R) (hri3 : G.degree (r i) = 3)
    (hhigh : (degreeThree G (G.neighborFinset (r i))).card = 1) :
    ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧
      lowPair G (r i) (r j) ∧ lowPair G (r i) (r k) := by
  have hparts := neighbor_parts_card hdeg (r i)
  have hlowcard : (degreeTwo G (G.neighborFinset (r i))).card = 2 := by
    omega
  obtain ⟨w1, w2, hw12, hlow⟩ := Finset.card_eq_two.mp hlowcard
  have hw1 : w1 ∈ degreeTwo G (G.neighborFinset (r i)) := by
    rw [hlow]
    simp
  have hw2 : w2 ∈ degreeTwo G (G.neighborFinset (r i)) := by
    rw [hlow]
    simp
  rcases Finset.mem_filter.mp hw1 with ⟨hw1N, hw1degree⟩
  rcases Finset.mem_filter.mp hw2 with ⟨hw2N, hw2degree⟩
  have hriw1 : G.Adj (r i) w1 := (G.mem_neighborFinset _ _).mp hw1N
  have hriw2 : G.Adj (r i) w2 := (G.mem_neighborFinset _ _).mp hw2N
  obtain ⟨j, hij, hrjw1⟩ :=
    other_right_of_low_neighbor hpart r hcover i hriR hw1degree hriw1
  obtain ⟨k, hik, hrkw2⟩ :=
    other_right_of_low_neighbor hpart r hcover i hriR hw2degree hriw2
  have hri_ne_rj : r i ≠ r j := fun h => hij (hrinj h)
  have hjk : j ≠ k := by
    intro heq
    have hrjw2 : G.Adj (r j) w2 := by simpa only [← heq] using hrkw2
    exact one_three_cross_impossible hpart.symm hg hriR hriR
      hriw2 hriw1 hrjw1.symm hrjw2 hri_ne_rj hw12 ⟨rfl, rfl⟩
  exact ⟨j, k, hjk, hij, hik,
    ⟨w1, hw1degree, hriw1, hrjw1⟩, ⟨w2, hw2degree, hriw2, hrkw2⟩⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairPartners

end

/- From actual asymmetric parameters to the seven actual low pairs. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricActualPairs
open SimpleGraph GirthSliceCounting AsymmetricLowPairing AsymmetricLowPairAllowed
open AsymmetricIndexedSliceLabels AsymmetricLowPairCompletion AsymmetricLowPairPartners
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairPartners (low_pair_partner_exists two_low_pair_partners_exists)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricIndexedSliceLabels (indexed_labels_of_parameters)
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricLowPairForced (first_four_low_pairs)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem indexed_high_card_bound (s : IndexedLabels G L R) (i : Fin 11) :
    (degreeThree G (G.neighborFinset (s.r i))).card ≤ 2 := by
  rw [s.high_neighbors i]
  fin_cases i <;> simp [highRow, s.h_injective.eq_iff]

private theorem indexed_stub_high_card (s : IndexedLabels G L R)
    (i : Fin 11) (hi : i ∈ ({7, 8, 9, 10} : Finset (Fin 11))) :
    (degreeThree G (G.neighborFinset (s.r i))).card = 1 := by
  rw [s.high_neighbors i]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [highRow]

private theorem indexed_first_four
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (s : IndexedLabels G L R) :
    lowPair G (s.r 1) (s.r 10) ∧ lowPair G (s.r 2) (s.r 9) ∧
      lowPair G (s.r 3) (s.r 8) ∧ lowPair G (s.r 4) (s.r 7) := by
  apply first_four_low_pairs hpart hdeg hlow hg hL hR hL2 hR2
    s.r s.h s.r_injective s.h_injective s.r_mem s.h_mem s.h_degree
    s.r_zero_degree s.incidence s.u_neighbors s.v_neighbors
  · simpa [highRow] using s.high_neighbors 0
  · simpa [highRow] using s.high_neighbors 1
  · simpa [highRow] using s.high_neighbors 2
  · simpa [highRow] using s.high_neighbors 3
  · simpa [highRow] using s.high_neighbors 4

private theorem all_actual_pairs
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 13) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 7) (hR2 : (degreeTwo G R).card = 1)
    (s : IndexedLabels G L R) :
    lowPair G (s.r 1) (s.r 10) ∧ lowPair G (s.r 2) (s.r 9) ∧
      lowPair G (s.r 3) (s.r 8) ∧ lowPair G (s.r 4) (s.r 7) ∧
      lowPair G (s.r 5) (s.r 6) ∧ lowPair G (s.r 7) (s.r 8) ∧
      lowPair G (s.r 9) (s.r 10) := by
  obtain ⟨h1, h2, h3, h4⟩ := indexed_first_four hpart hdeg hlow hg hL hR hL2 hR2 s
  have hexists : ∀ i : Fin 11, i ≠ 0 → ∃ j, i ≠ j ∧ lowPair G (s.r i) (s.r j) := by
    intro i hi
    exact low_pair_partner_exists hpart hdeg s.r s.r_complete i (s.r_mem i)
      (s.r_nonzero_degree i hi) (indexed_high_card_bound s i)
  have htwo : ∀ i ∈ ({7, 8, 9, 10} : Finset (Fin 11)),
      ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧
        lowPair G (s.r i) (s.r j) ∧ lowPair G (s.r i) (s.r k) := by
    intro i hi
    have hi0 : i ≠ 0 := by
      intro he
      simpa [he] using hi
    exact two_low_pair_partners_exists hpart hdeg hg s.r s.r_injective
      s.r_complete i (s.r_mem i) (s.r_nonzero_degree i hi0) (indexed_stub_high_card s i hi)
  obtain ⟨h5, h6, h7⟩ := actual_low_pair_completion hpart hlow hg s.r s.h
    s.r_injective s.h_injective s.r_mem s.h_degree s.r_zero_degree
    (fun i p hip => (s.incidence i p).mpr hip) hexists htwo h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricActualPairs

end
