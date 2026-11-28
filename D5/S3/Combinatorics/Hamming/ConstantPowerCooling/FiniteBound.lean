/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows, D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking]
   utility: none
   digest: Finite upper bound for constant-power error-correcting cooling codes. -/

import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.Shadows
import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.CliquePacking

/-! # Finite upper bound for constant-power error-correcting cooling codes -/

open scoped BigOperators ENat
open SimpleGraph

namespace CPECCBridge
open Finset

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def FinsetInduce {V : Type*} [DecidableEq V]
    (S : Finset V) (G : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.mk
    (fun u v => u ∈ S ∧ v ∈ S ∧ G.Adj u v)
    (Std.Symm.mk (by
      exact fun u v h => ⟨h.2.1, h.1, G.symm.symm u v h.2.2⟩))
    (Std.Irrefl.mk (by
      exact fun u h => G.loopless.irrefl u h.2.2))

private theorem finsetInduce_out_degree_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (FinsetInduce S G).Adj]
    (v : V) (hv : v ∉ S) :
    (FinsetInduce S G).degree v = 0 := by
  classical
  rw [← (FinsetInduce S G).ncard_neighborSet]
  have hzero : (FinsetInduce S G).neighborSet v = ∅ := by
    ext u
    constructor
    · intro hu
      exact False.elim (hv hu.1)
    · simp
  rw [hzero, Set.ncard_empty]

private theorem leave_degree_budget
    {V : Type*} [Fintype V]
    (L : SimpleGraph V) [Fintype L.edgeSet]
    (deg : V → ℕ)
    (S : Finset V) (x : V → ℕ) (k g d : ℕ)
    (h_out : ∀ v, v ∉ S → deg v = 0)
    (h_deg : ∀ v ∈ S, deg v ≤ (g - 1) + (k - 1) * x v)
    (h_pos : ∀ v ∈ S, 1 ≤ x v)
    (h_sum : ∑ v ∈ S, x v = k * d)
    (h_handshake : ∑ v, deg v = 2 * L.edgeFinset.card)
    (hk : 2 ≤ k) (hg : 1 ≤ g) :
    2 * L.edgeFinset.card ≤ k * (k + g - 2) * d := by
  have hsumdeg : (∑ v, deg v) = ∑ v ∈ S, deg v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro v hv hnot
    exact h_out v (by simpa using hnot)
  have hdeg_sum :
      (∑ v ∈ S, deg v) ≤
        ∑ v ∈ S, ((g - 1) + (k - 1) * x v) := by
    exact Finset.sum_le_sum fun v hv => h_deg v hv
  have hcard_le : S.card ≤ ∑ v ∈ S, x v := by
    calc
      S.card = ∑ _v ∈ S, 1 := by simp
      _ ≤ ∑ v ∈ S, x v := by
        exact Finset.sum_le_sum fun v hv => h_pos v hv
  have hconst :
      S.card * (g - 1) ≤ (∑ v ∈ S, x v) * (g - 1) :=
    Nat.mul_le_mul_right (g - 1) hcard_le
  have hbound :
      (∑ v ∈ S, deg v) ≤
        (k + g - 2) * (∑ v ∈ S, x v) := by
    calc
      (∑ v ∈ S, deg v) ≤
          ∑ v ∈ S, ((g - 1) + (k - 1) * x v) := hdeg_sum
      _ = S.card * (g - 1) + (k - 1) * (∑ v ∈ S, x v) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (∑ v ∈ S, x v) * (g - 1) +
          (k - 1) * (∑ v ∈ S, x v) := by
        exact Nat.add_le_add_right hconst _
      _ = (k + g - 2) * (∑ v ∈ S, x v) := by
        have hkg : k + g - 2 = (k - 1) + (g - 1) := by omega
        rw [hkg, Nat.add_mul]
        ac_rfl
  calc
    2 * L.edgeFinset.card = ∑ v, deg v := h_handshake.symm
    _ = ∑ v ∈ S, deg v := hsumdeg
    _ ≤ (k + g - 2) * (∑ v ∈ S, x v) := hbound
    _ = (k + g - 2) * (k * d) := by rw [h_sum]
    _ = k * (k + g - 2) * d := by ac_rfl


private theorem finite_shadow_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (L : SimpleGraph V) (H : I → SimpleGraph V)
    [(i : I) → Fintype (H i).edgeSet] [Fintype L.edgeSet]
    (B K d : ℕ)
    (hB : 0 < B)
    (h_each : ∀ i, B ≤ (H i).edgeFinset.card)
    (h_sub : ∀ i, H i ≤ L)
    (h_disj :
      (Set.univ : Set I).PairwiseDisjoint
        (fun i => (H i).edgeFinset))
    (h_budget : 2 * L.edgeFinset.card ≤ K * d)
    (h_threshold : K ≤ 2 * B) :
    Fintype.card I ≤ d := by
  have h_disj' :
      (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
        (fun i => (H i).edgeFinset) := by
    simpa using h_disj
  have h_union :
      ((Finset.univ : Finset I).biUnion (fun i => (H i).edgeFinset)).card =
        ∑ i : I, (H i).edgeFinset.card := by
    simpa using (Finset.card_biUnion (s := (Finset.univ : Finset I))
      (t := fun i => (H i).edgeFinset) h_disj')
  have h_union_sub :
      (Finset.univ : Finset I).biUnion (fun i => (H i).edgeFinset)
        ⊆ L.edgeFinset := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨i, hi⟩ := he
    exact (SimpleGraph.edgeFinset_subset_edgeFinset.mpr (h_sub i)) hi
  have h_sum_le : (∑ i : I, (H i).edgeFinset.card) ≤ L.edgeFinset.card := by
    rw [← h_union]
    exact Finset.card_le_card h_union_sub
  have h_lower : Fintype.card I * B ≤ ∑ i : I, (H i).edgeFinset.card := by
    calc
      Fintype.card I * B = ∑ i : I, B := by simp
      _ ≤ ∑ i : I, (H i).edgeFinset.card := by
        exact Finset.sum_le_sum (fun i hi => h_each i)
  have h_prod : Fintype.card I * B ≤ L.edgeFinset.card := h_lower.trans h_sum_le
  have h1 := Nat.mul_le_mul_left 2 h_prod
  have h2 := h1.trans h_budget
  have h3 := Nat.mul_le_mul_right d h_threshold
  have h4 : (2 * B) * Fintype.card I ≤ (2 * B) * d := by
    calc
      (2 * B) * Fintype.card I = 2 * (Fintype.card I * B) := by ac_rfl
      _ ≤ K * d := h2
      _ ≤ (2 * B) * d := h3
  exact Nat.le_of_mul_le_mul_left h4 (by omega)

private theorem leave_arithmetic
    (n k g R r : ℕ) (_hk : 2 ≤ k) (_hg : 1 ≤ g)
    (hgn : g ≤ n) (hR : n - g = (k - 1) * R) (hr : r ≤ R) :
    n - 1 - (k - 1) * r = (g - 1) + (k - 1) * (R - r) := by
  have hp : (k - 1) * r ≤ (k - 1) * R := Nat.mul_le_mul_left _ hr
  have hmid : n - 1 - (k - 1) * r = (g - 1) + ((k - 1) * R - (k - 1) * r) := by
    have hnrel : n = g + (k - 1) * R := by omega
    omega
  rw [hmid, Nat.mul_sub_left_distrib]

private theorem incidence_le_of_degree
    (n k g R r : ℕ) (_hk : 2 ≤ k) (_hg : 1 ≤ g)
    (hkg : g ≤ k - 1) (hgn : g ≤ n) (hR : n - g = (k - 1) * R)
    (hlt : (k - 1) * r < n) : r ≤ R := by
  have hnrel : n = g + (k - 1) * R := by omega
  by_contra h
  have hRr : R + 1 ≤ r := by omega
  have hm := Nat.mul_le_mul_left (k - 1) hRr
  rw [Nat.mul_add] at hm
  omega

private theorem deficit_arithmetic
    {V I : Type*} [Fintype V] [DecidableEq I]
    (r : V → ℕ) (x : V → ℕ) (S : Finset V)
    (C : Finset I) (k R d J : ℕ)
    (hS : ∀ v, v ∈ S ↔ 0 < x v)
    (hx : ∀ v, x v = R - r v)
    (hr : ∀ v, r v ≤ R)
    (hinc : ∑ v, r v = k * C.card)
    (hJR : Fintype.card V * R = k * J)
    (hJ : C.card + d = J) (hk : 1 ≤ k) :
    (∑ v ∈ S, x v = k * d) ∧ C.card ≤ J := by
  have hsum_le : (∑ v, r v) ≤ Fintype.card V * R := by
    calc
      (∑ v, r v) ≤ ∑ v, R := Finset.sum_le_sum (fun v hv => hr v)
      _ = Fintype.card V * R := by simp [Finset.sum_const]
  have hCmul : k * C.card ≤ k * J := by
    rw [← hinc, ← hJR]
    exact hsum_le
  have hC_le : C.card ≤ J := Nat.le_of_mul_le_mul_left hCmul (by omega)
  have hxzero : ∀ v, v ∉ S → x v = 0 := by
    intro v hv
    have hnot : ¬0 < x v := by simpa [hS v] using hv
    omega
  have hsumx : ∑ v, x v = k * d := by
    have hsumsub : ∑ v, x v = ∑ v ∈ S, x v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v hv hnot
      exact hxzero v (by simpa using hnot)
    have hsumsubR : ∑ v, x v = Fintype.card V * R - ∑ v, r v := by
      calc
        ∑ v, x v = ∑ v, (R - r v) := by simp_rw [hx]
        _ = Fintype.card V * R - ∑ v, r v := by
          rw [Finset.sum_tsub_distrib _ (by
            intro v hv
            exact hr v)]
          simp [Finset.sum_const]
    rw [hsumsubR, hinc, hJR]
    have hsub : J - C.card = d := by omega
    rw [← Nat.mul_sub_left_distrib, hsub]
  have hsumS : ∑ v ∈ S, x v = k * d := by
    have hsumsub : ∑ v, x v = ∑ v ∈ S, x v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v hv hnot
      exact hxzero v (by simpa using hnot)
    exact hsumsub.symm.trans hsumx
  refine ⟨hsumS, ?_⟩
  exact hC_le

private theorem choose_clique_supports
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (H : I → SimpleGraph V) (C : Finset I) (k : ℕ)
    (hC : ∀ i ∈ C, ∃ W : Finset V, (H i).IsNClique k W) :
    ∃ W : I → Finset V, ∀ i ∈ C, (H i).IsNClique k (W i) := by
  classical
  let W : I → Finset V := fun i => if hi : i ∈ C then Classical.choose (hC i hi) else ∅
  have hW : ∀ i ∈ C, (H i).IsNClique k (W i) := by
    intro i hi
    dsimp [W]
    split
    · next h => exact Classical.choose_spec (hC i h)
    · next h => exact False.elim (h hi)
  exact ⟨W, hW⟩

private theorem chosen_cliques_inter_le_one
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (H : I → SimpleGraph V) (C : Finset I) (k : ℕ)
    (W : I → Finset V)
    [(i : I) → DecidableRel (H i).Adj]
    (hW : ∀ i ∈ C, (H i).IsNClique k (W i))
    (hdisj : (Set.univ : Set I).PairwiseDisjoint
      (fun i => (H i).edgeFinset)) :
    ∀ ⦃i j : I⦄, i ∈ C → j ∈ C → i ≠ j → (W i ∩ W j).card ≤ 1 := by
  classical
  intro i j hi hj hij
  by_contra hbig
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < (W i ∩ W j).card)
  have hui : u ∈ (W i : Set V) := by simpa using (Finset.mem_inter.mp hu).1
  have hvi : v ∈ (W i : Set V) := by simpa using (Finset.mem_inter.mp hv).1
  have huj : u ∈ (W j : Set V) := by simpa using (Finset.mem_inter.mp hu).2
  have hvj : v ∈ (W j : Set V) := by simpa using (Finset.mem_inter.mp hv).2
  have hadj_i : (H i).Adj u v := by
    exact ((SimpleGraph.isClique_iff (G := H i)).mp (hW i hi).isClique) hui hvi huv
  have hadj_j : (H j).Adj u v := by
    exact ((SimpleGraph.isClique_iff (G := H j)).mp (hW j hj).isClique)
      huj hvj huv
  have hdi := hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hei : s(u, v) ∈ (H i).edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (H i)).2 hadj_i)
  have hej : s(u, v) ∈ (H j).edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (H j)).2 hadj_j)
  exact (Finset.disjoint_left.mp hdi) hei hej

theorem finite_cpecc_support_upper_bound
    (P : I → Finset (Finset V))
    (n w t g k : ℕ)
    (hn : Fintype.card V = n)
    (hkdef : k = w + t)
    (hkN : k ≤ n)
    (ht : 1 ≤ t)
    (hw : t + 3 < w)
    (hg : 1 ≤ g)
    (hgw : g < w)
    (hRdiv : k - 1 ∣ n - g)
    (hJdiv : k * (k - 1) ∣ n * (n - g))
    (hsize : ∀ i A, A ∈ P i → A.card = w)
    (hdel : ∀ i (D : Finset V), D.card = t → ∃ A ∈ P i, Disjoint D A)
    (hcross : ∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ B ∈ P j,
      (A ∩ B).card ≤ 1)
    (hthreshold : k * (k + g - 2) ≤ 2 * AppendixA.B w t) :
    Fintype.card I ≤ n * (n - g) / (k * (k - 1)) := by
  classical
  let H : I → SimpleGraph V := fun i => Shadow (P i)
  letI : (i : I) → DecidableRel (H i).Adj := fun i => Classical.decRel _
  have htv : t ≤ Fintype.card V := by omega
  have hk : 2 ≤ k := by omega
  have hkg : g ≤ k - 1 := by omega
  have hB : 0 < AppendixA.B w t := by
    have hleft : 0 < k * (k + g - 2) := Nat.mul_pos (by omega) (by omega)
    omega
  have hdist : ∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ B ∈ P j,
      2 * w - 3 ≤ (A \ B).card + (B \ A).card := by
    intro i j hij A hA B hB'
    exact support_distance_of_inter_le_one (hsize i A hA) (hsize j B hB')
      (hcross hij A hA B hB')
  have hdisj : (Set.univ : Set I).PairwiseDisjoint
      (fun i => (H i).edgeFinset) := by
    simpa [H] using (shadows_edge_disjoint_of_distance P hsize hdist)
  let C : Finset I := Finset.univ.filter
    (fun i => ∃ W : Finset V, (H i).IsNClique k W)
  have hCmem (i : I) : i ∈ C ↔ ∃ W : Finset V, (H i).IsNClique k W := by
    simp [C]
  have hCexists : ∀ i ∈ C, ∃ W : Finset V, (H i).IsNClique k W := by
    intro i hi
    exact (hCmem i).mp hi
  obtain ⟨W, hW⟩ := choose_clique_supports H C k hCexists
  have hWcard : ∀ i ∈ C, (W i).card = k := by
    intro i hi
    exact (hW i hi).card_eq
  have hinter : ∀ ⦃i j : I⦄, i ∈ C → j ∈ C → i ≠ j →
      (W i ∩ W j).card ≤ 1 := by
    exact chosen_cliques_inter_le_one H C k W hW hdisj
  have hclass : ∀ i, i ∈ C ∨ (H i).CliqueFree k := by
    intro i
    by_cases hi : i ∈ C
    · exact Or.inl hi
    · right
      intro Q hQ
      exact hi ((hCmem i).mpr ⟨Q, hQ⟩)
  let r : V → ℕ := fun v => (C.filter (fun i => v ∈ W i)).card
  obtain ⟨R, hR⟩ := hRdiv
  obtain ⟨J, hJ⟩ := hJdiv
  let R' : ℕ := R
  let J' : ℕ := J
  have hR_eq : n - g = (k - 1) * R' := by
    dsimp [R']
    exact hR
  have hJ_eq : n * (n - g) = k * (k - 1) * J' := by
    dsimp [J']
    exact hJ
  have hgn : g ≤ n := by omega
  have hJR : Fintype.card V * R' = k * J' := by
    have hmul : (k - 1) * (n * R') = (k - 1) * (k * J') := by
      calc
        (k - 1) * (n * R') = n * ((k - 1) * R') := by ac_rfl
        _ = n * (n - g) := by rw [hR_eq]
        _ = k * (k - 1) * J' := hJ_eq
        _ = (k - 1) * (k * J') := by ac_rfl
    have hnR : n * R' = k * J' := Nat.mul_left_cancel (by omega) hmul
    simpa [hn] using hnR
  let S : Finset V := Finset.univ.filter (fun v => r v < R')
  let x : V → ℕ := fun v => R' - r v
  let L₀ : SimpleGraph V := (packedGraph C W)ᶜ
  letI : DecidableRel L₀.Adj := Classical.decRel _
  letI : DecidableRel (FinsetInduce S L₀).Adj := Classical.decRel _
  have hpackdeg (v : V) : (packedGraph C W).degree v = (k - 1) * r v := by
    simpa [r] using (packedGraph_degree C W k hWcard hinter v)
  have hrl : ∀ v, r v ≤ R' := by
    intro v
    apply incidence_le_of_degree n k g R' (r v) hk hg hkg hgn hR_eq
    have hvlt := (packedGraph C W).degree_lt_card_verts v
    simpa [hpackdeg, hn] using hvlt
  have hleave : ∀ v, L₀.degree v = (g - 1) + (k - 1) * x v := by
    intro v
    have hdegcomp := SimpleGraph.degree_compl (packedGraph C W) v
    rw [hdegcomp, hpackdeg, hn]
    exact leave_arithmetic n k g R' (r v) hk hg hgn hR_eq (hrl v)
  have hbase_sub : ∀ i, i ∉ C → H i ≤ L₀ := by
    intro i hi u v huv
    rw [SimpleGraph.compl_adj]
    refine ⟨(H i).ne_of_adj huv, ?_⟩
    intro hpack
    obtain ⟨j, hj, huW, hvW⟩ := (packedGraph_adj_iff C W u v).mp hpack
    have huv' : u ≠ v := (Finset.mem_erase.mp hvW).1.symm
    have hvW' : v ∈ W j := (Finset.mem_erase.mp hvW).2
    have hadj : (H j).Adj u v :=
      (SimpleGraph.isClique_iff (G := H j)).mp (hW j hj).isClique (by simpa using huW) (by simpa using hvW') huv'
    have hei : s(u, v) ∈ (H i).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (H i)).2 huv)
    have hej : s(u, v) ∈ (H j).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (H j)).2 hadj)
    have hij : i ≠ j := by
      intro heq
      exact hi (heq ▸ hj)
    exact (Finset.disjoint_left.mp (hdisj (Set.mem_univ i) (Set.mem_univ j) hij)) hei hej
  have hsupport : ∀ i, i ∉ C → ∀ v, v ∈ (H i).support → v ∈ S := by
    intro i hi v hv
    have hdegH : w - 1 ≤ (H i).degree v :=
      shadow_degree_lower_of_mem (hsize i) hv
    have hdegL : (H i).degree v ≤ L₀.degree v :=
      (H i).degree_le_of_le (hbase_sub i hi)
    have hdegL' : (H i).degree v ≤
        (g - 1) + (k - 1) * (R' - r v) := by
      calc
        (H i).degree v ≤ L₀.degree v := hdegL
        _ = (g - 1) + (k - 1) * (R' - r v) := by simpa [x] using hleave v
    have hnot : r v < R' := by
      by_contra hnot
      have heq : r v = R' := Nat.le_antisymm (hrl v) (Nat.le_of_not_gt hnot)
      rw [heq] at hdegL'
      have hcontra : w - 1 ≤ g - 1 := by
        exact hdegH.trans (by simpa using hdegL')
      exact (Nat.not_le_of_lt (by omega : g - 1 < w - 1)) hcontra
    simpa [S, r] using hnot
  have hinterC : ∀ v, v ∈ S ↔ 0 < x v := by
    intro v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, x]
    omega
  have hinc : ∑ v : V, r v = k * C.card := by
    simpa [r] using incidence_sum C W k hWcard
  have hsumrle : (∑ v : V, r v) ≤ Fintype.card V * R' := by
    calc
      (∑ v : V, r v) ≤ ∑ v : V, R' := Finset.sum_le_sum (fun v hv => hrl v)
      _ = Fintype.card V * R' := by simp [Finset.sum_const]
  have hCmul : k * C.card ≤ k * J' := by
    rw [← hinc, ← hJR]
    exact hsumrle
  have hCle : C.card ≤ J' := Nat.le_of_mul_le_mul_left hCmul (by omega)
  have hJsum : C.card + (J' - C.card) = J' := by omega
  have hsum : ∑ v ∈ S, x v = k * (J' - C.card) := by
    have hdef := deficit_arithmetic r x S C k R' (J' - C.card) J'
      hinterC (by intro v; rfl) hrl hinc hJR hJsum (by omega)
    exact hdef.1
  have hnwt : w + t ≤ n := by omega
  have hinduce_sub : FinsetInduce S L₀ ≤ L₀ := by
    intro u v huv
    exact huv.2.2
  have hdeg_induce : ∀ v, (FinsetInduce S L₀).degree v ≤ L₀.degree v := by
    intro v
    exact (FinsetInduce S L₀).degree_le_of_le hinduce_sub
  have h_deg : ∀ v ∈ S,
      (FinsetInduce S L₀).degree v ≤ (g - 1) + (k - 1) * x v := by
    intro v hv
    calc
      (FinsetInduce S L₀).degree v ≤ L₀.degree v := hdeg_induce v
      _ = (g - 1) + (k - 1) * x v := hleave v
  have h_pos : ∀ v ∈ S, 1 ≤ x v := by
    intro v hv
    have hv' : r v < R' := by simpa [S] using hv
    simpa [x] using (show 1 ≤ R' - r v by omega)
  let N := {i : I // i ∉ C}
  let PN : N → Finset (Finset V) := fun i => P i.1
  let LN : SimpleGraph V := FinsetInduce S L₀
  letI : DecidableRel LN.Adj := Classical.decRel _
  have h_eachN : ∀ i : N, AppendixA.B w t ≤ (Shadow (PN i)).edgeFinset.card := by
    intro i
    dsimp [PN]
    exact nonclique_shadow_edge_lower_of_ambient_deletion ht hw htv
      (hsize i.1) (hdel i.1)
      (by simpa [H, hkdef] using (hclass i.1 |>.resolve_left i.2))
  have h_subN : ∀ i : N, Shadow (PN i) ≤ LN := by
    intro i u v huv
    have hbase := hbase_sub i.1 i.2 huv
    change u ∈ S ∧ v ∈ S ∧ L₀.Adj u v
    have huS : u ∈ S := hsupport i.1 i.2 u
      ((SimpleGraph.mem_support (H i.1)).mpr ⟨v, huv⟩)
    have hvS : v ∈ S := hsupport i.1 i.2 v
      ((SimpleGraph.mem_support (H i.1)).mpr ⟨u, (H i.1).symm.symm u v huv⟩)
    exact ⟨huS, hvS, hbase⟩
  have h_disjN : (Set.univ : Set N).PairwiseDisjoint
      (fun i => (Shadow (PN i)).edgeFinset) := by
    intro i hi j hj hij
    exact hdisj (Set.mem_univ i.1) (Set.mem_univ j.1)
      (by intro heq; exact hij (Subtype.ext heq))
  have hbudget : 2 * LN.edgeFinset.card ≤
      (k * (k + g - 2)) * (J' - C.card) := by
    have hhandshake : ∑ v : V, LN.degree v = 2 * LN.edgeFinset.card :=
      LN.sum_degrees_eq_twice_card_edges
    have hdeg' : ∀ v ∈ S, LN.degree v ≤
        (g - 1) + (k - 1) * x v := by
      intro v hv
      exact h_deg v hv
    exact leave_degree_budget LN (fun v => LN.degree v) S x k g (J' - C.card)
      (by intro v hv; exact finsetInduce_out_degree_zero S L₀ v hv)
      hdeg' h_pos hsum hhandshake hk hg
  have hNcard : Fintype.card N ≤ J' - C.card := by
    exact finite_shadow_bound LN (fun i : N => Shadow (PN i))
      (AppendixA.B w t) (k * (k + g - 2)) (J' - C.card) hB h_eachN
      h_subN h_disjN hbudget (by omega)
  have hcardN : Fintype.card N = Fintype.card I - C.card := by
    dsimp [N]
    rw [Fintype.card_subtype_compl (fun i : I => i ∈ C)]
    simp [Fintype.card_coe]
  have hboundJ : Fintype.card I ≤ J' := by omega
  have hquot : J' = n * (n - g) / (k * (k - 1)) := by
    symm
    apply Nat.div_eq_of_eq_mul_left
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hJ_eq
  rw [hquot] at hboundJ
  exact hboundJ

end
end CPECCBridge
