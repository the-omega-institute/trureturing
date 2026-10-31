/- GID: D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/ConfigurationCharge
   mirror-E: none(waiver:actual-common-activity-signed-charge-identity)
   anchors: []
   utility: none
   digest: The actual common-activity Gibbs defect is the mean signed configuration charge. -/

import D5.S3.StatisticalMechanics.HardCore.GibbsOccupation

/-! Exact signed configuration-charge identity for the actual finite Gibbs law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge

open scoped BigOperators
open Finset
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OccupationMoments
open D5.S3.StatisticalMechanics.HardCore.GibbsOccupation

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The occupied neighbors in the actual configuration. -/
def occupiedNeighbors (J : Finset α) (v : α) : Finset α := J.filter (G.Adj v)

/-- All vertex weights use the same activity. -/
def degreeWeight (lam : ℝ) (v : α) : ℝ :=
  lam / (1 + ((G.degree v : ℝ) + 1) * lam)

/-- Exact signed source charge; no sign is asserted. -/
def configurationCharge (lam : ℝ) (J : Finset α) : ℝ :=
  ∑ v, if 2 ≤ (occupiedNeighbors G J v).card then
    (∑ u ∈ occupiedNeighbors G J v, degreeWeight G lam u) - degreeWeight G lam v
    else 0

/-- Occupation defect under the actual Gibbs law on all independent subsets. -/
def occupationDefect (lam : ℝ) : ℝ :=
  meanOccupation G univ lam - ∑ v, degreeWeight G lam v

private theorem mem_full_configurations (J : Finset α) :
    J ∈ configurations G univ ↔ G.IsIndepSet (J : Set α) := by
  simp [configurations]

private theorem singleton_exchange (J : Finset α) (u v : α)
    (hJ : J ∈ configurations G univ)
    (hN : occupiedNeighbors G J v = {u}) :
    insert v (J.erase u) ∈ configurations G univ ∧
      occupiedNeighbors G (insert v (J.erase u)) u = {v} ∧
      insert u ((insert v (J.erase u)).erase v) = J ∧
      (insert v (J.erase u)).card = J.card := by
  have hu : u ∈ J := by
    have : u ∈ occupiedNeighbors G J v := hN.symm ▸ mem_singleton_self u
    exact (mem_filter.mp this).1
  have hvu : G.Adj v u := by
    have : u ∈ occupiedNeighbors G J v := hN.symm ▸ mem_singleton_self u
    exact (mem_filter.mp this).2
  have huv : u ≠ v := (G.ne_of_adj hvu).symm
  have hind := (mem_full_configurations G J).mp hJ
  have hv : v ∉ J := by
    intro hv
    exact hind hv hu huv.symm hvu
  have hneigh (x : α) (hx : x ∈ J.erase u) : ¬ G.Adj v x := by
    intro hvx
    have hmem : x ∈ occupiedNeighbors G J v := mem_filter.mpr ⟨mem_of_mem_erase hx, hvx⟩
    have he : x = u := mem_singleton.mp (hN ▸ hmem)
    exact (mem_erase.mp hx).1 he
  have hvE : v ∉ J.erase u := fun h => hv (mem_of_mem_erase h)
  refine ⟨(mem_full_configurations G _).mpr ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rcases mem_insert.mp hx with hxv | hxJ
    · subst x
      rcases mem_insert.mp hy with hyv | hyJ
      · subst y
        exact False.elim (hxy rfl)
      · exact hneigh y hyJ
    · rcases mem_insert.mp hy with hyv | hyJ
      · subst y
        exact fun h => hneigh x hxJ (G.adj_symm h)
      · exact hind (mem_of_mem_erase hxJ) (mem_of_mem_erase hyJ) hxy
  · ext x
    simp only [occupiedNeighbors, mem_filter, mem_insert, mem_erase, mem_singleton]
    constructor
    · rintro ⟨hx | ⟨hxu, hx⟩, hadj⟩
      · exact hx
      · exact False.elim (hind hu hx hxu.symm hadj)
    · rintro rfl
      exact ⟨Or.inl rfl, G.adj_symm hvu⟩
  · rw [erase_insert hvE, insert_erase hu]
  · rw [card_insert_of_notMem hvE, card_erase_of_mem hu]
    have : 0 < J.card := card_pos.mpr ⟨u, hu⟩
    omega

private theorem singleton_weight_symmetry (lam : ℝ) (u v : α) :
    (∑ J ∈ configurations G univ,
      if occupiedNeighbors G J v = {u} then lam ^ J.card else 0) =
    ∑ J ∈ configurations G univ,
      if occupiedNeighbors G J u = {v} then lam ^ J.card else 0 := by
  rw [← sum_filter, ← sum_filter]
  refine sum_bij'
    (i := fun (J : Finset α) _ => insert v (J.erase u))
    (j := fun (J : Finset α) _ => insert u (J.erase v))
    (hi := ?_) (hj := ?_) (h := ?_) (left_neg := ?_) (right_neg := ?_)
  · intro J hJ
    obtain ⟨hJ, hN⟩ := mem_filter.mp hJ
    exact mem_filter.mpr ⟨(singleton_exchange G J u v hJ hN).1,
      (singleton_exchange G J u v hJ hN).2.1⟩
  · intro J hJ
    obtain ⟨hJ, hN⟩ := mem_filter.mp hJ
    exact mem_filter.mpr ⟨(singleton_exchange G J v u hJ hN).1,
      (singleton_exchange G J v u hJ hN).2.1⟩
  · intro J hJ
    rw [(singleton_exchange G J u v (mem_filter.mp hJ).1 (mem_filter.mp hJ).2).2.2.2]
  · intro J hJ
    exact (singleton_exchange G J u v (mem_filter.mp hJ).1 (mem_filter.mp hJ).2).2.2.1
  · intro J hJ
    exact (singleton_exchange G J v u (mem_filter.mp hJ).1 (mem_filter.mp hJ).2).2.2.1

private theorem event_mass_eq (lam : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    (∑ J ∈ configurations G univ, if P J then gibbsMass G univ lam J else 0) =
      (∑ J ∈ configurations G univ, if P J then lam ^ J.card else 0) /
        partition G univ (fun _ => lam) := by
  rw [sum_div]
  apply sum_congr rfl
  intro J hJ
  simp only [gibbsMass, if_pos hJ]
  split_ifs <;> simp

private theorem singleton_mass_symmetry (lam : ℝ) (u v : α) :
    (∑ J ∈ configurations G univ,
      if occupiedNeighbors G J v = {u} then gibbsMass G univ lam J else 0) =
    ∑ J ∈ configurations G univ,
      if occupiedNeighbors G J u = {v} then gibbsMass G univ lam J else 0 := by
  rw [event_mass_eq, event_mass_eq, singleton_weight_symmetry]

private theorem vacancy_mass_balance (lam : ℝ) (hlam : 0 < lam) (v : α) :
    (∑ J ∈ configurations G univ,
      if occupiedNeighbors G J v = ∅ then gibbsMass G univ lam J else 0) =
    (1 + 1 / lam) * (∑ J ∈ configurations G univ,
      if v ∈ J then gibbsMass G univ lam J else 0) := by
  let K := univ.filter (fun x => ¬ G.Adj v x)
  have hf : (configurations G univ).filter
      (fun J => occupiedNeighbors G J v = ∅) = configurations G K := by
    ext J
    simp only [mem_filter, configurations, mem_powerset]
    constructor
    · rintro ⟨⟨_, hind⟩, hN⟩
      refine ⟨?_, hind⟩
      intro x hx
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro hadj
      have hm : x ∈ occupiedNeighbors G J v := mem_filter.mpr ⟨hx, hadj⟩
      rw [hN] at hm
      exact notMem_empty x hm
    · rintro ⟨hsub, hind⟩
      refine ⟨⟨subset_univ J, hind⟩, ?_⟩
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxJ, hadj⟩ := mem_filter.mp hx
      exact (mem_filter.mp (hsub hxJ)).2 hadj
  have he : K.erase v = closedComplement G univ v := by
    ext x
    simp [K, closedComplement, and_comm]
  have hc : closedComplement G K v = closedComplement G univ v := by
    ext x
    simp [K, closedComplement, and_assoc]
  have hv : v ∈ K := by simp [K]
  have hz : (∑ J ∈ configurations G univ,
      if occupiedNeighbors G J v = ∅ then lam ^ J.card else 0) =
      partition G K (fun _ => lam) := by
    rw [← sum_filter, hf]
    simp [partition]
  have hp := partition_delete G K v hv (fun _ => lam)
  rw [he, hc] at hp
  have ho := occupied_weight_add_erased G univ v (fun _ => lam)
  simp only [prod_const] at ho
  have hd := partition_delete G univ v (mem_univ v) (fun _ => lam)
  have how : (∑ J ∈ configurations G univ, if v ∈ J then lam ^ J.card else 0) =
      lam * partition G (closedComplement G univ v) (fun _ => lam) := by
    linarith
  have hZ : partition G univ (fun _ => lam) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_partition G univ (fun _ => lam) (fun _ _ => hlam.le)))
  rw [event_mass_eq, event_mass_eq, hz, hp, how]
  field_simp [ne_of_gt hlam, hZ]
  <;> ring

private theorem excess_charge_split (q : α → ℝ) (S : Finset α) (v : α) :
    (if 2 ≤ S.card then (∑ u ∈ S, q u) - q v else 0) =
      (∑ u ∈ S, q u) - q v + (if S = ∅ then q v else 0) -
        ∑ u, if S = {u} then q u - q v else 0 := by
  by_cases he : S = ∅
  · subst S
    simp
  by_cases h1 : S.card = 1
  · obtain ⟨u, rfl⟩ := card_eq_one.mp h1
    simp
  · have h2 : 2 ≤ S.card := by
      have := card_pos.mpr (nonempty_iff_ne_empty.mpr he)
      omega
    have hn : ∀ u, S ≠ {u} := by
      intro u hu
      exact h1 (hu ▸ card_singleton u)
    simp [h2, he, hn]

private theorem neighbor_weight_sum (q : α → ℝ) (J : Finset α) :
    (∑ v, ∑ u ∈ occupiedNeighbors G J v, q u) =
      ∑ u ∈ J, (G.degree u : ℝ) * q u := by
  simp only [occupiedNeighbors, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  have hs : (∑ v : α, if G.Adj v u then q u else 0) =
      ∑ v ∈ G.neighborFinset u, q u := by
    rw [← sum_filter]
    congr 1
    ext v
    simp [G.adj_comm]
  rw [hs]
  simp [nsmul_eq_mul]

private theorem configuration_charge_split (lam : ℝ) (J : Finset α) :
    configurationCharge G lam J =
      (∑ u ∈ J, (G.degree u : ℝ) * degreeWeight G lam u) -
      (∑ v, degreeWeight G lam v) +
      (∑ v, if occupiedNeighbors G J v = ∅ then degreeWeight G lam v else 0) -
      ∑ v, ∑ u, if occupiedNeighbors G J v = {u} then
        degreeWeight G lam u - degreeWeight G lam v else 0 := by
  unfold configurationCharge
  simp_rw [excess_charge_split]
  rw [sum_sub_distrib, sum_add_distrib, sum_sub_distrib, neighbor_weight_sum]

private theorem singleton_cancellation (lam : ℝ) (q : α → ℝ) :
    (∑ v, ∑ u, (q u - q v) *
      (∑ J ∈ configurations G univ,
        if occupiedNeighbors G J v = {u} then gibbsMass G univ lam J else 0)) = 0 := by
  let a := fun v u => ∑ J ∈ configurations G univ,
    if occupiedNeighbors G J v = {u} then gibbsMass G univ lam J else 0
  have ha (v u : α) : a v u = a u v := singleton_mass_symmetry G lam u v
  change (∑ v, ∑ u, (q u - q v) * a v u) = 0
  have hs : (∑ v, ∑ u, (q u - q v) * a v u) =
      ∑ v, ∑ u, (q v - q u) * a v u := by
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro u _
    rw [ha]
  have hz : (∑ v, ∑ u, (q u - q v) * a v u) +
      (∑ v, ∑ u, (q v - q u) * a v u) = 0 := by
    rw [← sum_add_distrib]
    apply sum_eq_zero
    intro v _
    rw [← sum_add_distrib]
    apply sum_eq_zero
    intro u _
    ring
  linarith

private theorem mass_sum_vertices (lam : ℝ) (f : Finset α → α → ℝ) :
    (∑ J ∈ configurations G univ, gibbsMass G univ lam J * ∑ v, f J v) =
      ∑ v, ∑ J ∈ configurations G univ, gibbsMass G univ lam J * f J v := by
  simp_rw [mul_sum]
  exact sum_comm

private theorem mass_event_factor (lam a : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    (∑ J ∈ configurations G univ, gibbsMass G univ lam J * (if P J then a else 0)) =
      a * (∑ J ∈ configurations G univ, if P J then gibbsMass G univ lam J else 0) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro J _
  split_ifs <;> simp [mul_comm]

/-- Complete original configuration-charge identity for every finite simple graph
and every common positive real activity, under its actual independent-set PMF. -/
theorem defect_eq_expected_charge (lam : ℝ) (hlam : 0 < lam) :
    occupationDefect G lam =
      ∑ J ∈ configurations G univ,
        (gibbsPMF G univ lam hlam.le J).toReal * configurationCharge G lam J := by
  let q := degreeWeight G lam
  let p := fun v => ∑ J ∈ configurations G univ,
    if v ∈ J then gibbsMass G univ lam J else 0
  have hM : meanOccupation G univ lam = ∑ v, p v := by
    rw [mean_eq_sum_vacancies G univ lam hlam.le]
    apply sum_congr rfl
    intro v _
    exact (by simpa only [p, gibbs_pmf_toReal] using
      (gibbs_vertex_occupied G univ v lam hlam.le).symm)
  have hdeg : (∑ J ∈ configurations G univ, gibbsMass G univ lam J *
      (∑ u ∈ J, (G.degree u : ℝ) * q u)) =
      ∑ u, ((G.degree u : ℝ) * q u) * p u := by
    calc
      _ = ∑ J ∈ configurations G univ, gibbsMass G univ lam J *
          (∑ u, if u ∈ J then (G.degree u : ℝ) * q u else 0) := by
        apply sum_congr rfl
        intro J _
        rw [sum_ite_mem_eq]
      _ = _ := by
        rw [mass_sum_vertices]
        apply sum_congr rfl
        intro u _
        exact mass_event_factor G lam _ (fun J => u ∈ J)
  have hconst : (∑ J ∈ configurations G univ,
      gibbsMass G univ lam J * (∑ v, q v)) = ∑ v, q v := by
    rw [← sum_mul, gibbs_mass_sum G univ lam hlam.le, one_mul]
  have hvac : (∑ J ∈ configurations G univ, gibbsMass G univ lam J *
      (∑ v, if occupiedNeighbors G J v = ∅ then q v else 0)) =
      ∑ v, q v * ((1 + 1 / lam) * p v) := by
    rw [mass_sum_vertices]
    apply sum_congr rfl
    intro v _
    rw [mass_event_factor, vacancy_mass_balance G lam hlam v]
  have hsingle : (∑ J ∈ configurations G univ, gibbsMass G univ lam J *
      (∑ v, ∑ u, if occupiedNeighbors G J v = {u} then q u - q v else 0)) = 0 := by
    rw [mass_sum_vertices]
    simp_rw [mass_sum_vertices, mass_event_factor]
    exact singleton_cancellation G lam q
  have hweight (v : α) : ((G.degree v : ℝ) + (1 + 1 / lam)) * q v = 1 := by
    have hd : 0 < 1 + ((G.degree v : ℝ) + 1) * lam := by positivity
    dsimp [q, degreeWeight]
    field_simp [ne_of_gt hlam, ne_of_gt hd]
    <;> ring
  have hraw : (∑ J ∈ configurations G univ,
      gibbsMass G univ lam J * configurationCharge G lam J) =
      meanOccupation G univ lam - ∑ v, q v := by
    calc
      _ = (∑ J ∈ configurations G univ, gibbsMass G univ lam J *
            (∑ u ∈ J, (G.degree u : ℝ) * q u)) -
          (∑ J ∈ configurations G univ, gibbsMass G univ lam J * (∑ v, q v)) +
          (∑ J ∈ configurations G univ, gibbsMass G univ lam J *
            (∑ v, if occupiedNeighbors G J v = ∅ then q v else 0)) -
          (∑ J ∈ configurations G univ, gibbsMass G univ lam J *
            (∑ v, ∑ u, if occupiedNeighbors G J v = {u} then q u - q v else 0)) := by
        simp_rw [configuration_charge_split]
        simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
        rfl
      _ = (∑ u, ((G.degree u : ℝ) * q u) * p u) - (∑ v, q v) +
          (∑ v, q v * ((1 + 1 / lam) * p v)) := by
        rw [hdeg, hconst, hvac, hsingle, sub_zero]
      _ = (∑ v, p v) - ∑ v, q v := by
        have he : (∑ u, ((G.degree u : ℝ) * q u) * p u) +
            (∑ v, q v * ((1 + 1 / lam) * p v)) = ∑ v, p v := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro v _
          calc
            _ = (((G.degree v : ℝ) + (1 + 1 / lam)) * q v) * p v := by ring
            _ = p v := by rw [hweight, one_mul]
        linarith
      _ = _ := by rw [hM]
  simp_rw [gibbs_pmf_toReal]
  exact hraw.symm

#print axioms defect_eq_expected_charge

end D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge


