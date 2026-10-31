/- GID: D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/ConfigurationCharge
   mirror-E: none(waiver:actual-common-activity-signed-charge-identity)
   anchors: []
   utility: none
   digest: The actual common-activity Gibbs defect is the mean signed configuration charge. -/

import D5.S3.StatisticalMechanics.HardCore.GibbsOccupation

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
  refine ⟨(mem_full_configurations G _).mpr ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx
    · rcases mem_insert.mp hy with rfl | hy
      · exact False.elim (hxy rfl)
      · exact hneigh y hy
    · rcases mem_insert.mp hy with rfl | hy
      · exact fun h => hneigh x hx (G.adj_symm h)
      · exact hind (mem_of_mem_erase hx) (mem_of_mem_erase hy) hxy
  · ext x
    simp only [occupiedNeighbors, mem_filter, mem_insert, mem_erase, mem_singleton]
    constructor
    · rintro ⟨hx | ⟨hxu, hx⟩, hadj⟩
      · exact hx
      · exact False.elim (hind hu hx hxu.symm hadj)
    · rintro rfl
      exact ⟨Or.inl rfl, G.adj_symm hvu⟩
  · rw [erase_insert (notMem_erase_of_notMem hv), insert_erase hu]
  · rw [card_insert_of_notMem (notMem_erase_of_notMem hv), card_erase_of_mem hu]
    have : 0 < J.card := card_pos.mpr ⟨u, hu⟩
    omega

private theorem singleton_weight_symmetry (lam : ℝ) (u v : α) :
    (∑ J ∈ configurations G univ,
      if occupiedNeighbors G J v = {u} then lam ^ J.card else 0) =
    ∑ J ∈ configurations G univ,
      if occupiedNeighbors G J u = {v} then lam ^ J.card else 0 := by
  rw [← sum_filter, ← sum_filter]
  apply sum_bij' (fun J _ => insert v (J.erase u))
    (fun J _ => insert u (J.erase v))
  · intro J hJ
    obtain ⟨hJ, hN⟩ := mem_filter.mp hJ
    exact mem_filter.mpr ⟨(singleton_exchange G J u v hJ hN).1,
      (singleton_exchange G J u v hJ hN).2.1⟩
  · intro J hJ
    obtain ⟨hJ, hN⟩ := mem_filter.mp hJ
    exact mem_filter.mpr ⟨(singleton_exchange G J v u hJ hN).1,
      (singleton_exchange G J v u hJ hN).2.1⟩
  · intro J hJ
    exact (singleton_exchange G J u v (mem_filter.mp hJ).1 (mem_filter.mp hJ).2).2.2.1
  · intro J hJ
    exact (singleton_exchange G J v u (mem_filter.mp hJ).1 (mem_filter.mp hJ).2).2.2.1
  · intro J hJ
    rw [(singleton_exchange G J u v (mem_filter.mp hJ).1 (mem_filter.mp hJ).2).2.2.2]

end D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge
