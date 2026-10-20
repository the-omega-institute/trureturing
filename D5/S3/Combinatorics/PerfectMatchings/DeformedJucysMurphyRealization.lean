/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRealization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.PossibleTypes]
   utility: none
   digest: Every positive partition is the complete type of an actual native matching. -/
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyComponents
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-! Matching realization retains repeated parts and fixed singleton components. -/

noncomputable section
namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRealization
open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

attribute [local instance] Classical.propDecidable

theorem orbit_parts_filter {A : Type*} [Fintype A] [DecidableEq A] (σ : Perm A) :
    ((Finpartition.ofSetoid (Perm.SameCycle.setoid σ)).parts.val.map
      Finset.card).filter (fun n => 2 ≤ n) = σ.cycleType := by
  classical
  let Q := Finpartition.ofSetoid (Perm.SameCycle.setoid σ)
  have hpart (c : Perm A) (hc : c ∈ σ.cycleFactorsFinset) (x : A)
      (hx : x ∈ c.support) : Q.part x = c.support := by
    have hσx : σ x ≠ x := Perm.mem_support.mp
      (Perm.mem_cycleFactorsFinset_support_le hc hx)
    have he := (Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c hc x).mpr hx
    rw [he]
    ext y
    exact Finpartition.mem_part_ofSetoid_iff_rel.trans
      (Perm.mem_support_cycleOf_iff' hσx).symm
  have hinj : Set.InjOn (fun c : Perm A => c.support) σ.cycleFactorsFinset := by
    intro c hc d hd he
    obtain ⟨x,hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    change c.support = d.support at he
    have hxd : x ∈ d.support := by rw [← he]; exact hx
    exact ((Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c hc x).mpr hx).trans
      ((Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ d hd x).mpr hxd).symm
  have himage : Q.parts.filter (fun C => 2 ≤ C.card) =
      σ.cycleFactorsFinset.image (fun c => c.support) := by
    ext C
    constructor
    · intro hC
      obtain ⟨hC,hcard⟩ := Finset.mem_filter.mp hC
      obtain ⟨x,hx⟩ := Q.nonempty_of_mem_parts hC
      have he : Q.part x = C := Q.part_eq_of_mem hC hx
      have hσx : σ x ≠ x := by
        intro hf
        have hs : Q.part x = {x} := by
          ext y
          rw [Finpartition.mem_part_ofSetoid_iff_rel, Finset.mem_singleton]
          exact ⟨fun h => (h.eq_of_left hf).symm, fun h => h ▸ Perm.SameCycle.refl σ x⟩
        rw [← he, hs, Finset.card_singleton] at hcard
        omega
      have hc : σ.cycleOf x ∈ σ.cycleFactorsFinset :=
        Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hσx)
      have hx' : x ∈ (σ.cycleOf x).support :=
        (Perm.mem_support_cycleOf_iff' hσx).mpr (Perm.SameCycle.refl σ x)
      exact Finset.mem_image.mpr ⟨σ.cycleOf x,hc,(hpart _ hc x hx').symm.trans he⟩
    · intro hC
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨x,hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
      exact Finset.mem_filter.mpr ⟨(hpart c hc x hx) ▸
        (Q.part_mem.mpr (Finset.mem_univ x)),
        (Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support⟩
  rw [Multiset.filter_map]
  change (Q.parts.filter (fun C => 2 ≤ C.card)).val.map Finset.card = _
  rw [himage, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rfl

private theorem positive_reconstruction (s : Multiset ℕ)
    (hs : ∀ r ∈ s, 0 < r) :
    s = s.filter (fun r => 2 ≤ r) +
      Multiset.replicate (s.sum - (s.filter (fun r => 2 ≤ r)).sum) 1 := by
  let t := s.filter (fun r => ¬2 ≤ r)
  have ht : t = Multiset.replicate t.card 1 := by
    apply Multiset.eq_replicate.mpr
    refine ⟨rfl, ?_⟩
    intro r hr
    have hm := Multiset.mem_filter.mp hr
    have hp := hs r hm.1
    omega
  have he := Multiset.filter_add_not (p := fun r => 2 ≤ r) s
  have hsum := congrArg Multiset.sum he
  change (s.filter (fun r => 2 ≤ r) + t).sum = s.sum at hsum
  rw [Multiset.sum_add, ht, Multiset.sum_replicate] at hsum
  simp only [nsmul_eq_mul, Nat.cast_id, mul_one] at hsum
  have hcard : t.card = s.sum - (s.filter (fun r => 2 ≤ r)).sum := by omega
  calc
    s = s.filter (fun r => 2 ≤ r) + t := he.symm
    _ = _ := by rw [ht, hcard]

/-- Every partition, including the empty partition and any repeated singleton
parts, is realized on the original native `P k` domain. -/
theorem matching_realization {k : ℕ} (ρ : Nat.Partition k) :
    ∃ p : P k, ct p = ρ := by
  classical
  have hsumFilter : (ρ.parts.filter (fun r => 2 ≤ r)).sum ≤ k := by
    have h := congrArg Multiset.sum
      (Multiset.filter_add_not (p := fun r => 2 ≤ r) ρ.parts)
    rw [Multiset.sum_add, ρ.parts_sum] at h
    omega
  obtain ⟨σ,hσ⟩ := (Perm.exists_with_cycleType_iff (α := Fin k)
    (m := ρ.parts.filter (fun r => 2 ≤ r))).mpr ⟨by
      simpa only [Fintype.card_fin] using hsumFilter,
      fun r hr => (Multiset.mem_filter.mp hr).2⟩
  refine ⟨oriented σ, Nat.Partition.ext ?_⟩
  rw [ct_oriented]
  let Q := Finpartition.ofSetoid (Perm.SameCycle.setoid σ)
  have hp : ∀ r ∈ Q.parts.val.map Finset.card, 0 < r := by
    intro r hr
    obtain ⟨C,hC,rfl⟩ := Multiset.mem_map.mp hr
    exact Finset.card_pos.mpr (Q.nonempty_of_mem_parts hC)
  have hsum : (Q.parts.val.map Finset.card).sum = k := by
    rw [← Finset.sum_eq_multiset_sum]
    simpa only [Finset.card_univ, Fintype.card_fin] using Q.sum_card_parts
  rw [positive_reconstruction _ hp,
    positive_reconstruction ρ.parts (fun r hr => ρ.parts_pos hr)]
  rw [orbit_parts_filter σ, hσ, hsum, ρ.parts_sum]

end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRealization
