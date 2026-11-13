/- GID: D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/CodeCentralizers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centralizer and normal-core obstructions for actual total perfect subgroup codes. -/

import D5.S3.Combinatorics.CayleySumCodes.NormalTransversal
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.NormalTransversal

variable {G : Type*} [Group G]

private theorem commutes_of_coset (H : Subgroup G) (T : Set G)
    (hn : NormalSubset T) (hc : Subgroup.IsComplement T (H : Set G))
    (a t : G) (ht : t ∈ T) (hm : (a * t * a⁻¹)⁻¹ * t ∈ H) :
    a * t = t * a := by
  obtain ⟨s, hs, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hc t
  have he : a * t * a⁻¹ = t := congrArg Subtype.val
    ((hu ⟨a * t * a⁻¹, hn a t ht⟩ hm).trans (hu ⟨t, ht⟩ (by simp)).symm)
  have he' := congrArg (fun x : G => x * a) he
  simpa [mul_assoc] using he'

private theorem core_transversal (H : Subgroup G) (T : Set G)
    (hn : NormalSubset T) (hc : Subgroup.IsComplement T (H : Set G)) :
    H.normalCore ≤ Subgroup.centralizer T := by
  intro a ha t ht
  apply (commutes_of_coset H T hn hc a t ht ?_).symm
  have hi : t⁻¹ * a⁻¹ * t ∈ H := by
    simpa using (H.normalCore.inv_mem ha) t⁻¹
  have hm := H.mul_mem (H.normalCore_le ha) hi
  simpa [mul_inv_rev, mul_assoc] using hm

/-- Every member of the normal core centralizes the entire connection set,
including both elements of the exceptional two-element branch. -/
theorem core [Finite G] (H : Subgroup G) (Y : Set G) (hn : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hn) H) :
    H.normalCore ≤ Subgroup.centralizer Y := by
  rcases transversal_cases H Y hn hc with ha | hb
  · exact core_transversal H Y hn ha.2
  · intro a ha y hy
    by_cases he : y = 1
    · simp [he]
    · exact core_transversal H (Y \ {1}) (by
        intro b t ht
        refine ⟨hn b t ht.1, ?_⟩
        intro h
        apply ht.2
        apply Set.mem_singleton_iff.mpr
        have hh := congrArg (fun z : G => b⁻¹ * z * b) (Set.mem_singleton_iff.mp h)
        simpa [mul_assoc] using hh) hb.2 ha y ⟨hy, he⟩

/-- H centralizes each member of Y intersect H. This needs no normality of H. -/
theorem internal [Finite G] (H : Subgroup G) (Y : Set G) (hn : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hn) H) :
    H ≤ Subgroup.centralizer (Y ∩ (H : Set G)) := by
  intro a ha y hy
  rcases transversal_cases H Y hn hc with hcase | hcase
  · apply (commutes_of_coset H Y hn hcase.2 a y hy.1 ?_).symm
    exact H.mul_mem (H.inv_mem (H.mul_mem (H.mul_mem ha hy.2) (H.inv_mem ha))) hy.2
  · by_cases he : y = 1
    · simp [he]
    · have hnorm : NormalSubset (Y \ {1}) := by
        intro b t ht
        refine ⟨hn b t ht.1, ?_⟩
        intro h
        apply ht.2
        apply Set.mem_singleton_iff.mpr
        have hh := congrArg (fun z : G => b⁻¹ * z * b) (Set.mem_singleton_iff.mp h)
        simpa [mul_assoc] using hh
      apply (commutes_of_coset H (Y \ {1}) hnorm hcase.2 a y ⟨hy.1, he⟩ ?_).symm
      exact H.mul_mem (H.inv_mem (H.mul_mem (H.mul_mem ha hy.2) (H.inv_mem ha))) hy.2

/-- For normal H, every connection element lying in H is central in G.
In particular the singleton in branch (a) is a central nonsquare. -/
theorem normal_inter_central [Finite G] (H : Subgroup G) [H.Normal]
    (Y : Set G) (hn : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hn) H) :
    Y ∩ (H : Set G) ⊆ Subgroup.center G := by
  intro y hy
  apply Subgroup.mem_center_iff.mpr
  intro a
  have hconj : a * y * a⁻¹ ∈ Y ∩ (H : Set G) :=
    ⟨hn a y hy.1, Subgroup.Normal.conj_mem (inferInstance : H.Normal) y hy.2 a⟩
  rcases transversal_cases H Y hn hc with ha | hb
  · exact commutes_of_coset H Y hn ha.2 a y hy.1
      (H.mul_mem (H.inv_mem hconj.2) hy.2)
  · by_cases he : y = 1
    · simp [he]
    · have hnorm : NormalSubset (Y \ {1}) := by
        intro b t ht
        refine ⟨hn b t ht.1, ?_⟩
        intro h
        apply ht.2
        apply Set.mem_singleton_iff.mpr
        have hh := congrArg (fun z : G => b⁻¹ * z * b) (Set.mem_singleton_iff.mp h)
        simpa [mul_assoc] using hh
      exact commutes_of_coset H (Y \ {1}) hnorm hb.2 a y ⟨hy.1, he⟩
        (H.mul_mem (H.inv_mem hconj.2) hy.2)

/-- A normal subgroup code with more than one connection element requires
at least two actual conjugacy classes, rather than merely two elements. -/
theorem two_classes [Finite G] (H : Subgroup G) [H.Normal]
    (Y : Set G) (hn : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hn) H) (hsize : 1 < Nat.card Y) :
    ∃ z ∈ Y, ∃ y ∈ Y, ¬IsConj z y := by
  classical
  have hz : ∃ z : G, z ∈ Y ∧ z ∈ H := by
    obtain ⟨_, ha | hb⟩ := (TotalPerfectCriterion.result H Y hn).mp hc
    · obtain ⟨z, hh, _, he⟩ := ha
      exact ⟨z, (he.symm ▸ Set.mem_singleton z).1, hh⟩
    · exact ⟨1, (hb.2 ⟨1, H.one_mem, by simp⟩).1, H.one_mem⟩
  obtain ⟨z, hzY, hzH⟩ := hz
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [Nat.card_eq_fintype_card] using hsize)
  obtain ⟨y, hy⟩ := exists_ne (⟨z, hzY⟩ : Y)
  refine ⟨z, hzY, y.1, y.2, ?_⟩
  intro hconj
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  have hcent := normal_inter_central H Y hn hc ⟨hzY, hzH⟩
  have he : a * z * a⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp hcent a]
    simp [mul_assoc]
  exact hy (Subtype.ext (ha.symm.trans he))

/-- A connected sum graph forces its connection set to generate G. Only
this direction is claimed; generation alone is not a connectedness test. -/
theorem connected_generates (Y : Set G) (hn : NormalSubset Y)
    (hc : (sumGraph Y hn).Connected) : Subgroup.closure Y = ⊤ := by
  have walk_mem (g h : G) (p : (sumGraph Y hn).Walk g h) :
      g ∈ Subgroup.closure Y → h ∈ Subgroup.closure Y := by
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      apply ih
      have hm := (Subgroup.closure Y).mul_mem ((Subgroup.closure Y).inv_mem hu)
        (Subgroup.subset_closure huv.2)
      simpa [mul_assoc] using hm
  apply top_unique
  intro g _
  obtain ⟨p⟩ := hc.preconnected 1 g
  exact walk_mem 1 g p (Subgroup.one_mem _)

/-- The retained connected-code obstruction uses the actual normal core
and center: a connected total-code sum graph forces core(H) into Z(G). -/
theorem connected_core [Finite G] (H : Subgroup G) (Y : Set G) (hn : NormalSubset Y)
    (hc : IsTotalPerfectCode (sumGraph Y hn) H)
    (hconn : (sumGraph Y hn).Connected) : H.normalCore ≤ Subgroup.center G := by
  have hg := connected_generates Y hn hconn
  have he : Subgroup.centralizer Y = Subgroup.center G := by
    rw [← Subgroup.centralizer_closure Y, hg]
    exact Subgroup.centralizer_univ
  exact he ▸ core H Y hn hc

#print axioms core
#print axioms internal
#print axioms normal_inter_central
#print axioms two_classes
#print axioms connected_generates
#print axioms connected_core

end D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers
