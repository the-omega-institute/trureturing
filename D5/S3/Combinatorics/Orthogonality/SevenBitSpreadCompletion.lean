/- GID: D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.result; instance=D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.orthogonal_seven
   digest: Unique full Lagrangian completion of every original eight-member partial spread. -/

import D5.S3.Combinatorics.Orthogonality.SevenBitCapacity
import D5.S3.Combinatorics.Orthogonality.PartialSpreadHoles

/-! The complete original six-dimensional even hyperplane is used. This is
universal completion of every eight-member partial spread, not one selected
spread or the paused seven/six-member nineteen-color case exclusions. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace D5.S3.Combinatorics.Orthogonality.SevenBitSpreadCompletion
open SevenBitGeometry

private def lagrangianGood (S : Finset Vector) : Bool :=
  decide (S.card ≤ 7 ∧ (S.card = 7 → LagrangianData S))
private def orthogonal (u v : Vector) : Bool := decide (dot u v = 0)
private def points : List Vector :=
  (List.finRange 128).filter (fun v => v ≠ 0 ∧ even v)

set_option maxHeartbeats 0 in
/-- Every seven-point orthogonal family in the entire original even
hyperplane is a full Lagrangian, with all closure and hyperplane data. -/
theorem orthogonal_seven (S : Finset Vector) (hS : S ⊆ evenPoints)
    (hcard : S.card = 7)
    (horth : ∀ x ∈ S, ∀ y ∈ S, dot x y = 0) : LagrangianData S := by
  have hcheck : CompatibleFamilyCheck.check lagrangianGood orthogonal 63
      ∅ points = true := by decide +kernel
  have hlen : points.length ≤ 63 := by decide +kernel
  have hs := CompatibleFamilyCheck.sound lagrangianGood orthogonal 63 ∅
    points hlen S (by intro x hx; simp only [points,List.mem_filter,List.mem_finRange,
      true_and,decide_eq_true_eq]; exact (Finset.mem_filter.mp (hS hx)).2)
    (by intro x hx y hy _; simp [orthogonal,horth x hx y hy]) hcheck
  have hp : S.card ≤ 7 ∧ (S.card = 7 → LagrangianData S) := by
    exact of_decide_eq_true (show lagrangianGood S = true from by
      simpa only [Finset.empty_union] using hs)
  exact hp.2 hcard

/-- All eight original full blocks have exactly one disjoint full ninth
completion. Its entire coordinate carrier is an actual totally isotropic
Submodule of finrank three; no basis-only or incidence proxy is returned. -/
theorem result (L : Fin 8 → Finset Vector) (hL : ∀ i, LagrangianData (L i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (L i) (L j)) :
    ∃! R : Finset Vector, LagrangianData R ∧
      (∀ i, Disjoint R (L i)) ∧
      R ∪ Finset.univ.biUnion L = evenPoints ∧
      ∃ U : Submodule (ZMod 2) Coordinates,
        Module.finrank (ZMod 2) U = 3 ∧
        (∀ u ∈ U, ∀ v ∈ U, dotProduct u v = 0) ∧
        (U : Set Coordinates) = bits '' ((insert 0 R : Finset Vector) : Set Vector) := by
  classical
  let R := PartialSpreadHoles.holes evenPoints L
  have hh := PartialSpreadHoles.result evenPoints (fun e v => dot e v = 0) L
    even_card (fun i => (hL i).1) (fun i => (hL i).2.1) hdisjoint
    hyperplane_card (fun e he i => (hL i).2.2.2.2 e he)
  have hsub : R ⊆ evenPoints := Finset.sdiff_subset
  have hR : LagrangianData R := orthogonal_seven R hsub hh.1 hh.2
  have hu : Finset.univ.biUnion L ⊆ evenPoints := by
    intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact (hL i).1 hi
  refine ⟨R,⟨hR,?_,?_,?_⟩,?_⟩
  · intro i
    apply Finset.disjoint_left.mpr
    intro x hx hi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hi⟩)
  · exact Finset.sdiff_union_of_subset hu
  · have hg := SevenBitCapacity.actual_lagrangian_geometry R hR
    exact ⟨SevenBitCapacity.actualLagrangian R hR,hg.1,hg.2,rfl⟩
  · intro R' hp
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      apply Finset.mem_sdiff.mpr
      refine ⟨hp.1.1 hx,?_⟩
      intro hi
      obtain ⟨i,_,hix⟩ := Finset.mem_biUnion.mp hi
      exact Finset.disjoint_left.mp (hp.2.1 i) hx hix
    · rw [hp.1.2.1,hh.1]

#print axioms result
end D5.S3.Combinatorics.Orthogonality.SevenBitSpreadCompletion
