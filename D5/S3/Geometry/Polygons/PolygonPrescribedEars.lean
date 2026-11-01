/- GID: D5/S3/Geometry/Polygons/PolygonPrescribedEars
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonPrescribedEars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact prescribed complete ear sets on whole native cyclic triangulations. -/

import D5.S3.Geometry.Polygons.PolygonEarContraction
import D5.S3.Geometry.Polygons.PolygonCatalanSupplier
import D5.S3.Geometry.Polygons.PolygonConditionedFan

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace D5.S3.Geometry.Polygons.PolygonPrescribedEars
open ClusterAlgebras.TypeA

private def doubleFan (B k : ℤ) : Finset (ℤ × ℤ) :=
  ((Icc 2 k).image fun j => (0,j)) ∪
    ((Icc (k+2) B).image fun j => (k,j))

private lemma mem_doubleFan {B k a b : ℤ} :
    (a,b) ∈ doubleFan B k ↔
      (a=0 ∧ 2 ≤ b ∧ b ≤ k) ∨ (a=k ∧ k+2 ≤ b ∧ b ≤ B) := by
  simp only [doubleFan, mem_union, mem_image, mem_Icc, Prod.mk.injEq]
  constructor
  · rintro (⟨j,hj,h0,hb⟩ | ⟨j,hj,hk,hb⟩)
    · exact .inl ⟨h0.symm, hb ▸ hj.1, hb ▸ hj.2⟩
    · exact .inr ⟨hk.symm, hb ▸ hj.1, hb ▸ hj.2⟩
  · rintro (⟨rfl,hb,hk⟩ | ⟨rfl,hb,hB⟩)
    · exact .inl ⟨b,⟨hb,hk⟩,rfl,rfl⟩
    · exact .inr ⟨b,⟨hb,hB⟩,rfl,rfl⟩

private theorem doubleFan_triangulation {B k : ℤ} (hk : 2 ≤ k) (hB : k+1 ≤ B) :
    IsIntervalTriangulation 0 B (doubleFan B k) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,b⟩ hp
    rw [mem_doubleFan] at hp
    rw [mk_mem_intervalDiagonals_iff]
    rcases hp with ⟨rfl,hb,hbk⟩ | ⟨rfl,hb,hbB⟩ <;> omega
  · rintro ⟨a,b⟩ hp ⟨c,d⟩ hq
    rw [mem_doubleFan] at hp hq
    simp only [Interleave]
    rcases hp with ⟨rfl,hb,hbk⟩ | ⟨rfl,hb,hbB⟩ <;>
      rcases hq with ⟨rfl,hd,hdk⟩ | ⟨rfl,hd,hdB⟩ <;> omega
  · rintro ⟨a,b⟩ hp hout
    rw [mk_mem_intervalDiagonals_iff] at hp
    rw [mem_doubleFan] at hout
    by_cases ha : a=0
    · subst a
      refine ⟨(k,B),mem_doubleFan.mpr (.inr ⟨rfl,?_,le_rfl⟩),?_⟩
      · omega
      · simp only [Interleave]; omega
    by_cases hak : a=k
    · subst a
      exact False.elim (hout (.inr ⟨rfl,hp.2.2.1,hp.2.1⟩))
    by_cases hlt : a<k
    · by_cases hbk : b≤k
      · refine ⟨(0,a+1),mem_doubleFan.mpr (.inl ⟨rfl,?_,?_⟩),?_⟩
        · omega
        · omega
        · simp only [Interleave]; omega
      · refine ⟨(0,k),mem_doubleFan.mpr (.inl ⟨rfl,hk,le_rfl⟩),?_⟩
        simp only [Interleave]; omega
    · refine ⟨(k,a+1),mem_doubleFan.mpr (.inr ⟨rfl,?_,?_⟩),?_⟩
      · omega
      · omega
      · simp only [Interleave]; omega


open D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Actual

private theorem native_doubleFan {n : ℕ} [NeZero n] (hn : 6 ≤ n)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k+2 ≤ n) :
    ∃ T : Finset (Sym2 (ZMod n)),
      PolygonEarSlide.Carrier.IsTriangulation T ∧
      EarCenters T = {1, ((k+1 : ℕ) : ZMod n)} := by
  have hI := doubleFan_triangulation (B := (n : ℤ)-1) (k := (k : ℤ))
    (by omega) (by omega)
  obtain ⟨T,hT,hS⟩ := (bijOn_basePosTri (0 : ZMod n)).surjOn hI
  have hTc : PolygonEarSlide.Carrier.IsTriangulation T :=
    ⟨hT.isDiagonal,hT.noncrossing,hT.maximal⟩
  refine ⟨T,hTc,?_⟩
  ext j
  rw [mem_earCenters, mem_insert, mem_singleton]
  have hmem : ear j ∈ T ↔ basePosSeg 0 (ear j) ∈ doubleFan ((n:ℤ)-1) k := by
    rw [← hS]
    change ear j ∈ T ↔ basePosSeg 0 (ear j) ∈ T.image (basePosSeg 0)
    constructor
    · exact mem_image_of_mem _
    · intro h
      obtain ⟨e,he,heq⟩ := mem_image.mp h
      exact (basePosSeg_injective (0 : ZMod n) heq) ▸ he
  rw [hmem]
  have hjlt := ZMod.val_lt j
  have hone : (1 : ZMod n).val=1 := ZMod.val_one'' (by omega)
  have hkj : (((k+1 : ℕ) : ZMod n)).val=k+1 := ZMod.val_natCast_of_lt (by omega)
  have hjeq : j=1 ↔ j.val=1 := by
    constructor
    · intro h; rw [h,hone]
    · intro h; apply ZMod.val_injective n; rwa [hone]
  have hkeq : j=((k+1 : ℕ) : ZMod n) ↔ j.val=k+1 := by
    constructor
    · intro h; rw [h,hkj]
    · intro h; apply ZMod.val_injective n; rwa [hkj]
  rw [hjeq,hkeq]
  have hp : (j-1).val = if j.val=0 then n-1 else j.val-1 := by
    by_cases hz : j.val=0
    · have he : j=0 := (ZMod.val_eq_zero j).mp hz
      subst j
      simp only [ZMod.val_zero, ite_true, zero_sub]
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 from NeZero.ne n)
      subst n
      simp [ZMod.val_neg_one]
    · rw [ite_eq_right hz,ZMod.val_sub (by omega),hone]
  have hs : (j+1).val = if j.val+1=n then 0 else j.val+1 := by
    rw [ZMod.val_add,hone]
    split_ifs with he
    · rw [he,Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  simp only [ear,basePosSeg_mk,basePos,sub_zero,hp,hs]
  clear hI hT hS hTc hmem hone hkj hjeq hkeq hp hs
  by_cases hz : j.val=0
  · have hlast : ¬(j.val+1=n) := by omega
    simp only [hz,ite_true,ite_false,show ¬(0+1=n) by omega,
      mem_doubleFan]
    omega
  · by_cases hlast : j.val+1=n
    · simp only [ite_eq_right hz,ite_eq_left hlast,Nat.cast_zero,
        min_eq_right (by omega : (0:ℤ) ≤ ↑(j.val-1)),
        max_eq_left (by omega : (0:ℤ) ≤ ↑(j.val-1)),mem_doubleFan]
      have hlow : (2:ℤ) ≤ ((j.val-1:ℕ):ℤ) := by omega
      have hk0 : ¬((0:ℤ)=(k:ℤ)) := by omega
      simp only [true_and,hlow,hk0,false_and,or_false]
      norm_cast
      omega
    · simp only [ite_eq_right hz,ite_eq_right hlast,
        min_eq_left (by omega : ((j.val-1:ℕ):ℤ) ≤ ↑(j.val+1)),
        max_eq_right (by omega : ((j.val-1:ℕ):ℤ) ≤ ↑(j.val+1)),mem_doubleFan]
      omega



open PolygonEarSlide.Carrier PolygonEarContraction

private theorem native_two_ears {n : ℕ} [NeZero n] (hn : 6 ≤ n)
    (i j : ZMod n) (hij : i ≠ j) (hc : ¬Cross (ear i) (ear j)) :
    ∃ T : Finset (Sym2 (ZMod n)), IsTriangulation T ∧ EarCenters T = {i,j} := by
  let a : ZMod n := 1-i
  let b : ZMod n := j+a
  have hi : i+a=1 := by dsimp [a]; ring
  have hb1 : b ≠ 1 := by
    intro h
    apply hij
    have : j+a=i+a := h.trans hi.symm
    exact (add_right_cancel this).symm
  have hcross : ¬Cross (ear (1 : ZMod n)) (ear b) := by
    intro h
    apply hc
    apply cross_ear_shift_iff.mp
    simpa only [hi] using h
  have hb0 : b ≠ 0 := by
    intro h
    apply hcross
    rw [h]
    exact (local_crossings hn).2.2
  have hb2 : b ≠ 2 := by
    intro h
    apply hcross
    rw [h]
    exact cross_symm (local_crossings hn).1
  have hblt := ZMod.val_lt b
  have hbge : 3 ≤ b.val := by
    have h0 : b.val ≠ 0 := fun h => hb0 ((ZMod.val_eq_zero b).mp h)
    have h1 : b.val ≠ 1 := by
      intro h
      apply hb1
      apply ZMod.val_injective n
      rwa [ZMod.val_one'' (show n ≠ 1 by omega)]
    have h2 : b.val ≠ 2 := by
      intro h
      apply hb2
      apply ZMod.val_injective n
      rwa [ZMod.val_natCast_of_lt (show 2<n by omega)]
    omega
  obtain ⟨U,hU,hE⟩ := native_doubleFan hn (b.val-1) (by omega) (by omega)
  have hbcast : (((b.val-1+1 : ℕ)) : ZMod n)=b := by
    rw [Nat.sub_add_cancel (by omega),ZMod.natCast_zmod_val]
  rw [hbcast] at hE
  refine ⟨shiftChords U (-a),isTriangulation_map_add hU (-a),?_⟩
  ext x
  rw [earCenters_shift_mem_iff,hE]
  simp only [neg_neg,mem_insert,mem_singleton]
  constructor
  · rintro (h | h)
    · left
      exact add_right_cancel (h.trans hi.symm)
    · right
      exact add_right_cancel h
  · rintro (rfl | rfl)
    · exact .inl hi
    · exact .inr rfl

private theorem expand_exact {m : ℕ} [NeZero m] (hm : 6 ≤ m)
    (P : Finset (ZMod (m+1))) (hP : Compatible P) (h1 : 1 ∈ P)
    {U : Finset (Sym2 (ZMod m))} (hU : IsTriangulation U)
    (hE : EarCenters U = reducedCenters P) :
    IsTriangulation (expand U) ∧ EarCenters (expand U) = P := by
  let e := forcedOneEquiv hm P hP h1
  let W := e.symm ⟨U,hU,by rw [hE]⟩
  have hT : IsTriangulation (expand U) := W.property.1
  have hsub : P ⊆ EarCenters (expand U) := W.property.2
  have hC : Compatible (EarCenters (expand U)) := by
    intro i hi j hj _
    exact hT.noncrossing _ (mem_earCenters.mp hi) _ (mem_earCenters.mp hj)
  have h1C : 1 ∈ EarCenters (expand U) := hsub h1
  let f := forcedOneEquiv hm (EarCenters (expand U)) hC h1C
  have hsubC := (f ⟨expand U,hT,Subset.rfl⟩).property.2
  change reducedCenters (EarCenters (expand U)) ⊆ EarCenters (reduce (expand U)) at hsubC
  rw [reduce_expand (by omega) hU,hE] at hsubC
  have hcard := card_le_card hsubC
  rw [reduced_centres_card hm h1C,reduced_centres_card hm h1] at hcard
  refine ⟨hT,eq_of_subset_of_card_le hsub ?_⟩
  have hpos := card_pos.mpr (show P.Nonempty from ⟨1,h1⟩)
  omega

private theorem exists_exact {n : ℕ} [NeZero n] (P : Finset (ZMod n))
    (hP : Compatible P) (hcard : 2 ≤ P.card) (hsize : 6 ≤ n-P.card) :
    ∃ T : Finset (Sym2 (ZMod n)), IsTriangulation T ∧ EarCenters T = P := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases htwo : P.card=2
    · obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp htwo
      exact native_two_ears (by omega) i j hij (hP (by simp) (by simp) hij)
    have hnon : P.Nonempty := card_pos.mp (by omega)
    obtain ⟨i,hi⟩ := hnon
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have hm : 6 ≤ m := by omega
    letI : NeZero m := ⟨by omega⟩
    let a : ZMod (m+1) := 1-i
    let S := shiftSet P a
    have hScard : S.card=P.card := card_image_of_injective _ (add_left_injective a)
    have hi1 : i+a=1 := by dsimp [a]; ring
    have h1 : (1 : ZMod (m+1)) ∈ S := by
      rw [← hi1]
      exact shiftSet_mem_iff.mpr hi
    have hS : Compatible S := by
      intro x hx y hy hxy hc
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
      exact hP hu hv (fun h => hxy (congrArg (fun z => z+a) h))
        (cross_ear_shift_iff.mp hc)
    have hRcard := reduced_centres_card hm h1
    have hRsize : 6 ≤ m-(reducedCenters S).card := by omega
    have hRtwo : 2 ≤ (reducedCenters S).card := by omega
    obtain ⟨U,hU,hE⟩ := ih m (by omega) (reducedCenters S)
      (reduced_centres_compatible hm hS h1) hRtwo hRsize
    obtain ⟨hT,hTE⟩ := expand_exact hm S hS h1 hU hE
    refine ⟨shiftChords (expand U) (-a),isTriangulation_map_add hT (-a),?_⟩
    ext j
    rw [earCenters_shift_mem_iff,hTE]
    simp only [neg_neg]
    exact shiftSet_mem_iff

/-- Every compatible prescribed set in the stated range is the complete actual ear set. -/
theorem prescribed_complete_ears {n : ℕ} [NeZero n] (hn : 14 ≤ n)
    (P : Finset (ZMod n)) (hP : Compatible P) (hcard : 3 ≤ P.card)
    (hsize : 6 ≤ n-P.card) :
    ∃ T : Finset (Sym2 (ZMod n)), IsTriangulation T ∧ EarCenters T = P := by
  exact exists_exact P hP (by omega) hsize

end D5.S3.Geometry.Polygons.PolygonPrescribedEars
