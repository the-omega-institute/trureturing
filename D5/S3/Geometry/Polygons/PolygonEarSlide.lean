/- GID: D5/S3/Geometry/Polygons/PolygonEarSlide
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlide
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact observed-ear trace transport and cyclic complete conditioned ear-slide equivalences. -/

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/cluster-algebras-polygon-third-party.md.
Authors: Ashvin A. Swaminathan.

The cyclic translation lemmas below are adapted from the rotation proof in
`ClusterAlgebras/TypeA/Polygon.lean` and
`ClusterAlgebras/Plabic/CornerTriangulation.lean` from AxiomMath/ClusterAlgebras,
revision a9174706bce3bcb0fa342b4614f98ef2acb7f91c.  The adapted polygon carrier
is owned by `PolygonEarSlideGeometry.lean`.  The ear-slide declarations are new
and use that carrier directly with this repository's pinned Mathlib.
-/

import D5.S3.Geometry.Polygons.PolygonEarSlideMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Geometry.Polygons.PolygonEarSlide
open Carrier

namespace Actual

variable {n : ℕ} [NeZero n]

def IsRemote (i : ZMod n) : Prop := i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3

def EarCenters (T : Finset (Sym2 (ZMod n))) : Finset (ZMod n) :=
  univ.filter (fun i => ear i ∈ T)

@[simp] lemma mem_earCenters {T : Finset (Sym2 (ZMod n))} {i : ZMod n} :
    i ∈ EarCenters T ↔ ear i ∈ T := by simp [EarCenters]

def E_K (K : Finset (ZMod n)) : Finset (ZMod n) :=
  univ.filter (fun i => i ∉ K ∧ ∀ k ∈ K, ¬Cross (ear i) (ear k))

def ConditionFiber (P Q J X : Finset (ZMod n)) : Type :=
  {T : Finset (Sym2 (ZMod n)) //
    IsTriangulation T ∧ P ⊆ EarCenters T ∧
      Disjoint Q (EarCenters T) ∧ EarCenters T ∩ J = X}

lemma remote_of_K (hn : 6 ≤ n) {K J : Finset (ZMod n)}
    (hJ : J ⊆ E_K K) (h1 : (1 : ZMod n) ∈ J) (h2 : (2 : ZMod n) ∈ J)
    {i : ZMod n} (hi : i ∈ K) : IsRemote i := by
  have h1E := mem_filter.mp (hJ h1)
  have h2E := mem_filter.mp (hJ h2)
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    exact h1E.2.2 0 hi (by
      simpa [sEar, e₀, ear, ear_one, ear_zero] using (local_crossings hn).2.2)
  have hi1 : i ≠ 1 := by
    intro hi1
    subst i
    exact h1E.2.1 hi
  have hi2 : i ≠ 2 := by
    intro hi2
    subst i
    exact h2E.2.1 hi
  have hi3 : i ≠ 3 := by
    intro hi3
    subst i
    exact h2E.2.2 3 hi (by
      simpa [tEar, uEar, ear, ear_two, ear_three] using (local_crossings hn).2.1)
  exact ⟨hi0, hi1, hi2, hi3⟩

lemma chordSwap_ear_remote (hn : 14 ≤ n) {i : ZMod n} (hi : IsRemote i) :
    chordSwap (ear i) = ear i := by
  have hm1 : i - 1 ≠ 1 := by
    intro h
    apply hi.2.2.1
    calc
      i = (i - 1) + 1 := by ring
      _ = 1 + 1 := congrArg (fun z : ZMod n => z + 1) h
      _ = 2 := by ring
  have hm2 : i - 1 ≠ 2 := by
    intro h
    apply hi.2.2.2
    calc
      i = (i - 1) + 1 := by ring
      _ = 2 + 1 := congrArg (fun z : ZMod n => z + 1) h
      _ = 3 := by ring
  have hp1 : i + 1 ≠ 1 := by
    intro h
    apply hi.1
    calc
      i = (i + 1) - 1 := by ring
      _ = 1 - 1 := congrArg (fun z : ZMod n => z - 1) h
      _ = 0 := by ring
  have hp2 : i + 1 ≠ 2 := by
    intro h
    apply hi.2.1
    calc
      i = (i + 1) - 1 := by ring
      _ = 2 - 1 := congrArg (fun z : ZMod n => z - 1) h
      _ = 1 := by ring
  simp [ear, chordSwap, vertexSwap, Equiv.swap_apply_def, hm1, hm2, hp1, hp2]

lemma earCenters_remote_phi (hn : 14 ≤ n) {T : Finset (Sym2 (ZMod n))}
    {i : ZMod n} (hi : IsRemote i) :
    i ∈ EarCenters (phi T) ↔ i ∈ EarCenters T := by
  rw [mem_earCenters, mem_earCenters]
  constructor
  · intro h
    simp only [phi, mem_insert] at h
    rcases h with h | h
    · have hfix := chordSwap_ear_remote hn hi
      rw [h] at hfix
      rw [chordSwap_sEar (show 6 ≤ n by omega)] at hfix
      exfalso
      apply (isDiagonal_sEar (show 6 ≤ n by omega)).2
      exact ⟨0, by simpa using hfix.symm⟩
    · obtain ⟨d, hd, hde⟩ := mem_image.mp h
      have hde' : d = ear i := by
        calc
          d = chordSwap (chordSwap d) := by simp
          _ = chordSwap (ear i) := congrArg chordSwap hde
          _ = ear i := chordSwap_ear_remote hn hi
      simpa [hde'] using mem_of_mem_erase hd
  · intro h
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨ear i, ?_, ?_⟩
    · apply mem_erase.mpr
      constructor
      · intro hti
        have hfix := chordSwap_ear_remote hn hi
        rw [hti] at hfix
        rw [chordSwap_tEar (show 6 ≤ n by omega)] at hfix
        exfalso
        apply (isDiagonal_tEar (show 6 ≤ n by omega)).2
        exact ⟨2, by
          calc
            tEar (n := n) = s(2, 3) := hfix.symm
            _ = s(2, (2 : ZMod n) + 1) := by rw [show (2 : ZMod n) + 1 = 3 by ring]⟩
      · exact h
    · exact chordSwap_ear_remote hn hi

lemma earCenters_remote_psi (hn : 14 ≤ n) {T : Finset (Sym2 (ZMod n))}
    {i : ZMod n} (hi : IsRemote i) :
    i ∈ EarCenters (psi T) ↔ i ∈ EarCenters T := by
  rw [mem_earCenters, mem_earCenters]
  constructor
  · intro h
    simp only [psi, mem_insert] at h
    rcases h with h | h
    · have hfix := chordSwap_ear_remote hn hi
      rw [h] at hfix
      rw [chordSwap_tEar (show 6 ≤ n by omega)] at hfix
      exfalso
      apply (isDiagonal_tEar (show 6 ≤ n by omega)).2
      exact ⟨2, by
        calc
          tEar (n := n) = s(2, 3) := hfix.symm
          _ = s(2, (2 : ZMod n) + 1) := by
            rw [show (2 : ZMod n) + 1 = 3 by ring]⟩
    · obtain ⟨d, hd, hde⟩ := mem_image.mp h
      have hde' : d = ear i := by
        calc
          d = chordSwap (chordSwap d) := by simp
          _ = chordSwap (ear i) := congrArg chordSwap hde
          _ = ear i := chordSwap_ear_remote hn hi
      simpa [hde'] using mem_of_mem_erase hd
  · intro h
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨ear i, ?_, chordSwap_ear_remote hn hi⟩
    apply mem_erase.mpr
    constructor
    · intro hsi
      have hfix := chordSwap_ear_remote hn hi
      rw [hsi] at hfix
      rw [chordSwap_sEar (show 6 ≤ n by omega)] at hfix
      exfalso
      apply (isDiagonal_sEar (show 6 ≤ n by omega)).2
      exact ⟨0, by simpa using hfix.symm⟩
    · exact h

lemma trace_phi (hn : 14 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T)
    {J R : Finset (ZMod n)} (hJ0 : (0 : ZMod n) ∉ J)
    (hJ1 : (1 : ZMod n) ∈ J) (hJ2 : (2 : ZMod n) ∈ J)
    (hR : R ⊆ ((J.erase 1).erase 2).erase 3)
    (htrace : EarCenters T ∩ J = insert 2 R) :
    EarCenters (phi T) ∩ (J.erase 2).erase 3 = insert 1 R := by
  have h12 : (1 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h13 : (1 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have hsT : sEar (n := n) ∉ T := by
    intro hs
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hs
      (local_crossings (show 6 ≤ n by omega)).1
  have huT : ear (3 : ZMod n) ∉ T := by
    intro hu
    exact hT.noncrossing (tEar (n := n)) ht (uEar (n := n)) hu
      (local_crossings (show 6 ≤ n by omega)).2.1
  ext i
  constructor
  · intro hi
    rcases mem_inter.mp hi with ⟨hiPhi, hiDom⟩
    rcases mem_erase.mp hiDom with ⟨hi3, hiDom2⟩
    rcases mem_erase.mp hiDom2 with ⟨hi2, hiJ⟩
    by_cases hi1 : i = 1
    · exact mem_insert.mpr (Or.inl hi1)
    · apply mem_insert.mpr
      right
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      have hiT : i ∈ EarCenters T := (earCenters_remote_phi hn hrem).mp hiPhi
      have hiR : i ∈ insert 2 R := by
        apply (Finset.ext_iff.mp htrace i).mp
        exact mem_inter.mpr ⟨hiT, hiJ⟩
      simpa [hi2] using hiR
  · intro hi
    rcases mem_insert.mp hi with hi1 | hiR
    · subst i
      apply mem_inter.mpr
      constructor
      · rw [mem_earCenters]
        simpa [sEar, ear_one, phi] using (mem_insert_self :
          sEar (n := n) ∈ phi T)
      · apply mem_erase.mpr
        exact ⟨h13, mem_erase.mpr ⟨h12, hJ1⟩⟩
    · have hiR' := hR hiR
      rcases mem_erase.mp hiR' with ⟨hi3, hiR2⟩
      rcases mem_erase.mp hiR2 with ⟨hi2, hiR1⟩
      rcases mem_erase.mp hiR1 with ⟨hi1, hiJ⟩
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      apply mem_inter.mpr
      constructor
      · apply (earCenters_remote_phi hn hrem).mpr
        exact (mem_inter.mp ((Finset.ext_iff.mp htrace i).mpr
          (mem_insert_of_mem hiR))).1
      · exact mem_erase.mpr ⟨hi3, mem_erase.mpr ⟨hi2, hiJ⟩⟩

lemma s_not_mem_psi (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U) :
    sEar (n := n) ∉ psi U := by
  intro h
  simp only [psi, mem_insert] at h
  rcases h with h | h
  · exact not_cross_self _ ((by simpa [h] using (local_crossings hn).1))
  · obtain ⟨d, hd, hde⟩ := mem_image.mp h
    exact chordSwap_ne_sEar_of_diagonal hn
      (hU.isDiagonal d (mem_of_mem_erase hd)) hde

lemma trace_psi (hn : 14 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U)
    {J R : Finset (ZMod n)} (hJ0 : (0 : ZMod n) ∉ J)
    (hJ1 : (1 : ZMod n) ∈ J) (hJ2 : (2 : ZMod n) ∈ J)
    (hR : R ⊆ ((J.erase 1).erase 2).erase 3)
    (htrace : EarCenters U ∩ (J.erase 2).erase 3 = insert 1 R) :
    EarCenters (psi U) ∩ J = insert 2 R := by
  have htU : tEar (n := n) ∉ U := by
    intro ht
    exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) ht
      (cross_symm (local_crossings (show 6 ≤ n by omega)).1)
  have huPsi : ear (3 : ZMod n) ∉ psi U := by
    intro hu
    have hpsi := psi_isTriangulation (show 6 ≤ n by omega) hU hs
    exact hpsi.noncrossing (tEar (n := n)) (by simp [psi])
      (uEar (n := n)) hu (local_crossings (show 6 ≤ n by omega)).2.1
  ext i
  constructor
  · intro hi
    rcases mem_inter.mp hi with ⟨hiPsi, hiJ⟩
    by_cases hi2 : i = 2
    · exact mem_insert.mpr (Or.inl hi2)
    · apply mem_insert.mpr
      right
      have hi3 : i ≠ 3 := by
        intro hi3
        subst i
        exact huPsi (by simpa [uEar, ear_three] using hiPsi)
      have hi1 : i ≠ 1 := by
        intro hi1
        subst i
        exact s_not_mem_psi (show 6 ≤ n by omega) hU hs
          (by simpa [sEar, ear_one] using hiPsi)
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      have hiU : i ∈ EarCenters U := (earCenters_remote_psi hn hrem).mp hiPsi
      have hiR : i ∈ insert 1 R := by
        apply (Finset.ext_iff.mp htrace i).mp
        exact mem_inter.mpr ⟨hiU, mem_erase.mpr ⟨hi3, mem_erase.mpr ⟨hi2, hiJ⟩⟩⟩
      simpa [hi1] using hiR
  · intro hi
    rcases mem_insert.mp hi with hi2 | hiR
    · subst i
      apply mem_inter.mpr
      constructor
      · rw [mem_earCenters]
        simp [psi, tEar, ear_two]
      · exact hJ2
    · have hiR' := hR hiR
      rcases mem_erase.mp hiR' with ⟨hi3, hiR2⟩
      rcases mem_erase.mp hiR2 with ⟨hi2, hiR1⟩
      rcases mem_erase.mp hiR1 with ⟨hi1, hiJ⟩
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      apply mem_inter.mpr
      constructor
      · apply (earCenters_remote_psi hn hrem).mpr
        exact (mem_inter.mp ((Finset.ext_iff.mp htrace i).mpr
          (mem_insert_of_mem hiR))).1
      · exact hiJ

/-! Cyclic translations are used to remove the temporary choice of the block origin. -/

def rotationBasePos (c v : ZMod n) : ℤ := ((v - c).val : ℤ)

lemma rotationBasePos_eq_ite (c v : ZMod n) :
    rotationBasePos c v =
      if c.val ≤ v.val then (v.val : ℤ) - c.val
      else (v.val : ℤ) - c.val + n := by
  unfold rotationBasePos
  split_ifs with h
  · rw [ZMod.val_sub h]
    push_cast [h]
    ring
  · have hv : v - c + c = v := by ring
    have h1 : n ≤ (v - c).val + c.val := by
      by_contra h2
      have h3 := ZMod.val_add_of_lt (not_le.mp h2)
      rw [hv] at h3
      have h4 := ZMod.val_lt (v - c)
      omega
    have h3 := ZMod.val_add_of_le h1
    rw [hv] at h3
    have h4 := ZMod.val_lt (v - c)
    omega

lemma rotation_sbtw_iff_val (x y z : ZMod n) :
    sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨
      (y.val < z.val ∧ z.val < x.val) ∨ (z.val < x.val ∧ x.val < y.val) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact Fin.sbtw_iff

lemma rotation_sbtw_iff_basePos (c x y z : ZMod n) :
    sbtw x y z ↔ sbtw (rotationBasePos c x)
      (rotationBasePos c y) (rotationBasePos c z) := by
  rw [rotation_sbtw_iff_val, Int.sbtw_iff, rotationBasePos_eq_ite,
    rotationBasePos_eq_ite, rotationBasePos_eq_ite]
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hz := ZMod.val_lt z
  split_ifs <;> omega

lemma sbtw_add_right_iff_actual (a x y z : ZMod n) :
    sbtw (x + a) (y + a) (z + a) ↔ sbtw x y z := by
  rw [rotation_sbtw_iff_basePos a, rotation_sbtw_iff_basePos 0]
  simp [rotationBasePos]

lemma cross_map_add_actual {e f : Sym2 (ZMod n)} (h : Cross e f) (a : ZMod n) :
    Cross (e.map (fun x => x + a)) (f.map (fun x => x + a)) := by
  obtain ⟨x, y, z, w, rfl, rfl, hxy, hzw⟩ := h
  exact ⟨x + a, y + a, z + a, w + a, rfl, rfl,
    (sbtw_add_right_iff_actual a _ _ _).2 hxy,
    (sbtw_add_right_iff_actual a _ _ _).2 hzw⟩

lemma chord_map_add_neg_map_add (e : Sym2 (ZMod n)) (a : ZMod n) :
    (e.map (fun x => x + a)).map (fun x => x + -a) = e := by
  induction e using Sym2.ind with
  | _ x y => simp [Sym2.map_map, Function.comp_def, add_assoc]

lemma isDiagonal_map_add {e : Sym2 (ZMod n)} (h : IsDiagonal e) (a : ZMod n) :
    IsDiagonal (e.map (fun x => x + a)) := by
  refine ⟨?_, ?_⟩
  · rw [IsSegment, Sym2.isDiag_map (add_left_injective a)]
    exact h.1
  · intro hs
    obtain ⟨i, hi⟩ := hs
    apply h.2
    refine ⟨i + -a, ?_⟩
    apply (chord_map_add_neg_map_add e a).symm.trans
    rw [hi, Sym2.map_mk]
    congr 1
    ring

lemma isTriangulation_map_add {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (a : ZMod n) :
    IsTriangulation (T.image (fun e => e.map (fun x => x + a))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    exact isDiagonal_map_add (hT.isDiagonal d hd) a
  · intro e he f hf hcross
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
    have hback := cross_map_add_actual (a := -a) hcross
    have hback' : Cross d g := by
      simpa [Sym2.map_map, Function.comp_def, add_assoc] using hback
    exact hT.noncrossing d hd g hg hback'
  · intro e he hnot
    have he' : IsDiagonal (e.map (fun x => x + -a)) :=
      isDiagonal_map_add he (-a)
    have heT' : e.map (fun x => x + -a) ∉ T := by
      intro heT
      apply hnot
      exact mem_image.mpr ⟨e.map (fun x => x + -a), heT, by
        simp [Sym2.map_map, Function.comp_def, add_assoc]⟩
    obtain ⟨d, hd, hcross⟩ := hT.maximal _ he' heT'
    refine ⟨d.map (fun x => x + a), mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    simpa [Sym2.map_map, Function.comp_def, add_assoc] using cross_map_add_actual hcross a

def shiftSet (S : Finset (ZMod n)) (a : ZMod n) : Finset (ZMod n) :=
  S.image (fun x => x + a)

def shiftChords (T : Finset (Sym2 (ZMod n))) (a : ZMod n) :
    Finset (Sym2 (ZMod n)) := T.image (fun e => e.map (fun x => x + a))

lemma shiftSet_mem_iff {S : Finset (ZMod n)} {a x : ZMod n} :
    x + a ∈ shiftSet S a ↔ x ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := mem_image.mp h
    have : y = x := by
      apply add_right_cancel
      exact hxy
    simpa [this] using hy
  · intro h
    exact mem_image.mpr ⟨x, h, rfl⟩

lemma mem_shiftSet_iff {S : Finset (ZMod n)} {a x : ZMod n} :
    x ∈ shiftSet S a ↔ x + -a ∈ S := by
  have h := shiftSet_mem_iff (S := S) (a := a) (x := x + -a)
  simpa [add_assoc] using h

lemma shiftSet_add_neg (S : Finset (ZMod n)) (a : ZMod n) :
    shiftSet (shiftSet S a) (-a) = S := by
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := mem_image.mp h
    obtain ⟨z, hz, hyz⟩ := mem_image.mp hy
    have : z = x := by
      calc z = (z + a) + -a := by simp [add_assoc]
           _ = y + -a := by rw [hyz]
           _ = x := hxy
    simpa [this] using hz
  · intro h
    apply mem_image.mpr
    refine ⟨x + a, ?_, ?_⟩
    · exact mem_image.mpr ⟨x, h, rfl⟩
    · simp [add_assoc]

lemma shiftChords_add_neg (T : Finset (Sym2 (ZMod n))) (a : ZMod n) :
    shiftChords (shiftChords T a) (-a) = T := by
  ext e
  constructor
  · intro h
    obtain ⟨f, hf, hfe⟩ := mem_image.mp h
    obtain ⟨d, hd, hdf⟩ := mem_image.mp hf
    have hfe' : f = e.map (fun x => x + a) := by
      have h := congrArg (fun q => q.map (fun x => x + a)) hfe
      simpa [Sym2.map_map, Function.comp_def, add_assoc] using h
    have : d = e := by
      apply Sym2.map.injective (add_left_injective a)
      exact hdf.trans hfe'
    simpa [this] using hd
  · intro h
    apply mem_image.mpr
    refine ⟨e.map (fun x => x + a), ?_, ?_⟩
    · exact mem_image.mpr ⟨e, h, rfl⟩
    · simp [Sym2.map_map, Function.comp_def, add_assoc]

lemma ear_add (i a : ZMod n) :
    ear (i + a) = (ear i).map (fun x => x + a) := by
  rw [ear, ear, Sym2.map_mk, Sym2.eq_iff]
  left
  constructor <;> ring

lemma ear_mem_shift_iff {T : Finset (Sym2 (ZMod n))} {i a : ZMod n} :
    i + a ∈ EarCenters (shiftChords T a) ↔ i ∈ EarCenters T := by
  rw [mem_earCenters, mem_earCenters, ear_add]
  constructor
  · intro h
    obtain ⟨d, hd, hde⟩ := mem_image.mp h
    have : d = ear i := Sym2.map.injective (add_left_injective a) hde
    simpa [this] using hd
  · intro h
    exact mem_image.mpr ⟨ear i, h, rfl⟩

lemma earCenters_shift_iff {T : Finset (Sym2 (ZMod n))} {i a : ZMod n} :
    i + a ∈ EarCenters (shiftChords T a) ↔ i ∈ EarCenters T :=
  ear_mem_shift_iff

lemma earCenters_shift_mem_iff {T : Finset (Sym2 (ZMod n))} {i a : ZMod n} :
    i ∈ EarCenters (shiftChords T a) ↔ i + -a ∈ EarCenters T := by
  have h := ear_mem_shift_iff (T := T) (i := i + -a) (a := a)
  simpa [add_assoc] using h

lemma cross_ear_shift_iff {i j a : ZMod n} :
    Cross (ear (i + a)) (ear (j + a)) ↔ Cross (ear i) (ear j) := by
  constructor
  · intro h
    have h' := cross_map_add_actual (a := -a) h
    simpa [ear_add, Sym2.map_map, Function.comp_def, add_assoc] using h'
  · intro h
    simpa [ear_add] using cross_map_add_actual (a := a) h

lemma mem_E_K_shift_iff {K : Finset (ZMod n)} {i a : ZMod n} :
    i + a ∈ E_K (shiftSet K a) ↔ i ∈ E_K K := by
  simp only [E_K, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hi, hcross⟩
    refine ⟨?_, ?_⟩
    · intro hiK
      apply hi
      exact mem_image.mpr ⟨i, hiK, rfl⟩
    · intro k hk hcrossik
      apply hcross (k + a)
      · exact mem_image.mpr ⟨k, hk, rfl⟩
      · exact (cross_ear_shift_iff (i := i) (j := k) (a := a)).mpr hcrossik
  · rintro ⟨hi, hcross⟩
    refine ⟨?_, ?_⟩
    · intro hiK
      obtain ⟨k, hk, hki⟩ := mem_image.mp hiK
      apply hi
      have : k = i := by
        apply add_right_cancel
        exact hki
      simpa [this] using hk
    · intro k hk hcrossik
      obtain ⟨j, hj, hkj⟩ := mem_image.mp hk
      have hjk : j + a = k := hkj
      have hcross' : Cross (ear i) (ear j) := by
        apply (cross_ear_shift_iff (i := i) (j := j) (a := a)).mp
        simpa [hjk] using hcrossik
      exact hcross j hj hcross'

lemma shiftSet_erase (S : Finset (ZMod n)) (x a : ZMod n) :
    shiftSet (S.erase x) a = (shiftSet S a).erase (x + a) := by
  unfold shiftSet
  rw [image_erase (add_left_injective a)]

lemma shiftSet_insert (S : Finset (ZMod n)) (x a : ZMod n) :
    shiftSet (insert x S) a = insert (x + a) (shiftSet S a) := by
  simp [shiftSet]

lemma shiftSet_union (S U : Finset (ZMod n)) (a : ZMod n) :
    shiftSet (S ∪ U) a = shiftSet S a ∪ shiftSet U a := by
  simp [shiftSet]

def shift_condition_fibre_equiv (a : ZMod n)
    {P Q J X : Finset (ZMod n)} :
    ConditionFiber P Q J X ≃
      ConditionFiber (shiftSet P a) (shiftSet Q a) (shiftSet J a) (shiftSet X a) := by
  refine
    { toFun := fun x => ?_
      invFun := fun y => ?_
      left_inv := ?_
      right_inv := ?_ }
  · rcases x with ⟨T, hT, hP, hQ, htrace⟩
    refine ⟨shiftChords T a, isTriangulation_map_add hT a, ?_, ?_, ?_⟩
    · rintro i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      exact (earCenters_shift_iff (T := T) (i := j) (a := a)).mpr (hP hj)
    · apply Finset.disjoint_left.mpr
      intro i hiQ hiT
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hiQ
      exact (Finset.disjoint_left.mp hQ) hj
        ((earCenters_shift_iff (T := T) (i := j) (a := a)).mp hiT)
    · ext i
      constructor
      · intro hi
        have hiT := (mem_inter.mp hi).1
        have hiJ := (mem_inter.mp hi).2
        have hiT' := (earCenters_shift_mem_iff (T := T) (i := i) (a := a)).mp hiT
        have hiJ' := (mem_shiftSet_iff (S := J) (a := a) (x := i)).mp hiJ
        have hiX' := (Finset.ext_iff.mp htrace (i + -a)).mp
          (mem_inter.mpr ⟨hiT', hiJ'⟩)
        exact (mem_shiftSet_iff (S := X) (a := a) (x := i)).mpr hiX'
      · intro hi
        have hiX' := (mem_shiftSet_iff (S := X) (a := a) (x := i)).mp hi
        have hiT'J' := (Finset.ext_iff.mp htrace (i + -a)).mpr
          ((mem_shiftSet_iff (S := X) (a := a) (x := i)).mp hi)
        have hiT' := (mem_inter.mp hiT'J').1
        have hiJ' := (mem_inter.mp hiT'J').2
        exact mem_inter.mpr
          ⟨(earCenters_shift_mem_iff (T := T) (i := i) (a := a)).mpr hiT',
            (mem_shiftSet_iff (S := J) (a := a) (x := i)).mpr hiJ'⟩
  · rcases y with ⟨U, hU, hP, hQ, htrace⟩
    refine ⟨shiftChords U (-a), isTriangulation_map_add hU (-a), ?_, ?_, ?_⟩
    · rintro i hi
      have hi' : i + a ∈ shiftSet P a := mem_image.mpr ⟨i, hi, rfl⟩
      exact (earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mpr
        (by simpa [neg_neg] using hP hi')
    · apply Finset.disjoint_left.mpr
      intro i hiQ hiU
      have hi' : i + a ∈ shiftSet Q a := mem_image.mpr ⟨i, hiQ, rfl⟩
      have hc := (earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mp hiU
      exact (Finset.disjoint_left.mp hQ) hi' (by simpa [neg_neg] using hc)
    · ext i
      constructor
      · intro hi
        have hiU := (mem_inter.mp hi).1
        have hiJ := (mem_inter.mp hi).2
        have hiU' := (earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mp hiU
        have hiJ' : i + a ∈ shiftSet J a := mem_image.mpr ⟨i, hiJ, rfl⟩
        have hiX' := (Finset.ext_iff.mp htrace (i + a)).mp
          (mem_inter.mpr ⟨by simpa [neg_neg] using hiU', hiJ'⟩)
        have hiX'' := (mem_shiftSet_iff (S := X) (a := a) (x := i + a)).mp hiX'
        simpa [add_assoc] using hiX''
      · intro hi
        have hiX' : i + a ∈ shiftSet X a := mem_image.mpr ⟨i, hi, rfl⟩
        have hiUJ' := (Finset.ext_iff.mp htrace (i + a)).mpr hiX'
        have hiU' := (mem_inter.mp hiUJ').1
        have hiJ'' := (mem_inter.mp hiUJ').2
        have hiJ : i ∈ J :=
          by
            simpa [add_assoc] using
              (mem_shiftSet_iff (S := J) (a := a) (x := i + a)).mp hiJ''
        exact mem_inter.mpr
          ⟨(earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mpr
              (by simpa [neg_neg] using hiU'), hiJ⟩
  · intro x
    rcases x with ⟨T, hT, hP, hQ, htrace⟩
    exact Subtype.ext (shiftChords_add_neg T a)
  · intro y
    rcases y with ⟨U, hU, hP, hQ, htrace⟩
    exact Subtype.ext (by simpa [neg_neg] using shiftChords_add_neg U (-a))

def condition_fibre_equiv (hn : 14 ≤ n)
    {P Q J R : Finset (ZMod n)}
    (hJ : J ⊆ E_K (P ∪ Q))
    (hJ0 : (0 : ZMod n) ∉ J) (hJ1 : (1 : ZMod n) ∈ J)
    (hJ2 : (2 : ZMod n) ∈ J)
    (hR : R ⊆ ((J.erase 1).erase 2).erase 3) :
    ConditionFiber P Q J (insert 2 R) ≃
      ConditionFiber P Q ((J.erase 2).erase 3) (insert 1 R) := by
  have h6 : 6 ≤ n := by omega
  have hPrem : ∀ i ∈ P, IsRemote i := by
    intro i hi
    apply remote_of_K h6 hJ hJ1 hJ2
    exact mem_union_left Q hi
  have hQrem : ∀ i ∈ Q, IsRemote i := by
    intro i hi
    apply remote_of_K h6 hJ hJ1 hJ2
    exact mem_union_right P hi
  have h12 : (1 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h13 : (1 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have hsource_s {T : Finset (Sym2 (ZMod n))}
      (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T) :
      sEar (n := n) ∉ T := by
    intro hs
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hs
      (local_crossings h6).1
  have htarget_s {U : Finset (Sym2 (ZMod n))}
      (hU : IsTriangulation U) (htrace : EarCenters U ∩
        ((J.erase 2).erase 3) = insert 1 R) :
      sEar (n := n) ∈ U := by
    have hdom : (1 : ZMod n) ∈ (J.erase 2).erase 3 :=
      mem_erase.mpr ⟨h13, mem_erase.mpr ⟨h12, hJ1⟩⟩
    have hmem := (Finset.ext_iff.mp htrace (1 : ZMod n)).mpr
      (by simp : (1 : ZMod n) ∈ insert 1 R)
    have hcenter : (1 : ZMod n) ∈ EarCenters U := (mem_inter.mp hmem).1
    exact (mem_earCenters.mp hcenter)
  have hsource_t {T : Finset (Sym2 (ZMod n))}
      (htrace : EarCenters T ∩ J = insert 2 R) :
      tEar (n := n) ∈ T := by
    have hmem := (Finset.ext_iff.mp htrace (2 : ZMod n)).mpr
      (by simp : (2 : ZMod n) ∈ insert 2 R)
    have hcenter : (2 : ZMod n) ∈ EarCenters T := (mem_inter.mp hmem).1
    exact (mem_earCenters.mp hcenter)
  refine
    { toFun := fun x =>
        ⟨phi x.1, ?_⟩
      invFun := fun y =>
        ⟨psi y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases x with ⟨T, hT, hP, hQ, htrace⟩
    have ht := hsource_t htrace
    have hphiT := phi_isTriangulation h6 hT ht
    refine ⟨hphiT, ?_, ?_, ?_⟩
    · intro i hi
      exact (earCenters_remote_phi hn (hPrem i hi)).mpr (hP hi)
    · apply Finset.disjoint_left.mpr
      intro i hiP hiPhi
      exact (Finset.disjoint_left.mp hQ) hiP
        ((earCenters_remote_phi hn (hQrem i hiP)).mp hiPhi)
    · exact trace_phi hn hT ht hJ0 hJ1 hJ2 hR htrace
  · rcases y with ⟨U, hU, hP, hQ, htrace⟩
    have hsU := htarget_s hU htrace
    have hpsiU := psi_isTriangulation h6 hU hsU
    refine ⟨hpsiU, ?_, ?_, ?_⟩
    · intro i hi
      exact (earCenters_remote_psi hn (hPrem i hi)).mpr (hP hi)
    · apply Finset.disjoint_left.mpr
      intro i hiP hiPsi
      exact (Finset.disjoint_left.mp hQ) hiP
        ((earCenters_remote_psi hn (hQrem i hiP)).mp hiPsi)
    · exact trace_psi hn hU hsU hJ0 hJ1 hJ2 hR htrace
  · intro x
    rcases x with ⟨T, hT, hP, hQ, htrace⟩
    have ht : tEar (n := n) ∈ T := hsource_t htrace
    have hs : sEar (n := n) ∉ T := hsource_s hT ht
    exact Subtype.ext (psi_phi h6 (fun e he => hT.isDiagonal e he) ht hs)
  · intro y
    rcases y with ⟨U, hU, hP, hQ, htrace⟩
    have hs : sEar (n := n) ∈ U := htarget_s hU htrace
    have ht : tEar (n := n) ∉ U := by
      intro ht
      exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) ht
        (cross_symm (local_crossings h6).1)
    exact Subtype.ext (phi_psi h6 (fun e he => hU.isDiagonal e he) hs ht)

def condition_fibre_equiv_at (hn : 14 ≤ n) (a : ZMod n)
    {P Q J R : Finset (ZMod n)}
    (hJ : J ⊆ E_K (P ∪ Q))
    (ha0 : a ∉ J) (ha1 : a + 1 ∈ J) (ha2 : a + 2 ∈ J)
    (hR : R ⊆ ((J.erase (a + 1)).erase (a + 2)).erase (a + 3)) :
    ConditionFiber P Q J (insert (a + 2) R) ≃
      ConditionFiber P Q ((J.erase (a + 2)).erase (a + 3)) (insert (a + 1) R) := by
  let P0 := shiftSet P (-a)
  let Q0 := shiftSet Q (-a)
  let J0 := shiftSet J (-a)
  let R0 := shiftSet R (-a)
  have hJ0sub : J0 ⊆ E_K (P0 ∪ Q0) := by
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := mem_image.mp hi
    have hiE := (mem_E_K_shift_iff (K := P ∪ Q) (i := i0) (a := -a)).mpr (hJ hi0)
    simpa [P0, Q0, shiftSet_union] using hiE
  have hJ00 : (0 : ZMod n) ∉ J0 := by
    intro hz
    have := (mem_shiftSet_iff (S := J) (a := -a) (x := 0)).mp hz
    exact ha0 (by simpa using this)
  have hJ01 : (1 : ZMod n) ∈ J0 := by
    apply (mem_shiftSet_iff (S := J) (a := -a) (x := 1)).mpr
    simpa [add_assoc, add_comm] using ha1
  have hJ02 : (2 : ZMod n) ∈ J0 := by
    apply (mem_shiftSet_iff (S := J) (a := -a) (x := 2)).mpr
    simpa [add_assoc, add_comm] using ha2
  have hR0 : R0 ⊆ ((J0.erase 1).erase 2).erase 3 := by
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := mem_image.mp hi
    have hi0' := hR hi0
    have htrip :
        shiftSet (((J.erase (a + 1)).erase (a + 2)).erase (a + 3)) (-a) =
          ((J0.erase 1).erase 2).erase 3 := by
      rw [shiftSet_erase, shiftSet_erase, shiftSet_erase]
      simp [J0, add_assoc]
    rw [← htrip]
    exact mem_image.mpr ⟨i0, hi0', rfl⟩
  let e0 := shift_condition_fibre_equiv (n := n) (-a)
    (P := P) (Q := Q) (J := J) (X := insert (a + 2) R)
  let ef := condition_fibre_equiv (n := n) hn hJ0sub
    hJ00 hJ01 hJ02 hR0
  let e1 := shift_condition_fibre_equiv (n := n) a
    (P := P0) (Q := Q0) (J := (J0.erase 2).erase 3) (X := insert 1 R0)
  have hPshift : shiftSet P0 a = P := by
    simpa [P0, neg_neg] using shiftSet_add_neg P (-a)
  have hQshift : shiftSet Q0 a = Q := by
    simpa [Q0, neg_neg] using shiftSet_add_neg Q (-a)
  have hX0 : shiftSet (insert (a + 2) R) (-a) = insert 2 R0 := by
    rw [shiftSet_insert]
    simp [R0, add_assoc]
  have htarget :
      shiftSet ((J0.erase 2).erase 3) a =
        (J.erase (a + 2)).erase (a + 3) := by
    rw [shiftSet_erase, shiftSet_erase]
    have hJshift : shiftSet J0 a = J := by
      simpa [J0, neg_neg] using shiftSet_add_neg J (-a)
    rw [hJshift]
    simp [add_comm, add_left_comm, add_assoc]
  have hRshift : shiftSet R0 a = R := by
    simpa [R0, neg_neg] using shiftSet_add_neg R (-a)
  have hsrcR : shiftSet (insert 1 R0) a = insert (a + 1) R := by
    rw [shiftSet_insert, hRshift]
    simp [add_comm, add_left_comm, add_assoc]
  have e0' : ConditionFiber P Q J (insert (a + 2) R) ≃
      ConditionFiber P0 Q0 J0 (insert 2 R0) := by
    simpa only [P0, Q0, J0, R0, hX0] using e0
  have e1' : ConditionFiber P0 Q0 ((J0.erase 2).erase 3) (insert 1 R0) ≃
      ConditionFiber P Q ((J.erase (a + 2)).erase (a + 3)) (insert (a + 1) R) := by
    simpa only [hPshift, hQshift, htarget, hsrcR] using e1
  exact e0'.trans (ef.trans e1')

end Actual

end D5.S3.Geometry.Polygons.PolygonEarSlide
