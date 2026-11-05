/- GID: D5/S3/Geometry/Polygons/PolygonEarSlideMaps
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlideMaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit complete ear-slide maps preserve maximal noncrossing triangulations and are mutual inverses. -/

import D5.S3.Geometry.Polygons.PolygonEarSlideGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Geometry.Polygons.PolygonEarSlide
open Carrier

namespace Actual

variable {n : ℕ} [NeZero n]

lemma isDiagonal_chordSwap_of_ne (hn : 6 ≤ n) {e : Sym2 (ZMod n)}
    (he : IsDiagonal e) (hes : e ≠ sEar (n := n)) (het : e ≠ tEar (n := n)) :
    IsDiagonal (chordSwap e) := by
  refine ⟨?_, ?_⟩
  · change ¬(chordSwap e).IsDiag
    have hseg := he.1
    change ¬e.IsDiag at hseg
    change ¬(Sym2.map (vertexSwap n) e).IsDiag
    rw [Sym2.isDiag_map (Equiv.injective (vertexSwap n))]
    exact hseg
  · intro hs
    have h01 : (0 : ZMod n) ≠ 1 := by
      have h1 : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (0 : ℕ) = 1 := by simpa [ZMod.val_zero, h1] using hv
      omega
    have h02 : (0 : ZMod n) ≠ 2 := by
      have h2 : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (0 : ℕ) = 2 := by simpa [ZMod.val_zero, h2] using hv
      omega
    have h12 : (1 : ZMod n) ≠ 2 := by
      have h1 : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h2 : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (1 : ℕ) = 2 := by simpa [h1, h2] using hv
      omega
    have h31 : (3 : ZMod n) ≠ 1 := by
      have h1 : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h3 : (3 : ZMod n).val = 3 := by
        simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (3 : ℕ) = 1 := by simpa [h1, h3] using hv
      omega
    have h32 : (3 : ZMod n) ≠ 2 := by
      have h2 : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      have h3 : (3 : ZMod n).val = 3 := by
        simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (3 : ℕ) = 2 := by simpa [h2, h3] using hv
      omega
    have hswap0 : vertexSwap n 0 = 0 := by
      simp [vertexSwap, Equiv.swap_apply_def, h01, h02]
    have hswap1 : vertexSwap n 1 = 2 := by simp [vertexSwap]
    have hswap2 : vertexSwap n 2 = 1 := by simp [vertexSwap, h12]
    have hswap3 : vertexSwap n 3 = 3 := by
      simp [vertexSwap, Equiv.swap_apply_def, h31, h32]
    have h11 : (1 : ZMod n) + 1 = 2 := by ring
    have h23 : (2 : ZMod n) + 1 = 3 := by ring
    rcases hs with ⟨i, hi⟩
    have heq : e = chordSwap s(i, i + 1) := by
      calc
        e = chordSwap (chordSwap e) := by simp
        _ = chordSwap s(i, i + 1) := congrArg chordSwap hi
    by_cases h0 : i = 0
    · apply hes
      simpa [sEar, ear_one, h0, chordSwap, hswap0, hswap1] using heq
    by_cases h1 : i = 1
    · apply he.2
      refine ⟨1, ?_⟩
      simpa [h1, chordSwap, hswap1, hswap2, h11, Sym2.eq_swap] using heq
    by_cases h2i : i = 2
    · apply het
      simpa [tEar, ear_two, h2i, chordSwap, hswap2, hswap3, h23] using heq
    apply he.2
    refine ⟨i, ?_⟩
    have hi1 : i + 1 ≠ 1 := by
      intro h
      apply h0
      calc
        i = (i + 1) - 1 := by ring
        _ = 1 - 1 := congrArg (fun z : ZMod n => z - 1) h
        _ = 0 := by ring
    have hi2 : i + 1 ≠ 2 := by
      intro h
      apply h1
      calc
        i = (i + 1) - 1 := by ring
        _ = 2 - 1 := congrArg (fun z : ZMod n => z - 1) h
        _ = 1 := by ring
    have hswapi : vertexSwap n i = i := by
      simp [vertexSwap, Equiv.swap_apply_def, h0, h1, h2i]
    have hswapi1 : vertexSwap n (i + 1) = i + 1 := by
      simp [vertexSwap, Equiv.swap_apply_def, hi1, hi2]
    simpa [chordSwap, hswapi, hswapi1] using heq

lemma avoidTwo_of_mem_triangulation (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T) {e : Sym2 (ZMod n)}
    (he : e ∈ T) : AvoidTwo e := by
  have hdiag : IsDiagonal e := hT.isDiagonal e he
  induction e using Sym2.ind with
  | _ a b =>
      rw [avoidTwo_mk_iff]
      constructor
      · intro ha
        have hside : ¬IsSide s(a, b) := by
          intro hs
          exact hdiag.2 hs
        have hb1 : b ≠ 1 := by
          intro hb
          apply hside
          refine ⟨1, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have hb3 : b ≠ 3 := by
          intro hb
          apply hside
          refine ⟨2, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have hc := cross_incident_two hn hb1 (by
          intro hb2
          exact hdiag.1 (by simp [ha, hb2, IsSegment, Sym2.mk_isDiag_iff])) hb3
        exact hT.noncrossing (s(a, b)) he (tEar (n := n)) ht
          (by simpa [ha] using hc)
      · intro hb
        have hside : ¬IsSide s(a, b) := by
          intro hs
          exact hdiag.2 hs
        have ha1 : a ≠ 1 := by
          intro ha
          apply hside
          refine ⟨1, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have ha3 : a ≠ 3 := by
          intro ha
          apply hside
          refine ⟨2, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have hc := cross_incident_two hn ha1 (by
          intro ha2
          exact hdiag.1 (by simp [ha2, hb, IsSegment, Sym2.mk_isDiag_iff])) ha3
        exact hT.noncrossing (s(a, b)) he (tEar (n := n)) ht
          (by simpa [hb, Sym2.eq_swap] using hc)

lemma avoidOne_of_mem_triangulation (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (hs : sEar (n := n) ∈ T) {e : Sym2 (ZMod n)}
    (he : e ∈ T) : ∀ x : ZMod n, e ≠ s(1, x) := by
  have hdiag : IsDiagonal e := hT.isDiagonal e he
  induction e using Sym2.ind with
  | _ a b =>
      intro x hx
      have hside : ¬IsSide s(a, b) := hdiag.2
      have hab : a ≠ b := by
        simpa [IsSegment, Sym2.mk_isDiag_iff] using hdiag.1
      rw [Sym2.eq_iff] at hx
      rcases hx with ⟨ha1, hbx⟩ | ⟨hax, hb1⟩
      · subst a
        have hb0 : b ≠ 0 := by
          intro hb
          apply hside
          exact ⟨0, by simp [hb, Sym2.eq_swap]⟩
        have hb1' : b ≠ 1 := by
          intro hb
          exact hab (by simpa [hb])
        have hb2 : b ≠ 2 := by
          intro hb
          apply hside
          refine ⟨1, ?_⟩
          rw [hb, Sym2.eq_iff]
          exact Or.inl ⟨rfl, by ring⟩
        exact hT.noncrossing (s(1, b)) (by simpa using he)
          (sEar (n := n)) hs (cross_incident_one hn hb0 hb1' hb2)
      · subst b
        have ha0 : a ≠ 0 := by
          intro ha
          apply hside
          exact ⟨0, by simp [ha]⟩
        have ha1' : a ≠ 1 := by
          intro ha
          exact hab (by simpa [ha])
        have ha2 : a ≠ 2 := by
          intro ha
          apply hside
          refine ⟨1, ?_⟩
          rw [ha, Sym2.eq_iff]
          exact Or.inr ⟨by ring, rfl⟩
        exact hT.noncrossing (s(a, 1)) (by simpa [Sym2.eq_swap] using he)
          (sEar (n := n)) hs
          (by simpa [Sym2.eq_swap] using cross_incident_one hn ha0 ha1' ha2)

lemma isDiagonal_sEar (hn : 6 ≤ n) : IsDiagonal (sEar (n := n)) := by
  rw [sEar, ear_one]
  have h02 : (0 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [ZMod.val_zero, h2] using hv
  have h21 : (2 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h03 : (0 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [ZMod.val_zero, h3] using hv
  refine ⟨?_, ?_⟩
  · simp [IsSegment, Sym2.mk_isDiag_iff, h02]
  · rintro ⟨i, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨h0, h2⟩ | ⟨h0, h2⟩
    · subst i
      apply h21
      simpa using h2
    · subst i
      apply h03
      calc
        (0 : ZMod n) = 2 + 1 := h0
        _ = 3 := by ring

lemma chordSwap_sEar (hn : 6 ≤ n) : chordSwap (sEar (n := n)) = s(0, 1) := by
  have h01 : (0 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    simpa [ZMod.val_zero, h1] using hv
  have h02 : (0 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [ZMod.val_zero, h2] using hv
  rw [sEar, ear_one, chordSwap_mk, vertexSwap_apply_two hn]
  simp [vertexSwap, Equiv.swap_apply_def, h01, h02]

lemma chordSwap_tEar (hn : 6 ≤ n) : chordSwap (tEar (n := n)) = s(2, 3) := by
  have h31 : (3 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have h32 : (3 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h2, h3] using hv
  rw [tEar, ear_two, chordSwap_mk, vertexSwap_apply_one hn]
  simp [vertexSwap, Equiv.swap_apply_def, h31, h32]

def phi (T : Finset (Sym2 (ZMod n))) : Finset (Sym2 (ZMod n)) :=
  insert (sEar (n := n)) (image chordSwap (T.erase (tEar (n := n))))

def psi (U : Finset (Sym2 (ZMod n))) : Finset (Sym2 (ZMod n)) :=
  insert (tEar (n := n)) (image chordSwap (U.erase (sEar (n := n))))

lemma chordSwap_ne_sEar_of_diagonal {e : Sym2 (ZMod n)}
    (hn : 6 ≤ n) (he : IsDiagonal e) (h : chordSwap e = sEar (n := n)) : False := by
  have heq : e = chordSwap (sEar (n := n)) := by
    calc
      e = chordSwap (chordSwap e) := by simp
      _ = chordSwap (sEar (n := n)) := congrArg chordSwap h
  rw [chordSwap_sEar hn] at heq
  apply he.2
  exact ⟨0, by simpa using heq⟩

lemma phi_erase_s (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ T, IsDiagonal e) (ht : tEar (n := n) ∈ T) :
    (phi T).erase (sEar (n := n)) = image chordSwap (T.erase (tEar (n := n))) := by
  apply erase_insert
  intro hs
  rw [mem_image] at hs
  obtain ⟨e, he, hse⟩ := hs
  exact chordSwap_ne_sEar_of_diagonal hn (hdiag e (mem_of_mem_erase he)) hse

lemma psi_phi (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ T, IsDiagonal e) (ht : tEar (n := n) ∈ T)
    (hs : sEar (n := n) ∉ T) : psi (phi T) = T := by
  rw [psi, phi_erase_s hn hdiag ht]
  rw [image_image]
  simp only [Function.comp_def]
  ext e
  simp [Function.comp_def, chordSwap_involutive, ht]

lemma phi_image_members_are_diagonal (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T)
    {e : Sym2 (ZMod n)} (he : e ∈ image chordSwap (T.erase (tEar (n := n)))) :
    IsDiagonal e := by
  obtain ⟨d, hd, rfl⟩ := mem_image.mp he
  have hdt : d ≠ tEar (n := n) := (mem_erase.mp hd).1
  have hdiag : IsDiagonal d := hT.isDiagonal d (mem_erase.mp hd).2
  have hds : d ≠ sEar (n := n) := by
    intro hds
    have hsT : sEar (n := n) ∈ T := by
      simpa [hds] using (mem_erase.mp hd).2
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hsT
      (local_crossings hn).1
  exact isDiagonal_chordSwap_of_ne hn hdiag hds hdt

lemma phi_isTriangulation (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T) :
    IsTriangulation (phi T) := by
  have hsT : sEar (n := n) ∉ T := by
    intro hs
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hs
      (local_crossings hn).1
  have hdiag : ∀ e ∈ phi T, IsDiagonal e := by
    intro e he
    simp only [phi, mem_insert] at he
    rcases he with rfl | he
    · exact isDiagonal_sEar hn
    · exact phi_image_members_are_diagonal hn hT ht he
  refine ⟨hdiag, ?_, ?_⟩
  · intro e he f hf hcross
    simp only [phi, mem_insert] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact not_cross_self _ hcross
      · obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn hcross
        obtain ⟨d, hd, hde⟩ := mem_image.mp hf
        exact chordSwap_not_incident_one_of_avoidTwo
          (avoidTwo_of_mem_triangulation hn hT ht (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
    · rcases hf with rfl | hf
      · exfalso
        obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn (cross_symm hcross)
        obtain ⟨d, hd, hde⟩ := mem_image.mp he
        exact chordSwap_not_incident_one_of_avoidTwo
          (avoidTwo_of_mem_triangulation hn hT ht (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
      · obtain ⟨d, hd, hde⟩ := mem_image.mp he
        obtain ⟨g, hg, hgf⟩ := mem_image.mp hf
        have hdT : d ∈ T := mem_of_mem_erase hd
        have hgT : g ∈ T := mem_of_mem_erase hg
        have hcross0 : Cross (chordSwap d) (chordSwap g) := by
          simpa [hde, hgf] using hcross
        have hcross' := (cross_chordSwap_of_avoidTwo hn
          (avoidTwo_of_mem_triangulation hn hT ht hdT)
          (avoidTwo_of_mem_triangulation hn hT ht hgT)).mp hcross0
        exact hT.noncrossing d hdT g hgT hcross'
  · intro e he hnot
    by_cases hcross : Cross e (sEar (n := n))
    · exact ⟨sEar (n := n), by simp [phi], hcross⟩
    have hes : e ≠ sEar (n := n) := by
      intro hes
      apply hnot
      rw [hes]
      simp [phi]
    have het : e ≠ tEar (n := n) := by
      intro het
      apply hcross
      simpa [het] using (local_crossings hn).1
    have havoidOne := avoidOne_of_diagonal_not_cross_s hn he hcross
    let g := chordSwap e
    have hgdiag : IsDiagonal g := isDiagonal_chordSwap_of_ne hn he hes het
    have hgavoid : AvoidTwo g := avoidTwo_of_chordSwap_of_avoidOne hn havoidOne
    have hgt : g ≠ tEar (n := n) := by
      intro hgt
      have heq : e = chordSwap (tEar (n := n)) := by
        calc
          e = chordSwap (chordSwap e) := by simp [g]
          _ = chordSwap (tEar (n := n)) := congrArg chordSwap hgt
      rw [chordSwap_tEar hn] at heq
      apply he.2
      rw [heq]
      refine ⟨2, ?_⟩
      rw [Sym2.eq_iff]
      exact Or.inl ⟨rfl, by ring⟩
    have hgnT : g ∉ T := by
      intro hgin
      apply hnot
      apply mem_insert_of_mem
      apply mem_image.mpr
      refine ⟨g, mem_erase.mpr ⟨hgt, hgin⟩, ?_⟩
      simp [g]
    obtain ⟨f, hfT, hgf⟩ := hT.maximal g hgdiag hgnT
    have hft : f ≠ tEar (n := n) := by
      intro hft
      subst f
      exact not_cross_t_of_avoidTwo hn hgavoid hgf
    refine ⟨chordSwap f, mem_insert_of_mem (mem_image.mpr
      ⟨f, mem_erase.mpr ⟨hft, hfT⟩, rfl⟩), ?_⟩
    have hfavoid := avoidTwo_of_mem_triangulation hn hT ht hfT
    have hmap := (cross_chordSwap_of_avoidTwo hn hgavoid hfavoid).mpr hgf
    simpa [g] using hmap

lemma isDiagonal_tEar (hn : 6 ≤ n) : IsDiagonal (tEar (n := n)) := by
  rw [tEar, ear_two]
  have h13 : (1 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have h12 : (1 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h32 : (3 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h2, h3] using hv
  have h23 : (2 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h2, h3] using hv
  have h41 : (3 : ZMod n) + 1 ≠ 1 := by
    intro h
    have h4 : (4 : ZMod n).val = 4 := by
      simpa using (ZMod.val_natCast_of_lt (show 4 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have hv := congrArg ZMod.val h
    rw [show (3 : ZMod n) + 1 = 4 by ring] at hv
    have : (4 : ℕ) = 1 := by simpa [h1, h3, h4] using hv
    omega
  refine ⟨?_, ?_⟩
  · simp [IsSegment, Sym2.mk_isDiag_iff, h13]
  · rintro ⟨i, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply h23
      calc
        (2 : ZMod n) = 1 + 1 := by ring
        _ = i + 1 := by rw [h1]
        _ = 3 := h2.symm
    · apply h41
      calc
        (3 : ZMod n) + 1 = i + 1 := by rw [h2]
        _ = 1 := h1.symm

lemma psi_image_members_are_diagonal (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U)
    {e : Sym2 (ZMod n)} (he : e ∈ image chordSwap (U.erase (sEar (n := n)))) :
    IsDiagonal e := by
  obtain ⟨d, hd, rfl⟩ := mem_image.mp he
  have hds : d ≠ sEar (n := n) := (mem_erase.mp hd).1
  have hdiag : IsDiagonal d := hU.isDiagonal d (mem_erase.mp hd).2
  have hdt : d ≠ tEar (n := n) := by
    intro hdt
    have htU : tEar (n := n) ∈ U := by simpa [hdt] using (mem_erase.mp hd).2
    exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) htU
      (cross_symm (local_crossings hn).1)
  exact isDiagonal_chordSwap_of_ne hn hdiag hds hdt

lemma psi_isTriangulation (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U) :
    IsTriangulation (psi U) := by
  have htU : tEar (n := n) ∉ U := by
    intro ht
    exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) ht
      (cross_symm (local_crossings hn).1)
  have hdiag : ∀ e ∈ psi U, IsDiagonal e := by
    intro e he
    simp only [psi, mem_insert] at he
    rcases he with rfl | he
    · exact isDiagonal_tEar hn
    · exact psi_image_members_are_diagonal hn hU hs he
  refine ⟨hdiag, ?_, ?_⟩
  · intro e he f hf hcross
    simp only [psi, mem_insert] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact not_cross_self _ hcross
      · obtain ⟨x, hx⟩ := cross_t_implies_incident_two hn hcross
        obtain ⟨d, hd, hde⟩ := mem_image.mp hf
        exact chordSwap_not_incident_two_of_avoidOne
          (avoidOne_of_mem_triangulation hn hU hs (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
    · rcases hf with rfl | hf
      · exfalso
        obtain ⟨x, hx⟩ := cross_t_implies_incident_two hn (cross_symm hcross)
        obtain ⟨d, hd, hde⟩ := mem_image.mp he
        exact chordSwap_not_incident_two_of_avoidOne
          (avoidOne_of_mem_triangulation hn hU hs (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
      · obtain ⟨d, hd, hde⟩ := mem_image.mp he
        obtain ⟨g, hg, hgf⟩ := mem_image.mp hf
        have hdU : d ∈ U := mem_of_mem_erase hd
        have hgU : g ∈ U := mem_of_mem_erase hg
        have hcross0 : Cross (chordSwap d) (chordSwap g) := by
          simpa [hde, hgf] using hcross
        have hcross' := (cross_chordSwap_of_avoidOne hn
          (avoidOne_of_mem_triangulation hn hU hs hdU)
          (avoidOne_of_mem_triangulation hn hU hs hgU)).mp hcross0
        exact hU.noncrossing d hdU g hgU hcross'
  · intro e he hnot
    by_cases hcross : Cross e (tEar (n := n))
    · exact ⟨tEar (n := n), by simp [psi], hcross⟩
    have het : e ≠ tEar (n := n) := by
      intro het
      apply hnot
      rw [het]
      simp [psi]
    have hes : e ≠ sEar (n := n) := by
      intro hes
      apply hcross
      rw [hes]
      exact (cross_symm (local_crossings hn).1)
    have havoidTwo := avoidTwo_of_diagonal_not_cross_t hn he het hcross
    let g := chordSwap e
    have hgdiag : IsDiagonal g := isDiagonal_chordSwap_of_ne hn he hes het
    have hgavoid : ∀ x : ZMod n, g ≠ s(1, x) :=
      avoidOne_of_chordSwap_of_avoidTwo havoidTwo
    have hgnU : g ∉ U := by
      intro hgin
      apply hnot
      apply mem_insert_of_mem
      apply mem_image.mpr
      refine ⟨g, mem_erase.mpr ⟨?_, hgin⟩, ?_⟩
      · intro hgt
        have : e = chordSwap (sEar (n := n)) := by
          calc
            e = chordSwap (chordSwap e) := by simp [g]
            _ = chordSwap (sEar (n := n)) := congrArg chordSwap hgt
        rw [chordSwap_sEar hn] at this
        exact he.2 (by rw [this]; exact ⟨0, by simp⟩)
      · simp [g]
    obtain ⟨f, hfU, hgf⟩ := hU.maximal g hgdiag hgnU
    have hfs : f ≠ sEar (n := n) := by
      intro hfs
      subst f
      exact not_cross_s_of_avoidOne hn hgavoid hgf
    refine ⟨chordSwap f, mem_insert_of_mem (mem_image.mpr
      ⟨f, mem_erase.mpr ⟨hfs, hfU⟩, rfl⟩), ?_⟩
    have hfavoid := avoidOne_of_mem_triangulation hn hU hs hfU
    have hmap := (cross_chordSwap_of_avoidOne hn hgavoid hfavoid).mpr hgf
    simpa [g] using hmap

lemma chordSwap_ne_tEar_of_diagonal {e : Sym2 (ZMod n)}
    (hn : 6 ≤ n) (he : IsDiagonal e) (h : chordSwap e = tEar (n := n)) : False := by
  have heq : e = chordSwap (tEar (n := n)) := by
    calc
      e = chordSwap (chordSwap e) := by simp
      _ = chordSwap (tEar (n := n)) := congrArg chordSwap h
  rw [chordSwap_tEar hn] at heq
  apply he.2
  exact ⟨2, by
    rw [heq, Sym2.eq_iff]
    exact Or.inl ⟨rfl, by ring⟩⟩

lemma psi_erase_t (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ U, IsDiagonal e) (hs : sEar (n := n) ∈ U) :
    (psi U).erase (tEar (n := n)) = image chordSwap (U.erase (sEar (n := n))) := by
  apply erase_insert
  intro ht
  rw [mem_image] at ht
  obtain ⟨e, he, hte⟩ := ht
  exact chordSwap_ne_tEar_of_diagonal hn (hdiag e (mem_of_mem_erase he)) hte

lemma phi_psi (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ U, IsDiagonal e) (hs : sEar (n := n) ∈ U)
    (ht : tEar (n := n) ∉ U) : phi (psi U) = U := by
  rw [phi, psi_erase_t hn hdiag hs]
  rw [image_image]
  simp only [Function.comp_def]
  ext e
  simp [Function.comp_def, chordSwap_involutive, hs, ht]


end Actual

end D5.S3.Geometry.Polygons.PolygonEarSlide
