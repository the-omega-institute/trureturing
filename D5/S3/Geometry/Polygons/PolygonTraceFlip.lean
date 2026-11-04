/- GID: D5/S3/Geometry/Polygons/PolygonTraceFlip
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonTraceFlip
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual conditioned polygon trace flips and injective reconstruction. -/

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Ashvin A. Swaminathan and Alexey Sorokin.

The ClusterAlgebras declarations below are the exact 32 flip-only declarations
from AxiomMath/ClusterAlgebras revision a9174706bce3bcb0fa342b4614f98ef2acb7f91c.
This is modified source: module, import, public and attribute metadata are
adapted; the 43 shared declarations belong to PolygonCatalanSupplier, whose
69-declaration count cone is the sole shared supplier. Original declaration
names and proof bodies are retained. The local conditioned trace construction
belongs to PolygonTraceFlip. Full source spans, identities and Apache-2.0 text
are in docs/reports/licenses/cluster-algebras-polygon-third-party.md.
-/
import D5.S3.Geometry.Polygons.PolygonCatalanSupplier
import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Circular.ZMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod
import D5.S3.Geometry.Polygons.PolygonEarSlide
import D5.S3.Geometry.Polygons.PolygonConditionalCounts
import D5.S3.Geometry.Polygons.PolygonConditionedFan

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace ClusterAlgebras
variable {m : ℕ} [NeZero m]

private theorem sbtw_rotate_four {n : ℕ} {a b c d : Fin n} (h1 : sbtw a c b) (h2 : sbtw b d a) :
    sbtw c b d ∧ sbtw d a c := by
  rw [Fin.sbtw_iff] at h1 h2
  refine ⟨?_, ?_⟩ <;> rw [Fin.sbtw_iff] <;>
    simp only [Fin.lt_def] at h1 h2 ⊢ <;> omega

theorem Cross.symm {e f : Sym2 (ZMod m)} (h : Cross e f) : Cross f e := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2⟩ := h
  refine ⟨c, d, b, a, rfl, Sym2.eq_swap, ?_⟩
  match m, ‹NeZero m›, a, b, c, d, h1, h2 with
  | (n + 1), _, a, b, c, d, h1, h2 => exact sbtw_rotate_four h1 h2

def segments (T : Finset (Sym2 (ZMod m))) : Finset (Sym2 (ZMod m)) :=
  T ∪ Finset.univ.filter IsSide

theorem mem_segments {T : Finset (Sym2 (ZMod m))} {e : Sym2 (ZMod m)} :
    e ∈ segments T ↔ e ∈ T ∨ IsSide e := by
  simp [segments]

def flipTriangulation (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) :
    Finset (Sym2 (ZMod m)) :=
  insert γ' (T.erase γ)

def IsFlipReplacement (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) : Prop :=
  IsTriangulation T ∧ γ ∈ T ∧ IsDiagonal γ' ∧ γ' ∉ T ∧
    IsTriangulation (flipTriangulation T γ γ')

namespace TypeA

variable {a b : ℤ} {S : Finset (ℤ × ℤ)}

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
theorem not_cross_self (σ : Sym2 (ZMod m)) : ¬Cross σ σ := by
  rintro ⟨a, b, c, d, rfl, h, h1, h2⟩
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [sbtw_irrefl_left h1, sbtw_irrefl_right h1]

omit [NeZero m] in
theorem basePos_self (c : ZMod m) : basePos c c = 0 := by
  simp [basePos]

theorem basePos_self_lt_of_ne {u v : ZMod m} (h : u ≠ v) : basePos u u < basePos u v := by
  rw [basePos_self]
  exact lt_of_le_of_ne (basePos_nonneg u v) fun e =>
    h (basePos_injective u ((basePos_self u).trans e))

theorem sbtw_iff_basePos {c u v : ZMod m} (huv : basePos c u < basePos c v) (x : ZMod m) :
    sbtw u x v ↔ basePos c u < basePos c x ∧ basePos c x < basePos c v := by
  rw [sbtw_iff_sbtw_basePos c, Int.sbtw_iff]
  omega

theorem bijOn_basePosSeg_isSide (hm : 3 ≤ m) (c : ZMod m) :
    Set.BijOn (basePosSeg c) {σ | IsSide σ} ↑(intervalSides 0 ((m : ℤ) - 1)) := by
  refine ⟨?_, (basePosSeg_injective c).injOn, ?_⟩
  · rintro σ ⟨i, rfl⟩
    simp only [Finset.mem_coe, intervalSides, Finset.mem_insert, Finset.mem_image, Finset.mem_Ico]
    have h0 := basePos_nonneg c i
    have hl := basePos_lt c i
    rw [basePosSeg_mk, basePos_add_one]
    split_ifs with h
    · left
      rw [min_eq_right h0, max_eq_left h0]
      ext
      · rfl
      · simp only
        omega
    · right
      refine ⟨basePos c i, ⟨h0, by omega⟩, ?_⟩
      rw [min_eq_left (by omega), max_eq_right (by omega)]
  · intro q hq
    simp only [Finset.mem_coe, intervalSides, Finset.mem_insert, Finset.mem_image,
      Finset.mem_Ico] at hq
    rcases hq with rfl | ⟨i, ⟨hi0, hi⟩, rfl⟩
    · obtain ⟨u, hu⟩ := exists_basePos_eq c (k := (m : ℤ) - 1) (by omega) (by omega)
      refine ⟨s(u, u + 1), ⟨u, rfl⟩, ?_⟩
      rw [basePosSeg_mk, basePos_add_one, if_pos (by omega), hu]
      ext <;> simp <;> omega
    · obtain ⟨u, hu⟩ := exists_basePos_eq c (k := i) hi0 (by omega)
      refine ⟨s(u, u + 1), ⟨u, rfl⟩, ?_⟩
      rw [basePosSeg_mk, basePos_add_one, if_neg (by omega), hu]
      ext <;> simp

theorem not_cross_of_isSide {σ τ : Sym2 (ZMod m)} (hτ : IsSide τ) : ¬Cross σ τ := by
  obtain ⟨i, rfl⟩ := hτ
  induction σ using Sym2.ind with | _ u v => ?_
  rw [cross_mk_iff_basePos i, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff,
    basePos_add_one, basePos_self]
  have := basePos_nonneg i u
  have := basePos_nonneg i v
  split_ifs <;> omega

theorem IsTriangulation.not_cross {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    {σ τ : Sym2 (ZMod m)} (hσ : σ ∈ segments T) (hτ : τ ∈ segments T) : ¬Cross σ τ := by
  rcases mem_segments.1 hσ with hσ | hσ
  · rcases mem_segments.1 hτ with hτ | hτ
    · exact hT.noncrossing σ hσ τ hτ
    · exact not_cross_of_isSide hτ
  · exact fun h => not_cross_of_isSide hσ h.symm

theorem mem_segments_iff_basePosSeg (hm : 3 ≤ m) (c : ZMod m) (T : Finset (Sym2 (ZMod m)))
    {σ : Sym2 (ZMod m)} :
    σ ∈ segments T ↔ basePosSeg c σ ∈ intervalSegments 0 ((m : ℤ) - 1) (basePosTri c T) := by
  have hS := bijOn_basePosSeg_isSide hm c
  rw [mem_segments, intervalSegments, Finset.mem_union, basePosTri,
    (basePosSeg_injective c).mem_finset_image]
  refine or_congr Iff.rfl ⟨fun h => hS.mapsTo h, fun h => ?_⟩
  obtain ⟨τ, hτ, hτσ⟩ := hS.surjOn h
  rwa [← basePosSeg_injective c hτσ]

omit [NeZero m] in
theorem isSegment_mk_of_ne {u v : ZMod m} (h : u ≠ v) : IsSegment s(u, v) := by
  rwa [IsSegment, Sym2.mk_isDiag_iff]

theorem mem_segments_iff_of_basePos_lt (hm : 3 ≤ m) {c u v : ZMod m}
    (T : Finset (Sym2 (ZMod m))) (huv : basePos c u < basePos c v) :
    s(u, v) ∈ segments T ↔
      (basePos c u, basePos c v) ∈ intervalSegments 0 ((m : ℤ) - 1) (basePosTri c T) := by
  rw [mem_segments_iff_basePosSeg hm c T, basePosSeg_mk_of_lt huv]

theorem IsTriangulation.existsUnique_apex (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {a c : ZMod m} (hac : s(a, c) ∈ segments T)
    (hx : ∃ x, sbtw a x c) :
    ∃! b, sbtw a b c ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T := by
  obtain ⟨x, hx⟩ := hx
  have hac' : a ≠ c := by rintro rfl; exact sbtw_irrefl_left_right hx
  have h0 := basePos_self a
  have hi := basePos_injective a
  have hpos := basePos_self_lt_of_ne hac'
  have hxK := (sbtw_iff_basePos hpos x).1 hx
  rw [h0] at hxK
  have hS : IsIntervalTriangulation 0 ((m : ℤ) - 1) (basePosTri a T) :=
    (bijOn_basePosTri a).mapsTo hT
  have hK := (mem_segments_iff_of_basePos_lt hm T hpos).1 hac
  rw [h0] at hK
  have hlt := basePos_lt a c
  obtain ⟨j, ⟨hj0, hjK, hj1, hj2⟩, hju⟩ :=
    IsIntervalTriangulation.existsUnique_apex (by omega) hS (by omega) hK
  obtain ⟨b, hb⟩ := exists_basePos_eq a (k := j) hj0.le (by omega)
  have hab : basePos a a < basePos a b := by rwa [h0, hb]
  have hbc : basePos a b < basePos a c := by rwa [hb]
  refine ⟨b, ⟨(sbtw_iff_basePos hpos b).2 ⟨hab, hbc⟩,
    (mem_segments_iff_of_basePos_lt hm T hab).2 (by rwa [h0, hb]),
    (mem_segments_iff_of_basePos_lt hm T hbc).2 (by rwa [hb])⟩, ?_⟩
  rintro y ⟨hy, hy1, hy2⟩
  obtain ⟨hay, hyc⟩ := (sbtw_iff_basePos hpos y).1 hy
  have e1 := (mem_segments_iff_of_basePos_lt hm T hay).1 hy1
  have e2 := (mem_segments_iff_of_basePos_lt hm T hyc).1 hy2
  rw [h0] at e1 hay
  exact hi ((hju _ ⟨hay, hyc, e1, e2⟩).trans hb.symm)

variable {a b c d : ZMod m}

theorem quadrilateral_basePos (hb : sbtw a b c) (hd : sbtw c d a) :
    basePos a a = 0 ∧ 0 < basePos a b ∧ basePos a b < basePos a c ∧
      basePos a c < basePos a d ∧ basePos a d < m := by
  rw [sbtw_iff_sbtw_basePos a, Int.sbtw_iff, basePos_self] at hb hd
  have := basePos_nonneg a b
  have := basePos_nonneg a c
  have := basePos_nonneg a d
  have := basePos_lt a d
  refine ⟨basePos_self a, ?_⟩
  omega

theorem quadrilateral_cross (hb : sbtw a b c) (hd : sbtw c d a) :
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧ IsDiagonal s(a, c) ∧
      IsDiagonal s(b, d) ∧ Cross s(a, c) s(b, d) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  have ne : ∀ x y : ZMod m, basePos a x ≠ basePos a y → x ≠ y := fun x y h e => h (e ▸ rfl)
  refine ⟨⟨ne _ _ (by omega), ne _ _ (by omega), ne _ _ (by omega), ne _ _ (by omega),
    ne _ _ (by omega), ne _ _ (by omega)⟩, ⟨isSegment_mk_of_ne (ne _ _ (by omega)), ?_⟩,
    ⟨isSegment_mk_of_ne (ne _ _ (by omega)), ?_⟩, ⟨a, c, b, d, rfl, rfl, hb, hd⟩⟩ <;>
    · rw [isSide_mk_iff_basePos (c := a) (by omega)]
      omega

theorem cross_mk_of_interleave (c : ZMod m) {u v x y : ZMod m}
    (h : Interleave (basePosSeg c s(u, v)) (basePosSeg c s(x, y))) : Cross s(u, v) s(x, y) := by
  refine (cross_iff_interleave c (isSegment_mk_of_ne ?_) (isSegment_mk_of_ne ?_)).2 h <;>
    · rintro rfl
      simp only [basePosSeg_mk, Interleave] at h
      omega

theorem quadrilateral_cross_left_of_basePos (hb : sbtw a b c) (hd : sbtw c d a) {x y : ZMod m}
    (H : 0 < basePos a x ∧ basePos a x < basePos a c ∧ basePos a c < basePos a y) :
    s(x, y) = s(b, d) ∨ Cross s(x, y) s(a, b) ∨ Cross s(x, y) s(b, c) ∨
      Cross s(x, y) s(c, d) ∨ Cross s(x, y) s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  have hi := basePos_injective a
  rcases lt_trichotomy (basePos a x) (basePos a b) with hxb | hxb | hxb
  · exact Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · rcases lt_trichotomy (basePos a y) (basePos a d) with hyd | hyd | hyd
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
    · rw [hi hxb, hi hyd]; exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · exact Or.inr <| Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)

theorem quadrilateral_cross_right_of_basePos (hb : sbtw a b c) (hd : sbtw c d a) {x y : ZMod m}
    (H : basePos a b < basePos a x ∧ basePos a x < basePos a d ∧
      (basePos a y < basePos a b ∨ basePos a d < basePos a y)) :
    s(x, y) = s(a, c) ∨ Cross s(x, y) s(a, b) ∨ Cross s(x, y) s(b, c) ∨
      Cross s(x, y) s(c, d) ∨ Cross s(x, y) s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  have hi := basePos_injective a
  have := basePos_nonneg a y
  rcases lt_trichotomy (basePos a x) (basePos a c) with hxc | hxc | hxc
  · exact Or.inr <| Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · rcases H.2.2 with hy | hy
    · rcases eq_or_lt_of_le this with hy0 | hy0
      · rw [hi hxc, hi (hy0.symm.trans h0.symm), Sym2.eq_swap]; exact Or.inl rfl
      · exact Or.inr <| Or.inl <|
          cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)

theorem quadrilateral_cross_left (hb : sbtw a b c) (hd : sbtw c d a) {e : Sym2 (ZMod m)}
    (he : Cross e s(a, c)) :
    e = s(b, d) ∨ Cross e s(a, b) ∨ Cross e s(b, c) ∨ Cross e s(c, d) ∨ Cross e s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  induction e using Sym2.ind with | _ x y => ?_
  have := basePos_nonneg a x
  have := basePos_nonneg a y
  rw [cross_mk_iff_basePos a, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff] at he
  rcases (by omega : (0 < basePos a x ∧ basePos a x < basePos a c ∧ basePos a c < basePos a y) ∨
      (0 < basePos a y ∧ basePos a y < basePos a c ∧ basePos a c < basePos a x)) with H | H
  · exact quadrilateral_cross_left_of_basePos hb hd H
  · simpa only [Sym2.eq_swap (a := x)] using quadrilateral_cross_left_of_basePos hb hd H

theorem quadrilateral_cross_right (hb : sbtw a b c) (hd : sbtw c d a) {e : Sym2 (ZMod m)}
    (he : Cross e s(b, d)) :
    e = s(a, c) ∨ Cross e s(a, b) ∨ Cross e s(b, c) ∨ Cross e s(c, d) ∨ Cross e s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  induction e using Sym2.ind with | _ x y => ?_
  have := basePos_nonneg a x
  have := basePos_nonneg a y
  rw [cross_mk_iff_basePos a, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff] at he
  rcases (by omega : (basePos a b < basePos a x ∧ basePos a x < basePos a d ∧
        (basePos a y < basePos a b ∨ basePos a d < basePos a y)) ∨
      (basePos a b < basePos a y ∧ basePos a y < basePos a d ∧
        (basePos a x < basePos a b ∨ basePos a d < basePos a x))) with H | H
  · exact quadrilateral_cross_right_of_basePos hb hd H
  · simpa only [Sym2.eq_swap (a := x)] using quadrilateral_cross_right_of_basePos hb hd H

def IsFlipQuadrilateral (T : Finset (Sym2 (ZMod m))) (a b c d : ZMod m) : Prop :=
  sbtw a b c ∧ sbtw c d a ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T ∧
    s(c, d) ∈ segments T ∧ s(d, a) ∈ segments T

variable {T : Finset (Sym2 (ZMod m))} {a b c d : ZMod m}

theorem IsDiagonal.exists_sbtw {u v : ZMod m} (h : IsDiagonal s(u, v)) : ∃ x, sbtw u x v := by
  have huv : u ≠ v := fun e => h.1 (Sym2.mk_isDiag_iff.2 e)
  have h0 := basePos_self u
  have hpos := basePos_self_lt_of_ne huv
  have hs := (isSide_mk_iff_basePos hpos).not.1 h.2
  have := basePos_lt u v
  rw [h0] at hs hpos
  obtain ⟨x, hx⟩ := exists_basePos_eq u (k := 1) (by omega) (by omega)
  exact ⟨x, (sbtw_iff_basePos (by rwa [h0]) x).2 (by omega)⟩

theorem mem_segments_flipTriangulation {γ γ' r : Sym2 (ZMod m)} (hr : r ∈ segments T)
    (hne : r ≠ γ) : r ∈ segments (flipTriangulation T γ γ') := by
  rcases mem_segments.1 hr with hr | hr
  · exact mem_segments.2 (Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hne, hr⟩)))
  · exact mem_segments.2 (Or.inr hr)

theorem IsFlipQuadrilateral.rim_ne (hq : IsFlipQuadrilateral T a b c d) :
    s(a, b) ≠ s(a, c) ∧ s(b, c) ≠ s(a, c) ∧ s(c, d) ≠ s(a, c) ∧ s(d, a) ≠ s(a, c) := by
  obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, -⟩ := quadrilateral_cross hq.1 hq.2.1
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

theorem IsTriangulation.existsUnique_apex_of_mem (hm : 4 ≤ m) (hT : IsTriangulation T)
    (hγ : s(a, c) ∈ T) :
    (∃! b, sbtw a b c ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T) ∧
      ∃! d, sbtw c d a ∧ s(c, d) ∈ segments T ∧ s(d, a) ∈ segments T := by
  have hdiag := hT.isDiagonal _ hγ
  have hseg : s(a, c) ∈ segments T := mem_segments.2 (Or.inl hγ)
  refine ⟨IsTriangulation.existsUnique_apex (by omega) hT hseg (IsDiagonal.exists_sbtw hdiag),
    IsTriangulation.existsUnique_apex (by omega) hT (by rwa [Sym2.eq_swap])
      (IsDiagonal.exists_sbtw (by rwa [Sym2.eq_swap] at hdiag))⟩

theorem IsFlipQuadrilateral.isFlipReplacement (hT : IsTriangulation T)
    (hγ : s(a, c) ∈ T) (hq : IsFlipQuadrilateral T a b c d) :
    IsFlipReplacement T s(a, c) s(b, d) := by
  obtain ⟨r1, r2, r3, r4⟩ := hq.rim_ne
  obtain ⟨hb, hd, hab, hbc, hcd, hda⟩ := hq
  obtain ⟨-, -, hbd, hcross⟩ := quadrilateral_cross hb hd
  have hbdT : s(b, d) ∉ T := fun h => hT.noncrossing _ hγ _ h hcross
  have rim : ∀ f ∈ T, f ≠ s(a, c) → Cross f s(b, d) → False := by
    intro f hf hfγ hfc
    have hf' : f ∈ segments T := mem_segments.2 (Or.inl hf)
    rcases quadrilateral_cross_right hb hd hfc with h | h | h | h | h
    exacts [hfγ h, IsTriangulation.not_cross hT hf' hab h, IsTriangulation.not_cross hT hf' hbc h,
      IsTriangulation.not_cross hT hf' hcd h, IsTriangulation.not_cross hT hf' hda h]
  refine ⟨hT, hγ, hbd, hbdT, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    exacts [hbd, hT.isDiagonal e (Finset.mem_of_mem_erase he)]
  · intro e he f hf hef
    rcases Finset.mem_insert.1 he with rfl | he <;> rcases Finset.mem_insert.1 hf with rfl | hf
    · exact not_cross_self _ hef
    · exact rim f (Finset.mem_of_mem_erase hf) (Finset.ne_of_mem_erase hf) hef.symm
    · exact rim e (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he) hef
    · exact hT.noncrossing e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · intro e he heT'
    by_cases heγ : e = s(a, c)
    · exact ⟨s(b, d), Finset.mem_insert_self _ _, heγ ▸ hcross⟩
    have heT : e ∉ T := fun h => heT' (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨heγ, h⟩))
    obtain ⟨f, hf, hef⟩ := hT.maximal e he heT
    by_cases hfγ : f = s(a, c)
    · subst hfγ
      have key : ∀ r ∈ segments T, r ≠ s(a, c) → Cross e r →
          ∃ f ∈ flipTriangulation T s(a, c) s(b, d), Cross e f := by
        intro r hr hrγ her
        rcases mem_segments.1 hr with hr | hr
        · exact ⟨r, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrγ, hr⟩), her⟩
        · exact absurd her (not_cross_of_isSide hr)
      rcases quadrilateral_cross_left hb hd hef with h | h | h | h | h
      exacts [absurd (h ▸ Finset.mem_insert_self _ _) heT', key _ hab r1 h, key _ hbc r2 h,
        key _ hcd r3 h, key _ hda r4 h]
    · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfγ, hf⟩), hef⟩

theorem IsFlipQuadrilateral.eq_of_isFlipReplacement (hT : IsTriangulation T)
    (hq : IsFlipQuadrilateral T a b c d) {γ'' : Sym2 (ZMod m)}
    (h : IsFlipReplacement T s(a, c) γ'') : γ'' = s(b, d) := by
  obtain ⟨r1, r2, r3, r4⟩ := hq.rim_ne
  obtain ⟨hb, hd, hab, hbc, hcd, hda⟩ := hq
  obtain ⟨-, -, hγ'', hγ''T, hT''⟩ := h
  obtain ⟨f, hf, hcf⟩ := hT.maximal _ hγ'' hγ''T
  have hmem : γ'' ∈ segments (flipTriangulation T s(a, c) γ'') :=
    mem_segments.2 (Or.inl (Finset.mem_insert_self _ _))
  by_cases hfγ : f = s(a, c)
  · subst hfγ
    rcases quadrilateral_cross_left hb hd hcf with h | h | h | h | h
    exacts [h,
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hab r1)),
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hbc r2)),
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hcd r3)),
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hda r4))]
  · exact absurd hcf (hT''.noncrossing _ (Finset.mem_insert_self _ _) _
      (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfγ, hf⟩)))

theorem IsTriangulation.existsUnique_isFlipReplacement (hm : 4 ≤ m) (hT : IsTriangulation T)
    {γ : Sym2 (ZMod m)} (hγ : γ ∈ T) : ∃! γ', IsFlipReplacement T γ γ' := by
  induction γ using Sym2.ind with
  | _ a c =>
    obtain ⟨⟨b, hb, -⟩, ⟨d, hd, -⟩⟩ := IsTriangulation.existsUnique_apex_of_mem hm hT hγ
    have hq : IsFlipQuadrilateral T a b c d := ⟨hb.1, hd.1, hb.2.1, hb.2.2, hd.2.1, hd.2.2⟩
    exact ⟨s(b, d), hq.isFlipReplacement hT hγ,
      fun _ => hq.eq_of_isFlipReplacement hT⟩

end TypeA
end ClusterAlgebras

namespace D5.S3.Geometry.Polygons.PolygonTraceFlip
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual

variable {n : ℕ} [NeZero n]

noncomputable instance sym2Finite : Finite (Sym2 (ZMod n)) :=
  Finite.of_surjective (fun p : ZMod n × ZMod n => s(p.1, p.2)) (by
    intro e
    induction e using Sym2.ind with
    | _ a b => exact ⟨(a, b), rfl⟩)

noncomputable instance sym2Fintype : Fintype (Sym2 (ZMod n)) := Fintype.ofFinite _

noncomputable instance conditionFiberFinite {P Q J X : Finset (ZMod n)} :
    Finite (ConditionFiber P Q J X) :=
  Finite.of_injective Subtype.val Subtype.coe_injective

noncomputable instance conditionFiberFintype {P Q J X : Finset (ZMod n)} :
    Fintype (ConditionFiber P Q J X) := Fintype.ofFinite _

private lemma carrier_cross_iff {e f : Sym2 (ZMod n)} :
    Carrier.Cross e f ↔ ClusterAlgebras.Cross e f := by
  constructor <;> intro h <;>
    simpa only [Carrier.Cross, ClusterAlgebras.Cross] using h

private def toSupplierTri {T : Finset (Sym2 (ZMod n))}
    (hT : Carrier.IsTriangulation T) : ClusterAlgebras.IsTriangulation T :=
  (PolygonConditionalCounts.allEquiv (n := n) ⟨T, hT⟩).property

private def fromSupplierTri {T : Finset (Sym2 (ZMod n))}
    (hT : ClusterAlgebras.IsTriangulation T) : Carrier.IsTriangulation T :=
  ((PolygonConditionalCounts.allEquiv (n := n)).symm ⟨T, hT⟩).property

private noncomputable def flipDelta (hm : 4 ≤ n) {h : ZMod n}
    (T : Finset (Sym2 (ZMod n))) (hT : Carrier.IsTriangulation T)
    (hgamma : ear h ∈ T) : Sym2 (ZMod n) :=
  Classical.choose
    (ClusterAlgebras.TypeA.IsTriangulation.existsUnique_isFlipReplacement
      (m := n) hm (toSupplierTri hT) hgamma)

private theorem flipDelta_spec (hm : 4 ≤ n) {h : ZMod n}
    {T : Finset (Sym2 (ZMod n))} (hT : Carrier.IsTriangulation T)
    (hgamma : ear h ∈ T) :
    ClusterAlgebras.IsFlipReplacement T (ear h) (flipDelta hm T hT hgamma) := by
  exact (Classical.choose_spec
    (ClusterAlgebras.TypeA.IsTriangulation.existsUnique_isFlipReplacement
      (m := n) hm (toSupplierTri hT) hgamma)).1

noncomputable def actual_flip_trace_one
    (hn : 14 ≤ n) {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (hEars : ∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H,
      ¬Carrier.Cross (ear i) (ear j))
    (hDisj : Disjoint H (P ∪ Q)) (hh : h ∈ H) (hR : R ⊆ H.erase h)
    (x : ConditionFiber P Q H (insert h R)) :
    ConditionFiber P Q H R := by
  rcases x with ⟨T, hT, hP, hQ, htrace⟩
  have htrace_h : h ∈ EarCenters T ∩ H := by
    rw [htrace]
    simp
  have hgamma : ear h ∈ T := mem_earCenters.mp (Finset.mem_inter.1 htrace_h).1
  let δ := flipDelta (by omega) T hT hgamma
  have hflip := flipDelta_spec (by omega) hT hgamma
  have hδdiag : Carrier.IsDiagonal δ := by
    simpa only [Carrier.IsDiagonal, Carrier.IsSegment, Carrier.IsSide,
      ClusterAlgebras.IsDiagonal, ClusterAlgebras.IsSegment, ClusterAlgebras.IsSide] using hflip.2.2.1
  have hδnot : δ ∉ T := hflip.2.2.2.1
  have hU : Carrier.IsTriangulation (insert δ (T.erase (ear h))) :=
    fromSupplierTri hflip.2.2.2.2
  have hcrossδ : Carrier.Cross δ (ear h) := by
    obtain ⟨f, hf, hfcross⟩ := hT.maximal δ hδdiag hδnot
    have hf_eq : f = ear h := by
      by_contra hfne
      have hfU : f ∈ insert δ (T.erase (ear h)) :=
        Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfne, hf⟩)
      exact hU.noncrossing δ (Finset.mem_insert_self _ _) f hfU
        (carrier_cross_iff.mpr hfcross)
    simpa [hf_eq] using hfcross
  have hδ_ne_ear : ∀ i ∈ P ∪ Q ∪ H, δ ≠ ear i := by
    intro i hi hδi
    have hicross : Carrier.Cross (ear i) (ear h) := by simpa [hδi] using hcrossδ
    exact (hEars i hi h (Finset.mem_union_right _ hh)) hicross
  have hδ_ne_h : δ ≠ ear h := hδ_ne_ear h (Finset.mem_union_right _ hh)
  have hEarhU : ear h ∉ insert δ (T.erase (ear h)) := by
    intro hm
    rcases Finset.mem_insert.1 hm with heq | herase
    · exact hδ_ne_h heq.symm
    · exact (Finset.mem_erase.1 herase).1 rfl
  have hPout : P ⊆ EarCenters (insert δ (T.erase (ear h))) := by
    intro i hi
    have hiT : ear i ∈ T := mem_earCenters.mp (hP hi)
    have hih : i ≠ h := by
      intro e
      subst i
      exact (Finset.disjoint_left.1 hDisj) hh (Finset.mem_union_left _ hi)
    have hie : ear i ≠ ear h := fun e => hih ((PolygonConditionedFan.ear_injective (by omega)) e)
    apply mem_earCenters.mpr
    exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hie, hiT⟩)
  have hQout : Disjoint Q (EarCenters (insert δ (T.erase (ear h)))) := by
    refine Finset.disjoint_left.2 ?_
    intro i hi hiet
    have hiT : i ∉ EarCenters T := Finset.disjoint_left.1 hQ hi
    rcases Finset.mem_insert.1 (mem_earCenters.mp hiet) with hie | herase
    · exact hδ_ne_ear i (Finset.mem_union_left _ (Finset.mem_union_right _ hi)) hie.symm
    · exact hiT (mem_earCenters.mpr (Finset.mem_of_mem_erase herase))
  have htrace_out : EarCenters (insert δ (T.erase (ear h))) ∩ H = R := by
    ext i
    constructor
    · intro hi
      have hiParts := Finset.mem_inter.1 hi
      have hiU : ear i ∈ insert δ (T.erase (ear h)) := mem_earCenters.mp hiParts.1
      have hih : i ≠ h := by
        intro e
        subst i
        exact hEarhU hiU
      rcases Finset.mem_insert.1 hiU with hie | herase
      · exact (hδ_ne_ear i (Finset.mem_union_right _ hiParts.2) hie.symm).elim
      · have hiT : i ∈ EarCenters T := mem_earCenters.mpr (Finset.mem_of_mem_erase herase)
        have hitrace : i ∈ insert h R := by
          have : i ∈ EarCenters T ∩ H := Finset.mem_inter.2 ⟨hiT, hiParts.2⟩
          rwa [htrace] at this
        rcases Finset.mem_insert.1 hitrace with rfl | hiR
        · exact (hih rfl).elim
        · exact hiR
    · intro hiR
      have hiH : i ∈ H := (Finset.mem_erase.1 (hR hiR)).2
      have hih : i ≠ h := (Finset.mem_erase.1 (hR hiR)).1
      have hiT : i ∈ EarCenters T := by
        have : i ∈ EarCenters T ∩ H := by
          rw [htrace]
          exact Finset.mem_insert_of_mem hiR
        exact (Finset.mem_inter.1 this).1
      have hie : ear i ≠ ear h := fun e => hih ((PolygonConditionedFan.ear_injective (by omega)) e)
      have hiU : ear i ∈ insert δ (T.erase (ear h)) :=
        Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hie, mem_earCenters.mp hiT⟩)
      exact Finset.mem_inter.2 ⟨mem_earCenters.mpr hiU, hiH⟩
  exact ⟨insert δ (T.erase (ear h)), ⟨hU, hPout, hQout, htrace_out⟩⟩

private theorem flipDelta_cross (hm : 4 ≤ n) {h : ZMod n}
    {T : Finset (Sym2 (ZMod n))} (hT : Carrier.IsTriangulation T)
    (hgamma : ear h ∈ T) :
    Carrier.Cross (flipDelta hm T hT hgamma) (ear h) := by
  have hflip := flipDelta_spec hm hT hgamma
  have hδdiag : Carrier.IsDiagonal (flipDelta hm T hT hgamma) := by
    simpa only [Carrier.IsDiagonal, Carrier.IsSegment, Carrier.IsSide,
      ClusterAlgebras.IsDiagonal, ClusterAlgebras.IsSegment, ClusterAlgebras.IsSide] using hflip.2.2.1
  have hδnot : flipDelta hm T hT hgamma ∉ T := hflip.2.2.2.1
  have hU : Carrier.IsTriangulation (insert (flipDelta hm T hT hgamma) (T.erase (ear h))) :=
    fromSupplierTri hflip.2.2.2.2
  obtain ⟨f, hf, hfcross⟩ := hT.maximal _ hδdiag hδnot
  have hf_eq : f = ear h := by
    by_contra hfne
    have hfU : f ∈ insert (flipDelta hm T hT hgamma) (T.erase (ear h)) :=
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfne, hf⟩)
    exact hU.noncrossing _ (Finset.mem_insert_self _ _) f hfU
      (carrier_cross_iff.mpr hfcross)
  simpa [hf_eq] using hfcross

private theorem gamma_mem_of_fiber {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (x : ConditionFiber P Q H (insert h R)) : ear h ∈ x.1 := by
  have hi : h ∈ EarCenters x.1 ∩ H := by
    rw [x.2.2.2.2]
    simp
  exact mem_earCenters.mp (Finset.mem_inter.1 hi).1

noncomputable def actual_flip_trace_map
    (hn : 14 ≤ n) {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (hEars : ∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H,
      ¬Carrier.Cross (ear i) (ear j))
    (hDisj : Disjoint H (P ∪ Q)) (hh : h ∈ H) (hR : R ⊆ H.erase h) :
    ConditionFiber P Q H (insert h R) → ConditionFiber P Q H R :=
  actual_flip_trace_one hn hEars hDisj hh hR

private theorem actual_flip_trace_map_val
    (hn : 14 ≤ n) {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (hEars : ∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H,
      ¬Carrier.Cross (ear i) (ear j))
    (hDisj : Disjoint H (P ∪ Q)) (hh : h ∈ H) (hR : R ⊆ H.erase h)
    (x : ConditionFiber P Q H (insert h R)) :
    (actual_flip_trace_map hn hEars hDisj hh hR x).1 =
      insert (flipDelta (by omega) x.1 x.2.1 (gamma_mem_of_fiber x))
        (x.1.erase (ear h)) := by
  rfl

theorem actual_flip_trace_injective
    (hn : 14 ≤ n) {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (hEars : ∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H,
      ¬Carrier.Cross (ear i) (ear j))
    (hDisj : Disjoint H (P ∪ Q)) (hh : h ∈ H) (hR : R ⊆ H.erase h) :
    Function.Injective (actual_flip_trace_map hn hEars hDisj hh hR) := by
  intro x y hxy
  have hval := congrArg Subtype.val hxy
  rw [actual_flip_trace_map_val hn hEars hDisj hh hR x,
    actual_flip_trace_map_val hn hEars hDisj hh hR y] at hval
  let δx := flipDelta (by omega) x.1 x.2.1 (gamma_mem_of_fiber x)
  let δy := flipDelta (by omega) y.1 y.2.1 (gamma_mem_of_fiber y)
  have hval' : insert δx (x.1.erase (ear h)) = insert δy (y.1.erase (ear h)) := by
    simpa [δx, δy] using hval
  have hcrossx : Carrier.Cross δx (ear h) := by
    simpa [δx] using
      (flipDelta_cross (n := n) (by omega) x.2.1 (gamma_mem_of_fiber x))
  have hδx_mem_y : δx ∈ insert δy (y.1.erase (ear h)) := by
    rw [← hval']
    exact Finset.mem_insert_self _ _
  have hδeq : δx = δy := by
    rcases Finset.mem_insert.1 hδx_mem_y with heq | herase
    · exact heq
    · have hret : δx ∈ y.1 := Finset.mem_of_mem_erase herase
      exact (y.2.1.noncrossing (ear h) (gamma_mem_of_fiber y)
        δx hret (Carrier.cross_symm hcrossx)).elim
  have hδnotx : δx ∉ x.1 := by
    simpa [δx] using
      (flipDelta_spec (n := n) (by omega) x.2.1 (gamma_mem_of_fiber x)).2.2.2.1
  have hδnoty : δy ∉ y.1 := by
    simpa [δy] using
      (flipDelta_spec (n := n) (by omega) y.2.1 (gamma_mem_of_fiber y)).2.2.2.1
  have hδnotxE : δx ∉ x.1.erase (ear h) := fun he => hδnotx (Finset.mem_of_mem_erase he)
  have hδnotyE : δx ∉ y.1.erase (ear h) := by
    intro he
    apply hδnoty
    rw [← hδeq]
    exact Finset.mem_of_mem_erase he
  have hδnotyE' : δy ∉ y.1.erase (ear h) :=
    fun he => hδnoty (Finset.mem_of_mem_erase he)
  have herase := congrArg (fun s : Finset (Sym2 (ZMod n)) => s.erase δx) hval'
  have hErase : x.1.erase (ear h) = y.1.erase (ear h) := by
    calc
      x.1.erase (ear h) = (insert δx (x.1.erase (ear h))).erase δx := by
        simp [hδnotxE]
      _ = (insert δy (y.1.erase (ear h))).erase δx := herase
      _ = y.1.erase (ear h) := by rw [hδeq]; simp [hδnotyE']
  apply Subtype.ext
  calc
    x.1 = insert (ear h) (x.1.erase (ear h)) :=
      (Finset.insert_erase (gamma_mem_of_fiber x)).symm
    _ = insert (ear h) (y.1.erase (ear h)) := congrArg (insert (ear h)) hErase
    _ = y.1 := Finset.insert_erase (gamma_mem_of_fiber y)

theorem actual_flip_trace_card_le
    (hn : 14 ≤ n) {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (hEars : ∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H,
      ¬Carrier.Cross (ear i) (ear j))
    (hDisj : Disjoint H (P ∪ Q)) (hh : h ∈ H) (hR : R ⊆ H.erase h) :
    Fintype.card (ConditionFiber P Q H (insert h R)) ≤
      Fintype.card (ConditionFiber P Q H R) := by
  classical
  exact Fintype.card_le_of_injective
    (actual_flip_trace_map hn hEars hDisj hh hR)
    (actual_flip_trace_injective hn hEars hDisj hh hR)

end D5.S3.Geometry.Polygons.PolygonTraceFlip
