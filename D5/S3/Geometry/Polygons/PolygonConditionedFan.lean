/- GID: D5/S3/Geometry/Polygons/PolygonConditionedFan
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonConditionedFan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal forced-ear fans on the original cyclic polygon and actual conditioned completions. -/

import D5.S3.Geometry.Polygons.PolygonEarSlide

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Geometry.Polygons.PolygonConditionedFan
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual

variable {n : ℕ} [NeZero n]

def Independent (P : Finset (ZMod n)) : Prop := ∀ i ∈ P, i + 1 ∉ P

def fan (P : Finset (ZMod n)) (h : ZMod n) : Finset (Sym2 (ZMod n)) :=
  P.image ear ∪ (univ.filter (fun j => j ∉ P ∧ IsDiagonal s(h, j))).image
    (fun j => s(h, j))

private lemma diagonal_iff (a b : ZMod n) :
    IsDiagonal s(a, b) ↔ a ≠ b ∧ b ≠ a + 1 ∧ a ≠ b + 1 := by
  simp only [IsDiagonal, IsSegment, Sym2.mk_isDiag_iff, IsSide, Sym2.eq_iff]
  constructor
  · rintro ⟨hab, hs⟩
    exact ⟨hab, fun h => hs ⟨a, Or.inl ⟨rfl, h⟩⟩,
      fun h => hs ⟨b, Or.inr ⟨h, rfl⟩⟩⟩
  · rintro ⟨hab, hb, ha⟩
    refine ⟨hab, ?_⟩
    rintro ⟨i, (⟨rfl, h⟩ | ⟨h, rfl⟩)⟩
    · exact hb h
    · exact ha h

private lemma cross_iff (a b c d : ZMod n) :
    Cross s(a, b) s(c, d) ↔
      (sbtw a c b ∧ sbtw b d a) ∨ (sbtw a d b ∧ sbtw b c a) := by
  constructor
  · rintro ⟨x, y, z, w, he, hf, hx, hy⟩
    rw [Sym2.eq_iff] at he hf
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact Or.inr ⟨hy, hx⟩
    · exact Or.inl ⟨hy, hx⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact ⟨a, b, c, d, rfl, rfl, hx, hy⟩
    · exact ⟨a, b, d, c, rfl, Sym2.eq_swap, hx, hy⟩

private lemma no_cross_spokes (h a b : ZMod n) : ¬Cross s(h, a) s(h, b) := by
  rw [cross_iff]
  rintro (⟨hx, _⟩ | ⟨_, hx⟩)
  · exact sbtw_irrefl_left hx
  · exact sbtw_irrefl_right hx

private lemma ear_cross_endpoint (hn : 6 ≤ n) (i a b : ZMod n)
    (hc : Cross (ear i) s(a, b)) : i = a ∨ i = b := by
  have hc' := cross_map_add_actual hc (1 - i)
  have he : (ear i).map (fun x => x + (1-i)) = sEar (n := n) := by
    rw [← ear_add]
    congr 1
    ring
  rw [he] at hc'
  obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn hc'
  change s(a + (1-i), b + (1-i)) = s(1, x) at hx
  rw [Sym2.eq_iff] at hx
  rcases hx with ⟨ha, _⟩ | ⟨_, hb⟩
  · left; linear_combination -ha
  · right; linear_combination -hb

private lemma cross_ear_spoke (hn : 6 ≤ n) (i x : ZMod n)
    (he : IsDiagonal s(i, x)) : Cross s(i, x) (ear i) := by
  have he' := isDiagonal_map_add he (1-i)
  change IsDiagonal s(i+(1-i), x+(1-i)) at he'
  have hi : i+(1-i) = 1 := by ring
  rw [hi, diagonal_iff] at he'
  have hc := cross_incident_one hn (x := x+(1-i))
    (by intro hx; apply he'.2.2; rw [hx]; simp)
    he'.1.symm (by simpa only [show (1 : ZMod n)+1=2 by ring] using he'.2.1)
  have hb := cross_map_add_actual hc (i-1)
  simpa only [sEar, ← ear_add, Sym2.map_mk,
    show (1 : ZMod n)+(i-1)=i by ring,
    show x+(1-i)+(i-1)=x by ring] using hb

private lemma ear_diagonal (hn : 6 ≤ n) (i : ZMod n) : IsDiagonal (ear i) := by
  have h := isDiagonal_map_add (isDiagonal_sEar hn) (i-1)
  simpa only [sEar, ← ear_add, show (1 : ZMod n)+(i-1)=i by ring] using h

private lemma ear_injective (hn : 6 ≤ n) : Function.Injective (ear (n := n)) := by
  intro i j he
  change s(i-1,i+1)=s(j-1,j+1) at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h, _⟩ | ⟨h, k⟩
  · linear_combination h
  · have hz : (4 : ZMod n) = 0 := by linear_combination -h+k
    change ((4 : ℕ) : ZMod n) = 0 at hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (show 4 < n by omega), ZMod.val_zero] at hv
    omega

private lemma adjacent_cross (hn : 6 ≤ n) (i : ZMod n) :
    Cross (ear i) (ear (i+1)) := by
  have hc := (cross_ear_shift_iff (i := 0) (j := 1) (a := i)).2
    (cross_symm (local_crossings hn).2.2)
  simpa only [zero_add, add_zero, add_comm, sEar, e₀] using hc

private lemma independent_of_noncrossing (hn : 6 ≤ n) (P : Finset (ZMod n))
    (hP : (P : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j))) : Independent P := by
  intro i hi hj
  have hc := adjacent_cross hn i
  by_cases he : i = i+1
  · rw [← he] at hc
    exact not_cross_self _ hc
  · exact hP hi hj he hc

private lemma forced_mem {P : Finset (ZMod n)} {h i : ZMod n} (hi : i ∈ P) :
    ear i ∈ fan P h := mem_union_left _ (mem_image_of_mem ear hi)

private lemma spoke_mem {P : Finset (ZMod n)} {h j : ZMod n}
    (hj : j ∉ P) (he : IsDiagonal s(h,j)) : s(h,j) ∈ fan P h :=
  mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hj, he⟩))

private lemma gap_spoke (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (a b c : ℕ) (ha : 0 < a) (hac : a < c) (hcb : c < b) (hb : b < n)
    (hcP : (c : ZMod n)+h ∉ P) :
    ∃ f ∈ fan P h, Cross s((a : ZMod n)+h, (b : ZMod n)+h) f := by
  have hd : IsDiagonal s((0 : ZMod n), (c : ZMod n)) := by
    rw [diagonal_iff]
    have h0 := ZMod.val_zero (n := n)
    have hv := ZMod.val_natCast_of_lt (show c < n by omega)
    have hv1 := ZMod.val_natCast_of_lt (show 1 < n by omega)
    have hvp := ZMod.val_natCast_of_lt (show c+1 < n by omega)
    refine ⟨?_, ?_, ?_⟩
    · intro he; have hh := congrArg ZMod.val he; simp only [h0, hv] at hh; omega
    · intro he; have hh := congrArg ZMod.val he
      simp only [zero_add, h0, hv, hv1] at hh; omega
    · intro he
      change (0 : ZMod n) = ((c+1 : ℕ) : ZMod n) at he
      have hh := congrArg ZMod.val he; simp only [h0, hvp] at hh; omega
  have hc : Cross s((a : ZMod n), (b : ZMod n)) s(0, (c : ZMod n)) := by
    refine ⟨(a : ZMod n), (b : ZMod n), (c : ZMod n), 0,
      rfl, Sym2.eq_swap, ?_, ?_⟩ <;>
      rw [sbtw_val hn] <;>
      simp only [ZMod.val_natCast_of_lt (show a < n by omega),
        ZMod.val_natCast_of_lt (show b < n by omega),
        ZMod.val_natCast_of_lt (show c < n by omega), ZMod.val_zero] <;> omega
  refine ⟨s(h, (c : ZMod n)+h), spoke_mem hcP ?_, ?_⟩
  · simpa only [Sym2.map_mk, zero_add] using isDiagonal_map_add hd h
  · simpa only [Sym2.map_mk, zero_add] using cross_map_add_actual hc h

private lemma gap_maximal (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hP : Independent P) (a b : ℕ) (hab : a < b) (hb : b < n)
    (he : IsDiagonal s((a : ZMod n)+h, (b : ZMod n)+h))
    (hout : s((a : ZMod n)+h, (b : ZMod n)+h) ∉ fan P h)
    (haP : (a : ZMod n)+h ∉ P) (hbP : (b : ZMod n)+h ∉ P) :
    ∃ f ∈ fan P h, Cross s((a : ZMod n)+h, (b : ZMod n)+h) f := by
  have ha : 0 < a := by
    by_contra hz
    have ha0 : a = 0 := by omega
    subst a
    simp only [Nat.cast_zero, zero_add] at he hout
    exact hout (spoke_mem hbP he)
  have hgap : a+2 ≤ b := by
    have hd := (diagonal_iff _ _).1 he
    by_contra hg
    have hba : b = a+1 := by omega
    apply hd.2.1
    rw [hba, Nat.cast_add, Nat.cast_one]
    ring
  by_cases hc : ((a+1 : ℕ) : ZMod n)+h ∉ P
  · exact gap_spoke hn P h a b (a+1) ha (by omega) (by omega) hb hc
  · have hcP : ((a+1 : ℕ) : ZMod n)+h ∈ P := by tauto
    have hbne : b ≠ a+2 := by
      intro heq
      apply hout
      have hea : ear (((a+1 : ℕ) : ZMod n)+h) =
          s((a : ZMod n)+h, (b : ZMod n)+h) := by
        rw [heq, ear]
        congr 1 <;> push_cast <;> ring
      rw [← hea]
      exact forced_mem hcP
    have hcnext : ((a+2 : ℕ) : ZMod n)+h ∉ P := by
      have hnext := hP _ hcP
      convert hnext using 1 <;> push_cast <;> ring
    exact gap_spoke hn P h a b (a+2) ha (by omega) (by omega) hb hcnext

theorem fan_isTriangulation (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hP : Independent P) (hh : h ∉ P) : IsTriangulation (fan P h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp he
      exact ear_diagonal hn p
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp he
      exact (mem_filter.mp hj).2.2
  · intro e he f hf hc
    rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp he
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hf
      rcases ear_cross_endpoint hn p (q-1) (q+1) hc with hpq | hpq
      · apply hP p hp
        convert hq using 1
        linear_combination hpq
      · exact hP q hq (hpq ▸ hp)
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp he
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hf
      rcases ear_cross_endpoint hn p h j hc with rfl | rfl
      · exact hh hp
      · exact (mem_filter.mp hj).2.1 hp
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp he
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hf
      rcases ear_cross_endpoint hn p h j (cross_symm hc) with rfl | rfl
      · exact hh hp
      · exact (mem_filter.mp hj).2.1 hp
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp he
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hf
      exact no_cross_spokes h j k hc
  · intro e he hout
    induction e using Sym2.ind with
    | _ x y =>
      by_cases hxP : x ∈ P
      · exact ⟨ear x, forced_mem hxP, cross_ear_spoke hn x y he⟩
      by_cases hyP : y ∈ P
      · refine ⟨ear y, forced_mem hyP, ?_⟩
        rw [Sym2.eq_swap] at he ⊢
        exact cross_ear_spoke hn y x he
      have hx : ((x-h).val : ZMod n)+h = x := by simp
      have hy : ((y-h).val : ZMod n)+h = y := by simp
      have hne : (x-h).val ≠ (y-h).val := by
        intro hv
        apply (diagonal_iff x y).1 he |>.1
        rw [← hx, ← hy, hv]
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · rw [← hx, ← hy] at he hout ⊢
        exact gap_maximal hn P h hP _ _ hlt (ZMod.val_lt _) he hout
          (hx ▸ hxP) (hy ▸ hyP)
      · have hs : s(x,y) = s(y,x) := Sym2.eq_swap
        rw [hs, ← hx, ← hy] at he hout ⊢
        exact gap_maximal hn P h hP _ _ hlt (ZMod.val_lt _) he hout
          (hy ▸ hyP) (hx ▸ hxP)

private lemma ear_bounds (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n) :
    P ⊆ EarCenters (fan P h) ∧
      EarCenters (fan P h) ⊆ P ∪ {h-1,h+1} := by
  refine ⟨fun i hi => mem_earCenters.mpr (forced_mem hi), ?_⟩
  intro i hi
  rcases mem_union.mp (mem_earCenters.mp hi) with hi | hi
  · obtain ⟨p, hp, he⟩ := mem_image.mp hi
    exact mem_union_left _ ((ear_injective hn he) ▸ hp)
  · obtain ⟨j, hj, he⟩ := mem_image.mp hi
    change s(h,j)=s(i-1,i+1) at he
    rw [Sym2.eq_iff] at he
    apply mem_union_right
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · have hi : i=h+1 := by linear_combination -he
      simp [hi]
    · have hi : i=h-1 := by linear_combination -he
      simp [hi]

end D5.S3.Geometry.Polygons.PolygonConditionedFan
