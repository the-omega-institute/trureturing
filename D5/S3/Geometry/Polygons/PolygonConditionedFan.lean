/- GID: D5/S3/Geometry/Polygons/PolygonConditionedFan
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonConditionedFan
   mirror-E: none(waiver:evidence - not - specified - by - formal - manifest)
   anchors: []
   utility: none
   digest: Literal forced - ear fans and actual conditioned polygon completions. -/

import D5.S3.Geometry.Polygons.PolygonEarSlide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Forced ears and surviving root spokes on the original cyclic polygon. -/

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
  have he : (ear i).map (fun x => x + (1 - i)) = sEar (n := n) := by
    rw [← ear_add]
    congr 1
    ring
  rw [he] at hc'
  obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn hc'
  change s(a + (1 - i), b + (1 - i)) = s(1, x) at hx
  rw [Sym2.eq_iff] at hx
  rcases hx with ⟨ha, _⟩ | ⟨_, hb⟩
  · left; linear_combination -ha
  · right; linear_combination -hb

private lemma cross_ear_spoke (hn : 6 ≤ n) (i x : ZMod n)
    (he : IsDiagonal s(i, x)) : Cross s(i, x) (ear i) := by
  have he' := isDiagonal_map_add he (1 - i)
  change IsDiagonal s(i + (1 - i), x + (1 - i)) at he'
  have hi : i + (1 - i) = 1 := by ring
  rw [hi, diagonal_iff] at he'
  have hc := cross_incident_one hn (x := x + (1 - i))
    (by intro hx; apply he'.2.2; rw [hx]; simp)
    he'.1.symm (by simpa only [show (1 : ZMod n) + 1=2 by ring] using he'.2.1)
  have hb := cross_map_add_actual hc (i - 1)
  simpa only [sEar, ← ear_add, Sym2.map_mk,
    show (1 : ZMod n) + (i - 1)=i by ring,
    show x + (1 - i) + (i - 1)=x by ring] using hb

private lemma ear_diagonal (hn : 6 ≤ n) (i : ZMod n) : IsDiagonal (ear i) := by
  have h := isDiagonal_map_add (isDiagonal_sEar hn) (i - 1)
  simpa only [sEar, ← ear_add, show (1 : ZMod n) + (i - 1)=i by ring] using h

lemma ear_injective (hn : 6 ≤ n) : Function.Injective (ear (n := n)) := by
  intro i j he
  change s(i - 1, i + 1)=s(j - 1, j + 1) at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h, _⟩ | ⟨h, k⟩
  · linear_combination h
  · have hz : (4 : ZMod n) = 0 := by linear_combination -h + k
    change ((4 : ℕ) : ZMod n) = 0 at hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (show 4 < n by omega), ZMod.val_zero] at hv
    omega

private lemma adjacent_cross (hn : 6 ≤ n) (i : ZMod n) :
    Cross (ear i) (ear (i + 1)) := by
  have hc := (cross_ear_shift_iff (i := 0) (j := 1) (a := i)).2
    (cross_symm (local_crossings hn).2.2)
  simpa only [zero_add, add_zero, add_comm, sEar, e₀] using hc

private lemma independent_of_noncrossing (hn : 6 ≤ n) (P : Finset (ZMod n))
    (hP : (P : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j))) : Independent P := by
  intro i hi hj
  have hc := adjacent_cross hn i
  by_cases he : i = i + 1
  · rw [← he] at hc
    exact not_cross_self _ hc
  · exact hP hi hj he hc

private lemma forced_mem {P : Finset (ZMod n)} {h i : ZMod n} (hi : i ∈ P) :
    ear i ∈ fan P h := mem_union_left _ (mem_image_of_mem ear hi)

private lemma spoke_mem {P : Finset (ZMod n)} {h j : ZMod n}
    (hj : j ∉ P) (he : IsDiagonal s(h, j)) : s(h, j) ∈ fan P h :=
  mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hj, he⟩))

private lemma gap_spoke (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (a b c : ℕ) (ha : 0 < a) (hac : a < c) (hcb : c < b) (hb : b < n)
    (hcP : (c : ZMod n) + h ∉ P) :
    ∃ f ∈ fan P h, Cross s((a : ZMod n) + h, (b : ZMod n) + h) f := by
  have hd : IsDiagonal s((0 : ZMod n), (c : ZMod n)) := by
    rw [diagonal_iff]
    have h0 := ZMod.val_zero (n := n)
    have hv := ZMod.val_natCast_of_lt (show c < n by omega)
    have hv1 : (1 : ZMod n).val = 1 := by
      simpa using ZMod.val_natCast_of_lt (show 1 < n by omega)
    have hvp := ZMod.val_natCast_of_lt (show c + 1 < n by omega)
    refine ⟨?_, ?_, ?_⟩
    · intro he; have hh := congrArg ZMod.val he; simp only [h0, hv] at hh; omega
    · intro he; have hh := congrArg ZMod.val he
      simp only [zero_add, h0, hv, hv1] at hh; omega
    · intro he
      have he' : (0 : ZMod n) = ((c + 1 : ℕ) : ZMod n) := by
        simpa only [Nat.cast_add, Nat.cast_one] using he
      have hh := congrArg ZMod.val he'; simp only [h0, hvp] at hh; omega
  have hc : Cross s((a : ZMod n), (b : ZMod n)) s(0, (c : ZMod n)) := by
    refine ⟨(a : ZMod n), (b : ZMod n), (c : ZMod n), 0,
      rfl, Sym2.eq_swap, ?_, ?_⟩ <;>
      rw [sbtw_val hn] <;>
      simp only [ZMod.val_natCast_of_lt (show a < n by omega),
        ZMod.val_natCast_of_lt (show b < n by omega),
        ZMod.val_natCast_of_lt (show c < n by omega), ZMod.val_zero] <;> omega
  refine ⟨s(h, (c : ZMod n) + h), spoke_mem hcP ?_, ?_⟩
  · simpa only [Sym2.map_mk, zero_add] using isDiagonal_map_add hd h
  · simpa only [Sym2.map_mk, zero_add] using cross_map_add_actual hc h

private lemma gap_maximal (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hP : Independent P) (a b : ℕ) (hab : a < b) (hb : b < n)
    (he : IsDiagonal s((a : ZMod n) + h, (b : ZMod n) + h))
    (hout : s((a : ZMod n) + h, (b : ZMod n) + h) ∉ fan P h)
    (hbP : (b : ZMod n) + h ∉ P) :
    ∃ f ∈ fan P h, Cross s((a : ZMod n) + h, (b : ZMod n) + h) f := by
  have ha : 0 < a := by
    by_contra hz
    have ha0 : a = 0 := by omega
    subst a
    simp only [Nat.cast_zero, zero_add] at he hout
    exact hout (spoke_mem hbP he)
  have hgap : a + 2 ≤ b := by
    have hd := (diagonal_iff _ _).1 he
    by_contra hg
    have hba : b = a + 1 := by omega
    apply hd.2.1
    rw [hba, Nat.cast_add, Nat.cast_one]
    ring
  by_cases hc : ((a + 1 : ℕ) : ZMod n) + h ∉ P
  · exact gap_spoke hn P h a b (a + 1) ha (by omega) (by omega) hb hc
  · have hcP : ((a + 1 : ℕ) : ZMod n) + h ∈ P := by tauto
    have hbne : b ≠ a + 2 := by
      intro heq
      apply hout
      have hea : ear (((a + 1 : ℕ) : ZMod n) + h) =
          s((a : ZMod n) + h, (b : ZMod n) + h) := by
        rw [heq, ear]
        congr 1 <;> push_cast <;> ring
      rw [← hea]
      exact forced_mem hcP
    have hcnext : ((a + 2 : ℕ) : ZMod n) + h ∉ P := by
      have hnext := hP _ hcP
      have heq : ((a + 2 : ℕ) : ZMod n) + h =
          (((a + 1 : ℕ) : ZMod n) + h) + 1 := by push_cast; ring
      rw [heq]
      exact hnext
    exact gap_spoke hn P h a b (a + 2) ha (by omega) (by omega) hb hcnext

private theorem fan_geometry (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
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
      rcases ear_cross_endpoint hn p (q - 1) (q + 1) hc with hpq | hpq
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
      have hx : ((x - h).val : ZMod n) + h = x := by simp
      have hy : ((y - h).val : ZMod n) + h = y := by simp
      have hne : (x - h).val ≠ (y - h).val := by
        intro hv
        apply (diagonal_iff x y).1 he |>.1
        rw [← hx, ← hy, hv]
      have he' : IsDiagonal s(((x - h).val : ZMod n) + h, ((y - h).val : ZMod n) + h) := by
        simpa only [hx, hy] using he
      have hout' : s(((x - h).val : ZMod n) + h, ((y - h).val : ZMod n) + h) ∉ fan P h := by
        simpa only [hx, hy] using hout
      have hxP' : ((x - h).val : ZMod n) + h ∉ P := by simpa only [hx] using hxP
      have hyP' : ((y - h).val : ZMod n) + h ∉ P := by simpa only [hy] using hyP
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hres := gap_maximal hn P h hP _ _ hlt (ZMod.val_lt _) he' hout' hyP'
        simpa only [hx, hy] using hres
      · have heSwap : IsDiagonal
            s(((y - h).val : ZMod n) + h, ((x - h).val : ZMod n) + h) := by
          rw [Sym2.eq_swap]
          exact he'
        have houtSwap :
            s(((y - h).val : ZMod n) + h, ((x - h).val : ZMod n) + h) ∉ fan P h := by
          rw [Sym2.eq_swap]
          exact hout'
        have hres := gap_maximal hn P h hP _ _ hlt (ZMod.val_lt _)
          heSwap houtSwap hxP'
        rw [Sym2.eq_swap]
        simpa only [hx, hy] using hres

private lemma ear_bounds (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n) :
    P ⊆ EarCenters (fan P h) ∧
      EarCenters (fan P h) ⊆ P ∪ {h - 1, h + 1} := by
  refine ⟨fun i hi => mem_earCenters.mpr (forced_mem hi), ?_⟩
  intro i hi
  rcases mem_union.mp (mem_earCenters.mp hi) with hi | hi
  · obtain ⟨p, hp, he⟩ := mem_image.mp hi
    exact mem_union_left _ ((ear_injective hn he) ▸ hp)
  · obtain ⟨j, hj, he⟩ := mem_image.mp hi
    change s(h, j)=s(i - 1, i + 1) at he
    rw [Sym2.eq_iff] at he
    apply mem_union_right
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · have hi : i=h + 1 := by linear_combination -he
      simp [hi]
    · have hi : i=h - 1 := by linear_combination -he
      simp [hi]

/-- The literal union is maximal on all original internal diagonals, with controlled ears. -/
theorem fan_triangulation (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hP : Independent P) (hh : h ∉ P) :
    IsTriangulation (fan P h) ∧ P ⊆ EarCenters (fan P h) ∧
      EarCenters (fan P h) ⊆ P ∪ {h - 1, h + 1} :=
  ⟨fan_geometry hn P h hP hh, ear_bounds hn P h⟩

/-- Two distinct original internal spokes cross the root ear. -/
theorem fan_two_crossings (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hsize : P.card + 4 < n) :
    ∃ e ∈ fan P h, ∃ f ∈ fan P h, e ≠ f ∧ IsDiagonal e ∧ IsDiagonal f ∧
      Cross e (ear h) ∧ Cross f (ear h) := by
  let B : Finset (ZMod n) := P ∪ {h, h - 1, h + 1}
  have hB : B.card ≤ P.card + 3 := by
    have h3 : ({h, h - 1, h + 1} : Finset (ZMod n)).card ≤ 3 := by
      exact (card_insert_le _ _).trans
        (Nat.add_le_add_right ((card_insert_le _ _).trans (by simp)) 1)
    exact (card_union_le _ _).trans (Nat.add_le_add_left h3 _)
  have htargets : 1 < (univ \ B).card := by
    rw [card_sdiff_of_subset (subset_univ B), card_univ, ZMod.card]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := one_lt_card.mp htargets
  have good (x : ZMod n) (hx : x ∈ univ \ B) :
      x ∉ P ∧ IsDiagonal s(h, x) := by
    have hxB := (mem_sdiff.mp hx).2
    have hxP : x ∉ P := fun hxp => hxB (mem_union_left _ hxp)
    have hx0 : x ≠ h := by intro he; apply hxB; simp [B, he]
    have hxm : x ≠ h - 1 := by intro he; apply hxB; simp [B, he]
    have hxp : x ≠ h + 1 := by intro he; apply hxB; simp [B, he]
    refine ⟨hxP, (diagonal_iff _ _).2 ⟨hx0.symm, hxp, ?_⟩⟩
    intro he
    apply hxm
    linear_combination -he
  obtain ⟨hjP, hjd⟩ := good j hj
  obtain ⟨hkP, hkd⟩ := good k hk
  refine ⟨s(h, j), spoke_mem hjP hjd, s(h, k), spoke_mem hkP hkd,
    ?_, hjd, hkd, cross_ear_spoke hn h j hjd, cross_ear_spoke hn h k hkd⟩
  intro he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨_, he⟩ | ⟨he, hf⟩
  · exact hjk he
  · exact hjk (hf.trans he)

private lemma choose_root (P Q : Finset (ZMod n)) (hsize : P.card + 2 * Q.card < n) :
    ∃ h : ZMod n, h ∉ P ∧ h - 1 ∉ Q ∧ h + 1 ∉ Q := by
  let B := (P ∪ Q.image (fun q => q - 1)) ∪ Q.image (fun q => q + 1)
  have hB : B.card ≤ P.card + 2 * Q.card := by
    have h1 := card_union_le P (Q.image (fun q => q - 1))
    have h2 := card_union_le (P ∪ Q.image (fun q => q - 1)) (Q.image (fun q => q + 1))
    have h3 := card_image_le (s := Q) (f := fun q => q - 1)
    have h4 := card_image_le (s := Q) (f := fun q => q + 1)
    dsimp [B]
    omega
  have hb : B.card < (univ : Finset (ZMod n)).card := by
    rw [card_univ, ZMod.card]
    omega
  obtain ⟨h, _, hh⟩ := exists_mem_notMem_of_card_lt_card hb
  refine ⟨h, ?_, ?_, ?_⟩
  · intro hp; exact hh (mem_union_left _ (mem_union_left _ hp))
  · intro hq
    apply hh
    apply mem_union_right
    exact mem_image.mpr ⟨h - 1, hq, by ring⟩
  · intro hq
    apply hh
    apply mem_union_left
    apply mem_union_right
    exact mem_image.mpr ⟨h + 1, hq, by ring⟩

private lemma conditioned_completion (hn : 6 ≤ n) (P Q J : Finset (ZMod n))
    (h : ZMod n) (hP : Independent P) (hh : h ∉ P)
    (hdisj : Disjoint P (Q ∪ J)) (hm : h - 1 ∉ Q ∪ J) (hp : h + 1 ∉ Q ∪ J) :
    ∃ T : ConditionFiber P Q J ∅, T.val = fan P h := by
  have ht := fan_triangulation hn P h hP hh
  have avoid : Disjoint (Q ∪ J) (EarCenters (fan P h)) := by
    apply disjoint_left.mpr
    intro i hi hiE
    rcases mem_union.mp (ht.2.2 hiE) with hiP | hiN
    · exact disjoint_left.mp hdisj hiP hi
    · simp only [mem_insert, mem_singleton] at hiN
      rcases hiN with rfl | rfl
      · exact hm hi
      · exact hp hi
  refine ⟨⟨fan P h, ht.1, ht.2.1, ?_, ?_⟩, rfl⟩
  · exact disjoint_left.mpr fun i hi hiE =>
      disjoint_left.mp avoid (mem_union_left J hi) hiE
  · apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact disjoint_left.mp avoid (mem_union_right Q (mem_inter.mp hi).2)
      (mem_inter.mp hi).1

private lemma compatible_neighbors (hn : 6 ≤ n) (S : Finset (ZMod n))
    (h : ZMod n) (hc : ∀ i ∈ S, ¬Cross (ear h) (ear i)) :
    h - 1 ∉ S ∧ h + 1 ∉ S := by
  refine ⟨?_, ?_⟩
  · intro hi
    apply hc _ hi
    exact cross_symm (by simpa only [sub_add_cancel] using adjacent_cross hn (h - 1))
  · intro hi
    exact hc _ hi (adjacent_cross hn h)

/-- Actual original - carrier positivity and a terminal empty - trace fan with two crossings. -/
theorem source_conditioned_witnesses (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hdisj : Disjoint P Q)
    (hcompat : (↑(P ∪ Q) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : (P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
      (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)) :
    Nonempty (ConditionFiber P Q ∅ ∅) ∧
      0 < Nat.card (ConditionFiber P Q ∅ ∅) ∧
      (∃ h : ZMod n, h ∉ P ∧
        ∃ T : ConditionFiber P Q ∅ ∅, T.val = fan P h) ∧
      ∀ H : Finset (ZMod n), H ⊆ E_K (P ∪ Q) →
        (H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)) →
        ∀ h ∈ H, ∃ T : ConditionFiber P Q H ∅, T.val = fan P h ∧
          ∃ e ∈ T.val, ∃ f ∈ T.val, e ≠ f ∧ IsDiagonal e ∧ IsDiagonal f ∧
            Cross e (ear h) ∧ Cross f (ear h) := by
  have hn6 : 6 ≤ n := by omega
  have hP : Independent P := independent_of_noncrossing hn6 P
    (fun i hi j hj hij => hcompat (mem_union_left Q hi) (mem_union_left Q hj) hij)
  have hbound : P.card + 2 * Q.card < n ∧ P.card + 4 < n := by
    rcases hcases with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> omega
  obtain ⟨r, hrP, hrm, hrp⟩ := choose_root P Q hbound.1
  obtain ⟨T, hT⟩ := conditioned_completion hn6 P Q ∅ r hP hrP
    (by simpa using hdisj) (by simpa using hrm) (by simpa using hrp)
  have hnon : Nonempty (ConditionFiber P Q ∅ ∅) := ⟨T⟩
  have hpos : 0 < Nat.card (ConditionFiber P Q ∅ ∅) := by
    letI := hnon
    have : Finite (ConditionFiber P Q ∅ ∅) := by
      unfold ConditionFiber
      infer_instance
    exact Nat.card_pos
  refine ⟨hnon, hpos, ⟨r, hrP, T, hT⟩, ?_⟩
  intro H hHE hH h hhH
  have hE := (mem_filter.mp (hHE hhH)).2
  have hhP : h ∉ P := fun hp => hE.1 (mem_union_left Q hp)
  have hdisjH : Disjoint P (Q ∪ H) := by
    apply disjoint_left.mpr
    intro i hi hqi
    rcases mem_union.mp hqi with hqi | hhi
    · exact disjoint_left.mp hdisj hi hqi
    · exact (mem_filter.mp (hHE hhi)).2.1 (mem_union_left Q hi)
  have hQneighbors := compatible_neighbors hn6 Q h
    (fun i hi => hE.2 i (mem_union_right P hi))
  have hHneighbors := compatible_neighbors hn6 H h (by
    intro i hi
    by_cases he : h = i
    · rw [← he]; exact not_cross_self _
    · exact hH hhH hi he)
  obtain ⟨U, hU⟩ := conditioned_completion hn6 P Q H h hP hhP hdisjH
    (by simpa only [mem_union, not_or] using ⟨hQneighbors.1, hHneighbors.1⟩)
    (by simpa only [mem_union, not_or] using ⟨hQneighbors.2, hHneighbors.2⟩)
  refine ⟨U, hU, ?_⟩
  rw [hU]
  exact fan_two_crossings hn6 P h hbound.2

end D5.S3.Geometry.Polygons.PolygonConditionedFan
