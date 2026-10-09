/- GID: D5/S0/Computability/Coding/RetainedDepthExactImage
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/RetainedDepthExactImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local complete-bundle cuts characterize the exact image of depth-budget codes. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Mathlib.Order.Partition.Finpartition

open scoped BigOperators

namespace D5.S0.Computability.Coding.RetainedDepthExactImage

open PrefixFreeCode DepthBudgetIidGreedyOptimality

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A retained sequence starts at zero, increases strictly, and is unbounded. -/
def Retained (s : ℕ → ℕ) : Prop :=
  s 0 = 0 ∧ StrictMono s ∧ ∀ n, ∃ j, n ≤ s j

/-- The first retained depth not less than a requested depth. -/
noncomputable def firstDepth (s : ℕ → ℕ) (h : Retained s) (n : ℕ) : ℕ :=
  s (Nat.find (h.2.2 n))

/-- The full descendant expansion, including every suffix at the first retained depth. -/
def expansion (s : ℕ → ℕ) (h : Retained s) (F : Set (List A)) : Set (List A) :=
  {g | ∃ w ∈ F, w <+: g ∧ g.length = firstDepth s h w.length}

/-- Segment j is the half-open interval (s j, s (j+1)]. -/
def Band (s : ℕ → ℕ) (j : ℕ) (w : List A) : Prop :=
  s j < w.length ∧ w.length ≤ s (j + 1)

/-- Every descendant at the specified depth belongs to the target code. -/
def Bundle (G : Set (List A)) (r : ℕ) (w : List A) : Prop :=
  ∀ g, g.length = r → w <+: g → g ∈ G

/-- Available ancestors have the entire descendant bundle inside the target level. -/
noncomputable def available (s : ℕ → ℕ) (G : Set (List A)) (j : ℕ) :
    Finset (List A) := by
  classical
  exact ((Finset.range (s (j + 1) + 1)).biUnion (words (α := A))).filter
    (fun w => Band s j w ∧ Bundle G (s (j + 1)) w)

/-- The two finite systems of leaf-cover and depth-budget equations. -/
noncomputable def Equations (s : ℕ → ℕ) (G : Set (List A)) (b : ℕ → ℕ)
    (j : ℕ) (x : List A → Bool) : Prop := by
  classical
  exact (∀ g ∈ G, g.length = s (j + 1) →
    ∑ w ∈ (available s G j).filter (fun w => w <+: g),
      (if x w then 1 else 0 : ℕ) = 1) ∧
    (∀ n, s j < n → n ≤ s (j + 1) →
      ∑ w ∈ (available s G j).filter (fun w => w.length = n),
        (if x w then 1 else 0 : ℕ) ≤ b n)

private theorem mem_words (w : List A) (n : ℕ) : w ∈ words n ↔ w.length = n := by
  classical
  simp only [words, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

private theorem mem_level (F : Set (List A)) (n : ℕ) (w : List A) :
    w ∈ level F n ↔ w.length = n ∧ w ∈ F := by
  classical
  simp [level, mem_words]

private theorem mem_available (s : ℕ → ℕ) (G : Set (List A)) (j : ℕ) (w : List A) :
    w ∈ available s G j ↔ Band s j w ∧ Bundle G (s (j + 1)) w := by
  classical
  simp only [available.eq_1, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, mem_words]
  exact ⟨fun h => h.2, fun h => ⟨⟨w.length, by have := h.1.2; omega, rfl⟩, h⟩⟩

omit [Fintype A] [DecidableEq A] in
private theorem band_unique (s : ℕ → ℕ) (hs : StrictMono s) (w : List A)
    {j k : ℕ} (hj : Band s j w) (hk : Band s k w) : j = k := by
  unfold Band at hj hk
  rcases lt_trichotomy j k with hjk | he | hkj
  · have hle : s (j + 1) ≤ s k := hs.monotone (by omega)
    obtain ⟨_, _⟩ := hj
    obtain ⟨_, _⟩ := hk
    omega
  · exact he
  · have hle : s (k + 1) ≤ s j := hs.monotone (by omega)
    obtain ⟨_, _⟩ := hj
    obtain ⟨_, _⟩ := hk
    omega

private theorem positive_has_band (s : ℕ → ℕ) (h : Retained s) (n : ℕ)
    (hn : 0 < n) : ∃ j, s j < n ∧ n ≤ s (j + 1) := by
  obtain ⟨j, hj, hjnext⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun k => n ≤ s k) (by rw [h.1]; omega) (h.2.2 n)
  exact ⟨j, Nat.lt_of_not_ge hj, hjnext⟩

private theorem firstDepth_eq (s : ℕ → ℕ) (h : Retained s) {j n : ℕ}
    (hl : s j < n) (hr : n ≤ s (j + 1)) : firstDepth s h n = s (j + 1) := by
  classical
  unfold firstDepth
  congr 1
  apply (Nat.find_eq_iff (h.2.2 n)).mpr
  refine ⟨hr, ?_⟩
  intro k hk hn
  have := h.2.1.monotone (show k ≤ j by omega)
  omega

/-- A finite segment cut has complete bundles, unique leaf coverage, and the original budgets. -/
private def Cut (s : ℕ → ℕ) (G : Set (List A)) (b : ℕ → ℕ) (j : ℕ)
    (C : Finset (List A)) : Prop :=
  (∀ w ∈ C, Band s j w ∧ Bundle G (s (j + 1)) w) ∧
  (∀ g ∈ G, g.length = s (j + 1) → ∃! w, w ∈ C ∧ w <+: g) ∧
  (∀ n, s j < n → n ≤ s (j + 1) → (level (C : Set (List A)) n).card ≤ b n)

omit [Fintype A] [DecidableEq A] in
private theorem cross_no_prefix (s : ℕ → ℕ) (hs : StrictMono s)
    (G : Set (List A)) (hG : IsPrefixFree G) (a : A) {j k : ℕ} (hjk : j < k)
    {w v : List A} (hw : Band s j w) (hv : Band s k v)
    (bw : Bundle G (s (j + 1)) w) (bv : Bundle G (s (k + 1)) v) : ¬ w <+: v := by
  unfold Band at hw hv
  intro hwv
  let t := v.take (s (j + 1))
  let g := v ++ List.replicate (s (k + 1) - v.length) a
  have hrv : s (j + 1) < v.length :=
    lt_of_le_of_lt (hs.monotone (Nat.succ_le_of_lt hjk)) hv.1
  have htlen : t.length = s (j + 1) := by simp [t, List.length_take, hrv.le]
  have hglen : g.length = s (k + 1) := by simp [g]; omega
  have hwt : w <+: t := List.prefix_of_prefix_length_le hwv
    (List.take_prefix _ _) (by rw [htlen]; exact hw.2)
  have htG := bw t htlen hwt
  have hgG := bv g hglen (List.prefix_append _ _)
  have htg : t <+: g := (List.take_prefix _ _).trans (List.prefix_append _ _)
  have he : s (j + 1) = s (k + 1) := by
    simpa only [htlen, hglen] using congrArg List.length (hG htG hgG htg)
  have hrr : s (j + 1) < s (k + 1) := hs (by omega)
  omega

local notation "glue" C => (⋃ j, (C j : Set (List A)))

private theorem cut_cover (s : ℕ → ℕ) (G : Set (List A)) (b : ℕ → ℕ) (j : ℕ)
    (C : Finset (List A)) (hC : Cut s G b j C) (a : A)
    {g : List A} (hg : g ∈ G) (hglen : g.length = s (j + 1)) :
    ∃ w ∈ C, w <+: g := by
  classical
  let desc (w : List A) := (words (α := A) (s (j + 1))).filter (fun v => w <+: v)
  let parts := C.image desc
  have md (w v : List A) : v ∈ desc w ↔ v.length = s (j + 1) ∧ w <+: v := by
    simp [desc, mem_words]
  have sub : ∀ p ∈ parts, p ⊆ level G (s (j + 1)) := by
    rintro p hp v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hlen, hpref⟩ := (md w v).mp hv
    exact (mem_level _ _ _).mpr ⟨hlen, (hC.1 w hw).2 v hlen hpref⟩
  have unique : ∀ v ∈ level G (s (j + 1)), ∃! p, p ∈ parts ∧ v ∈ p := by
    intro v hv
    obtain ⟨hlen, hvG⟩ := (mem_level _ _ _).mp hv
    obtain ⟨w, hw, hu⟩ := hC.2.1 v hvG hlen
    refine ⟨desc w, ⟨Finset.mem_image.mpr ⟨w, hw.1, rfl⟩,
      (md w v).mpr ⟨hlen, hw.2⟩⟩, ?_⟩
    rintro p ⟨hp, hvp⟩
    obtain ⟨u, huc, rfl⟩ := Finset.mem_image.mp hp
    exact congrArg desc (hu u ⟨huc, ((md u v).mp hvp).2⟩)
  have nonempty : ∅ ∉ parts := by
    intro hp
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hp
    let v := w ++ List.replicate (s (j + 1) - w.length) a
    have hvlen : v.length = s (j + 1) := by
      simp only [v, List.length_append, List.length_replicate]
      exact Nat.add_sub_of_le (hC.1 w hw).1.2
    have hv : v ∈ desc w := (md w v).mpr ⟨hvlen, List.prefix_append _ _⟩
    rw [he] at hv
    exact Finset.notMem_empty _ hv
  let P : Finpartition (level G (s (j + 1))) :=
    Finpartition.ofExistsUnique parts sub unique nonempty
  have hgm : g ∈ P.parts.biUnion id := by
    rw [P.biUnion_parts]
    exact (mem_level _ _ _).mpr ⟨hglen, hg⟩
  change g ∈ parts.biUnion id at hgm
  obtain ⟨p, hp, hgp⟩ := Finset.mem_biUnion.mp hgm
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨w, hw, ((md w g).mp hgp).2⟩

private theorem glue_prefix_free (s : ℕ → ℕ) (hs : StrictMono s)
    (G : Set (List A)) (hG : IsPrefixFree G) (a : A) (b : ℕ → ℕ)
    (C : ℕ → Finset (List A)) (hC : ∀ j, Cut s G b j (C j)) :
    IsPrefixFree (glue C) := by
  simp only [IsPrefixFree, Set.mem_iUnion, Finset.mem_coe]
  rintro w ⟨j, hw⟩ v ⟨k, hv⟩ hwv
  obtain ⟨wb, bw⟩ := (hC j).1 w hw
  obtain ⟨vb, bv⟩ := (hC k).1 v hv
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · exact False.elim (cross_no_prefix s hs G hG a hjk wb vb bw bv hwv)
  · let g := v ++ List.replicate (s (j + 1) - v.length) a
    have hglen : g.length = s (j + 1) := by
      simp only [g, List.length_append, List.length_replicate]
      exact Nat.add_sub_of_le vb.2
    have hvg : v <+: g := List.prefix_append _ _
    exact ExistsUnique.unique ((hC j).2.1 g (bv g hglen hvg) hglen)
      ⟨hw, hwv.trans hvg⟩ ⟨hv, hvg⟩
  · have hle : s (k + 1) ≤ s j := hs.monotone (by omega)
    have hlen := hwv.length_le
    have := wb.1
    have := vb.2
    omega

private theorem glue_level_eq (s : ℕ → ℕ) (hs : StrictMono s)
    (G : Set (List A)) (b : ℕ → ℕ) (C : ℕ → Finset (List A))
    (hC : ∀ j, Cut s G b j (C j)) {n j : ℕ} (hl : s j < n) (hr : n ≤ s (j + 1)) :
    level (glue C) n = level (C j : Set (List A)) n := by
  classical
  ext w
  simp only [mem_level, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro ⟨hlen, k, hw⟩
    have hj : Band s j w := ⟨by omega, by omega⟩
    have he := band_unique s hs w hj ((hC k).1 w hw).1
    subst k
    exact ⟨hlen, hw⟩
  · rintro ⟨hlen, hw⟩
    exact ⟨hlen, j, hw⟩

private theorem glue_correct (s : ℕ → ℕ) (h : Retained s)
    (G : Set (List A)) (hG : IsPrefixFree G)
    (hlevels : ∀ g ∈ G, ∃ j, g.length = s (j + 1)) (a : A) (b : ℕ → ℕ)
    (C : ℕ → Finset (List A)) (hC : ∀ j, Cut s G b j (C j)) :
    Legal b (glue C) ∧ expansion s h (glue C) = G := by
  have hroot : [] ∉ glue C := by
    simp only [Set.mem_iUnion, Finset.mem_coe]
    rintro ⟨j, hw⟩
    have := ((hC j).1 [] hw).1.1
    simp at this
  refine ⟨⟨glue_prefix_free s h.2.1 G hG a b C hC, hroot, ?_⟩, ?_⟩
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : level (glue C) 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        obtain ⟨hlen, hm⟩ := (mem_level _ _ _).mp hw
        exact hroot ((List.length_eq_zero_iff.mp hlen) ▸ hm)
      simp [hz]
    · obtain ⟨j, hl, hr⟩ := positive_has_band s h n hn
      rw [glue_level_eq s h.2.1 G b C hC hl hr]
      exact (hC j).2.2 n hl hr
  · ext g
    constructor
    · rintro ⟨w, hwF, hp, hglen⟩
      obtain ⟨j, hw⟩ := Set.mem_iUnion.mp hwF
      obtain ⟨wb, bw⟩ := (hC j).1 w hw
      exact bw g (hglen.trans (firstDepth_eq s h wb.1 wb.2)) hp
    · intro hg
      obtain ⟨j, hglen⟩ := hlevels g hg
      obtain ⟨w, hw, hp⟩ := cut_cover s G b j (C j) (hC j) a hg hglen
      have wb := ((hC j).1 w hw).1
      exact ⟨w, Set.mem_iUnion.mpr ⟨j, hw⟩, hp,
        hglen.trans (firstDepth_eq s h wb.1 wb.2).symm⟩

private theorem forward_cut (s : ℕ → ℕ) (h : Retained s)
    (G F : Set (List A)) (b : ℕ → ℕ) (hF : Legal b F)
    (he : expansion s h F = G) (j : ℕ) : ∃ C, Cut s G b j C := by
  classical
  let C := (available s G j).filter (fun w => w ∈ F)
  have mc (w : List A) : w ∈ C ↔ w ∈ F ∧ Band s j w := by
    constructor
    · intro hw
      obtain ⟨ha, hf⟩ := Finset.mem_filter.mp hw
      exact ⟨hf, ((mem_available _ _ _ _).mp ha).1⟩
    · rintro ⟨hf, wb⟩
      refine Finset.mem_filter.mpr ⟨(mem_available _ _ _ _).mpr ⟨wb, ?_⟩, hf⟩
      intro g hg hp
      rw [← he]
      exact ⟨w, hf, hp, hg.trans (firstDepth_eq s h wb.1 wb.2).symm⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro w hw
    exact (mem_available _ _ _ _).mp (Finset.mem_filter.mp hw).1
  · intro g hg hglen
    obtain ⟨w, hf, hp, hlen⟩ := he.symm ▸ hg
    have hn : 0 < w.length := by
      by_contra hh
      have hz : w.length = 0 := by omega
      exact hF.2.1 ((List.length_eq_zero_iff.mp hz) ▸ hf)
    obtain ⟨k, hl, hr⟩ := positive_has_band s h w.length hn
    have hk : k = j := by
      have hsEq : s (k + 1) = s (j + 1) :=
        (firstDepth_eq s h hl hr).symm.trans (hlen.symm.trans hglen)
      have := h.2.1.injective hsEq
      omega
    subst k
    refine ⟨w, ⟨(mc w).mpr ⟨hf, hl, hr⟩, hp⟩, ?_⟩
    rintro v ⟨hv, hvp⟩
    have hvF := ((mc v).mp hv).1
    rcases List.prefix_or_prefix_of_prefix hp hvp with hwv | hvw
    · exact (hF.1 hf hvF hwv).symm
    · exact hF.1 hvF hf hvw
  · intro n _ _
    apply (Finset.card_le_card ?_).trans (hF.2.2 n)
    intro w hw
    obtain ⟨hlen, hm⟩ := (mem_level _ _ _).mp hw
    exact (mem_level _ _ _).mpr ⟨hlen, ((mc w).mp hm).1⟩

private theorem level_card (C : Finset (List A)) (n : ℕ) :
    (level (C : Set (List A)) n).card = (C.filter (fun w => w.length = n)).card := by
  classical
  congr 1
  ext w
  simp only [mem_level, Finset.mem_filter, Finset.mem_coe]
  exact and_comm

private theorem cut_iff_equations (s : ℕ → ℕ) (G : Set (List A))
    (b : ℕ → ℕ) (j : ℕ) : (∃ C, Cut s G b j C) ↔ ∃ x, Equations s G b j x := by
  classical
  let chosen (x : List A → Bool) := (available s G j).filter (fun w => x w = true)
  have hc (x : List A → Bool) (g : List A) :
      ∑ w ∈ (available s G j).filter (fun w => w <+: g), (if x w then 1 else 0 : ℕ) =
      ((chosen x).filter (fun w => w <+: g)).card := by
    simp only [Finset.sum_boole, Nat.cast_id, chosen, Finset.filter_filter]
    congr 1
    ext w
    simp [and_comm]
  have hn (x : List A → Bool) (n : ℕ) :
      ∑ w ∈ (available s G j).filter (fun w => w.length = n), (if x w then 1 else 0 : ℕ) =
      (level (chosen x : Set (List A)) n).card := by
    rw [level_card]
    simp only [Finset.sum_boole, Nat.cast_id, chosen, Finset.filter_filter]
    congr 1
    ext w
    simp [and_comm]
  constructor
  · rintro ⟨C, hC⟩
    let x : List A → Bool := fun w => decide (w ∈ C)
    have heq : chosen x = C := by
      ext w
      simp only [chosen, Finset.mem_filter, x, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨(mem_available _ _ _ _).mpr (hC.1 w h), h⟩⟩
    refine ⟨x, ?_, ?_⟩
    · intro g hg hglen
      rw [hc, heq, Finset.card_eq_one_iff_existsUnique]
      simpa only [Finset.mem_filter] using hC.2.1 g hg hglen
    · intro n hl hr
      rw [hn, heq]
      exact hC.2.2 n hl hr
  · rintro ⟨x, hx⟩
    refine ⟨chosen x, ?_, ?_, ?_⟩
    · intro w hw
      exact (mem_available _ _ _ _).mp (Finset.mem_filter.mp hw).1
    · intro g hg hglen
      have hh := hx.1 g hg hglen
      change _ = 1 at hh
      rw [hc, Finset.card_eq_one_iff_existsUnique] at hh
      simpa only [Finset.mem_filter] using hh
    · intro n hl hr
      have hh := hx.2 n hl hr
      change _ ≤ b n at hh
      rwa [hn] at hh

/-- A single rootless budget-legal code has the specified retained-depth image exactly when
every segment admits the two finite 0-1 systems. -/
theorem result (hA : 2 ≤ Fintype.card A) (s : ℕ → ℕ) (h : Retained s)
    (b : ℕ → ℕ) (G : Set (List A)) (hG : IsPrefixFree G)
    (hlevels : ∀ g ∈ G, ∃ j, g.length = s (j + 1)) :
    (∃ F, Legal b F ∧ expansion s h F = G) ↔
      ∀ j, ∃ x : List A → Bool, Equations s G b j x := by
  classical
  constructor
  · rintro ⟨F, hf, he⟩ j
    exact (cut_iff_equations s G b j).mp (forward_cut s h G F b hf he j)
  · intro hx
    have hc : ∀ j, ∃ C, Cut s G b j C :=
      fun j => (cut_iff_equations s G b j).mpr (hx j)
    choose C hC using hc
    have hpos : 0 < Fintype.card A := by omega
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨glue C, glue_correct s h G hG hlevels a b C hC⟩

end D5.S0.Computability.Coding.RetainedDepthExactImage
