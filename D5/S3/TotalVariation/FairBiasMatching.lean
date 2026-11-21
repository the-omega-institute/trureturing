/- GID: D5/S3/TotalVariation/FairBiasMatching
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Acyclic matching on the nonempty signed fair-bias faces with explicit critical faces. -/
import D5.S3.TotalVariation.FairBiasRestriction

set_option linter.unusedSectionVars false

open D5.S3.TotalVariation.FairBiasRestriction
open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasShelling

namespace D5.S3.TotalVariation.FairBiasMatching

section

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

private def toggle {V : Type*} [DecidableEq V] (x : V) (S : Finset V) : Finset V :=
  if x ∈ S then S.erase x else insert x S

private theorem toggle_firstAt (c : L → A) {B S : Finset (L × Bool)} {x : L × Bool}
    (hB : B ∈ facets c) (hS : FirstAt c S B)
    (hx : x ∈ B) (hxR : x ∉ restrictionFace c B) :
    FirstAt c (toggle x S) B := by
  have hR := (firstAt_iff_restriction_subset c hB hS.1).mp hS
  unfold toggle
  split_ifs with hxS
  · apply (firstAt_iff_restriction_subset c hB ((Finset.erase_subset _ _).trans hS.1)).mpr
    intro y hy
    have hyx : y ≠ x := fun h => hxR (h ▸ hy)
    exact Finset.mem_erase.mpr ⟨hyx, hR hy⟩
  · apply (firstAt_iff_restriction_subset c hB (Finset.insert_subset_iff.mpr ⟨hx, hS.1⟩)).mpr
    exact hR.trans (Finset.subset_insert _ _)

private theorem firstAt_monotone (c : L → A) {B C S T : Finset (L × Bool)}
    (hC : C ∈ facets c) (hS : FirstAt c S B) (hT : FirstAt c T C) (hST : S ⊆ T) :
    ¬ lexBefore (L × Bool) C B :=
  fun hBefore => hS.2 C hC hBefore (hST.trans hT.1)

end

section

private theorem erased_pivot_of_cover {V : Type*} [DecidableEq V] {p q : Finset V} {x : V}
    (hpq : p ⊆ q) (hcard : q.card = p.card + 1) (hxq : x ∈ q) (hxp : x ∉ p) :
    q.erase x = p := by
  have hsub : p ⊆ q.erase x := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun h => hxp (h ▸ hz), hpq hz⟩
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  have herase := Finset.card_erase_add_one hxq
  omega

private theorem rank_decreases_inside_fiber {V : Type*} [DecidableEq V] (pivot : V) (margin : ℕ) (hmargin : 1 < margin)
    {p q : Finset V}
    (down : q ⊆ p ∧ p.card = q.card + 1 ∧ p.erase pivot ≠ q ∨
      q = insert pivot p ∧ pivot ∉ p) :
    q.card + (if pivot ∈ q then 0 else margin) <
    p.card + (if pivot ∈ p then 0 else margin) := by
  rcases down with ⟨hsub, hcard, hnm⟩ | ⟨rfl, hn⟩
  · have hm (h : pivot ∈ p) : pivot ∈ q := by
      by_contra hq
      exact hnm (erased_pivot_of_cover hsub hcard h hq)
    by_cases hp : pivot ∈ p
    · simp [hp, hm hp, hcard]
    · have hq : pivot ∉ q := fun h => hp (hsub h)
      simp only [ite_eq_right hp, ite_eq_right hq]
      omega
  · simp only [Finset.mem_insert_self, ite_true, ite_eq_right hn, Nat.add_zero,
      Finset.card_insert_of_notMem hn]
    omega

end

section

open Finset

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

/-- A signed face, with the empty face adjoined. -/
abbrev Face (c : L → A) := { S : Finset (L × Bool) // S ∈ augmentedFaces c }

private structure FirstFacetSelector (c : L → A) where
  facet : Face c → Finset (L × Bool)
  mem_facets (s : Face c) : facet s ∈ facets c
  firstAt (s : Face c) : FirstAt c s.val (facet s)

private structure IntervalPivots (c : L → A) where
  vertex : Finset (L × Bool) → Option (L × Bool)
  vertex_mem {B : Finset (L × Bool)} {x : L × Bool} :
    vertex B = some x → x ∈ B ∧ x ∉ restrictionFace c B
  vertex_none (B : Finset (L × Bool)) :
    vertex B = none ↔ B = restrictionFace c B

variable {c : L → A}

private theorem toggle_involutive {V : Type*} [DecidableEq V] (x : V) :
    Function.Involutive (toggle x) := by
  intro S
  by_cases hx : x ∈ S
  · simp [toggle, hx, Finset.insert_erase hx]
  · simp [toggle, hx]

/-- A matched face toggles its interval's pivot. A critical face is a fixed point. -/
private noncomputable def mate (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : Face c) : Face c :=
  match h : piv.vertex (sel.facet s) with
  | none => s
  | some x =>
      have hx := piv.vertex_mem h
      have hfirst := toggle_firstAt c (sel.mem_facets s) (sel.firstAt s)
        hx.1 hx.2
      ⟨toggle x s.val, augmented_of_subset_facet c (sel.mem_facets s) hfirst.1⟩

private theorem mate_first_facet (sel : FirstFacetSelector c) (piv : IntervalPivots c) (s : Face c) :
    sel.facet (mate sel piv s) = sel.facet s := by
  unfold mate
  split
  · rfl
  · rename_i x hx
    have hv := piv.vertex_mem hx
    exact first_unique c (sel.mem_facets _) (sel.mem_facets s) (sel.firstAt _)
      (toggle_firstAt c (sel.mem_facets s) (sel.firstAt s) hv.1 hv.2)

private theorem mate_val_of_some (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : Face c) {x : L × Bool} (h : piv.vertex (sel.facet s) = some x) :
    (mate sel piv s).val = toggle x s.val := by
  unfold mate
  split
  · rename_i hn
    rw [h] at hn
    cases hn
  · rename_i y hy
    have he : y = x := Option.some.inj (hy.symm.trans h)
    subst y
    rfl

private theorem mate_eq_of_none (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : Face c) (h : piv.vertex (sel.facet s) = none) : mate sel piv s = s := by
  unfold mate
  split
  · rfl
  · rename_i y hy
    rw [h] at hy
    cases hy

private theorem mate_involutive (sel : FirstFacetSelector c) (piv : IntervalPivots c) :
    Function.Involutive (mate sel piv) := by
  intro s
  cases h : piv.vertex (sel.facet s) with
  | none => simp only [mate_eq_of_none sel piv s h]
  | some x =>
      have hp : piv.vertex (sel.facet (mate sel piv s)) = some x := by
        rw [mate_first_facet, h]
      apply Subtype.ext
      rw [mate_val_of_some sel piv _ hp, mate_val_of_some sel piv _ h]
      exact toggle_involutive x s.val

/-- Incidence by exactly one additional vertex. -/
def Cover (s t : Face c) : Prop := s.val ⊆ t.val ∧ t.val.card = s.val.card + 1

private theorem mate_cover_or_fixed (sel : FirstFacetSelector c) (piv : IntervalPivots c) (s : Face c) :
    Cover s (mate sel piv s) ∨ Cover (mate sel piv s) s ∨ mate sel piv s = s := by
  cases h : piv.vertex (sel.facet s) with
  | none => exact Or.inr (Or.inr (mate_eq_of_none sel piv s h))
  | some x =>
      have hm := mate_val_of_some sel piv s h
      by_cases hx : x ∈ s.val
      · refine Or.inr (Or.inl ?_)
        unfold Cover
        rw [hm]
        simpa only [toggle, ite_eq_left hx] using
          And.intro (Finset.erase_subset x s.val) (Finset.card_erase_add_one hx).symm
      · refine Or.inl ?_
        unfold Cover
        rw [hm]
        simpa only [toggle, ite_eq_right hx] using
          And.intro (Finset.subset_insert x s.val) (Finset.card_insert_of_notMem hx)

private theorem mate_fixed_iff (sel : FirstFacetSelector c) (piv : IntervalPivots c) (s : Face c) :
    mate sel piv s = s ↔ s.val = sel.facet s ∧ restrictionFace c s.val = s.val := by
  have hR := (firstAt_iff_restriction_subset c (sel.mem_facets s) (sel.firstAt s).1).mp
    (sel.firstAt s)
  constructor
  · intro hm
    have hn : piv.vertex (sel.facet s) = none := by
      cases hv : piv.vertex (sel.facet s) with
      | none => rfl
      | some x =>
          have heq := mate_val_of_some sel piv s hv
          rw [hm] at heq
          by_cases hx : x ∈ s.val
          · simp only [toggle, ite_eq_left hx] at heq
            exact (Finset.notMem_erase x s.val (heq ▸ hx)).elim
          · simp only [toggle, ite_eq_right hx] at heq
            exact (hx (heq.symm ▸ Finset.mem_insert_self x s.val)).elim
    have hfull := (piv.vertex_none _).mp hn
    have he : s.val = sel.facet s :=
      Finset.Subset.antisymm (sel.firstAt s).1 (hfull.symm ▸ hR)
    exact ⟨he, by rw [he]; exact hfull.symm⟩
  · rintro ⟨he, hfull⟩
    apply mate_eq_of_none
    exact (piv.vertex_none _).mpr (by rw [← he, hfull])

/-- Orient matched cover edges up and the remaining covers down. -/
private def Step (sel : FirstFacetSelector c) (piv : IntervalPivots c) (s t : Face c) : Prop :=
  (Cover t s ∧ mate sel piv s ≠ t) ∨ (Cover s t ∧ mate sel piv s = t)

private noncomputable def facetIndex (c : L → A) (B : Finset (L × Bool)) : ℕ := by
  classical
  exact ((facets c).filter fun C => lexBefore (L × Bool) C B).card

private theorem facetIndex_lt {B C : Finset (L × Bool)}
    (hB : B ∈ facets c) (hBC : lexBefore (L × Bool) B C) :
    facetIndex c B < facetIndex c C := by
  classical
  unfold facetIndex
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSf, hSB⟩
    exact Finset.mem_filter.mpr ⟨hSf, lt_trans hBC hSB⟩
  · intro he
    have hm : B ∈ (facets c).filter (fun F => lexBefore (L × Bool) F C) :=
      Finset.mem_filter.mpr ⟨hB, hBC⟩
    rw [← he] at hm
    exact lt_irrefl _ (Finset.mem_filter.mp hm).2

private noncomputable def localRank (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : Face c) : ℕ :=
  s.val.card + match piv.vertex (sel.facet s) with
  | none => 0
  | some x => if x ∈ s.val then 0 else 2

private noncomputable def rank (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : Face c) : ℕ :=
  facetIndex c (sel.facet s) * (Fintype.card (L × Bool) + 3) + localRank sel piv s

private theorem localRank_bound (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : Face c) : localRank sel piv s < Fintype.card (L × Bool) + 3 := by
  have hc := Finset.card_le_univ s.val
  unfold localRank
  split
  · omega
  · split <;> omega

private theorem localRank_decreases (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    {s t : Face c} (h : Step sel piv s t) (he : sel.facet t = sel.facet s) :
    localRank sel piv t < localRank sel piv s := by
  unfold localRank
  rw [he]
  cases hx : piv.vertex (sel.facet s) with
  | none =>
      simp only [Nat.add_zero]
      rcases h with ⟨hc, _⟩ | ⟨hc, hm⟩
      · have := hc.2
        omega
      · rw [mate_eq_of_none sel piv s hx] at hm
        subst t
        have := hc.2
        omega
  | some x =>
      apply rank_decreases_inside_fiber x 2 (by decide)
      have hm := mate_val_of_some sel piv s hx
      rcases h with ⟨hc, hne⟩ | ⟨hc, heq⟩
      · refine Or.inl ⟨hc.1, hc.2, ?_⟩
        intro herase
        by_cases hs : x ∈ s.val
        · apply hne
          apply Subtype.ext
          simpa only [hm, toggle, ite_eq_left hs] using herase
        · have hh : s.val.erase x = s.val := Finset.erase_eq_of_notMem hs
          rw [hh] at herase
          have hcard := hc.2
          rw [herase] at hcard
          omega
      · apply Or.inr
        have hval : t.val = toggle x s.val := by rw [← heq, hm]
        have hn : x ∉ s.val := by
          intro hs
          have hnot : x ∉ t.val := by
            rw [hval, toggle, ite_eq_left hs]
            exact Finset.notMem_erase _ _
          exact hnot (hc.1 hs)
        exact ⟨by simpa only [toggle, ite_eq_right hn] using hval, hn⟩

private theorem rank_decreases (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    {s t : Face c} (h : Step sel piv s t) : rank sel piv t < rank sel piv s := by
  have hn : ¬ lexBefore (L × Bool) (sel.facet s) (sel.facet t) := by
    rcases h with ⟨hc, _⟩ | ⟨_, hm⟩
    · exact firstAt_monotone c (sel.mem_facets s) (sel.firstAt t)
        (sel.firstAt s) hc.1
    · rw [← hm, mate_first_facet]
      exact lt_irrefl _
  by_cases he : sel.facet t = sel.facet s
  · have hd := localRank_decreases sel piv h he
    unfold rank
    rw [he]
    exact Nat.add_lt_add_left hd _
  · have hlt : lexBefore (L × Bool) (sel.facet t) (sel.facet s) := by
      rcases lt_trichotomy (toColex (α := Finset (L × Bool)ᵒᵈ) (sel.facet s))
          (toColex (α := Finset (L × Bool)ᵒᵈ) (sel.facet t)) with hlt | heq | hgt
      · exact hlt
      · exact (he (toColex.injective heq.symm)).elim
      · exact (hn hgt).elim
    have hi := facetIndex_lt (sel.mem_facets t) hlt
    have hb := localRank_bound sel piv t
    unfold rank
    calc
      _ < facetIndex c (sel.facet t) * (Fintype.card (L × Bool) + 3) +
          (Fintype.card (L × Bool) + 3) := Nat.add_lt_add_left hb _
      _ = (facetIndex c (sel.facet t) + 1) * (Fintype.card (L × Bool) + 3) := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ facetIndex c (sel.facet s) * (Fintype.card (L × Bool) + 3) :=
        Nat.mul_le_mul_right _ hi
      _ ≤ _ := Nat.le_add_right _ _

end

section

open Finset

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)] {c : L → A}

private noncomputable def emptyFace (c : L → A) : Face c :=
  ⟨∅, by classical exact Finset.mem_insert_self _ _⟩

private theorem restriction_subset (B : Finset (L × Bool)) :
    restrictionFace c B ⊆ B := by
  classical
  exact Finset.filter_subset _ _

private theorem first_restriction_empty (sel : FirstFacetSelector c) :
    restrictionFace c (sel.facet (emptyFace c)) = ∅ :=
  Finset.Subset.antisymm
    ((firstAt_iff_restriction_subset c (sel.mem_facets _) (sel.firstAt _).1).mp (sel.firstAt _))
    (Finset.empty_subset _)

/-- Use the prescribed vertex on the first interval, and the least available pivot elsewhere. -/
private noncomputable def chosenPivots (sel : FirstFacetSelector c) (x : L × Bool)
    (hx : x ∈ sel.facet (emptyFace c)) : IntervalPivots c := by
  classical
  have hx' : x ∈ sel.facet (emptyFace c) \ restrictionFace c (sel.facet (emptyFace c)) := by
    rw [first_restriction_empty sel, Finset.sdiff_empty]
    exact hx
  refine ⟨fun B => if B = sel.facet (emptyFace c) then some x
    else if h : (B \ restrictionFace c B).Nonempty
      then some ((B \ restrictionFace c B).min' h) else none, ?_, ?_⟩
  · intro B y
    by_cases hb : B = sel.facet (emptyFace c)
    · subst B
      rw [ite_eq_left (show sel.facet (emptyFace c) = sel.facet (emptyFace c) from rfl)]
      intro he
      exact Option.some.inj he ▸ Finset.mem_sdiff.mp hx'
    · simp only [ite_eq_right hb]
      split
      · rename_i h
        intro he
        exact Option.some.inj he ▸ Finset.mem_sdiff.mp (Finset.min'_mem _ h)
      · intro he
        cases he
  · intro B
    by_cases hb : B = sel.facet (emptyFace c)
    · subst B
      have hne : sel.facet (emptyFace c) ≠ restrictionFace c (sel.facet (emptyFace c)) :=
        fun he => (Finset.mem_sdiff.mp hx').2 (he ▸ hx)
      simp [hne]
    · simp only [ite_eq_right hb]
      split
      · rename_i h
        have hne : B ≠ restrictionFace c B := by
          intro he
          apply (Finset.sdiff_nonempty.mp h)
          rw [← he]
        simp [hne]
      · rename_i h
        have hs : B ⊆ restrictionFace c B :=
          Classical.not_not.mp (fun h' => h (Finset.sdiff_nonempty.mpr h'))
        exact iff_of_true rfl (Finset.Subset.antisymm hs (restriction_subset B))

private theorem mate_empty_val (sel : FirstFacetSelector c) (x : L × Bool)
    (hx : x ∈ sel.facet (emptyFace c)) :
    (mate sel (chosenPivots sel x hx) (emptyFace c)).val = {x} := by
  have hp : (chosenPivots sel x hx).vertex (sel.facet (emptyFace c)) = some x := by
    simp [chosenPivots]
  rw [mate_val_of_some sel _ _ hp]
  change toggle x ∅ = {x}
  simp [toggle]

/-- The nonempty faces of the signed fair-bias complex. -/
abbrev NonemptyFace (c : L → A) := {s : Face c // s.val.Nonempty}

/-- Restrict the matching by leaving the former mate of the empty face unmatched. -/
private noncomputable def nonemptyMate (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : NonemptyFace c) : NonemptyFace c := by
  classical
  exact if h : (mate sel piv s.val).val.Nonempty then ⟨mate sel piv s.val, h⟩ else s

private theorem nonemptyMate_involutive (sel : FirstFacetSelector c) (piv : IntervalPivots c) :
    Function.Involutive (nonemptyMate sel piv) := by
  intro s
  by_cases h : (mate sel piv s.val).val.Nonempty
  · have hm : nonemptyMate sel piv s = ⟨mate sel piv s.val, h⟩ := by
      simp only [nonemptyMate, dite_eq_left h]
    rw [hm]
    simp only [nonemptyMate, mate_involutive sel piv s.val, dite_eq_left s.property]
  · have hm : nonemptyMate sel piv s = s := by simp only [nonemptyMate, dite_eq_right h]
    simp only [hm]

private theorem nonemptyMate_cover_or_fixed (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : NonemptyFace c) :
    Cover s.val (nonemptyMate sel piv s).val ∨ Cover (nonemptyMate sel piv s).val s.val ∨
      nonemptyMate sel piv s = s := by
  by_cases h : (mate sel piv s.val).val.Nonempty
  · simp only [nonemptyMate, dite_eq_left h]
    rcases mate_cover_or_fixed sel piv s.val with hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Subtype.ext hc))
  · exact Or.inr (Or.inr (by simp only [nonemptyMate, dite_eq_right h]))

private def NonemptyStep (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s t : NonemptyFace c) : Prop :=
  (Cover t.val s.val ∧ nonemptyMate sel piv s ≠ t) ∨
    (Cover s.val t.val ∧ nonemptyMate sel piv s = t)

private theorem nonemptyMate_eq_iff_of_ne (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    {s t : NonemptyFace c} (hne : s ≠ t) :
    nonemptyMate sel piv s = t ↔ mate sel piv s.val = t.val := by
  by_cases h : (mate sel piv s.val).val.Nonempty
  · simp only [nonemptyMate, dite_eq_left h, Subtype.ext_iff]
  · rw [nonemptyMate, dite_eq_right h]
    exact iff_of_false hne (fun he => h (he.symm ▸ t.property))

private theorem nonemptyStep_iff (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    {s t : NonemptyFace c} : NonemptyStep sel piv s t ↔ Step sel piv s.val t.val := by
  have ne_of_cover {a b : NonemptyFace c} (h : Cover a.val b.val) : a ≠ b := by
    rintro rfl
    have := h.2
    omega
  unfold NonemptyStep Step
  exact or_congr (and_congr_right fun hc =>
    not_congr (nonemptyMate_eq_iff_of_ne sel piv (ne_of_cover hc).symm))
    (and_congr_right fun hc => nonemptyMate_eq_iff_of_ne sel piv (ne_of_cover hc))

private theorem nonemptyStep_acyclic (sel : FirstFacetSelector c) (piv : IntervalPivots c)
    (s : NonemptyFace c) : ¬ Relation.TransGen (NonemptyStep sel piv) s s := by
  have descent {a b : NonemptyFace c} (h : Relation.TransGen (NonemptyStep sel piv) a b) :
      rank sel piv b.val < rank sel piv a.val := by
    induction h with
    | single h => exact rank_decreases sel piv ((nonemptyStep_iff sel piv).mp h)
    | tail _ h ih => exact lt_trans (rank_decreases sel piv ((nonemptyStep_iff sel piv).mp h)) ih
  exact fun h => Nat.lt_irrefl _ (descent h)

private theorem nonemptyMate_fixed_iff (sel : FirstFacetSelector c) (x : L × Bool)
    (hx : x ∈ sel.facet (emptyFace c)) (s : NonemptyFace c) :
    nonemptyMate sel (chosenPivots sel x hx) s = s ↔
      s.val.val = {x} ∨ (s.val.val ∈ facets c ∧ restrictionFace c s.val.val = s.val.val) := by
  let piv := chosenPivots sel x hx
  change nonemptyMate sel piv s = s ↔ _
  have hempty : (mate sel piv s.val).val = ∅ ↔ s.val.val = {x} := by
    have he := mate_empty_val sel x hx
    constructor
    · intro h
      have h' : mate sel piv s.val = emptyFace c := Subtype.ext h
      have hh : s.val = mate sel piv (emptyFace c) :=
        (mate_involutive sel piv s.val).symm.trans (congrArg (mate sel piv) h')
      exact (congrArg Subtype.val hh).trans he
    · intro h
      have h' : s.val = mate sel piv (emptyFace c) := Subtype.ext (h.trans he.symm)
      rw [h', mate_involutive sel piv (emptyFace c)]
      rfl
  have hfixed : mate sel piv s.val = s.val ↔
      s.val.val ∈ facets c ∧ restrictionFace c s.val.val = s.val.val := by
    rw [mate_fixed_iff]
    constructor
    · rintro ⟨h, hfull⟩
      exact ⟨h.symm ▸ sel.mem_facets s.val, hfull⟩
    · rintro ⟨hf, hfull⟩
      have hfirst := (firstAt_iff_restriction_subset c hf (Finset.Subset.refl _)).mpr
        (restriction_subset s.val.val)
      exact ⟨first_unique c hf (sel.mem_facets s.val) hfirst (sel.firstAt s.val), hfull⟩
  by_cases hn : (mate sel piv s.val).val.Nonempty
  · have hne : s.val.val ≠ {x} := fun h => hn.ne_empty (hempty.mpr h)
    simpa only [nonemptyMate, dite_eq_left hn, Subtype.ext_iff, hne, false_or] using hfixed
  · have he := hempty.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
    simp [nonemptyMate, hn, he]

end

section

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

private noncomputable def selectFirst (c : L → A) (h : (facets c).Nonempty) : FirstFacetSelector c where
  facet s := (exists_first_facet c h s.property).choose
  mem_facets s := (exists_first_facet c h s.property).choose_spec.1
  firstAt s := (exists_first_facet c h s.property).choose_spec.2

/-- The nonempty signed faces admit an acyclic cover matching with exactly the specified fixed faces. -/
theorem actualMatching (c : L → A) (h : (facets c).Nonempty) :
    ∃ (B : Finset (L × Bool)) (x : L × Bool) (mate : NonemptyFace c → NonemptyFace c),
      B ∈ facets c ∧ FirstAt c ∅ B ∧ x ∈ B ∧
      Function.Involutive mate ∧
      (∀ s, Cover s.val (mate s).val ∨ Cover (mate s).val s.val ∨ mate s = s) ∧
      (∀ s, mate s = s ↔ s.val.val = {x} ∨
        (s.val.val ∈ facets c ∧ restrictionFace c s.val.val = s.val.val)) ∧
      (∀ s, ¬ Relation.TransGen
        (fun p q => Cover q.val p.val ∧ mate p ≠ q ∨
          Cover p.val q.val ∧ mate p = q) s s) := by
  let sel := selectFirst c h
  obtain ⟨x, hx⟩ := (mem_facets.mp (sel.mem_facets (emptyFace c))).1.1
  let piv := chosenPivots sel x hx
  refine ⟨sel.facet (emptyFace c), x, nonemptyMate sel piv,
    sel.mem_facets (emptyFace c), sel.firstAt (emptyFace c), hx,
    nonemptyMate_involutive sel piv,
    nonemptyMate_cover_or_fixed sel piv, nonemptyMate_fixed_iff sel x hx, ?_⟩
  intro s
  exact nonemptyStep_acyclic sel piv s

end

end D5.S3.TotalVariation.FairBiasMatching
