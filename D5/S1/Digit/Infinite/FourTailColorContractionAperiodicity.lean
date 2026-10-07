/- GID: D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/FourTailColorContractionAperiodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four actual tail colors prohibit nontrivial cycles under an inward outer branch. -/

import D5.S1.Digit.Infinite.FixedTailClosedBudget
import D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction
import D5.S1.Digit.Infinite.OddColorThreeSource
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.FourTailColorContractionAperiodicity

open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction
  (labelIndex label_index_injective)
open D5.S1.Digit.Infinite.OddColorThreeSource (golden_relations)
open Function

local notation "I" => stateInterval true
local notation "X" => stateInterval false
local notation "embed" => (Fin.castLE (by decide : 4 ≤ 5) : Fin 4 → Fin 5)

/-- Exact decoding of all legal closed branches, with the normalized endpoint colors.
Colors one through five are represented by zero through four in `Fin 5`. -/
structure DecoderContract (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label) : Prop where
  decode : ∀ (a : Label) (y : ℝ), y ∈ stateInterval (outgoing a) →
    D (Q (branch a y)) (Q y) = a
  endpoints : Q (-t ^ 2) = 0 ∧ Q g = 1 ∧ Q t = 2 ∧ Q (2 * t) = 3 ∧
    Q (1 + t) = 4 ∧ Q (-1) = 3

private theorem tail_bound (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    {y : ℝ} (hy : y ∈ I) : (Q y).val < 4 := by
  obtain ⟨c, hc⟩ := hs ▸ Set.mem_image_of_mem Q hy
  rw [← hc]
  exact c.isLt

/-- The four-color restriction of the actual scalar coloring on the closed tail interval. -/
noncomputable def tailColor (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (y : I) : Fin 4 := ⟨(Q y.val).val, tail_bound Q hs y.property⟩

private theorem tail_color_embed (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (y : I) : embed (tailColor Q hs y) = Q y := by
  apply Fin.ext
  rfl

private theorem tail_represented (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (c : Fin 4) : ∃ y : I, tailColor Q hs y = c := by
  have hc : embed c ∈ Q '' I := hs ▸ Set.mem_range_self c
  obtain ⟨y, hy, he⟩ := hc
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Fin.ext
  change (Q y).val = c.val
  exact congrArg Fin.val he

private noncomputable def representative (Q : ℝ → Fin 5)
    (hs : Q '' I = Set.range embed) (c : Fin 4) : I :=
  Classical.choose (tail_represented Q hs c)

private theorem inward_maps (i : Fin 3) :
    Set.MapsTo (branch (labelIndex (i.castLE (by decide)))) I I := by
  have hpath : SourcePath true [labelIndex (i.castLE (by decide))]
      (outgoing (labelIndex (i.castLE (by decide)))) := by
    apply SourcePath.cons _ (SourcePath.nil _)
    refine ⟨?_, rfl⟩
    intro _
    fin_cases i <;> decide
  intro y hy
  apply source_path_maps hpath
  cases h : outgoing (labelIndex (i.castLE (by decide)))
  · exact state_subset true hy
  · exact hy

/-- The unique inward output color of a tail-color column, realized by an actual tail. -/
noncomputable def branchColor (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (i : Fin 3) (c : Fin 4) : Fin 4 :=
  tailColor Q hs ⟨branch (labelIndex (i.castLE (by decide))) (representative Q hs c),
    inward_maps i (representative Q hs c).property⟩

private theorem representative_color (Q : ℝ → Fin 5)
    (hs : Q '' I = Set.range embed) (c : Fin 4) :
    Q (representative Q hs c) = embed c := by
  rw [← tail_color_embed Q hs]
  exact congrArg embed (Classical.choose_spec (tail_represented Q hs c))

private theorem column_injective (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label)
    (hD : DecoderContract Q D) (hs : Q '' I = Set.range embed) (c : Fin 4) :
    Injective (fun r => D r (embed c)) := by
  let y := representative Q hs c
  let outputs (i : Fin 5) := Q (branch (labelIndex i) y)
  have decoded (i : Fin 5) : D (outputs i) (embed c) = labelIndex i := by
    rw [← representative_color Q hs c]
    apply hD.decode
    cases h : outgoing (labelIndex i)
    · exact state_subset true y.property
    · exact y.property
  have ho : Injective outputs := by
    intro i j he
    apply label_index_injective
    rw [← decoded i, ← decoded j, he]
  have hsurj : Surjective outputs := (Finite.injective_iff_surjective).mp ho
  intro r s he
  obtain ⟨i, rfl⟩ := hsurj r
  obtain ⟨j, rfl⟩ := hsurj s
  change D (outputs i) (embed c) = D (outputs j) (embed c) at he
  apply congrArg outputs
  apply label_index_injective
  rwa [decoded i, decoded j] at he

private theorem branch_color_decode (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label)
    (hD : DecoderContract Q D) (hs : Q '' I = Set.range embed) (i : Fin 3) (c : Fin 4) :
    D (embed (branchColor Q hs i c)) (embed c) = labelIndex (i.castLE (by decide)) := by
  rw [branchColor, tail_color_embed, ← representative_color Q hs c]
  apply hD.decode
  cases h : outgoing (labelIndex (i.castLE (by decide)))
  · exact state_subset true (representative Q hs c).property
  · exact (representative Q hs c).property

private theorem branch_color_actual (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label)
    (hD : DecoderContract Q D) (hs : Q '' I = Set.range embed) (i : Fin 3) (y : I) :
    tailColor Q hs ⟨branch (labelIndex (i.castLE (by decide))) y, inward_maps i y.property⟩ =
      branchColor Q hs i (tailColor Q hs y) := by
  apply Fin.ext
  have he := column_injective Q D hD hs (tailColor Q hs y)
  have hd : D (Q (branch (labelIndex (i.castLE (by decide))) y))
      (embed (tailColor Q hs y)) = labelIndex (i.castLE (by decide)) := by
    rw [tail_color_embed]
    apply hD.decode
    cases h : outgoing (labelIndex (i.castLE (by decide)))
    · exact state_subset true y.property
    · exact y.property
  change (Q (branch (labelIndex (i.castLE (by decide))) y)).val =
    (branchColor Q hs i (tailColor Q hs y)).val
  exact congrArg Fin.val (he (hd.trans (branch_color_decode Q D hD hs i _).symm))

private theorem branch_colors_distinct (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label)
    (hD : DecoderContract Q D) (hs : Q '' I = Set.range embed)
    (c : Fin 4) : Injective (fun i : Fin 3 => branchColor Q hs i c) := by
  intro i j he
  have hd := congrArg (fun r => D (embed r) (embed c)) he
  rw [branch_color_decode Q D hD hs, branch_color_decode Q D hD hs] at hd
  have hi := label_index_injective hd
  apply Fin.ext
  exact congrArg (fun v : Fin 5 => v.val) hi

private theorem word_maps {s : Bool} {w : List Label} (hw : SourcePath true w s) :
    Set.MapsTo (wordScalar w) I I := by
  intro y hy
  apply source_path_maps hw
  cases s
  · exact state_subset true hy
  · exact hy

private theorem fixed_color (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (f : ℝ → ℝ) (hf : Continuous f) (hm : Set.MapsTo f I I) (T : Fin 4 → Fin 4)
    (hi : ∀ y : I, tailColor Q hs ⟨f y, hm y.property⟩ = T (tailColor Q hs y)) :
    ∃ c : Fin 4, T c = c := by
  have hI : (-1 : ℝ) ≤ t := by linarith [golden_relations.1]
  obtain ⟨z, hz, he⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hf.continuousOn hI hm
  refine ⟨tailColor Q hs ⟨z, hz⟩, ?_⟩
  rw [← hi ⟨z, hz⟩]
  exact congrArg (tailColor Q hs) (Subtype.ext he)

/-- Three disjoint fixed-color sets leave room for at most one periodic color. -/
private theorem fixed_colors_obstruct_cycle (F : Fin 3 → Fin 4 → Fin 4)
    (V : Fin 4 → Fin 4) (a : Fin 3) (m : ℕ) (hm : 1 ≤ m)
    (hsep : ∀ d, Injective (fun i => F i d))
    (hroot : ∃ d, (F a ∘ V) d = d)
    (hother : ∀ i, i ≠ a → ∃ d, F i (V ((F a ∘ V)^[m - 1] d)) = d)
    (c : Fin 4) (hc : (F a ∘ V)^[m] c = c) : (F a ∘ V) c = c := by
  classical
  let T := F a ∘ V
  let L (i : Fin 3) : Fin 4 → Fin 4 :=
    if i = a then T else fun d => F i (V (T^[m - 1] d))
  have hroots (i : Fin 3) : ∃ d, L i d = d := by
    by_cases hi : i = a
    · simpa only [L, if_pos hi] using hroot
    · simpa only [L, if_neg hi] using hother i hi
  have haway (i : Fin 3) (hi : i ≠ a) (d : Fin 4) (hd : T d = d) : L i d ≠ d := by
    simp only [L, if_neg hi, iterate_fixed hd]
    intro he
    exact hi (hsep (V d) (he.trans hd.symm))
  have hdisjoint (i j : Fin 3) (hij : i ≠ j) (d : Fin 4)
      (hi : L i d = d) (hj : L j d = d) : False := by
    by_cases hia : i = a
    · have hd : T d = d := by simpa only [L, if_pos hia] using hi
      exact haway j (by simpa only [hia, ne_eq, eq_comm] using hij) d hd hj
    by_cases hja : j = a
    · have hd : T d = d := by simpa only [L, if_pos hja] using hj
      exact haway i hia d hd hi
    simp only [L, if_neg hia] at hi
    simp only [L, if_neg hja] at hj
    exact hij (hsep _ (hi.trans hj.symm))
  by_contra hn
  change T c ≠ c at hn
  have hperiod (d : Fin 4) (hd : T^[m] d = d) (hnd : T d ≠ d) (i : Fin 3) :
      L i d ≠ d := by
    by_cases hi : i = a
    · simpa only [L, if_pos hi] using hnd
    simp only [L, if_neg hi]
    intro he
    have ha : F a (V (T^[m - 1] d)) = d := by
      change T (T^[m - 1] d) = d
      rw [← iterate_succ_apply' T (m - 1) d, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hm]
      exact hd
    exact hi (hsep _ (he.trans ha.symm))
  have htc : T^[m] (T c) = T c := by
    rw [← iterate_succ_apply, iterate_succ_apply', hc]
  have hntc : T (T c) ≠ T c := by
    intro he
    have hp : T^[m] c = T c := by
      rw [← Nat.sub_add_cancel hm, iterate_succ_apply, iterate_fixed he]
    exact hn (hp.symm.trans hc)
  let roots (i : Fin 3) := Classical.choose (hroots i)
  have hr (i : Fin 3) : L i (roots i) = roots i := Classical.choose_spec (hroots i)
  have hrne (i j : Fin 3) (hij : i ≠ j) : roots i ≠ roots j := by
    intro he
    apply hdisjoint i j hij (roots i) (hr i)
    rw [he]
    exact hr j
  have hcne (i : Fin 3) : c ≠ roots i := by
    intro he
    apply hperiod c hc hn i
    rw [he]
    exact hr i
  have htne (i : Fin 3) : T c ≠ roots i := by
    intro he
    apply hperiod (T c) htc hntc i
    rw [he]
    exact hr i
  have hbound := Finset.card_le_univ ({c, T c, roots 0, roots 1, roots 2} : Finset (Fin 4))
  have h01 := hrne 0 1 (by decide)
  have h02 := hrne 0 2 (by decide)
  have h12 := hrne 1 2 (by decide)
  have hcard : ({c, T c, roots 0, roots 1, roots 2} : Finset (Fin 4)).card = 5 := by
    simp [Finset.card_insert_eq_ite, hcne 0, hcne 1, hcne 2,
      htne 0, htne 1, htne 2, h01, h02, h12, Ne.symm hn]
  rw [hcard] at hbound
  norm_num at hbound

/-- Each alternate inward outer branch has a fixed color for the same actual inner composite. -/
private theorem three_fixed_colors (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label)
    (hD : DecoderContract Q D) (hs : Q '' I = Set.range embed)
    {s : Bool} (w : List Label) (hw : SourcePath true w s)
    (V : Fin 4 → Fin 4)
    (hV : ∀ y : I, tailColor Q hs ⟨wordScalar w y, word_maps hw y.property⟩ =
      V (tailColor Q hs y))
    (a : Fin 3) (n : ℕ) :
    (∃ d, (branchColor Q hs a ∘ V) d = d) ∧
    ∀ i : Fin 3, ∃ d,
      branchColor Q hs i (V ((branchColor Q hs a ∘ V)^[n] d)) = d := by
  let f : ℝ → ℝ := branch (labelIndex (a.castLE (by decide))) ∘ wordScalar w
  let T := branchColor Q hs a ∘ V
  have hf : Continuous f := by
    apply Continuous.comp _ (wordScalar_continuous w)
    unfold branch
    fun_prop
  have hfm : Set.MapsTo f I I := (inward_maps a).comp (word_maps hw)
  have hT : ∀ y : I, tailColor Q hs ⟨f y, hfm y.property⟩ = T (tailColor Q hs y) := by
    intro y
    exact (branch_color_actual Q D hD hs a
      ⟨wordScalar w y, word_maps hw y.property⟩).trans
      (congrArg (branchColor Q hs a) (hV y))
  have hit : Semiconj (tailColor Q hs) (hfm.restrict f I I) T := hT
  have hn (y : I) : tailColor Q hs ⟨f^[n] y, hfm.iterate n y.property⟩ =
      T^[n] (tailColor Q hs y) := by
    have he := hit.iterate_right n y
    rwa [hfm.iterate_restrict] at he
  refine ⟨fixed_color Q hs f hf hfm T hT, ?_⟩
  intro i
  let fi : ℝ → ℝ := branch (labelIndex (i.castLE (by decide))) ∘ wordScalar w ∘ f^[n]
  have hfi : Continuous fi := by
    have hb : Continuous (branch (labelIndex (i.castLE (by decide)))) := by
      unfold branch
      fun_prop
    exact hb.comp ((wordScalar_continuous w).comp (hf.iterate n))
  have hmi : Set.MapsTo fi I I :=
    ((inward_maps i).comp (word_maps hw)).comp (hfm.iterate n)
  apply fixed_color Q hs fi hfi hmi (fun d => branchColor Q hs i (V (T^[n] d)))
  intro y
  exact (branch_color_actual Q D hD hs i
    ⟨wordScalar w (f^[n] y), word_maps hw (hfm.iterate n y.property)⟩).trans
    (congrArg (branchColor Q hs i)
      ((hV ⟨f^[n] y, hfm.iterate n y.property⟩).trans (congrArg V (hn y))))

/-- For every exact normalized five-color decoder with four colors on the tail interval,
every legal finite self-composite followed by three, null, or five induces an aperiodic
color transformation. The empty word is included, and no regularity of `Q` is assumed. -/
theorem result (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label)
    (hD : DecoderContract Q D) (hs : Q '' I = Set.range embed)
    (a : Fin 3) {s : Bool} (w : List Label) (hw : SourcePath true w s)
    (V : Fin 4 → Fin 4)
    (hV : ∀ y : I, tailColor Q hs ⟨wordScalar w y, word_maps hw y.property⟩ =
      V (tailColor Q hs y))
    (c : Fin 4) (m : ℕ) (hm : 1 ≤ m)
    (hc : (branchColor Q hs a ∘ V)^[m] c = c) :
    (branchColor Q hs a ∘ V) c = c := by
  obtain ⟨hroot, hother⟩ := three_fixed_colors Q D hD hs w hw V hV a (m - 1)
  exact fixed_colors_obstruct_cycle (branchColor Q hs) V a m hm
    (branch_colors_distinct Q D hD hs) hroot (fun i _ => hother i) c hc

end D5.S1.Digit.Infinite.FourTailColorContractionAperiodicity
