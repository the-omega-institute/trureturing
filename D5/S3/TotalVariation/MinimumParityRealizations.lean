/- GID: D5/S3/TotalVariation/MinimumParityRealizations
   generality: G
   mirror-B: D5/B/S3/TotalVariation/MinimumParityRealizations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labelled minimal affine parity presentations have a finite coordinate description. -/

import D5.S3.TotalVariation.MinimumParityInputs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! Coordinates for the labelled minimal affine independent-bit presentations of a fixed law. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.MinimumParityRealizations

open D5.S3.TotalVariation.GroupedParityBias
open D5.S3.TotalVariation.QuotientParitySpectrum
open D5.S3.TotalVariation.MinimumParityInputs

universe u v w

section Reconstruction
variable {A : Type u} {I : Type v} {J : Type w}
  [AddCommGroup A] [Fintype A] [Fintype I] [Fintype J]

private theorem moment_eq_zero_of_nontrivial_on_fair_columns
    (two : ∀ a : A, a + a = 0) (c : I → A) (s : A) (q : I → ℝ)
    (χ : AddChar A ℂ) (hχ : ¬ ∀ a ∈ fairSpan c q, χ a = 1) :
    moment (law c s q) χ = 0 := by
  by_contra hn
  apply hχ
  apply trivial_on_closure
  rintro _ ⟨i, hi, rfl⟩
  exact (support_iff_trivial_on_fair_columns two c s q χ).1 hn i hi

omit [Fintype A] in
private theorem absolute_group_product {B : Type*} (c : I → B) (q : I → ℝ) (b : B) :
    groupBias c (fun i => |q i|) b = |groupBias c q b| := by
  rw [groupBias, groupBias, Finset.abs_prod]

private theorem law_eq_of_matching_quotient_data
    (two : ∀ a : A, a + a = 0)
    (c : I → A) (s : A) (q : I → ℝ) (d : J → A) (t : A) (r : J → ℝ)
    (hspan : fairSpan d r = fairSpan c q) :
    let H := fairSpan c q
    let π := QuotientAddGroup.mk' H
    (s + ∑ i with q i < 0, c i) - (t + ∑ j with r j < 0, d j) ∈ H →
    (∀ a : A ⧸ H, a ≠ 0 → |groupBias (π ∘ c) q a| = |groupBias (π ∘ d) r a|) →
    law c s q = law d t r := by
  classical
  intro H π hoffset hgroup
  let _ : Fintype (A ⧸ H) := Fintype.ofFinite _
  apply law_from_moments two
  intro χ
  by_cases hχ : ∀ a ∈ H, χ a = 1
  · obtain ⟨φ, rfl⟩ := trivial_character_descends H χ hχ
    let ψ := φ.compAddMonoidHom π
    let s' := s + ∑ i with q i < 0, c i
    let t' := t + ∑ j with r j < 0, d j
    have hphase : ψ s' = ψ t' := by
      calc
        ψ s' = ψ ((s' - t') + t') := by rw [sub_add_cancel]
        _ = ψ t' := by rw [AddChar.map_add_eq_mul, hχ _ hoffset, one_mul]
    have he : sign ψ s' = sign ψ t' := congrArg Complex.re hphase
    rw [sign_phase_and_magnitude two c s q ψ, sign_phase_and_magnitude two d t r ψ]
    change sign ψ s' * moment (law c (0 : A) (fun i => |q i|)) ψ =
      sign ψ t' * moment (law d (0 : A) (fun j => |r j|)) ψ
    rw [he, moment_pushforward two, moment_pushforward two, map_zero]
    rw [moment_factor (quotient_two H two), moment_factor (quotient_two H two)]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    rw [absolute_group_product, absolute_group_product]
    apply hgroup a
    intro hz
    have hsign := (Finset.mem_filter.mp ha).2
    norm_num [hz, sign] at hsign
  · have hd : ¬ ∀ a ∈ fairSpan d r, χ a = 1 := by
      rw [hspan]
      exact hχ
    rw [moment_eq_zero_of_nontrivial_on_fair_columns two c s q χ hχ,
      moment_eq_zero_of_nontrivial_on_fair_columns two d t r χ hd]


end Reconstruction

section Coordinates
variable {I : Type v} [Fintype I]

omit [Fintype I] in
private theorem fair_column_member {A : Type u} [AddCommGroup A]
    (c : I → A) (q : I → ℝ) (i : I) (hi : q i = 0) : c i ∈ fairSpan c q :=
  AddSubgroup.subset_closure ⟨i, hi, rfl⟩

variable {A : Type u} [AddCommGroup A] [Fintype A] [Module (ZMod 2) A]

private theorem fair_column_span (c : I → A) (q : I → ℝ) :
    Submodule.span (ZMod 2) (Set.range (fun i : {i : I // q i = 0} => c i)) =
      AddSubgroup.toZModSubmodule 2 (fairSpan c q) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨i, rfl⟩
    exact fair_column_member c q i i.property
  · change fairSpan c q ≤ (Submodule.span (ZMod 2)
      (Set.range (fun i : {i : I // q i = 0} => c i))).toAddSubgroup
    apply (AddSubgroup.closure_le _).mpr
    rintro a ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

private theorem minimum_fair_basis_and_quotient_factors (two : ∀ a : A, a + a = 0)
    (c : I → A) (s : A) (q : I → ℝ)
    (hmin : Fintype.card I = minimumInputCount (law c s q)) :
    let H := fairSpan c q
    let B := {a : A ⧸ H // a ≠ 0 ∧ visibleBias H (law c s q) a < 1}
    LinearIndependent (ZMod 2) (fun i : {i : I // q i = 0} => c i) ∧
      ∃ e : B ≃ {i : I // q i ≠ 0}, ∀ a : B,
        QuotientAddGroup.mk' H (c (e a)) = a ∧
          |q (e a)| = visibleBias H (law c s q) a := by
  classical
  let H := fairSpan c q
  let B := {a : A ⧸ H // a ≠ 0 ∧ visibleBias H (law c s q) a < 1}
  let F := {i : I // q i = 0}
  let N := {i : I // q i ≠ 0}
  let π := QuotientAddGroup.mk' H
  let f : I → A ⧸ H := π ∘ c
  letI : DecidableEq (A ⧸ H) := fun x y => Classical.propDecidable (x = y)
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype F := Fintype.ofFinite _
  letI : Fintype N := Fintype.ofFinite _
  have hFairZero (i : I) (hi : q i = 0) : f i = 0 := by
    change c i ∈ π.ker
    rw [QuotientAddGroup.ker_mk']
    exact fair_column_member c q i hi
  have hver (a : B) : ∃ i : N, f i = a.val := by
    have hprod : |groupBias f q a.val| < 1 := by
      rw [← visibleBias_recovered two c s q a.val a.property.1]
      exact a.property.2
    by_contra hn
    have hone : groupBias f q a.val = 1 := by
      unfold groupBias
      apply Finset.prod_eq_one
      intro i hi
      have he := (Finset.mem_filter.mp hi).2
      have hnonfair : q i ≠ 0 := fun hz => a.property.1 (he.symm.trans (hFairZero i hz))
      exact (hn ⟨⟨i, hnonfair⟩, he⟩).elim
    rw [hone, abs_one] at hprod
    exact lt_irrefl _ hprod
  choose g hg using hver
  have hginj : Function.Injective g := by
    intro a b he
    exact Subtype.ext ((hg a).symm.trans ((congrArg (fun i : N => f i) he).trans (hg b)))
  let rank := Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2 H)
  have hsum : Fintype.card I = rank + Fintype.card B := by
    rw [minimumInputCount, ← fairSpan_eq_spectralAnnihilator two] at hmin
    exact hmin.trans (congrArg (rank + ·) Nat.card_eq_fintype_card)
  have hspan : Submodule.span (ZMod 2) (Set.range (fun i : F => c i)) =
      AddSubgroup.toZModSubmodule 2 H := fair_column_span c q
  have hf : rank ≤ Fintype.card F := by
    change Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2 H) ≤ Fintype.card F
    rw [← hspan]
    exact finrank_range_le_card (R := ZMod 2) (fun i : F => c i)
  have hgcard := Fintype.card_le_of_injective _ hginj
  have hcomp : Fintype.card N = Fintype.card I - Fintype.card F :=
    Fintype.card_subtype_compl (fun i : I => q i = 0)
  have hfcard : Fintype.card F ≤ Fintype.card I := Fintype.card_subtype_le (fun i : I => q i = 0)
  have hfeq : Fintype.card F = rank := by omega
  have hneq : Fintype.card B = Fintype.card N := by omega
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hneq⟩)
  refine ⟨(linearIndependent_iff_card_eq_finrank_span (R := ZMod 2)).mpr ?_, e, ?_⟩
  · change Fintype.card F = Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun i : F => c i)))
    rwa [hspan]
  · intro a
    refine ⟨hg a, ?_⟩
    have he : f (g a) = a.val := hg a
    have hfiber (i : I) (hi : f i = a.val) : i = (g a).val := by
      let j : N := ⟨i, fun hz => a.property.1 (hi.symm.trans (hFairZero i hz))⟩
      obtain ⟨b, hb⟩ := e.surjective j
      have hba : b = a := Subtype.ext ((hg b).symm.trans
        ((congrArg (fun i : N => f i) hb).trans hi))
      rw [hba] at hb
      exact (congrArg Subtype.val hb).symm
    have hprod : groupBias f q a.val = q (g a) := by
      unfold groupBias
      apply Finset.prod_eq_single_of_mem (g a).val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      intro i hi hne
      exact (hne (hfiber i (Finset.mem_filter.mp hi).2)).elim
    rw [visibleBias_recovered two c s q a.val a.property.1]
    change |q (g a)| = |groupBias f q a.val|
    rw [hprod]

/-- The columns and signed biases at the prescribed input labels, with the affine offset. -/
@[ext]
structure Parameters (I : Type v) (A : Type u) where
  column : I → A
  offset : A
  bias : I → ℝ

/-- The valid representations of a law at a fixed set of input labels. -/
def Presentations (I : Type v) [Fintype I] (μ : A → ℝ) : Type (max u v) :=
  {p : Parameters I A // (∀ i, |p.bias i| ≤ 1) ∧ law p.column p.offset p.bias = μ}

private abbrev Active (H : AddSubgroup A) (μ : A → ℝ) :=
  {a : A ⧸ H // a ≠ 0 ∧ visibleBias H μ a < 1}

private abbrev FairSpace (H : AddSubgroup A) := ↥(AddSubgroup.toZModSubmodule 2 H)

/-- The biased labels occupy one slot per active quotient column. The unused labels index a
basis of the fair subgroup. The final offset coordinate is the sign-corrected offset. -/
structure Choices (I : Type v) (H : AddSubgroup A) (μ : A → ℝ) (s : A) where
  placement : Active H μ ↪ I
  basis : {i : I // i ∉ Set.range placement} → FairSpace H
  independent : LinearIndependent (ZMod 2) basis
  representative : ∀ a : Active H μ, {x : A // QuotientAddGroup.mk' H x = a.val}
  negative : Active H μ → Bool
  corrected : {x : A // QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H s}

private noncomputable def slots {B : Type*} (e : B ↪ I) :
    B ⊕ {i : I // i ∉ Set.range e} ≃ I := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (· ∈ Set.range e))

private theorem slots_active {B : Type*} (e : B ↪ I) (b : B) :
    slots e (.inl b) = e b := rfl

private theorem slots_fair {B : Type*} (e : B ↪ I) (i : {i : I // i ∉ Set.range e}) :
    slots e (.inr i) = i := rfl

private noncomputable def decodeColumn {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) : I → A :=
  Sum.elim (fun a => (ch.representative a).val) (fun i => (ch.basis i).val) ∘
    (slots ch.placement).symm

private noncomputable def decodeBias {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) : I → ℝ :=
  Sum.elim (fun a => if ch.negative a then -visibleBias H μ a.val else visibleBias H μ a.val)
    (fun _ => 0) ∘ (slots ch.placement).symm

private theorem decode_column_active {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (a : Active H μ) :
    decodeColumn ch (ch.placement a) = (ch.representative a).val := by
  rw [← slots_active ch.placement a]
  simp [decodeColumn]

private theorem decode_column_fair {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (i : {i : I // i ∉ Set.range ch.placement}) :
    decodeColumn ch i = (ch.basis i).val := by
  rw [← slots_fair ch.placement i]
  simp [decodeColumn]

private theorem decode_bias_active {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (a : Active H μ) :
    decodeBias ch (ch.placement a) =
      if ch.negative a then -visibleBias H μ a.val else visibleBias H μ a.val := by
  rw [← slots_active ch.placement a]
  simp [decodeBias]

private theorem decode_bias_fair {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (i : {i : I // i ∉ Set.range ch.placement}) :
    decodeBias ch i = 0 := by
  rw [← slots_fair ch.placement i]
  simp [decodeBias]

noncomputable section

/-- Decode the input columns, signed factors, and raw affine offset from the choices. -/
def decode {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) : Parameters I A := by
  classical
  exact ⟨decodeColumn ch,
    ch.corrected.val - ∑ i with decodeBias ch i < 0, decodeColumn ch i, decodeBias ch⟩

private theorem visible_bias_positive (H : AddSubgroup A) (μ : A → ℝ) (a : A ⧸ H) :
    0 < visibleBias H μ a := by
  unfold visibleBias
  exact Real.exp_pos _

private theorem decode_nonfair_iff {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (i : I) :
    decodeBias ch i ≠ 0 ↔ i ∈ Set.range ch.placement := by
  obtain ⟨b | j, rfl⟩ := (slots ch.placement).surjective i
  · rw [slots_active, decode_bias_active]
    have hpos := (visible_bias_positive H μ b.val).ne'
    cases h : ch.negative b <;> simp [h, hpos]
  · rw [slots_fair, decode_bias_fair]
    simp [j.property]

set_option maxHeartbeats 650000 in
private theorem decode_fair_span {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s)
    (hcard : Fintype.card I =
      Module.finrank (ZMod 2) (FairSpace H) + Nat.card (Active H μ)) :
    fairSpan (decodeColumn ch) (decodeBias ch) = H := by
  classical
  let B := Active H μ
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype ((Set.range ch.placement)ᶜ : Set I) := Fintype.ofFinite _
  letI : Fintype (Set.range ch.placement) := Fintype.ofFinite _
  have hfcard : Fintype.card ((Set.range ch.placement)ᶜ : Set I) =
      Module.finrank (ZMod 2) (FairSpace H) := by
    rw [Fintype.card_compl_set, Fintype.card_range ch.placement, hcard,
      Nat.card_eq_fintype_card, Nat.add_sub_cancel_right]
  have hfcard' : Fintype.card {i : I // i ∉ Set.range ch.placement} =
      Module.finrank (ZMod 2) (FairSpace H) := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_eq_fintype_card :
      Nat.card ((Set.range ch.placement)ᶜ : Set I) =
        Fintype.card ((Set.range ch.placement)ᶜ : Set I)).trans hfcard
  have hspan := ch.independent.span_eq_top_of_card_eq_finrank' hfcard'
  apply le_antisymm
  · apply (AddSubgroup.closure_le H).mpr
    rintro x ⟨i, hq, rfl⟩
    have hi : i ∉ Set.range ch.placement := by
      intro he
      exact ((decode_nonfair_iff ch i).mpr he) hq
    rw [decode_column_fair ch ⟨i, hi⟩]
    exact (ch.basis ⟨i, hi⟩).property
  · let K := fairSpan (decodeColumn ch) (decodeBias ch)
    let V := AddSubgroup.toZModSubmodule 2 H
    let L := AddSubgroup.toZModSubmodule 2 K
    have hle : Submodule.span (ZMod 2) (Set.range ch.basis) ≤ L.comap V.subtype := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      change (ch.basis i).val ∈ K
      rw [← decode_column_fair ch i]
      exact fair_column_member (decodeColumn ch) (decodeBias ch) i (decode_bias_fair ch i)
    rw [hspan] at hle
    intro x hx
    have hxmem : (⟨x, hx⟩ : V) ∈ L.comap V.subtype :=
      hle (Submodule.mem_top (x := (⟨x, hx⟩ : V)))
    exact hxmem

private theorem decode_bias_abs {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (a : Active H μ) :
    |decodeBias ch (ch.placement a)| = visibleBias H μ a.val := by
  rw [decode_bias_active]
  have h := (visible_bias_positive H μ a.val).le
  cases hh : ch.negative a <;> simp [hh, abs_of_nonneg h]

private theorem min_repr_bias_bound {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (i : I) : |decodeBias ch i| ≤ 1 := by
  obtain ⟨a | f, rfl⟩ := (slots ch.placement).surjective i
  · rw [slots_active, decode_bias_abs]
    exact a.property.2.le
  · rw [slots_fair, decode_bias_fair, abs_zero]
    exact zero_le_one

private theorem decode_groupBias {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) (a : A ⧸ H) (ha : a ≠ 0)
    (hbound : visibleBias H μ a ≤ 1) :
    |groupBias (QuotientAddGroup.mk' H ∘ decodeColumn ch) (decodeBias ch) a| =
      visibleBias H μ a := by
  classical
  let π := QuotientAddGroup.mk' H
  letI : DecidableEq (A ⧸ H) := fun x y => Classical.propDecidable (x = y)
  have hread (i : I) (hi : π (decodeColumn ch i) = a) :
      ∃ b : Active H μ, i = ch.placement b ∧ b.val = a := by
    obtain ⟨b | j, rfl⟩ := (slots ch.placement).surjective i
    · rw [slots_active, decode_column_active] at hi
      exact ⟨b, slots_active ch.placement b, (ch.representative b).property.symm.trans hi⟩
    · rw [slots_fair, decode_column_fair] at hi
      have hz : π (ch.basis j).val = 0 := by
        change (ch.basis j).val ∈ π.ker
        rw [QuotientAddGroup.ker_mk']
        exact (ch.basis j).property
      exact (ha (hi.symm.trans hz)).elim
  by_cases hlt : visibleBias H μ a < 1
  · let b : Active H μ := ⟨a, ha, hlt⟩
    have hpoint : π (decodeColumn ch (ch.placement b)) = a := by
      rw [decode_column_active]
      exact (ch.representative b).property
    have hone : groupBias (π ∘ decodeColumn ch) (decodeBias ch) a =
        decodeBias ch (ch.placement b) := by
      unfold groupBias
      apply Finset.prod_eq_single_of_mem (ch.placement b) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hpoint⟩)
      intro i hi hne
      obtain ⟨d, hid, hd⟩ := hread i (Finset.mem_filter.mp hi).2
      have he : d = b := Subtype.ext hd
      exact (hne (hid.trans (congrArg ch.placement he))).elim
    rw [hone, decode_bias_abs]
  · have hone : groupBias (π ∘ decodeColumn ch) (decodeBias ch) a = 1 := by
      unfold groupBias
      apply Finset.prod_eq_one
      intro i hi
      obtain ⟨d, _, hd⟩ := hread i (Finset.mem_filter.mp hi).2
      exact (hlt (hd ▸ d.property.2)).elim
    rw [hone, abs_one]
    exact (le_antisymm hbound (le_of_not_gt hlt)).symm

private theorem adjusted_decode_offset {H : AddSubgroup A} {μ : A → ℝ} {s : A}
    (ch : Choices I H μ s) :
    (decode ch).offset + ∑ i with (decode ch).bias i < 0, (decode ch).column i =
      ch.corrected.val := by
  classical
  unfold decode
  exact sub_add_cancel _ _

private theorem decode_law {J : Type*} [Fintype J] (two : ∀ a : A, a + a = 0)
    (c : J → A) (s : A) (q : J → ℝ) (hq : ∀ i, |q i| ≤ 1)
    (ch : Choices I (fairSpan c q) (law c s q) (s + ∑ j with q j < 0, c j))
    (hcard : Fintype.card I = minimumInputCount (law c s q)) :
    law (decode ch).column (decode ch).offset (decode ch).bias = law c s q := by
  classical
  let H := fairSpan c q
  let π := QuotientAddGroup.mk' H
  have hcount : Fintype.card I =
      Module.finrank (ZMod 2) (FairSpace H) + Nat.card (Active H (law c s q)) := by
    rw [minimumInputCount, ← fairSpan_eq_spectralAnnihilator two] at hcard
    exact hcard
  have hspan : fairSpan (decode ch).column (decode ch).bias = H := decode_fair_span ch hcount
  symm
  apply law_eq_of_matching_quotient_data two c s q _ _ _ hspan
  · rw [adjusted_decode_offset]
    change s + (∑ j with q j < 0, c j) - ch.corrected.val ∈ H
    rw [← QuotientAddGroup.ker_mk' H]
    change π (s + (∑ j with q j < 0, c j) - ch.corrected.val) = 0
    rw [map_sub, ch.corrected.property, sub_self]
  · intro a ha
    have habs := visibleBias_recovered two c s q a ha
    rw [← habs]
    symm
    apply decode_groupBias ch a ha
    rw [habs, groupBias, Finset.abs_prod]
    apply Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hq i)

private theorem corrected_offset_positive {J : Type*} [Fintype J] (two : ∀ a : A, a + a = 0)
    (c : J → A) (s : A) (q : J → ℝ) (χ : AddChar A ℂ)
    (hχ : moment (law c s q) χ ≠ 0) :
    0 < sign χ (s + ∑ j with q j < 0, c j) * moment (law c s q) χ := by
  classical
  let s' := s + ∑ j with q j < 0, c j
  have hphase : moment (law c s q) χ =
      sign χ s' * moment (law c (0 : A) (fun j => |q j|)) χ :=
    sign_phase_and_magnitude two c s q χ
  have hn : moment (law c (0 : A) (fun j => |q j|)) χ ≠ 0 := by
    intro hz
    exact hχ (by rw [hphase, hz, mul_zero])
  change 0 < sign χ s' * moment (law c s q) χ
  rw [hphase, ← mul_assoc, sign_sq_eq_one two, one_mul]
  apply lt_of_le_of_ne _ hn.symm
  rw [moment_from_inputs two, show sign χ 0 = 1 by simp [sign], one_mul]
  exact Finset.prod_nonneg (fun i _ => by split <;> positivity)

set_option maxHeartbeats 650000 in
private theorem decode_surjective {J : Type*} [Fintype J] (two : ∀ a : A, a + a = 0)
    (c : J → A) (s : A) (q : J → ℝ)
    (hcard : Fintype.card I = minimumInputCount (law c s q))
    (p : Parameters I A) (hp : law p.column p.offset p.bias = law c s q) :
    ∃ ch : Choices I (fairSpan c q) (law c s q) (s + ∑ j with q j < 0, c j), decode ch = p := by
  classical
  let H := fairSpan c q
  let μ := law c s q
  let π := QuotientAddGroup.mk' H
  let B := Active H μ
  let s' := s + ∑ j with q j < 0, c j
  let p' := p.offset + ∑ i with p.bias i < 0, p.column i
  have hspan : fairSpan p.column p.bias = H := by
    rw [fairSpan_eq_spectralAnnihilator two, hp, ← fairSpan_eq_spectralAnnihilator two]
  have hmin : Fintype.card I = minimumInputCount (law p.column p.offset p.bias) :=
    hp.symm ▸ hcard
  have hshape := minimum_fair_basis_and_quotient_factors two p.column p.offset p.bias hmin
  dsimp only at hshape
  rw [hspan, hp] at hshape
  obtain ⟨hli, e₀, he⟩ := hshape
  let e : B ↪ I := e₀.toEmbedding.trans (Function.Embedding.subtype (fun i => p.bias i ≠ 0))
  have he_active (a : B) : π (p.column (e a)) = a.val := (he a).1
  have habs (a : B) : |p.bias (e a)| = visibleBias H μ a.val := (he a).2
  have hrange (i : I) : i ∈ Set.range e ↔ p.bias i ≠ 0 := by
    constructor
    · rintro ⟨a, rfl⟩
      exact (e₀ a).property
    · intro hn
      obtain ⟨a, ha⟩ := e₀.surjective ⟨i, hn⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hf (i : {i : I // i ∉ Set.range e}) : p.bias i = 0 := by
    by_contra hn
    exact i.property ((hrange i).mpr hn)
  let fairIndex : {i : I // i ∉ Set.range e} → {i : I // p.bias i = 0} :=
    fun i => ⟨i, hf i⟩
  let basis : {i : I // i ∉ Set.range e} → FairSpace H := fun i =>
    ⟨p.column i, hspan ▸ fair_column_member p.column p.bias i (hf i)⟩
  have hlin : LinearIndependent (ZMod 2) basis := by
    apply ((AddSubgroup.toZModSubmodule 2 H).subtype.linearIndependent_iff_of_injOn
      (v := basis) (Submodule.subtype_injective _).injOn).mp
    exact hli.comp fairIndex (fun _ _ h =>
      Subtype.ext (congrArg (fun i : {i : I // p.bias i = 0} => i.val) h))
  have hps (χ : AddChar A ℂ) (hχ : moment μ χ ≠ 0) : 0 < sign χ p' * moment μ χ := by
    have h := corrected_offset_positive two p.column p.offset p.bias χ (by rwa [hp])
    rwa [hp] at h
  have hss (χ : AddChar A ℂ) (hχ : moment μ χ ≠ 0) : 0 < sign χ s' * moment μ χ :=
    corrected_offset_positive two c s q χ hχ
  have hoff : π p' = π s' := by
    have hm := signed_offsets_agree_modulo_annihilator two μ p' s' hps hss
    rw [← fairSpan_eq_spectralAnnihilator two c s q] at hm
    have hzero : π (p' - s') = 0 := by
      change p' - s' ∈ π.ker
      rw [QuotientAddGroup.ker_mk']
      exact hm
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero
  let ch : Choices I H μ s' :=
    ⟨e, basis, hlin, fun a => ⟨p.column (e a), he_active a⟩,
      fun a => decide (p.bias (e a) < 0), ⟨p', hoff⟩⟩
  have hc : decodeColumn ch = p.column := by
    funext i
    obtain ⟨a | j, rfl⟩ := (slots ch.placement).surjective i
    · rw [slots_active, decode_column_active]
    · rw [slots_fair, decode_column_fair]
  have hb : decodeBias ch = p.bias := by
    funext i
    obtain ⟨a | j, rfl⟩ := (slots ch.placement).surjective i
    · rw [slots_active, decode_bias_active]
      change (if decide (p.bias (e a) < 0) then -visibleBias H μ a.val
        else visibleBias H μ a.val) = p.bias (e a)
      rw [← habs]
      rcases lt_or_ge (p.bias (e a)) 0 with h | h
      · simp [h, abs_of_neg h]
      · simp [not_lt.mpr h, abs_of_nonneg h]
    · rw [slots_fair, decode_bias_fair]
      exact (hf j).symm
  refine ⟨ch, Parameters.ext hc ?_ hb⟩
  change p' - ∑ i with decodeBias ch i < 0, decodeColumn ch i = p.offset
  rw [hc, hb, add_sub_cancel_right]

set_option maxHeartbeats 650000 in
private theorem decode_injective (H : AddSubgroup A) (μ : A → ℝ) (s : A) :
    Function.Injective (decode : Choices I H μ s → Parameters I A) := by
  classical
  intro x y h
  have hc : decodeColumn x = decodeColumn y := congrArg Parameters.column h
  have hb : decodeBias x = decodeBias y := congrArg Parameters.bias h
  have hoffset : x.corrected = y.corrected := by
    apply Subtype.ext
    rw [← adjusted_decode_offset x, ← adjusted_decode_offset y, h]
  have he : x.placement = y.placement := by
    ext a
    have hx : x.placement a ∈ Set.range x.placement := ⟨a, rfl⟩
    have hn := (decode_nonfair_iff x _).mpr hx
    rw [hb] at hn
    obtain ⟨b, hpos⟩ := (decode_nonfair_iff y _).mp hn
    have hcoset := congrArg (QuotientAddGroup.mk' H) (congrFun hc (x.placement a))
    rw [decode_column_active, ← hpos, decode_column_active] at hcoset
    have hab : a = b := Subtype.ext
      ((x.representative a).property.symm.trans (hcoset.trans (y.representative b).property))
    exact hpos.symm.trans (congrArg y.placement hab.symm)
  cases x with
  | mk ex bx hx rx nx tx =>
    cases y with
    | mk ey byy hy ry ny ty =>
      change ex = ey at he
      subst ey
      have hBasis : bx = byy := by
        funext i
        apply Subtype.ext
        have hi := congrFun hc i.val
        rw [decode_column_fair _ i, decode_column_fair _ i] at hi
        exact hi
      have hRep : rx = ry := by
        funext a
        apply Subtype.ext
        have hi := congrFun hc (ex a)
        rw [decode_column_active, decode_column_active] at hi
        exact hi
      have hNeg : nx = ny := by
        funext a
        have hi := congrFun hb (ex a)
        rw [decode_bias_active, decode_bias_active] at hi
        change (if nx a then -visibleBias H μ a.val else visibleBias H μ a.val) =
          (if ny a then -visibleBias H μ a.val else visibleBias H μ a.val) at hi
        have hp := visible_bias_positive H μ a.val
        cases ha : nx a <;> cases hby : ny a <;> simp_all <;> linarith
      cases hBasis
      cases hRep
      cases hNeg
      cases hoffset
      rfl

/-- At a minimum-size set of labels, the parameters of a realization are equivalent to
the choices of a fair basis, placement and lifts of the active columns, signs, and offset. -/
noncomputable def minimumPresentationsEquiv {J : Type*} [Fintype J]
    (two : ∀ a : A, a + a = 0)
    (c : J → A) (s : A) (q : J → ℝ) (hq : ∀ j, |q j| ≤ 1)
    (hcard : Fintype.card I = minimumInputCount (law c s q)) :
    Choices I (fairSpan c q) (law c s q) (s + ∑ j with q j < 0, c j) ≃
      Presentations I (law c s q) := by
  classical
  let f (ch : Choices I (fairSpan c q) (law c s q) (s + ∑ j with q j < 0, c j)) :
      Presentations I (law c s q) :=
    ⟨decode ch, min_repr_bias_bound ch, decode_law two c s q hq ch hcard⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact decode_injective _ _ _ (congrArg Subtype.val h)
  · intro p
    obtain ⟨ch, hch⟩ := decode_surjective two c s q hcard p.val p.property.2
    exact ⟨ch, Subtype.ext hch⟩

private noncomputable def quotientFiberEquiv (H : AddSubgroup A) (a : A ⧸ H) :
    {x : A // QuotientAddGroup.mk' H x = a} ≃ H := by
  let π := QuotientAddGroup.mk' H
  have hker : π.ker = H := QuotientAddGroup.ker_mk' H
  exact (AddMonoidHom.fiberEquivKerOfSurjective (QuotientAddGroup.mk'_surjective H) a).trans
    (Equiv.cast (congrArg (fun K : AddSubgroup A => ↥K) hker))

private noncomputable def fairBasisEquiv {B : Type*} [Fintype B] (H : AddSubgroup A)
    (e : B ↪ I) (hcard : Fintype.card I =
      Module.finrank (ZMod 2) (FairSpace H) + Fintype.card B) :
    {f : {i : I // i ∉ Set.range e} → FairSpace H // LinearIndependent (ZMod 2) f} ≃
      {f : Fin (Module.finrank (ZMod 2) (FairSpace H)) → FairSpace H //
        LinearIndependent (ZMod 2) f} := by
  classical
  let R := Module.finrank (ZMod 2) (FairSpace H)
  let C := ((Set.range e)ᶜ : Set I)
  letI : Fintype C := Fintype.ofFinite _
  letI : Fintype (Set.range e) := Fintype.ofFinite _
  have hC : Fintype.card C = R := by
    dsimp only [C]
    rw [Fintype.card_compl_set, Fintype.card_range e, hcard, Nat.add_sub_cancel_right]
  let t : C ≃ Fin R := Fintype.equivFinOfCardEq hC
  exact Equiv.subtypeEquiv (Equiv.arrowCongr t (Equiv.refl (FairSpace H)))
    (fun _ => (linearIndependent_equiv t.symm).symm)

private noncomputable def choicesSigmaEquiv (H : AddSubgroup A) (μ : A → ℝ) (s : A) :
    Choices I H μ s ≃
      Σ e : Active H μ ↪ I,
        {f : {i : I // i ∉ Set.range e} → FairSpace H // LinearIndependent (ZMod 2) f} ×
        (∀ a : Active H μ, {x : A // QuotientAddGroup.mk' H x = a.val}) ×
        (Active H μ → Bool) ×
        {x : A // QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H s} where
  toFun ch := ⟨ch.placement, ⟨ch.basis, ch.independent⟩,
    ch.representative, ch.negative, ch.corrected⟩
  invFun d := ⟨d.1, d.2.1.val, d.2.1.property, d.2.2.1, d.2.2.2.1, d.2.2.2.2⟩
  left_inv ch := by cases ch; rfl
  right_inv d := by cases d; rfl

private theorem card_choices (H : AddSubgroup A) (μ : A → ℝ) (s : A)
    (hcard : Fintype.card I =
      Module.finrank (ZMod 2) (FairSpace H) + Nat.card (Active H μ)) :
    let h := Module.finrank (ZMod 2) (FairSpace H)
    let b := Nat.card (Active H μ)
    Nat.card (Choices I H μ s) = (Fintype.card I).factorial / h.factorial *
      (∏ j : Fin h, (2 ^ h - 2 ^ j.val)) * Nat.card H ^ (b + 1) * 2 ^ b := by
  classical
  let B := Active H μ
  letI : Fintype B := Fintype.ofFinite _
  let h := Module.finrank (ZMod 2) (FairSpace H)
  let b := Nat.card B
  change Nat.card (Choices I H μ s) = (Fintype.card I).factorial / h.factorial *
    (∏ j : Fin h, (2 ^ h - 2 ^ j.val)) * Nat.card H ^ (b + 1) * 2 ^ b
  have hlabels : Fintype.card I = h + Fintype.card B :=
    hcard.trans (congrArg (h + ·) Nat.card_eq_fintype_card)
  let E := B ↪ I
  let L := {f : Fin h → FairSpace H // LinearIndependent (ZMod 2) f}
  let e : Choices I H μ s ≃ E × (L × (B → H) × (B → Bool) × H) :=
    (choicesSigmaEquiv H μ s).trans (Equiv.sigmaEquivProdOfEquiv fun e =>
      (fairBasisEquiv H e hlabels).prodCongr
        ((Equiv.piCongrRight fun a : B => quotientFiberEquiv H a.val).prodCongr
          ((Equiv.refl (B → Bool)).prodCongr (quotientFiberEquiv H _))))
  have he : Nat.card E = (Fintype.card I).factorial / h.factorial := by
    have hle : Fintype.card B ≤ Fintype.card I := hlabels ▸ Nat.le_add_left _ _
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Nat.descFactorial_eq_div hle,
      hlabels, Nat.add_sub_cancel_right]
  have hl : Nat.card L = ∏ j : Fin h, (2 ^ h - 2 ^ j.val) := by
    change Nat.card {f : Fin h → FairSpace H // LinearIndependent (ZMod 2) f} = _
    simpa only [ZMod.card] using
      (card_linearIndependent (K := ZMod 2) (V := FairSpace H) (le_rfl (a := h)))
  have hbool : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    he, hl, Nat.card_fun, Nat.card_fun, hbool, pow_succ]
  ac_rfl

/-- Count the labelled realizations of a fixed affine independent-bit law at the minimum
number of inputs. Here the active columns are the nonzero quotient columns with absolute
bias below one, and the fair rank is the dimension of the fair subgroup. -/
theorem minimum_presentations_card {J : Type*} [Fintype J]
    (two : ∀ a : A, a + a = 0)
    (c : J → A) (s : A) (q : J → ℝ) (hq : ∀ j, |q j| ≤ 1)
    (hcard : Fintype.card I = minimumInputCount (law c s q)) :
    let H := fairSpan c q
    let h := Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2 H)
    let b := Nat.card {a : A ⧸ H // a ≠ 0 ∧ visibleBias H (law c s q) a < 1}
    Nat.card (Presentations I (law c s q)) = (Fintype.card I).factorial / h.factorial *
      (∏ j : Fin h, (2 ^ h - 2 ^ j.val)) * Nat.card H ^ (b + 1) * 2 ^ b := by
  classical
  have he := minimumPresentationsEquiv (I := I) two c s q hq hcard
  have hc := Nat.card_congr he
  rw [minimumInputCount, ← fairSpan_eq_spectralAnnihilator two] at hcard
  exact hc.symm.trans (card_choices (fairSpan c q) (law c s q) _ hcard)

end
end Coordinates
end D5.S3.TotalVariation.MinimumParityRealizations
