/- GID: D5/S3/TotalVariation/ParityCosetReduction
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityCosetReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The image quotient of uniform noise preserves total variation. -/

import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.BigOperators

/-! Coset reduction for a finite output mixed with uniform additive noise. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.ParityCosetReduction

open D5.S3.Divergence.ClassicalDPI (channelOutput)
open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift (labelKernel)
open D5.S3.TotalVariation.Equality.DataProcessingEquality
  (total_variation_channel_eq_iff_no_sign_mixing)

open Classical in
/-- The output combines a shifted uniform additive image with a second readout.
Projection to the quotient by the noise image preserves total variation against
a reference law uniform in the first factor. -/
theorem total_variation_noise_image_quotient {F A B Z : Type*}
    [AddCommGroup F] [Fintype F] [AddCommGroup A] [Fintype A]
    [Fintype B] [Fintype Z] (noise : F →+ A) (shift : Z → A)
    (rest : Z → B) (weight : Z → ℝ) (reference : B → ℝ) :
    let Q := A ⧸ noise.range
    let project (x : A × B) : Q × B := (QuotientAddGroup.mk' noise.range x.1, x.2)
    let source (z : Z × F) : A × B := (shift z.1 + noise z.2, rest z.1)
    let μ := channelOutput (labelKernel source) (fun z => weight z.1 / Fintype.card F)
    let ν (x : A × B) := reference x.2 / Fintype.card A
    let P := channelOutput (labelKernel project) μ
    let R := channelOutput (labelKernel project) ν
    (∀ q : Q × B, P q = ∑ z with project (shift z, rest z) = q, weight z) ∧
      (∀ q : Q × B, R q = reference q.2 / Fintype.card Q) ∧
      totalVariation μ ν = totalVariation P R := by
  classical
  intro Q project source μ ν P R
  have hF : (Fintype.card F : ℝ) ≠ 0 := by positivity
  have hproject (z : Z × F) : project (source z) = project (shift z.1, rest z.1) := by
    change (QuotientAddGroup.mk' noise.range (shift z.1 + noise z.2), rest z.1) =
      (QuotientAddGroup.mk' noise.range (shift z.1), rest z.1)
    have hzero : QuotientAddGroup.mk' noise.range (noise z.2) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨z.2, rfl⟩
    rw [map_add, hzero, add_zero]
  have hconstant (x y : A × B) (h : project x = project y) : μ x = μ y := by
    have hrest : x.2 = y.2 := congrArg (fun q : Q × B => q.2) h
    have hquot :
        QuotientAddGroup.mk' noise.range x.1 = QuotientAddGroup.mk' noise.range y.1 :=
      congrArg (fun q : Q × B => q.1) h
    obtain ⟨t, ht⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hquot.symm
    have hshift : x.1 + noise t = y.1 := by rw [ht]; abel
    have hsource (z : Z × F) :
        source (z.1, z.2 + t) = y ↔ source z = x := by
      rw [show source (z.1, z.2 + t) = (shift z.1 + noise z.2 + noise t, rest z.1) by
        simp [source, map_add, add_assoc]]
      change _ = y ↔ (shift z.1 + noise z.2, rest z.1) = x
      simp only [Prod.ext_iff]
      rw [← hshift, ← hrest, add_left_inj]
    let e : Z × F ≃ Z × F := Equiv.prodCongr (Equiv.refl Z) (Equiv.addRight t)
    change (∑ z : Z × F, (weight z.1 / Fintype.card F) * labelKernel source z x) =
      ∑ z : Z × F, (weight z.1 / Fintype.card F) * labelKernel source z y
    rw [← e.sum_comp (fun z => (weight z.1 / Fintype.card F) * labelKernel source z y)]
    apply Finset.sum_congr rfl
    intro z _
    change _ * (if source z = x then 1 else 0) =
      (weight z.1 / Fintype.card F) * (if source (z.1, z.2 + t) = y then 1 else 0)
    simp only [hsource]
  have hjoint (q : Q × B) : P q = ∑ z with project (shift z, rest z) = q, weight z := by
    change (∑ x : A × B, (∑ z : Z × F, (weight z.1 / Fintype.card F) *
      labelKernel source z x) * labelKernel project x q) = _
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hcomp (z : Z × F) :
        (∑ x : A × B, labelKernel source z x * labelKernel project x q) =
        labelKernel project (source z) q := by
      rw [Finset.sum_eq_single (source z)]
      · simp [labelKernel]
      · intro x _ hx
        simp [labelKernel, Ne.symm hx]
      · simp
    simp_rw [hcomp, labelKernel, hproject]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp [nsmul_eq_mul, mul_div_cancel₀, hF]
  have hquotcard (c : Q) :
      (Finset.univ.filter (fun a : A => QuotientAddGroup.mk' noise.range a = c)).card =
        Nat.card noise.range := by
    let s : Finset A := Finset.univ.filter (fun a => QuotientAddGroup.mk' noise.range a = c)
    have he : s ≃ (QuotientAddGroup.mk : A → Q) ⁻¹' ({c} : Set Q) :=
      Equiv.subtypeEquivRight fun a => by
        change (a ∈ s ↔ QuotientAddGroup.mk' noise.range a = c)
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    have hp := QuotientAddGroup.preimageMkEquivAddSubgroupProdSet noise.range ({c} : Set Q)
    change s.card = _
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_congr (he.trans hp), Nat.card_prod]
    simp
  have hA : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hQ : (Fintype.card Q : ℝ) ≠ 0 := by positivity
  have hcard : (Fintype.card A : ℝ) = (Nat.card noise.range : ℝ) * Fintype.card Q := by
    have hcount := noise.range.card_mul_index
    rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card (α := A),
      Nat.card_eq_fintype_card (α := Q)] at hcount
    exact_mod_cast hcount.symm
  have href (q : Q × B) : R q = reference q.2 / Fintype.card Q := by
    change (∑ x : A × B, reference x.2 / Fintype.card A * labelKernel project x q) = _
    rcases q with ⟨c, b⟩
    rw [Fintype.sum_prod_type]
    have hfiber (a : A) :
        (∑ y : B, reference y / Fintype.card A * labelKernel project (a, y) (c, b)) =
          if QuotientAddGroup.mk' noise.range a = c then reference b / Fintype.card A else 0 := by
      by_cases h : (QuotientAddGroup.mk a : Q) = c <;>
        simp [labelKernel, project, h, mul_ite]
    simp only [hfiber]
    rw [← Finset.sum_filter, Finset.sum_const, hquotcard, nsmul_eq_mul]
    rw [eq_div_iff hQ]
    calc
      _ = reference b * ((Nat.card noise.range : ℝ) * Fintype.card Q) / Fintype.card A := by
        ring
      _ = reference b := by rw [← hcard, mul_div_cancel_right₀ _ hA]
  refine ⟨hjoint, href, ?_⟩
  symm
  apply (total_variation_channel_eq_iff_no_sign_mixing μ ν (labelKernel project) ?_).mpr
  · intro q
    by_cases hnegative : ∃ x, μ x < ν x ∧ project x = q
    · right
      obtain ⟨x, hx, hproj⟩ := hnegative
      intro y hy
      have hne : project y ≠ q := by
        intro he
        have hxy := hproj.trans he.symm
        have hμ := hconstant x y hxy
        have hν : ν x = ν y := by
          change reference x.2 / Fintype.card A = reference y.2 / Fintype.card A
          rw [show x.2 = y.2 from congrArg (fun q : Q × B => q.2) hxy]
        rw [← hν, ← hμ] at hy
        exact (not_lt_of_gt hx) hy
      simp [labelKernel, hne]
    · left
      intro x hx
      have hne : project x ≠ q := fun h => hnegative ⟨x, hx, h⟩
      simp [labelKernel, hne]
  · constructor
    · intro x q
      simp [labelKernel, ite_nonneg]
    · intro x
      unfold labelKernel
      rw [Finset.sum_eq_single (project x)]
      · simp
      · intro q _ hq
        simp [Ne.symm hq]
      · simp

end D5.S3.TotalVariation.ParityCosetReduction
