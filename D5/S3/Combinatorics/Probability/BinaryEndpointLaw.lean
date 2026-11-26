/- GID: D5/S3/Combinatorics/Probability/BinaryEndpointLaw
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/BinaryEndpointLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform binary images of independent endpoint choices and spanning by fair generators. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic.NormNum

/-! The fair endpoint generators determine uniformity of the induced binary law. -/

namespace D5.S3.Combinatorics.Probability.BinaryEndpointLaw

open scoped BigOperators
open Finset

variable {ι V : Type*} [Fintype ι] [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

private def endpoint (a : V) (chosen : Bool) : V := if chosen then a else 0

private def weight (p : ℂ) (chosen : Bool) : ℂ := if chosen then p else 1 - p

open Classical in
/-- The mass of the binary linear combination of independent endpoint choices. -/
noncomputable def mass (a : ι → V) (p : ι → ℂ) (v : V) : ℂ :=
  ∑ x : ι → Bool, if (∑ i, endpoint (a i) (x i)) = v then ∏ i, weight (p i) (x i) else 0

open Classical in
private theorem moment (a : ι → V) (p : ι → ℂ) (χ : AddChar V ℂ) :
    (∑ v, mass a p v * χ v) = ∏ i, ((1 - p i) + p i * χ (a i)) := by
  calc
    (∑ v, mass a p v * χ v) =
        ∑ x : ι → Bool, (∏ i, weight (p i) (x i)) * χ (∑ i, endpoint (a i) (x i)) := by
      simp_rw [mass, sum_mul, ite_mul, zero_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      simp
    _ = ∑ x : ι → Bool, ∏ i, (weight (p i) (x i) * χ (endpoint (a i) (x i))) := by
      apply sum_congr rfl
      intro x _
      rw [prod_mul_distrib]
      congr 1
      change (χ.toAddMonoidHom (∑ i, endpoint (a i) (x i))).toMul =
        ∏ i, (χ.toAddMonoidHom (endpoint (a i) (x i))).toMul
      rw [map_sum, toMul_sum]
    _ = ∏ i, ∑ c : Bool, weight (p i) c * χ (endpoint (a i) c) :=
      (Fintype.prod_sum (fun i (c : Bool) => weight (p i) c * χ (endpoint (a i) c))).symm
    _ = _ := by
      apply prod_congr rfl
      intro i _
      simp [Fintype.univ_bool, weight, endpoint, add_comm]

omit [Fintype V] in
private theorem char_values (χ : AddChar V ℂ) (v : V) : χ v = 1 ∨ χ v = -1 := by
  have hv : (2 : ℕ) • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  have hs : χ v ^ 2 = 1 := by rw [← χ.map_nsmul_eq_pow, hv, χ.map_zero_eq_one]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans (one_pow 2).symm)

omit [Module (ZMod 2) V] in
open Classical in
private theorem eq_of_moments (w w' : V → ℂ)
    (h : ∀ χ : AddChar V ℂ, (∑ v, w v * χ v) = ∑ v, w' v * χ v) : w = w' := by
  let linear (f : V → ℂ) : (V → ℂ) →ₗ[ℂ] ℂ :=
    ∑ v, f v • LinearMap.proj v
  have hlin : linear w = linear w' := by
    apply (AddChar.complexBasis V).ext
    intro χ
    simpa [linear, LinearMap.sum_apply, smul_eq_mul] using h χ
  funext v
  simpa [linear, LinearMap.sum_apply, smul_eq_mul, Pi.single_apply, mul_ite] using
    LinearMap.congr_fun hlin (Pi.single v 1)

open Classical in
/-- Uniformity of the image law is equivalent to spanning by the generators whose
endpoint choices are fair. The identity also holds for complex weights. -/
theorem mass_eq_uniform_iff_span (a : ι → V) (p : ι → ℂ) :
    (mass a p = fun _ => (Fintype.card V : ℂ)⁻¹) ↔
      Submodule.span (ZMod 2) {v | ∃ i, p i = 1 / 2 ∧ a i = v} = ⊤ := by
  let carriers : Set V := {v | ∃ i, p i = 1 / 2 ∧ a i = v}
  change _ ↔ Submodule.span (ZMod 2) carriers = ⊤
  constructor
  · intro hm
    by_contra hspan
    obtain ⟨f, hf, hvanish⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (R := ZMod 2) (lt_top_iff_ne_top.mpr hspan) inferInstance
    let sign : AddChar (ZMod 2) ℂ := AddChar.zmodChar 2 (ζ := (-1 : ℂ)) (by simp)
    let χ := sign.compAddMonoidHom f.toAddMonoidHom
    have hχ : χ ≠ 0 := by
      apply AddChar.ne_zero_iff.mpr
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra! hall
        exact hf (LinearMap.ext hall)
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (f v) with hzero | hone
      · exact False.elim (hv hzero)
      refine ⟨v, ?_⟩
      change sign (f v) ≠ 1
      rw [hone]
      have hval : (1 : ZMod 2).val = 1 := rfl
      norm_num [sign, AddChar.zmodChar_apply, hval]
    have hzero : (∑ v, mass a p v * χ v) = 0 := by
      rw [hm, ← mul_sum, AddChar.sum_eq_zero_iff_ne_zero.mpr hχ, mul_zero]
    rw [moment] at hzero
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hzero
    rcases char_values χ (a i) with hpos | hneg
    · simp [hpos] at hi
    have hb : p i = 1 / 2 := by
      rw [hneg, mul_neg_one, ← sub_eq_add_neg, sub_sub] at hi
      apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
      rw [mul_two, ← sub_eq_zero.mp hi]
    have hmem : f (a i) ∈ (Submodule.span (ZMod 2) carriers).map f :=
      ⟨a i, Submodule.subset_span ⟨i, hb, rfl⟩, rfl⟩
    have hfi : f (a i) = 0 := by
      rw [hvanish] at hmem
      exact (Submodule.mem_bot (ZMod 2)).mp hmem
    have hpos : χ (a i) = 1 := by simp [χ, hfi]
    rw [hpos] at hneg
    norm_num at hneg
  · intro hspan
    apply eq_of_moments
    intro χ
    rw [moment, ← mul_sum]
    by_cases hχ : χ = 0
    · have hcard : (Fintype.card V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      simp [hχ, hcard]
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hχ, mul_zero]
    apply Finset.prod_eq_zero_iff.mpr
    have exists_fair : ∃ i, p i = 1 / 2 ∧ χ (a i) ≠ 1 := by
      by_contra! hfair
      have hker (v : V) (hv : v ∈ Submodule.span (ZMod 2) carriers) : χ v = 1 := by
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨i, hi, rfl⟩ := hv
          exact hfair i hi
        | zero => simp
        | add x y _ _ hx hy => simp [AddChar.map_add_eq_mul, hx, hy]
        | smul c v _ hv =>
          rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
          · simp
          · simpa using hv
      apply hχ
      exact AddChar.eq_zero_iff.mpr fun v => hker v (by rw [hspan]; exact Submodule.mem_top)
    obtain ⟨i, hp, hsign⟩ := exists_fair
    have hn := (char_values χ (a i)).resolve_left hsign
    exact ⟨i, mem_univ _, by norm_num [hp, hn]⟩

end D5.S3.Combinatorics.Probability.BinaryEndpointLaw
