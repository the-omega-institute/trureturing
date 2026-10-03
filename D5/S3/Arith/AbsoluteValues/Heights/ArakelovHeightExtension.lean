/- GID: D5/S3/Arith/AbsoluteValues/Heights/ArakelovHeightExtension
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/ArakelovHeightExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arakelov tuple height over a finite extension is the base-field height raised to the extension degree. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Source: rwst/Subspace-Theorems, ArithmeticHeights/Extension.lean, bfd830f481b296989fa5f0c1e48d9316f72270d8.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.RowEntryHeight
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

public section

namespace NumberField

open Finset Function Height InfinitePlace Module

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {κ : Type*} [Fintype κ]

set_option maxHeartbeats 2000000 in
/-- The Arakelov height of a tuple over an extension is the base-field height
raised to the extension degree. -/
theorem arakelovMulHeight_pow_finrank (x : κ → K) :
    arakelovMulHeight x ^ Module.finrank K L =
      arakelovMulHeight (algebraMap K L ∘ x) := by
  have nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  have nativeSource12L := (open Finset Function Height Real in (fun {ι : Type _} [instSource4 : Fintype ι] (x : ι → L) {c : L} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace L, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace L, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace L, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace L, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace L) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace L) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace L) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  have nativeSource73 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} [instSource1 : Field K] [instSource3 : NumberField K] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∃ (d : K) (y : ι → 𝓞 K), d ≠ 0 ∧ ∀ i, (y i : K) = d * x i from by
    classical
    letI : FaithfulSMul (𝓞 K) K :=
      (faithfulSMul_iff_algebraMap_injective (𝓞 K) K).2
        (IsFractionRing.injective (𝓞 K) K)
    have := Fintype.ofFinite ι
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
      (Finset.univ : Finset ι) x
    refine ⟨Algebra.algebraMap (𝓞 K) K (b : 𝓞 K), fun i ↦ (hb i (Finset.mem_univ i)).choose, ?_, fun i ↦ ?_⟩
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr
        (nonZeroDivisors.coe_ne_zero b)
    · have h := (hb i (Finset.mem_univ i)).choose_spec
      rw [show (((hb i (Finset.mem_univ i)).choose : 𝓞 K) : K)
        = Algebra.algebraMap (𝓞 K) K (hb i (Finset.mem_univ i)).choose from rfl, h, Algebra.smul_def])))
  have nativeSource74 := (open Finset Function Height InfinitePlace Module in (fun {y : κ → 𝓞 K} (hy : y ≠ 0) => (show ∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)) =
        (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (y i : K)) ^ Module.finrank K L from by
    classical
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
    have hy' : (fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
    have hspan : Ideal.span (Set.range fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)) =
        (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    have hK := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy
    have hL := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy'
    rw [hspan, ← Ideal.absNorm_relNorm (𝓞 K), Ideal.relNorm_algebraMap, map_pow,
      ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hL
    have hcoe (a : 𝓞 K) :
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) := by
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    simp_rw [hcoe] at hL
    have hN : ((Ideal.span (Set.range y)).absNorm : ℝ) ≠ 0 := by
      have : Ideal.span (Set.range y) ≠ ⊥ := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
        exact fun h ↦ hi (by simpa using (Ideal.span_eq_bot.mp h) (y i) ⟨i, rfl⟩)
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr this
    refine mul_left_cancel₀ (pow_ne_zero (Module.finrank K L) hN) ?_
    rw [← mul_pow, hK, one_pow]
    exact_mod_cast hL)))
  have nativeSource75 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun (ψ : K →+* ℂ) => (show #{φ : L →+* ℂ | φ.comp (Algebra.algebraMap K L) = ψ} = Module.finrank K L from by
    classical
    letI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
    letI : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
    letI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
    let : Algebra K ℂ := ψ.toAlgebra
    rw [← AlgHom.card K L ℂ]
    refine (Finset.card_nbij AlgHom.toRingHom (fun σ _ ↦ ?_) (fun σ _ τ _ h => AlgHom.ext fun x => DFunLike.congr_fun h x)
      (fun φ hφ ↦ ?_)).symm
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and]
      ext r
      simp [RingHom.algebraMap_toAlgebra]
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hφ
      exact ⟨⟨φ, fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← hφ]⟩, mem_univ _, rfl⟩))))
  have nativeSource76 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun (F : (K →+* ℂ) → ℝ) => (show ∏ φ : L →+* ℂ, F (φ.comp (algebraMap K L)) = (∏ ψ : K →+* ℂ, F ψ) ^ Module.finrank K L from by
    classical
    rw [← Finset.prod_fiberwise Finset.univ (fun φ : L →+* ℂ ↦ φ.comp (algebraMap K L))
      (fun φ ↦ F (φ.comp (algebraMap K L))), ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun ψ _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, nativeSource75]))))
  have nativeSource77K (f : NumberField.InfinitePlace K → ℝ) :
      ∏ φ : K →+* ℂ, f (NumberField.InfinitePlace.mk φ) =
        ∏ w : NumberField.InfinitePlace K, f w ^ w.mult := by
    classical
    rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk (fun φ ↦ f (NumberField.InfinitePlace.mk φ))]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq]
  have nativeSource77L (f : NumberField.InfinitePlace L → ℝ) :
      ∏ φ : L →+* ℂ, f (NumberField.InfinitePlace.mk φ) =
        ∏ w : NumberField.InfinitePlace L, f w ^ w.mult := by
    classical
    rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk (fun φ ↦ f (NumberField.InfinitePlace.mk φ))]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq]
  have nativeSource78 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun (f : NumberField.InfinitePlace K → ℝ) (g : NumberField.InfinitePlace L → ℝ)
      (h : ∀ φ : L →+* ℂ, g (NumberField.InfinitePlace.mk φ) = f (NumberField.InfinitePlace.mk (φ.comp (Algebra.algebraMap K L)))) => (show ∏ w : NumberField.InfinitePlace L, g w ^ w.mult = (∏ v : NumberField.InfinitePlace K, f v ^ v.mult) ^ Module.finrank K L from by
    classical
    rw [← nativeSource77L g, ← nativeSource77K f,
      ← nativeSource76 (fun ψ ↦ f (NumberField.InfinitePlace.mk ψ))]
    exact Finset.prod_congr rfl fun φ _ ↦ h φ))))
  have nativeSource106 := (open Finset Function Height InfinitePlace Module in (fun (x : κ → K) => (show ∏ w : NumberField.InfinitePlace L, (∑ i, w (algebraMap K L (x i)) ^ 2) ^ ((w.mult : ℝ) / 2) =
        (∏ v : NumberField.InfinitePlace K, (∑ i, v (x i) ^ 2) ^ ((v.mult : ℝ) / 2)) ^ Module.finrank K L from by
    classical
    have key := nativeSource78
      (fun v ↦ Real.sqrt (∑ i, v (x i) ^ 2))
      (fun w ↦ Real.sqrt (∑ i, w (algebraMap K L (x i)) ^ 2))
      (fun φ ↦ congrArg Real.sqrt
        (Finset.sum_congr rfl fun i _ ↦ by simp [InfinitePlace.apply]))
    calc ∏ w : NumberField.InfinitePlace L, (∑ i, w (algebraMap K L (x i)) ^ 2) ^ ((w.mult : ℝ) / 2)
        = ∏ w : NumberField.InfinitePlace L, Real.sqrt (∑ i, w (algebraMap K L (x i)) ^ 2) ^ w.mult :=
          Finset.prod_congr rfl fun w _ ↦ by
            rw [Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast]
      _ = (∏ v : NumberField.InfinitePlace K, Real.sqrt (∑ i, v (x i) ^ 2) ^ v.mult) ^ Module.finrank K L := key
      _ = _ := by
          congr 1
          exact Finset.prod_congr rfl fun v _ ↦ by
            rw [Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast])))
  have nativeSource107 := (open Finset Function Height InfinitePlace Module in (fun (y : κ → 𝓞 K) => (show NumberField.arakelovMulHeight (fun i ↦ (y i : K)) ^ Module.finrank K L
        = NumberField.arakelovMulHeight (fun i ↦ algebraMap K L (y i : K)) from by
    classical
    letI : FaithfulSMul (𝓞 K) K :=
      (faithfulSMul_iff_algebraMap_injective (𝓞 K) K).2
        (IsFractionRing.injective (𝓞 K) K)
    letI : FaithfulSMul K L :=
      (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
    rcases eq_or_ne y 0 with rfl | hy
    · have hK : (fun _ : κ ↦ ((0 : 𝓞 K) : K)) = 0 := by
        funext i
        simp
      have hL : (fun _ : κ ↦ algebraMap K L ((0 : 𝓞 K) : K)) = 0 := by
        funext i
        simp
      simp only [Pi.zero_apply]
      rw [hK, hL]
      simp [NumberField.arakelovMulHeight]
    have hz : (fun i ↦ (y i : K)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact Function.ne_iff.mpr ⟨i, by simpa using hi⟩
    have hz' : (fun i ↦ algebraMap K L (y i : K)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
      exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (FaithfulSMul.algebraMap_injective K L
        (by simpa using h))⟩
    rw [NumberField.arakelovMulHeight, if_neg hz, NumberField.arakelovMulHeight, if_neg hz', mul_pow,
      nativeSource106, nativeSource74 hy])))
  have nativeSource108 := (open Finset Function Height InfinitePlace Module in (fun (x : κ → K) => (show NumberField.arakelovMulHeight x ^ Module.finrank K L = NumberField.arakelovMulHeight (algebraMap K L ∘ x) from by
    classical
    letI : FaithfulSMul K L :=
      (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
    obtain ⟨d, y, hd, hy⟩ := nativeSource73 (K := K) x
    have hd' : algebraMap K L d ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr hd
    have h1 : (fun i ↦ (y i : K)) = d • x := funext fun i ↦ by rw [hy i]; rfl
    have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
      funext i
      simp [hy i]
    have e1 : NumberField.arakelovMulHeight (fun i ↦ (y i : K)) = NumberField.arakelovMulHeight x :=
      h1 ▸ nativeSource12 x hd
    have e2 : NumberField.arakelovMulHeight (fun i ↦ algebraMap K L (y i : K))
        = NumberField.arakelovMulHeight (algebraMap K L ∘ x) := by
      rw [h2]
      exact nativeSource12L (algebraMap K L ∘ x) (c := algebraMap K L d) hd'
    rw [← e1, ← e2]
    exact nativeSource107 y)))
  exact nativeSource108 x

end NumberField

end
