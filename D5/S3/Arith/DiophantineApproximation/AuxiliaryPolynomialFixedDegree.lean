/- GID: D5/S3/Arith/DiophantineApproximation/AuxiliaryPolynomialFixedDegree
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/AuxiliaryPolynomialFixedDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed-degree construction yields an auxiliary polynomial under the power inequality. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module
public import D5.S3.Arith.AbsoluteValues.Heights.BombieriVaalerRelative
public import D5.S3.Arith.DiophantineApproximation.BoxMonomial
public import D5.S3.Arith.DiophantineApproximation.CountingVolume
public import D5.S3.Arith.DiophantineApproximation.PolynomialIndex
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Nat.Choose.Bounds
@[expose] public section
open Finset Height Height.AdmissibleAbsValues MeasureTheory Module MvPolynomial NumberField Real
noncomputable section
namespace MvPolynomial
set_option maxHeartbeats 2000000 in
/-- **Layer 2.6 at a fixed multidegree.** -/
theorem exists_ne_zero_le_index_logHeight_le_of_pow_le
    {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F] [Algebra K F]
    {m N : ℕ} (α : Fin N → Fin m → F) {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {κ : ℝ} (hκ1 : 1 ≤ κ)
    (hκ : ∀ k, (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m ≤ κ)
    (hfeas : (finrank K F : ℝ) * κ * ∑ k, cubeSimplexVolume m (t k) < 1) :
    ∃ P : MvPolynomial (Fin m) K, P ≠ 0 ∧ (∀ j, P.degreeOf j ≤ d j) ∧
      (∀ k, ENNReal.ofReal (t k) ≤ index (fun j ↦ (d j : ℝ)) (α k) (P.map (algebraMap K F))) ∧
      Real.log P.mulHeight / (finrank ℚ K : ℝ)
        ≤ (2 * (finrank ℚ K : ℝ))⁻¹ * Real.log |(NumberField.discr K : ℝ)|
          + (finrank K F : ℝ) * κ
              / (1 - (finrank K F : ℝ) * κ * ∑ k, cubeSimplexVolume m (t k))
            * ((∑ k, cubeSimplexVolume m (t k)
                  * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
              + (∑ k, cubeSimplexVolume m (t k)) / 2
                * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))) := by
  have nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite : (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) : (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) : (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) : (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
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
  have nativeSource13 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · simp [NumberField.arakelovMulHeight]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
    have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
    rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
    refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ ?_)
      (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
    have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 := le_trans (le_of_eq (by simp [hi']))
        (Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (mem_univ i))
    exact Real.one_le_rpow h1 (by positivity))))
  have nativeSource16 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 0 < NumberField.arakelovMulHeight x from by
    classical
    exact zero_lt_one.trans_le (nativeSource13 x))))
  have nativeSource73 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} [instSource1 : Field K] [instSource3 : NumberField K] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∃ (d : K) (y : ι → 𝓞 K), d ≠ 0 ∧ ∀ i, (y i : K) = d * x i from by
    classical
    have := Fintype.ofFinite ι
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
      (Finset.univ : Finset ι) x
    refine ⟨Algebra.algebraMap (𝓞 K) K (b : 𝓞 K), fun i ↦ (hb i (Finset.mem_univ i)).choose, ?_, fun i ↦ ?_⟩
    · exact (map_ne_zero_iff _ (NumberField.RingOfIntegers.coe_injective (K := K))).mpr
        (nonZeroDivisors.coe_ne_zero b)
    · have h := (hb i (Finset.mem_univ i)).choose_spec
      rw [show (((hb i (Finset.mem_univ i)).choose : 𝓞 K) : K)
        = Algebra.algebraMap (𝓞 K) K (hb i (Finset.mem_univ i)).choose from rfl, h, Algebra.smul_def])))
  have nativeSource74 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] {y : ι → 𝓞 K} (hy : y ≠ 0) => (show ∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)) =
        (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (y i : K)) ^ Module.finrank K L from by
    classical
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := NumberField.RingOfIntegers.algebraMap.injective K L
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
    have hcoe (a : 𝓞 K) : ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) := by
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
  have nativeSource75 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] (ψ : K →+* ℂ) => (show #{φ : L →+* ℂ | φ.comp (Algebra.algebraMap K L) = ψ} = Module.finrank K L from by
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
  have nativeSource76 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] (F : (K →+* ℂ) → ℝ) => (show ∏ φ : L →+* ℂ, F (φ.comp (algebraMap K L)) = (∏ ψ : K →+* ℂ, F ψ) ^ Module.finrank K L from by
    classical
    rw [← Finset.prod_fiberwise Finset.univ (fun φ : L →+* ℂ ↦ φ.comp (algebraMap K L))
      (fun φ ↦ F (φ.comp (algebraMap K L))), ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun ψ _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, nativeSource75]))))
  have nativeSource77 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} [instSource1 : Field K] [instSource3 : NumberField K] {M : Type _} [CommMonoid M] (f : NumberField.InfinitePlace K → M) => (show ∏ φ : K →+* ℂ, f (NumberField.InfinitePlace.mk φ) = ∏ w : NumberField.InfinitePlace K, f w ^ w.mult from by
    classical
    rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk (fun φ ↦ f (NumberField.InfinitePlace.mk φ))]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq])))
  have nativeSource78 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] (f : NumberField.InfinitePlace K → ℝ) (g : NumberField.InfinitePlace L → ℝ)
      (h : ∀ φ : L →+* ℂ, g (NumberField.InfinitePlace.mk φ) = f (NumberField.InfinitePlace.mk (φ.comp (Algebra.algebraMap K L)))) => (show ∏ w : NumberField.InfinitePlace L, g w ^ w.mult = (∏ v : NumberField.InfinitePlace K, f v ^ v.mult) ^ Module.finrank K L from by
    classical
    rw [← nativeSource77 (K := L) g, ← nativeSource77 (K := K) f,
      ← nativeSource76 (fun ψ ↦ f (NumberField.InfinitePlace.mk ψ))]
    exact Finset.prod_congr rfl fun φ _ ↦ h φ))))
  have nativeSource79 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∏ w : NumberField.InfinitePlace L, (⨆ i, w (Algebra.algebraMap K L (x i))) ^ w.mult =
        (∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ Module.finrank K L from by
    classical
    exact (nativeSource78 _ _ fun φ ↦ iSup_congr fun i ↦ by simp [InfinitePlace.apply])))))
  have nativeSource80 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (y : ι → 𝓞 K) => (show Height.mulHeight (fun i ↦ (y i : K)) ^ Module.finrank K L = Height.mulHeight (fun i ↦ algebraMap K L (y i : K)) from by
    classical
    letI : FaithfulSMul (𝓞 K) K := (faithfulSMul_iff_algebraMap_injective (𝓞 K) K).2 (IsFractionRing.injective (𝓞 K) K)
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have hz : (fun i ↦ (y i : K)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (NumberField.RingOfIntegers.coe_injective (by simpa using h))⟩
    have hz' : (fun i ↦ algebraMap K L (y i : K)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
      exact Function.ne_iff.mpr ⟨i, fun h ↦ hi ((algebraMap K L).injective (by simpa using h))⟩
    rw [NumberField.mulHeight_eq hz, NumberField.mulHeight_eq hz', mul_pow,
      nativeSource79 (L := L), nativeSource74 hy])))
  have nativeSource81 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show Height.mulHeight x ^ Module.finrank K L = Height.mulHeight (algebraMap K L ∘ x) from by
    classical
    obtain ⟨d, y, hd, hy⟩ := nativeSource73 (K := K) x
    have hd' : algebraMap K L d ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hd
    have h1 : (fun i ↦ (y i : K)) = d • x := funext fun i ↦ by rw [hy i]; rfl
    have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
      funext i
      simp [hy i]
    have e1 : Height.mulHeight (fun i ↦ (y i : K)) = Height.mulHeight x := h1 ▸ Height.mulHeight_smul_eq_mulHeight x hd
    have e2 : Height.mulHeight (fun i ↦ algebraMap K L (y i : K)) = Height.mulHeight (algebraMap K L ∘ x) :=
      h2 ▸ Height.mulHeight_smul_eq_mulHeight _ hd'
    rw [← e1, ← e2]
    exact nativeSource80 y)))
  have nativeSource82 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show NumberField.absMulHeight x = Height.mulHeight x ^ ((finrank ℚ K : ℝ))⁻¹ from by
    classical
    letI : Algebra.IsIntegral ℚ K := Algebra.IsIntegral.of_finite ℚ K
    have hint : ∀ i, IsIntegral ℚ (x i) := fun i ↦ Algebra.IsIntegral.isIntegral _
    haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range (x))) :=
      IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
        obtain ⟨i, rfl⟩ := hy
        exact hint i
    haveI : NumberField (adjoin ℚ (Set.range (x))) := {}
    have : Module.Finite (adjoin ℚ (Set.range x)) K := Module.Finite.of_restrictScalars_finite ℚ _ K
    have hcomp : (Algebra.algebraMap (adjoin ℚ (Set.range x)) K) ∘
        (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x))) = x := rfl
    letI : FaithfulSMul (adjoin ℚ (Set.range x)) K :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (adjoin ℚ (Set.range x)) K).injective
    letI : Module.Free ℚ (adjoin ℚ (Set.range x)) := Module.Free.of_divisionRing _ _
    letI : Module.Free (adjoin ℚ (Set.range x)) K := Module.Free.of_divisionRing _ _
    letI : IsTorsionFree ℚ (adjoin ℚ (Set.range x)) := Module.Free.instIsTorsionFree _ _
    letI : IsTorsionFree (adjoin ℚ (Set.range x)) K := Module.Free.instIsTorsionFree _ _
    rw [NumberField.absMulHeight, dif_pos hint]
    conv_rhs => rw [← hcomp]
    rw [← nativeSource81, ← Module.finrank_mul_finrank ℚ (adjoin ℚ (Set.range x)) K]
    rw [← Real.rpow_natCast (Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))) (finrank (adjoin ℚ (Set.range x)) K), ← Real.rpow_mul ((Height.mulHeight_pos (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))).le)]
    congr 1
    have hm' : ((finrank ℚ (adjoin ℚ (Set.range x))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := adjoin ℚ (Set.range x))).ne'
    have hn' : ((finrank (adjoin ℚ (Set.range x)) K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos (R := adjoin ℚ (Set.range x)) (M := K)).ne'
    push_cast
    field_simp)))
  have nativeSource83 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show NumberField.absLogHeight x = ((Module.finrank ℚ K : ℝ))⁻¹ * Height.logHeight x from by
    classical
    rw [NumberField.absLogHeight, nativeSource82, Real.log_rpow (Height.mulHeight_pos x),
      Height.logHeight_eq_log_mulHeight])))
  have nativeSource84 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] {E : IntermediateField ℚ K} [NumberField E] {x : ι → K}
      (hx : ∀ i, x i ∈ E) => (show NumberField.absMulHeight x = Height.mulHeight (fun i ↦ (⟨x i, hx i⟩ : E)) ^ ((finrank ℚ E : ℝ))⁻¹ from by
    classical
    letI : Algebra.IsIntegral ℚ E := Algebra.IsIntegral.of_finite ℚ E
    have hint : ∀ i, IsIntegral ℚ (x i) := fun i ↦
      (Algebra.IsIntegral.isIntegral (⟨x i, hx i⟩ : E)).map E.val
    have hFE : adjoin ℚ (Set.range x) ≤ E := adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
    haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range (x))) :=
      IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
        obtain ⟨i, rfl⟩ := hy
        exact hint i
    haveI : NumberField (adjoin ℚ (Set.range (x))) := {}
    let : Algebra (adjoin ℚ (Set.range x)) E := (inclusion hFE).toAlgebra
    have : IsScalarTower ℚ (adjoin ℚ (Set.range x)) E := IsScalarTower.of_algebraMap_eq fun r ↦ ((inclusion hFE).commutes r).symm
    have : Module.Finite (adjoin ℚ (Set.range x)) E := Module.Finite.of_restrictScalars_finite ℚ _ E
    have hcomp : (Algebra.algebraMap (adjoin ℚ (Set.range x)) E) ∘
        (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))
        = fun i ↦ (⟨x i, hx i⟩ : E) := rfl
    letI : FaithfulSMul (adjoin ℚ (Set.range x)) E :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (adjoin ℚ (Set.range x)) E).injective
    letI : Module.Free ℚ (adjoin ℚ (Set.range x)) := Module.Free.of_divisionRing _ _
    letI : Module.Free (adjoin ℚ (Set.range x)) E := Module.Free.of_divisionRing _ _
    letI : IsTorsionFree ℚ (adjoin ℚ (Set.range x)) := Module.Free.instIsTorsionFree _ _
    letI : IsTorsionFree (adjoin ℚ (Set.range x)) E := Module.Free.instIsTorsionFree _ _
    rw [NumberField.absMulHeight, dif_pos hint, ← hcomp, ← nativeSource81, ← Module.finrank_mul_finrank ℚ (adjoin ℚ (Set.range x)) E]
    rw [← Real.rpow_natCast (Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))) (finrank (adjoin ℚ (Set.range x)) E), ← Real.rpow_mul ((Height.mulHeight_pos (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))).le)]
    congr 1
    have hm' : ((finrank ℚ (adjoin ℚ (Set.range x))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := adjoin ℚ (Set.range x))).ne'
    have hn' : ((finrank (adjoin ℚ (Set.range x)) E) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos (R := adjoin ℚ (Set.range x)) (M := E)).ne'
    push_cast
    field_simp)))
  have nativeSource85 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show NumberField.absMulHeight ![x, 1] = NumberField.absMulHeight₁ x from by
    classical
    by_cases hx : IsIntegral ℚ x
    · have : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
      have : NumberField ℚ⟮x⟯ := {}
      have hmem : ∀ i, (![x, 1] : Fin 2 → K) i ∈ ℚ⟮x⟯ := by
        intro i
        fin_cases i
        · exact IntermediateField.mem_adjoin_simple_self ℚ x
        · exact OneMemClass.one_mem _
      have heq : (fun i ↦ (⟨(![x, 1] : Fin 2 → K) i, hmem i⟩ : ℚ⟮x⟯)) = ![IntermediateField.AdjoinSimple.gen ℚ x, 1] := by
        funext i
        fin_cases i <;> exact Subtype.ext rfl
      rw [nativeSource84 hmem, heq, NumberField.absMulHeight₁, dif_pos hx,
        Height.mulHeight₁_eq_mulHeight]
    · have hne : ¬ ∀ i, IsIntegral ℚ ((![x, 1] : Fin 2 → K) i) := fun h ↦ hx (by simpa using h 0)
      rw [NumberField.absMulHeight, dif_neg hne, NumberField.absMulHeight₁,
        dif_neg hx]))))
  have nativeSource86 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show NumberField.absLogHeight ![x, 1] = NumberField.absLogHeight₁ x from by
    classical
    exact (congrArg Real.log (nativeSource85 x))))))
  have nativeSource88 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 1 ≤ NumberField.absMulHeight x from by
    classical
    by_cases hx : ∀ i, IsIntegral ℚ (x i)
    · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range (x))) :=
        IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
          obtain ⟨i, rfl⟩ := hy
          exact hx i
      haveI : NumberField (IntermediateField.adjoin ℚ (Set.range (x))) := {}
      rw [NumberField.absMulHeight, dif_pos hx]
      exact Real.one_le_rpow (Height.one_le_mulHeight _) (by positivity)
    · rw [NumberField.absMulHeight, dif_neg hx])))
  have nativeSource90 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show 1 ≤ NumberField.absMulHeight₁ x from by
    classical
    exact (nativeSource85 x ▸ nativeSource88 ![x, 1])))))
  have nativeSource91 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show 0 ≤ NumberField.absLogHeight₁ x from by
    classical
    exact (Real.log_nonneg (nativeSource90 x))))))
  have nativeSource93 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 0 < NumberField.absMulHeight x from by
    classical
    exact (zero_lt_one.trans_le <| nativeSource88 x))))
  have nativeSource102 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (v : NumberField.InfinitePlace K) (x : ι → K) => (show ∑ i, v (x i) ^ 2 ≤ (Fintype.card ι : ℝ) * (⨆ i, v (x i)) ^ 2 from by
    classical
    rcases isEmpty_or_nonempty ι with _ | _
    · simp
    rw [← Finset.card_univ, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
    gcongr
    exact Finite.le_ciSup_of_le i le_rfl)))
  have nativeSource103 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (v : NumberField.InfinitePlace K) (x : ι → K) => (show (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) ≤
        ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) ^ v.mult * (⨆ i, v (x i)) ^ v.mult from by
    classical
    have h0 : (0 : ℝ) ≤ ⨆ i, v (x i) := Real.iSup_nonneg fun i ↦ apply_nonneg v (x i)
    have hPower : ((⨆ i, v (x i)) ^ 2) ^ ((v.mult : ℝ) / 2) = (⨆ i, v (x i)) ^ v.mult := by
      rw [← Real.rpow_natCast (⨆ i, v (x i)) v.mult,
        ← Real.rpow_natCast (⨆ i, v (x i)) 2, ← Real.rpow_mul h0]
      congr 1
      push_cast
      ring
    have hc : ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) ^ v.mult = (Fintype.card ι : ℝ) ^ (v.mult / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) v.mult,
        ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    calc (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)
        ≤ ((Fintype.card ι : ℝ) * (⨆ i, v (x i)) ^ 2) ^ (v.mult / 2 : ℝ) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦ by positivity) (nativeSource102 v x)
            (by positivity)
      _ = (Fintype.card ι : ℝ) ^ (v.mult / 2 : ℝ) * ((⨆ i, v (x i)) ^ 2) ^ (v.mult / 2 : ℝ) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) ^ v.mult * (⨆ i, v (x i)) ^ v.mult := by
          rw [hc, hPower])))
  have nativeSource104 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show ∏ v : NumberField.InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) ≤
        (Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2) *
          ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult from by
    classical
    calc ∏ v : NumberField.InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)
        ≤ ∏ v : NumberField.InfinitePlace K,
            ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) ^ v.mult * (⨆ i, v (x i)) ^ v.mult :=
          Finset.prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ nativeSource103 v x
      _ = (∏ v : NumberField.InfinitePlace K, ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) ^ v.mult) *
            ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := Finset.prod_mul_distrib
      _ = (Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2) *
            ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
          congr 1
          rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq,
            ← Real.rpow_natCast ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) (Module.finrank ℚ K),
            ← Real.rpow_mul (by positivity), NumberField.totalWeight_eq_finrank]
          congr 1
          ring)))
  have nativeSource105 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] [Nonempty ι] (x : ι → K) => (show NumberField.arakelovMulHeight x ≤
        (Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2) * Height.mulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [(show NumberField.arakelovMulHeight (0 : ι → K) = 1 from by
        simp [NumberField.arakelovMulHeight]), Height.mulHeight_zero, mul_one]
      exact Real.one_le_rpow (by exact_mod_cast Fintype.card_pos) (by positivity)
    rw [NumberField.mulHeight_eq hx, NumberField.arakelovMulHeight, if_neg hx, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (nativeSource104 x) (finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg v (x i)))))
  have hasseDeriv_apply (μ : Fin m →₀ ℕ) (P : MvPolynomial (Fin m) F) : MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials (Fin m) F).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  classical
  have hst : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hFin : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hrpos : 0 < finrank K F := Module.finrank_pos
  have hr1 : (1 : ℝ) ≤ (finrank K F : ℝ) := by exact_mod_cast hrpos
  set rr : ℝ := (finrank K F : ℝ) with hrrdef
  set S : ℝ := ∑ k, cubeSimplexVolume m (t k) with hSdef
  set G : ℝ := ∑ k, cubeSimplexVolume m (t k)
    * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ) with hGdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ (fun m t ↦ (show 0 ≤ MeasureTheory.cubeSimplexVolume m t from ENNReal.toReal_nonneg)) m (t k)
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ1
  have hb0 : 0 < 1 - rr * κ * S := by linarith
  have hProd0 : (0 : ℝ) ≤ ∏ j, (d j : ℝ) := Finset.prod_nonneg fun j _ ↦ Nat.cast_nonneg _
  have hB0 : ∀ k, 0 ≤ ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ) := fun k ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg
      (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
          have := nativeSource91 (α k j)
          linarith) (Nat.cast_nonneg _)
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun k _ ↦ mul_nonneg ((fun m t ↦ (show 0 ≤ MeasureTheory.cubeSimplexVolume m t from ENNReal.toReal_nonneg)) m (t k)) (hB0 k)
  have hne : Nonempty (∀ j : Fin m, Fin (d j + 1)) := ⟨fun j ↦ 0⟩
  set MM : ℕ := Fintype.card (∀ j : Fin m, Fin (d j + 1)) with hMMdef
  have hMpos : 0 < MM := Fintype.card_pos
  have hM0 : (0 : ℝ) < (MM : ℝ) := by exact_mod_cast hMpos
  have hM1 : (1 : ℝ) ≤ (MM : ℝ) := by exact_mod_cast hMpos
  have hlm0 : 0 ≤ Real.log (MM : ℝ) := Real.log_nonneg hM1
  have hMprod : (MM : ℝ) = ∏ j, ((d j : ℝ) + 1) := by
    rw [hMMdef, Fintype.card_pi]
    push_cast
    simp
  have hProdM : ∏ j, (d j : ℝ) ≤ (MM : ℝ) := by
    rw [hMprod]
    exact Finset.prod_le_prod₀ (fun j _ ↦ Nat.cast_nonneg _)
      fun j _ ↦ le_add_of_nonneg_right zero_le_one
  obtain ⟨n, e⟩ : Σ' n : ℕ, Fin n ≃ (Σ k : Fin N, {I : ∀ j, Fin (d j + 1) //
      ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k}) := ⟨_, (Fintype.equivFin _).symm⟩
  have hncard : n = Fintype.card (Σ k : Fin N, {I : ∀ j, Fin (d j + 1) //
      ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : Type _) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hcardk : ∀ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
        ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ)
      ≤ cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ)) := by
    intro k
    have h1 : (Fintype.card {I : ∀ j, Fin (d j + 1) //
        ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ) ≤ ((latticePoints d (t k)).card : ℝ) := by
      have hcardbox : Fintype.card
          {I : ∀ j, Fin (d j + 1) // ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k}
            ≤ (latticePoints d (t k)).card := by
        classical
        rw [← Finset.card_univ]
        refine Finset.card_le_card_of_injOn (fun I ↦ fun j ↦ ((I : ∀ j, Fin (d j + 1)) j : ℕ))
          (fun I _ ↦ (show (fun j ↦ (I.1 j : ℕ)) ∈ MeasureTheory.latticePoints d (t k) ↔
              (∀ j, (I.1 j : ℕ) ≤ d j) ∧
                ∑ j, ((I.1 j : ℕ) : ℝ) / (d j : ℝ) ≤ t k from by
              simp [MeasureTheory.latticePoints]).mpr ⟨fun j ↦ Nat.lt_succ_iff.mp (I.1 j).isLt, I.2.le⟩)
          fun I _ J _ h ↦ Subtype.ext (funext fun j ↦ Fin.ext (congrFun h j))
      exact_mod_cast hcardbox
    refine h1.trans ((card_latticePoints_le hd (ht k)).trans ?_)
    have hk := hκ k
    have hV := (fun m t ↦ (show 0 ≤ MeasureTheory.cubeSimplexVolume m t from ENNReal.toReal_nonneg)) m (t k)
    calc cubeSimplexVolume m (t k) * (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m
          * ∏ j, (d j : ℝ)
        ≤ cubeSimplexVolume m (t k) * κ * ∏ j, (d j : ℝ) := by gcongr
      _ = cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ)) := by ring
  have hcount : (n : ℝ) ≤ κ * S * ∏ j, (d j : ℝ) := by
    have h1 : (n : ℝ) = ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
        ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ) := by
      rw [hncard, Fintype.card_sigma]
      push_cast
      ring
    calc (n : ℝ) = ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
            ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ) := h1
      _ ≤ ∑ k, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ)) :=
          Finset.sum_le_sum fun k _ ↦ hcardk k
      _ = S * (κ * ∏ j, (d j : ℝ)) := by rw [hSdef, ← Finset.sum_mul]
      _ = κ * S * ∏ j, (d j : ℝ) := by ring
  let _ : LinearOrder (∀ j : Fin m, Fin (d j + 1)) := linearOrderOfSTO WellOrderingRel
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (∀ j : Fin m, Fin (d j + 1)) F,
      A = fun i ↦ hasseDerivRow d (α (e i).1) (boxMonomial d (e i).2.1) := ⟨_, rfl⟩
  have hrankn : (A.rank : ℝ) ≤ (n : ℝ) := by
    have h : A.rank ≤ n := by simpa using A.rank_le_card_height
    exact_mod_cast h
  have hrr0 : (0 : ℝ) ≤ rr := by linarith only [hr1]
  have hrκS0 : (0 : ℝ) ≤ rr * κ * S := mul_nonneg (mul_nonneg hrr0 hκ0.le) hS0
  have hrankM : rr * (A.rank : ℝ) ≤ rr * κ * S * (MM : ℝ) := by
    have h2 : rr * (A.rank : ℝ) ≤ rr * (κ * S * ∏ j, (d j : ℝ)) := mul_le_mul_of_nonneg_left (hrankn.trans hcount) hrr0
    have h3 : rr * (κ * S * ∏ j, (d j : ℝ)) ≤ rr * κ * S * (MM : ℝ) := by
      rw [show rr * (κ * S * ∏ j, (d j : ℝ)) = rr * κ * S * ∏ j, (d j : ℝ) by ring]
      exact mul_le_mul_of_nonneg_left hProdM hrκS0
    linarith only [h2, h3]
  have hfeas' : finrank K F * A.rank < MM := by
    have h1 : ((finrank K F * A.rank : ℕ) : ℝ) = rr * (A.rank : ℝ) := by
      rw [hrrdef]; push_cast; ring
    have h4 : rr * κ * S * (MM : ℝ) < (MM : ℝ) := by
      calc rr * κ * S * (MM : ℝ) < 1 * (MM : ℝ) := by
            refine mul_lt_mul_of_pos_right ?_ hM0
            rw [hrrdef]; exact hfeas
        _ = (MM : ℝ) := one_mul _
    have h5 : ((finrank K F * A.rank : ℕ) : ℝ) < ((MM : ℕ) : ℝ) := by
      rw [h1]; linarith only [hrankM, h4]
    exact_mod_cast h5
  have hfeasRank : finrank K F * A.rank <
      Fintype.card (∀ j : Fin m, Fin (d j + 1)) := by
    rw [← hMMdef]
    exact hfeas'
  let k' := Fintype.card (∀ j : Fin m, Fin (d j + 1)) - finrank K F * A.rank
  have hk'0 : 0 < k' := by dsimp [k']; omega
  let V := LinearMap.ker (Matrix.mulVecRestrict (K := K) A)
  let k := finrank K V
  have hk'k : k' ≤ k := by
    have hnull := LinearMap.finrank_range_add_finrank_ker
      (Matrix.mulVecRestrict (K := K) A)
    rw [Module.finrank_fintype_fun_eq_card] at hnull
    have hrange := Matrix.finrank_range_mulVecRestrict_le (K := K) A
    change Fintype.card (∀ j : Fin m, Fin (d j + 1)) - finrank K F * A.rank
      ≤ finrank K (LinearMap.ker (Matrix.mulVecRestrict (K := K) A))
    omega
  have hk0 : 0 < k := lt_of_lt_of_le hk'0 hk'k
  have hBasis : ∃ b : Basis (Fin k) K ↥(LinearMap.ker (Matrix.mulVecRestrict (K := K) A)),
      (∀ l j, IsIntegral ℤ ((b l : (∀ j : Fin m, Fin (d j + 1)) → K) j)) ∧
      (∏ l, NumberField.absMulHeight fun j ↦ (b l : (∀ j : Fin m, Fin (d j + 1)) → K) j) ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
          ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F := by
    have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
    set e := Module.finBasis K F with hedef
    have hker : LinearMap.ker (Matrix.restrictScalars e A).mulVecLin = LinearMap.ker (Matrix.mulVecRestrict (K := K) A) := by
      have hmul (x : (∀ j : Fin m, Fin (d j + 1)) → K) : (Matrix.restrictScalars e A).mulVec x = fun p ↦ e.repr (A.mulVec (fun j ↦ algebraMap K F (x j)) p.1) p.2 := by
        funext q
        have h : A.mulVec (fun j ↦ algebraMap K F (x j)) q.1 = ∑ j, x j • A q.1 j := by simp only [Matrix.mulVec, dotProduct]; exact Finset.sum_congr rfl fun j _ ↦ by rw [Algebra.smul_def, mul_comm]
        rw [h, map_sum]; simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.restrictScalars, Matrix.of_apply]
        exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
      ext x
      have hcast : ((Algebra.linearMap K F).compLeft _) x = (fun j ↦ algebraMap K F (x j)) := by funext j; rw [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecRestrict, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hmul x]
      rw [hcast]; constructor
      · intro h; funext i; refine (map_eq_zero_iff e.repr e.repr.injective).1 ?_; ext t; simpa using congrFun h (i, t)
      · intro h; funext p; rw [h]; simp
    have hk : finrank K (LinearMap.ker (Matrix.mulVecRestrict (K := K) A)) = k := rfl
    rw [← hker] at hk ⊢
    obtain ⟨b, hint, hle⟩ := NumberField.exists_basis_ker_prod_absMulHeight_le
      (Matrix.restrictScalars e A) hk
    have hpi1 : (2 / π : ℝ) ^ ((k * NumberField.InfinitePlace.nrComplexPlaces K : ℝ) /
        finrank ℚ K) ≤ 1 := by
      refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      rw [div_le_one Real.pi_pos]
      linarith [Real.pi_gt_three]
    have hspan0 : (0 : ℝ) ≤
        (Submodule.span K (Set.range (Matrix.restrictScalars e A).row)).arakelovMulHeight := by
      change 0 ≤ Projectivization.projectiveArakelovMulHeight
        ((Submodule.span K (Set.range (Matrix.restrictScalars e A).row)).pluckerPoint rfl)
      positivity
    have hpos : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
        (Submodule.span K (Set.range (Matrix.restrictScalars e A).row)).arakelovMulHeight ^
          (finrank ℚ K : ℝ)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hspan0 _)
    have hle' : (∏ l, NumberField.absMulHeight
        (fun j ↦ (b l : (∀ j : Fin m, Fin (d j + 1)) → K) j)) ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
          (Submodule.span K (Set.range (Matrix.restrictScalars e A).row)).arakelovMulHeight ^
            (finrank ℚ K : ℝ)⁻¹ := by
      apply hle.trans
      rw [mul_assoc]
      exact mul_le_of_le_one_left hpos hpi1
    exact ⟨b, hint, hle'.trans (mul_le_mul_of_nonneg_left
      (Matrix.arakelovMulHeight_span_restrictScalars_rpow_le' e A)
      (Real.rpow_nonneg (abs_nonneg _) _))⟩
  obtain ⟨b, hint, hle⟩ := hBasis
  let g : Fin k → ℝ := fun l ↦ NumberField.absMulHeight fun j ↦ (b l : (∀ j : Fin m, Fin (d j + 1)) → K) j
  have hg : ∀ l, 1 ≤ g l := by
    intro l
    let z : (∀ j : Fin m, Fin (d j + 1)) → K := b l
    change 1 ≤ NumberField.absMulHeight z
    by_cases hz : ∀ j, IsIntegral ℚ (z j)
    · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range z)) := IntermediateField.finiteDimensional_adjoin (by rintro y ⟨j, rfl⟩; exact hz j)
      haveI : NumberField (IntermediateField.adjoin ℚ (Set.range z)) := {}
      rw [NumberField.absMulHeight, dif_pos hz]; exact Real.one_le_rpow (Height.one_le_mulHeight _) (by positivity)
    · rw [NumberField.absMulHeight, dif_neg hz]
  obtain ⟨f, hfinj, hfle⟩ := Real.exists_injective_prod_pow_le g hg hk'k
  let Pheight : ℝ := ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F
  let Dk : ℝ := |(NumberField.discr K : ℝ)|
  have hDk0 : 0 ≤ Dk := abs_nonneg _
  have hP1 : 1 ≤ Pheight := Finset.one_le_prod₀ fun i _ ↦ one_le_pow₀
      (Real.one_le_rpow (nativeSource13 _) (by positivity))
  let Qheight : ℝ := Dk ^ ((k : ℝ) / (2 * finrank ℚ K)) * Pheight
  have hQ0 : 0 ≤ Qheight := by positivity
  let T : ℝ := ∏ l, g (f l)
  have hT0 : 0 ≤ T := Finset.prod_nonneg fun l _ ↦ le_trans zero_le_one (hg _)
  have hstep : T ^ k ≤ Qheight ^ k' := hfle.trans (pow_le_pow_left₀
      (Finset.prod_nonneg fun l _ ↦ le_trans zero_le_one (hg l)) hle k')
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hTle : T ≤ Qheight ^ ((k' : ℝ) / k) := by
    have h := Real.rpow_le_rpow (by positivity) hstep
      (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast hT0 hk0.ne'] at h
    refine h.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast Qheight k', ← Real.rpow_mul hQ0, div_eq_mul_inv]
  have hDpow : (Dk ^ ((k : ℝ) / (2 * finrank ℚ K))) ^ ((k' : ℝ) / k) =
      Dk ^ ((k' : ℝ) / (2 * finrank ℚ K)) := by
    rw [← Real.rpow_mul hDk0]
    congr 1
    field_simp
  have hPpow : Pheight ^ ((k' : ℝ) / k) ≤ Pheight := by
    calc Pheight ^ ((k' : ℝ) / k) ≤ Pheight ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hP1
            (by rw [div_le_one (by positivity)]; exact_mod_cast hk'k)
      _ = Pheight := Real.rpow_one Pheight
  have hTfinal : T ≤ Dk ^ ((k' : ℝ) / (2 * finrank ℚ K)) * Pheight := by
    refine hTle.trans ?_
    rw [show Qheight ^ ((k' : ℝ) / k) =
      (Dk ^ ((k : ℝ) / (2 * finrank ℚ K))) ^ ((k' : ℝ) / k) *
        Pheight ^ ((k' : ℝ) / k) from
      Real.mul_rpow (Real.rpow_nonneg hDk0 _) (by linarith), hDpow]
    exact mul_le_mul_of_nonneg_left hPpow (Real.rpow_nonneg hDk0 _)
  have : Nonempty (Fin k') := Fin.pos_iff_nonempty.1 hk'0
  obtain ⟨l₀, hl₀⟩ := Finite.exists_min fun l : Fin k' ↦ g (f l)
  let H : ℝ := g (f l₀)
  have hH1 : 1 ≤ H := hg _
  have hpow : H ^ k' ≤ Dk ^ ((k' : ℝ) / (2 * finrank ℚ K)) * Pheight := by
    refine le_trans ?_ hTfinal
    calc H ^ k' = ∏ _l : Fin k', H := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ T := Finset.prod_le_prod₀ (fun l _ ↦ by positivity) fun l _ ↦ hl₀ l
  have hfinal : H ≤ Dk ^ (2 * finrank ℚ K : ℝ)⁻¹ * Pheight ^ ((k' : ℝ))⁻¹ := by
    have h := Real.rpow_le_rpow (by positivity) hpow
      (by positivity : (0 : ℝ) ≤ (k' : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by linarith) hk'0.ne'] at h
    refine h.trans (le_of_eq ?_)
    rw [Real.mul_rpow (Real.rpow_nonneg hDk0 _) (by linarith),
      ← Real.rpow_mul hDk0]
    congr 2
    have hk'ne : (k' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk'0.ne'
    field_simp
  obtain ⟨x, hx0, hxker, hxint, hxpos, hxle⟩ :=
    (show ∃ x : (∀ j : Fin m, Fin (d j + 1)) → K, x ≠ 0 ∧
      A.mulVec (fun j ↦ algebraMap K F (x j)) = 0 ∧
      (∀ j, IsIntegral ℤ (x j)) ∧ 1 ≤ NumberField.absMulHeight x ∧
      NumberField.absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          Pheight ^ ((k' : ℝ))⁻¹ from by
      refine ⟨fun j ↦ (b (f l₀) : (∀ j : Fin m, Fin (d j + 1)) → K) j,
        ?_, ?_, fun j ↦ hint (f l₀) j, hH1, hfinal⟩
      · intro h
        exact (b.linearIndependent.ne_zero (f l₀)) (Subtype.ext h)
      · let z : (∀ j : Fin m, Fin (d j + 1)) → K := b (f l₀)
        have hz : Matrix.mulVecRestrict (K := K) A z = 0 := LinearMap.mem_ker.mp (b (f l₀)).property
        have hlin : A.mulVec (((Algebra.linearMap K F).compLeft _) z) = 0 := by
          simpa only [Matrix.mulVecRestrict, LinearMap.comp_apply,
            LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] using hz
        have hcast : ((Algebra.linearMap K F).compLeft _) z =
            (fun j ↦ algebraMap K F (z j)) := by
          funext j
          rw [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
        rw [hcast] at hlin
        exact hlin)
  obtain ⟨P, hPdef⟩ : ∃ P : MvPolynomial (Fin m) K, P = ofBox d x := ⟨_, rfl⟩
  have hBoxInjective : Function.Injective (boxMonomial d) := by
    intro I J h
    funext j
    exact Fin.ext (by
      simpa only [boxMonomial, Finsupp.coe_equivFunOnFinite_symm] using
        congrFun (congrArg (⇑) h) j)
  have hOfBoxApply (z : (∀ j, Fin (d j + 1)) → K) : ofBox d z = ∑ I : (∀ j, Fin (d j + 1)), monomial (boxMonomial d I) (z I) := by
    simp [ofBox, LinearMap.sum_apply]
  have hCoeff (z : (∀ j, Fin (d j + 1)) → K) (I : ∀ j, Fin (d j + 1)) : (ofBox d z).coeff (boxMonomial d I) = z I := by
    classical
    rw [hOfBoxApply, MvPolynomial.coeff_sum, Finset.sum_eq_single I ?_ (by simp)]
    · simp [coeff_monomial]
    · intro J _ hJ
      rw [coeff_monomial]
      exact if_neg fun h ↦ absurd (hBoxInjective h) hJ
  have hCoeffOff (z : (∀ j, Fin (d j + 1)) → K) {ν : Fin m →₀ ℕ}
      (hν : ¬ ∀ j, ν j ≤ d j) : (ofBox d z).coeff ν = 0 := by
    classical
    rw [hOfBoxApply, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun I _ ↦ ?_
    have hne : boxMonomial d I ≠ ν := fun h ↦ hν (h ▸ (fun d (I : ∀ j, Fin (d j + 1)) j ↦
        (show MvPolynomial.boxMonomial d I j ≤ d j from by
          simpa [MvPolynomial.boxMonomial] using Nat.lt_succ_iff.mp (I j).isLt)) d I)
    simp [coeff_monomial, hne]
  have hPdeg : ∀ j, P.degreeOf j ≤ d j := by
    rw [hPdef]
    intro j
    rw [degreeOf_le_iff]
    intro ν hν
    by_contra h
    exact (mem_support_iff.mp hν) (hCoeffOff x fun hle ↦ h (hle j))
  have hPcoeff : ∀ I, P.coeff (boxMonomial d I) = x I := by
    rw [hPdef]
    exact hCoeff x
  have hP0 : P ≠ 0 := by
    rw [hPdef]
    exact fun h ↦ hx0 (funext fun I ↦ by
      have heq := congrArg (fun Q : MvPolynomial (Fin m) K ↦ Q.coeff (boxMonomial d I))
        (h.trans (map_zero (ofBox d)).symm)
      simpa [hCoeff] using heq)
  have hQdeg : ∀ j, (P.map (algebraMap K F)).degreeOf j ≤ d j := fun j ↦
    degreeOf_le_iff.mpr fun ν hν ↦ degreeOf_le_iff.mp (hPdeg j) ν
      (support_map_subset (algebraMap K F) P hν)
  have hEval {Q : MvPolynomial (Fin m) F} (hQ : ∀ j, Q.degreeOf j ≤ d j)
      (α : Fin m → F) (μ : Fin m →₀ ℕ) :
      eval α (hasseDeriv μ Q)
        = ∑ I : (∀ j, Fin (d j + 1)), hasseDerivRow d α μ I * Q.coeff (boxMonomial d I) := by
    classical
    set w : (Fin m →₀ ℕ) → F := fun ν ↦
      ((μ.prod fun j k ↦ (ν j).choose k : ℕ) : F) * (∏ j, α j ^ (ν j - μ j)) * Q.coeff ν with hw
    have hL : eval α (hasseDeriv μ Q) = ∑ ν ∈ Q.support, w ν := by
      rw [hasseDeriv_apply, map_sum]
      refine Finset.sum_congr rfl fun ν _ ↦ ?_
      rw [eval_monomial, hw]
      have hprod : ((ν - μ).prod fun j e ↦ α j ^ e) = ∏ j, α j ^ (ν j - μ j) := by
        rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
        exact Finset.prod_congr rfl fun j _ ↦ by rw [Finsupp.tsub_apply]
      rw [hprod]
      ring
    have hR : ∑ I : (∀ j, Fin (d j + 1)), w (boxMonomial d I) = ∑ ν ∈ Q.support, w ν := by
      rw [← Finset.sum_image (g := boxMonomial d) (f := w) fun a _ b _ h ↦ hBoxInjective h]
      refine (Finset.sum_subset (fun ν hν ↦ ?_) fun ν _ hν ↦ ?_).symm
      · obtain ⟨I, rfl⟩ : ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = ν := by
          refine ⟨fun j ↦ ⟨ν j, Nat.lt_succ_of_le ?_⟩, ?_⟩
          · exact degreeOf_le_iff.mp (hQ j) ν hν
          · ext j; rfl
        exact Finset.mem_image.mpr ⟨I, Finset.mem_univ I, rfl⟩
      · simp [hw, notMem_support_iff.mp hν]
    rw [hL, ← hR]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    rw [hw, hasseDerivRow]
    simp only [MvPolynomial.boxMonomial, Finsupp.coe_equivFunOnFinite_symm]
  refine ⟨P, hP0, hPdeg, ?_, ?_⟩
  · -- the index conditions
    intro k
    refine (fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {c : ENNReal}
      (h : ∀ μ : _ →₀ ℕ, MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0 →
        c ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j)) ↦
      (show c ≤ MvPolynomial.index d α P from le_iInf fun μ ↦ le_iInf fun hμ ↦ h μ hμ)) (fun j ↦ (d j : ℝ)) fun μ hμne ↦
      ENNReal.ofReal_le_ofReal (not_lt.mp fun hμ ↦ hμne ?_)
    by_cases hbox : ∀ j, μ j ≤ d j
    · obtain ⟨I, rfl⟩ : ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = μ := by
        refine ⟨fun j ↦ ⟨μ j, Nat.lt_succ_of_le (hbox j)⟩, ?_⟩
        ext j
        rfl
      have hw : ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k := by
        rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)] at hμ
        simpa only [MvPolynomial.boxMonomial, Finsupp.coe_equivFunOnFinite_symm] using hμ
      obtain ⟨i, hi⟩ : ∃ i : Fin n, e i = ⟨k, ⟨I, hw⟩⟩ :=
        ⟨e.symm _, Equiv.apply_symm_apply e _⟩
      have hAi : A i = hasseDerivRow d (α k) (boxMonomial d I) := by
        simp only [hAdef]
        rw [hi]
      have hmv : ∑ I', A i I' * algebraMap K F (x I') = 0 := by
        rw [← Matrix.mulVec_apply_eq_sum, hxker]
        rfl
      rw [hEval hQdeg]
      refine Eq.trans (Finset.sum_congr rfl fun I' _ ↦ ?_) hmv
      rw [hAi, coeff_map, hPcoeff]
    · push Not at hbox
      obtain ⟨j, hj⟩ := hbox
      rw [hasseDeriv_eq_zero_of_lt (lt_of_le_of_lt (hQdeg j) hj), map_zero]
  · -- the height bound
    have hdF : (0 : ℝ) < (finrank ℚ F : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
    have hdisc : (0 : ℝ) < |(NumberField.discr K : ℝ)| := by
      have h : (NumberField.discr K : ℝ) ≠ 0 := by
        exact_mod_cast NumberField.discr_ne_zero (K := K)
      positivity
    have hlm0' : 0 ≤ Real.log (MM : ℝ) := hlm0
    have hZ0 : 0 ≤ G + S / 2 * Real.log (MM : ℝ) := add_nonneg hG0 (mul_nonneg (by linarith) hlm0')
    have hArakRow (α : Fin m → F) {μ : Fin m →₀ ℕ} (hmu : ∀ j, μ j ≤ d j) : Real.log (arakelovMulHeight (hasseDerivRow d α μ)) / (finrank ℚ F : ℝ)
          ≤ 2⁻¹ * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
            + ∑ j, (d j : ℝ) * (Real.log 2 + absLogHeight₁ (α j)) := by
      have hBound {dd : ℕ} {x : Fin (dd + 1) → F} {C : ℝ} (hC : 1 ≤ C)
          (harch : ∀ v ∈ archAbsVal (K := F), (⨆ i, v (x i)) ≤ C)
          (hnon : ∀ v ∈ nonarchAbsVal (K := F), (⨆ i, v (x i)) ≤ 1) :
          Height.mulHeight x ≤ C ^ totalWeight F := by
        rcases eq_or_ne x 0 with rfl | hx
        · simpa using one_le_pow₀ hC
        rw [Height.mulHeight_eq hx]
        have h1 : (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod ≤ C ^ totalWeight F := by
          calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
              ≤ (archAbsVal.map fun _ : AbsoluteValue F ℝ ↦ C).prod :=
                Multiset.prod_map_le_prod_map₀ _ _
                  (fun v _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) fun v hv ↦ harch v hv
            _ = C ^ totalWeight F := by rw [Multiset.map_const', Multiset.prod_replicate]; rfl
        have h2 : ∏ᶠ v : nonarchAbsVal (K := F), ⨆ i, v.val (x i) ≤ 1 := (finprod_induction (f := fun v : nonarchAbsVal (K := F) ↦ ⨆ i, v.val (x i))
            (fun y ↦ 0 ≤ y ∧ y ≤ 1) ⟨zero_le_one, le_rfl⟩
            (fun y z hy hz ↦ ⟨mul_nonneg hy.1 hz.1, by nlinarith [hy.1, hy.2, hz.1, hz.2]⟩)
            fun v ↦ ⟨Real.iSup_nonneg fun _ ↦ v.val.nonneg _, hnon v.val v.prop⟩).2
        have hnn : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := F), ⨆ i, v.val (x i) := finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
        calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
                * ∏ᶠ v : nonarchAbsVal (K := F), ⨆ i, v.val (x i)
            ≤ C ^ totalWeight F * 1 := mul_le_mul h1 h2 hnn (by positivity)
          _ = C ^ totalWeight F := mul_one _
      have hNatCast {dd : ℕ} {n : Fin (dd + 1) → ℕ} {N : ℕ}
          (hN : 1 ≤ N) (hn : ∀ i, n i ≤ N) :
          Height.mulHeight (fun i ↦ (n i : F)) ≤ (N : ℝ) ^ totalWeight F := by
        refine hBound (by exact_mod_cast hN) (fun v _ ↦ ?_) fun v hv ↦ ?_
        · exact Real.iSup_le
            (fun i ↦ (v.apply_nat_le_self (n i)).trans (by exact_mod_cast hn i)) (by positivity)
        · exact Real.iSup_le
            (fun i ↦ (isNonarchimedean v hv).apply_natCast_le_one (by simp) (map_one v))
            zero_le_one
      have hPower (α : F) (d : ℕ) : Height.mulHeight (fun k : Fin (d + 1) ↦ α ^ (k : ℕ)) = Height.mulHeight₁ α ^ d := by
        have hx : (fun k : Fin (d + 1) ↦ α ^ (k : ℕ)) ≠ 0 := Function.ne_iff.mpr ⟨0, by simp⟩
        have hy : (![α ^ d, 1] : Fin 2 → F) ≠ 0 := Function.ne_iff.mpr ⟨1, by simp⟩
        have key : ∀ v : AbsoluteValue F ℝ,
            (⨆ k : Fin (d + 1), v (α ^ (k : ℕ))) = ⨆ i : Fin 2, v (![α ^ d, 1] i) := by
          intro v
          have hr : (⨆ i : Fin 2, v (![α ^ d, 1] i)) = max (v α ^ d) 1 := by
            refine le_antisymm (ciSup_le fun i ↦ ?_) (max_le ?_ ?_)
            · fin_cases i <;> simp [map_pow]
            · exact Finite.le_ciSup_of_le 0 (by simp [map_pow])
            · exact Finite.le_ciSup_of_le 1 (by simp)
          rw [hr]
          refine le_antisymm (Real.iSup_le (fun k ↦ ?_) (by positivity)) (max_le ?_ ?_)
          · rw [map_pow]
            rcases le_total (v α) 1 with h | h
            · exact le_trans (pow_le_one₀ (v.nonneg _) h) (le_max_right _ _)
            · exact le_trans (pow_le_pow_right₀ h (by omega)) (le_max_left _ _)
          · exact Finite.le_ciSup_of_le (Fin.last d) (by simp [map_pow])
          · exact Finite.le_ciSup_of_le 0 (by simp)
        have heq : Height.mulHeight (fun k : Fin (d + 1) ↦ α ^ (k : ℕ)) = Height.mulHeight (![α ^ d, 1] : Fin 2 → F) := by
          rw [Height.mulHeight_eq hx, Height.mulHeight_eq hy]
          congr 1
          · exact congrArg _ (Multiset.map_congr rfl fun v _ ↦ key v)
          · exact finprod_congr fun v ↦ key v.val
        rw [heq, ← Height.mulHeight₁_pow, Height.mulHeight₁_eq_mulHeight, Height.mulHeight_swap]
      have hMulRow (α : Fin m → F) {μ : Fin m →₀ ℕ} (hmu : ∀ j, μ j ≤ d j) : Height.mulHeight (hasseDerivRow d α μ)
            ≤ ((2 : ℝ) ^ (∑ j, d j)) ^ Height.totalWeight F
              * ∏ j, Height.mulHeight₁ (α j) ^ d j := by
        have hx : ∀ j : Fin m,
            (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j)) ≠ 0 := by
          intro j
          have h := hmu j
          exact Function.ne_iff.mpr ⟨⟨μ j, by omega⟩, by simp⟩
        have hfac : ∀ j : Fin m,
            Height.mulHeight (fun k : Fin (d j + 1) ↦
                (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
              ≤ ((2 : ℝ) ^ d j) ^ Height.totalWeight F * Height.mulHeight₁ (α j) ^ d j := by
          intro j
          have hmuj := hmu j
          have hsplit : (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
                = (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F))
                  * (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j)) := rfl
          have hc : Height.mulHeight (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F)) ≤ ((2 : ℝ) ^ d j) ^ Height.totalWeight F := by
            have := hNatCast
              (n := fun k : Fin (d j + 1) ↦ (k : ℕ).choose (μ j)) (N := 2 ^ d j) Nat.one_le_two_pow
              fun k ↦ (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
            simpa using this
          have hg : Height.mulHeight (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j)) ≤ Height.mulHeight₁ (α j) ^ d j := by
            rw [← hPower (α j) (d j),
              show (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j))
                  = (fun k : Fin (d j + 1) ↦ α j ^ (k : ℕ))
                    ∘ fun k : Fin (d j + 1) ↦ (⟨(k : ℕ) - μ j, by omega⟩ : Fin (d j + 1)) from rfl]
            exact Height.mulHeight_comp_le _ _
          calc Height.mulHeight (fun k : Fin (d j + 1) ↦
                  (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
              ≤ Height.mulHeight (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F))
                  * Height.mulHeight (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j)) := by
                rw [hsplit]; exact Height.mulHeight_mul_le _ _
            _ ≤ ((2 : ℝ) ^ d j) ^ Height.totalWeight F * Height.mulHeight₁ (α j) ^ d j := by gcongr
        have hRow : ∀ I : (∀ j, Fin (d j + 1)), hasseDerivRow d α μ I = ∏ j, (((I j : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((I j : ℕ) - μ j) := by
          intro I
          classical
          rw [hasseDerivRow, Finset.prod_mul_distrib]
          congr 1
          rw [← Nat.cast_prod]
          congr 1
          exact Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)
        rw [funext hRow, Height.mulHeight_fun_prod_eq hx]
        calc ∏ j, Height.mulHeight (fun k : Fin (d j + 1) ↦
                (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
            ≤ ∏ j, (((2 : ℝ) ^ d j) ^ Height.totalWeight F * Height.mulHeight₁ (α j) ^ d j) :=
              Finset.prod_le_prod₀ (fun j _ ↦ (Height.mulHeight_pos _).le) fun j _ ↦ hfac j
          _ = ((2 : ℝ) ^ (∑ j, d j)) ^ Height.totalWeight F * ∏ j, Height.mulHeight₁ (α j) ^ d j := by
              rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow_eq_pow_sum]
      have hdF : (0 : ℝ) < (finrank ℚ F : ℝ) := by
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
      have htw : (Height.totalWeight F : ℝ) = (finrank ℚ F : ℝ) := by
        rw [NumberField.totalWeight_eq_finrank]
      have hne : Nonempty (∀ j : Fin m, Fin (d j + 1)) := ⟨fun j ↦ 0⟩
      have hcard : (0 : ℝ) < (Fintype.card (∀ j : Fin m, Fin (d j + 1)) : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have hpos1 : 0 < Height.mulHeight (hasseDerivRow d α μ) := Height.mulHeight_pos _
      have h1 := Real.log_le_log (nativeSource16 (hasseDerivRow d α μ))
        (nativeSource105 (hasseDerivRow d α μ))
      rw [Real.log_mul (by positivity) hpos1.ne', Real.log_rpow hcard, htw] at h1
      have h2 := Real.log_le_log hpos1 (hMulRow α hmu)
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_prod (fun j _ ↦ by positivity)] at h2
      have h3 : Real.log (((2 : ℝ) ^ (∑ j, d j)) ^ Height.totalWeight F) = (finrank ℚ F : ℝ) * ((∑ j, (d j : ℝ)) * Real.log 2) := by
        rw [← pow_mul, Real.log_pow, ← htw]
        push_cast
        ring
      have h4 : ∑ j, Real.log (Height.mulHeight₁ (α j) ^ d j) = ∑ j, (d j : ℝ) * Real.log (Height.mulHeight₁ (α j)) :=
        Finset.sum_congr rfl fun j _ ↦ Real.log_pow _ _
      rw [h3, h4] at h2
      rw [div_le_iff₀ hdF]
      have hterm : ∀ j : Fin m, (d j : ℝ) * (Real.log 2 + NumberField.absLogHeight₁ (α j))
            * (finrank ℚ F : ℝ)
          = (finrank ℚ F : ℝ) * ((d j : ℝ) * Real.log 2)
            + (d j : ℝ) * Real.log (Height.mulHeight₁ (α j)) := by
        intro j
        rw [← nativeSource86, nativeSource83,
      Height.logHeight_eq_log_mulHeight, ← Height.mulHeight₁_eq_mulHeight]
        field_simp
      have hexp : (2⁻¹ * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
            + ∑ j, (d j : ℝ) * (Real.log 2 + NumberField.absLogHeight₁ (α j))) * (finrank ℚ F : ℝ)
          = (finrank ℚ F : ℝ) / 2 * Real.log (Fintype.card (∀ j : Fin m, Fin (d j + 1)))
            + ((finrank ℚ F : ℝ) * ((∑ j, (d j : ℝ)) * Real.log 2)
              + ∑ j, (d j : ℝ) * Real.log (Height.mulHeight₁ (α j))) := by
        rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl fun j _ ↦ hterm j,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      rw [hexp]
      linarith only [h1, h2]
    have hrowi : ∀ i : Fin n, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ) ≤ 2⁻¹ * Real.log (MM : ℝ)
          + ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ) := by
      intro i
      have h := hArakRow (α (e i).1) ((fun d (I : ∀ j, Fin (d j + 1)) j ↦
      (show MvPolynomial.boxMonomial d I j ≤ d j from by
        simpa [MvPolynomial.boxMonomial, Finsupp.coe_equivFunOnFinite_symm] using Nat.lt_succ_iff.mp (I j).isLt)) d (e i).2.1)
      rw [← hMMdef] at h
      have hcomm : ∑ j, (d j : ℝ) * (Real.log 2 + absLogHeight₁ (α (e i).1 j))
          = ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ) :=
        Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
      simp only [hAdef]
      rw [← hcomm]
      exact h
    have hW : ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
        ≤ κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ)) := by
      have h1 : ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
          ≤ ∑ i : Fin n, (2⁻¹ * Real.log (MM : ℝ)
              + ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ)) :=
        Finset.sum_le_sum fun i _ ↦ hrowi i
      have h2 : ∑ i : Fin n, (2⁻¹ * Real.log (MM : ℝ)
              + ∑ j, (Real.log 2 + absLogHeight₁ (α (e i).1 j)) * (d j : ℝ))
          = ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
                ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ)
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)) := by
        rw [Equiv.sum_comp e (fun ρ ↦ 2⁻¹ * Real.log (MM : ℝ)
            + ∑ j, (Real.log 2 + absLogHeight₁ (α ρ.1 j)) * (d j : ℝ)),
          ← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        dsimp only
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h3 : ∑ k, (Fintype.card {I : ∀ j, Fin (d j + 1) //
                ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t k} : ℝ)
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
          ≤ ∑ k, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ))
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hcardk k)
          (add_nonneg (by positivity) (hB0 k))
      have h4 : ∑ k, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ))
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
          = κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ)) := by
        have hterm : ∀ k : Fin N, cubeSimplexVolume m (t k) * (κ * ∏ j, (d j : ℝ))
              * (2⁻¹ * Real.log (MM : ℝ)
                + ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ))
            = (κ * ∏ j, (d j : ℝ)) * (cubeSimplexVolume m (t k) * (2⁻¹ * Real.log (MM : ℝ)))
              + (κ * ∏ j, (d j : ℝ)) * (cubeSimplexVolume m (t k)
                  * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)) := fun k ↦ by ring
        rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.sum_mul, ← hGdef, ← hSdef]
        ring
      linarith [h1, h3]
    have hRk0 : (0 : ℝ)
        < ∏ i, (arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹) ^ finrank K F :=
      Finset.prod_pos fun i _ ↦ pow_pos (Real.rpow_pos_of_pos (nativeSource16 _) _) _
    have hlogRk : Real.log (∏ i, (arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹)
          ^ finrank K F)
        = rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ) := by
      rw [Real.log_prod (f := fun i : Fin n ↦
          (arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹) ^ finrank K F)
        (fun i _ ↦ (pow_pos (Real.rpow_pos_of_pos (nativeSource16 _) _) _).ne'),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Real.log_pow, Real.log_rpow (nativeSource16 _), hrrdef]
      ring
    have hxP : absMulHeight x = P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ := by
      rw [← funext hPcoeff]
      exact absMulHeight_coeff_box P hPdeg
    have hlogle := Real.log_le_log (zero_lt_one.trans_le hxpos) hxle
    rw [hxP, Real.log_rpow (show 0 < P.mulHeight from Height.mulHeight_pos
      (fun i : (AddMonoidAlgebra.coeff P).support ↦ (AddMonoidAlgebra.coeff P) i.val)),
      Real.log_mul (Real.rpow_pos_of_pos hdisc _).ne' (Real.rpow_pos_of_pos hRk0 _).ne',
      Real.log_rpow hdisc, Real.log_rpow hRk0, hlogRk] at hlogle
    have hden2 : (MM : ℝ) * (1 - rr * κ * S) ≤ (MM : ℝ) - rr * (A.rank : ℝ) := by
      linarith [hrankM]
    have hden1 : (0 : ℝ) < (MM : ℝ) * (1 - rr * κ * S) := mul_pos hM0 hb0
    have hden0 : (0 : ℝ) < (MM : ℝ) - rr * (A.rank : ℝ) := lt_of_lt_of_le hden1 hden2
    have hCnn : (0 : ℝ) ≤ rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ)) :=
      mul_nonneg (div_nonneg (mul_nonneg hrr0 hκ0.le) hb0.le) hZ0
    have hkey : ((MM : ℝ) - rr * (A.rank : ℝ))⁻¹
          * (rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ))
        ≤ rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ)) := by
      rw [← div_eq_inv_mul, div_le_iff₀ hden0]
      have e1 : rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ))
            * ((MM : ℝ) * (1 - rr * κ * S))
          = rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ)) := by
        field_simp
      have e2 : rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
          ≤ rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ)) := by
        calc rr * ∑ i, Real.log (arakelovMulHeight (A i)) / (finrank ℚ F : ℝ)
            ≤ rr * (κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ))) :=
              mul_le_mul_of_nonneg_left hW hrr0
          _ ≤ rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ)) := by
              rw [show rr * (κ * (∏ j, (d j : ℝ)) * (G + S / 2 * Real.log (MM : ℝ)))
                  = rr * κ * (G + S / 2 * Real.log (MM : ℝ)) * ∏ j, (d j : ℝ) by ring,
                show rr * κ * (MM : ℝ) * (G + S / 2 * Real.log (MM : ℝ))
                  = rr * κ * (G + S / 2 * Real.log (MM : ℝ)) * (MM : ℝ) by ring]
              exact mul_le_mul_of_nonneg_left hProdM
                (mul_nonneg (mul_nonneg hrr0 hκ0.le) hZ0)
      have e3 : rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ))
            * ((MM : ℝ) * (1 - rr * κ * S))
          ≤ rr * κ / (1 - rr * κ * S) * (G + S / 2 * Real.log (MM : ℝ))
            * ((MM : ℝ) - rr * (A.rank : ℝ)) :=
        mul_le_mul_of_nonneg_left hden2 hCnn
      linarith [e1, e2, e3]
    have hk'cast : (k' : ℝ) = (MM : ℝ) - rr * (A.rank : ℝ) := by
      dsimp [k']; rw [Nat.cast_sub hfeasRank.le, ← hMMdef, Nat.cast_mul, ← hrrdef]
    rw [hk'cast] at hlogle
    rw [div_eq_inv_mul]
    linarith only [hlogle, hkey]
end MvPolynomial
end
