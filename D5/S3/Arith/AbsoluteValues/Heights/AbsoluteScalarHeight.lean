/- GID: D5/S3/Arith/AbsoluteValues/Heights/AbsoluteScalarHeight
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/AbsoluteScalarHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The absolute scalar logarithmic height is the relative logarithmic height divided by the field degree. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Source: rwst/Subspace-Theorems, ArithmeticHeights/Extension.lean, bfd830f481b296989fa5f0c1e48d9316f72270d8.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasis
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Set.Card

@[expose] public section

namespace NumberField

open Finset Function Height InfinitePlace Module

/-- Scalar absolute and relative logarithmic heights agree after scaling by the degree. -/
theorem scalar_absolute_log_height {F : Type*} [Field F] [NumberField F] (x : F) :
    Real.log (Height.mulHeight₁ x) = (Module.finrank ℚ F : ℝ) * absLogHeight₁ x := by
  have hfrF : (0 : ℝ) < (finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
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
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
      NumberField.RingOfIntegers.algebraMap.injective K L
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
    exact (
      nativeSource78 _ _ fun φ ↦ iSup_congr fun i ↦ by simp [InfinitePlace.apply]
    )))))
  have nativeSource80 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (y : ι → 𝓞 K) => (show Height.mulHeight (fun i ↦ (y i : K)) ^ Module.finrank K L
        = Height.mulHeight (fun i ↦ algebraMap K L (y i : K)) from by
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
    have hd' : algebraMap K L d ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr hd
    have h1 : (fun i ↦ (y i : K)) = d • x := funext fun i ↦ by rw [hy i]; rfl
    have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
      funext i
      simp [hy i]
    have e1 : Height.mulHeight (fun i ↦ (y i : K)) = Height.mulHeight x :=
      h1 ▸ Height.mulHeight_smul_eq_mulHeight x hd
    have e2 : Height.mulHeight (fun i ↦ algebraMap K L (y i : K))
        = Height.mulHeight (algebraMap K L ∘ x) :=
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
    have : Module.Finite (adjoin ℚ (Set.range x)) K :=
      Module.Finite.of_restrictScalars_finite ℚ _ K
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
    have hm' : ((finrank ℚ (adjoin ℚ (Set.range x))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := ℚ) (M := adjoin ℚ (Set.range x))).ne'
    have hn' : ((finrank (adjoin ℚ (Set.range x)) K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := adjoin ℚ (Set.range x)) (M := K)).ne'
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
    have : IsScalarTower ℚ (adjoin ℚ (Set.range x)) E :=
      IsScalarTower.of_algebraMap_eq fun r ↦ ((inclusion hFE).commutes r).symm
    have : Module.Finite (adjoin ℚ (Set.range x)) E :=
      Module.Finite.of_restrictScalars_finite ℚ _ E
    have hcomp : (Algebra.algebraMap (adjoin ℚ (Set.range x)) E) ∘
        (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))
        = fun i ↦ (⟨x i, hx i⟩ : E) := rfl
    letI : FaithfulSMul (adjoin ℚ (Set.range x)) E :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (adjoin ℚ (Set.range x)) E).injective
    letI : Module.Free ℚ (adjoin ℚ (Set.range x)) := Module.Free.of_divisionRing _ _
    letI : Module.Free (adjoin ℚ (Set.range x)) E := Module.Free.of_divisionRing _ _
    letI : IsTorsionFree ℚ (adjoin ℚ (Set.range x)) := Module.Free.instIsTorsionFree _ _
    letI : IsTorsionFree (adjoin ℚ (Set.range x)) E := Module.Free.instIsTorsionFree _ _
    rw [NumberField.absMulHeight, dif_pos hint, ← hcomp, ← nativeSource81,
      ← Module.finrank_mul_finrank ℚ (adjoin ℚ (Set.range x)) E]
    rw [← Real.rpow_natCast (Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))) (finrank (adjoin ℚ (Set.range x)) E), ← Real.rpow_mul ((Height.mulHeight_pos (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))).le)]
    congr 1
    have hm' : ((finrank ℚ (adjoin ℚ (Set.range x))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := ℚ) (M := adjoin ℚ (Set.range x))).ne'
    have hn' : ((finrank (adjoin ℚ (Set.range x)) E) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := adjoin ℚ (Set.range x)) (M := E)).ne'
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
      have heq : (fun i ↦ (⟨(![x, 1] : Fin 2 → K) i, hmem i⟩ : ℚ⟮x⟯))
          = ![IntermediateField.AdjoinSimple.gen ℚ x, 1] := by
        funext i
        fin_cases i <;> exact Subtype.ext rfl
      rw [nativeSource84 hmem, heq, NumberField.absMulHeight₁, dif_pos hx,
        Height.mulHeight₁_eq_mulHeight]
    · have hne : ¬ ∀ i, IsIntegral ℚ ((![x, 1] : Fin 2 → K) i) := fun h ↦ hx (by simpa using h 0)
      rw [NumberField.absMulHeight, dif_neg hne, NumberField.absMulHeight₁,
        dif_neg hx]))))
  have nativeSource86 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show NumberField.absLogHeight ![x, 1] = NumberField.absLogHeight₁ x from by
    classical
    exact (
      congrArg Real.log (nativeSource85 x)
    )))))
  rw [← nativeSource86, nativeSource83,
    Height.logHeight_eq_log_mulHeight, ← Height.mulHeight₁_eq_mulHeight]
  field_simp

end NumberField
