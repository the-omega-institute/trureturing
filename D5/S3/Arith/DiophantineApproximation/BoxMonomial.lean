/- GID: D5/S3/Arith/DiophantineApproximation/BoxMonomial
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/BoxMonomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A multivariate polynomial's coefficient box controls its absolute multiplicative height. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasis
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

open Nat

open Finsupp

noncomputable section

namespace MvPolynomial

section Monomials

variable {σ : Type*} [Fintype σ] {d : σ → ℕ}

/-- **The exponent named by a point of the box** `∀ j, Fin (d j + 1)`. -/
def boxMonomial (d : σ → ℕ) (I : ∀ j, Fin (d j + 1)) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ (I j : ℕ)

omit [Fintype σ] in
/-- **A Hasse derivative of an order that leaves the box vanishes** on a polynomial of bounded
partial degrees: the binomial factor `(m j).choose (μ j)` of `MvPolynomial.hasseDeriv_monomial`
is zero at every monomial `m` that occurs. -/
theorem hasseDeriv_eq_zero_of_lt {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {j : σ}
    {μ : σ →₀ ℕ} (h : P.degreeOf j < μ j) : hasseDeriv μ P = 0 := by
  have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials σ R).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
    (μ.prod fun j k ↦ (m j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  classical
  rw [hasseDeriv_apply]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  have hmj : m j < μ j := lt_of_le_of_lt (degreeOf_le_iff.mp le_rfl m hm) h
  rw [prod_choose_eq_zero (fun hle ↦ absurd (hle j) (by omega))]
  simp

end Monomials

section OfBox

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] {d : σ → ℕ}

/-- **The polynomial named by a coefficient vector on the box.** -/
def ofBox (d : σ → ℕ) : ((∀ j, Fin (d j + 1)) → K) →ₗ[K] MvPolynomial σ K :=
  ∑ I : (∀ j, Fin (d j + 1)), (monomial (boxMonomial d I)).comp (LinearMap.proj I)

end OfBox

section Row

variable {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]

/-- **The row of the condition matrix** attached to the Hasse derivative of order `μ` at `α`:
the linear form in the coefficients of a polynomial of the box whose vanishing says that
`∂_μ P` vanishes at `α`. -/
def hasseDerivRow (d : σ → ℕ) (α : σ → R) (μ : σ →₀ ℕ) : (∀ j, Fin (d j + 1)) → R :=
  fun I ↦ ((μ.prod fun j k ↦ (I j : ℕ).choose k : ℕ) : R) * ∏ j, α j ^ ((I j : ℕ) - μ j)

end Row

section Height

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
  {d : σ → ℕ}

end Height

section Absolute

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [NumberField K] {d : σ → ℕ}

/-- The absolute height of the box coefficient vector agrees with the polynomial height. -/
theorem absMulHeight_coeff_box (P : MvPolynomial σ K) (hP : ∀ j, P.degreeOf j ≤ d j) :
    NumberField.absMulHeight (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I))
      = P.mulHeight ^ ((Module.finrank ℚ K : ℝ))⁻¹ := by
  have nativeSource81 := (open scoped Classical NumberField in (open Finset Function Height NumberField.InfinitePlace Module in (fun {K L : Type _} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {ι : Type _} [Finite ι] (x : ι → K) => (show Height.mulHeight x ^ Module.finrank K L = Height.mulHeight (algebraMap K L ∘ x) from by
    letI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
    letI : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
    letI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
    have nativeSource73 := (open Finset Function Height NumberField.InfinitePlace Module in (fun {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∃ (d : K) (y : ι → NumberField.RingOfIntegers K), d ≠ 0 ∧ ∀ i, (y i : K) = d * x i from by
      classical
      have := Fintype.ofFinite ι
      obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers K))
        (Finset.univ : Finset ι) x
      refine ⟨Algebra.algebraMap (NumberField.RingOfIntegers K) K (b : NumberField.RingOfIntegers K), fun i ↦ (hb i (Finset.mem_univ i)).choose, ?_, fun i ↦ ?_⟩
      · exact (map_ne_zero_iff _ (NumberField.RingOfIntegers.coe_injective (K := K))).mpr
          (nonZeroDivisors.coe_ne_zero b)
      · have h := (hb i (Finset.mem_univ i)).choose_spec
        rw [show (((hb i (Finset.mem_univ i)).choose : NumberField.RingOfIntegers K) : K)
          = Algebra.algebraMap (NumberField.RingOfIntegers K) K (hb i (Finset.mem_univ i)).choose from rfl, h, Algebra.smul_def])))
    have nativeSource74 := (open Finset Function Height NumberField.InfinitePlace Module in (fun {ι : Type _} [instSource7 : Finite ι] {y : ι → NumberField.RingOfIntegers K} (hy : y ≠ 0) => (show ∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)) =
          (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (y i : K)) ^ Module.finrank K L from by
      classical
      have hinj : Function.Injective (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) :=
        NumberField.RingOfIntegers.algebraMap.injective K L
      have hy' : (fun i ↦ algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) (y i)) ≠ 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
        exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
      have hspan : Ideal.span (Set.range fun i ↦ algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) (y i)) =
          (Ideal.span (Set.range y)).map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) := by
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      have hK := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy
      have hL := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy'
      rw [hspan, ← Ideal.absNorm_relNorm (NumberField.RingOfIntegers K), Ideal.relNorm_algebraMap, map_pow,
        ← IsFractionRing.finrank_eq (NumberField.RingOfIntegers K) K (NumberField.RingOfIntegers L) L] at hL
      have hcoe (a : NumberField.RingOfIntegers K) :
          ((algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a : NumberField.RingOfIntegers L) : L) = algebraMap K L (a : K) := by
        rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
          ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L,
          ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L]
      simp_rw [hcoe] at hL
      have hN : ((Ideal.span (Set.range y)).absNorm : ℝ) ≠ 0 := by
        have : Ideal.span (Set.range y) ≠ ⊥ := by
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
          exact fun h ↦ hi (by simpa using (Ideal.span_eq_bot.mp h) (y i) ⟨i, rfl⟩)
        exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr this
      refine mul_left_cancel₀ (pow_ne_zero (Module.finrank K L) hN) ?_
      rw [← mul_pow, hK, one_pow]
      exact_mod_cast hL)))
    have nativeSource75 := (open Finset Function Height NumberField.InfinitePlace Module in (open scoped Classical in (fun (ψ : K →+* ℂ) => (show #{emb : L →+* ℂ | emb.comp (Algebra.algebraMap K L) = ψ} = Module.finrank K L from by
      classical
      let : Algebra K ℂ := ψ.toAlgebra
      rw [← AlgHom.card K L ℂ]
      refine (Finset.card_nbij AlgHom.toRingHom (fun σ _ ↦ ?_) (fun σ _ τ _ h => AlgHom.ext fun x => DFunLike.congr_fun h x)
        (fun emb hφ ↦ ?_)).symm
      · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and]
        ext r
        simp [RingHom.algebraMap_toAlgebra]
      · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hφ
        exact ⟨⟨emb, fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← hφ]⟩, mem_univ _, rfl⟩))))
    have nativeSource76 := (open Finset Function Height NumberField.InfinitePlace Module in (open scoped Classical in (fun (F : (K →+* ℂ) → ℝ) => (show ∏ emb : L →+* ℂ, F (emb.comp (algebraMap K L)) = (∏ ψ : K →+* ℂ, F ψ) ^ Module.finrank K L from by
      classical
      rw [← Finset.prod_fiberwise Finset.univ (fun emb : L →+* ℂ ↦ emb.comp (algebraMap K L))
        (fun emb ↦ F (emb.comp (algebraMap K L))), ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun ψ _ ↦ ?_
      rw [Finset.prod_congr rfl (fun emb hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
        Finset.prod_const, nativeSource75]))))
    have nativeSource78 := (open Finset Function Height NumberField.InfinitePlace Module in (open scoped Classical in (fun (f : NumberField.InfinitePlace K → ℝ) (g : NumberField.InfinitePlace L → ℝ)
        (h : ∀ emb : L →+* ℂ, g (NumberField.InfinitePlace.mk emb) = f (NumberField.InfinitePlace.mk (emb.comp (Algebra.algebraMap K L)))) => (show ∏ w : NumberField.InfinitePlace L, g w ^ w.mult = (∏ v : NumberField.InfinitePlace K, f v ^ v.mult) ^ Module.finrank K L from by
      classical
      have hLg : (∏ emb : L →+* ℂ, g (NumberField.InfinitePlace.mk emb))
          = ∏ w : NumberField.InfinitePlace L, g w ^ w.mult := by
        rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk
          (fun emb ↦ g (NumberField.InfinitePlace.mk emb))]
        refine Finset.prod_congr rfl fun w _ ↦ ?_
        rw [Finset.prod_congr rfl (fun emb hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
          Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq]
      have hKf : (∏ emb : K →+* ℂ, f (NumberField.InfinitePlace.mk emb))
          = ∏ v : NumberField.InfinitePlace K, f v ^ v.mult := by
        rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk
          (fun emb ↦ f (NumberField.InfinitePlace.mk emb))]
        refine Finset.prod_congr rfl fun v _ ↦ ?_
        rw [Finset.prod_congr rfl (fun emb hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
          Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq]
      rw [← hLg, ← hKf, ← nativeSource76 (fun ψ ↦ f (NumberField.InfinitePlace.mk ψ))]
      exact Finset.prod_congr rfl fun emb _ ↦ h emb))))
    have nativeSource79 := (open Finset Function Height NumberField.InfinitePlace Module in (open scoped Classical in (fun {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∏ w : NumberField.InfinitePlace L, (⨆ i, w (Algebra.algebraMap K L (x i))) ^ w.mult =
          (∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ Module.finrank K L from by
      classical
      exact (
        nativeSource78 _ _ fun emb ↦ iSup_congr fun i ↦ by simp only [NumberField.InfinitePlace.apply, RingHom.comp_apply]
      )))))
    have nativeSource80 := (open Finset Function Height NumberField.InfinitePlace Module in (fun {ι : Type _} [instSource7 : Finite ι] (y : ι → NumberField.RingOfIntegers K) => (show Height.mulHeight (fun i ↦ (y i : K)) ^ Module.finrank K L
          = Height.mulHeight (fun i ↦ algebraMap K L (y i : K)) from by
      classical
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      have hz : (fun i ↦ (y i : K)) ≠ 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
        change y i ≠ 0 at hi
        exact Function.ne_iff.mpr ⟨i, fun h ↦ hi
          (NumberField.RingOfIntegers.coe_injective (K := K)
            (by simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap, Pi.zero_apply, map_zero] using h))⟩
      have hz' : (fun i ↦ algebraMap K L (y i : K)) ≠ 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
        change (y i : K) ≠ 0 at hi
        exact Function.ne_iff.mpr ⟨i, fun h ↦ hi ((algebraMap K L).injective
          (by simpa only [Pi.zero_apply, map_zero] using h))⟩
      rw [NumberField.mulHeight_eq hz, NumberField.mulHeight_eq hz', mul_pow,
        nativeSource79, nativeSource74 hy])))
    classical
    obtain ⟨d, y, hd, hy⟩ := nativeSource73 x
    have hd' : algebraMap K L d ≠ 0 :=
      (map_ne_zero_iff _ ((algebraMap K L).injective)).mpr hd
    have h1 : (fun i ↦ (y i : K)) = d • x := _root_.funext fun i ↦ by rw [hy i]; rfl
    have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
      funext i
      simp [hy i]
    have e1 : Height.mulHeight (fun i ↦ (y i : K)) = Height.mulHeight x :=
      h1 ▸ Height.mulHeight_smul_eq_mulHeight x hd
    have e2 : Height.mulHeight (fun i ↦ algebraMap K L (y i : K))
        = Height.mulHeight (algebraMap K L ∘ x) :=
      h2 ▸ Height.mulHeight_smul_eq_mulHeight _ hd'
    rw [← e1, ← e2]
    exact nativeSource80 y
    ))))
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
      (faithfulSMul_iff_algebraMap_injective (adjoin ℚ (Set.range x)) K).2
        (algebraMap (adjoin ℚ (Set.range x)) K).injective
    letI : Module.Free ℚ (adjoin ℚ (Set.range x)) :=
      Module.Free.of_divisionRing ℚ (adjoin ℚ (Set.range x))
    letI : Module.Free (adjoin ℚ (Set.range x)) K :=
      Module.Free.of_divisionRing (adjoin ℚ (Set.range x)) K
    letI : IsTorsionFree ℚ (adjoin ℚ (Set.range x)) :=
      Module.Free.instIsTorsionFree ℚ (adjoin ℚ (Set.range x))
    letI : IsTorsionFree (adjoin ℚ (Set.range x)) K :=
      Module.Free.instIsTorsionFree (adjoin ℚ (Set.range x)) K
    rw [NumberField.absMulHeight, dif_pos hint]
    conv_rhs => rw [← hcomp]
    rw [← nativeSource81,
      ← Module.finrank_mul_finrank ℚ (adjoin ℚ (Set.range x)) K]
    rw [← Real.rpow_natCast (Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))) (finrank (adjoin ℚ (Set.range x)) K), ← Real.rpow_mul ((Height.mulHeight_pos (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))).le)]
    congr 1
    have hm' : ((finrank ℚ (adjoin ℚ (Set.range x))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := ℚ) (M := adjoin ℚ (Set.range x))).ne'
    have hn' : ((finrank (adjoin ℚ (Set.range x)) K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := adjoin ℚ (Set.range x)) (M := K)).ne'
    push_cast
    field_simp)))
  have hBoxInjective : Function.Injective (boxMonomial d) := by
    intro I J h
    funext j
    exact Fin.ext (by
      simpa only [boxMonomial, Finsupp.coe_equivFunOnFinite_symm] using
        congrFun (congrArg (⇑) h) j)
  have hSupport : ∀ a ∈ P.support, a ∈ Set.range (boxMonomial d) := by
    intro a ha
    have hle : ∀ j, a j ≤ d j := fun j ↦
      le_trans (degreeOf_le_iff.mp le_rfl a ha) (hP j)
    refine ⟨fun j ↦ ⟨a j, Nat.lt_succ_of_le (hle j)⟩, ?_⟩
    ext j
    rfl
  have hHeight : P.mulHeight = Height.mulHeight
      (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I)) := by
    classical
    have hbij : Function.Bijective
        (fun I : Function.support (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I)) ↦
          (⟨boxMonomial d I.val, Finsupp.mem_support_iff.mpr I.prop⟩ : P.support)) := by
      refine ⟨fun I J h ↦ Subtype.ext (hBoxInjective (congrArg Subtype.val h)),
        fun ⟨a, ha⟩ ↦ ?_⟩
      obtain ⟨I, rfl⟩ := hSupport a ha
      exact ⟨⟨I, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
    change Height.mulHeight (fun a : P.support ↦ P.coeff a.val) =
      Height.mulHeight (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I))
    rw [Height.mulHeight_eq_mulHeight_restrict_support
      (fun I : (∀ j, Fin (d j + 1)) ↦ P.coeff (boxMonomial d I)),
      ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
    change Height.mulHeight _ = Height.mulHeight _
    rfl
  rw [nativeSource82, hHeight]

end Absolute

section Acceptance

end Acceptance

end MvPolynomial

end
