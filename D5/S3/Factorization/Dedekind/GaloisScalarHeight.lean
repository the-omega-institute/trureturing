/- GID: D5/S3/Factorization/Dedekind/GaloisScalarHeight
   generality: G
   mirror-B: D5/B/S3/Factorization/Dedekind/GaloisScalarHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/tauceti2026canonicalheight]
   utility: none
   digest: Number-field automorphisms preserve scalar absolute height through ideal norms and infinite-place multiplicities. -/

/-
Copyright (c) 2026 trureturing contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026canonicalheight.md.
Authors: trureturing contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.Quotient.Operations

public section

open Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

lemma scalar_mul_height_galois (σ : Gal(K/ℚ)) (x : K) :
    mulHeight₁ (σ x) = mulHeight₁ x := by
  have hpair (a b : 𝓞 K) (hb : b ≠ 0) :
      mulHeight ![σ (a : K), σ (b : K)] = mulHeight ![(a : K), (b : K)] := by
    let e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv σ.toRingEquiv
    have he (c : 𝓞 K) : (e c : K) = σ (c : K) := by
      simp [e]
    have hσ : (![σ (a : K), σ (b : K)] : Fin 2 → K) =
        ![(e a : K), (e b : K)] := by
      funext i
      fin_cases i <;> simp [he]
    have hne : (![(a : K), (b : K)] : Fin 2 → K) ≠ 0 := by
      intro h
      apply hb
      have h1 := congrFun h (1 : Fin 2)
      exact RingOfIntegers.coe_injective (by simpa using h1)
    have hne' : (![(e a : K), (e b : K)] : Fin 2 → K) ≠ 0 := by
      intro h
      apply e.injective.ne hb
      have h1 := congrFun h (1 : Fin 2)
      exact RingOfIntegers.coe_injective (by simpa using h1)
    have hmult (τ : Gal(K/ℚ)) (v : InfinitePlace K) : (τ • v).mult = v.mult := by
      simp only [InfinitePlace.mult]
      by_cases hv : v.IsReal
      · have hτ : (τ • v).IsReal :=
          (InfinitePlace.isReal_smul_iff (σ := τ) (w := v)).mpr hv
        simp [hv, hτ]
      · have hτ : ¬ (τ • v).IsReal := fun h ↦
          hv ((InfinitePlace.isReal_smul_iff (σ := τ) (w := v)).mp h)
        simp [hv, hτ]
    have harch :
        (∏ v : InfinitePlace K, (⨆ i : Fin 2, v (![σ (a : K), σ (b : K)] i)) ^ v.mult) =
          ∏ v : InfinitePlace K, (⨆ i : Fin 2, v (![(a : K), (b : K)] i)) ^ v.mult := by
      classical
      apply Fintype.prod_equiv (MulAction.toPerm σ⁻¹) _ _
      intro v
      have hv (i : Fin 2) :
          v (![σ (a : K), σ (b : K)] i) =
            (σ⁻¹ • v) (![(a : K), (b : K)] i) := by
        fin_cases i <;> simp [InfinitePlace.smul_apply, AlgEquiv.aut_inv]
      simpa only [MulAction.toPerm_apply, hmult] using
        congrArg (fun y : ℝ => y ^ v.mult) (iSup_congr hv)
    rw [hσ] at harch
    have hfin :
        (∏ᶠ v : FinitePlace K, ⨆ i : Fin 2, v (![e a, e b] i : K)) =
          ∏ᶠ v : FinitePlace K, ⨆ i : Fin 2, v (![a, b] i : K) := by
      have hx : (![a, b] : Fin 2 → 𝓞 K) ≠ 0 := by
        intro h
        apply hb
        have h1 := congrFun h (1 : Fin 2)
        simpa using h1
      have hx' : (![e a, e b] : Fin 2 → 𝓞 K) ≠ 0 := by
        intro h
        apply e.injective.ne hb
        have h1 := congrFun h (1 : Fin 2)
        simpa using h1
      have hspan : Ideal.span (Set.range (![e a, e b] : Fin 2 → 𝓞 K)) =
          (Ideal.span (Set.range (![a, b] : Fin 2 → 𝓞 K))).map e := by
        have hvec : (![e a, e b] : Fin 2 → 𝓞 K) =
            e ∘ (![a, b] : Fin 2 → 𝓞 K) := by
          funext i
          fin_cases i <;> rfl
        rw [hvec, Set.range_comp, Ideal.map_span]
      have hnorm (I : Ideal (𝓞 K)) : Ideal.absNorm (I.map e) = Ideal.absNorm I := by
        rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
          Submodule.cardQuot_apply, Submodule.cardQuot_apply]
        exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm
      have hleft := NumberField.absNorm_mul_finprod_finitePlace_eq_one (K := K) hx'
      have hright := NumberField.absNorm_mul_finprod_finitePlace_eq_one (K := K) hx
      rw [hspan, hnorm] at hleft
      have hn : (Ideal.absNorm (Ideal.span (Set.range (![a, b] : Fin 2 → 𝓞 K))) : ℝ) ≠ 0 := by
        intro h
        rw [h, zero_mul] at hright
        norm_num at hright
      exact mul_left_cancel₀ hn (hleft.trans hright.symm)
    have hcoe (c d : 𝓞 K) (i : Fin 2) :
        ((![c, d] i : 𝓞 K) : K) = (![(c : K), (d : K)] i) := by
      fin_cases i <;> rfl
    simp only [hcoe] at hfin
    rw [hσ, NumberField.mulHeight_eq hne', NumberField.mulHeight_eq hne]
    exact congrArg₂ (· * ·) harch hfin
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [map_div₀, mulHeight₁_div_eq_mulHeight, mulHeight₁_div_eq_mulHeight]
  exact hpair a b hb0

end NumberField
