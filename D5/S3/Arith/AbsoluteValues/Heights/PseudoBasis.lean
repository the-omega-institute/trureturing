/- GID: D5/S3/Arith/AbsoluteValues/Heights/PseudoBasis
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/PseudoBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finitely generated module over a Dedekind domain admits a pseudo-basis. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Localization.Finiteness

public section

open Module

section LinearIndependent

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

end LinearIndependent

namespace exteriorPower

section Field

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] {k : ℕ}

end Field

section Snoc

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}

end Snoc

section Plucker

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The **Plücker coordinates** of a family `v : Fin k → (ι → R)`: the coordinate tuple of the
wedge `v 0 ∧ ⋯ ∧ v (k-1)` in the basis of `⋀[R]^k (ι → R)` induced by the standard basis of
`ι → R`, indexed by the `k`-element subsets of `ι`. -/
@[expose] noncomputable def plucker (k : ℕ) (v : Fin k → (ι → R)) : Set.powersetCard ι k → R :=
  ((Pi.basisFun R ι).exteriorPower k).equivFun (ιMulti R k v)

variable {K : Type*} [Field K] {k : ℕ} {v : Fin k → (ι → K)}

end Plucker

end exteriorPower

namespace Submodule

open exteriorPower

section Basis

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {κ : Type*}
  {V : Submodule R M}

end Basis

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

/-- **The Plücker point of a `k`-dimensional subspace of `ι → K`** (Bombieri–Gubler 2.8.4;
Hindry–Silverman, Exercise A.1.11(a)–(b)): the point of projective space on the `k`-element subsets
of `ι` given by the Plücker coordinates of any basis of `V`. It does not depend on the basis; see
`Submodule.pluckerPoint_eq_mk`. -/
@[expose] noncomputable def pluckerPoint (V : Submodule K (ι → K)) (hV : finrank K V = k) :
    Projectivization K (Set.powersetCard ι k → K) := by
  classical
  let v : Fin k → (ι → K) := fun i => ((finBasisOfFinrankEq K V hV) i : ι → K)
  have hv : LinearIndependent K v :=
    (finBasisOfFinrankEq K V hV).linearIndependent.map' V.subtype V.ker_subtype
  have hn : exteriorPower.ιMulti K k v ≠ 0 := by
    have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
    have hs : (⇑(Set.powersetCard.ofFinEmbEquiv.symm
        (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k))) = (id : Fin k → Fin k) := by
      rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
      exact (Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_univ x) strictMono_id).symm
    rwa [exteriorPower.ιMulti_family, hs, Function.comp_id] at h
  have hp : exteriorPower.plucker k v ≠ 0 := by
    intro h0
    apply hn
    apply ((Pi.basisFun K ι).exteriorPower k).equivFun.injective
    simpa only [exteriorPower.plucker, map_zero] using h0
  exact Projectivization.mk K (exteriorPower.plucker k v) hp

end Submodule

section Examples

open Submodule exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

end Examples

end

public section

open Function Real

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*}

/-- The **affine height** of a tuple: the projective height of the tuple with a coordinate `1`
appended.

Unlike `Height.mulHeight` this is not invariant under scaling
(`Height.exists_mulHeightAff_smul_ne`), and that is exactly what a bound on a non-homogeneous
quantity needs: the value `∑ i, a i * x i` of a linear form is not a function on projective
space, so no scaling-invariant quantity can bound its height. The affine height dominates the
projective height (`Height.mulHeight_le_mulHeightAff`) and the height of every single coordinate
(`Height.mulHeight₁_le_mulHeightAff`), neither of which `mulHeight` does. -/
@[expose] noncomputable def mulHeightAff (x : ι → K) : ℝ := mulHeight fun o : Option ι ↦ o.elim 1 x

/-- The affine logarithmic height of a tuple. As everywhere in this development, the logarithmic
height is *defined* as the logarithm of the multiplicative one. -/
@[expose] noncomputable def logHeightAff (x : ι → K) : ℝ := log (mulHeightAff x)

section Affine

variable [Finite ι]

end Affine

end Height

end

public section

namespace NumberField

open Function IntermediateField Module

section Def

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Finite ι]

open scoped Classical in
/-- The **absolute multiplicative height** of a tuple of algebraic numbers: the height relative to
the field the coordinates generate, taken to the power `1 / [ℚ(x₀, x₁, …) : ℚ]`. A tuple with a
coordinate that is not algebraic gets the junk value `1`.

This is the tuple analogue of Mathlib's `NumberField.absMulHeight₁`, which takes this route
through `ℚ⟮x⟯`; `absMulHeight_eq_absMulHeight₁` says the two agree where both apply. -/
@[expose] noncomputable def absMulHeight (x : ι → K) : ℝ :=
  if hx : ∀ i, IsIntegral ℚ (x i) then
    haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range x)) :=
      finiteDimensional_adjoin fun y hy ↦ by obtain ⟨i, rfl⟩ := hy; exact hx i
    haveI : NumberField (adjoin ℚ (Set.range x)) := {}
    Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))
      ^ ((finrank ℚ (adjoin ℚ (Set.range x)) : ℝ))⁻¹
  else 1

/-- The **absolute logarithmic height** of a tuple of algebraic numbers. -/
@[expose] noncomputable def absLogHeight (x : ι → K) : ℝ := Real.log (absMulHeight x)

end Def

section RingEquiv

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] {ι : Type*} [Finite ι]

end RingEquiv

section FieldOfDefinition

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Finite ι]

end FieldOfDefinition

section NumberFieldBase

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

end NumberFieldBase

section Comp

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] {ι : Type*} [Finite ι]

end Comp

section ArakelovComp

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
variable {κ : Type*} [Fintype κ]

end ArakelovComp

section Basic

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Finite ι]

end Basic

end NumberField

namespace Projectivization

open NumberField Real

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Finite ι]

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/-- The absolute multiplicative height of a point of projective space over a field of algebraic
numbers. -/
noncomputable def absMulHeight (x : Projectivization K (ι → K)) : ℝ := by
  let nativeSource84 := (open Function IntermediateField Module in (fun      {E : IntermediateField ℚ K} [NumberField E] {x : ι → K}
        (hx : ∀ i, x i ∈ E) => (show NumberField.absMulHeight x = Height.mulHeight (fun i ↦ (⟨x i, hx i⟩ : E)) ^ ((finrank ℚ E : ℝ))⁻¹ from by
      classical
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
      let HeightSourceField := adjoin ℚ (Set.range x)
      let nativeSource73 := (open Finset Function Height InfinitePlace Module in (fun      (x : ι → HeightSourceField) => (show ∃ (d : HeightSourceField) (y : ι → 𝓞 HeightSourceField), d ≠ 0 ∧ ∀ i, (y i : HeightSourceField) = d * x i from by
          classical
          have := Fintype.ofFinite ι
          obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 HeightSourceField))
            (Finset.univ : Finset ι) x
          refine ⟨Algebra.algebraMap (𝓞 HeightSourceField) HeightSourceField (b : 𝓞 HeightSourceField), fun i ↦ (hb i (Finset.mem_univ i)).choose, ?_, fun i ↦ ?_⟩
          · exact (map_ne_zero_iff _ (NumberField.RingOfIntegers.coe_injective)).mpr
              (nonZeroDivisors.coe_ne_zero b)
          · have h := (hb i (Finset.mem_univ i)).choose_spec
            rw [show (((hb i (Finset.mem_univ i)).choose : 𝓞 HeightSourceField) : HeightSourceField)
              = Algebra.algebraMap (𝓞 HeightSourceField) HeightSourceField (hb i (Finset.mem_univ i)).choose from rfl, h, Algebra.smul_def])))
      let nativeSource74 := (open Finset Function Height InfinitePlace Module in (fun          {y : ι → 𝓞 HeightSourceField} (hy : y ≠ 0) => (show ∏ᶠ w : NumberField.FinitePlace E, ⨆ i, w (algebraMap HeightSourceField E (y i : HeightSourceField)) =
              (∏ᶠ v : NumberField.FinitePlace HeightSourceField, ⨆ i, v (y i : HeightSourceField)) ^ Module.finrank HeightSourceField E from by
          classical
          have hinj : Function.Injective (algebraMap (𝓞 HeightSourceField) (𝓞 E)) :=
            NumberField.RingOfIntegers.algebraMap.injective HeightSourceField E
          have hy' : (fun i ↦ algebraMap (𝓞 HeightSourceField) (𝓞 E) (y i)) ≠ 0 := by
            obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
            exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
          have hspan : Ideal.span (Set.range fun i ↦ algebraMap (𝓞 HeightSourceField) (𝓞 E) (y i)) =
              (Ideal.span (Set.range y)).map (algebraMap (𝓞 HeightSourceField) (𝓞 E)) := by
            rw [Ideal.map_span, ← Set.range_comp]
            rfl
          have hK := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy
          have hL := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy'
          rw [hspan, ← Ideal.absNorm_relNorm (𝓞 HeightSourceField), Ideal.relNorm_algebraMap, map_pow,
            ← IsFractionRing.finrank_eq (𝓞 HeightSourceField) HeightSourceField (𝓞 E) E] at hL
          have hcoe (a : 𝓞 HeightSourceField) :
              ((algebraMap (𝓞 HeightSourceField) (𝓞 E) a : 𝓞 E) : E) = algebraMap HeightSourceField E (a : HeightSourceField) := by
            rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
              ← IsScalarTower.algebraMap_apply (𝓞 HeightSourceField) (𝓞 E) E,
              ← IsScalarTower.algebraMap_apply (𝓞 HeightSourceField) HeightSourceField E]
          simp_rw [hcoe] at hL
          have hN : ((Ideal.span (Set.range y)).absNorm : ℝ) ≠ 0 := by
            have : Ideal.span (Set.range y) ≠ ⊥ := by
              obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
              exact fun h ↦ hi (by simpa using (Ideal.span_eq_bot.mp h) (y i) ⟨i, rfl⟩)
            exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr this
          refine mul_left_cancel₀ (pow_ne_zero (Module.finrank HeightSourceField E) hN) ?_
          rw [← mul_pow, hK, one_pow]
          exact_mod_cast hL)))
      let nativeSource75 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun        (ψ : HeightSourceField →+* ℂ) => (show #{φ : E →+* ℂ | φ.comp (Algebra.algebraMap HeightSourceField E) = ψ} = Module.finrank HeightSourceField E from by
          classical
          letI : CharZero HeightSourceField := NumberField.to_charZero
          letI : Algebra.IsIntegral HeightSourceField E := Algebra.IsIntegral.of_finite HeightSourceField E
          letI : Algebra.IsSeparable HeightSourceField E := Algebra.IsSeparable.of_integral HeightSourceField E
          let : Algebra HeightSourceField ℂ := ψ.toAlgebra
          rw [← AlgHom.card HeightSourceField E ℂ]
          refine (Finset.card_nbij AlgHom.toRingHom (fun σ _ ↦ ?_) (fun σ _ τ _ h => AlgHom.ext fun x => DFunLike.congr_fun h x)
            (fun φ hφ ↦ ?_)).symm
          · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and]
            ext r
            exact σ.commutes r
          · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hφ
            exact ⟨⟨φ, fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← hφ]⟩, mem_univ _, rfl⟩))))
      let nativeSource76 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun        (F : (HeightSourceField →+* ℂ) → ℝ) => (show ∏ φ : E →+* ℂ, F (φ.comp (algebraMap HeightSourceField E)) = (∏ ψ : HeightSourceField →+* ℂ, F ψ) ^ Module.finrank HeightSourceField E from by
          classical
          rw [← Finset.prod_fiberwise Finset.univ (fun φ : E →+* ℂ ↦ φ.comp (algebraMap HeightSourceField E))
            (fun φ ↦ F (φ.comp (algebraMap HeightSourceField E))), ← Finset.prod_pow]
          refine Finset.prod_congr rfl fun ψ _ ↦ ?_
          rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
            Finset.prod_const, nativeSource75]))))
      let nativeSource77Source := (open Finset Function Height InfinitePlace Module in (fun      (f : NumberField.InfinitePlace HeightSourceField → ℝ) => (show ∏ φ : HeightSourceField →+* ℂ, f (NumberField.InfinitePlace.mk φ) = ∏ w : NumberField.InfinitePlace HeightSourceField, f w ^ w.mult from by
          classical
          classical
          rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk (fun φ ↦ f (NumberField.InfinitePlace.mk φ))]
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
            Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq])))
      let nativeSource77Target := (open Finset Function Height InfinitePlace Module in (fun      (f : NumberField.InfinitePlace E → ℝ) => (show ∏ φ : E →+* ℂ, f (NumberField.InfinitePlace.mk φ) = ∏ w : NumberField.InfinitePlace E, f w ^ w.mult from by
          classical
          classical
          rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk (fun φ ↦ f (NumberField.InfinitePlace.mk φ))]
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
            Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq])))
      let nativeSource78 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun        (f : NumberField.InfinitePlace HeightSourceField → ℝ) (g : NumberField.InfinitePlace E → ℝ)
            (h : ∀ φ : E →+* ℂ, g (NumberField.InfinitePlace.mk φ) = f (NumberField.InfinitePlace.mk (φ.comp (Algebra.algebraMap HeightSourceField E)))) => (show ∏ w : NumberField.InfinitePlace E, g w ^ w.mult = (∏ v : NumberField.InfinitePlace HeightSourceField, f v ^ v.mult) ^ Module.finrank HeightSourceField E from by
          classical
          rw [← nativeSource77Target g, ← nativeSource77Source f,
            ← nativeSource76 (fun ψ ↦ f (NumberField.InfinitePlace.mk ψ))]
          exact Finset.prod_congr rfl fun φ _ ↦ h φ))))
      let nativeSource79 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun          (x : ι → HeightSourceField) => (show ∏ w : NumberField.InfinitePlace E, (⨆ i, w (Algebra.algebraMap HeightSourceField E (x i))) ^ w.mult =
              (∏ v : NumberField.InfinitePlace HeightSourceField, (⨆ i, v (x i)) ^ v.mult) ^ Module.finrank HeightSourceField E from by
          classical
          exact (
            nativeSource78 _ _ fun φ ↦ iSup_congr fun i ↦ by simp [InfinitePlace.apply]
          )))))
      let nativeSource80 := (open Finset Function Height InfinitePlace Module in (fun          (y : ι → 𝓞 HeightSourceField) => (show Height.mulHeight (fun i ↦ (y i : HeightSourceField)) ^ Module.finrank HeightSourceField E
              = Height.mulHeight (fun i ↦ algebraMap HeightSourceField E (y i : HeightSourceField)) from by
          classical
          rcases eq_or_ne y 0 with rfl | hy
          · simp
          have hz : (fun i ↦ (y i : HeightSourceField)) ≠ 0 := by
            obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
            exact Function.ne_iff.mpr ⟨i, by simpa using hi⟩
          have hz' : (fun i ↦ algebraMap HeightSourceField E (y i : HeightSourceField)) ≠ 0 := by
            obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
            exact Function.ne_iff.mpr ⟨i, fun h ↦ hi ((algebraMap HeightSourceField E).injective
              (by simpa using h))⟩
          rw [NumberField.mulHeight_eq hz, NumberField.mulHeight_eq hz', mul_pow,
            nativeSource79, nativeSource74 hy])))
      let nativeSource81 := (open Finset Function Height InfinitePlace Module in (fun          (x : ι → HeightSourceField) => (show Height.mulHeight x ^ Module.finrank HeightSourceField E = Height.mulHeight (algebraMap HeightSourceField E ∘ x) from by
          classical
          obtain ⟨d, y, hd, hy⟩ := nativeSource73 x
          have hd' : algebraMap HeightSourceField E d ≠ 0 :=
            (map_ne_zero_iff _ ((algebraMap HeightSourceField E).injective)).mpr hd
          have h1 : (fun i ↦ (y i : HeightSourceField)) = d • x := funext fun i ↦ by rw [hy i]; rfl
          have h2 : (fun i ↦ algebraMap HeightSourceField E (y i : HeightSourceField)) = algebraMap HeightSourceField E d • (algebraMap HeightSourceField E ∘ x) := by
            funext i
            simp [hy i]
          have e1 : Height.mulHeight (fun i ↦ (y i : HeightSourceField)) = Height.mulHeight x :=
            h1 ▸ Height.mulHeight_smul_eq_mulHeight x hd
          have e2 : Height.mulHeight (fun i ↦ algebraMap HeightSourceField E (y i : HeightSourceField))
              = Height.mulHeight (algebraMap HeightSourceField E ∘ x) :=
            h2 ▸ Height.mulHeight_smul_eq_mulHeight _ hd'
          rw [← e1, ← e2]
          exact nativeSource80 y)))
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
  let nativeSource94 := (open Function IntermediateField Module in (open scoped Classical in (fun      (x : ι → K) {c : K} (hc : c ≠ 0) (hc' : IsAlgebraic ℚ c) => (show NumberField.absMulHeight (c • x) = NumberField.absMulHeight x from by
      classical
      by_cases hx : ∀ i, IsIntegral ℚ (x i)
      · have hfin : (insert c (Set.range x)).Finite := (Set.finite_range x).insert c
        have := hfin.to_subtype
        have hfd : FiniteDimensional ℚ (adjoin ℚ (insert c (Set.range x))) :=
          finiteDimensional_adjoin fun y hy ↦ by
            rcases hy with rfl | ⟨i, rfl⟩
            · exact hc'.isIntegral
            · exact hx i
        have : NumberField (adjoin ℚ (insert c (Set.range x))) := {}
        have hcE : c ∈ adjoin ℚ (insert c (Set.range x)) := subset_adjoin ℚ _ (Set.mem_insert _ _)
        have hxE : ∀ i, x i ∈ adjoin ℚ (insert c (Set.range x)) := fun i ↦
          subset_adjoin ℚ _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
        have hcxE : ∀ i, (c • x) i ∈ adjoin ℚ (insert c (Set.range x)) := fun i ↦ mul_mem hcE (hxE i)
        have hsmul : (fun i ↦ (⟨(c • x) i, hcxE i⟩ : adjoin ℚ (insert c (Set.range x))))
            = (⟨c, hcE⟩ : adjoin ℚ (insert c (Set.range x))) •
              fun i ↦ (⟨x i, hxE i⟩ : adjoin ℚ (insert c (Set.range x))) := by
          funext i
          exact Subtype.ext rfl
        rw [nativeSource84 hcxE, nativeSource84 hxE, hsmul,
          Height.mulHeight_smul_eq_mulHeight _ (fun h ↦ hc (congrArg Subtype.val h))]
      · unfold NumberField.absMulHeight
        rw [dif_neg hx, dif_neg (show ¬ ∀ i, IsIntegral ℚ ((c • x) i) from by
          intro h
          refine hx fun i ↦ ?_
          have hxi : x i = c⁻¹ * (c * x i) := by field_simp
          rw [hxi]
          exact hc'.inv.isIntegral.mul (h i))]))))
  let nativeSource113 := (open NumberField Real in (fun       (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) => (show NumberField.absMulHeight a.val = NumberField.absMulHeight b.val from by
      classical
      exact (
        have ht : t ≠ 0 := by
          contrapose! h
          simpa [h] using a.prop
        h ▸ nativeSource94 _ ht (Algebra.IsAlgebraic.isAlgebraic t)
      ))))
  exact x.lift (fun r => NumberField.absMulHeight r.val) nativeSource113

/-- The absolute logarithmic height of a point of projective space over a field of algebraic
numbers. -/
noncomputable def absLogHeight (x : Projectivization K (ι → K)) : ℝ := Real.log (absMulHeight x)

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `NumberField.absMulHeight` is always positive. -/
@[positivity NumberField.absMulHeight _]
meta def evalAbsMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.absMulHeight $K $KF $KCZ $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q((
      let nativeSource88 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 1 ≤ NumberField.absMulHeight x from by
        classical
        by_cases hx : ∀ i, IsIntegral ℚ (x i)
        · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range (x))) :=
            IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
              obtain ⟨i, rfl⟩ := hy
              exact hx i
          haveI : NumberField (IntermediateField.adjoin ℚ (Set.range (x))) := {}
          rw [NumberField.absMulHeight, dif_pos hx]
          exact Real.one_le_rpow (Height.one_le_mulHeight _) (by positivity)
        · rw [NumberField.absMulHeight, dif_neg hx])));
      let nativeSource93 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 0 < NumberField.absMulHeight x from by
        classical
        exact (
          zero_lt_one.trans_le <| nativeSource88 x
        ))));
      nativeSource93 $a)))
  | _, _, _ => throwError "not NumberField.absMulHeight"

/-- Extension for the `positivity` tactic: `NumberField.absLogHeight` is always nonnegative. -/
@[positivity NumberField.absLogHeight _]
meta def evalAbsLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.absLogHeight $K $KF $KCZ $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q((
      let nativeSource88 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 1 ≤ NumberField.absMulHeight x from by
        classical
        by_cases hx : ∀ i, IsIntegral ℚ (x i)
        · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range (x))) :=
            IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
              obtain ⟨i, rfl⟩ := hy
              exact hx i
          haveI : NumberField (IntermediateField.adjoin ℚ (Set.range (x))) := {}
          rw [NumberField.absMulHeight, dif_pos hx]
          exact Real.one_le_rpow (Height.one_le_mulHeight _) (by positivity)
        · rw [NumberField.absMulHeight, dif_neg hx])));
      let nativeSource89 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 0 ≤ NumberField.absLogHeight x from by
        classical
        exact (
          Real.log_nonneg <| nativeSource88 x
        ))));
      nativeSource89 $a)))
  | _, _, _ => throwError "not NumberField.absLogHeight"

/-- Extension for the `positivity` tactic: `Projectivization.absMulHeight` is always positive. -/
@[positivity Projectivization.absMulHeight _]
meta def evalProjAbsMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Projectivization.absMulHeight $K $KF $KCZ $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q((
      let nativeSource88 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 1 ≤ NumberField.absMulHeight x from by
        classical
        by_cases hx : ∀ i, IsIntegral ℚ (x i)
        · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range (x))) :=
            IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
              obtain ⟨i, rfl⟩ := hy
              exact hx i
          haveI : NumberField (IntermediateField.adjoin ℚ (Set.range (x))) := {}
          rw [NumberField.absMulHeight, dif_pos hx]
          exact Real.one_le_rpow (Height.one_le_mulHeight _) (by positivity)
        · rw [NumberField.absMulHeight, dif_neg hx])));
      let nativeSource117 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] [instSource3 : Algebra.IsAlgebraic ℚ K] {ι : Type _} [instSource5 : Finite ι] (x : Projectivization K (ι → K)) => (show 1 ≤ Projectivization.absMulHeight x from by
        classical
        rw [← x.mk_rep]
        change 1 ≤ NumberField.absMulHeight x.rep
        exact nativeSource88 _)));
      let nativeSource121 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] [instSource3 : Algebra.IsAlgebraic ℚ K] {ι : Type _} [instSource5 : Finite ι] (x : Projectivization K (ι → K)) => (show 0 < Projectivization.absMulHeight x from by
        classical
        exact (
          zero_lt_one.trans_le <| nativeSource117 x
        ))));
      nativeSource121 $a)))
  | _, _, _ => throwError "not Projectivization.absMulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.absLogHeight` is always
nonnegative. -/
@[positivity Projectivization.absLogHeight _]
meta def evalProjAbsLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Projectivization.absLogHeight $K $KF $KCZ $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q((
      let nativeSource88 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show 1 ≤ NumberField.absMulHeight x from by
        classical
        by_cases hx : ∀ i, IsIntegral ℚ (x i)
        · haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range (x))) :=
            IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
              obtain ⟨i, rfl⟩ := hy
              exact hx i
          haveI : NumberField (IntermediateField.adjoin ℚ (Set.range (x))) := {}
          rw [NumberField.absMulHeight, dif_pos hx]
          exact Real.one_le_rpow (Height.one_le_mulHeight _) (by positivity)
        · rw [NumberField.absMulHeight, dif_neg hx])));
      let nativeSource115 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] [instSource3 : Algebra.IsAlgebraic ℚ K] {ι : Type _} [instSource5 : Finite ι] (x : Projectivization K (ι → K)) => (show Projectivization.absLogHeight x = log (Projectivization.absMulHeight x) from by
        classical
        rw [← x.mk_rep]
        change NumberField.absLogHeight x.rep = Real.log (NumberField.absMulHeight x.rep)
        rfl)));
      let nativeSource117 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] [instSource3 : Algebra.IsAlgebraic ℚ K] {ι : Type _} [instSource5 : Finite ι] (x : Projectivization K (ι → K)) => (show 1 ≤ Projectivization.absMulHeight x from by
        classical
        rw [← x.mk_rep]
        change 1 ≤ NumberField.absMulHeight x.rep
        exact nativeSource88 _)));
      let nativeSource118 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] [instSource3 : Algebra.IsAlgebraic ℚ K] {ι : Type _} [instSource5 : Finite ι] (x : Projectivization K (ι → K)) => (show 0 ≤ Projectivization.absLogHeight x from by
        classical
        rw [nativeSource115]
        exact log_nonneg (nativeSource117 x))));
      nativeSource118 $a)))
  | _, _, _ => throwError "not Projectivization.absLogHeight"

end Mathlib.Meta.Positivity

namespace NumberField

section Examples

open Function IntermediateField Module

end Examples

end NumberField

end

public section

open FractionalIdeal Module
open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] {ι : Type*}

/-- **A finitely generated module over a Dedekind domain has a pseudo-basis.** -/
theorem Submodule.exists_pseudoBasis [Finite ι] : ∀ (k : ℕ) (M : Submodule A (ι → K)), M.FG →
    finrank K (Submodule.span K (M : Set (ι → K))) = k →
    ∃ (y : Fin k → (ι → K)) (𝔞 : Fin k → FractionalIdeal A⁰ K),
      LinearIndependent K y ∧ (∀ i, 𝔞 i ≠ 0) ∧
      (∀ x, x ∈ M ↔ ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  intro k
  induction k with
  | zero =>
    intro M hM hk
    have hbot : Submodule.span K (M : Set (ι → K)) = ⊥ := Submodule.finrank_eq_zero.1 hk
    refine ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, linearIndependent_empty_type,
      fun i ↦ i.elim0, fun x ↦ ?_⟩
    constructor
    · intro hx
      refine ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
      have hx' : x ∈ Submodule.span K (M : Set (ι → K)) := Submodule.subset_span hx
      rw [hbot, Submodule.mem_bot] at hx'
      simp [hx']
    · rintro ⟨c, -, rfl⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact M.zero_mem
  | succ k ih =>
    intro M hM hk
    -- a nonzero element of M
    have hne : ∃ m ∈ M, m ≠ 0 := by
      by_contra h
      push Not at h
      have : Submodule.span K (M : Set (ι → K)) = ⊥ := Submodule.span_eq_bot.2 (fun x hx ↦ h x hx)
      rw [this] at hk
      simp at hk
    obtain ⟨m, hmM, hm0⟩ := hne
    obtain ⟨l, hl⟩ : ∃ l, m l ≠ 0 := by
      by_contra h
      push Not at h
      exact hm0 (funext h)
    set f : (ι → K) →ₗ[K] K := LinearMap.proj l with hf
    obtain ⟨y₀, 𝔞₀, h𝔞₀, hfy₀, hsmul, hfM⟩ := (fun (M : Submodule A (ι → K)) (hM : M.FG)
    (f : (ι → K) →ₗ[K] K) (hf : ∃ m ∈ M, f m ≠ 0) => (show ∃ (y : ι → K) (𝔞 : FractionalIdeal A⁰ K), 𝔞 ≠ 0 ∧ f y = 1 ∧
      (∀ c ∈ 𝔞, c • y ∈ M) ∧ (∀ x ∈ M, f x ∈ 𝔞) from by
  classical
  set I₀ : Submodule A K := Submodule.map (f.restrictScalars A) M with hI₀
  have hI₀fg : I₀.FG := hM.map _
  set 𝔞 : FractionalIdeal A⁰ K := ⟨I₀, isFractional_of_fg hI₀fg⟩ with h𝔞
  have hmem𝔞 : ∀ z : K, z ∈ 𝔞 ↔ z ∈ I₀ := fun _ ↦ Iff.rfl
  have h𝔞ne : 𝔞 ≠ 0 := by
    obtain ⟨m, hm, hfm⟩ := hf
    intro h
    apply hfm
    have : f m ∈ 𝔞 := (hmem𝔞 _).2 ⟨m, hm, rfl⟩
    rw [h] at this
    simpa using this
  obtain ⟨s, a, b, ha, hb, hab⟩ := (fun (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) => (show ∃ (s : Finset K) (a b : K → K), (∀ x ∈ s, a x ∈ I) ∧ (∀ x ∈ s, b x ∈ I⁻¹) ∧
      ∑ x ∈ s, a x * b x = 1 from by
  classical
  have h1 : (1 : K) ∈ (I * I⁻¹ : FractionalIdeal A⁰ K) := by
    rw [mul_inv_cancel₀ hI]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul,
    Submodule.mul_eq_span_mul_set, Submodule.mem_span_set] at h1
  obtain ⟨c, hc, hsum⟩ := h1
  have hmem : ∀ x ∈ c.support, ∃ p q : K, p ∈ I ∧ q ∈ I⁻¹ ∧ p * q = x := by
    intro x hx
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.1 (hc hx)
    exact ⟨p, q, hp, hq, hpq⟩
  choose! p q hp hq hpq using hmem
  refine ⟨c.support, fun x ↦ c x • p x, q, fun x hx ↦ ?_, fun x hx ↦ hq x hx, ?_⟩
  · exact (I : Submodule A K).smul_mem _ (hp x hx)
  · rw [← hsum, Finsupp.sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [smul_mul_assoc, hpq x hx])) 𝔞 h𝔞ne
  have hpre : ∀ x ∈ s, ∃ m ∈ M, f m = a x := fun x hx ↦ ha x hx
  choose! m hmM hfm using hpre
  refine ⟨∑ x ∈ s, b x • m x, 𝔞, h𝔞ne, ?_, ?_, fun x hx ↦ (hmem𝔞 _).2 ⟨x, hx, rfl⟩⟩
  · rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [← hab]
    exact Finset.sum_congr rfl fun x hx ↦ by rw [hfm x hx, mul_comm]
  · intro c hc
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun x hx ↦ ?_
    have hone : c * b x ∈ (1 : FractionalIdeal A⁰ K) := by
      rw [← mul_inv_cancel₀ h𝔞ne]
      exact FractionalIdeal.mul_mem_mul hc (hb x hx)
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hone
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hmM x hx))) M hM f ⟨m, hmM, hl⟩
    set M' : Submodule A (ι → K) := M ⊓ (LinearMap.ker f).restrictScalars A with hM'
    have hM'le : M' ≤ M := inf_le_left
    have hM'fg : M'.FG := by
      have hN : IsNoetherian A ↥M := isNoetherian_of_fg_of_noetherian M hM
      have h1 : (M'.comap M.subtype).FG := IsNoetherian.noetherian _
      have h2 : M' = Submodule.map M.subtype (M'.comap M.subtype) :=
        (Submodule.map_comap_eq_self (by simpa using hM'le)).symm
      rw [h2]
      exact h1.map _
    have hspanM' : Submodule.span K (M' : Set (ι → K))
        = Submodule.span K (M : Set (ι → K)) ⊓ LinearMap.ker f := by
      refine le_antisymm (Submodule.span_le.2 ?_) ?_
      · rintro x ⟨hxM, hxk⟩
        exact ⟨Submodule.subset_span hxM, hxk⟩
      · rintro v ⟨hv1, hv2⟩
        obtain ⟨d, hdSpan⟩ :=
          _root_.multiple_mem_span_of_mem_localization_span A⁰ K
            (M : Set (ι → K)) v hv1
        have hd : (d : A) • v ∈ M := by
          simpa only [Submodule.span_eq, Submonoid.smul_def] using hdSpan
        have hdK : (algebraMap A K (d : A)) ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
        have hfv : f v = 0 := hv2
        have hdM' : ((d : A) • v) ∈ M' := by
          refine Submodule.mem_inf.2 ⟨hd, ?_⟩
          rw [Submodule.restrictScalars_mem, LinearMap.mem_ker,
            ← algebraMap_smul (R := A) K (d : A) v, map_smul, hfv, smul_zero]
        have hvv : v = (algebraMap A K (d : A))⁻¹ • ((d : A) • v) := by
          rw [← algebraMap_smul (R := A) K (d : A) v, inv_smul_smul₀ hdK]
        rw [hvv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hdM')
    have hrank' : finrank K (Submodule.span K (M' : Set (ι → K))) = k := by
      set W := Submodule.span K (M : Set (ι → K)) with hW
      set g : W →ₗ[K] K := f.domRestrict W with hg
      have hsurj : LinearMap.range g = ⊤ := by
        refine LinearMap.range_eq_top.2 ?_
        intro z
        refine ⟨(z / f m) • ⟨m, Submodule.subset_span hmM⟩, ?_⟩
        simp only [hg, LinearMap.domRestrict_apply, map_smul]
        have hfm : f m ≠ 0 := hl
        rw [smul_eq_mul, div_mul_cancel₀ _ hfm]
      have h1 := LinearMap.finrank_range_add_finrank_ker g
      rw [hsurj, finrank_top, Module.finrank_self] at h1
      have h2 : finrank K ↥(LinearMap.ker g) = k := by omega
      have hkerg : LinearMap.ker g = Submodule.comap W.subtype (LinearMap.ker f) := rfl
      have h3 : Submodule.map W.subtype (LinearMap.ker g) = W ⊓ LinearMap.ker f := by
        rw [hkerg]; exact Submodule.map_comap_subtype W (LinearMap.ker f)
      have h4 : finrank K ↥(Submodule.map W.subtype (LinearMap.ker g))
          = finrank K ↥(LinearMap.ker g) :=
        (Submodule.equivMapOfInjective W.subtype W.injective_subtype
          (LinearMap.ker g)).finrank_eq.symm
      rw [hspanM', ← h3, h4, h2]
    obtain ⟨y', 𝔞', hli', h𝔞', hchar'⟩ := ih M' hM'fg hrank'
    have hy'ker : ∀ i, f (y' i) = 0 := by
      intro i
      obtain ⟨a, ha, ha0⟩ : ∃ a ∈ 𝔞' i, a ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact h𝔞' i (FractionalIdeal.eq_zero_iff.2 hcon)
      have hmem : a • y' i ∈ M' := by
        refine (hchar' _).2 ⟨Pi.single i a, fun j ↦ ?_, ?_⟩
        · rcases eq_or_ne j i with rfl | hj
          · simpa using ha
          · simp [hj, (𝔞' j).zero_mem]
        · rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [hj]
          · simp
      have : f (a • y' i) = 0 := hmem.2
      rw [map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left ha0
    have hy₀notin : y₀ ∉ Submodule.span K (Set.range y') := by
      intro hcon
      have hle : Submodule.span K (Set.range y') ≤ LinearMap.ker f :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hy'ker i)
      have : f y₀ = 0 := hle hcon
      rw [hfy₀] at this
      exact one_ne_zero this
    refine ⟨Fin.cons y₀ y', Fin.cons 𝔞₀ 𝔞', linearIndependent_finCons.2 ⟨hli', hy₀notin⟩,
      fun i ↦ Fin.cases h𝔞₀ h𝔞' i, fun x ↦ ?_⟩
    constructor
    · intro hx
      have hc₀ : f x ∈ 𝔞₀ := hfM x hx
      have hrest : x - (f x) • y₀ ∈ M' := by
        refine Submodule.mem_inf.2 ⟨M.sub_mem hx (hsmul _ hc₀), ?_⟩
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul,
          hfy₀, mul_one, sub_self]
      obtain ⟨c', hc', heq⟩ := (hchar' _).1 hrest
      refine ⟨Fin.cons (f x) c', fun i ↦ Fin.cases hc₀ hc' i, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← heq]
      abel
    · rintro ⟨c, hc, rfl⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      refine M.add_mem (hsmul _ (by simpa using hc 0)) (hM'le ((hchar' _).2 ⟨fun i ↦ c i.succ,
        fun i ↦ by simpa using hc i.succ, rfl⟩))

end
