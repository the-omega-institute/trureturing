/- GID: D5/S3/Factorization/Galois/GoldenCubicBlockCoordinateActions
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicBlockCoordinateActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Galois cardinality realizes cubic coordinate actions and the actual tower is Galois with its positive-root generators. -/

import D5.S3.Factorization.MordellTwoAdicNonTorsion
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic
import D5.S3.Factorization.Mordell.SymmetricSquareAddition
import D5.S3.QuadraticForms.ParallelogramConstruction
import D5.S3.Factorization.Mordell.CanonicalPointHeight
import D5.S3.Factorization.Dedekind.GaloisScalarHeight
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import D5.S3.Factorization.Galois.GoldenCubicCommonInertiaAndSignature
import D5.S3.Factorization.Mordell.PointVariableChange
import D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
import D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range



set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Scale
open D5.S3.Factorization.MordellTwoAdicNonTorsion
open D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
open WeierstrassCurve
open Polynomial
open Height


namespace D5.S3.Factorization.Galois.GoldenCubicBlockCoordinateActions

theorem cubic_coordinate_automorphism
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (J : ℕ) (zeta : K) (hzeta : IsPrimitiveRoot zeta 3)
    (beta : Fin J → L) (hbeta0 : ∀ i, beta i ≠ 0)
    (hbetaCube : ∀ i, ∃ a : K, beta i ^ 3 = algebraMap K L a)
    (hgen : IntermediateField.adjoin K (Set.range beta) = ⊤)
    (hdegree : Module.finrank K L = 3 ^ J) :
    ∀ j : Fin J, ∃ sigma : L ≃ₐ[K] L,
      ∀ i : Fin J,
        sigma (beta i) =
          if i = j then algebraMap K L zeta * beta i else beta i := by
  classical
  let zetaL : L := algebraMap K L zeta
  have hzetaL : IsPrimitiveRoot zetaL 3 :=
    hzeta.map_of_injective (algebraMap K L).injective
  have hexp (sigma : L ≃ₐ[K] L) (i : Fin J) :
      ∃ e : Fin 3, sigma (beta i) = zetaL ^ e.val * beta i := by
    obtain ⟨a, ha⟩ := hbetaCube i
    have ha0 : algebraMap K L a ≠ 0 := by
      rw [← ha]
      exact pow_ne_zero _ (hbeta0 i)
    have hq : (sigma (beta i) / beta i) ^ 3 = 1 := by
      rw [div_pow, ← map_pow, ha, sigma.commutes, div_self ha0]
    obtain ⟨n, hn, hp⟩ := hzetaL.eq_pow_of_pow_eq_one hq
    refine ⟨⟨n, hn⟩, ?_⟩
    calc
      sigma (beta i) = (sigma (beta i) / beta i) * beta i :=
        (div_mul_cancel₀ _ (hbeta0 i)).symm
      _ = zetaL ^ n * beta i := by rw [← hp]
  let coord (sigma : L ≃ₐ[K] L) (i : Fin J) : Fin 3 :=
    Classical.choose (hexp sigma i)
  have hcoord (sigma : L ≃ₐ[K] L) (i : Fin J) :
      sigma (beta i) = zetaL ^ (coord sigma i).val * beta i :=
    Classical.choose_spec (hexp sigma i)
  have hinj : Function.Injective coord := by
    intro sigma tau heq
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ IntermediateField.adjoin K (Set.range beta) := by
      rw [hgen]
      exact Set.mem_univ x
    refine IntermediateField.adjoin_induction K
      (p := fun y _ => sigma y = tau y)
      (fun y hy => ?_) (fun a => by simp)
      (fun a b _ _ ha hb => by simp [ha, hb])
      (fun a _ ha => by simp [ha])
      (fun a b _ _ ha hb => by simp [ha, hb]) hx
    obtain ⟨i, rfl⟩ := hy
    rw [hcoord sigma i, hcoord tau i, congrFun heq i]
  have hcard : Nat.card (L ≃ₐ[K] L) = Nat.card (Fin J → Fin 3) := by
    rw [IsGalois.card_aut_eq_finrank, hdegree]
    rw [Nat.card_fun, Nat.card_fin, Nat.card_fin]
  have hsurj : Function.Surjective coord :=
    ((Nat.bijective_iff_injective_and_card coord).2 ⟨hinj, hcard⟩).2
  intro j
  let basis : Fin J → Fin 3 := fun i => if i = j then 1 else 0
  obtain ⟨sigma, hsigma⟩ := hsurj basis
  refine ⟨sigma, ?_⟩
  intro i
  rw [hcoord sigma i, congrFun hsigma i]
  by_cases hij : i = j
  · simp [basis, hij, zetaL]
  · simp [basis, hij]


set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Scale
open D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
open D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
open Polynomial

theorem actual_complex_tower_galois_and_generators (J : ℕ) :
    IsGalois ComplexBase (complexTower J) ∧
      ∃ beta : Fin J → complexTower J,
        (∀ i, (beta i : ℂ) = positiveRoot (i.val + 1)) ∧
        IntermediateField.adjoin ComplexBase (Set.range beta) = ⊤ := by
  classical
  let K := ComplexBase
  let L := complexTower J
  have homegaMem : omega ∈ K :=
    IntermediateField.subset_adjoin ℚ {omega} (Set.mem_singleton omega)
  let zeta : K := ⟨omega, homegaMem⟩
  have hzeta : IsPrimitiveRoot zeta 3 := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := algebraMap K ℂ) (hf := (algebraMap K ℂ).injective)
    change IsPrimitiveRoot omega 3
    exact Complex.isPrimitiveRoot_exp 3 (by decide)
  have hblock0 (j : ℕ) : (block j : K) ≠ 0 := by
    have hpos : 0 < goldenLucas (3 ^ j) ^ 2 + (3 : ℤ) := by positivity
    have hn : block j ≠ 0 := by
      change (goldenLucas (3 ^ j) ^ 2 + 3).natAbs ≠ 0
      exact Int.natAbs_ne_zero.mpr hpos.ne'
    exact Nat.cast_ne_zero.mpr hn
  have hpositive (j : ℕ) : positiveRoot j ^ 3 = (block j : ℂ) := by
    change (((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) ^ 3 = (block j : ℂ)
    rw [← Complex.ofReal_pow]
    simpa using congrArg (fun x : ℝ => (x : ℂ))
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (block j))
        (by decide : (3 : ℕ) ≠ 0))
  have hsingle (j : ℕ) :
      IsGalois K (IntermediateField.adjoin K {positiveRoot j}) := by
    let T := IntermediateField.adjoin K {positiveRoot j}
    let beta : T := ⟨positiveRoot j,
      IntermediateField.subset_adjoin K {positiveRoot j} (Set.mem_singleton _)⟩
    have hcube : beta ^ 3 = algebraMap K T (block j : K) := by
      apply Subtype.ext
      simpa [beta, IntermediateField.coe_pow, IntermediateField.coe_algebraMap_apply]
        using hpositive j
    have hgen : IntermediateField.adjoin K {beta} = ⊤ := by
      apply (IntermediateField.lift_injective T)
      simp only [IntermediateField.lift_adjoin, Set.image_singleton,
        IntermediateField.lift_top]
      rfl
    let p : K[X] := X ^ 3 - C (block j : K)
    have hsplit : (p.map (algebraMap K T)).Splits := by
      simpa only [p, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C] using
        (X_pow_sub_C_splits_of_isPrimitiveRoot
          (hzeta.map_of_injective (algebraMap K T).injective) hcube)
    have hp0 : p ≠ 0 := X_pow_sub_C_ne_zero (by decide) (block j : K)
    letI : Module.IsTorsionFree K T :=
      DivisionSemiring.to_moduleIsTorsionFree
    have hroot : beta ∈ p.rootSet T := by
      rw [mem_rootSet_of_ne hp0]
      simp [p, aeval_def, hcube]
    have hrootGen : IntermediateField.adjoin K (p.rootSet T) = ⊤ := by
      apply top_unique
      have hle : IntermediateField.adjoin K {beta} ≤
          IntermediateField.adjoin K (p.rootSet T) :=
        IntermediateField.adjoin_le_iff.mpr (by
          intro x hx
          rw [Set.mem_singleton_iff.mp hx]
          exact IntermediateField.subset_adjoin K (p.rootSet T) hroot)
      simpa only [hgen] using hle
    have hpfield : p.IsSplittingField K T :=
      isSplittingField_iff_intermediateField.mpr ⟨hsplit, hrootGen⟩
    have hpsep : p.Separable := by
      dsimp [p]
      exact separable_X_pow_sub_C (block j : K)
        (by norm_num : (3 : K) ≠ 0) (hblock0 j)
    letI : p.IsSplittingField K T := hpfield
    exact IsGalois.of_separable_splitting_field hpsep
  have hrootSet :
      D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J =
      Set.range (fun i : Fin J => positiveRoot (i.val + 1)) := by
    ext z
    constructor
    · rintro ⟨j, hj, hjJ, rfl⟩
      refine ⟨⟨j - 1, by omega⟩, ?_⟩
      simpa [Nat.sub_add_cancel hj]
    · rintro ⟨i, rfl⟩
      exact ⟨i.val + 1, by omega, by omega, rfl⟩
  let layer : Fin J → IntermediateField K ℂ :=
    fun i => IntermediateField.adjoin K {positiveRoot (i.val + 1)}
  let composite : IntermediateField K ℂ := ⨆ i, layer i
  have hfields : L = composite := by
    change IntermediateField.adjoin K
      (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J) =
        ⨆ i, layer i
    rw [hrootSet]
    have hrange :
        Set.range (fun i : Fin J => positiveRoot (i.val + 1)) =
          ⋃ i : Fin J, {positiveRoot (i.val + 1)} := by
      ext z
      simp
    rw [hrange, IntermediateField.adjoin_iUnion]
  have hnormal : Normal K composite := by
    letI : ∀ i : Fin J, Normal K (layer i) :=
      fun i => (hsingle (i.val + 1)).to_normal
    change Normal K (↥((⨆ i, layer i) : IntermediateField K ℂ))
    infer_instance
  have hseparable : Algebra.IsSeparable K composite := by
    letI : ∀ i : Fin J, Algebra.IsSeparable K (layer i) :=
      fun i => (hsingle (i.val + 1)).to_isSeparable
    change Algebra.IsSeparable K (↥((⨆ i, layer i) : IntermediateField K ℂ))
    infer_instance
  have hgal : IsGalois K L := by
    rw [hfields]
    exact isGalois_iff.mpr ⟨hseparable, hnormal⟩
  let beta : Fin J → L := fun i =>
    ⟨positiveRoot (i.val + 1),
      IntermediateField.subset_adjoin K
        (D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J)
        ⟨i.val + 1, by omega, by omega, rfl⟩⟩
  have himage : Subtype.val '' Set.range beta =
      D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower.rootSet J := by
    rw [hrootSet]
    ext z
    constructor
    · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨beta i, ⟨i, rfl⟩, rfl⟩
  have hgen : IntermediateField.adjoin K (Set.range beta) = ⊤ := by
    apply (IntermediateField.lift_injective L)
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, himage]
    rfl
  exact ⟨hgal, beta, (fun _ => rfl), hgen⟩

end D5.S3.Factorization.Galois.GoldenCubicBlockCoordinateActions
