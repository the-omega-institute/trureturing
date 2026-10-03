/- GID: D5/S3/Factorization/Galois/GoldenCubicBlockPositiveRootTower
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicBlockPositiveRootTower
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Positive real Lucas-block roots generate a complex tower of cubic stages. -/

import D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower

open D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
open D5.S1.Scale

noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The concrete copy of the cubic cyclotomic field in the complex numbers. -/
noncomputable abbrev ComplexBase : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {omega}

/-- The designated positive real cube root, viewed in `ℂ`. -/
noncomputable def positiveRoot (j : ℕ) : ℂ :=
  ((block j : ℝ) ^ ((3 : ℝ)⁻¹) : ℝ)

noncomputable def rootSet (J : ℕ) : Set ℂ :=
  {z | ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ z = positiveRoot j}

/-- Section 26's fields `ℚ(ω)(β₁,…,β_J)`, with each `β_j` the positive real
cube root of the actual Lucas block. -/
noncomputable def complexTower (J : ℕ) : IntermediateField ComplexBase ℂ :=
  IntermediateField.adjoin ComplexBase (rootSet J)

/-- The concrete positive-root tower has one cubic degree increase per block. -/
theorem golden_cubic_block_positive_root_tower_degree (J : ℕ) :
    Module.finrank ComplexBase (complexTower J) = 3 ^ J := by
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ Base :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hω : IsPrimitiveRoot omega 3 :=
    Complex.isPrimitiveRoot_exp 3 (by decide)
  letI : IsCyclotomicExtension {3} ℚ ComplexBase :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      3 ℚ ℂ ComplexBase hω).2 rfl
  let e : Base ≃ₐ[ℚ] ComplexBase :=
    IsCyclotomicExtension.algEquiv {3} ℚ Base ComplexBase
  let i : Base →ₐ[ℚ] ℂ := ComplexBase.val.comp e.toAlgHom
  letI : Algebra Base ℂ := i.toRingHom.toAlgebra
  letI : IsScalarTower ℚ Base ℂ := IsScalarTower.of_algHom i
  let f : Ambient →ₐ[Base] ℂ := IsAlgClosed.lift
  let ζ : Base := IsCyclotomicExtension.zeta 3 ℚ Base
  have hζ : IsPrimitiveRoot (algebraMap Base ℂ ζ) 3 :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ Base).map_of_injective
      (algebraMap Base ℂ).injective
  have hblock0 (j : ℕ) : (block j : ℂ) ≠ 0 := by
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
  have hroot_mem (x y b : ℂ) (hx : x ^ 3 = b) (hy : y ^ 3 = b)
      (hb : b ≠ 0) : x ∈ IntermediateField.adjoin Base {y} := by
    have hy0 : y ≠ 0 := by
      intro hy0
      exact hb (hy.symm.trans (by simp [hy0]))
    have hratio : (x / y) ^ 3 = 1 := by
      rw [div_pow, hx, hy, div_self hb]
    obtain ⟨k, _, hk⟩ := hζ.eq_pow_of_pow_eq_one hratio
    have hbase : (algebraMap Base ℂ ζ) ^ k ∈
        IntermediateField.adjoin Base {y} :=
      pow_mem (IntermediateField.algebraMap_mem _ ζ) k
    have hyfield : y ∈ IntermediateField.adjoin Base {y} :=
      IntermediateField.subset_adjoin Base {y} (Set.mem_singleton y)
    have hxy : x = (algebraMap Base ℂ ζ) ^ k * y := by
      calc
        x = (x / y) * y := (div_mul_cancel₀ _ hy0).symm
        _ = (algebraMap Base ℂ ζ) ^ k * y := by rw [hk]
    rw [hxy]
    exact mul_mem hbase hyfield
  have hsame (x y b : ℂ) (hx : x ^ 3 = b) (hy : y ^ 3 = b)
      (hb : b ≠ 0) :
      IntermediateField.adjoin Base {x} = IntermediateField.adjoin Base {y} := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hroot_mem x y b hx hy hb
    · apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hroot_mem y x b hy hx hb
  let roots : ℕ → Ambient := fun j =>
    Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (block j : Ambient) (by decide : 0 < 3))
  have hroots : ∀ j, 1 ≤ j → roots j ^ 3 = algebraMap Base Ambient (block j) := by
    intro j _
    exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (block j : Ambient) (by decide : 0 < 3))
  have hmaproot (j : ℕ) :
      IntermediateField.adjoin Base {f (roots j)} =
        IntermediateField.adjoin Base {positiveRoot j} := by
    apply hsame _ _ (block j : ℂ) _ (hpositive j) (hblock0 j)
    change (f (Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (block j : Ambient) (by decide : 0 < 3)))) ^ 3 = (block j : ℂ)
    rw [← map_pow, Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (block j : Ambient) (by decide : 0 < 3))]
    simp
  have hset_succ (m : ℕ) :
      rootSet (m + 1) = rootSet m ∪ {positiveRoot (m + 1)} := by
    ext z
    constructor
    · rintro ⟨j, hj, hjm, rfl⟩
      by_cases hle : j ≤ m
      · exact Or.inl ⟨j, hj, hle, rfl⟩
      · have heq : j = m + 1 := by omega
        exact Or.inr (by simp [heq])
    · rintro (⟨j, hj, hjm, rfl⟩ | hz)
      · exact ⟨j, hj, by omega, rfl⟩
      · have hz' : z = positiveRoot (m + 1) := Set.mem_singleton_iff.mp hz
        subst z
        exact ⟨m + 1, by omega, by omega, rfl⟩
  have hmap (m : ℕ) :
      (tower roots m).map f = IntermediateField.adjoin Base (rootSet m) := by
    induction m with
    | zero =>
        have hempty : rootSet 0 = ∅ := by
          ext z
          simp only [rootSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨j, hj, hj0, _⟩
          omega
        simp [tower, hempty, IntermediateField.map_bot]
    | succ m ih =>
        calc
          (tower roots (m + 1)).map f =
              (tower roots m).map f ⊔
                IntermediateField.adjoin Base {f (roots (m + 1))} := by
              rw [tower, IntermediateField.map_sup, IntermediateField.adjoin_map]
              simp
          _ = IntermediateField.adjoin Base (rootSet m) ⊔
                IntermediateField.adjoin Base {positiveRoot (m + 1)} := by
              rw [ih, hmaproot (m + 1)]
          _ = IntermediateField.adjoin Base (rootSet (m + 1)) := by
              rw [← IntermediateField.adjoin_union, ← hset_succ m]
  have hfin_base :
      Module.finrank Base (IntermediateField.adjoin Base (rootSet J)) = 3 ^ J := by
    rw [← hmap J, ← (IntermediateField.equivMap (tower roots J) f).toLinearEquiv.finrank_eq]
    exact golden_cubic_block_kummer_tower_degree roots hroots J
  have hi : (algebraMap Base ℂ) = (algebraMap ComplexBase ℂ) ∘ e := by
    funext x
    rfl
  have hfields :
      (IntermediateField.adjoin Base (rootSet J)).restrictScalars ℚ =
        (complexTower J).restrictScalars ℚ := by
    exact IntermediateField.restrictScalars_adjoin_of_algEquiv e hi (rootSet J)
  let j : (IntermediateField.adjoin Base (rootSet J)) ≃+* (complexTower J) :=
    (IntermediateField.equivOfEq hfields).toRingEquiv
  have hc : (algebraMap ComplexBase (complexTower J)).comp e.toRingEquiv.toRingHom =
      j.toRingHom.comp (algebraMap Base (IntermediateField.adjoin Base (rootSet J))) := by
    ext x
    exact (congrFun hi x).symm
  rw [← hfin_base]
  exact (Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv j hc).symm

end D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
