/- GID: D5/S3/Factorization/Galois/SquareRootArithmetic
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/SquareRootArithmetic
   mirror-E: none(waiver:source-candidate-only)
   anchors: []
   utility: none
   digest: Arithmetic Frobenius and odd-prime unramifiedness for actual square-root extensions. -/
/-
Copyright (c) 2026 The Tau Ceti contributors, Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in licenses/TauCeti-LICENSE.
Authors: The Tau Ceti contributors, Chris Birkbeck
Adapted from TauCetiProject/TauCeti at 14f2a0fe0892587f041a6ca7b6f6a05e31b1f65d.
The exact declaration-level source map accompanies this source candidate.
Receiving mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.
SOURCE ONLY: elaboration, kernel, axioms and admission have NOT_RUN status.
-/
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Polynomial IntermediateField Ideal NumberField
open scoped NumberField Pointwise
namespace D5.S3.Factorization.Galois.SquareRootArithmetic

section QuadraticFactor
variable {F E : Type*} [CommRing F] [CommRing E] [Algebra F E] {a : F} {δ : E}
private theorem splits_map_X_pow_two_sub_C (hδ : δ ^ 2 = algebraMap F E a) :
    (((X : F[X]) ^ 2 - C a).map (algebraMap F E)).Splits := by
  have hmap : ((X : F[X]) ^ 2 - C a).map (algebraMap F E) = (X - C δ) * (X - C (-δ)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hδ, map_pow, map_neg]
    ring
  rw [hmap]
  exact (Splits.X_sub_C δ).mul (Splits.X_sub_C (-δ))

end QuadraticFactor

section AdjoinGalois
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  [Finite ι] {d : ι → K} {root : ι → L}
private noncomputable def definingPolynomial (d : ι → K) : K[X] :=
  letI := Fintype.ofFinite ι
  ∏ i, (X ^ 2 - C (d i))

omit [Finite ι] in
/-- Each quadratic factor splits in `M`, with roots `± rootᵢ`. -/
private theorem splits_X_sq_sub_C (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    ((X ^ 2 - C (d i)).map (algebraMap K (adjoin K (Set.range root)))).Splits := by
  have hmem : root i ∈ adjoin K (Set.range root) := subset_adjoin _ _ ⟨i, rfl⟩
  have hy2 : (⟨root i, hmem⟩ : adjoin K (Set.range root)) ^ 2
      = algebraMap K (adjoin K (Set.range root)) (d i) := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, IntermediateField.coe_algebraMap_apply]
    exact hroot i
  exact splits_map_X_pow_two_sub_C hy2

/-- The `i`-th generator, as an element of the multiquadratic field `M`. -/
private noncomputable def gen (root : ι → L) (i : ι) : adjoin K (Set.range root) :=
  ⟨root i, subset_adjoin _ _ ⟨i, rfl⟩⟩

omit [Finite ι] in
/-- Coercing the `i`-th generator of `K(rootᵢ : i)` back to `L` gives `root i`. -/
private theorem coe_gen (i : ι) : (gen (K := K) root i : L) = root i := rfl

omit [Finite ι] in
/-- The generators generate `M` as its own top field. -/
private theorem adjoin_gen_eq_top :
    IntermediateField.adjoin K (Set.range (gen (K := K) root)) = ⊤ := by
  refine IntermediateField.map_injective (adjoin K (Set.range root)).val ?_
  have hmaptop : (⊤ : IntermediateField K (adjoin K (Set.range root))).map
      (adjoin K (Set.range root)).val = adjoin K (Set.range root) := by
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [IntermediateField.adjoin_map, hmaptop]
  congr 1
  rw [← Set.range_comp]
  rfl

omit [Finite ι] in
/-- The generator squares to its radicand (in `M`). -/
private theorem gen_sq (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    gen (K := K) root i ^ 2 = algebraMap K (adjoin K (Set.range root)) (d i) := by
  apply Subtype.ext
  rw [IntermediateField.coe_pow, coe_gen, IntermediateField.coe_algebraMap_apply]
  exact hroot i

/-- `∏ᵢ (X² - dᵢ)` is nonzero. -/
private theorem definingPolynomial_ne_zero : definingPolynomial d ≠ 0 := by
  rw [definingPolynomial, Finset.prod_ne_zero_iff]
  exact fun i _ => Polynomial.X_pow_sub_C_ne_zero (by norm_num) (d i)

/-- The defining polynomial splits over `M`. -/
private theorem splits_definingPolynomial (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    ((definingPolynomial d).map (algebraMap K (adjoin K (Set.range root)))).Splits := by
  rw [definingPolynomial, Polynomial.map_prod]
  exact Polynomial.Splits.prod fun i _ => splits_X_sq_sub_C hroot i

omit [Finite ι] in
/-- Each generator is algebraic over `K` (it satisfies `X² - dᵢ`). -/
private theorem isAlgebraic_gen (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    IsAlgebraic K (gen (K := K) root i) :=
  ⟨X ^ 2 - C (d i), X_pow_sub_C_ne_zero (by norm_num) _, by
    rw [map_sub, map_pow, aeval_X, aeval_C, gen_sq hroot i, sub_self]⟩

/-- `M = K(rootᵢ : i)` is the splitting field of `∏ᵢ (X² - dᵢ)` over `K`. -/
private theorem isSplittingField (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    (definingPolynomial d).IsSplittingField K (adjoin K (Set.range root)) where
  splits' := splits_definingPolynomial hroot
  adjoin_rootSet' := by
    let := Fintype.ofFinite ι
    have hsub : Set.range (gen (K := K) root) ⊆
        (definingPolynomial d).rootSet (adjoin K (Set.range root)) := by
      rintro _ ⟨i, rfl⟩
      rw [Polynomial.mem_rootSet]
      refine ⟨definingPolynomial_ne_zero, ?_⟩
      rw [definingPolynomial, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [map_sub, map_pow, aeval_X, aeval_C, gen_sq hroot i, sub_self])
    have halg : ∀ x ∈ Set.range (gen (K := K) root), IsAlgebraic K x := by
      rintro _ ⟨i, rfl⟩; exact isAlgebraic_gen hroot i
    refine le_antisymm le_top ?_
    rw [← Algebra.adjoin_eq_top_of_intermediateField halg (adjoin_gen_eq_top (root := root))]
    exact Algebra.adjoin_mono hsub

theorem squareRootAdjoin_isGalois [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    IsGalois K (adjoin K (Set.range root)) := by
  have := isSplittingField hroot
  have : Normal K (adjoin K (Set.range root)) := Normal.of_isSplittingField (definingPolynomial d)
  have : Algebra.IsSeparable K (adjoin K (Set.range root)) := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    rintro _ ⟨i, rfl⟩
    -- `root i` is a root of `X² - dᵢ`; this is separable when `dᵢ ≠ 0` (as `2 ≠ 0`), and when
    -- `dᵢ = 0` the generator is `0`, a root of the separable polynomial `X`.
    have haeval : aeval (root i) (X ^ 2 - C (d i)) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, hroot i, sub_self]
    by_cases hd : d i = 0
    · have hr0 : root i = 0 := by
        have hz : root i ^ 2 = 0 := by rw [hroot i, hd, map_zero]
        exact pow_eq_zero_iff (by norm_num) |>.mp hz
      exact separable_X.of_dvd (minpoly.dvd K (root i) (by rw [aeval_X, hr0]))
    · exact (separable_X_pow_sub_C (d i) (by exact_mod_cast two_ne_zero) hd).of_dvd
        (minpoly.dvd K (root i) haeval)
  constructor

end AdjoinGalois

section Extensionality
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {s : Set E}
private theorem algHom_ext_of_adjoin_eq_top {E₂ : Type*} [Semiring E₂] [Algebra F E₂]
    (htop : IntermediateField.adjoin F s = ⊤)
    {σ τ : E →ₐ[F] E₂} (h : ∀ x ∈ s, σ x = τ x) : σ = τ := by
  -- Transport `σ`, `τ` along `adjoin F s ≃ E` and compare on the subfield with Mathlib's
  -- `algHom_ext_of_eq_adjoin`, which is the adjoin induction we would otherwise repeat.
  let e : IntermediateField.adjoin F s ≃ₐ[F] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  have key : σ.comp e.toAlgHom = τ.comp e.toAlgHom :=
    IntermediateField.adjoin_algHom_ext F fun x hx => h x hx
  refine AlgHom.ext fun y => ?_
  obtain ⟨z, rfl⟩ := e.surjective y
  exact AlgHom.congr_fun key z

/-- Two `F`-algebra automorphisms of `E` agreeing on a generating set are equal. -/
private theorem algEquiv_ext_of_adjoin_eq_top (htop : IntermediateField.adjoin F s = ⊤)
    {σ τ : E ≃ₐ[F] E} (h : ∀ x ∈ s, σ x = τ x) : σ = τ :=
  AlgEquiv.ext (AlgHom.ext_iff.mp
    (algHom_ext_of_adjoin_eq_top (E₂ := E) htop (σ := σ.toAlgHom) (τ := τ.toAlgHom) h))

/-- An `F`-algebra automorphism of `E` that fixes every element of a set generating `E` over
`F` is the identity. This is `TauCeti.IntermediateField.algEquiv_ext_of_adjoin_eq_top` against
the identity. -/
private theorem algEquiv_eq_one_of_adjoin_eq_top (htop : IntermediateField.adjoin F s = ⊤)
    {σ : E ≃ₐ[F] E} (hfix : ∀ x ∈ s, σ x = x) : σ = 1 :=
  algEquiv_ext_of_adjoin_eq_top htop (σ := σ) (τ := 1) (by simpa using hfix)


end Extensionality

private theorem algebraMap_int_mem_iff_dvd_of_liesOver {S : Type*} [Ring S] {a : ℤ}
    (Q : Ideal S) [Q.LiesOver (span {a})] (m : ℤ) :
    algebraMap ℤ S m ∈ Q ↔ a ∣ m :=
  (Ideal.mem_of_liesOver Q (span {a}) m).symm.trans Ideal.mem_span_singleton

/-- The base residue ring of an ideal lying over a rational prime has `p` elements:
`Nat.card (ℤ ⧸ Q ∩ ℤ) = p` for `Q` over `(p)`.

This is the cardinality that `AlgHom.IsArithFrobAt` raises to over the base `ℤ`, so it is what
turns an abstract Frobenius congruence into the congruence `φ y ≡ y ^ p`. -/
private theorem natCard_quotient_under_of_liesOver {S : Type*} [Ring S] {p : ℕ}
    (Q : Ideal S) [Q.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := Q) (p := span {(p : ℤ)})]
  exact Int.card_ideal_quot p

section IntegralRoots
variable {K : Type*} [Field K] {x : K} {d : ℤ}
private noncomputable def integralSqrt (hx : x ^ 2 = algebraMap ℤ K d) : 𝓞 K :=
  ⟨x, IsIntegral.of_pow two_pos (hx ▸ isIntegral_algebraMap)⟩

/-- Under `𝓞 K ↪ K`, `NumberField.integralSqrt hx` maps back to `x`. -/
private theorem algebraMap_integralSqrt (hx : x ^ 2 = algebraMap ℤ K d) :
    algebraMap (𝓞 K) K (integralSqrt hx) = x :=
  NumberField.RingOfIntegers.map_mk x _

/-- `NumberField.integralSqrt hx` squares to the radicand `d` in `𝓞 K`. -/
private theorem integralSqrt_sq (hx : x ^ 2 = algebraMap ℤ K d) :
    integralSqrt hx ^ 2 = algebraMap ℤ (𝓞 K) d := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_pow, algebraMap_integralSqrt, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  exact hx


end IntegralRoots

-- Consumed rational-base specialization of TauCeti's AutomorphismAction instance.
private instance integers_smulCommClass {K : Type*} [Field K] [CharZero K] :
    SMulCommClass (K ≃ₐ[ℚ] K) (𝓞 ℚ) (𝓞 K) where
  smul_comm σ r x := by
    apply NumberField.RingOfIntegers.ext
    simp only [Algebra.smul_def, map_mul]
    change σ (algebraMap (𝓞 K) K (algebraMap (𝓞 ℚ) (𝓞 K) r) *
      algebraMap (𝓞 K) K x) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 ℚ) (𝓞 K) r) *
        σ (algebraMap (𝓞 K) K x)
    rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ K, AlgEquiv.commutes]

section LocalSquareRootAction
variable {S : Type*} [CommRing S] {p : ℕ} [Fact p.Prime] {d : ℤ}
  {Q : Ideal S} {x : S}
private theorem sub_legendreSym_smul_mem {φ : S →ₐ[ℤ] S}
    (H : φ.IsArithFrobAt Q) [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2)
    (hx : x ^ 2 = algebraMap ℤ S d) : φ x - legendreSym p d • x ∈ Q := by
  -- `p` is odd, so `p = 2·(p/2) + 1`; hence `x ^ p = (x²)^(p/2) · x = d^(p/2) · x`.
  have hp : p = 2 * (p / 2) + 1 := by
    have := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hodd); omega
  have hxp : x ^ p = algebraMap ℤ S (d ^ (p / 2)) * x := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hx, ← map_pow]
  -- Euler's criterion: `p ∣ d ^ (p / 2) - legendreSym p d`.
  have heuler : (p : ℤ) ∣ d ^ (p / 2) - legendreSym p d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr (legendreSym.eq_pow p d).symm
  -- Scaling Euler by `x`: `d^(p/2) · x ≡ legendreSym p d • x (mod Q)`.
  have hstep : algebraMap ℤ S (d ^ (p / 2)) * x - legendreSym p d • x ∈ Q := by
    have hfactor : algebraMap ℤ S (d ^ (p / 2)) * x - legendreSym p d • x =
        algebraMap ℤ S (d ^ (p / 2) - legendreSym p d) * x := by
      simp only [map_sub, sub_mul, zsmul_eq_mul, eq_intCast]
    rw [hfactor]
    exact Q.mul_mem_right x ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mpr heuler)
  -- Combine with the base congruence `φ x ≡ x ^ p (mod Q)`.
  have hpow : φ x - x ^ p ∈ Q := by
    simpa only [natCard_quotient_under_of_liesOver (p := p) Q] using H x
  have hsum := Q.add_mem hpow hstep
  rw [hxp] at hsum
  rwa [sub_add_sub_cancel] at hsum

/-- The two square roots of `d` are **distinct modulo `Q`**: if `x² = d`, the prime `p` is odd
and `p ∤ d`, and `Q` lies over `(p)`, then `x + x ∉ Q`. (Otherwise `(x + x) * x = 2d ∈ Q` would
give `p ∣ 2d`, forcing `p = 2` or `p ∣ d`.) Internal step of `apply_sqrt`. -/
private theorem add_self_notMem (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    [Q.LiesOver (span {(p : ℤ)})] (hx : x ^ 2 = algebraMap ℤ S d) : x + x ∉ Q := by
  intro hmem
  -- Multiplying by `x` gives `2d ∈ Q`, hence `p ∣ 2d` since `Q ∩ ℤ = (p)`.
  have h2d : algebraMap ℤ S (2 * d) ∈ Q := by
    simpa only [add_mul, ← sq, hx, map_mul, map_ofNat, two_mul, map_add] using
      Q.mul_mem_right x hmem
  rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_mul.mp
      ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h2d) with h2 | hdd
  · -- `p ∣ 2` forces `p = 2`, excluded.
    exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      (by exact_mod_cast h2))
  · exact hd hdd

/-- **An arithmetic Frobenius acts on square roots by the Legendre symbol.** Let `S` be a
commutative ring without zero divisors, `Q` an ideal of `S` over the odd rational prime `p`, and
`φ : S →ₐ[ℤ] S` an arithmetic Frobenius at `Q`. If `x² = d` for an integer `d` not divisible
by `p`, then `φ x = legendreSym p d • x`: the Frobenius fixes `√d` when `d` is a quadratic
residue mod `p` and negates it otherwise. Primality of `Q` is not needed. -/
private theorem frobenius_apply_sqrt [NoZeroDivisors S] {φ : S →ₐ[ℤ] S}
    (H : φ.IsArithFrobAt Q)
    [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    (hx : x ^ 2 = algebraMap ℤ S d) :
    φ x = legendreSym p d • x := by
  -- `φ x ≡ legendreSym p d • x (mod Q)` by the Frobenius congruence refined via Euler.
  have hkey : φ x - legendreSym p d • x ∈ Q :=
    sub_legendreSym_smul_mem H hodd hx
  -- `(φ x)² = x²`, so as `S` has no zero divisors the value `φ x` is `x` or `-x` on the nose.
  have hpm : φ x = x ∨ φ x = -x :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow, hx, AlgHom.commutes])
  -- The target `legendreSym p d • x` is likewise `x` or `-x`, since the symbol is `±1`.
  have hgoal : legendreSym p d • x = x ∨ legendreSym p d • x = -x :=
    (legendreSym.eq_one_or_neg_one p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])).imp
      (fun h ↦ by rw [h, one_smul]) (fun h ↦ by rw [h, neg_smul, one_smul])
  -- When both signs agree the goal is immediate; when they disagree `x + x ∈ Q`, excluded.
  have hsep : x + x ∉ Q := add_self_notMem hodd hd hx
  rcases hpm with hx' | hx' <;> rcases hgoal with hg | hg <;>
    simp_all [sub_eq_add_neg, ← neg_add, -neg_add_rev]


end LocalSquareRootAction

private theorem under_rat_eq_map {S : Type*} [CommRing S] [Algebra (𝓞 ℚ) S]
    (Q : Ideal S) : Q.under (𝓞 ℚ) = (Q.under ℤ).map (algebraMap ℤ (𝓞 ℚ)) := by
  rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ℚ) Q]
  have hbij : Function.Bijective (algebraMap ℤ (𝓞 ℚ)) := by
    have he : algebraMap ℤ (𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
      Subsingleton.elim _ _
    rw [he]
    exact Rat.ringOfIntegersEquiv.symm.bijective
  exact (Ideal.map_comap_of_surjective _ hbij.surjective _).symm

private theorem card_quot_under_rat {S : Type*} [CommRing S] [Algebra (𝓞 ℚ) S]
    (Q : Ideal S) : Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ Q.under ℤ) := by
  have he : Q.under (𝓞 ℚ) = (Q.under ℤ).map
      (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) := by
    rw [under_rat_eq_map]
    congr 1
    exact Subsingleton.elim _ _
  exact (Nat.card_congr (Ideal.quotientEquiv (Q.under ℤ) (Q.under (𝓞 ℚ))
    Rat.ringOfIntegersEquiv.symm he).toEquiv).symm

/-- The arithmetic convention has base residue cardinality p. The base is 𝓞 ℚ;
    the lies-over hypothesis is transported to ℤ before Euler's criterion. -/
theorem arithmeticFrobenius_sqrt {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt (𝓞 ℚ) σ Q) :
    σ x = jacobiSym d p • x := by
  have hz : IsArithFrobAt ℤ σ Q := by
    simpa only [IsArithFrobAt, AlgHom.IsArithFrobAt,
      MulSemiringAction.toAlgHom_apply, card_quot_under_rat] using hσ
  have hr : σ • integralSqrt hx = legendreSym p d • integralSqrt hx := by
    simpa only [MulSemiringAction.toAlgHom_apply] using
      frobenius_apply_sqrt hz hodd hd (integralSqrt_sq hx)
  have heq : σ x = legendreSym p d • x := by
    have hmap := congrArg (algebraMap (𝓞 K) K) hr
    change σ (algebraMap (𝓞 K) K (integralSqrt hx)) =
      algebraMap (𝓞 K) K (legendreSym p d • integralSqrt hx) at hmap
    simpa only [map_zsmul, algebraMap_integralSqrt] using hmap
  simpa only [jacobiSym.legendreSym.to_jacobiSym] using heq

section Unramified
variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
private theorem apply_eq_self_of_mem_inertia {x : K} {c : ℤ} (hx : x ^ 2 = algebraMap ℤ K c)
    (hodd : p ≠ 2) (hc : ¬ (p : ℤ) ∣ c) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] {τ : K ≃ₐ[ℚ] K} (hτ : τ ∈ Q.inertia (K ≃ₐ[ℚ] K)) :
    τ x = x := by
  -- `τ x` is a square root of `c`, hence `± x`; rule out the minus sign.
  have hx' : x ^ 2 = algebraMap ℚ K (c : ℚ) := by rw [hx]; simp
  have hsq : τ x ^ 2 = x ^ 2 := by rw [← map_pow, hx', AlgEquiv.commutes]
  refine (eq_or_eq_neg_of_sq_eq_sq _ _ hsq).resolve_right fun hneg => ?_
  let R : 𝓞 K := integralSqrt hx
  have hR : τ • R = -R := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    have hmap : algebraMap (𝓞 K) K (τ • R) = τ (algebraMap (𝓞 K) K R) :=
      integralClosure.coe_smul τ R
    rw [hmap, map_neg, algebraMap_integralSqrt, hneg]
  -- `τ` acts trivially modulo `Q`, so `τ • R - R = -(2 * R)` lies in `Q`.
  have h2R : (2 : 𝓞 K) * R ∈ Q := by
    have h := (Ideal.mem_inertia.mp hτ) R
    rw [hR, show -R - R = -((2 : 𝓞 K) * R) by ring] at h
    exact Q.neg_mem_iff.mp h
  rcases (‹Q.IsPrime›).mem_or_mem h2R with h2 | hRQ
  · -- `2 ∈ Q` would force the odd prime `p` to divide `2`.
    have h2' : algebraMap ℤ (𝓞 K) 2 ∈ Q := by simpa using h2
    have hdvd : (p : ℤ) ∣ 2 := (algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h2'
    exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast hdvd))
  · -- `R ∈ Q` would put `c = R ^ 2` in `Q`, so `p ∣ c`.
    have hc' : algebraMap ℤ (𝓞 K) c ∈ Q := by
      rw [← integralSqrt_sq hx, pow_two]
      exact Q.mul_mem_left _ hRQ
    exact hc ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hc')


/-- Every odd prime avoiding all radicands is unramified. Galoisness is derived
    from generation by square roots; neither degree nor unramifiedness is a premise. -/
theorem squareRoot_unramified {ι : Type*} [Finite ι] (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
  have hrQ : ∀ i, r i ^ 2 = algebraMap ℚ K (d i : ℚ) := by
    intro i
    rw [hr i]
    simp
  letI : IsGalois ℚ K := by
    have hg := squareRootAdjoin_isGalois hrQ
    rw [htop] at hg
    exact isGalois_iff_isGalois_top.mp hg
  have hinertia : Q.inertia (K ≃ₐ[ℚ] K) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => ?_
    refine algEquiv_eq_one_of_adjoin_eq_top htop ?_
    rintro _ ⟨i, rfl⟩
    exact apply_eq_self_of_mem_inertia (hr i) hodd (hcop i) Q hτ
  -- Receiver-pin bridge: the available cardinality theorem names ramificationIdxIn.
  let P : Ideal (𝓞 ℚ) := Q.under (𝓞 ℚ)
  have hcard : Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) = Q.ramificationIdx (𝓞 ℚ) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[ℚ] K) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q (K ≃ₐ[ℚ] K)]
  apply (Ideal.ramificationIdx_eq_one_iff (R := 𝓞 ℚ) (q := Q)).mp
  rw [← hcard, hinertia]
  simp
end Unramified
end D5.S3.Factorization.Galois.SquareRootArithmetic
