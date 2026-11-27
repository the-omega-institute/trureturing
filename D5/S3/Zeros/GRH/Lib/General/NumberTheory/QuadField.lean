/- GID: D5/S3/Zeros/GRH/Lib/General/NumberTheory/QuadField
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/NumberTheory/QuadField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.NumberTheory.QuadField. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/NumberTheory/QuadField.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Analysis.ZpowSum
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.Embeddings
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Imaginary quadratic field Q(√-d): degree, CM structure, integers, different, quadratic
character. -/

noncomputable section

open NumberField Complex Polynomial InfinitePlace Module IntermediateField AddChar


instance (d : Nat.Primes) : Fact d.1.Prime := ⟨d.2⟩

variable {N} [NeZero N] (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-- The Legendre symbol (·/d) as an integer-valued Dirichlet character modulo the prime d; for d
≡ 3 mod 4 it is the character χ_K of K = ℚ(√−d). -/
def chiK : DirichletCharacter ℤ d := open Calc in quadraticChar _

lemma chiK_eq_legendreSym (n : ℕ) : chiK d n = legendreSym d n := by simp [chiK, legendreSym]

/-- For a Dirichlet character χ mod N and a prime d, the character mod Nd that is the product of
χ and the Legendre symbol (·/d). -/
def quadTwist :=
  χ.changeLevel ⟨d, rfl⟩ * .changeLevel (by simp) ((chiK d).ringHomComp (algebraMap ..))

/-- The entire function equal to L(s, χ) if χ is not principal, and to the continuation of (s −
1)L(s, χ) if χ is principal. -/
def entireL := ite (χ = 1) (DirichletCharacter.LFunctionTrivChar₁ N) χ.LFunction

/-- For an odd prime d, the number γ − Re L'/L(1, χ), with γ Euler's constant and χ the Legendre
symbol modulo d. -/
def chowlaSelbergConst := .eulerMascheroniConstant - (logDeriv (entireL (@quadTwist 1 1 d _)) 1).re

variable (d n : ℕ) [NeZero n] {M : Type} [Field M] [CharZero M] {x y : M}

/-- The natural number d is a prime congruent to 7 modulo 8. -/
class PrimeSevenModEight extends Fact d.Prime where mod_eight : d % 8 = 7

attribute [local simp] neg_eq_self NeZero.ne NeZero.pos mul_pow RingOfIntegers.ext_iff
attribute [local simp ←] ofReal_pow

/-- If a number field M contains primitive roots of unity of coprime orders n and d, then its
degree over ℚ is at least φ(d)φ(n). -/
lemma totient_mul_totient_le_finrank [NeZero d] [NumberField M] (c : n.Coprime d) (hx :
  IsPrimitiveRoot x n) (hy : IsPrimitiveRoot y d) : d.totient * n.totient ≤ finrank ℚ M := by grind
  [n.totient_mul, c.lcm_eq_mul, hx.lcm_totient_le_finrank hy (cyclotomic.irreducible_rat (by simp))]

/-- The subfield K = ℚ(i√d) of ℂ. -/
def QuadField := ℚ⟮I * √d⟯

namespace QuadField

/-- The generator √−d = i√d of K = ℚ(i√d). -/
@[simps! coe] def sqrtNegD : QuadField d := AdjoinSimple.gen ..

@[local simp] lemma sqrtNegD_sq : sqrtNegD d ^ 2 = -d := by aesop

lemma isIntegral_sqrtNegD : IsIntegral ℚ (I * √d) := .of_pow two_pos (by simp [isIntegral_natCast])

instance : NumberField (QuadField d) where
  to_finiteDimensional := adjoin.finiteDimensional (isIntegral_sqrtNegD d)

instance [PrimeSevenModEight d] : Fact (d % 4 = 3) := ⟨by grind [PrimeSevenModEight]⟩

variable [h : Fact (d % 4 = 3)]

instance : NeZero d := ⟨by grind [Fact]⟩

lemma minpoly_sqrtNegD : X ^ 2 - C (-d : ℚ) = minpoly ℚ (I * √d) :=
  minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime Fact.out
  (sq_nonneg · |>.not_gt <| by simp [·])) (by simp) (by monicity!)

lemma finrank_K : finrank ℚ (QuadField d) = 2 :=
  adjoin.finrank (isIntegral_sqrtNegD d) ▸ minpoly_sqrtNegD d ▸ natDegree_X_pow_sub_C

instance : IsTotallyComplex (QuadField d) := ⟨fun _ ↦ not_isReal_iff_isComplex.1
  (by simpa [← map_pow] using sq_nonneg <| embedding_of_isReal · (sqrtNegD d))⟩

instance : Unique (InfinitePlace (QuadField d)) := ⟨⟨mk (val _).1⟩,
  (Fintype.card_le_one_iff.1 (by grind [finrank_eq_two_mul_card_infinitePlace, finrank_K]) · _)⟩

/-- For d ≡ 3 mod 4 and y with y² = −d in a field M of characteristic zero, the embedding of K =
ℚ(i√d) into M sending i√d to y. -/
def embOfSqrt (e : y ^ 2 = -d) : QuadField d →ₐ[ℚ] M :=
  (adjoin.powerBasis (isIntegral_sqrtNegD d)).lift y (by simp [minpoly_gen, ← minpoly_sqrtNegD, e])

open Subalgebra Int Algebra Ideal ZMod

/-- For a prime d ≡ 3 mod 4, the field ℚ(√−d) embeds in every field M of characteristic zero
that contains a primitive d-th root of unity (quadratic Gauss sum). -/
def nonempty_algHom_of_isPrimitiveRoot [Fact d.Prime] (hx : IsPrimitiveRoot x d) : QuadField d →ₐ[ℚ]
  M := embOfSqrt d (by rw [gaussSum_sq (MulChar.ne_one_iff.2 ⟨-1, _⟩) ((quadraticChar_isQuadratic
  _).comp (castRingHom _)) (zmodChar_primitive_of_primitive_root _ hx)] <;>
  simp [quadraticCharFun, exists_sq_eq_neg_one_iff, h.1])

@[simp] lemma four_dvd_d_add_one : 4 ∣ d + 1 := by grind [Fact]

instance : IsQuadraticExtension ℚ (QuadField d) := ⟨finrank_K d⟩

instance : IsCMField (QuadField d) := .ofCMExtension ℚ _

@[simp] lemma coe_star_eq_conj (y : QuadField d) : star y = starRingEnd ℂ y :=
  map_star_complex (QuadField d).val y

@[simp] lemma star_sqrtNegD : star (sqrtNegD d) = -sqrtNegD d := by aesop

lemma abs_norm_eq_norm_sq (x : QuadField d) : |(norm ℚ x : ℝ)| = ‖x.1‖ ^ 2 := by simpa using!
  (prod_eq_abs_norm x).symm

lemma absNorm_span_eq_mul_star (y : 𝓞 (QuadField d)) : (span {y}).absNorm = y * star y := by
  ext; simp [← coe_norm_int, ← abs_norm_eq_norm_sq, ← cast_abs, mul_conj']

/-- For d ≡ 3 mod 4, the algebraic integer (1 + √−d)/2 of K = ℚ(√−d). -/
def c₀ : 𝓞 (QuadField d) := ⟨(1 + sqrtNegD d) / 2, X ^ 2 - X + (d.succ / 4).cast, by monicity!,
  by simp; grind [sqrtNegD_sq]⟩

@[simp] lemma coe_c₀ : c₀ d = (1 + sqrtNegD d) / 2 := rfl

@[simp] lemma star_c₀ : star (c₀ d) = 1 - c₀ d := by simp; ring

lemma c₀_mul_one_sub : c₀ d * (1 - c₀ d) = ↑((d + 1) / 4) := by simp; grind [sqrtNegD_sq]

/-- For d ≡ 3 mod 4, the element √−d = i√d of the ring of integers of K = ℚ(√−d), defined as
2·(1 + √−d)/2 − 1. -/
abbrev sqrtNegDInt := 2 * c₀ d - 1

lemma sqrtNegDInt_sq : sqrtNegDInt d ^ 2 = -d := by simp [two_mul]

/-- For a prime d ≡ 7 mod 8, K = ℚ(√−d) and c₀ = (1 + √−d)/2, the different of K over ℚ is
generated by 2c₀ − 1, and ℤ[c₀] is the whole ring of integers of K. -/
lemma different_eq_span_and_adjoin_c₀ [PrimeSevenModEight d] : differentIdeal ℤ _ =
  span {sqrtNegDInt d} ∧ ℤ[c₀ d] = ⊤ := differentIdeal_eq_span_of_dvd ℚ (((
  isSimpleOrder_of_finrank (finrank_K d)).2 _).resolve_left ((·.le (subset_adjoin rfl)).mt fun ⟨_,
  e⟩ ↦ by simpa using congr(-($e + $e).1.im))) ((d.succ / 4).cast - X * (1 - X)) (by simp [
  c₀_mul_one_sub]) (by simp [two_mul, add_sub]) (dvd_differentIdeal_of_mem_sq (p :=
  d) (by simp [span_singleton_pow, sqrtNegDInt_sq]))
