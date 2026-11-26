import GRH.Lib.Analytic.Landau.PolarLandau
import GRH.Lib.GaloisRep.Main.LocalEmbedding
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: the class number of an imaginary quadratic field of prime discriminant is odd. It
is stated here as bijectivity of squaring on the class group, for primes congruent to 7 modulo 8.
Source: C. F. Gauss, Disquisitiones; D. Cox, Primes of the form x²+ny² (1989), §3 and §6.

Part of: Chowla-Selberg formula in logarithmic form (known result; see
Lib.CM.FormalGroup.FormalHeight).

This file: A complex number bounded under all 2-adic identifications is algebraic. Odd class number
for prime discriminant; ramified prime; zeta factorisation of the quadratic field. -/


/-- If a complex number x satisfies |ι(x)|₂ ≤ c, with one bound c, for every field isomorphism ι
from ℂ onto the algebraic closure of ℚ₂, then x is algebraic over ℚ. -/
lemma isAlgebraic_of_padic {x c} (h : ∀ ι, ‖complexToCp (p := 2) ι x‖ ≤ c) : IsAlgebraic ℚ x := by
  obtain ⟨_, _, ⟨k⟩⟩ := (Polynomial.basisMonomials ℚ).1.injective.countable,
    ((Algebraic.countable ℚ (PadicAlgCl 2)).dense_compl ℚ_[2]).exists_mem_open
    (continuous_norm.1 _ isOpen_Ioi) (NormedField.exists_lt_norm _ c)
  simp [isAlgebraic_iff_not_injective] at *
  intro t
  grind [by simpa using
    (exists_ringEquiv_extend mk_complex_eq_mk_padicAlgCl _ _ t k).choose_spec .X]

open NumberField Ideal ClassGroup Nat Equiv Complex CharP DirichletCharacter

namespace QuadField

variable {d} [PrimeSevenModEight d]

attribute [local simp] span_singleton_pow sqrtNegDInt_sq mul_pow

lemma eq_d_of_span_eq_sq {p : ℕ} (_ : Fact p.Prime) C (k : span {(p : 𝓞 (QuadField d))} = C ^ 2) :
  p = d := by simpa [← k, different_eq_span_and_adjoin_c₀, Algebra.norm_natCast,
  Nat.pow_dvd_pow_iff Module.finrank_pos.ne', Fact.out, prime_dvd_prime_iff_eq]
  using map_dvd absNorm (pow_dvd_pow_of_dvd (dvd_differentIdeal_of_mem_sq (k.le (by bound))) 2)

/-- For d a prime ≡ 7 mod 8, squaring is a bijection of the class group of ℚ(√−d); that is, the
class number is odd (genus theory).

Known result: The class number of an imaginary quadratic field of prime discriminant is odd. -/
lemma classGroup_sq_bijective : (· ^ 2 : ClassGroup (𝓞 (QuadField d)) → _).Bijective :=
  ((injective_iff_map_eq_one (@powMonoidHom (ClassGroup _) ..)).2 (by
  simp [← map_pow, mk0_surjective.forall, mk0_eq_one_iff]
  intro I _ ⟨α, hα⟩
  wlog h0 : 0 < (span {star α + I.absNorm} * I).absNorm generalizing α
  apply this (-α) <;> simp_all; grind [cast_ne_zero, absNorm_eq_zero_iff]
  obtain ⟨M, r, s, _, _, e, hr⟩ := (span_singleton_mul_span_singleton
    (R := 𝓞 (QuadField d)) · · |>.symm), sq_mul_squarefree_of_pos h0
  have hJ : (span {star α + I.absNorm} * I) ^ 2 = span {s.cast} ^ 2 * span {r.cast}
  rcases congr(α + absNorm $hα), congr(α + $e)
  simp [↓map_pow, hα, ← M, absNorm_span_eq_mul_star, -absNorm_span_singleton] at *; congr 2; grind
  obtain ⟨B⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 ⟨_, hJ⟩
  rw [eq_prime_pow_of_unique_prime_dvd hr.ne_zero fun h ⟨_, k⟩ ↦
    (exists_eq_pow_of_mul_eq_pow_of_coprime ((isCoprime_span_singleton_iff ..).2
    (coprime_of_squarefree_mul (k ▸ hr)).cast) (c := B) (by aesop)).rec (eq_d_of_span_eq_sq ⟨h⟩),
    cast_pow, ← span_singleton_pow, (by simp : span {↑d} = span {sqrtNegDInt d} ^ 2),
    pow_right_comm, ← mul_pow, pow_left_inj two_ne_zero, span_singleton_pow, ← M] at hJ
  cases span_singleton_le_span_singleton.1 (hJ ▸ mul_le_left)
  use ‹_›, by simp_all)).bijective_of_finite

lemma eulerProd_one_eq_zeta_mul {s} (h : 1 < s) : eulerProd (K := QuadField d) 1 s =
  riemannZeta s * entireL (@quadTwist 1 1 d _) s := by
  simp [entireL, quadTwist_ne_one _ d (by grind [PrimeSevenModEight]), LFunction_eq_LSeries, h]
  use (((sigmaFiberEquiv (Subtype.mk _ <| prime_ringChar <| ResField ·)).hasProd_iff.2
    (hasProd_eulerProd (by simp) h)).sigma fun ⟨p, hp⟩ ↦ let f := Fact.mk hp
    ?_).unique ((riemannZeta_eulerProduct_hasProd h).mul (LSeries_eulerProduct_hasProd _ h))
  have ⟨w, J, F, h⟩ := (FinPlace.exists_natCast_mem (QuadField d) p).imp prime_inert_or_eq_mul
  convert (subtypeEquivRight _).hasProd_iff.2 (Finset.hasProd {w, J} (1 - cpow ·.q (-s))⁻¹) <;>
    simp [ringChar.eq_iff, charP_iff_prime_eq_zero hp, ← algebraMap_ResField_eq_zero, ← F,
    @Subsingleton.eq_one (ZMod 1), mod_cast (quadTwist_apply · d p)]
  obtain ⟨_, ⟨⟩, ⟨⟨⟨⟩⟩⟩ | ⟨_, ⟨⟩⟩, ⟨⟩⟩ := exists_eq_pow_of_mul_eq_pow_of_coprime (n := 2) (c := span
    {sqrtNegDInt d}) ∘ w.isCoprime_of_ne J, h, chiK_cases d p, em (w = J) <;> simp_all [@sq ℕ,
    ↓chiK_eq_legendreSym, natCast_mul_natCast_cpow] <;> grind [→ q_eq_iff_legendreSym_ne_neg_one,
    chiK_eq_legendreSym, not_prime_mul, hp.ne_one, eq_d_of_span_eq_sq f w.1, sq]
