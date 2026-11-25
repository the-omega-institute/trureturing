/- GID: D5/S3/Quantum/Entanglement/Marginals/FibPositiveRationalPurity
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibPositiveRationalPurity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A Gaussian norm characterizes the degenerate rational pure Fibonacci extensions. -/

import D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension

/-! The hidden coupling and its norm in rational pure Fibonacci extensions. -/

open Matrix Complex
open scoped Matrix ComplexOrder ComplexConjugate
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity

private theorem pure_hidden_rational (b : ℝ) (u v w z : ℂ)
    (L R : Matrix Bool Bool ℂ) (hb : b ≠ 0)
    (ht : L.trace + (b : ℂ) = 1)
    (hL : L = partialTraceRight (correction b (middleRow u v w z)))
    (hR : R = partialTraceLeft (correction b (middleRow u v w z)))
    (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (h : v ≠ 0 ∨ w ≠ 0) : RationalEntry z := by
  have qb : (b : ℂ) ∈ rationalComplex := by
    have hq : L.trace ∈ rationalComplex := rationalComplex.sum_mem fun i _ => qL i i
    rw [show (b : ℂ) = 1 - L.trace by linear_combination ht]
    exact rationalComplex.sub_mem rationalComplex.one_mem hq
  have b0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have solve (a c ell : ℂ) (qa : a ∈ rationalComplex) (qc : c ∈ rationalComplex)
      (qell : ell ∈ rationalComplex) (hc : c ≠ 0)
      (he : ell = (b : ℂ)⁻¹ * (conj u * a + conj c * z)) : RationalEntry z := by
    have hc0 : conj c ≠ 0 := by simpa using hc
    have eqn : ((b : ℂ) * ell - conj u * a) / conj c = z := by
      rw [he]
      field_simp
      ring
    rw [← eqn]
    exact rationalComplex.div_mem (rationalComplex.sub_mem (rationalComplex.mul_mem qb qell)
      (rationalComplex.mul_mem (rationalConjugate ⟨u, qu⟩).property qa))
      (rationalConjugate ⟨c, qc⟩).property
  rcases h with hv | hw
  · apply solve w v (R false true) qw qv (qR false true) hv
    have e := congrFun (congrFun hR false) true
    simpa [partialTraceLeft, correction, Matrix.vecMulVec_apply, middleRow, Fintype.sum_bool,
      Complex.ofReal_inv, smul_eq_mul, mul_add, add_comm, Matrix.smul_apply] using e
  · apply solve v w (L false true) qv qw (qL false true) hw
    have e := congrFun (congrFun hL false) true
    simpa [partialTraceRight, correction, Matrix.vecMulVec_apply, middleRow, Fintype.sum_bool,
      Complex.ofReal_inv, smul_eq_mul, mul_add, add_comm, Matrix.smul_apply] using e

private theorem rational_pure_at (b : ℝ) (u v w z : ℂ) (L R : Matrix Bool Bool ℂ)
    (hb : 0 < b) (ht : L.trace + (b : ℂ) = 1)
    (hL : L = partialTraceRight (correction b (middleRow u v w z)))
    (hR : R = partialTraceLeft (correction b (middleRow u v w z)))
    (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w) (qz : RationalEntry z) :
    ∃ ψ : Word → ℂ, MatchesCoherentData b L R u v w z (rankOneDensity ψ) ∧
      ∀ i j, RationalEntry (rankOneDensity ψ i j) := by
  obtain ⟨ρ, ⟨ψ, rfl⟩, hψ⟩ := (pure_coherent_iff b L R u v w z hb.ne').1.mpr ⟨ht, hL, hR⟩
  have hr : R.trace = L.trace := by
    rw [hL, hR, trace_partialTraceLeft, trace_partialTraceRight]
  have hzero : b = 0 → middleRow u v w z = 0 := fun h => (hb.ne' h).elim
  have pL : (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef := by
    rw [← hL, sub_self]
    exact Matrix.PosSemidef.zero
  have pR : (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef := by
    rw [← hR, sub_self]
    exact Matrix.PosSemidef.zero
  obtain ⟨ρ, hρ, hdata, hq⟩ :=
    rational_extension_at b L R u v w z hb.le ht hr hzero pL pR qL qR qu qv qw qz
  have hrho := (pure_coherent_iff b L R u v w z hb.ne').2 ψ ρ hψ hρ hdata
  exact ⟨ψ, hψ, hrho ▸ hq⟩

private theorem diagonal_left_norm (b : ℝ) (hb : b ≠ 0) (u z : ℂ)
    (L : Matrix Bool Bool ℂ) (hL : L = partialTraceRight (correction b (middleRow u 0 0 z))) :
    normSq z = b * (L true true).re := by
  have h := congrFun (congrFun hL true) true
  have hs : L true true = (b : ℂ)⁻¹ * (normSq z : ℂ) := by
    rw [show (normSq z : ℂ) = conj z * z by rw [mul_comm, Complex.mul_conj]]
    simpa [partialTraceRight, correction, Matrix.vecMulVec_apply, middleRow, Fintype.sum_bool,
      Complex.ofReal_inv, smul_eq_mul, Matrix.smul_apply] using h
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul] at hs
  have re := congrArg Complex.re hs
  rw [Complex.ofReal_re] at re
  rw [re, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]

private theorem replace_norm (b : ℝ) (u z t : ℂ) (h : normSq z = normSq t) :
    partialTraceRight (correction b (middleRow u 0 0 z)) =
      partialTraceRight (correction b (middleRow u 0 0 t)) ∧
    partialTraceLeft (correction b (middleRow u 0 0 z)) =
      partialTraceLeft (correction b (middleRow u 0 0 t)) := by
  have hprod : conj z * z = conj t * t := by
    rw [mul_comm (conj z) z, mul_comm (conj t) t, Complex.mul_conj, Complex.mul_conj, h]
  constructor <;> ext i j : 1 <;> cases i <;> cases j <;>
    simp [partialTraceRight, partialTraceLeft, correction, Matrix.vecMulVec_apply, middleRow,
      Complex.ofReal_inv, Matrix.smul_apply, hprod]

/-- With positive middle occupation and an ordinary pure extension, a nonzero coupling
to either occupied endpoint forces the hidden coupling to be rational. When both
couplings vanish, rational purity is exactly a Gaussian norm condition. -/
theorem positive_rational_purity_iff
    (b : ℝ) (u v w : ℂ) (L R : Matrix Bool Bool ℂ)
    (hb : 0 < b)
    (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (hPure : ∃ (z : ℂ) (ψ : Word → ℂ), MatchesCoherentData b L R u v w z (rankOneDensity ψ)) :
    (∃ (z : ℂ) (ψ : Word → ℂ), MatchesCoherentData b L R u v w z (rankOneDensity ψ) ∧
      ∀ i j, RationalEntry (rankOneDensity ψ i j)) ↔
      v ≠ 0 ∨ w ≠ 0 ∨ ∃ z, RationalEntry z ∧ normSq z = b * (L true true).re := by
  constructor
  · rintro ⟨z, ψ, hψ, hQ⟩
    by_cases hv : v = 0
    · by_cases hw : w = 0
      · subst v
        subst w
        have eqns := (pure_coherent_iff b L R u 0 0 z hb.ne').1.mp
          ⟨rankOneDensity ψ, ⟨ψ, rfl⟩, hψ⟩
        have qz : RationalEntry z := hψ.2.2.2 ▸ hQ (.inl 0) (.inr true)
        exact Or.inr (Or.inr ⟨z, qz, diagonal_left_norm b hb.ne' u z L eqns.2.1⟩)
      · exact Or.inr (Or.inl hw)
    · exact Or.inl hv
  · intro h
    obtain ⟨z, ψ, hψ⟩ := hPure
    obtain ⟨ht, hL, hR⟩ := (pure_coherent_iff b L R u v w z hb.ne').1.mp
      ⟨rankOneDensity ψ, ⟨ψ, rfl⟩, hψ⟩
    by_cases nonzero : v ≠ 0 ∨ w ≠ 0
    · exact ⟨z, rational_pure_at b u v w z L R hb ht hL hR qL qR qu qv qw
        (pure_hidden_rational b u v w z L R hb.ne' ht hL hR qL qR qu qv qw nonzero)⟩
    · push Not at nonzero
      obtain ⟨rfl, rfl⟩ := nonzero
      rcases h with h | h | ⟨t, qt, hnorm⟩
      · exact (h rfl).elim
      · exact (h rfl).elim
      · have both := replace_norm b u z t ((diagonal_left_norm b hb.ne' u z L hL).trans hnorm.symm)
        exact ⟨t, rational_pure_at b u 0 0 t L R hb ht (hL.trans both.1) (hR.trans both.2)
          qL qR qu rationalComplex.zero_mem rationalComplex.zero_mem qt⟩

end D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity
