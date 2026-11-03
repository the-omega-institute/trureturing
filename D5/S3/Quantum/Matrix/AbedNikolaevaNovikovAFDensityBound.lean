/- GID: D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fixed-dimensional density-independent bounds for accretive matrix quotients. -/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! The quotient and supremum in arXiv:2610.34388v1, Sections 5.12 and 11.2(5).
The density is positive definite and is not required to have trace one.
The ordinary matrix inequality is used without any invertibility hypothesis on X.

The external problem binding is owner #22774. The proposed admission basis is
open-problem-resolution for its fixed-dimensional boundedness sentence.
The substantive intermediate result is `accretive_le_card_abs`, used by
`quotient_bounds` and hence `result`. Its live spectral diagonal estimate and
finite-basis quadratic-form bound include zero singular values.
`norm_mulVec_sq`, `basis_norm_bound`, and `eigenbasis_quadratic` organize
standard identities and Cauchy–Schwarz applications; their consumer is
`accretive_le_card_abs`. The trace factorization in `trace_pair_pos` is consumed
by `denominator_pos`, then by `one_mem_quotientValues`, `quotient_bounds`, and
`result`. These helpers are not independent novelty claims.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound

open D5.S3.Quantum.FiniteDimensional (bornProbability)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def quotientValues (rho : Matrix ι ι ℂ) : Set ℝ :=
  {q | ∃ A B : Matrix ι ι ℂ, A.PosSemidef ∧ B.IsHermitian ∧
    A + Complex.I • B ≠ 0 ∧
    q = (bornProbability rho A).re / (bornProbability rho (CFC.abs (A + Complex.I • B))).re}

def a (rho : Matrix ι ι ℂ) : ℝ := sSup (quotientValues rho)

/-- The complete fixed-dimension density-independent boundedness question. -/
def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (rho : Matrix (Fin n) (Fin n) ℂ), rho.PosDef →
        (quotientValues rho).Nonempty ∧
        IsLUB (quotientValues rho) (a rho) ∧ a rho ≤ C

private lemma norm_mulVec_sq (Y : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    ‖WithLp.toLp 2 (Y *ᵥ v.ofLp)‖ ^ 2 =
      (star v.ofLp ⬝ᵥ ((Yᴴ * Y) *ᵥ v.ofLp)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  change ((Y *ᵥ v.ofLp) ⬝ᵥ star (Y *ᵥ v.ofLp)).re = _
  rw [dotProduct_comm (Y *ᵥ v.ofLp), star_mulVec, dotProduct_mulVec,
    vecMul_vecMul, ← dotProduct_mulVec]

private lemma basis_norm_bound (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι) :
    ‖L v‖ ^ 2 ≤ (Fintype.card ι : ℝ) *
      ∑ j, ‖b.repr v j‖ ^ 2 * ‖L (b j)‖ ^ 2 := by
  have he : L v = ∑ j, b.repr v j • L (b j) := by
    conv_lhs => rw [← b.sum_repr v, map_sum]
    simp only [map_smul]
  calc
    ‖L v‖ ^ 2 ≤ (∑ j, ‖b.repr v j • L (b j)‖) ^ 2 := by
      rw [he]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Fintype.card ι : ℝ) * ∑ j, ‖b.repr v j • L (b j)‖ ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun j => ‖b.repr v j • L (b j)‖))
    _ = _ := by simp [norm_smul, mul_pow]

private lemma eigenbasis_quadratic (P : Matrix ι ι ℂ)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (s : ι → ℝ)
    (he : ∀ j, P.toEuclideanLin (b j) = (s j : ℂ) • b j) (v : EuclideanSpace ℂ ι) :
    (star v.ofLp ⬝ᵥ (P *ᵥ v.ofLp)).re = ∑ j, ‖b.repr v j‖ ^ 2 * s j := by
  have hPv : P.toEuclideanLin v = ∑ j, b.repr v j • ((s j : ℂ) • b j) := by
    conv_lhs => rw [← b.sum_repr v, map_sum]
    simp only [map_smul, he]
  rw [show star v.ofLp ⬝ᵥ (P *ᵥ v.ofLp) = inner ℂ v (P.toEuclideanLin v) by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _]
  rw [hPv, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hi : inner ℂ v (b j) = star (b.repr v j) := by
    rw [b.repr_apply_apply]
    exact (inner_conj_symm _ _).symm
  rw [inner_smul_right, inner_smul_right, hi]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, mul_zero, sub_zero,
    zero_mul, add_zero, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem accretive_le_card_abs (A B : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hB : B.IsHermitian) : A ≤ (Fintype.card ι : ℝ) • CFC.abs (A + Complex.I • B) := by
  let X := A + Complex.I • B
  let P := CFC.abs X
  have hP : P.PosSemidef := (CFC.abs_nonneg X).posSemidef
  let b := hP.isHermitian.eigenvectorBasis
  let s := hP.isHermitian.eigenvalues
  have he (j : ι) : P.toEuclideanLin (b j) = (s j : ℂ) • b j := by
    apply PiLp.ext
    intro i
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, b, s,
      RCLike.real_smul_eq_coe_smul] using
      congrFun (hP.isHermitian.mulVec_eigenvectorBasis j) i
  have hs (j : ι) : 0 ≤ s j := hP.eigenvalues_nonneg j
  have hPP : P * P = Xᴴ * X := CFC.abs_mul_abs X
  have hXnorm (j : ι) : ‖X.toEuclideanLin (b j)‖ = s j := by
    have hn := norm_mulVec_sq X (b j)
    rw [← hPP] at hn
    have hmul : (P * P) *ᵥ (b j).ofLp = (s j * s j : ℂ) • (b j).ofLp := by
      rw [← mulVec_mulVec]
      have he' := congrArg WithLp.ofLp (he j)
      change P *ᵥ (b j).ofLp = (s j : ℂ) • (b j).ofLp at he'
      rw [he', mulVec_smul, he', smul_smul]
    rw [hmul, dotProduct_smul] at hn
    have hb : star (b j).ofLp ⬝ᵥ (b j).ofLp = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K]
      simp
    rw [hb] at hn
    simp only [mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hn
    exact (sq_eq_sq₀ (norm_nonneg _) (hs j)).mp
      (by simpa [pow_two, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hn)
  have hdiag (j : ι) :
      (star (b j).ofLp ⬝ᵥ (A *ᵥ (b j).ofLp)).re ≤ s j := by
    have hreal : (star (b j).ofLp ⬝ᵥ (X *ᵥ (b j).ofLp)).re =
        (star (b j).ofLp ⬝ᵥ (A *ᵥ (b j).ofLp)).re := by
      have him : (star (b j).ofLp ⬝ᵥ (B *ᵥ (b j).ofLp)).im = 0 :=
        hB.im_star_dotProduct_mulVec_self _
      simp [X, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
        Complex.mul_re, him]
    have hc := re_inner_le_norm (𝕜 := ℂ) (b j) (X.toEuclideanLin (b j))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hc
    have hcn : ‖b j‖ = 1 := b.orthonormal.1 j
    rw [hcn, hXnorm, one_mul] at hc
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp] at hc
    change ((X *ᵥ (b j).ofLp) ⬝ᵥ star (b j).ofLp).re ≤ s j at hc
    rw [dotProduct_comm, hreal] at hc
    exact hc
  let Q := CFC.sqrt A
  have hQ : Qᴴ * Q = A := by
    rw [show Qᴴ = Q from (CFC.sqrt_nonneg A).star_eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  apply Matrix.le_iff.mpr
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (hP.isHermitian.smul (isSelfAdjoint_iff.mpr rfl :
      IsSelfAdjoint (Fintype.card ι : ℝ))).sub hA.isHermitian
  intro x
  apply RCLike.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · let v : EuclideanSpace ℂ ι := WithLp.toLp 2 x
    have hbnd := basis_norm_bound Q.toEuclideanLin b v
    have hnorm (w : EuclideanSpace ℂ ι) : ‖Q.toEuclideanLin w‖ ^ 2 =
        (star w.ofLp ⬝ᵥ (A *ᵥ w.ofLp)).re := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, hQ] using norm_mulVec_sq Q w
    rw [hnorm] at hbnd
    have hh : (star x ⬝ᵥ (A *ᵥ x)).re ≤
        (Fintype.card ι : ℝ) * ∑ j, ‖b.repr v j‖ ^ 2 * s j := by
      apply hbnd.trans
      gcongr with j
      rw [hnorm]
      exact hdiag j
    rw [← eigenbasis_quadratic P b s he v] at hh
    simpa [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      Complex.sub_re, RCLike.real_smul_eq_coe_smul] using sub_nonneg.mpr hh
  · exact ((hP.isHermitian.smul (isSelfAdjoint_iff.mpr rfl :
      IsSelfAdjoint (Fintype.card ι : ℝ))).sub hA.isHermitian).im_star_dotProduct_mulVec_self x

private lemma trace_pair_pos (rho P : Matrix ι ι ℂ) (hr : rho.PosDef)
    (hP : P.PosSemidef) (hne : P ≠ 0) : 0 < (bornProbability rho P).re := by
  have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hr.posSemidef hP
  apply lt_of_le_of_ne hn
  intro hz
  obtain ⟨Y, hY, hρ⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hr.isStrictlyPositive
  let Q := CFC.sqrt P
  have hQ : Q * Q = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hQs : Qᴴ = Q := (CFC.sqrt_nonneg P).star_eq
  have htrace : ((Y * Q)ᴴ * (Y * Q)).trace = 0 := by
    apply Complex.ext
    · have he : ((Y * Q)ᴴ * (Y * Q)).trace = (rho * P).trace := by
        have he : (Y * Q)ᴴ * (Y * Q) = Q * (Yᴴ * Y) * Q := by
          simp only [conjTranspose_mul, hQs, mul_assoc]
        rw [he, mul_assoc, trace_mul_comm Q, mul_assoc, hQ]
        simpa only [star_eq_conjTranspose] using congrArg (fun Z => (Z * P).trace) hρ.symm
      rw [he]
      exact hz.symm
    · exact (RCLike.nonneg_iff.mp
        (posSemidef_conjTranspose_mul_self (Y * Q)).trace_nonneg).2
  have hzero := trace_conjTranspose_mul_self_eq_zero_iff.mp htrace
  have hQzero : Q = 0 := hY.mul_left_cancel (by simpa only [mul_zero] using hzero)
  exact hne (by rw [← hQ, hQzero, mul_zero])

private theorem denominator_pos (rho A B : Matrix ι ι ℂ) (hr : rho.PosDef)
    (hne : A + Complex.I • B ≠ 0) :
    0 < (bornProbability rho (CFC.abs (A + Complex.I • B))).re :=
  trace_pair_pos rho _ hr (CFC.abs_nonneg _).posSemidef
    (fun h => hne ((CFC.abs_eq_zero_iff (a := A + Complex.I • B)).mp h))

private theorem one_mem_quotientValues [Nonempty ι] (rho : Matrix ι ι ℂ) (hr : rho.PosDef) :
    1 ∈ quotientValues rho := by
  refine ⟨1, 0, PosSemidef.one, isHermitian_zero, ?_, ?_⟩
  · simpa using (one_ne_zero : (1 : Matrix ι ι ℂ) ≠ 0)
  · have hp := denominator_pos rho 1 0 hr (by simp)
    simpa [bornProbability] using (div_self (ne_of_gt hp)).symm

private theorem quotient_bounds (rho : Matrix ι ι ℂ) (hr : rho.PosDef)
    {q : ℝ} (hq : q ∈ quotientValues rho) : 0 ≤ q ∧ q ≤ Fintype.card ι := by
  obtain ⟨A, B, hA, hB, hne, rfl⟩ := hq
  have hp := denominator_pos rho A B hr hne
  have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hr.posSemidef hA
  have hu := RHLinalg.trace_mul_nonneg_of_posSemidef hr.posSemidef
    (Matrix.le_iff.mp (accretive_le_card_abs A B hA hB))
  refine ⟨div_nonneg hn hp.le, (div_le_iff₀ hp).mpr ?_⟩
  have hu' : 0 ≤ (Fintype.card ι : ℝ) *
      (bornProbability rho (CFC.abs (A + Complex.I • B))).re -
      (bornProbability rho A).re := by
    simpa [bornProbability, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_smul, RCLike.smul_re] using hu
  linarith

/-- Every fixed positive dimension admits the density-independent witness C = n. -/
theorem result : claim := by
  intro n hn
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨n, Nat.cast_nonneg n, ?_⟩
  intro rho hr
  have h1 := one_mem_quotientValues rho hr
  have hne : (quotientValues rho).Nonempty := ⟨1, h1⟩
  have hb : BddAbove (quotientValues rho) := ⟨n, fun q hq => by
    simpa using (quotient_bounds rho hr hq).2⟩
  have hlub : IsLUB (quotientValues rho) (a rho) := isLUB_csSup hne hb
  exact ⟨hne, hlub, hlub.2 (fun q hq => by
    simpa using (quotient_bounds rho hr hq).2)⟩

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
