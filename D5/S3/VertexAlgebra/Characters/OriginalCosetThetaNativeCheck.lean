/- Transient exact application check, not a retained library declaration. -/
import D5.S3.Fourier.MatrixGaussianSourcePoisson
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory Matrix
open D5.S3.Fourier.MatrixGaussian
open D5.S3.VertexAlgebra LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open TwistedGround.OriginalFourMChargeCoset

namespace OriginalCosetThetaNativeCheck
noncomputable section

private def source (D : LatticeData) (a : Charge D) (V : Fin D.rank → ℂ) : ℂ :=
  ∑ i, ∑ j, (a i : ℂ)*(D.G i j : ℂ)*V j

private def theta (D : LatticeData) (a : ModTwoCharge D) (τ : ℂ) (V : Fin D.rank → ℂ) : ℂ :=
  ∑' l : Charge D, if reduceCharge D l = a then
    Complex.exp (Real.pi*Complex.I*τ*(bilinear D l l : ℂ)/2 + source D l V) else 0

private lemma term_T (D : LatticeData) (τ : ℂ) (V : Fin D.rank → ℂ) (l : Charge D) :
    Complex.exp (Real.pi*Complex.I*(τ+1)*(bilinear D l l : ℂ)/2 + source D l V) =
      quadraticSign D (reduceCharge D l) *
        Complex.exp (Real.pi*Complex.I*τ*(bilinear D l l : ℂ)/2 + source D l V) := by
  have hq : (bilinear D l l : ℂ)/2 = (chargeEnergy D l : ℂ) := by
    have h := congrArg (fun k : ℤ => (k : ℂ)) (two_chargeEnergy D l)
    push_cast at h
    linear_combination -h/2
  have he : Complex.exp (Real.pi*Complex.I*(bilinear D l l : ℂ)/2) =
      paritySign (chargeEnergy D l) := by
    rw [show Real.pi*Complex.I*(bilinear D l l : ℂ)/2 =
      (chargeEnergy D l : ℂ)*(Real.pi*Complex.I) by rw [mul_div_assoc, hq]; ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I, neg_one_zpow_eq_ite]
    rfl
  rw [show Real.pi*Complex.I*(τ+1)*(bilinear D l l : ℂ)/2 + source D l V =
    Real.pi*Complex.I*(bilinear D l l : ℂ)/2 +
      (Real.pi*Complex.I*τ*(bilinear D l l : ℂ)/2 + source D l V) by ring,
    Complex.exp_add, he, quadraticSign_integral]
  rfl

-- The full-source original T telescope, checked anonymously.
example (D : LatticeData) (a : ModTwoCharge D) (τ : ℂ) (V : Fin D.rank → ℂ) :
    theta D a (τ+1) V = quadraticSign D a * theta D a τ V := by
  unfold theta
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  split_ifs with h
  · rw [term_T, h]
  · simp

-- Genuine absolute summability over every original charge with the literal source.
example (D : LatticeData)
    (hD : (D.G.map (Int.cast : ℤ → ℝ)).PosDef)
    (a : ModTwoCharge D) (τ : ℂ) (hτ : 0 < τ.im) (V : Fin D.rank → ℂ) :
    Summable (fun l : Charge D => ‖if reduceCharge D l = a then
      Complex.exp (Real.pi*Complex.I*τ*(bilinear D l l : ℂ)/2 + source D l V) else 0‖) := by
  let A : Matrix (Fin D.rank) (Fin D.rank) ℝ := D.G.map (Int.cast : ℤ → ℝ)
  let z : Fin D.rank → ℂ := (D.G.map (Int.castRingHom ℂ)) *ᵥ V
  have hb : 0 < (-Complex.I*τ/2).re := by simpa using half_pos hτ
  have h := summable_norm_source_gaussian A hD (-Complex.I*τ/2) hb z
  have he (l : Charge D) : sourceGaussianMap A (-Complex.I*τ/2) z
      (fun i => (l i : ℝ)) =
      Complex.exp (Real.pi*Complex.I*τ*(bilinear D l l : ℂ)/2 + source D l V) := by
    change Complex.exp _ = Complex.exp _
    congr 1
    have hQ : (quadratic A (fun i => (l i : ℝ)) : ℂ) = (bilinear D l l : ℂ) := by
      simp [A, quadratic, bilinear, Matrix.mulVec, dotProduct, Finset.mul_sum,
        Complex.ofReal_sum, Complex.ofReal_mul]
    rw [hQ]
    dsimp [z, source, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum, ← Complex.intCast_mul, ← Complex.intCast_sum]
    push_cast
    ring
  have hs := h.congr (fun l => congrArg norm (he l))
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
  split_ifs <;> simp

end
end OriginalCosetThetaNativeCheck
