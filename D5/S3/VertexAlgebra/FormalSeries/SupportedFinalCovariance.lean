/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed monomial multiplication for native formal series. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision
/-! Native monomial multiplication is a signed coefficient translation. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.SupportedFinalCovariance
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
noncomputable section
def signedExtension {R : Type*} [CommRing R] [Algebra ℂ R] :
    MvPowerSeries (Fin 3) R →ₗ[ℂ] Distribution 3 R where
  toFun := signedExtend
  map_add' P Q := by
    funext e
    by_cases he : ∀ i, 0 ≤ e i <;> simp [signedExtend, he] <;> rfl
  map_smul' c P := by
    funext e
    by_cases he : ∀ i, 0 ≤ e i <;> simp [signedExtend, he] <;> rfl

private theorem signed_monomial_mul {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (d : Fin 3 →₀ ℕ) (e : Exponent 3) :
    signedExtend (MvPowerSeries.monomial d 1 * P) e =
      signedExtend P (fun i => e i - d i) := by
  classical
  by_cases he : ∀ i, 0 ≤ e i
  · rw [signedExtend, if_pos he]
    change MvPowerSeries.coeff (signedIndex e) (MvPowerSeries.monomial d 1 * P) = _
    rw [mul_comm, MvPowerSeries.coeff_mul_monomial]
    by_cases hd : d ≤ signedIndex e
    · rw [if_pos hd, mul_one, signedExtend,
        if_pos (show ∀ i, 0 ≤ e i - d i by
          intro i
          have hi := hd i
          change d i ≤ (e i).toNat at hi
          have := Int.toNat_of_nonneg (he i)
          omega)]
      apply congrArg P
      ext i
      change (e i).toNat - d i = (e i - d i).toNat
      have hi := hd i
      change d i ≤ (e i).toNat at hi
      omega
    · rw [if_neg hd]
      symm
      apply if_neg
      intro hs
      apply hd
      intro i
      change d i ≤ (e i).toNat
      have hi : 0 ≤ e i - (d i : ℤ) := hs i
      have hei := he i
      omega
  · have hs : ¬ ∀ i, 0 ≤ e i - d i := by
      intro hs
      apply he
      intro i
      have hi : 0 ≤ e i - (d i : ℤ) := hs i
      omega
    simp only [signedExtend, if_neg he, if_neg hs]

/-- A native nonnegative monomial is an actual signed translation. -/
theorem signed_X_pow_mul {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (i : Fin 3) (n : ℕ) (e : Exponent 3) :
    signedExtend (MvPowerSeries.X i ^ n * P) e =
      signedExtend P (e - n • Pi.single i 1) := by
  rw [MvPowerSeries.X_pow_eq, signed_monomial_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp [nsmul_eq_mul]
  · simp [Pi.single_apply, h, Ne.symm h, Finsupp.single_eq_of_ne h]

end
end D5.S3.VertexAlgebra.SupportedFinalCovariance
