/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthDefect
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fourth-order pairing defect under a quadratic relation is evaluated exactly. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticFourthExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticCubicExpansion

/-! Lemma 498.2 follows by subtracting the three second-moment products. -/

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing A] [Algebra ℝ A]

/-- Lemma 498.2: the fourth-order pairing defect under a quadratic relation. -/
theorem quadratic_fourth_pairing_defect
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hq : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g h q : ι → ℝ) :
    quadraticFamilyMoment ℓ Y ![f,g,h,q] - perfectPairingSum (fun u v => quadraticFamilyMoment ℓ Y ![u,v]) f g h q =
    distinctIndexMoment ℓ Y ![f,g,h,q] - perfectPairingSum (fun u v => distinctIndexMoment ℓ Y ![u,v]) f g h q +
      a * repeatedPairSum (fun u v w => distinctIndexMoment ℓ Y ![u,v,w]) f g h q +
      a^2 * pairPairSum (fun u v => distinctIndexMoment ℓ Y ![u,v]) f g h q +
      (a^2-2*b) * tripleSingletonSum (fun u v => distinctIndexMoment ℓ Y ![u,v]) f g h q +
      (a^2*b-2*b^2) * indexSum (f*g*h*q) := by
  rw [quadratic_fourth_moment_expansion ℓ Y a b h1 h0 hq]
  simp only [perfectPairingSum, repeatedPairSum, quadratic_second_moment_eq ℓ Y a b h1 h0 hq]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
