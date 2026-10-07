/- GID: D5/S3/VertexAlgebra/LatticeActualConformalEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualConformalEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two inverse-Gram identities give nonhomogeneous, weighted and fused actual energy laws. -/

import D5.S3.VertexAlgebra.LatticeActualConformalWard
import D5.S3.VertexAlgebra.LatticeSugawaraConformal

/-
Nonhomogeneous actual energy covariance and its weighted / fused-state
consequences. These concern the actual carrier, actual Y, and actual
Sugawara modes, not an abstract grading record. Exactly the two supplier
inverse-Gram premises are used. No energy compatibility is a premise.
See LatticeActualConformalState for primary sources and retained licenses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeActualConformalEnergy
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeSugawaraCurrents
open LatticeActualStateFieldCalculus LatticeActualConformalState
open LatticeActualConformalWard LatticeActualStateDerivative
open LatticeSugawaraConformal MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

/-- All actual states, including arbitrary sums of different energies and
charges, satisfy this operator identity at every integer mode. -/
theorem energy_covariance (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Carrier D) (q : ℤ) :
    sugawaraMode D H 0 * ((Y D a)[[q]]) -
        ((Y D a)[[q]]) * sugawaraMode D H 0 =
      ((Y D (sugawaraMode D H 0 a))[[q]]) -
        ((q : ℂ) + 1) • ((Y D a)[[q]]) := by
  have h := one_mode_commutator D (omega D H) a q
  rw [omega_ncoeff, omega_product, omega_product,
    show (1 : ℤ) - 1 = 0 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num,
    sugawaraMode_minus_one_eq_translation D H hHG hGH,
    state_derivative_modes D] at h
  simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right] at h
  rw [h]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [neg_smul, sub_eq_add_neg, add_comm]

/-- Explicit energy eigenvectors give the genuine homogeneous mode law. -/
theorem eigenstate_mode_energy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Carrier D) (energy : ℂ)
    (ha : sugawaraMode D H 0 a = energy • a) (q : ℤ) :
    sugawaraMode D H 0 * ((Y D a)[[q]]) -
        ((Y D a)[[q]]) * sugawaraMode D H 0 =
      (energy - (q : ℂ) - 1) • ((Y D a)[[q]]) := by
  rw [energy_covariance D H hHG hGH, ha, map_smul]
  simp only [map_smul, Pi.smul_apply]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [← sub_smul]
  congr 1
  ring

theorem weighted_homogeneous_mode_energy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (p : Oscillator D) (r : ℕ)
    (hp : IsWeightedHomogeneous (fun x : Index D => x.2 + 1) p r) (q : ℤ) :
    sugawaraMode D H 0 * ((Y D (Finsupp.single beta p))[[q]]) -
        ((Y D (Finsupp.single beta p))[[q]]) * sugawaraMode D H 0 =
      ((r : ℂ) + (bilinear D beta beta : ℂ) / 2 - (q : ℂ) - 1) •
        ((Y D (Finsupp.single beta p))[[q]]) :=
  eigenstate_mode_energy D H hHG hGH (Finsupp.single beta p)
    ((r : ℂ) + (bilinear D beta beta : ℂ) / 2)
    (sugawaraMode_weighted_homogeneous D H hHG hGH beta p r hp) q

/-- Energy of the actual mode product, before imposing any eigenvalue law. -/
theorem fused_state_energy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Carrier D) (q : ℤ) :
    sugawaraMode D H 0 (mu D a q b) =
      mu D (sugawaraMode D H 0 a) q b +
        mu D a q (sugawaraMode D H 0 b) -
          ((q : ℂ) + 1) • mu D a q b := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A b)
    (energy_covariance D H hHG hGH a q)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  change sugawaraMode D H 0 (mu D a q b) -
    mu D a q (sugawaraMode D H 0 b) =
    mu D (sugawaraMode D H 0 a) q b - ((q : ℂ) + 1) • mu D a q b at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

theorem fused_eigenstate_energy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Carrier D) (alpha beta : ℂ)
    (ha : sugawaraMode D H 0 a = alpha • a)
    (hb : sugawaraMode D H 0 b = beta • b) (q : ℤ) :
    sugawaraMode D H 0 (mu D a q b) =
      (alpha + beta - (q : ℂ) - 1) • mu D a q b := by
  rw [fused_state_energy D H hHG hGH, ha, hb]
  simp only [mu, map_smul, Pi.smul_apply, LinearMap.smul_apply]
  rw [← add_smul, ← sub_smul]
  congr 1
  ring

end
end D5.S3.VertexAlgebra.LatticeActualConformalEnergy
