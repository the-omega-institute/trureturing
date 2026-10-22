/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorGroundRigidity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorGroundRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual polynomial-current commutant controls the ground coefficient recurrence. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorReconstruction

/-!
Ground coefficient rigidity uses the existing actual polynomial-current
commutant theorem. No private polynomial-rigidity proof is copied.
The intended ground uniqueness route is downward induction from the
statewise pole bound, with positive Ward and the actual conformal zero mode.
Classical free-boson source and Sugawara architecture attribution remain
Bakalov--Kac and Kalle Kytölä as in the imported suppliers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeActualConformalState
open MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

/-- Positive-current annihilation forces a scalar by the actual commutant telescope. -/
theorem scalar_of_positive_currents (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (γ : Charge D) (g : Oscillator D)
    (hpos : ∀ (i : Fin D.rank) (r : ℕ),
      neutralPolynomialMode D i γ ((r : ℤ) + 1) g = 0) :
    g = constantCoeff g • (1 : Oscillator D) := by
  have hz (i : Fin D.rank) (r : ℕ) : weightedPartial D i r g = 0 := by
    have h := hpos i r
    rw [neutralPolynomialMode_positive, LinearMap.smul_apply] at h
    exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.succ_ne_zero r)
  have leibniz (i : Fin D.rank) (r : ℕ) (p : Oscillator D) :
      weightedPartial D i r (g * p) =
        g * weightedPartial D i r p + p * weightedPartial D i r g := by
    let d : Derivation ℂ (Oscillator D) (Oscillator D) :=
      ∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j, r)
    simpa [d, weightedPartial, smul_eq_mul] using d.leibniz g p
  let A : Module.End ℂ (Oscillator D) := LinearMap.mulLeft ℂ g
  have commutes (i : Fin D.rank) (q : ℤ) :
      A * neutralPolynomialMode D i γ q - neutralPolynomialMode D i γ q * A = 0 := by
    by_cases neg : q < 0
    · apply LinearMap.ext
      intro p
      simp only [A, neutralPolynomialMode, if_pos neg, LinearMap.sub_apply,
        Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
      ring
    · by_cases zero : q = 0
      · subst q
        apply LinearMap.ext
        intro p
        simp [A, neutralPolynomialMode, Module.End.mul_apply, smul_eq_C_mul,
          mul_comm, mul_left_comm, mul_assoc]
      · let r : ℕ := (q - 1).toNat
        have index : q = (r : ℤ) + 1 := by dsimp [r]; omega
        rw [index, neutralPolynomialMode_positive]
        apply LinearMap.ext
        intro p
        simp only [A, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.mulLeft_apply, leibniz, hz, mul_zero, add_zero, LinearMap.zero_apply]
        simp [smul_eq_C_mul, mul_comm, mul_left_comm, mul_assoc]
  have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F 1)
    (polynomial_current_commutant_scalar D H hHG γ A commutes)
  simpa [A] using h

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
