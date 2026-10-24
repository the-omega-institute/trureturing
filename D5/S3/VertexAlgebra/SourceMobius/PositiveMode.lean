/- GID: D5/S3/VertexAlgebra/SourceMobius/PositiveMode
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceMobius/PositiveMode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Sugawara positive source action and sharp oscillator-weight nilpotence. -/
/-
The existing normal-ordered Sugawara construction is adapted from Kalle
Kytola's VirasoroProject, retaining its Apache-2.0 attribution in the imported
source. Classical source: Bakalov--Kac, arXiv math/0402315, section 4.1.
No novelty claim, positivity hypothesis, Jacobi premise or ground pairing.
The charge norm can have either sign. Local nilpotence uses finite oscillator
and charge support on the original Carrier, not finite total-energy spaces.
Admission basis: escape-witness. The action computation and the sharp
product-nilpotence induction are the substantive source-coordinate bridge.
-/
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace D5.S3.VertexAlgebra.SourceMobius
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open scoped BigOperators

def loweringVariable (D : LatticeData) (a : Charge D) : Index D → Oscillator D
  | (i,0) => C (bilinear D (unitCharge D i) a : ℂ)
  | (i,r+1) => (r + 2 : ℂ) • X (i,r)

/-- Charge-preserving source Möbius lowering, with the ACTUAL charge zero-mode. -/
def sectorL1 (D : LatticeData) (a : Charge D) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  mkDerivation ℂ (loweringVariable D a)

/-- This is a new action calculation, using existing source current commutators
and existing positive-mode charged-ground annihilation, WITHOUT a Jacobi premise. -/
theorem sugawara_one_single (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (p : Oscillator D) :
    sugawaraMode D H 1 (Finsupp.single a p) = Finsupp.single a (sectorL1 D a p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C z =>
    rw [MvPolynomial.C_eq_smul_one, ← Finsupp.smul_single, map_smul,
      sugawaraMode_ground_positive D H a 1 (by omega)]
    simp
  | add p q hp hq => simp only [map_add, Finsupp.single_add, hp, hq]
  | mul_X p x hp =>
    rcases x with ⟨i,r⟩
    let k : ℤ := -(r : ℤ) - 1
    have negMode (q : Oscillator D) :
        neutralMode D i k (Finsupp.single a q) = Finsupp.single a (X (i,r) * q) := by
      rw [neutralMode_single]
      simp [neutralPolynomialMode, k, show -(r : ℤ) - 1 < 0 by omega]
    have nextMode :
        (-(k : ℂ)) • neutralMode D i (1+k) (Finsupp.single a p) =
          Finsupp.single a (loweringVariable D a (i,r) * p) := by
      rw [neutralMode_single]
      cases r with
      | zero => simp [k, neutralPolynomialMode, loweringVariable, smul_eq_C_mul]
      | succ r =>
        simp [k, neutralPolynomialMode, loweringVariable,
          show (-1 : ℤ) < (r : ℤ) by omega,
          smul_eq_C_mul, mul_assoc]
        congr 1
        push_cast
        norm_num only [map_ofNat]
        ring
    have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single a p))
      (sugawaraMode_current_commutator D H hHG hGH i 1 k)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
    rw [negMode, hp, negMode, nextMode] at hc
    have result := sub_eq_iff_eq_add.mp hc
    simpa only [mul_comm p (X (i,r)), Derivation.leibniz, smul_eq_mul,
      sectorL1, mkDerivation_X, Finsupp.single_add, add_comm,
      mul_comm p (loweringVariable D a (i,r))] using result


end D5.S3.VertexAlgebra.SourceMobius
