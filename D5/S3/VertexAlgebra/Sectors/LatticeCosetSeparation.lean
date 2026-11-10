/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetSeparation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native old-current transport on arbitrary transverse target polynomials. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetTransverse

/-!
Orthogonal oscillator separation for the native lattice fields of
Bakalov--Kac, math/0402315v1, section 4.1. The original integral charges,
cocycle and half diagonal are unchanged. Only the old Gram matrix is
positive definite; no positivity or nondegeneracy of the ambient form is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetSeparation

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeCosetCompression LatticeCosetTransverse
open LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private gram_longitudinal_complex weightedPartial_mul weightedPartial_variable
  old_current_pairing injection_single projection_single polynomialProjection_injection
  from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- Embed an arbitrary transverse polynomial into the actual ambient ring. -/
def transversePolynomial : MvPolynomial (Fin e × ℕ) ℂ →ₐ[ℂ]
    Oscillator (ambient D e B C hC hCe) :=
  aeval (fun x : Fin e × ℕ => transverse D B C hC hCe x.1 x.2)

/-- The bilinear oscillator embedding with a fixed external charge. -/
def mixedState (d : Fin e → ℤ) (h : MvPolynomial (Fin e × ℕ) ℂ) :
    Carrier D →ₗ[ℂ] Carrier (ambient D e B C hC hCe) :=
  Finsupp.lsum ℂ (fun n =>
    (Finsupp.lsingle (liftCharge D B C hC hCe d n)).comp
      ((LinearMap.mulRight (transversePolynomial D B C hC hCe h)).comp
        (polynomialInjection D B C hC hCe).toLinearMap))

private theorem mixedState_single (d : Fin e → ℤ)
    (h : MvPolynomial (Fin e × ℕ) ℂ) (n : Charge D) (f : Oscillator D) :
    mixedState D B C hC hCe d h (Finsupp.single n f) =
      Finsupp.single (liftCharge D B C hC hCe d n)
        (polynomialInjection D B C hC hCe f * transversePolynomial D B C hC hCe h) := by
  simp [mixedState]

private theorem partial_transverse (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r : ℕ) (j : Fin e) (k : ℕ) :
    weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
      (transverse D B C hC hCe j k) = 0 := by
  classical
  simp only [transverse, map_sub, map_sum, map_smul, weightedPartial_variable]
  by_cases hr : r = k
  · simp only [hr, ↓reduceIte, ambient, Fin.addCases_left, Fin.addCases_right]
    simp only [MvPolynomial.smul_eq_C_mul, ← map_mul, ← map_sum]
    rw [show (∑ t, (longitudinal D B t j : ℂ) * (D.G i t : ℂ)) = (B i j : ℂ) by
      simpa only [mul_comm] using gram_longitudinal_complex D B hD i j]
    exact sub_self _
  · simp [hr]

private theorem partial_transversePolynomial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r : ℕ) (h : MvPolynomial (Fin e × ℕ) ℂ) :
    weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
      (transversePolynomial D B C hC hCe h) = 0 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C z => simp [transversePolynomial, weightedPartial]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p x hp =>
    rw [map_mul, weightedPartial_mul, hp, zero_mul, zero_add]
    simp only [transversePolynomial, aeval_X]
    rw [partial_transverse D B C hC hCe hD, mul_zero]

private theorem partial_injection (i : Fin D.rank) (r : ℕ) (f : Oscillator D) :
    weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
        (polynomialInjection D B C hC hCe f) =
      polynomialInjection D B C hC hCe (weightedPartial D i r f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C z => simp [polynomialInjection, weightedPartial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    have hx : weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r
        (polynomialInjection D B C hC hCe (X x)) =
        polynomialInjection D B C hC hCe (weightedPartial D i r (X x)) := by
      simp only [polynomialInjection, rename_X, weightedPartial_variable]
      split_ifs <;> simp [ambient]
    simp only [map_mul, weightedPartial_mul, map_add, hp, hx]

/-- Every actual old current acts only on the longitudinal target factor,
including arbitrary transverse polynomials and all integer modes. -/
theorem current_mixed_polynomial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (d : Fin e → ℤ) (n : Charge D) (m : ℤ)
    (f : Oscillator D) (h : MvPolynomial (Fin e × ℕ) ℂ) :
    neutralPolynomialMode (ambient D e B C hC hCe) (i.castAdd e)
        (liftCharge D B C hC hCe d n) m
        (polynomialInjection D B C hC hCe f * transversePolynomial D B C hC hCe h) =
      polynomialInjection D B C hC hCe
        (LatticeDualCosetModule.shiftedCurrentPolynomial D (Matrix.mulVec B d) 1 i n m f) *
          transversePolynomial D B C hC hCe h := by
  by_cases hm : m < 0
  · simp [neutralPolynomialMode, LatticeDualCosetModule.shiftedCurrentPolynomial,
      hm, polynomialInjection, mul_assoc]
  · by_cases hz : m = 0
    · have hp := old_current_pairing D B C hC hCe i (liftCharge D B C hC hCe d n)
      simp only [oldCharge, externalCharge, liftCharge, Fin.addCases_left,
        Fin.addCases_right] at hp
      simp [neutralPolynomialMode, LatticeDualCosetModule.shiftedCurrentPolynomial,
        hm, hz, hp, map_smul, smul_mul_assoc]
    · change ((m : ℂ) • weightedPartial (ambient D e B C hC hCe) (i.castAdd e)
        (m-1).toNat) _ = _
      simp only [LinearMap.smul_apply, weightedPartial_mul, partial_injection,
        partial_transversePolynomial D B C hC hCe hD, mul_zero, add_zero]
      simp [LatticeDualCosetModule.shiftedCurrentPolynomial, hm, hz, weightedPartial,
        map_smul, smul_mul_assoc]

/-- Native shifted currents already have statewise truncation. The full
ambient current intertwines their action on every transverse target factor. -/
theorem current_mixed (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (d : Fin e → ℤ) (m : ℤ) (g : Carrier D)
    (h : MvPolynomial (Fin e × ℕ) ℂ) :
    neutralMode (ambient D e B C hC hCe) (i.castAdd e) m
        (mixedState D B C hC hCe d h g) =
      mixedState D B C hC hCe d h
        (((LatticeDualCosetModule.action D (Matrix.mulVec B d)
          (Finsupp.single (0 : Charge D) (X (i,0))))[[m]]) g) := by
  have he : (neutralMode (ambient D e B C hC hCe) (i.castAdd e) m).comp
      (mixedState D B C hC hCe d h) =
      (mixedState D B C hC hCe d h).comp
        ((LatticeDualCosetModule.action D (Matrix.mulVec B d)
          (Finsupp.single (0 : Charge D) (X (i,0))))[[m]]) := by
    apply Finsupp.lhom_ext
    intro n f
    simp only [LinearMap.comp_apply, mixedState_single,
      LatticeDualCosetModule.action_current_coefficients, neutralMode,
      Finsupp.lsum_single, Finsupp.lsingle_apply]
    rw [current_mixed_polynomial D B C hC hCe hD]
  exact DFunLike.congr_fun he g

end
end D5.S3.VertexAlgebra.LatticeCosetSeparation
