/- GID: D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian adjoints of the odd norm-four axis Virasoro modes. -/

import D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockChargedHermitian
import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockSugawaraHermitian

/-! Hermitian adjoints on the actual algebraic negative-parity HalfFock sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.NormFourAxisAdjoint

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockCorrectedConformal (quadratic_field normal_pair_coeff shift_identity_coeff)
open NormFourLowestGrades (charge_square_expansion)
open LatticeHalfFockTensorHermitian LatticeHalfFockChargedHermitian
open LatticeHalfFockSugawaraHermitian
open LatticeHalfFockParityField NormFourFirstGradeSpectrum
open _root_.D5.S3.VertexAlgebra.Lattice MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

variable (D : LatticeData) (hu : IsUnit D.G.det)

private def rawExponent (n : ℤ) : ℤ := -2 * n - 4

local notation "H" => tensorForm D hu

private theorem quadratic_monomial_coeff (i j : Fin D.rank) (n : ℤ)
    (x : ActualTensor D hu) :
    (correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0)))).coeff
        (rawExponent n) x =
      tensorEnd D (ActualGround D hu) (normalSum D i j n) x +
        ((1 / 8 : ℂ) * (D.G i j : ℂ)) • (if n = 0 then x else 0) := by
  have even : rawExponent n % 2 = 0 := by unfold rawExponent; omega
  have index : (-rawExponent n - 4) / 2 = n := by unfold rawExponent; omega
  have zero : rawExponent n = -4 ↔ n = 0 := by unfold rawExponent; omega
  rw [quadratic_field]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, normal_pair_coeff, shift_identity_coeff, even, ite_true,
    index, zero, tensor_normalSum]
  rfl

private theorem quadratic_monomial_adjoint (i j : Fin D.rank) (n : ℤ)
    (x y : ActualTensor D hu) :
    H ((correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0)))).coeff
        (rawExponent n) x) y =
      H x ((correctedField D hu (Finsupp.single 0 (X (i, 0) * X (j, 0)))).coeff
        (rawExponent (-n)) y) := by
  rw [quadratic_monomial_coeff, quadratic_monomial_coeff]
  have hn := tensorEnd_adjoint D hu _ _ (normalSum_adjoint D i j n) x y
  by_cases hz : n = 0
  · subst n
    simp only [neg_zero, ite_true, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul,
      map_div₀, map_intCast, map_one, map_ofNat]
    simp only [neg_zero, hn]
  · have hneg : -n ≠ 0 := by omega
    simp only [hz, hneg, ite_false, smul_zero, add_zero]
    exact hn

private theorem quadratic_coeff_adjoint (a : Charge D) (n : ℤ)
    (x y : ActualTensor D hu) :
    H ((correctedField D hu (NormFourVirasoroVector.quadraticState D a)).coeff
        (rawExponent n) x) y =
      H x ((correctedField D hu (NormFourVirasoroVector.quadraticState D a)).coeff
        (rawExponent (-n)) y) := by
  unfold NormFourVirasoroVector.quadraticState
  rw [charge_square_expansion]
  simp only [Finsupp.single_finsetSum, ← Finsupp.smul_single, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_intCast,
    quadratic_monomial_adjoint]

private theorem charged_coeff_adjoint (a : Charge D) (ha : bilinear D a a = 4)
    (n : ℤ) (x y : ActualTensor D hu) :
    H ((correctedField D hu (NormFourVirasoroVector.chargedState D a)).coeff
        (rawExponent n) x) y =
      H x ((correctedField D hu (NormFourVirasoroVector.chargedState D a)).coeff
        (rawExponent (-n)) y) := by
  have ha' : bilinear D (-a) (-a) = 4 := by
    simpa only [bilinear_neg_left, bilinear_neg_right, neg_neg] using ha
  have phase (b : Charge D) (hb : bilinear D b b = 4) : epsilon D b b = 1 := by
    rw [epsilon, LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square, hb]
    norm_num [paritySign]
  have reflect (b : Charge D) (hb : bilinear D b b = 4) :
      -rawExponent n - 2 * chargeNorm D b = rawExponent (-n) := by
    unfold rawExponent chargeNorm
    omega
  change H ((correctedField D hu
      (Finsupp.single a (1 : Oscillator D) + Finsupp.single (-a) 1)).coeff
        (rawExponent n) x) y =
    H x ((correctedField D hu
      (Finsupp.single a (1 : Oscillator D) + Finsupp.single (-a) 1)).coeff
        (rawExponent (-n)) y)
  simp only [map_add, Pi.add_apply, LinearMap.add_apply,
    corrected_singleton_coeff_charged, chargedField, HVertexOperator.coeff_of_coeff]
  rw [(charged_coefficient_field_adjoint D hu a (rawExponent n) x y).1,
    (charged_coefficient_field_adjoint D hu (-a) (rawExponent n) x y).1,
    phase a ha, phase (-a) ha', reflect a ha, reflect (-a) ha',
    one_mul, one_mul, neg_neg, add_comm]

private theorem corrected_axis_adjoint (a : Charge D) (ha : bilinear D a a = 4)
    (s : ℂ) (n : ℤ) (x y : ActualTensor D hu) :
    H ((correctedField D hu (NormFourVirasoroVector.vector D a s)).coeff
        (rawExponent n) x) y =
      H x ((correctedField D hu (NormFourVirasoroVector.vector D a (starRingEnd ℂ s))).coeff
        (rawExponent (-n)) y) := by
  simp only [NormFourVirasoroVector.vector, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    smul_eq_mul, map_div₀, map_one, map_ofNat,
    quadratic_coeff_adjoint, charged_coeff_adjoint D hu a ha]

/-- The index is the Virasoro index. The physical vertex-operator mode is `n + 1`. -/
theorem mode_adjoint (a : Charge D) (ha : bilinear D a a = 4)
    (s : ℂ) (n : ℤ) (x y : paritySpace D hu (-1)) :
    H (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[n + 1]]) x).val y.val =
      H x.val (((fixedParitySlice D hu (-1) (normFourFixedSource D a (starRingEnd ℂ s)))
        [[-n + 1]]) y).val := by
  have exp (m : ℤ) : 2 * (-(m + 1) - 1) = rawExponent m := by unfold rawExponent; omega
  simp only [fixedParitySlice, VertexOperator.ncoeff_of_coeff, LinearMap.restrict_apply,
    normFourFixedSource, exp]
  exact corrected_axis_adjoint D hu a ha s n x.val y.val

/-- For either Ising sign, opposite Virasoro modes are adjoints in the inherited
positive form on the actual negative-parity sector. -/
theorem ising_mode_adjoint (positive : (LatticeOscillatorFockMetric.gramReal D).PosDef)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (n : ℤ) :
    (∀ x : paritySpace D hu (-1), x ≠ 0 → 0 < (H x.val x.val).re) ∧
    (∀ x y : paritySpace D hu (-1),
      H (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[n + 1]]) x).val y.val =
        H x.val (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[(-n) + 1]])
          y).val) := by
  constructor
  · intro x hx
    exact tensorForm_positive D hu positive x.val (fun h => hx (Subtype.ext h))
  · intro x y
    have realSign : starRingEnd ℂ s = s := by
      rcases sq_eq_one_iff.mp hs with rfl | rfl
      · exact map_one _
      · simp only [map_neg, map_one]
    simpa only [realSign] using mode_adjoint D hu a ha s n x y

#print axioms mode_adjoint
#print axioms ising_mode_adjoint

end
end D5.S3.VertexAlgebra.HalfFock.NormFourAxisAdjoint
