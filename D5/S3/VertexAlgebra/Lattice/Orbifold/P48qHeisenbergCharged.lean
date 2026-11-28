/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qHeisenbergCharged
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Present the signed Heisenberg commutator with the concrete charged field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPositiveCurrentChargedField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMixedCurrentChargedField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qMomentumEnergy (physicalMomentum)
open P48qThirdTwistedField
open ThirdEigenspacePairing (p48qForm)
open ThirdTwistedChargeAction (N_apply shift)
open scoped BigOperators
open private action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private project_adjoint negative_pairing from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

private theorem end_lie_def (A B : Module.End ℂ State) :
    ⁅A, B⁆ = A * B - B * A :=
  rfl

private theorem sum_smul_commutator {ι : Type*} [Fintype ι] {R : Type*} [Ring R] [Algebra ℂ R]
    (c : ι → ℂ) (A : ι → R) (B : R) :
    (∑ i, c i • A i) * B - B * (∑ i, c i • A i) =
      ∑ i, c i • (A i * B - B * A i) := by
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_sub, Finset.sum_sub_distrib]

private theorem mode_positive_eq_sum (h : Cartan) (n : ℕ) :
    mode h (.ofNat (n + 1)) =
      ∑ i, annCoordinates h n i • positiveCurrentState (i, n) := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  simp only [mode_positive_apply, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    LinearMap.smul_apply, Finsupp.smul_apply, positiveCurrentState,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, positiveCurrent_apply,
    frequency, scale, smul_smul]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun c : ℂ => c • MvPolynomial.pderiv (i, n) (w p)) (mul_comm _ _)

private theorem mode_negative_eq_sum (h : Cartan) (n : ℕ) :
    mode h (.negSucc n) =
      ∑ i, creCoordinates h n i • negativeCurrentState (i, n) := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  simp only [mode_negative_apply, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    LinearMap.smul_apply, Finsupp.smul_apply, negativeCurrentState_apply]

private theorem physicalMomentum_shift (a : Charge lattice) (p : Momentum) :
    (physicalMomentum (shift lattice g a p) : Cartan) =
      (physicalMomentum p : Cartan) + projectAt 0 (chargeVector a) := by
  have chargeVector_add (b c : Charge lattice) :
      chargeVector (b + c) = chargeVector b + chargeVector c := by
    funext i
    exact Int.cast_add (b i) (c i)
  change (3 : ℂ)⁻¹ • chargeVector (shift lattice g a p).1 =
    (3 : ℂ)⁻¹ • chargeVector p.1 + project 1 (chargeVector a)
  rw [shift_numerator, chargeVector_add, smul_add, N_apply]
  simp only [project, action_chargeVector, one_pow, one_smul, chargeVector_add]

private theorem mode_zero_single (h : Cartan) (p : Momentum) (P : Fock) :
    mode h 0 (Finsupp.single p P) =
      p48qForm h (physicalMomentum p : Cartan) • Finsupp.single p P := by
  apply Finsupp.ext
  intro q
  simp only [mode_zero_apply, Finsupp.smul_apply]
  by_cases hp : q = p
  · subst q
    rfl
  · simp only [Finsupp.single_eq_of_ne hp, smul_zero]

private theorem mode_zero_fieldCoeff_commutator (h : Cartan) (a : Charge lattice) (l : ℤ) :
    ⁅mode h 0, fieldCoeff fixedDualBases a l⁆ =
      p48qForm (projectAt 0 h) (chargeVector a) • fieldCoeff fixedDualBases a l := by
  have hpair (p : Momentum) :
      p48qForm h (physicalMomentum (shift lattice g a p) : Cartan) =
        p48qForm h (physicalMomentum p : Cartan) +
          p48qForm (projectAt 0 h) (chargeVector a) := by
    rw [physicalMomentum_shift, map_add]
    congr 1
    simpa only [projectAt, one_pow] using
      (project_adjoint (1 : ℂ) (one_pow 3) h (chargeVector a)).symm
  rw [end_lie_def]
  apply Finsupp.lhom_ext
  intro p P
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    mode_zero_single, map_smul, fieldCoeff_single]
  rw [← sub_smul, hpair, add_sub_cancel_left]

/-- The signed mode at physical index `k / 3` shifts the exponent of the
charged cover coefficient by `-k`. The current direction is projected to
the eigenspace of eigenvalue `ζ⁻ᵏ`. -/
theorem mode_fieldCoeff_commutator (h : Cartan) (a : Charge lattice) (k l : ℤ) :
    ⁅mode h k, fieldCoeff fixedDualBases a l⁆ =
      p48qForm (projectAt k h) (chargeVector a) • fieldCoeff fixedDualBases a (l - k) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      change ⁅mode h 0, fieldCoeff fixedDualBases a l⁆ =
        p48qForm (projectAt 0 h) (chargeVector a) • fieldCoeff fixedDualBases a (l - 0)
      rw [sub_zero, mode_zero_fieldCoeff_commutator]
    | succ n =>
      rw [end_lie_def, mode_positive_eq_sum,
        sum_smul_commutator (annCoordinates h n) (fun i => positiveCurrentState (i, n))
          (fieldCoeff fixedDualBases a l), positive_pairing]
      simp_rw [fieldCoeff_positiveCurrent_commutator, smul_smul]
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun _ _ => rfl
  | negSucc n =>
    rw [end_lie_def, mode_negative_eq_sum,
      sum_smul_commutator (creCoordinates h n) (fun i => negativeCurrentState (i, n))
        (fieldCoeff fixedDualBases a l), negative_pairing]
    simp_rw [fieldCoeff_commutator, smul_smul]
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun _ _ => rfl

/-- The commutator evaluated on the concrete Hahn field, at the coefficient of `x^l`. -/
theorem mode_concreteChargedField_commutator (h : Cartan) (a : Charge lattice)
    (k l : ℤ) (w : State) :
    mode h k (((HahnModule.of ℂ).symm (concreteChargedField a w)).coeff l) -
      ((HahnModule.of ℂ).symm (concreteChargedField a (mode h k w))).coeff l =
      p48qForm (projectAt k h) (chargeVector a) •
        ((HahnModule.of ℂ).symm (concreteChargedField a w)).coeff (l - k) := by
  simp only [concreteChargedField, chargedField_coeff]
  have hc := mode_fieldCoeff_commutator h a k l
  rw [end_lie_def] at hc
  exact LinearMap.congr_fun hc w

/-- The twisted current `∑ₖ h(k) x^(-k-3)` in the cover coordinate
`x`, where the physical coordinate is `x^3`. -/
def currentField (h : Cartan) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun m => mode h (-m - 3)) (by
    intro w
    obtain ⟨bound, hbound⟩ := restricted_positive_modes w
    refine ⟨-bound - 3, ?_⟩
    intro m hm
    exact le_of_not_gt fun hm' => hm (hbound h _ (by omega)))

theorem currentField_coeff (h : Cartan) (m : ℤ) :
    HVertexOperator.coeff (currentField h) m = mode h (-m - 3) :=
  rfl

private theorem projectAt_add_three (h : Cartan) (k : ℤ) :
    projectAt (k + 3) h = projectAt k h := by
  rw [projectAt_eq_fourier, projectAt_eq_fourier, Int.add_emod_right]

/-- The coefficient of `x^m y^l` in
`(x^3 - y^3) [currentField h (x), concreteChargedField a (y)]` vanishes. -/
theorem currentField_concreteChargedField_locality (h : Cartan) (a : Charge lattice)
    (m l : ℤ) :
    ⁅HVertexOperator.coeff (currentField h) (m - 3),
        HVertexOperator.coeff (concreteChargedField a) l⁆ -
      ⁅HVertexOperator.coeff (currentField h) m,
        HVertexOperator.coeff (concreteChargedField a) (l - 3)⁆ = 0 := by
  change ⁅mode h (-(m - 3) - 3), fieldCoeff fixedDualBases a l⁆ -
    ⁅mode h (-m - 3), fieldCoeff fixedDualBases a (l - 3)⁆ = 0
  rw [mode_fieldCoeff_commutator, mode_fieldCoeff_commutator,
    show -(m - 3) - 3 = (-m - 3) + 3 by omega, projectAt_add_three,
    show l - ((-m - 3) + 3) = l - 3 - (-m - 3) by omega]
  exact sub_self
    (p48qForm (projectAt (-m - 3) h) (chargeVector a) •
      fieldCoeff fixedDualBases a (l - 3 - (-m - 3)) : Module.End ℂ State)

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg.mode_fieldCoeff_commutator
#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg.mode_concreteChargedField_commutator
#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg.currentField_concreteChargedField_locality
