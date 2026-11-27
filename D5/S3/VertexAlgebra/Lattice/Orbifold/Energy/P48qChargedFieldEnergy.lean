import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMixedCurrentChargedField
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Module

/-!
The energy degree of the charged coefficients on the constructed P48q state carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy

open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum)
open P48qThirdTwistedField
open MvPolynomial
open scoped BigOperators

noncomputable section

local notation "N" => ThirdTwistedChargeAction.N lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g

private theorem pair_norm_of_fixed (x a : Charge lattice) (hx : g x = x) :
    bilinear lattice x (N a) = 3 * bilinear lattice x a := by
  have step (y : Charge lattice) : bilinear lattice x (g y) = bilinear lattice x y := by
    simpa only [hx] using g_isometry x y
  rw [ThirdTwistedChargeAction.N_apply, bilinear_add_right, bilinear_add_right,
    step (g a), step a]
  ring

/-- The change in the integral squared norm under the actual charge shift. -/
theorem shift_norm_difference (a : Charge lattice) (p : Momentum) :
    bilinear lattice (shift a p).1 (shift a p).1 - bilinear lattice p.1 p.1 =
      6 * bilinear lattice p.1 a + 3 * bilinear lattice (N a) a := by
  obtain ⟨b, hb⟩ := (show ∃ b, N b = p.1 from p.2)
  have hp : g p.1 = p.1 := by
    rw [← hb]
    exact ThirdTwistedChargeAction.norm_fixed lattice g g_cube b
  have hcross := pair_norm_of_fixed p.1 a hp
  have hnorm := pair_norm_of_fixed (N a) a
    (ThirdTwistedChargeAction.norm_fixed lattice g g_cube a)
  have hadd (x y z : Charge lattice) :
      bilinear lattice (x + y) z = bilinear lattice x z + bilinear lattice y z := by
    rw [bilinear_symmetric lattice (x + y) z, bilinear_add_right,
      bilinear_symmetric lattice z x, bilinear_symmetric lattice z y]
  rw [shift_numerator, hadd, bilinear_add_right, bilinear_add_right,
    bilinear_symmetric lattice (N a) p.1, hcross, hnorm]
  ring

/-- The ground energy change computed from the native momentum exponent. -/
theorem momentumWeight_shift (a : Charge lattice) (p : Momentum) :
    (momentumWeight (shift a p) : ℂ) - (momentumWeight p : ℂ) =
      (momentumExponent a p : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 := by
  have hdiff :
      (bilinear lattice (shift a p).1 (shift a p).1 : ℂ) - (bilinear lattice p.1 p.1 : ℂ) =
        6 * (bilinear lattice p.1 a : ℂ) + 3 * (bilinear lattice (N a) a : ℂ) := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z : ℂ)) (shift_norm_difference a p)
  have hnorm :
      (bilinear lattice (N a) (N a) : ℂ) = 3 * (bilinear lattice (N a) a : ℂ) := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ℂ))
      (pair_norm_of_fixed (N a) a (ThirdTwistedChargeAction.norm_fixed lattice g g_cube a))
  have hexp :
      (momentumExponent a p : ℂ) =
        3 * ((ThirdTwistedChargeAction.bShift lattice g a : ℂ) + (bilinear lattice a p.1 : ℂ) / 3) := by
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] using
      congrArg (fun z : ℚ => (z : ℂ)) (momentumExponent_eq a p)
  have hb :
      (ThirdTwistedChargeAction.bShift lattice g a : ℂ) =
        ((bilinear lattice (N a) (N a) : ℂ) / 9 - (bilinear lattice a a : ℂ)) / 2 := by
    simp only [ThirdTwistedChargeAction.bShift, Rat.cast_div, Rat.cast_sub,
      Rat.cast_intCast, Rat.cast_ofNat]
  simp only [momentumWeight, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  rw [← sub_div, hdiff, hexp, hb, hnorm, bilinear_symmetric lattice a p.1]
  ring

private theorem occupationFrequency_eq_weight (d : Occupation) :
    occupationFrequency d = Finsupp.weight frequency d := by
  simp [occupationFrequency, Finsupp.weight_apply, Nat.nsmul_eq_mul, Nat.mul_comm]

private theorem oscillator_of_homogeneous {P : Fock} {n : ℕ}
    (h : P.IsWeightedHomogeneous frequency n) :
    oscillator P = ((n : ℂ) / 3) • P := by
  apply MvPolynomial.ext
  intro d
  rw [oscillator_coeff, coeff_smul, smul_eq_mul]
  by_cases hd : P.coeff d = 0
  · simp only [hd, mul_zero]
  · rw [occupationFrequency_eq_weight, h hd]

private theorem oscillator_one : oscillator (1 : Fock) = 0 := by
  simpa only [Nat.cast_zero, zero_div, zero_smul] using
    oscillator_of_homogeneous (isWeightedHomogeneous_one ℂ frequency)

private theorem oscillator_X_mul (j : Mode) (P : Fock) :
    oscillator (X j * P) = X j * oscillator P + ((frequency j : ℂ) / 3) • (X j * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [oscillator_monomial d c, mul_smul_comm, ← add_smul]
    have hmul : X j * monomial d c = monomial (Finsupp.single j 1 + d) c := by
      simpa only [pow_one] using
        (monomial_single_add (n := j) (e := 1) (s := d) (a := c)).symm
    have weight_add :
        Finsupp.weight frequency (Finsupp.single j 1 + d) =
          Finsupp.weight frequency (Finsupp.single j 1) + Finsupp.weight frequency d :=
      map_add (Finsupp.weight frequency) _ _
    rw [hmul, oscillator_monomial (Finsupp.single j 1 + d) c]
    simp only [occupationFrequency_eq_weight, weight_add, Finsupp.weight_single,
      one_smul, Nat.cast_add, add_div]
    rw [add_comm ((frequency j : ℂ) / 3) ((Finsupp.weight frequency d : ℂ) / 3)]
  | add P Q hP hQ =>
    simp only [mul_add, map_add, hP, hQ, smul_add]
    abel

private theorem creationSeries_homogeneous (B : FixedDualBases) (a : Charge lattice) (n : ℕ) :
    (PowerSeries.coeff n (creationSeries B a)).IsWeightedHomogeneous frequency n := by
  cases n with
  | zero =>
    rw [creationSeries, PowerSeries.coeff_mk]
    exact isWeightedHomogeneous_zero ℂ frequency 0
  | succ n =>
    rw [coeff_creationSeries_succ]
    let W := weightedHomogeneousSubmodule ℂ frequency (n + 1)
    change _ ∈ W
    apply W.smul_mem
    apply W.sum_mem
    intro i _
    exact W.smul_mem _ (isWeightedHomogeneous_X ℂ frequency (i, n))

private theorem creationExponential_homogeneous (B : FixedDualBases) (a : Charge lattice) (n : ℕ) :
    (PowerSeries.coeff n (creationExponential B a)).IsWeightedHomogeneous frequency n := by
  have hpow (r : ℕ) : ∀ m : ℕ,
      (PowerSeries.coeff m (creationSeries B a ^ r)).IsWeightedHomogeneous frequency m := by
    induction r with
    | zero =>
      intro m
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs with hm
      · subst m
        exact isWeightedHomogeneous_one ℂ frequency
      · exact isWeightedHomogeneous_zero ℂ frequency m
    | succ r ih =>
      intro m
      rw [pow_succ, PowerSeries.coeff_mul]
      apply IsWeightedHomogeneous.sum
      intro ij hij
      have hindex : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [← hindex]
      exact (ih ij.1).mul (creationSeries_homogeneous B a ij.2)
  have hzero : PowerSeries.constantCoeff (creationSeries B a) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, creationSeries, PowerSeries.coeff_mk]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hzero
  rw [creationExponential, PowerSeries.coeff_subst' hs,
    finsum_eq_sum _ (PowerSeries.coeff_subst_finite' hs (PowerSeries.exp Fock) n)]
  apply IsWeightedHomogeneous.sum
  intro r _
  rw [← PowerSeries.map_exp (algebraMap ℂ Fock), PowerSeries.coeff_map,
    smul_eq_mul, ← Algebra.smul_def]
  exact (weightedHomogeneousSubmodule ℂ frequency n).smul_mem _ (hpow r n)

private theorem oscillator_creationCoeff (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    oscillator (creationCoeff B a k) = ((k : ℂ) / 3) • creationCoeff B a k := by
  unfold creationCoeff
  by_cases hk : k < 0
  · simp only [if_pos hk, map_zero, smul_zero]
  · have hcast : (k.toNat : ℂ) = (k : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_of_not_gt hk)]
    simpa only [if_neg hk, hcast] using
      oscillator_of_homogeneous (creationExponential_homogeneous B a k.toNat)

/-- The oscillator coefficient has energy degree (k/3) on the full polynomial Fock space. -/
theorem oscillatorCoeff_degree_apply (B : FixedDualBases) (a : Charge lattice) (P : Fock) (k : ℤ) :
    oscillator (oscillatorCoeff B a k P) =
      oscillatorCoeff B a k (oscillator P) + ((k : ℂ) / 3) • oscillatorCoeff B a k P := by
  revert k
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro k
    simp only [C_eq_smul_one, map_smul, oscillator_one, smul_zero, map_zero, zero_add,
      oscillatorCoeff_one, oscillator_creationCoeff, smul_comm c ((k : ℂ) / 3)]
  | add P Q hP hQ =>
    intro k
    simp only [map_add, hP k, hQ k, smul_add]
    abel
  | mul_X P j ih =>
    intro k
    have htranslate (l : ℤ) (Q : Fock) :
        oscillatorCoeff B a l (X j * Q) =
          X j * oscillatorCoeff B a l Q -
            annihilationPairing B a j • oscillatorCoeff B a (l + (frequency j : ℤ)) Q := by
      rw [← oscillatorCoeff_commutator_apply B a j l Q, sub_sub_cancel]
    rw [mul_comm P (X j)]
    simp only [htranslate, oscillator_X_mul, map_sub, map_add, map_smul, ih,
      mul_add, mul_smul_comm, Int.cast_add, Int.cast_natCast]
    module

private theorem totalLZero_single (p : Momentum) (P : Fock) :
    totalLZero (Finsupp.single p P) =
      Finsupp.single p (oscillator P + (momentumWeight p : ℂ) • P + (16 / 9 : ℂ) • P) := by
  simp only [totalLZero, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, momentumEnergy_single,
    Finsupp.smul_single, Finsupp.single_add]

/-- The zero mode grades each coefficient of the actual charged field in the cover coordinate. -/
theorem totalLZero_fieldCoeff_commutator (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    totalLZero.comp (fieldCoeff B a k) - (fieldCoeff B a k).comp totalLZero =
      ((k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2) • fieldCoeff B a k := by
  apply Finsupp.lhom_ext
  intro p P
  have hdegree :
      ((k - momentumExponent a p : ℤ) : ℂ) / 3 +
        ((momentumWeight (shift a p) : ℂ) - (momentumWeight p : ℂ)) =
        (k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 := by
    rw [momentumWeight_shift, Int.cast_sub]
    ring
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    totalLZero_single, fieldCoeff_single, Finsupp.smul_single, ← Finsupp.single_sub]
  apply congrArg (Finsupp.single (shift a p))
  rw [← hdegree]
  simp only [map_add, map_smul, oscillatorCoeff_degree_apply]
  module

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
