/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qDiagonalAnnihilationDerivative
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficientwise diagonal differentiation of the native annihilation polynomial. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qDiagonalAnnihilationTransport
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
The coefficientwise derivative in the diagonal variable `t` of the native
annihilation polynomial. The outer variable `y⁻¹` is held fixed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qIntegratedNormalMode (integratedNormalMode)
open scoped BigOperators

open private mapScalarToFock from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private translatedPolynomial_generator from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedOrderedProduct
open private positiveAnnihilator_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

local notation "R" => PowerSeries Fock
local notation "Cₜ" => (PowerSeries.C : Fock →+* R)

/-- The native inverse-cover polynomial in the regular diagonal expansion. -/
def nativeDiagonalAnnihilationPolynomial (B : FixedDualBases) (a b : Charge lattice) :
    Fock →ₐ[ℂ] Polynomial R :=
  diagonalInverseCoverPolynomial.comp ((translateOuter B b).comp (translatedPolynomial B a))

/-- Differentiate the power series coefficients in `t`. -/
def diagonalPolynomialTDerivative : Derivation Fock (Polynomial R) (Polynomial R) :=
  PolynomialModule.equivPolynomialSelf.toLinearMap.compDer
    (PowerSeries.derivative : Derivation Fock R R).mapCoeffs

@[simp] theorem coeff_diagonalPolynomialTDerivative (Q : Polynomial R) (d : ℕ) :
    (diagonalPolynomialTDerivative Q).coeff d = PowerSeries.derivative (Q.coeff d) := rfl

private theorem diagonalPolynomialTDerivative_C (f : R) :
    diagonalPolynomialTDerivative (Polynomial.C f) =
      Polynomial.C (PowerSeries.derivative f) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0 <;> simp [Polynomial.coeff_C, hn]

private theorem diagonalPolynomialTDerivative_X :
    diagonalPolynomialTDerivative (Polynomial.X : Polynomial R) = 0 := by
  change PolynomialModule.equivPolynomialSelf
    ((PowerSeries.derivative : Derivation Fock R R).mapCoeffs (Polynomial.X : Polynomial R)) = 0
  rw [Derivation.mapCoeffs_X, map_zero]

private theorem derivative_mapScalarToFock (f : PowerSeries ℂ) :
    PowerSeries.derivative (mapScalarToFock f) = mapScalarToFock (PowerSeries.derivative f) := by
  apply PowerSeries.ext
  intro n
  simp only [mapScalarToFock, PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul,
    map_add, map_natCast, map_one]

private theorem nativeDiagonalAnnihilationPolynomial_derivative_X (B : FixedDualBases)
    (a b : Charge lattice) (j : Mode) :
    diagonalPolynomialTDerivative (nativeDiagonalAnnihilationPolynomial B a b (MvPolynomial.X j)) =
      Polynomial.C (mapScalarToFock (PowerSeries.derivative
        (integratedNormalMode (frequency j : ℤ)))) * Polynomial.X ^ frequency j *
          Polynomial.C (Cₜ (positiveAnnihilator B a j.2 (MvPolynomial.X j))) := by
  have hgenerator :
      nativeDiagonalAnnihilationPolynomial B a b (MvPolynomial.X j) =
        Polynomial.C (Cₜ (MvPolynomial.X j)) +
          Polynomial.C (mapScalarToFock (integratedNormalMode (frequency j : ℤ)) *
            Cₜ (positiveAnnihilator B a j.2 (MvPolynomial.X j))) * Polynomial.X ^ frequency j -
          Polynomial.C (Cₜ (algebraMap ℂ Fock (annihilationPairing B (a + b) j))) *
            Polynomial.X ^ frequency j := by
    rw [nativeDiagonalAnnihilationPolynomial, AlgHom.comp_apply, AlgHom.comp_apply,
      ← diagonalAnnihilationPolynomial_transport, translatedPolynomial_generator]
    simp only [map_sub, map_mul, map_pow, Polynomial.aevalTower_C,
      Polynomial.aevalTower_X, AlgHom.commutes,
      Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply, diagonalAnnihilationShift,
      MvPolynomial.aeval_X]
  rw [hgenerator]
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    diagonalPolynomialTDerivative_C, diagonalPolynomialTDerivative_X, PowerSeries.derivative_C,
    mul_zero, add_zero, zero_add, map_zero, derivative_mapScalarToFock, Polynomial.C_mul]
  ring

private theorem nativeDiagonalAnnihilationPolynomial_derivative_cutoff (B : FixedDualBases)
    (a b : Charge lattice) (E : ℕ) (P : Fock)
    (hP : ∀ j ∈ P.vars, frequency j ∈ Finset.Icc 1 E) :
    diagonalPolynomialTDerivative (nativeDiagonalAnnihilationPolynomial B a b P) =
      ∑ s ∈ Finset.Icc 1 E, Polynomial.C (mapScalarToFock (PowerSeries.derivative
        (integratedNormalMode (s : ℤ)))) * Polynomial.X ^ s *
          nativeDiagonalAnnihilationPolynomial B a b (positiveAnnihilator B a (s - 1) P) := by
  let A := nativeDiagonalAnnihilationPolynomial B a b
  let S := Finset.Icc 1 E
  let weight : ℕ → Polynomial R := fun s =>
    Polynomial.C (mapScalarToFock (PowerSeries.derivative (integratedNormalMode (s : ℤ)))) *
      Polynomial.X ^ s
  change diagonalPolynomialTDerivative (A P) =
    ∑ s ∈ S, weight s * A (positiveAnnihilator B a (s - 1) P)
  have hmem : P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' {j : Mode | frequency j ∈ S}) :=
    MvPolynomial.mem_supported.mpr hP
  clear hP
  induction hmem using Algebra.adjoin_induction with
  | mem q hq =>
    obtain ⟨j, hj, rfl⟩ := hq
    have hfreq : frequency j ∈ S := hj
    rw [Finset.sum_eq_single (frequency j)]
    · have hconst :
          A (positiveAnnihilator B a j.2 (MvPolynomial.X j)) =
            Polynomial.C (Cₜ (positiveAnnihilator B a j.2 (MvPolynomial.X j))) := by
        rw [positiveAnnihilator_X, ite_eq_left rfl, Algebra.smul_def, mul_one,
          AlgHom.commutes, Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply]
      rw [show frequency j - 1 = j.2 by simp [frequency], hconst]
      exact nativeDiagonalAnnihilationPolynomial_derivative_X B a b j
    · intro s hs hne
      have hspos : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hsne : s - 1 ≠ j.2 := by unfold frequency at hne; omega
      simp only [positiveAnnihilator_X, ite_eq_right hsne, map_zero, mul_zero]
    · exact fun h => (h hfreq).elim
  | algebraMap r =>
    have hconst (s : ℕ) : positiveAnnihilator B a (s - 1) (algebraMap ℂ Fock r) = 0 := by
      simp only [MvPolynomial.algebraMap_eq, positiveAnnihilator, LinearMap.sum_apply,
        LinearMap.smul_apply, Derivation.coeFn_coe, MvPolynomial.pderiv_C, smul_zero,
        Finset.sum_const_zero]
    simp only [AlgHom.commutes, Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply,
      diagonalPolynomialTDerivative_C, PowerSeries.derivative_C, hconst, map_zero, mul_zero,
      Finset.sum_const_zero]
  | add P Q _ _ hP hQ =>
    simp only [map_add, hP, hQ, mul_add, Finset.sum_add_distrib]
  | mul P Q _ _ hP hQ =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hP, hQ, positiveAnnihilator_mul,
      map_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring

/-- The positive-mode contribution to the diagonal recurrence. Each term
lowers the input by the actual Fock annihilator and multiplies the resulting
diagonal polynomial by the differentiated mode weight and its inverse-cover
monomial. -/
theorem nativeDiagonalAnnihilationPolynomial_derivative (B : FixedDualBases)
    (a b : Charge lattice) (P : Fock) :
    diagonalPolynomialTDerivative (nativeDiagonalAnnihilationPolynomial B a b P) =
      ∑ s ∈ Finset.Icc 1 (occupationBound P),
        Polynomial.C (mapScalarToFock (PowerSeries.derivative (integratedNormalMode (s : ℤ)))) *
          Polynomial.X ^ s *
          nativeDiagonalAnnihilationPolynomial B a b (positiveAnnihilator B a (s - 1) P) := by
  apply nativeDiagonalAnnihilationPolynomial_derivative_cutoff
  intro j hj
  obtain ⟨d, hd, hjd⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
  have hpos : 1 ≤ d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hjd)
  rw [Finset.mem_Icc, occupationBound_eq]
  refine ⟨Nat.succ_pos _, ?_⟩
  calc
    frequency j ≤ d j * frequency j := by
      simpa only [one_mul] using Nat.mul_le_mul_right (frequency j) hpos
    _ ≤ ∑ i ∈ d.support, d i * frequency i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (d i * frequency i)) hjd
    _ ≤ _ := Finset.le_sup (f := fun e => ∑ i ∈ e.support, e i * frequency i) hd

#print axioms nativeDiagonalAnnihilationPolynomial
#print axioms diagonalPolynomialTDerivative
#print axioms coeff_diagonalPolynomialTDerivative
#print axioms nativeDiagonalAnnihilationPolynomial_derivative

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
