/- GID: D5/S3/VertexAlgebra/Lattice/P48qLiftAnomaly
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/P48qLiftAnomaly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd-order lift rigidity on actual fixed charge lines and the P48q type. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic

/-!
The charge product is the leading lattice vertex mode on the original
zero-oscillator states in the finite-support carrier. Commutation with a lift
of inversion and multiplicativity for this product force fixed-charge phases
to have order dividing two. An odd operator period makes the phases trivial.

The spectral inputs for P48q are exposed as hypotheses. Nebe, arXiv:1312.3780,
Tables 1 and 2 give the lattice rank and order-three fixed rank.
Gemünden–Keller, arXiv:1909.09626, defines standard lifts by their action on
fixed charges and gives the lowest twisted weight and cyclic type in
equations (113) and (24).
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.P48qLiftAnomaly

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeSectorIntertwiner
open scoped VertexOperator

noncomputable section

private abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

private theorem ground_ne_zero (D : LatticeData) (a : Charge D) :
    ground D a ≠ 0 := by
  classical
  simp

/-- The cocycle product on the actual charge basis is a normalized vertex mode. -/
private theorem ground_mul (D : LatticeData) (a b : Charge D) :
    ((Y D (ground D a))[[-bilinear D a b - 1]]) (ground D b) =
      epsilon D a b • ground D (a + b) := by
  change ((Y D (inclusion D a 1))[[-bilinear D a b - 1]]) (inclusion D b 1) = _
  rw [← inclusion_canonical, canonical_ground_normalization, map_smul]
  rfl

/-- An odd-period multiplicative monomial lift commuting with a lift of
inversion has trivial phase on every fixed charge. The inversion phase is
an arbitrary unit. -/
theorem fixed_charge_phase_eq_one_of_odd_period
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (lift inversion : Carrier D ≃ₗ[ℂ] Carrier D)
    (phase inversionPhase : Charge D → ℂˣ)
    (hLift : ∀ a, lift (ground D a) = (phase a : ℂ) • ground D (g a))
    (hInversion : ∀ a, inversion (ground D a) = (inversionPhase a : ℂ) • ground D (-a))
    (hMode : ∀ (u v : Carrier D) (m : ℤ),
      lift (((Y D u)[[m]]) v) = ((Y D (lift u))[[m]]) (lift v))
    (hCommute : Commute lift inversion)
    (n : ℕ) (hOdd : Odd n) (hPeriod : lift ^ n = 1)
    (a : Charge D) (ha : g a = a) :
    phase a = 1 := by
  have hFixedAdd (b c : Charge D) (hb : g b = b) (hc : g c = c) :
      phase (b + c) = phase b * phase c := by
    have hbc : g (b + c) = b + c := by rw [map_add, hb, hc]
    have h := hMode (ground D b) (ground D c) (-bilinear D b c - 1)
    rw [ground_mul, map_smul, hLift, hbc, hLift b, hLift c, hb, hc, map_smul] at h
    simp only [VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply,
      map_smul, smul_smul] at h
    rw [← VertexOperator.ncoeff, ground_mul, smul_smul] at h
    have hEps : epsilon D b c ≠ 0 := by
      unfold epsilon paritySign
      split_ifs <;> simp
    apply Units.ext
    change (phase (b + c) : ℂ) = (phase b : ℂ) * (phase c : ℂ)
    apply mul_left_cancel₀ hEps
    exact (smul_left_injective ℂ (ground_ne_zero D (b + c)) h).trans (by ac_rfl)
  have hZero : phase 0 = 1 := by
    have h := hFixedAdd 0 0 (map_zero g) (map_zero g)
    rw [zero_add] at h
    exact mul_left_cancel (by simpa only [mul_one] using h.symm :
      phase 0 * phase 0 = phase 0 * 1)
  have hNegFixed : g (-a) = -a := by rw [map_neg, ha]
  have hInverse := hFixedAdd a (-a) ha hNegFixed
  rw [add_neg_cancel, hZero] at hInverse
  have hSame : phase (-a) = phase a := by
    have h := congrArg (fun T : Carrier D ≃ₗ[ℂ] Carrier D => T (ground D a)) hCommute.eq
    simp only [LinearEquiv.mul_apply, hInversion, hLift, map_smul, ha, hNegFixed,
      smul_smul] at h
    rw [mul_comm (phase a : ℂ)] at h
    apply Units.ext
    exact mul_left_cancel₀ (Units.ne_zero (inversionPhase a))
      (smul_left_injective ℂ (ground_ne_zero D (-a)) h)
  have hSquare : phase a ^ 2 = 1 := by
    simpa only [pow_two, hSame] using hInverse.symm
  have hPower (k : ℕ) : (lift ^ k) (ground D a) = ((phase a : ℂ) ^ k) • ground D a := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hLift, ha, smul_smul, pow_succ]
  have hScalarPeriod : phase a ^ n = 1 := by
    apply Units.ext
    have h := hPower n
    rw [hPeriod] at h
    exact smul_left_injective ℂ (ground_ne_zero D a) (by simpa using h.symm)
  apply orderOf_eq_one_iff.mp
  have hDvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hScalarPeriod)
    (orderOf_dvd_of_pow_eq_one hSquare)
  simpa [hOdd.coprime_two_right.gcd_eq_one] using hDvd

/-- For the P48q spectral data, every such order-three lift has type one.
The lowest-weight premise specializes the standard-lift formula to the two
nontrivial eigenspaces. Each has complex dimension `pairs`. The residue is
computed on an integer representing nine times the twisted lowest weight. -/
theorem p48q_order_three_type_one
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (lift inversion : Carrier D ≃ₗ[ℂ] Carrier D)
    (phase inversionPhase : Charge D → ℂˣ)
    (hLift : ∀ a, lift (ground D a) = (phase a : ℂ) • ground D (g a))
    (hInversion : ∀ a, inversion (ground D a) = (inversionPhase a : ℂ) • ground D (-a))
    (hMode : ∀ (u v : Carrier D) (m : ℤ),
      lift (((Y D u)[[m]]) v) = ((Y D (lift u))[[m]]) (lift v))
    (hCommute : Commute lift inversion) (hOrderThree : lift ^ 3 = 1)
    (fixedRank pairs : ℕ)
    (hNebeRank : D.rank = 48) (hNebeFixedRank : fixedRank = 16)
    (hOrderThreeRankDecomposition : fixedRank + 2 * pairs = D.rank)
    (rho : ℚ)
    (hStandardLiftLowestWeight :
      (∀ a, g a = a → phase a = 1) →
        rho = (1 * (3 - 1) * (pairs : ℚ) + 2 * (3 - 2) * (pairs : ℚ)) / (4 * 3 ^ 2)) :
    pairs = 16 ∧ rho = 16 / 9 ∧ (3 : ℚ) ^ 2 * rho = 16 ∧
      (∀ t : ℤ, (3 : ℚ) ^ 2 * rho = (t : ℚ) → (t : ZMod 3) = 1) := by
  have hPairs : pairs = 16 := by omega
  have hStandard := fixed_charge_phase_eq_one_of_odd_period D g lift inversion
    phase inversionPhase hLift hInversion hMode hCommute 3
    (show Odd (3 : ℕ) from ⟨1, rfl⟩) hOrderThree
  have hRho := hStandardLiftLowestWeight hStandard
  rw [hPairs] at hRho
  norm_num at hRho
  have hScaled : (3 : ℚ) ^ 2 * rho = 16 := by
    rw [hRho]
    norm_num
  refine ⟨hPairs, hRho, hScaled, ?_⟩
  intro t ht
  have ht16 : t = 16 := by exact_mod_cast ht.symm.trans hScaled
  subst t
  rfl

#print axioms fixed_charge_phase_eq_one_of_odd_period
#print axioms p48q_order_three_type_one

end
end D5.S3.VertexAlgebra.Lattice.P48qLiftAnomaly
