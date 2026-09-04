/- GID: D5/S1/Solenoid/ComplexPowerSolenoidDecomposition
   generality: I
   mirror-B: D5/B/S1/Solenoid/ComplexPowerSolenoidDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible nonzero complex power threads split into a conserved real charge
     and a universal-solenoid phase. -/

/- Library-search audit trail (2026-09-05):
   * Repository keyword and symbol searches found the additive `UniversalSolenoid`, its
     compactness, exact sequence, and streamline decomposition, but no compatible nonzero
     complex power tower or conserved logarithmic norm charge.
   * The retired formalization-receipt tree was not consulted. Digestion CAS/backfill searches
     found only residual source atoms, not a Lean owner of this theorem. In-flight module and
     branch-log searches found no complex-power-solenoid implementation.
   * The generalized repository search covered inverse limits, complex norm/log identities,
     unit-modulus phases, and solenoid decompositions under names not containing "complexified".
   * Pinned Mathlib supplies `Complex.norm_pow`, `Real.log_pow`, `Real.exp_nat_mul`,
     `AddCircle.homeomorphCircle`, and `AddCircle.toCircle_nsmul`. It has no packaged theorem
     splitting a compatible complex power thread, so the normalization and inverse maps are
     constructed here.
-/

import D5.S1.Dynamics.UniversalSolenoid
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S1.Solenoid.ComplexPowerSolenoidDecomposition

open D5.S1.Dynamics

private def oneIndex : ℕ+ := ⟨1, Nat.zero_lt_one⟩

private def productIndex (m n : ℕ+) : ℕ+ :=
  ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩

/-- A nonzero complex coordinate at every positive level, compatible with all power maps. -/
structure ComplexPowerThread where
  coord : ℕ+ → ℂ
  coord_ne_zero : ∀ m, coord m ≠ 0
  pow_compatible : ∀ m n, coord (productIndex m n) ^ n.1 = coord m

@[ext]
theorem ComplexPowerThread.ext {z w : ComplexPowerThread} (h : z.coord = w.coord) : z = w := by
  cases z
  cases w
  cases h
  rfl

/-- The level-one logarithmic norm is the Archimedean charge of the thread. -/
noncomputable def logarithmicCharge (z : ComplexPowerThread) : ℝ :=
  Real.log ‖z.coord oneIndex‖

/-- The radial complex factor with charge `q` at level `m`. -/
noncomputable def radialFactor (q : ℝ) (m : ℕ+) : ℂ :=
  (Real.exp (q / m.1) : ℂ)

private theorem radialFactor_ne_zero (q : ℝ) (m : ℕ+) : radialFactor q m ≠ 0 := by
  simp [radialFactor]

private theorem radialFactor_norm (q : ℝ) (m : ℕ+) :
    ‖radialFactor q m‖ = Real.exp (q / m.1) := by
  rw [radialFactor, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private theorem radialFactor_pow (q : ℝ) (m n : ℕ+) :
    radialFactor q (productIndex m n) ^ n.1 = radialFactor q m := by
  rw [radialFactor, radialFactor]
  norm_cast
  change Real.exp (q / ((m.1 * n.1 : ℕ) : ℝ)) ^ n.1 = Real.exp (q / m.1)
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp [Nat.ne_of_gt m.2, Nat.ne_of_gt n.2]

/-- The source formula `m * log ‖z_m‖` is independent of the positive level `m`. -/
theorem logarithmic_charge_conservation (z : ComplexPowerThread) (m : ℕ+) :
    (m.1 : ℝ) * Real.log ‖z.coord m‖ = logarithmicCharge z := by
  have hIndex : productIndex oneIndex m = m := by
    apply Subtype.ext
    exact Nat.one_mul m.1
  have hPower := z.pow_compatible oneIndex m
  rw [hIndex] at hPower
  calc
    (m.1 : ℝ) * Real.log ‖z.coord m‖ = Real.log (‖z.coord m‖ ^ m.1) := by
      rw [Real.log_pow]
    _ = Real.log ‖z.coord m ^ m.1‖ := by rw [norm_pow]
    _ = Real.log ‖z.coord oneIndex‖ := congrArg (fun w : ℂ => Real.log ‖w‖) hPower
    _ = logarithmicCharge z := rfl

/-- Divide a nonzero complex coordinate by its positive norm to obtain its circle phase. -/
noncomputable def normalizedPhase (z : ComplexPowerThread) (m : ℕ+) : Circle :=
  ⟨z.coord m / (‖z.coord m‖ : ℂ), by
    simp [Submonoid.unitSphere, Complex.norm_real,
      norm_ne_zero_iff.mpr (z.coord_ne_zero m)]⟩

private theorem normalizedPhase_pow (z : ComplexPowerThread) (m n : ℕ+) :
    normalizedPhase z (productIndex m n) ^ n.1 = normalizedPhase z m := by
  apply Subtype.ext
  change (z.coord (productIndex m n) / (‖z.coord (productIndex m n)‖ : ℂ)) ^ n.1 =
    z.coord m / (‖z.coord m‖ : ℂ)
  rw [div_pow, z.pow_compatible]
  have hNorm := congrArg norm (z.pow_compatible m n)
  simp only [norm_pow] at hNorm
  congr 1
  exact_mod_cast hNorm

private theorem toCircle_homeomorphCircle_symm (u : Circle) :
    AddCircle.toCircle ((AddCircle.homeomorphCircle one_ne_zero).symm u) = u := by
  rw [← AddCircle.homeomorphCircle_apply (T := (1 : ℝ)) one_ne_zero]
  exact Homeomorph.apply_symm_apply _ _

/-- The normalized phases form the existing universal additive solenoid. -/
noncomputable def phaseSolenoid (z : ComplexPowerThread) : UniversalSolenoid :=
  ⟨fun m => (AddCircle.homeomorphCircle one_ne_zero).symm (normalizedPhase z m), by
    intro m n
    apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
    rw [AddCircle.toCircle_nsmul, toCircle_homeomorphCircle_symm,
      toCircle_homeomorphCircle_symm]
    exact normalizedPhase_pow z m n⟩

private theorem toCircle_phaseSolenoid (z : ComplexPowerThread) (m : ℕ+) :
    AddCircle.toCircle ((phaseSolenoid z).1 m) = normalizedPhase z m := by
  exact toCircle_homeomorphCircle_symm _

/-- Reassemble a compatible complex thread from one real charge and one solenoid phase. -/
noncomputable def assemble (data : ℝ × UniversalSolenoid) : ComplexPowerThread where
  coord m := radialFactor data.1 m * (AddCircle.toCircle (data.2.1 m) : ℂ)
  coord_ne_zero m := mul_ne_zero (radialFactor_ne_zero data.1 m)
    (AddCircle.toCircle (data.2.1 m)).coe_ne_zero
  pow_compatible m n := by
    rw [mul_pow, radialFactor_pow]
    congr 1
    have hPhase := congrArg AddCircle.toCircle (data.2.2 m n)
    rw [AddCircle.toCircle_nsmul] at hPhase
    exact congrArg Subtype.val hPhase

private theorem logarithmicCharge_assemble (q : ℝ) (theta : UniversalSolenoid) :
    logarithmicCharge (assemble (q, theta)) = q := by
  change Real.log ‖radialFactor q oneIndex *
    (AddCircle.toCircle (theta.1 oneIndex) : ℂ)‖ = q
  rw [norm_mul, radialFactor_norm, Circle.norm_coe, mul_one]
  rw [Real.log_exp]
  have hOneNat : oneIndex.1 = 1 := by rfl
  have hOne : (oneIndex.1 : ℝ) = 1 := by exact_mod_cast hOneNat
  rw [hOne, div_one]

private theorem normalizedPhase_assemble (q : ℝ) (theta : UniversalSolenoid) (m : ℕ+) :
    normalizedPhase (assemble (q, theta)) m = AddCircle.toCircle (theta.1 m) := by
  apply Subtype.ext
  change (radialFactor q m * (AddCircle.toCircle (theta.1 m) : ℂ)) /
    (‖radialFactor q m * (AddCircle.toCircle (theta.1 m) : ℂ)‖ : ℂ) =
      (AddCircle.toCircle (theta.1 m) : ℂ)
  rw [norm_mul, radialFactor_norm]
  simp only [Circle.norm_coe, mul_one]
  change (Real.exp (q / m.1) : ℂ) * (AddCircle.toCircle (theta.1 m) : ℂ) /
    (Real.exp (q / m.1) : ℂ) = (AddCircle.toCircle (theta.1 m) : ℂ)
  exact mul_div_cancel_left₀ _ (by simp)

private theorem phaseSolenoid_assemble (q : ℝ) (theta : UniversalSolenoid) :
    phaseSolenoid (assemble (q, theta)) = theta := by
  apply Subtype.ext
  funext m
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  rw [toCircle_phaseSolenoid, normalizedPhase_assemble]

private theorem radialFactor_logarithmicCharge (z : ComplexPowerThread) (m : ℕ+) :
    radialFactor (logarithmicCharge z) m = (‖z.coord m‖ : ℂ) := by
  rw [radialFactor]
  norm_cast
  have hm : (m.1 : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt m.2
  have hDivision : logarithmicCharge z / m.1 = Real.log ‖z.coord m‖ := by
    apply (div_eq_iff hm).2
    simpa [mul_comm] using (logarithmic_charge_conservation z m).symm
  rw [hDivision, Real.exp_log (norm_pos_iff.mpr (z.coord_ne_zero m))]

private theorem assemble_charge_phase (z : ComplexPowerThread) :
    assemble (logarithmicCharge z, phaseSolenoid z) = z := by
  apply ComplexPowerThread.ext
  funext m
  change radialFactor (logarithmicCharge z) m *
    (AddCircle.toCircle ((phaseSolenoid z).1 m) : ℂ) = z.coord m
  rw [radialFactor_logarithmicCharge, toCircle_phaseSolenoid]
  change (‖z.coord m‖ : ℂ) * (z.coord m / (‖z.coord m‖ : ℂ)) = z.coord m
  field_simp [norm_ne_zero_iff.mpr (z.coord_ne_zero m)]

/-- Polar decomposition commutes with every bonding power: compatible nonzero complex threads
are exactly a real Archimedean charge together with a universal-solenoid phase thread. -/
noncomputable def complexPowerThreadEquiv :
    ComplexPowerThread ≃ ℝ × UniversalSolenoid where
  toFun z := (logarithmicCharge z, phaseSolenoid z)
  invFun := assemble
  left_inv := assemble_charge_phase
  right_inv data := by
    rcases data with ⟨q, theta⟩
    apply Prod.ext
    · exact logarithmicCharge_assemble q theta
    · exact phaseSolenoid_assemble q theta

/-- Every real value occurs as the conserved charge of an explicit compatible thread. -/
theorem logarithmicCharge_surjective : Function.Surjective logarithmicCharge := by
  intro q
  exact ⟨assemble (q, 0), logarithmicCharge_assemble q 0⟩

/-- Zero charge is exactly the unit-modulus locus; positivity of every coordinate norm excludes
the totalized-logarithm zero branch. -/
theorem logarithmicCharge_eq_zero_iff (z : ComplexPowerThread) :
    logarithmicCharge z = 0 ↔ ∀ m, ‖z.coord m‖ = 1 := by
  constructor
  · intro hCharge m
    have hConservation := logarithmic_charge_conservation z m
    rw [hCharge] at hConservation
    have hLog : Real.log ‖z.coord m‖ = 0 := by
      have hm : (0 : ℝ) < m.1 := by exact_mod_cast m.2
      nlinarith
    exact Real.eq_one_of_pos_of_log_eq_zero
      (norm_pos_iff.mpr (z.coord_ne_zero m)) hLog
  · intro hUnit
    simp [logarithmicCharge, hUnit oneIndex]

end D5.S1.Solenoid.ComplexPowerSolenoidDecomposition
