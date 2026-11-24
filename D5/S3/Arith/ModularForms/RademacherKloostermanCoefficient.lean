/- GID: D5/S3/Arith/ModularForms/RademacherKloostermanCoefficient
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite Rademacher Fourier coefficients as standard Kloosterman sums. -/

import D5.S3.Arith.ModularForms.RademacherPhaseRamanujan
import D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase

open scoped BigOperators UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherKloostermanCoefficient

open D5.S3.Arith.ModularForms.RademacherLinearCutoff
  (linearWeight reducedResidues shiftedArgument)
open D5.S3.Arith.ModularForms.RademacherPhaseRamanujan
  (linearPhase_eq_vacuumPhase negatedInverseResidue residuePhase sum_vacuumPhase_one
    vacuumPhase_eq_residuePhase_negatedInverse)
open D5.S3.Arith.ModularForms.RademacherVacuum
  (inverseResidue inverseResidue_spec vacuumPhase)
open D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase (kloosterman phase)

set_option autoImplicit false

noncomputable section

private def reducedResiduesEquivCoprime (c : ℕ) [NeZero c] :
    ↥(reducedResidues (c : ℤ)) ≃ {x : ZMod c // x.val.Coprime c} where
  toFun d := ⟨(d.1 : ZMod c), by
    rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast, ZMod.val_intCast, Int.gcd_emod]
    exact (Finset.mem_filter.mp d.2).2⟩
  invFun x := ⟨(x.1.val : ℤ), by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, ?_⟩, ?_⟩
    · exact_mod_cast (ZMod.val_lt x.1)
    · simpa only [Int.gcd_natCast_natCast] using (Nat.coprime_iff_gcd_eq_one.mp x.2)⟩
  left_inv d := by
    apply Subtype.ext
    obtain ⟨hd₀, hdc⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp d.2).1
    change ((d.1 : ZMod c).val : ℤ) = d.1
    exact (ZMod.val_intCast d.1).trans (Int.emod_eq_of_lt hd₀ hdc)
  right_inv x := by
    apply Subtype.ext
    change ((x.1.val : ℤ) : ZMod c) = x.1
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Send each reduced residue to the unit represented by that residue. -/
def reducedResiduesEquivUnits (c : ℕ) [NeZero c] :
    ↥(reducedResidues (c : ℤ)) ≃ (ZMod c)ˣ :=
  (reducedResiduesEquivCoprime c).trans (ZMod.unitsEquivCoprime (n := c)).symm

theorem coe_reducedResiduesEquivUnits (c : ℕ) [NeZero c]
    (d : ↥(reducedResidues (c : ℤ))) :
    (reducedResiduesEquivUnits c d : ZMod c) = (d.1 : ZMod c) := by
  let r := reducedResiduesEquivCoprime c d
  change (ZMod.unitOfCoprime r.val.val r.property : ZMod c) = (d.1 : ZMod c)
  exact (ZMod.coe_unitOfCoprime _ _).trans (ZMod.natCast_zmod_val r.val)

/-- The chosen least nonnegative representative of the negative inverse has the expected cast. -/
theorem intCast_negatedInverseResidue {c : ℕ} [NeZero c] {d : ℤ}
    (hd : d ∈ reducedResidues (c : ℤ)) :
    (negatedInverseResidue (c : ℤ) d : ZMod c) = -((d : ZMod c)⁻¹) := by
  have hc : 0 < (c : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne c))
  have hg : (c : ℤ).gcd d = 1 := (Int.gcd_comm _ _).trans (Finset.mem_filter.mp hd).2
  have hinv : (d : ZMod c) * (inverseResidue (c : ℤ) d : ZMod c) = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (d * inverseResidue (c : ℤ) d) 1 c).2
      (inverseResidue_spec hc hg).2.2
    simpa only [Int.cast_mul, Int.cast_one] using h
  rw [negatedInverseResidue, ZMod.intCast_mod, Int.cast_neg,
    ZMod.inv_eq_of_mul_eq_one c _ _ hinv]

private theorem residuePhase_eq_stdAddChar (c : ℕ) [NeZero c] (a : ℤ) :
    residuePhase (c : ℤ) a = ZMod.stdAddChar (a : ZMod c) := by
  simp only [ZMod.stdAddChar_coe, residuePhase, Int.cast_natCast, div_eq_mul_inv, mul_assoc]

/-- The Fourier factor uses the original denominator residue as its argument. -/
theorem vacuumPhase_mul_residuePhase_eq_phase (c : ℕ) [NeZero c] (n : ℤ) {d : ℤ}
    (hd : d ∈ reducedResidues (c : ℤ)) :
    vacuumPhase (c : ℤ) d * residuePhase (c : ℤ) (n * d) =
      phase (n : ZMod c) (-1) (d : ZMod c) := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
  rw [vacuumPhase_eq_residuePhase_negatedInverse hc, phase]
  simp only [residuePhase_eq_stdAddChar, ← AddChar.map_add_eq_mul, Int.cast_mul,
    intCast_negatedInverseResidue hd, neg_one_mul, add_comm]

/-- The actual finite residue sum gives the unnormalized Kloosterman sum at `(n, -1)`. -/
theorem sum_vacuumPhase_mul_residuePhase_eq_kloosterman (c : ℕ) [NeZero c] (n : ℤ) :
    (∑ d ∈ reducedResidues (c : ℤ), vacuumPhase (c : ℤ) d * residuePhase (c : ℤ) (n * d)) =
      kloosterman (n : ZMod c) (-1) := by
  rw [← Finset.sum_coe_sort (reducedResidues (c : ℤ)), kloosterman]
  refine Fintype.sum_equiv (reducedResiduesEquivUnits c) _ _ fun d => ?_
  rw [coe_reducedResiduesEquivUnits, Units.coe_neg_one]
  exact vacuumPhase_mul_residuePhase_eq_phase c n d.2

private theorem reducedResidues_one : reducedResidues (1 : ℤ) = {0} := by
  ext d
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd₀, hd₁⟩, _⟩
    omega
  · rintro rfl
    decide

/-- Modulus one contributes a single term, from the residue zero. -/
theorem sum_vacuumPhase_mul_residuePhase_one (n : ℤ) :
    (∑ d ∈ reducedResidues (1 : ℤ), vacuumPhase 1 d * residuePhase 1 (n * d)) = 1 := by
  have hv : vacuumPhase 1 0 = 1 := by
    simpa only [reducedResidues_one, Finset.sum_singleton] using sum_vacuumPhase_one
  simp [reducedResidues_one, hv, residuePhase]

private theorem exp_shiftedArgument_pow (τ : ℂ) (c : ℕ) (d : ℤ) (m : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument τ (c : ℤ) d) ^ m =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m *
        residuePhase (c : ℤ) ((m : ℤ) * d) := by
  unfold shiftedArgument residuePhase
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [Int.cast_mul, Int.cast_natCast, div_eq_mul_inv]
  ring

private theorem sum_linearWeight_qPower {c : ℕ} [NeZero c] (m : ℕ) (τ : ℂ) :
    (∑ d ∈ reducedResidues (c : ℤ), linearWeight (c : ℤ) d *
      ((-2 * (Real.pi : ℂ) * Complex.I) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument τ (c : ℤ) d) ^ m)) =
      (4 * (Real.pi : ℂ) ^ 2 / (c : ℂ) ^ 2) * kloosterman ((m : ℤ) : ZMod c) (-1) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m := by
  rw [← sum_vacuumPhase_mul_residuePhase_eq_kloosterman c (m : ℤ),
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hc : 0 < (c : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne c))
  rw [linearWeight, linearPhase_eq_vacuumPhase hc (Finset.mem_filter.mp hd).2,
    exp_shiftedArgument_pow]
  calc
    _ = -(Complex.I * Complex.I) *
        ((4 * (Real.pi : ℂ) ^ 2 / (c : ℂ) ^ 2) *
          (vacuumPhase (c : ℤ) d * residuePhase (c : ℤ) ((m : ℤ) * d)) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ m) := by
      simp only [Int.cast_natCast, div_eq_mul_inv]
      ring
    _ = _ := by rw [Complex.I_mul_I, neg_neg, one_mul]

/-- Fixing the positive power in `linearPrincipalValueQTail` gives a finite
outer coefficient weighted by `4π²/c²`. -/
theorem sum_linearQTail_power_eq_kloosterman (N n : ℕ) (τ : ℍ) :
    (∑ c ∈ (Finset.range N).erase 0, ∑ d ∈ reducedResidues (c : ℤ),
      linearWeight (c : ℤ) d * ((-2 * (Real.pi : ℂ) * Complex.I) *
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * shiftedArgument (τ : ℂ) (c : ℤ) d) ^ (n + 1))) =
      (∑ c : ↥((Finset.range N).erase 0),
        (4 * (Real.pi : ℂ) ^ 2 / (c.1 : ℂ) ^ 2) *
          @kloosterman c.1 ⟨(Finset.mem_erase.mp c.2).1⟩ (((n + 1 : ℕ) : ℤ) : ZMod c.1) (-1)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (n + 1) := by
  rw [← Finset.sum_coe_sort ((Finset.range N).erase 0), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  let : NeZero c.1 := ⟨(Finset.mem_erase.mp c.2).1⟩
  exact sum_linearWeight_qPower (c := c.1) (n + 1) (τ : ℂ)

end

end D5.S3.Arith.ModularForms.RademacherKloostermanCoefficient
