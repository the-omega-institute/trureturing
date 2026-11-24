/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal Leech sector traces and their genus-one modular transformations. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldModularCovariance

/-! The sector order is the fixed and anti-fixed lattice spaces followed by
the negative and positive oscillator-parity spaces of the twisted module.
The twisted grades use twice the oscillator energy as their index. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Function Matrix UpperHalfPlane
open scoped Matrix MatrixGroups

namespace D5.S3.VertexAlgebra.ActualLeechSectorCharacters

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (leechUnit leechPosDef)
open ActualLeechOrbifoldAllWeightDimension
open ActualLeechOrbifoldTraceSeries (ordinaryTrace ordinaryCharacter ordinary_trace_series)
open ActualLeechOrbifoldModularCovariance
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeInvolution (minusSpace)
open LatticePositiveEnergy (grade actualL0_eigenspace_eq_grade)
open LatticeThetaCharacter
open LatticeHalfFockGradedTrace
open LatticeHalfFockCharacter
open LatticeHalfFockParityT
open SourceBPZ.ThetaGradeTraceSplit (minusGrade plusGrade gradeSplitEquiv)

local notation "D" => leechData
local notation "H" => actualInverse D
local notation "hHG" => actualInverse_left D leechUnit
local notation "hGH" => actualInverse_right D leechUnit
local notation "q" => Periodic.qParam 1
local notation "Θ" => positiveFullThetaTrace D H hHG hGH leechPosDef
local notation "Z" => holonomyTrace

/-- The literal lattice Sugawara grade, restricted to theta parity. -/
def latticeSectorGrade (odd : Bool) (n : ℕ) : Submodule ℂ (Carrier D) :=
  if odd then UntwistedWeight n ⊓ minusSpace D else FixedWeight n

/-- The literal twisted stress grade, restricted to oscillator parity. -/
def twistedSectorGrade (odd : Bool) (n : ℕ) : Submodule ℂ (ActualTensor D leechUnit) :=
  actualGrade D leechUnit n ⊓ paritySpace D leechUnit (if odd then -1 else 1)

instance (odd : Bool) (n : ℕ) : FiniteDimensional ℂ (latticeSectorGrade odd n) := by
  cases odd
  · exact fixedWeight_finite n
  · exact Submodule.finiteDimensional_of_le
      (inf_le_left : UntwistedWeight n ⊓ minusSpace D ≤ UntwistedWeight n)

instance (odd : Bool) (n : ℕ) : FiniteDimensional ℂ (twistedSectorGrade odd n) := by
  let := actualGrade_module_finite D leechUnit n
  exact Submodule.finiteDimensional_of_le inf_le_left

private def latticeTerm (odd : Bool) (τ : ℍ) (n : ℕ) : ℂ :=
  (q τ)⁻¹ * (LinearMap.trace ℂ (latticeSectorGrade odd n) LinearMap.id * q τ ^ n)

private def twistedTerm (odd : Bool) (τ : ℍ) (n : ℕ) : ℂ :=
  exp (Real.pi * Complex.I * (τ : ℂ)) *
    (LinearMap.trace ℂ (twistedSectorGrade odd n) LinearMap.id *
      exp (Real.pi * Complex.I * (τ : ℂ)) ^ n)

/-- The finite-grade traces include the vacuum shift (c/24=1).
The twisted weight at index (n) is (3/2+n/2). -/
def sectorTerm (i : Fin 4) (τ : ℍ) : ℕ → ℂ :=
  ![latticeTerm false τ, latticeTerm true τ, twistedTerm true τ, twistedTerm false τ] i

/-- The ordered characters of (V_L^+, V_L^-, M^-, M^+). -/
def sectorCharacter (τ : ℍ) (i : Fin 4) : ℂ := ∑' n : ℕ, sectorTerm i τ n

private theorem lattice_grade_trace (odd : Bool) (n : ℕ) :
    LinearMap.trace ℂ (latticeSectorGrade odd n) LinearMap.id =
      (ordinaryTrace n + (if odd then -1 else 1) * Θ n) / 2 := by
  have hp := fixed_weight_finrank_eq_trace (n : ℤ)
  have hgrade : UntwistedWeight (n : ℤ) = grade D (n : ℤ) :=
    actualL0_eigenspace_eq_grade D H hHG hGH n
  have hplus : FixedWeight (n : ℤ) = plusGrade D (n : ℤ) := by
    rw [show FixedWeight (n : ℤ) = LatticeInvolution.fixedSpace D ⊓
      UntwistedWeight (n : ℤ) from rfl, hgrade]
    exact inf_comm (LatticeInvolution.fixedSpace D) (grade D (n : ℤ))
  let : FiniteDimensional ℂ (grade D (n : ℤ)) := by
    rw [← hgrade]
    infer_instance
  let : FiniteDimensional ℂ (plusGrade D (n : ℤ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let : FiniteDimensional ℂ (minusGrade D (n : ℤ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hsplit := (gradeSplitEquiv D (n : ℤ)).finrank_eq
  rw [Module.finrank_prod, ← hplus, ← hgrade] at hsplit
  have hs : (Module.finrank ℂ (UntwistedWeight (n : ℤ)) : ℂ) =
      (Module.finrank ℂ (FixedWeight (n : ℤ)) : ℂ) +
      (Module.finrank ℂ (minusGrade D (n : ℤ)) : ℂ) := by
    exact_mod_cast hsplit
  cases odd
  · change LinearMap.trace ℂ (FixedWeight (n : ℤ)) LinearMap.id = _
    simpa [LinearMap.trace_id, ordinaryTrace] using hp
  · change LinearMap.trace ℂ (UntwistedWeight (n : ℤ) ⊓ minusSpace D :
        Submodule ℂ (Carrier D)) LinearMap.id = _
    rw [LinearMap.trace_id, ordinaryTrace, LinearMap.trace_id]
    rw [show UntwistedWeight (n : ℤ) ⊓ minusSpace D = minusGrade D (n : ℤ) from
      congrArg (fun g : Submodule ℂ (Carrier D) => g ⊓ minusSpace D) hgrade]
    simp only [ite_true]
    linear_combination -hs - hp

private theorem lattice_sector_hasSum (odd : Bool) (τ : ℍ) :
    HasSum (latticeTerm odd τ)
      ((Z (0, 0) τ + (if odd then -1 else 1) * Z (0, 1) τ) / 2) := by
  have ha := (ordinary_trace_series τ).1.of_norm.hasSum.mul_left (q τ)⁻¹
  have hb := (positive_full_theta_character D H hHG hGH leechPosDef
    (Periodic.norm_qParam_lt_one one_pos τ.im_pos)).2.1.of_norm.hasSum.mul_left (q τ)⁻¹
  have hq : q τ = exp (2 * Real.pi * Complex.I * (τ : ℂ)) := by simp [Periodic.qParam]
  have hv : exp (-2 * Real.pi * Complex.I * (τ : ℂ) * leechData.rank / 24) = (q τ)⁻¹ := by
    rw [leech_spec.1, hq, ← exp_neg]
    congr 1
    push_cast
    ring
  rw [holonomyTrace_zero_zero, holonomyTrace_zero_one, positiveFullThetaCharacter, hv, ← hq]
  refine ((ha.add (hb.mul_left (if odd then -1 else 1))).div_const 2).congr_fun ?_
  intro n
  dsimp [latticeTerm]
  rw [lattice_grade_trace]
  ring

private theorem twisted_grade_trace (odd : Bool) (n : ℕ) :
    2 * LinearMap.trace ℂ (twistedSectorGrade odd n) LinearMap.id =
      (1 + (if odd then -1 else 1) * (-1 : ℂ) ^ n) *
        LinearMap.trace ℂ (actualGrade D leechUnit n) LinearMap.id := by
  let a : ℂ := if odd then -1 else 1
  let p : ℂ := (-1) ^ n
  have hpar (v : ActualTensor D leechUnit) (hv : v ∈ actualGrade D leechUnit n) :
      actualParity D leechUnit v = p • v :=
    actualParity_on_actualGrade D leechUnit n ⟨v, hv⟩
  have ha : a = 1 ∨ a = -1 := by cases odd <;> simp [a]
  have hp : p = 1 ∨ p = -1 := by
    rw [show p = (-1 : ℂ) ^ (n % 2) from neg_one_pow_eq_pow_mod_two _]
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;> simp [h]
  change 2 * _ = (1 + a * p) * _
  by_cases h : a = p
  · have hg : twistedSectorGrade odd n = actualGrade D leechUnit n := by
      apply inf_eq_left.mpr
      intro v hv
      simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, ← h] using hpar v hv
    have hap : a * p = 1 := by
      rw [← h]
      rcases ha with ha | ha <;> rw [ha] <;> norm_num
    rw [hg, hap]
    ring
  · have hg : twistedSectorGrade odd n = ⊥ := by
      apply le_antisymm _ bot_le
      intro v hv
      have hv' : v ∈ actualGrade D leechUnit n ∧ v ∈ paritySpace D leechUnit a := hv
      have hs : actualParity D leechUnit v = a • v := by
        simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, sub_eq_zero] using hv'.2
      have hz : (a - p) • v = 0 := by rw [sub_smul, ← hs, ← hpar v hv'.1, sub_self]
      exact (Submodule.mem_bot ℂ).mpr ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h))
    have hap : a * p = -1 := by
      rcases ha with ha | ha <;> rcases hp with hp | hp
      · exact (h (ha.trans hp.symm)).elim
      · norm_num [ha, hp]
      · norm_num [ha, hp]
      · exact (h (ha.trans hp.symm)).elim
    simp [hg, hap, LinearMap.trace_id]

private theorem twisted_sector_hasSum (odd : Bool) (τ : ℍ) :
    HasSum (twistedTerm odd τ)
      ((Z (1, 0) τ + (if odd then 1 else -1) * Z (1, 1) τ) / 2) := by
  let t := exp (Real.pi * Complex.I * (τ : ℂ))
  let v := exp (2 * Real.pi * Complex.I * (τ : ℂ) * leechData.rank / 48)
  have hv : v = t := by
    dsimp [v, t]
    rw [leech_spec.1]
    congr 1
    push_cast
    ring
  have hu := actual_character_modular D leechUnit LinearMap.id τ τ.im_pos
  have ha : HasSum (fun n => v * actualTraceTerm D leechUnit LinearMap.id t n)
      (actualInsertedCharacter D leechUnit LinearMap.id τ) := hu.2.2.1.symm ▸ hu.2.1
  have hb := (actual_parity_character_series D leechUnit LinearMap.id τ τ.im_pos).2
  rw [holonomyTrace_one_zero, holonomyTrace_one_one]
  have hsign : (if odd then 1 else -1 : ℂ) * (-1) = (if odd then -1 else 1) := by
    cases odd <;> norm_num
  rw [mul_neg, ← neg_mul, ← mul_neg_one (if odd then (1 : ℂ) else -1), hsign]
  refine ((ha.add (hb.mul_left (if odd then -1 else 1))).div_const 2).congr_fun ?_
  intro n
  have hid : actualGroundInsertRestrict D leechUnit n LinearMap.id = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [actualGroundInsertRestrict_coe, actualGroundInsert, TensorProduct.map_id]
    rfl
  change t * (_ * t ^ n) = (v * actualTraceTerm D leechUnit LinearMap.id t n +
      (if odd then -1 else 1) * (v * actualParityTraceTerm D leechUnit LinearMap.id t n)) / 2
  rw [actualTraceTerm, actualParityTraceTerm, actualParityTraceTerm_eq, hid, hv]
  linear_combination (t * t ^ n / 2) * twisted_grade_trace odd n

/-- Each holonomy combination is an absolutely convergent sum of the identity
traces of its literal parity-projected grades. The physical insertion in the
doubly twisted holonomy is minus oscillator parity. -/
theorem sector_trace_series (i : Fin 4) (τ : ℍ) :
    Summable (fun n => ‖sectorTerm i τ n‖) ∧
    HasSum (sectorTerm i τ)
      (![ (Z (0, 0) τ + Z (0, 1) τ) / 2, (Z (0, 0) τ - Z (0, 1) τ) / 2,
          (Z (1, 0) τ + Z (1, 1) τ) / 2, (Z (1, 0) τ - Z (1, 1) τ) / 2 ] i) := by
  suffices h : HasSum (sectorTerm i τ) _ from ⟨summable_norm_iff.mpr h.summable, h⟩
  fin_cases i
  · simpa [sectorTerm] using lattice_sector_hasSum false τ
  · simpa [sectorTerm, sub_eq_add_neg] using lattice_sector_hasSum true τ
  · simpa [sectorTerm] using twisted_sector_hasSum true τ
  · simpa [sectorTerm, sub_eq_add_neg] using twisted_sector_hasSum false τ

private theorem sectorCharacter_eq (τ : ℍ) (i : Fin 4) :
    sectorCharacter τ i =
      (![ (Z (0, 0) τ + Z (0, 1) τ) / 2, (Z (0, 0) τ - Z (0, 1) τ) / 2,
          (Z (1, 0) τ + Z (1, 1) τ) / 2, (Z (1, 0) τ - Z (1, 1) τ) / 2 ] i) :=
  (sector_trace_series i τ).2.tsum_eq

/-- The modular S matrix in the literal sector order. -/
def sectorS : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1,  1,  1,  1;
                   1,  1, -1, -1;
                   1, -1,  1, -1;
                   1, -1, -1,  1]

/-- The modular T matrix including the central-charge shift. -/
def sectorT : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, 1, 1, -1]

/-- Native S swaps the spatial and temporal holonomies. -/
theorem sectorCharacter_S (τ : ℍ) :
    sectorCharacter (ModularGroup.S • τ) = sectorS *ᵥ sectorCharacter τ := by
  funext i
  simp only [sectorCharacter_eq, holonomyTrace_S]
  fin_cases i <;>
    simp [sectorS, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sectorCharacter_eq] <;> ring

/-- Native T exchanges the two twisted holonomy traces. -/
theorem sectorCharacter_T (τ : ℍ) :
    sectorCharacter (ModularGroup.T • τ) = sectorT *ᵥ sectorCharacter τ := by
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  funext i
  simp only [sectorCharacter_eq, holonomyTrace_T, zero_add, add_zero, hone]
  rw [sectorT, Matrix.mulVec_diagonal]
  fin_cases i <;> simp [sectorCharacter_eq] <;> ring

end D5.S3.VertexAlgebra.ActualLeechSectorCharacters

#print axioms D5.S3.VertexAlgebra.ActualLeechSectorCharacters.sector_trace_series
#print axioms D5.S3.VertexAlgebra.ActualLeechSectorCharacters.sectorCharacter_S
#print axioms D5.S3.VertexAlgebra.ActualLeechSectorCharacters.sectorCharacter_T
