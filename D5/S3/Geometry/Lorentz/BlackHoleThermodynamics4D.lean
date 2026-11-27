/- GID: D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/BlackHoleThermodynamics4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kerr-Newman horizon mechanics, exact mass derivatives, rotational extraction and Schwarzschild heat capacity. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Kerr-Newman thermodynamics in geometric units, with explicit constants in the
Schwarzschild temperature and entropy formulas. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D

def spin (M J : ℝ) : ℝ := J / M
def horizonGap (M J Q : ℝ) : ℝ := Real.sqrt (M ^ 2 - Q ^ 2 - spin M J ^ 2)
def rPlus (M J Q : ℝ) : ℝ := M + horizonGap M J Q
def rMinus (M J Q : ℝ) : ℝ := M - horizonGap M J Q
def horizonFactor (M J Q : ℝ) : ℝ := rPlus M J Q ^ 2 + spin M J ^ 2
def horizonArea (M J Q : ℝ) : ℝ := 4 * Real.pi * horizonFactor M J Q
def surfaceGravity (M J Q : ℝ) : ℝ :=
  (rPlus M J Q - rMinus M J Q) / (2 * horizonFactor M J Q)
def angularVelocity (M J Q : ℝ) : ℝ := spin M J / horizonFactor M J Q
def electricPotential (M J Q : ℝ) : ℝ := Q * rPlus M J Q / horizonFactor M J Q
def irreducibleMass (M J Q : ℝ) : ℝ := Real.sqrt (horizonArea M J Q / (16 * Real.pi))

private theorem spin_mul {M J : ℝ} (hM : 0 < M) : spin M J * M = J := by
  simp [spin, hM.ne']

private theorem gap_sq {M J Q : ℝ} (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    horizonGap M J Q ^ 2 = M ^ 2 - Q ^ 2 - spin M J ^ 2 :=
  Real.sq_sqrt (by linarith)

private theorem rPlus_pos {M J Q : ℝ} (hM : 0 < M) : 0 < rPlus M J Q :=
  add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)

private theorem factor_pos {M J Q : ℝ} (hM : 0 < M) : 0 < horizonFactor M J Q := by
  unfold horizonFactor
  have hr := rPlus_pos (J := J) (Q := Q) hM
  positivity

theorem horizonArea_pos {M J Q : ℝ} (hM : 0 < M) : 0 < horizonArea M J Q := by
  unfold horizonArea
  have hr := factor_pos (J := J) (Q := Q) hM
  positivity

private theorem surfaceGravity_eq (M J Q : ℝ) :
    surfaceGravity M J Q = horizonGap M J Q / horizonFactor M J Q := by
  unfold surfaceGravity rPlus rMinus
  ring

theorem surfaceGravity_pos_of_subextremal {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 < M ^ 2) : 0 < surfaceGravity M J Q := by
  rw [surfaceGravity_eq]
  exact div_pos (Real.sqrt_pos.2 (by linarith [h])) (factor_pos hM)

theorem surfaceGravity_zero_of_extremal {M J Q : ℝ}
    (h : Q ^ 2 + spin M J ^ 2 = M ^ 2) : surfaceGravity M J Q = 0 := by
  rw [surfaceGravity_eq, horizonGap, show M ^ 2 - Q ^ 2 - spin M J ^ 2 = 0 by linarith]
  simp

theorem rPlus_sq_add_a_sq_eq {M J Q : ℝ} (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    rPlus M J Q ^ 2 + spin M J ^ 2 = 2 * M * rPlus M J Q - Q ^ 2 := by
  unfold rPlus
  nlinarith only [gap_sq h]

/-- The squared mass as a rational function of the thermodynamic coordinates. -/
def kerrNewmanMassSq (A J Q : ℝ) : ℝ :=
  A / (16 * Real.pi) + Q ^ 2 / 2 + Real.pi * (Q ^ 4 + 4 * J ^ 2) / A

def kerrNewmanMass (A J Q : ℝ) : ℝ := Real.sqrt (kerrNewmanMassSq A J Q)

theorem kerrNewmanMassSq_irreducible {A J Q : ℝ} (hA : 0 < A) :
    kerrNewmanMassSq A J Q =
      (Real.sqrt (A / (16 * Real.pi)) + Q ^ 2 / (4 * Real.sqrt (A / (16 * Real.pi)))) ^ 2
        + J ^ 2 / (4 * (A / (16 * Real.pi))) := by
  let m := Real.sqrt (A / (16 * Real.pi))
  have hm : 0 < m := Real.sqrt_pos.2 (by positivity)
  have hs : m ^ 2 = A / (16 * Real.pi) := Real.sq_sqrt (by positivity)
  have hA' : A = 16 * Real.pi * m ^ 2 := by
    rw [hs]; field_simp
  change _ = (m + Q ^ 2 / (4 * m)) ^ 2 + _
  rw [kerrNewmanMassSq, hA']
  field_simp [hm.ne', Real.pi_ne_zero]
  ring

private theorem factor_relation {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    (horizonFactor M J Q + Q ^ 2) ^ 2 + 4 * J ^ 2 = 4 * M ^ 2 * horizonFactor M J Q := by
  have hr : horizonFactor M J Q + Q ^ 2 = 2 * M * rPlus M J Q := by
    unfold horizonFactor
    linarith [rPlus_sq_add_a_sq_eq h]
  rw [hr, horizonFactor]
  have hJ := congrArg (fun z : ℝ => z ^ 2) (spin_mul (J := J) hM)
  nlinarith only [hJ]

theorem christodoulou_ruffini_mass_sq {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    M ^ 2 = kerrNewmanMassSq (horizonArea M J Q) J Q := by
  unfold kerrNewmanMassSq horizonArea
  have hR := (factor_pos (J := J) (Q := Q) hM).ne'
  field_simp [hR, Real.pi_ne_zero]
  nlinarith only [factor_relation hM h]

theorem kerrNewmanMass_eq {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    kerrNewmanMass (horizonArea M J Q) J Q = M := by
  rw [kerrNewmanMass, ← christodoulou_ruffini_mass_sq hM h, Real.sqrt_sq hM.le]

private theorem first_law_area_coeff {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    (1 / (16 * Real.pi) - Real.pi * (Q ^ 4 + 4 * J ^ 2) / horizonArea M J Q ^ 2) /
        (2 * M) = surfaceGravity M J Q / (8 * Real.pi) := by
  have hR := (factor_pos (J := J) (Q := Q) hM).ne'
  have hr : horizonFactor M J Q + Q ^ 2 = 2 * M * rPlus M J Q := by
    unfold horizonFactor
    linarith [rPlus_sq_add_a_sq_eq h]
  have hh : horizonFactor M J Q ^ 2 - (Q ^ 4 + 4 * J ^ 2) =
      4 * M * horizonGap M J Q * horizonFactor M J Q := by
    have hr' := congrArg (fun x : ℝ => x * (2 * horizonFactor M J Q)) hr
    dsimp [rPlus] at hr'
    nlinarith only [factor_relation hM h, hr']
  rw [surfaceGravity_eq, horizonArea]
  field_simp [hR, hM.ne', Real.pi_ne_zero]
  nlinarith only [hh]

private theorem first_law_spin_coeff {M J Q : ℝ} (hM : 0 < M) :
    (Real.pi * (8 * J) / horizonArea M J Q) / (2 * M) = angularVelocity M J Q := by
  unfold horizonArea angularVelocity spin
  field_simp [(factor_pos (J := J) (Q := Q) hM).ne', hM.ne', Real.pi_ne_zero]
  ring

private theorem first_law_charge_coeff {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    (Q + Real.pi * (4 * Q ^ 3) / horizonArea M J Q) / (2 * M) =
      electricPotential M J Q := by
  have hR := (factor_pos (J := J) (Q := Q) hM).ne'
  have hr : horizonFactor M J Q + Q ^ 2 = 2 * M * rPlus M J Q := by
    unfold horizonFactor
    linarith [rPlus_sq_add_a_sq_eq h]
  have hr' := congrArg (fun x : ℝ => x * Q) hr
  unfold electricPotential horizonArea
  field_simp [hR, hM.ne', Real.pi_ne_zero]
  nlinarith only [hr']

/-- First law for differentiable area, angular momentum, and charge curves. It
remains valid at extremality in these thermodynamic coordinates. -/
theorem kerrNewman_first_law {M J Q t A' J' Q' : ℝ} {Acurve Jcurve Qcurve : ℝ → ℝ}
    (hM : 0 < M) (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2)
    (hA : Acurve t = horizonArea M J Q) (hJ : Jcurve t = J) (hQ : Qcurve t = Q)
    (dA : HasDerivAt Acurve A' t) (dJ : HasDerivAt Jcurve J' t)
    (dQ : HasDerivAt Qcurve Q' t) :
    HasDerivAt (fun s => kerrNewmanMass (Acurve s) (Jcurve s) (Qcurve s))
      (surfaceGravity M J Q / (8 * Real.pi) * A' + angularVelocity M J Q * J' +
        electricPotential M J Q * Q') t := by
  have hA0 : Acurve t ≠ 0 := hA.symm ▸ (horizonArea_pos (J := J) (Q := Q) hM).ne'
  have dSpin := HasDerivAt.const_mul (4 : ℝ) (dJ.fun_pow 2)
  have dNum := HasDerivAt.const_mul Real.pi (HasDerivAt.add (dQ.fun_pow 4) dSpin)
  have derivative := HasDerivAt.add
    (HasDerivAt.add (dA.div_const (16 * Real.pi)) ((dQ.fun_pow 2).div_const 2))
    (dNum.fun_div dA hA0)
  have derivative' : HasDerivAt (fun s => kerrNewmanMassSq (Acurve s) (Jcurve s) (Qcurve s))
      (A' / (16 * Real.pi) + Qcurve t * Q' +
        (Real.pi * (4 * Qcurve t ^ 3 * Q' + 8 * Jcurve t * J') * Acurve t -
          Real.pi * (Qcurve t ^ 4 + 4 * Jcurve t ^ 2) * A') / Acurve t ^ 2) t := by
    change HasDerivAt (fun s => kerrNewmanMassSq (Acurve s) (Jcurve s) (Qcurve s)) _ t at derivative
    convert derivative using 1
    norm_num [Pi.add_apply]
    ring
  have hm : kerrNewmanMassSq (Acurve t) (Jcurve t) (Qcurve t) = M ^ 2 := by
    rw [hA, hJ, hQ, ← christodoulou_ruffini_mass_sq hM h]
  have hd := derivative'.sqrt (show kerrNewmanMassSq (Acurve t) (Jcurve t) (Qcurve t) ≠ 0 by
    rw [hm]; positivity)
  change HasDerivAt (fun s => kerrNewmanMass (Acurve s) (Jcurve s) (Qcurve s)) _ t at hd
  convert hd using 1
  rw [hA, hJ, hQ, ← christodoulou_ruffini_mass_sq hM h, Real.sqrt_sq hM.le]
  rw [← first_law_area_coeff hM h, ← first_law_spin_coeff hM, ← first_law_charge_coeff hM h]
  have hA1 := (horizonArea_pos (J := J) (Q := Q) hM).ne'
  field_simp [hA1, hM.ne', Real.pi_ne_zero]
  ring

theorem kerrNewman_partial_A {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    HasDerivAt (fun A => kerrNewmanMass A J Q)
      (surfaceGravity M J Q / (8 * Real.pi)) (horizonArea M J Q) := by
  unfold horizonArea
  simpa [horizonArea] using kerrNewman_first_law (Acurve := id) (Jcurve := fun _ => J) (Qcurve := fun _ => Q)
    hM h rfl rfl rfl (hasDerivAt_id (horizonArea M J Q))
    (hasDerivAt_const (horizonArea M J Q) J) (hasDerivAt_const (horizonArea M J Q) Q)

theorem kerrNewman_partial_J {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    HasDerivAt (fun j => kerrNewmanMass (horizonArea M J Q) j Q) (angularVelocity M J Q) J := by
  simpa using kerrNewman_first_law (Acurve := fun _ => horizonArea M J Q) (Jcurve := id) (Qcurve := fun _ => Q)
    hM h rfl rfl rfl (hasDerivAt_const J (horizonArea M J Q))
    (hasDerivAt_id J) (hasDerivAt_const J Q)

theorem kerrNewman_partial_Q {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    HasDerivAt (fun q => kerrNewmanMass (horizonArea M J Q) J q) (electricPotential M J Q) Q := by
  simpa using kerrNewman_first_law (Acurve := fun _ => horizonArea M J Q) (Jcurve := fun _ => J) (Qcurve := id)
    hM h rfl rfl rfl (hasDerivAt_const Q (horizonArea M J Q))
    (hasDerivAt_const Q J) (hasDerivAt_id Q)

theorem kerrNewman_smarr_formula {M J Q : ℝ} (hM : 0 < M)
    (h : Q ^ 2 + spin M J ^ 2 ≤ M ^ 2) :
    M = surfaceGravity M J Q * horizonArea M J Q / (4 * Real.pi) +
      2 * angularVelocity M J Q * J + electricPotential M J Q * Q := by
  have hR := (factor_pos (J := J) (Q := Q) hM).ne'
  rw [surfaceGravity_eq, horizonArea, angularVelocity, electricPotential]
  field_simp [hR, Real.pi_ne_zero]
  unfold horizonFactor rPlus
  have hd := gap_sq h
  nlinarith only [congrArg (fun x : ℝ => x * M) hd,
    congrArg (fun x : ℝ => x * horizonGap M J Q) hd,
    congrArg (fun x : ℝ => x * spin M J) (spin_mul (J := J) hM), hd]

private theorem kerr_gap_sq {M J : ℝ} (hM : 0 < M) (hJ : |J| ≤ M ^ 2) :
    horizonGap M J 0 ^ 2 = M ^ 2 - spin M J ^ 2 := by
  have hj : |J| / M ≤ M := by
    apply (div_le_iff₀ hM).2
    simpa [pow_two] using hJ
  have hs : spin M J ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs (spin M J), sq_le_sq₀ (abs_nonneg _) hM.le, spin, abs_div, abs_of_pos hM]
    exact hj
  simpa using gap_sq (M := M) (J := J) (Q := 0) (by simpa using hs)

private theorem kerr_irred_sq {M J : ℝ} (hM : 0 < M) (hJ : |J| ≤ M ^ 2) :
    irreducibleMass M J 0 ^ 2 = M * (M + horizonGap M J 0) / 2 := by
  have hs := kerr_gap_sq hM hJ
  have hA := horizonArea_pos (J := J) (Q := 0) hM
  rw [irreducibleMass, Real.sq_sqrt (by positivity), horizonArea]
  unfold horizonFactor rPlus
  field_simp [Real.pi_ne_zero]
  nlinarith only [hs]

private theorem irred_nonneg (M J Q : ℝ) : 0 ≤ irreducibleMass M J Q := Real.sqrt_nonneg _

theorem kerr_irreducible_mass_bounds {M J : ℝ} (hM : 0 < M) (hJ : |J| ≤ M ^ 2) :
    M / Real.sqrt 2 ≤ irreducibleMass M J 0 ∧ irreducibleMass M J 0 ≤ M := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hg : 0 ≤ horizonGap M J 0 := Real.sqrt_nonneg _
  have hgs : horizonGap M J 0 ≤ M := by
    rw [← sq_le_sq₀ hg hM.le, kerr_gap_sq hM hJ]
    nlinarith [sq_nonneg (spin M J)]
  have hi := kerr_irred_sq hM hJ
  constructor
  · rw [← sq_le_sq₀ (by positivity) (irred_nonneg M J 0), div_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [mul_nonneg hM.le hg]
  · rw [← sq_le_sq₀ (irred_nonneg M J 0) hM.le]
    nlinarith [mul_le_mul_of_nonneg_left hgs hM.le]

theorem kerr_irreducible_mass_min_iff {M J : ℝ} (hM : 0 < M) (hJ : |J| ≤ M ^ 2) :
    irreducibleMass M J 0 = M / Real.sqrt 2 ↔ |J| = M ^ 2 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  rw [← sq_eq_sq₀ (irred_nonneg M J 0) (by positivity), div_pow, Real.sq_sqrt (by norm_num),
    kerr_irred_sq hM hJ]
  have hg : M * (M + horizonGap M J 0) / 2 = M ^ 2 / 2 ↔ horizonGap M J 0 = 0 := by
    constructor
    · intro he
      have hm : M * horizonGap M J 0 = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_left hM.ne'
    · intro he
      rw [he]; ring
  rw [hg, ← sq_eq_zero_iff, kerr_gap_sq hM hJ]
  rw [sub_eq_zero, eq_comm, ← sq_abs (spin M J), sq_eq_sq₀ (abs_nonneg _) hM.le,
    spin, abs_div, abs_of_pos hM, div_eq_iff hM.ne', pow_two]

private theorem schwarzschild_irred {M : ℝ} (hM : 0 < M) : irreducibleMass M 0 0 = M := by
  have hj : |(0 : ℝ)| ≤ M ^ 2 := by simpa using sq_nonneg M
  rw [← sq_eq_sq₀ (irred_nonneg _ _ _) hM.le, kerr_irred_sq hM hj]
  simp [horizonGap, spin, Real.sqrt_sq hM.le]
  ring

theorem penrose_efficiency_bound {M₁ J₁ M₂ J₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hJ₁ : |J₁| ≤ M₁ ^ 2) (hJ₂ : |J₂| ≤ M₂ ^ 2)
    (hA : horizonArea M₁ J₁ 0 ≤ horizonArea M₂ J₂ 0) :
    (M₁ - M₂) / M₁ ≤ 1 - 1 / Real.sqrt 2 := by
  have hi : irreducibleMass M₁ J₁ 0 ≤ irreducibleMass M₂ J₂ 0 :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hA (by positivity))
  have hb := (kerr_irreducible_mass_bounds hM₁ hJ₁).1.trans
    (hi.trans (kerr_irreducible_mass_bounds hM₂ hJ₂).2)
  rw [sub_div, div_self hM₁.ne']
  have hb' := (div_le_div_iff_of_pos_right hM₁).2 hb
  have he : M₁ / Real.sqrt 2 / M₁ = 1 / Real.sqrt 2 := by
    field_simp [hM₁.ne']
  rw [he] at hb'
  exact sub_le_sub_left hb' 1

theorem penrose_efficiency_sharp {M₁ J₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hJ : |J₁| = M₁ ^ 2) (hA : horizonArea M₂ 0 0 = horizonArea M₁ J₁ 0) :
    (M₁ - M₂) / M₁ = 1 - 1 / Real.sqrt 2 := by
  have he : irreducibleMass M₂ 0 0 = irreducibleMass M₁ J₁ 0 := by
    unfold irreducibleMass
    rw [hA]
  rw [schwarzschild_irred hM₂, (kerr_irreducible_mass_min_iff hM₁ hJ.le).2 hJ] at he
  rw [sub_div, div_self hM₁.ne', he]
  field_simp [hM₁.ne']

def hawkingTemp (ℏ κ : ℝ) : ℝ := ℏ * κ / (2 * Real.pi)
def bekensteinEntropy (G ℏ A : ℝ) : ℝ := A / (4 * G * ℏ)

theorem hawking_entropy_differential {G ℏ κ A dA : ℝ} (hG : 0 < G) (hh : 0 < ℏ) :
    hawkingTemp ℏ κ * deriv (bekensteinEntropy G ℏ) A * dA =
      κ / (8 * Real.pi * G) * dA := by
  have hd := (hasDerivAt_id A).div_const (4 * G * ℏ)
  change HasDerivAt (bekensteinEntropy G ℏ) (1 / (4 * G * ℏ)) A at hd
  rw [hd.deriv, hawkingTemp]
  field_simp [hG.ne', hh.ne', Real.pi_ne_zero]
  ring

def schwarzschildTemp (G ℏ M : ℝ) : ℝ := ℏ / (8 * Real.pi * G * M)

theorem hawking_temp_schwarzschild {G ℏ M : ℝ} (hG : 0 < G) (hM : 0 < M) :
    hawkingTemp ℏ (surfaceGravity (G * M) 0 0) = schwarzschildTemp G ℏ M := by
  rw [surfaceGravity_eq]
  have hm : 0 < G * M := mul_pos hG hM
  simp [hawkingTemp, schwarzschildTemp, horizonFactor, rPlus, horizonGap, spin,
    Real.sqrt_sq hm.le]
  field_simp [hG.ne', hM.ne', Real.pi_ne_zero]
  ring

theorem hawking_temp_schwarzschild_deriv {G ℏ M : ℝ} (hG : 0 < G) (hh : 0 < ℏ)
    (hM : 0 < M) :
    HasDerivAt (schwarzschildTemp G ℏ) (-ℏ / (8 * Real.pi * G * M ^ 2)) M ∧
      -ℏ / (8 * Real.pi * G * M ^ 2) < 0 := by
  have hd := (hasDerivAt_const M ℏ).fun_div
    (hasDerivAt_const_mul (x := M) (8 * Real.pi * G)) (by positivity)
  refine ⟨?_, div_neg_of_neg_of_pos (neg_neg_of_pos hh) (by positivity)⟩
  change HasDerivAt (schwarzschildTemp G ℏ) _ M at hd
  convert hd using 1
  field_simp [hG.ne', hM.ne', Real.pi_ne_zero]
  ring

/-- The reciprocal temperature parametrizes the Schwarzschild mass branch. -/
def schwarzschildMassAtTemp (G ℏ T : ℝ) : ℝ := ℏ / (8 * Real.pi * G * T)

theorem schwarzschild_specific_heat_neg {G ℏ M : ℝ} (hG : 0 < G) (hh : 0 < ℏ) (hM : 0 < M) :
    schwarzschildMassAtTemp G ℏ (schwarzschildTemp G ℏ M) = M ∧
      HasDerivAt (schwarzschildMassAtTemp G ℏ) (-8 * Real.pi * G * M ^ 2 / ℏ)
        (schwarzschildTemp G ℏ M) ∧ -8 * Real.pi * G * M ^ 2 / ℏ < 0 := by
  have ht : 0 < schwarzschildTemp G ℏ M := by unfold schwarzschildTemp; positivity
  have hd := (hasDerivAt_const (schwarzschildTemp G ℏ M) ℏ).fun_div
    (hasDerivAt_const_mul (x := schwarzschildTemp G ℏ M) (8 * Real.pi * G)) (by positivity)
  change HasDerivAt (schwarzschildMassAtTemp G ℏ) _ (schwarzschildTemp G ℏ M) at hd
  refine ⟨?_, ?_, ?_⟩
  · unfold schwarzschildMassAtTemp schwarzschildTemp
    field_simp [hG.ne', hh.ne', hM.ne', Real.pi_ne_zero]
  · convert hd using 1
    unfold schwarzschildTemp
    field_simp [hG.ne', hh.ne', hM.ne', Real.pi_ne_zero]
    ring
  · have hp : 0 < 8 * Real.pi * G * M ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) hh

/-- Along any approach to the extremal locus at fixed positive mass, the
surface gravity tends to zero. In particular this covers subextremal approaches. -/
theorem extremal_surface_gravity_tendsto_zero {ι : Type*} {l : Filter ι} {M : ℝ}
    {J Q : ι → ℝ} (hM : 0 < M)
    (h : Tendsto (fun t => Q t ^ 2 + spin M (J t) ^ 2) l (𝓝 (M ^ 2))) :
    Tendsto (fun t => surfaceGravity M (J t) (Q t)) l (𝓝 0) := by
  have hh : Tendsto (fun t => horizonGap M (J t) (Q t)) l (𝓝 0) := by
    have hd := tendsto_const_nhds.sub h (a := M ^ 2)
    have hs := (Real.continuous_sqrt.tendsto _).comp hd
    simpa only [sub_self, Real.sqrt_zero, Function.comp_def, horizonGap, sub_sub] using hs
  have hb : Tendsto (fun t => horizonGap M (J t) (Q t) / M ^ 2) l (𝓝 0) := by
    simpa using hh.div_const (M ^ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro t
    dsimp
    rw [surfaceGravity_eq]
    exact div_nonneg (Real.sqrt_nonneg _) (factor_pos hM).le
  · intro t
    dsimp
    rw [surfaceGravity_eq]
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    unfold horizonFactor rPlus
    have hg : 0 ≤ horizonGap M (J t) (Q t) := Real.sqrt_nonneg _
    nlinarith only [mul_nonneg hM.le hg, sq_nonneg (horizonGap M (J t) (Q t)),
      sq_nonneg (spin M (J t))]

end D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D
