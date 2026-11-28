import OmegaBuild.Commands
import OmegaMath.Analysis.FourSpatialMassShell
import OmegaMath.Analysis.WeightedConeProfiles
import OmegaMath.Analysis.ShellPairing
import OmegaMath.Analysis.HalfPowerCapIntegral
import OmegaMath.Analysis.RegulatedSeparation

/-!
Omega original.

Regulated cone shell squares and their position-space representation for a
compact angular space mapped continuously into four-dimensional Euclidean space.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped InnerProductSpace Topology

namespace Omega.FourSpatialConeShell

open Omega.ConeProfiles Omega.FourSpatialMassShell

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
variable (ι : A → E) (σ : Measure A) [IsFiniteMeasure σ] (hι : Continuous ι)

def fluxWeight (u : ℝ) : ℝ := u * Real.sqrt u

/-- The plane-wave amplitude of the affine radial derivative on the cone. -/
def amplitude (M : ℝ) (F : (ConeProfile A)) (k : E) : ℂ :=
  ∫ u in Ioo (0 : ℝ) 1, ∫ n : A, (fluxWeight u : ℂ) * profileDeriv F u n *
    Complex.exp (Complex.I * (((energy M k - ⟪k, ι n⟫_ℝ) * u : ℝ) : ℂ))
      ∂σ

/-- The shell square with positive imaginary-time damping. -/
def regulatedQuad (M ε : ℝ) (F : (ConeProfile A)) : ℝ :=
  4 * ∫ k : E, shellWeight M k * Real.exp (-ε * energy M k) * ‖amplitude ι σ M F k‖ ^ 2

/-- The regulated spectral form is nonnegative for every real mass and regulator. -/
theorem regulatedQuad_nonneg (M ε : ℝ) (F : (ConeProfile A)) :
    0 ≤ regulatedQuad ι σ M ε F := by
  unfold regulatedQuad
  refine mul_nonneg (by norm_num) (integral_nonneg (fun k => ?_))
  unfold Omega.FourSpatialMassShell.shellWeight Omega.FourSpatialMassShell.energy
  positivity

def coneMeasure : Measure (ℝ × A) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod σ

local instance : IsFiniteMeasure (coneMeasure σ) := by
  unfold coneMeasure
  infer_instance

private def phase (M : ℝ) (k : E) (p : (ℝ × A)) : ℝ :=
  (energy M k - ⟪k, ι p.2⟫_ℝ) * p.1

def derivativeWeight (F : (ConeProfile A)) (p : (ℝ × A)) : ℂ :=
  (fluxWeight p.1 : ℂ) * profileDeriv F p.1 p.2

theorem derivativeWeight_continuous (F : (ConeProfile A)) :
    Continuous (derivativeWeight F) :=
  by
  unfold derivativeWeight fluxWeight
  exact (Complex.continuous_ofReal.comp (continuous_fst.mul
    (Real.continuous_sqrt.comp continuous_fst))).mul (profileDeriv_continuous F)

theorem derivativeWeight_memLp (F : (ConeProfile A)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ p ∂(coneMeasure σ), ‖derivativeWeight F p‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ (univ : Set A)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := (hc.image (derivativeWeight_continuous F)).isBounded.exists_norm_le
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  have hae : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), u ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [((volume.restrict (Ioo (0 : ℝ) 1)).quasiMeasurePreserving_fst
    (ν := σ)).ae hae] with p hp
  exact (hC _ ⟨p, ⟨Ioo_subset_Icc_self hp, mem_univ _⟩, rfl⟩).trans (le_max_right _ _)

include hι in
private theorem phase_continuous (M : ℝ) :
    Continuous (fun p : E × (ℝ × A) => phase ι M p.1 p.2) := by
  have h := hι
  unfold phase energy
  fun_prop

private def planeWave (M : ℝ) (F : (ConeProfile A)) (k : E) (p : (ℝ × A)) : ℂ :=
  derivativeWeight F p * Complex.exp (Complex.I * (phase ι M k p : ℂ))

private theorem derivativeWeight_integrable (F : (ConeProfile A)) :
    Integrable (derivativeWeight F) (coneMeasure σ) := by
  obtain ⟨C, -, hC⟩ := derivativeWeight_memLp σ F
  exact (integrable_const C).mono' (derivativeWeight_continuous F).aestronglyMeasurable hC

include hι in
private theorem shellAmplitude_eq_integral (M : ℝ) (F : (ConeProfile A)) (k : E) :
    amplitude ι σ M F k = ∫ p, planeWave ι M F k p ∂(coneMeasure σ) :=
  (integral_prod _ (Omega.shellWave_integrable (a := derivativeWeight F) (phase := phase ι M)
    (derivativeWeight_integrable σ F) (phase_continuous ι hι M).measurable k)).symm

private def shellDamping (M ε : ℝ) (k : E) : ℝ :=
  shellWeight M k * Real.exp (-ε * energy M k)

private theorem shellDamping_integrable (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (shellDamping M ε) := by
  have hτ : 0 < (ε : ℂ).re := by simpa using hε
  convert (Omega.FourSpatialMassShell.bulkU5D_integrable M hτ (0 : E)).norm using 1
  funext k
  simp only [shellDamping, inner_zero_right, Complex.ofReal_zero, mul_zero, add_zero,
    norm_mul, Complex.norm_real, Complex.norm_exp]
  have hnonneg : 0 ≤ shellWeight M k := by unfold Omega.FourSpatialMassShell.shellWeight Omega.FourSpatialMassShell.energy; positivity
  rw [Real.norm_of_nonneg hnonneg]
  congr 2
  simp [Complex.mul_re]

def conePair (M ε : ℝ) (F : (ConeProfile A))
    (z : E × ((ℝ × A) × (ℝ × A))) : ℂ :=
  (shellDamping M ε z.1 : ℂ) *
    (star (planeWave ι M F z.1 z.2.1) * planeWave ι M F z.1 z.2.2)

include hι in
theorem conePair_integrable (M : ℝ) {ε : ℝ} (hε : 0 < ε) (F : (ConeProfile A)) :
    Integrable (conePair ι M ε F) ((volume : Measure E).prod ((coneMeasure σ).prod (coneMeasure σ))) :=
  Omega.shellPair_integrable (a := derivativeWeight F) (phase := phase ι M)
    (shellDamping_integrable M hε) (derivativeWeight_integrable σ F) (phase_continuous ι hι M).measurable

def coneTime (ε : ℝ) (z : (ℝ × A) × (ℝ × A)) : ℂ :=
  (ε : ℂ) + Complex.I * ((z.1.1 - z.2.1 : ℝ) : ℂ)

def coneDisplacement (z : (ℝ × A) × (ℝ × A)) : E :=
  z.1.1 • ι z.1.2 - z.2.1 • ι z.2.2

def bulkIntegrand (M ε : ℝ) (F : (ConeProfile A)) (z : (ℝ × A) × (ℝ × A)) : ℂ :=
  star (derivativeWeight F z.1) * derivativeWeight F z.2 *
    bulkU5D M (coneTime ε z) (coneDisplacement ι z)

theorem bulkIntegrand_eq_inner (M ε : ℝ) (F : (ConeProfile A))
    (z : (ℝ × A) × (ℝ × A)) :
    (∫ k : E, conePair ι M ε F (k, z)) = bulkIntegrand ι M ε F z := by
  unfold bulkIntegrand coneTime coneDisplacement Omega.FourSpatialMassShell.bulkU5D
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  simp only [conePair, planeWave, shellDamping, Complex.ofReal_mul, Complex.ofReal_exp,
    star_mul, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  simp only [phase, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  rw [show ∀ a b c d e f : ℂ, a * b * (c * d * (e * f)) =
    (d * e) * (a * ((b * c) * f)) by intros; ring]
  simp only [← Complex.exp_add]
  congr 3
  ring

include hι in
/-- At fixed positive regulator, the square of the plane-wave amplitude equals
the double boundary pairing with the regulated bulk kernel. -/
theorem regulatedQuad_eq_bulk (M : ℝ) {ε : ℝ} (hε : 0 < ε) (F : (ConeProfile A)) :
    regulatedQuad ι σ M ε F =
      (4 * ∫ z : (ℝ × A) × (ℝ × A),
        star (derivativeWeight F z.1) * derivativeWeight F z.2 *
          bulkU5D M ((ε : ℂ) + Complex.I * ((z.1.1 - z.2.1 : ℝ) : ℂ))
            (z.1.1 • ι z.1.2 - z.2.1 • ι z.2.2)
        ∂((coneMeasure σ).prod (coneMeasure σ))).re := by
  have h := Omega.integral_shellWave_norm_sq (a := derivativeWeight F) (phase := phase ι M)
    (shellDamping_integrable M hε) (derivativeWeight_integrable σ F) (phase_continuous ι hι M).measurable
  change (∫ k : E, shellDamping M ε k * ‖∫ p, planeWave ι M F k p ∂(coneMeasure σ)‖ ^ 2) =
    (∫ z, ∫ k : E, conePair ι M ε F (k,z) ∂volume ∂((coneMeasure σ).prod (coneMeasure σ))).re at h
  simp_rw [← shellAmplitude_eq_integral ι σ hι, bulkIntegrand_eq_inner ι] at h
  change (4 * ∫ k, shellDamping M ε k * ‖amplitude ι σ M F k‖ ^ 2) =
    (4 * ∫ z, bulkIntegrand ι M ε F z ∂((coneMeasure σ).prod (coneMeasure σ))).re
  rw [h]
  simp [Complex.mul_re]

theorem fluxWeight_rpow {u : ℝ} (hu : 0 < u) :
    fluxWeight u = u ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  rfl

abbrev capPrefactor : ℂ := 1 / (4 * (Real.pi : ℂ) ^ 2 * (Real.sqrt 2 : ℂ))

theorem bulkU5D_zero_cap {ε u v x : ℝ} (hε : 0 < ε) (hu : 0 < u) (hv : 0 < v)
    (hx : x ≤ 1) (r : E)
    (hsep : ((‖r‖ ^ 2 : ℝ) : ℂ) + ((ε : ℂ) + Complex.I * ((u - v : ℝ) : ℂ)) ^ 2 =
      Omega.regulatedSeparation ε u v x) :
    (4 * (fluxWeight u : ℂ) * (fluxWeight v : ℂ)) *
      bulkU5D 0 ((ε : ℂ) + Complex.I * ((u - v : ℝ) : ℂ)) r =
        capPrefactor * Omega.halfPowerCap (1 - x) (Omega.capShift ε u v) := by
  let k := 1 - x
  let d := Omega.capShift ε u v
  let C := 2 * u * v
  let z : ℂ := (k : ℂ) + d
  have hC : 0 < C := by dsimp [C]; positivity
  have hz : z ≠ 0 := by
    apply Complex.slitPlane_ne_zero
    apply Or.inl
    dsimp [z, d]
    rw [Omega.capShift_re]
    have hk : 0 ≤ k := sub_nonneg.mpr hx
    positivity
  have he : Omega.regulatedSeparation ε u v x = (C : ℂ) * z := by
    have hc : ((C : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    change _ = (C : ℂ) * ((k : ℂ) + d)
    rw [mul_add]
    have hd : d = (((ε ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * ε * (u - v) : ℝ) : ℂ)) /
        (C : ℂ) := rfl
    rw [hd, mul_div_cancel₀ _ hc]
    unfold Omega.regulatedSeparation C k
    push_cast
    ring
  have hτ : 0 < ((ε : ℂ) + Complex.I * ((u - v : ℝ) : ℂ)).re := by
    simpa [Complex.mul_re] using hε
  rw [Omega.FourSpatialMassShell.bulkU5D_elementary (M := 0) le_rfl hτ]
  change _ * Omega.FourSpatialMassShell.elementary 0
    (((‖r‖ ^ 2 : ℝ) : ℂ) + ((ε : ℂ) + Complex.I * ((u - v : ℝ) : ℂ)) ^ 2) = _
  rw [hsep, he]
  simp only [Omega.FourSpatialMassShell.elementary, Complex.ofReal_zero, neg_zero,
    zero_mul, Complex.exp_zero, add_zero, mul_one]
  have hs : ((C : ℂ) * z) ^ (1 / 2 : ℂ) = (Real.sqrt C : ℂ) * principalRoot z := by
    change _ = _
    rw [show (1 / 2 : ℂ) = 2⁻¹ by ring]
    exact Omega.principalRoot_scale hC hz
  rw [hs]
  have hr : Real.sqrt C = Real.sqrt 2 * Real.sqrt u * Real.sqrt v := by
    unfold C
    rw [Real.sqrt_mul (mul_nonneg (by norm_num) hu.le), Real.sqrt_mul (by norm_num)]
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.2 (by norm_num)).ne'
  have hp : (Real.sqrt u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hu).ne'
  have hq : (Real.sqrt v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hv).ne'
  change _ = capPrefactor * (z⁻¹ * (principalRoot z)⁻¹)
  unfold capPrefactor fluxWeight
  rw [hr]
  dsimp only [C]
  push_cast
  field_simp [hz, hp, hq, hn, Complex.ofReal_ne_zero.mpr hu.ne',
    Complex.ofReal_ne_zero.mpr hv.ne', Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

end Omega.FourSpatialConeShell
