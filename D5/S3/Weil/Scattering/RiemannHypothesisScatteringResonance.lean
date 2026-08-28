/- GID: D5/S3/Weil/Scattering/RiemannHypothesisScatteringResonance
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/RiemannHypothesisScatteringResonance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify RH with the quarter-line poles and three-quarter-line scattering zeros. -/

import D5.S3.Weil.Scattering.CompletedZetaScatteringCollapse
import D5.S3.Weil.ZetaRvm.CountByIntegral
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace D5.S3.Weil.Scattering.RiemannHypothesisScatteringResonance

open Filter
open Zeta23
open Zeta23.RvM

noncomputable section

-- The modular-surface scattering coefficient as the source's completed-zeta ratio.
def scatteringCoefficient (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)

-- A nontrivial scattering pole is a zero of the completed-zeta denominator.
def IsNontrivialScatteringPole (s : ℂ) : Prop :=
  completedRiemannZeta (2 * s) = 0

-- A nontrivial scattering zero is a zero of the completed-zeta numerator.
def IsNontrivialScatteringZero (s : ℂ) : Prop :=
  completedRiemannZeta (2 * s - 1) = 0

-- The resonance coordinate attached to a nontrivial zeta zero.
def scatteringResonance (rho : ℂ) : ℂ :=
  (1 / 2 : ℂ) * rho

private theorem affine_injective (b : ℂ) :
    Function.Injective (fun s : ℂ => 2 * s + b) := by
  intro s t h
  have h' : 2 * s + b = 2 * t + b := by
    simpa using h
  have hmul : (2 : ℂ) * s = 2 * t := by
    calc
      (2 : ℂ) * s = (2 * s + b) - b := by ring
      _ = (2 * t + b) - b := by rw [h']
      _ = 2 * t := by ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hmul

private theorem eventually_affine_zeta_ne_zero (b : ℂ) :
    ∀ᶠ s in codiscrete ℂ, riemannZeta (2 * s + b) ≠ 0 := by
  let affine : ℂ → ℂ := fun s => 2 * s + b
  have hcontinuous : Continuous affine := by
    unfold affine
    fun_prop
  have hclosed : IsClosed (affine ⁻¹' riemannZetaZeros) :=
    isClosed_riemannZetaZeros.preimage hcontinuous
  have hdiscrete : IsDiscrete (affine ⁻¹' riemannZetaZeros) :=
    isDiscrete_riemannZetaZeros.preimage hcontinuous.continuousOn
      (by simpa [affine] using affine_injective b)
  have hcodiscrete : (affine ⁻¹' riemannZetaZeros)ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨hclosed, hdiscrete⟩
  filter_upwards [hcodiscrete] with s hs
  simpa [affine, riemannZetaZeros] using hs

private theorem eventually_affine_completed_zeta_ne_zero (b : ℂ) :
    ∀ᶠ s in codiscrete ℂ, completedRiemannZeta (2 * s + b) ≠ 0 := by
  filter_upwards [eventually_affine_zeta_ne_zero b] with s hs
  intro hcompleted
  exact hs (completedRiemannZeta_eq_zero_iff.mp hcompleted).1

private theorem scattering_functional_equation :
    (fun s => scatteringCoefficient s * scatteringCoefficient (1 - s))
      =ᶠ[codiscrete ℂ] fun _ => 1 := by
  filter_upwards [eventually_affine_completed_zeta_ne_zero (-1),
    eventually_affine_completed_zeta_ne_zero 0] with s hnum hden
  have hnumeratorReflection :
      completedRiemannZeta (2 * (1 - s) - 1) = completedRiemannZeta (2 * s) := by
    convert completedRiemannZeta_one_sub (2 * s) using 1 <;> ring
  have hdenominatorReflection :
      completedRiemannZeta (2 * (1 - s)) = completedRiemannZeta (2 * s - 1) := by
    convert completedRiemannZeta_one_sub (2 * s - 1) using 1 <;> ring
  rw [scatteringCoefficient, scatteringCoefficient,
    hnumeratorReflection, hdenominatorReflection]
  have hnum' : completedRiemannZeta (2 * s - 1) ≠ 0 := by
    simpa only [sub_eq_add_neg] using hnum
  have hden' : completedRiemannZeta (2 * s) ≠ 0 := by
    simpa using hden
  field_simp

private theorem strip_zero_of_mathlib_nontrivial_inputs {rho : ℂ}
    (hzero : riemannZeta rho = 0)
    (hnotTrivial : ¬∃ n : ℕ, rho = -2 * (n + 1)) :
    IsNontrivialZero rho := by
  refine ⟨hzero, ?_, ?_⟩
  · by_contra hpositive
    have hre : rho.re ≤ 0 := le_of_not_gt hpositive
    have hrhoZero : rho ≠ 0 := by
      intro hrho
      subst rho
      rw [riemannZeta_zero] at hzero
      norm_num at hzero
    have hcompleted : completedRiemannZeta rho ≠ 0 :=
      completedRiemannZeta_ne_zero_of_re_nonpos hre
    have hgamma : Complex.Gammaℝ rho = 0 := by
      rw [riemannZeta_def_of_ne_zero hrhoZero] at hzero
      exact (div_eq_zero_iff.mp hzero).resolve_left hcompleted
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hgamma
    cases n with
    | zero =>
        apply hrhoZero
        simpa using hn
    | succ n =>
        apply hnotTrivial
        refine ⟨n, ?_⟩
        simpa [Nat.cast_add, Nat.cast_one] using hn
  · by_contra hlt
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hlt) hzero

private theorem rh_iff_scattering_poles_on_quarter_line :
    RiemannHypothesis ↔
      ∀ {s : ℂ}, IsNontrivialScatteringPole s → s.re = 1 / 4 := by
  constructor
  · intro hRH s hpole
    have hzero : IsNontrivialZero (2 * s) :=
      completedRiemannZeta_eq_zero_iff.mp hpole
    have hline := RH_implies_on_line hRH hzero
    norm_num at hline ⊢
    linarith
  · intro hpoles rho hzero hnotTrivial _
    have hstrip := strip_zero_of_mathlib_nontrivial_inputs hzero hnotTrivial
    have hpole : IsNontrivialScatteringPole (scatteringResonance rho) := by
      unfold IsNontrivialScatteringPole scatteringResonance
      convert completedRiemannZeta_eq_zero_iff.mpr hstrip using 1 <;> ring
    have hquarter := hpoles hpole
    simp [scatteringResonance] at hquarter
    linarith

private theorem corresponding_scattering_zero :
    ∀ {rho : ℂ}, IsNontrivialZero rho →
      IsNontrivialScatteringZero (1 - scatteringResonance rho) := by
  intro rho hrho
  have hcompleted : completedRiemannZeta rho = 0 :=
    completedRiemannZeta_eq_zero_iff.mpr hrho
  have hreflected : completedRiemannZeta (1 - rho) = 0 :=
    (completedRiemannZeta_one_sub rho).trans hcompleted
  unfold IsNontrivialScatteringZero scatteringResonance
  convert hreflected using 1 <;> ring

private theorem rh_iff_scattering_zeros_on_three_quarter_line :
    RiemannHypothesis ↔
      ∀ {s : ℂ}, IsNontrivialScatteringZero s → s.re = 3 / 4 := by
  constructor
  · intro hRH s hzero
    have hzeta : IsNontrivialZero (2 * s - 1) :=
      completedRiemannZeta_eq_zero_iff.mp hzero
    have hline := RH_implies_on_line hRH hzeta
    norm_num at hline ⊢
    linarith
  · intro hzeros rho hzero hnotTrivial _
    have hstrip := strip_zero_of_mathlib_nontrivial_inputs hzero hnotTrivial
    have hscatteringZero := corresponding_scattering_zero hstrip
    have hthreeQuarters := hzeros hscatteringZero
    simp [scatteringResonance] at hthreeQuarters
    linarith

private theorem critical_line_coordinate_split :
    (∀ rho : ℂ, rho.re = 1 / 2 →
      (scatteringResonance rho).re = 1 / 4) ∧
    (∀ rho : ℂ, rho.re = 1 / 2 →
      (1 - scatteringResonance rho).re = 3 / 4) := by
  constructor <;> intro rho hline <;> simp [scatteringResonance] <;> linarith

-- RH is equivalent to the quarter-line resonance form and to its reflected
-- three-quarter-line antiresonance form; the completed-zeta scattering ratio obeys
-- the functional equation as a meromorphic identity.
theorem riemann_hypothesis_scattering_resonance_form :
    (RiemannHypothesis ↔
      ∀ {s : ℂ}, IsNontrivialScatteringPole s → s.re = 1 / 4) ∧
    ((fun s => scatteringCoefficient s * scatteringCoefficient (1 - s))
      =ᶠ[codiscrete ℂ] fun _ => 1) ∧
    (∀ {rho : ℂ}, IsNontrivialZero rho →
      IsNontrivialScatteringZero (1 - scatteringResonance rho)) ∧
    (RiemannHypothesis ↔
      ∀ {s : ℂ}, IsNontrivialScatteringZero s → s.re = 3 / 4) ∧
    ((∀ rho : ℂ, rho.re = 1 / 2 →
        (scatteringResonance rho).re = 1 / 4) ∧
      (∀ rho : ℂ, rho.re = 1 / 2 →
        (1 - scatteringResonance rho).re = 3 / 4)) := by
  exact ⟨rh_iff_scattering_poles_on_quarter_line,
    scattering_functional_equation,
    corresponding_scattering_zero,
    rh_iff_scattering_zeros_on_three_quarter_line,
    critical_line_coordinate_split⟩

example
    (hpoles : ∀ {s : ℂ}, IsNontrivialScatteringPole s → s.re = 1 / 4) :
    RiemannHypothesis :=
  riemann_hypothesis_scattering_resonance_form.1.mpr hpoles

example {rho : ℂ} (hrho : IsNontrivialZero rho) :
    completedRiemannZeta (2 * (1 - scatteringResonance rho) - 1) = 0 := by
  exact riemann_hypothesis_scattering_resonance_form.2.2.1 hrho

example : ¬IsNontrivialScatteringPole 0 := by
  intro hpole
  apply completedRiemannZeta_ne_zero_of_re_nonpos (s := 0) (by norm_num)
  simpa [IsNontrivialScatteringPole] using hpole

end

end D5.S3.Weil.Scattering.RiemannHypothesisScatteringResonance
