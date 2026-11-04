import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.MatrixGaussianSecondMoment

/-! Source-bound exponential-family audits for the quadratic Fourier and inversion laws. -/

open MeasureTheory Matrix LeanInformationAudit
open scoped BigOperators
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Fourier.MatrixGaussianSecondMoment
noncomputable section
open Reg.D5.S3.Fourier.MatrixGaussian

def fourierArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re → ∀ (u v w : Fin r → ℝ),
    (∫ x : Fin r → ℝ, R.readout () () (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      ((u ⬝ᵥ A *ᵥ x : ℝ) : ℂ) * ((v ⬝ᵥ A *ᵥ x : ℝ) : ℂ) *
      R.readout () () (-Real.pi * b * (quadratic A x : ℂ))) =
    (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
      (((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) / (2 * Real.pi * b) -
        ((u ⬝ᵥ w : ℝ) : ℂ) * ((v ⬝ᵥ w : ℝ) : ℂ) / b ^ 2) *
      R.readout () () (-Real.pi / b * (quadratic A⁻¹ w : ℂ))

theorem fourier_bridge : (type_of% (@integral_fourier_second_moment)) ↔
    fourierArena.Law actual := Iff.rfl

def observedTerm (R : Realization expSignature) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (u v : Fin r → ℝ) (τ : ℂ) (n : Fin r → ℤ) : ℂ :=
  ((u ⬝ᵥ A *ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) *
  ((v ⬝ᵥ A *ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) *
  R.readout () () (Real.pi * Complex.I * τ * (quadratic A (fun i => (n i : ℝ)) : ℂ))

def inversionArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (u v : Fin r → ℝ) (τ : ℂ), 0 < τ.im →
    Summable (fun n : Fin r → ℤ => ‖observedTerm R A u v (-1 / τ) n‖) ∧
    HasSum (observedTerm R A u v (-1 / τ))
      (((-Complex.I * τ) ^ ((r : ℂ) / 2) / (Real.sqrt A.det : ℂ)) *
        (τ ^ 2 * (∑' n : Fin r → ℤ, observedTerm R A⁻¹ (A *ᵥ u) (A *ᵥ v) τ n) +
          τ / (2 * Real.pi * Complex.I) * ((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) *
            ∑' n : Fin r → ℤ, R.readout () ()
              (Real.pi * Complex.I * τ * (quadratic A⁻¹ (fun i => (n i : ℝ)) : ℂ))))

theorem inversion_bridge : (type_of% (@second_moment_inversion)) ↔
    inversionArena.Law actual := Iff.rfl

def negative : Realization expSignature :=
  realize expSignature (fun _ _ z => -Complex.exp z) (fun e => nomatch e)

theorem fourier_rejected : ¬ fourierArena.Law negative := by
  intro h
  have hb := h (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one 1 (by norm_num)
    (fun _ => 1) (fun _ => 1) 0
  have hg := integral_fourier_second_moment (1 : Matrix (Fin 1) (Fin 1) ℝ)
    Matrix.PosDef.one 1 (by norm_num) (fun _ => 1) (fun _ => 1) 0
  norm_num [negative, realize, quadratic, dotProduct, Matrix.mulVec] at hb hg
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz : (Real.pi : ℂ)⁻¹ * (1 / 2) = -((Real.pi : ℂ)⁻¹ * (1 / 2)) := hg.symm.trans hb
  have hn : (Real.pi : ℂ)⁻¹ * (1 / 2) ≠ 0 := mul_ne_zero (inv_ne_zero hp) (by norm_num)
  apply hn
  linear_combination (1 / 2 : ℂ) * hz

theorem inversion_rejected : ¬ inversionArena.Law rejected := by
  intro h
  have hh := (h (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one
    (fun _ => 1) (fun _ => 1) Complex.I (by norm_num)).1
  let embed := fun k : ℕ => fun _ : Fin 1 => (k + 1 : ℤ)
  have he : Function.Injective embed := by
    intro a b hab
    have hh := congrFun hab 0
    dsimp [embed] at hh
    exact_mod_cast (add_right_cancel hh)
  have hs := hh.comp_injective he
  have hs' : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2) := by
    convert hs using 1
    funext k
    simp [observedTerm, rejected, realize, embed, dotProduct, Matrix.mulVec, norm_mul,
      Complex.norm_real, abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity), pow_two]
  have hc : Summable (fun _ : ℕ => (1 : ℝ)) := hs'.of_nonneg_of_le (fun _ => zero_le_one)
    (fun k => by nlinarith [show 0 ≤ (k : ℝ) by positivity])
  simpa [summable_const_iff] using hc

def fourierRegistration : Registration fourierArena
    (type_of% (@integral_fourier_second_moment)) where
  actual := actual
  bridge := fourier_bridge
  variation := ⟨@integral_fourier_second_moment, negative, fourier_rejected⟩
  sensitivity := ⟨fun i => ⟨negative,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, fourier_rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def inversionRegistration : Registration inversionArena
    (type_of% (@second_moment_inversion)) where
  actual := actual
  bridge := inversion_bridge
  variation := ⟨@second_moment_inversion, rejected, inversion_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, inversion_rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_fourier_second_moment)
    (type_of% (realize expSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Fourier.MatrixGaussian.integral_fourier_second_moment.information_unit,
  realizationName := `Reg.D5.S3.Fourier.MatrixGaussianSecondMoment.fourierRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨fourierArena⟩,
  objectArena := .source ⟨fourierArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source fourierArena ⟨fourierRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize expSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@second_moment_inversion)
    (type_of% (realize expSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Fourier.MatrixGaussian.second_moment_inversion.information_unit,
  realizationName := `Reg.D5.S3.Fourier.MatrixGaussianSecondMoment.inversionRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨inversionArena⟩,
  objectArena := .source ⟨inversionArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source inversionArena ⟨inversionRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize expSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


end
end Reg.D5.S3.Fourier.MatrixGaussianSecondMoment
