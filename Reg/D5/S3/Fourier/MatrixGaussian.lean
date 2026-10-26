import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.MatrixGaussian

open MeasureTheory Matrix
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Fourier.MatrixGaussian
noncomputable section
universe u

abbrev expSignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization expSignature :=
  realize expSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)

def rejected : Realization expSignature :=
  realize expSignature (fun _ _ _ => 1) (fun e => nomatch e)

def integrableArena : Arena where
  signature := expSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ), A.PosDef → ∀ (b : ℂ), 0 < b.re → ∀ (c : ℂ) (w : n → ℝ),
      Integrable (fun x : n → ℝ => R.readout () ()
        (-b * (quadratic A x : ℂ) + c * (w ⬝ᵥ x : ℝ)))

def integralArena : Arena where
  signature := expSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ), A.PosDef → ∀ (b : ℂ), 0 < b.re → ∀ (c : ℂ) (w : n → ℝ),
      (∫ x : n → ℝ, R.readout () ()
        (-b * (quadratic A x : ℂ) + c * (w ⬝ᵥ x : ℝ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * (Real.pi / b) ^ ((Fintype.card n : ℂ) / 2) *
        R.readout () () (c ^ 2 * (quadratic A⁻¹ w : ℂ) / (4 * b))

def fourierArena : Arena where
  signature := expSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ), A.PosDef → ∀ (b : ℂ), 0 < b.re → ∀ (w : n → ℝ),
      (∫ x : n → ℝ, R.readout () () (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
        R.readout () () (-Real.pi * b * (quadratic A x : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(Fintype.card n : ℂ) / 2) *
        R.readout () () (-Real.pi / b * (quadratic A⁻¹ w : ℂ))

theorem integrable_bridge : (type_of% (@integrable_gaussian_linear.{u})) ↔
    integrableArena.{u}.Law actual := Iff.rfl

theorem integral_bridge : (type_of% (@integral_gaussian_linear.{u})) ↔
    integralArena.{u}.Law actual := Iff.rfl

theorem fourier_bridge : (type_of% (@integral_fourier_gaussian.{u})) ↔
    fourierArena.{u}.Law actual := Iff.rfl

theorem dependence : ObservationalDependence expSignature actual := by
  intro i
  refine ⟨(), 0, Complex.log 2, ?_⟩
  norm_num [actual, realize, Complex.exp_log]

theorem integral_rejected : ¬ integralArena.{u}.Law rejected := by
  intro h
  have hh := h (n := ULift.{u} (Fin 1)) 1 Matrix.PosDef.one (Real.pi : ℂ)
    (by simpa using Real.pi_pos) 0 0
  simpa [rejected, realize, MeasureTheory.integral_const, measureReal_def,
    MeasureTheory.Measure.pi_univ] using hh

def integralRegistration : Registration integralArena.{u}
    (type_of% (@integral_gaussian_linear.{u})) where
  actual := actual
  bridge := integral_bridge
  variation := ⟨@integral_gaussian_linear, rejected, integral_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, integral_rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_gaussian_linear.{u})
    (type_of% (realize expSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Fourier.MatrixGaussian.integral_gaussian_linear.information_unit,
  realizationName := `Reg.D5.S3.Fourier.MatrixGaussian.integralRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨integralArena.{u}⟩,
  objectArena := .source ⟨integralArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source integralArena.{u} ⟨integralRegistration⟩,
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

#print axioms integralRegistration
#print axioms registration_1
end
end Reg.D5.S3.Fourier.MatrixGaussian
