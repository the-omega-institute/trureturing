import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletRampEndpoint
import Reg.Support.SingleDependentReadout
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! One test replaces the logarithm at the endpoint. A second removes the eventual lower cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Set MeasureTheory Filter Finset
open _root_.D5.S3.Weil.Mertens _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.CharacterSums.DirichletRampEndpoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.CharacterSums.DirichletRampEndpoint

private theorem nonprincipal_three : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  exact ⟨χ, fun he => hχ (he ▸ MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))⟩

namespace Endpoint

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x),
    ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ ‖gChi χ x‖ / x + log (V.readout () () x) - 1 -
      eulerMascheroniConstant - ∫ u in Set.Ioi x, (Chebyshev.psi u - u) / u ^ 2

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hχ⟩ := nonprincipal_three
  have hb := h χ hχ (x := 2) (by norm_num)
  have hf : Finset.Ioc 0 (2 : ℕ) = {1,2} := by decide
  have hg : gChi χ 2 = (2 : ℂ) * (deriv χ.LFunction 1 / χ.LFunction 1) := by
    simp [gChi, hχ, characterRamp, hf, mangoldtRamp]
  have ht := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    WeightedPrimeLimit.chebyshev_error_kernel_integrable (show (2:ℝ) ≤ 2 by rfl)
  change ‖_‖ ≤ ‖gChi χ 2‖ / 2 + log 1 - 1 - eulerMascheroniConstant - _ at hb
  rw [hg, norm_mul] at hb
  simp [Chebyshev.psi, hf, Real.log_one] at ht hb
  linarith only [ht, hb, Real.log_pos (show (1:ℝ) < 2 by norm_num)]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @logDerivative_le_ramp_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logDerivative_le_ramp_tail, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@logDerivative_le_ramp_tail) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletRampEndpoint.logDerivative_le_ramp_tail
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.DirichletRampEndpoint.Endpoint "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Threshold

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {ε η : ℝ} (hε : ε < 1 / 2) (hη : 0 < η),
    ∃ X ≥ (2 : ℝ), ∀ x ≥ V.readout () () X, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → ‖gChi χ x‖ ≤ x ^ (1 / 2 + ε) →
      ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ log x - 1 - eulerMascheroniConstant + η

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X, _, hX⟩ := h (ε := 0) (η := 1) (by norm_num) (by norm_num)
  obtain ⟨χ, hχ⟩ := nonprincipal_three
  have hg : gChi χ 0 = 0 := by simp [gChi, hχ, characterRamp]
  have bad := hX 0 (le_refl _) χ hχ (by simp [hg])
  change ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ log 0 - 1 - eulerMascheroniConstant + 1 at bad
  rw [Real.log_zero] at bad
  linarith only [bad, norm_nonneg (deriv χ.LFunction 1 / χ.LFunction 1),
    Real.one_half_lt_eulerMascheroniConstant]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @uniform_logDerivative_of_ramp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_logDerivative_of_ramp, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_logDerivative_of_ramp) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletRampEndpoint.uniform_logDerivative_of_ramp
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.DirichletRampEndpoint.Threshold "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "domain", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Threshold

end Reg.D5.S3.CharacterSums.DirichletRampEndpoint
