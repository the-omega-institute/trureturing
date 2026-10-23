import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set
open scoped ENNReal
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

-- The varying state is the original physical source, not a theorem proof.
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ F => ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

-- All original clauses remain.  Only the one actual positive-mass data
-- occurrence is observed; other theta, Fourier/domain and metric expressions
-- are kept literally as in the original compiler statement.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ K : ℝ, (∃ F : ℝ → ℂ,
    originalPhysicalH6 F ∧
    (∀ x : ℝ, (F x).im = 0) ∧
    (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
    Integrable (actualGammaProfile F) volume ∧
    MemLp (actualGammaProfile F) 2 volume ∧
    (∀ q : ℝ, Integrable
      (fun t : ℝ => Real.exp (q * t) * ‖actualGammaProfile F t‖ ^ 2) volume) ∧
    (0 < R.readout () K F) ∧
    Integrable (fun t : ℝ => t * ‖actualGammaProfile F t‖ ^ 2)
      (volume.restrict (Ioi 0)) ∧
    (0 < ∫ t : ℝ in Ioi 0, t * ‖actualGammaProfile F t‖ ^ 2) ∧
    (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
    ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
      K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
    ((∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
      ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2)) = ∞) ∧
    (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
      ¬ originalGammaFormDomain c F)) ↔ 1 < K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨F, _, _, _, _, _, _, hmass, _, _, _, _, _, _⟩ :=
    (h (2 : ℝ)).mpr (by norm_num)
  norm_num [rejected, realize] at hmass

def family : Registration arena
    (type_of% @actual_h6_gamma_domain_escape_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_h6_gamma_domain_escape_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨F, _, _, _, _, _, _, hmass, _, _, _, _, _, _⟩ :=
      (actual_h6_gamma_domain_escape_iff (2 : ℝ)).mpr (by norm_num)
    refine ⟨(2 : ℝ), (fun _ : ℝ => (0 : ℂ)), F, ?_⟩
    change (∫ t : ℝ, ‖actualGammaProfile (fun _ : ℝ => (0 : ℂ)) t‖ ^ 2) ≠
      ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2
    have hzero :
        (∫ t : ℝ, ‖actualGammaProfile (fun _ : ℝ => (0 : ℂ)) t‖ ^ 2) = 0 := by
      simp [actualGammaProfile, fullTheta, physicalTerm]
    rw [hzero]
    exact ne_of_lt hmass

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_h6_gamma_domain_escape_iff)
    (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actual_h6_gamma_domain_escape_iff.audit
  realizationName :=
    `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.family
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
    (fun _ _ F => ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℂ)
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
    definition := none
    coordinates := #[0]
    readouts := #[{
      -- K forall body / Iff left / Exists predicate / F lambda / six right
      -- And branches / left clause / right operand of 0 < actual mass.
      path := #["body", "fn", "arg", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
