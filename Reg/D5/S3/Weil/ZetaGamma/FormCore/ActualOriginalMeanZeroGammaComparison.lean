import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualOriginalMeanZeroGammaComparison
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
import Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualOriginalMeanZeroGammaComparison

open MeasureTheory Set
open scoped ENNReal Topology
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol
open _root_.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open _root_.D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
    (fun _ _ F => ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- The complete public law, with exactly one integral occurrence replaced. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : ℝ) (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hmean : (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0)
    (hGamma : originalGammaFormDomain c F),
    Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) volume ∧
    -(R.readout () c F) / 2 ≤
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) -
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) / 2

private theorem source_reconstruction :
    (type_of% (@actual_original_mean_zero_gamma_excess_comparison)) ↔
      arena.Law actual := Iff.rfl

private theorem actual_law : arena.Law actual :=
  @actual_original_mean_zero_gamma_excess_comparison

private def zeroF : ℝ → ℂ := fun _ => 0

private theorem zero_profile (t : ℝ) : actualGammaProfile zeroF t = 0 := by
  simp [actualGammaProfile, fullTheta, physicalTerm, zeroF]

private theorem zero_h6 : originalPhysicalH6 zeroF := by
  constructor
  · exact MemLp.zero'
  · simp [zeroF]

private theorem zero_mean : (∫ r : ℝ, actualSuzukiEvenBProfile zeroF r) = 0 := by
  simp [actualSuzukiEvenBProfile, actualSuzukiBProfile, rightExponentialTail,
    zero_profile]

private theorem zero_fourier (ξ : ℝ) :
    unitarySourceFourier (actualGammaProfile zeroF) ξ = 0 := by
  simp [unitarySourceFourier_eq_integral, zero_profile]

private theorem zero_even_fourier (ξ : ℝ) :
    unitarySourceFourier (fun t : ℝ => actualGammaProfile zeroF |t|) ξ = 0 := by
  simp [unitarySourceFourier_eq_integral, zero_profile]

private theorem zero_gamma (c : ℝ) : originalGammaFormDomain c zeroF := by
  simp [originalGammaFormDomain, zero_fourier]

/- This bundle is used only to establish admissible witness states. It does
not restrict or replace the original State carrier or reconstruct the law
through a subtype. In particular no arbitrary H6-to-Gamma implication occurs. -/
private abbrev admissibleState (c : ℝ) :=
  { F : ℝ → ℂ // originalPhysicalH6 F ∧
    (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0 ∧ originalGammaFormDomain c F }

private def zeroState (c : ℝ) : admissibleState c :=
  ⟨zeroF, zero_h6, zero_mean, zero_gamma c⟩

private theorem zero_energy_facts (c : ℝ) :
    Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile zeroF |t|) ξ‖ ^ 2) volume ∧
    (∫ ξ : ℝ, (gammaWeight ξ + c) *
      ‖unitarySourceFourier (actualGammaProfile zeroF) ξ‖ ^ 2) = 0 ∧
    (∫ ξ : ℝ, (gammaWeight ξ + c) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile zeroF |t|) ξ‖ ^ 2) = 0 := by
  simp [zero_fourier, zero_even_fourier]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  let z : admissibleState 0 := zeroState 0
  have h := hall (0 : ℝ) z.1 z.2.1 z.2.2.1 z.2.2.2
  obtain ⟨hEven, hOneZero, hEvenZero⟩ := zero_energy_facts 0
  -- hEven proves that the first conclusion clause is true at this state.
  -- The second clause alone would demand 1/2 <= 0.
  have hbad := h.2
  change -(-1 : ℝ) / 2 ≤
    (∫ ξ : ℝ, (gammaWeight ξ + 0) *
      ‖unitarySourceFourier (actualGammaProfile zeroF) ξ‖ ^ 2) -
    (∫ ξ : ℝ, (gammaWeight ξ + 0) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile zeroF |t|) ξ‖ ^ 2) / 2 at hbad
  rw [hOneZero, hEvenZero] at hbad
  norm_num at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨F, hF, hmean, hAllGamma, hHasSum, hD, hThetaD⟩ :=
    actual_h6_mean_zero_positive_fullTheta_excess_all_gamma_domains
  let z : admissibleState 0 := zeroState 0
  let w : admissibleState 0 := ⟨F, hF, hmean, hAllGamma 0⟩
  -- Both states carry the SAME c=0 original dependent premises. The original
  -- function F is projected only after all its actual premises are supplied.
  -- hHasSum and hThetaD belong to this very F, not to a formal L2 substitute.
  refine ⟨(0 : ℝ), z.1, w.1, ?_⟩
  have hz : actual.readout i (0 : ℝ) z.1 = 0 := by
    simp [actual, realize, z, zeroState, zeroF]
  have hw : 0 < actual.readout i (0 : ℝ) w.1 := by
    simpa only [actual, realize, w] using hD
  rw [hz]
  exact ne_of_lt hw

def family : Registration arena
    (type_of% (@actual_original_mean_zero_gamma_excess_comparison)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The selector retains the full original law.
Lexical binders: c=0, F=1, hF=2, hmean=3, hGamma=4. Parameter c is retained.
After the five bodies: And.right; LE.left; division numerator; negation arg.
The final path ends at the integral, without entering its x lambda. It changes
no even Integrable clause or energy occurrence and creates no function operand.
-/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_original_mean_zero_gamma_excess_comparison)
    (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma.actual_original_mean_zero_gamma_excess_comparison.audit
  realizationName :=
    `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualOriginalMeanZeroGammaComparison.family
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
    (fun _ _ F => ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualOriginalMeanZeroGammaComparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualOriginalMeanZeroGammaComparison
