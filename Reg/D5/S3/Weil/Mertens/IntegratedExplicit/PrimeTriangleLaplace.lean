import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Reg.Support.SingleDependentReadout

/-! The triangular Laplace transform is an observable readout for the residue theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Analytic.Laplace.EulerPoleObstruction (kernel)
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
  (zetaZeroData zetaZeroData_isNontrivial)
open scoped Topology

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ => hingeTransform) (fun e => nomatch e)

private def shifted : Realization signature :=
  realize signature (fun _ _ s => hingeTransform s + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V :=
    let Φ := V.readout () ()
    (∀ s : ℂ, 1 < s.re →
      IntegrableOn (kernel (fun t => PrimeQuarterTriangle.hinge U (Real.exp t)) s) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), kernel (fun u => PrimeQuarterTriangle.hinge U (Real.exp u)) s t) = Φ s) ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
      multiplier ρ * c ≠ 0 ∧
        Tendsto (fun s : ℂ => (s - ρ) * Φ s) (𝓝[≠] ρ) (𝓝 (multiplier ρ * c))

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hs : 1 < (2 : ℂ).re := by norm_num
  have he := (hingeTransform_integral_and_zero_residues.1 2 hs).2.symm.trans (h.1 2 hs).2
  change hingeTransform 2 = hingeTransform 2 + 1 at he
  exact one_ne_zero (by linear_combination -he : (1 : ℂ) = 0)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  by_contra! hconstant
  let z := zetaZeroData.zero 0
  have hz := zetaZeroData_isNontrivial 0
  obtain ⟨hn, hpole⟩ := hingeTransform_integral_and_zero_residues.2 z hz.1 hz.2.1 hz.2.2
  have hconst (s : ℂ) : hingeTransform s = hingeTransform z := hconstant () s z
  have hzero : Tendsto (fun s : ℂ => (s - z) * hingeTransform z) (𝓝[≠] z) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have hcont : ContinuousAt (fun s : ℂ => (s - z) * hingeTransform z) z :=
      (continuousAt_id.sub continuousAt_const).mul continuousAt_const
    simpa only [sub_self, zero_mul] using hcont.tendsto
  have heq : (fun s : ℂ => (s - z) * hingeTransform z) =ᶠ[𝓝[≠] z]
      (fun s : ℂ => (s - z) * hingeTransform s) :=
    Eventually.of_forall (fun s => by
      change (s - z) * hingeTransform z = (s - z) * hingeTransform s
      rw [hconst s])
  exact hn (tendsto_nhds_unique hpole (hzero.congr' heq))

def evidence : Registration arena (type_of% @hingeTransform_integral_and_zero_residues) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hingeTransform_integral_and_zero_residues, shifted, shifted_fails⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual shifted shifted_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hingeTransform_integral_and_zero_residues) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace.hingeTransform_integral_and_zero_residues.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => hingeTransform) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace
