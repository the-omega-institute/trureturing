import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Metric
open _root_.D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

/-- The actual zeta value in the incoming zero hypothesis. -/
def actual : Realization signature :=
  realize signature (fun _ _ z => riemannZeta z) (fun e => nomatch e)

def allZeros : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {z₀ : ℂ} (_ : V.readout () () z₀ = 0) {σ δ : ℝ} (_ : 2 < σ)
    (_ : 0 < δ) (_ : δ < z₀.re - 1/2),
    ∃ (p ρ : ℂ) (r : ℝ), p.re = σ ∧ riemannZeta ρ = 0 ∧
      0 < dist p ρ ∧ dist p ρ < r ∧ r < σ-z₀.re+δ ∧
      (∀ w ∈ closedBall (σ : ℂ) r, 1/2 < w.re ∧ riemannZeta w ≠ 0) ∧
      (∀ w ∈ closedBall p r, 1/2 < w.re ∧ (riemannZeta w = 0 → w = ρ))

private theorem all_zeros_fails : ¬ arena.Law allZeros := by
  intro h
  obtain ⟨p,ρ,r,_,_,hd,hr,hbound,_⟩ :=
    h (z₀ := 5) rfl (σ := 3) (δ := 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbound
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, -2, ?_⟩
  change riemannZeta 0 ≠ riemannZeta (-2)
  have hz : riemannZeta (-2) = 0 := by simpa using riemannZeta_neg_two_mul_nat_add_one 0
  rw [hz, riemannZeta_zero]
  norm_num

def family : Registration arena (type_of% @equal_radius_zero_disks) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equal_radius_zero_disks, allZeros, all_zeros_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual allZeros all_zeros_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@equal_radius_zero_disks) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks.equal_radius_zero_disks
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks "family"
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
    (fun _ _ z => riemannZeta z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
