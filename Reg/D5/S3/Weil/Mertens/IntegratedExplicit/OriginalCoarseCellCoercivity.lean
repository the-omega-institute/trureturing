import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalCoarseCellCoercivity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit for the full arbitrary-beta finite-cell endpoint. -/
noncomputable section
universe u
open MeasureTheory Set Filter
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.OriginalCoarseCellCoercivity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The entire original grid and finite-family telescope is preserved. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (D β : ℝ) (hD : 0 < D) (hβ : 0 < β),
    ∃ N : ℕ, 1 ≤ N ∧ ∃ g : ℕ → ℝ,
      g 0 = 0 ∧ g N = D ∧ StrictMono g ∧
      ∀ (I : Type u) (_ : Fintype I) (x : I → ℝ) (a : I → ℂ),
        (∀ i, x i ∈ Icc 0 D) → (∑ i, a i = 0) →
        (∀ k < N, (∫ u in g k..g (k + 1), «prefix» x a u) = 0) →
        β * (∫ u : ℝ, ‖«prefix» x a u‖^2) ≤ R.readout () () (quadratic x a P)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨N, hN, g, hzero, hend, hmono, hall⟩ := h 1 1 (by norm_num) (by norm_num)
  have hbad := hall (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by simp)
    (by intro k hk; simp [«prefix»])
  norm_num [rejected, realize, «prefix»] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩

def family : Registration arena.{u} (type_of% @original_coarse_cell_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_coarse_cell_coercivity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_coarse_cell_coercivity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.original_coarse_cell_coercivity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.OriginalCoarseCellCoercivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.OriginalCoarseCellCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.OriginalCoarseCellCoercivity
