import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.WolfordBinomialBiroot
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.WolfordBinomialBiroot
open LeanInformationAudit Filter Topology

noncomputable section
namespace Reg.D5.S3.ArithSums.WolfordBinomialBiroot

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p m => beta p.1 p.2.1 p.2.2 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (x c : ℝ) (n : ℕ), 0 < x → 0 < c → 1 ≤ n →
    (∀ m : ℕ, 0 < m → 0 < denominator x c n m) ∧
      Tendsto (R.readout () ⟨x, ⟨c, n⟩⟩) atTop (𝓝 (x ^ ((n : ℝ)⁻¹)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := by
    simpa [rejected, realize] using (h 1 1 2 (by norm_num) (by norm_num) (by norm_num)).2
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique h0 h1
  norm_num at heq

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1, ⟨1, 2⟩⟩, 0, 1, ?_⟩
    norm_num [actual, realize, beta, numerator, denominator, ceiling, Finset.sum_range_succ]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ArithSums.WolfordBinomialBiroot.quotient_information_unit
  realizationName := `Reg.D5.S3.ArithSums.WolfordBinomialBiroot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => beta p.1 p.2.1 p.2.2 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.WolfordBinomialBiroot
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.ArithSums.WolfordBinomialBiroot
