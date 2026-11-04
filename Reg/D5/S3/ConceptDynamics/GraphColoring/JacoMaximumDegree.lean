import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
namespace Reg.D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open _root_.D5.S1.Words.Powers.ZeckendorfDeletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
private instance (n : ℕ) : DecidableRel (jaco n).Adj := by
  intro a b
  simp only [jaco, _root_.D5.S0.Certificates.JacoExponentialDominationRefutation.Adj]
  infer_instance
abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
private theorem depends : ObservationalDependence sig actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; omega⟩

namespace Target0
abbrev arena : Arena where
  signature := sig
  Law R := ∀ (n : ℕ) (v : Vertex n), (jaco n).degree v = min v.1 (R.readout () () n - beattyOut v.1)
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h2 := h 2 (⟨1, by decide⟩ : Vertex 2)
  rw [degree_formula] at h2
  have hb := beatty_bounds 1 (by decide)
  change min 1 (2 - beattyOut 1) = min 1 (0 - beattyOut 1) at h2
  omega
def evidence : Registration arena (type_of% @degree_formula) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨degree_formula, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@degree_formula) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree.degree_formula.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree.Target0.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end Target0

namespace Target1
abbrev arena : Arena where
  signature := sig
  Law R := ∀ n : ℕ, 1 ≤ n → (jaco n).maxDegree = deleteLeast (R.readout () () n)
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h2 := h 2 (by decide)
  rw [max_degree_eq_deletion 2 (by decide)] at h2
  have hd2 : deleteLeast 2 = 1 := by decide +kernel
  have hd0 : deleteLeast 0 = 0 := by decide +kernel
  change deleteLeast 2 = deleteLeast 0 at h2
  rw [hd2, hd0] at h2
  omega
def evidence : Registration arena (type_of% @max_degree_eq_deletion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨max_degree_eq_deletion, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@max_degree_eq_deletion) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree.max_degree_eq_deletion.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree.Target1.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
end Target1

end

end Reg.D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
