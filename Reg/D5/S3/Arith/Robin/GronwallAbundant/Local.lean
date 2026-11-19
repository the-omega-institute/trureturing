import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GronwallAbundant.Local
import Reg.Support.SingleDependentReadout

set_option linter.style.longLine false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.GronwallAbundant.Local
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.GronwallAbundant
open Filter
open scoped BigOperators

namespace ga1_local_criterion
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Prop) (fun _ => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ↔ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 0 < N → q ∈ N.primeFactors → 4 ≤ N / q →
    R.readout () () (gronwallQ (N / q) ≤ gronwallQ N)
      (primeDeletionSum N q * (Real.log (Real.log N) - Real.log (Real.log (N / q : ℕ))) ≤
        Real.log (Real.log N))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 8) (q := 2) (by norm_num) (by norm_num [Nat.mem_primeFactors]) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), False, True, ?_⟩
  intro he
  have hf : True ↔ False := Eq.mp (congrFun he False) Iff.rfl
  exact hf.mp trivial
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_local_criterion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_local_criterion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_local_criterion) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Local.ga1_local_criterion.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Local.ga1_local_criterion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ↔ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Local
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ga1_local_criterion

namespace prime_deletion_log_gap
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 0 < N → q ∈ N.primeFactors → 4 ≤ N / q →
    R.readout () () (Real.log q / Real.log N)
      (Real.log (Real.log N) - Real.log (Real.log (N / q : ℕ)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 8) (q := 2) (by norm_num) (by norm_num [Nat.mem_primeFactors]) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.prime_deletion_log_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.prime_deletion_log_gap, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.prime_deletion_log_gap) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Local.prime_deletion_log_gap.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Local.prime_deletion_log_gap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Local
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end prime_deletion_log_gap

end Reg.D5.S3.Arith.Robin.GronwallAbundant.Local
