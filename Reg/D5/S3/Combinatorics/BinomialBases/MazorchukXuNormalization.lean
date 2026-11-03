import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalization
import Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies

/-! Exact source readouts for the all-rank coordinate count identity. -/
set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalization
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MazorchukXu

abbrev signature := Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies.signature
noncomputable def actual : Realization signature := realize signature
  (fun _ n k => count n k) (fun e => nomatch e)
noncomputable def rejected : Realization signature := realize signature
  (fun _ n k => count n k + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n i : ℕ}, i ≤ n + 1 → R.readout () n (n + 1 - i) =
    ∑ k ∈ Finset.range (2 * i + 1), patternCoefficient i k * (n + 1 - i).choose k

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hx := h (n := 0) (i := 0) (by omega)
  have ht := count_eq_binomial_sum (n := 0) (i := 0) (by omega)
  change count 0 (0 + 1 - 0) + 1 = _ at hx
  omega

noncomputable def family_registration : Registration arena (type_of% (@count_eq_binomial_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_eq_binomial_sum, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies.family_registration.dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@count_eq_binomial_sum) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.MazorchukXu.count_eq_binomial_sum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalization.family_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => count n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }


end Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalization
