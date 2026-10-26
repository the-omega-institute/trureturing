import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies
import Reg.Support.SingleDependentReadout

/-! Source-bound family registrations for the finite counting interfaces. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MazorchukXu

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => ℕ) (fun _ => ℕ)

noncomputable def actual : Realization signature := realize signature
  (fun _ n k => count n k) (fun e => nomatch e)

noncomputable def rejected : Realization signature := realize signature
  (fun _ n k => count n k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, R.readout () n k = (edgeFamily n k).card

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 0 0
  have ht := count_eq_edgeFamily_card 0 0
  change count 0 0 + 1 = (edgeFamily 0 0).card at hx
  omega

noncomputable def family_registration : Registration arena (type_of% (@count_eq_edgeFamily_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_eq_edgeFamily_card, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    classical
    intro role
    refine ⟨0, 0, 2, ?_⟩
    change count 0 0 ≠ count 0 2
    have htriangle : triangle 0 = {(0, 0)} := by
      ext ⟨a, b⟩
      simp only [mem_triangle, Finset.mem_singleton, Prod.mk.injEq]
      omega
    norm_num [count, family, htriangle, D5.S3.Combinatorics.MazorchukXu.Star,
      firstColumnCard, Finset.powerset_insert]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@count_eq_edgeFamily_card) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.MazorchukXu.count_eq_edgeFamily_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies.family_registration
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
    owner := `D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies
