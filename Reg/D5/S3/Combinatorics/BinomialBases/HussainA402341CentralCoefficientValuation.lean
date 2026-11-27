import D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readouts of the two coefficient occurrences in the exact valuation law. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation

open _root_.D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation (result)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Finset
open scoped BigOperators

private abbrev central (n : ℕ) : ℕ :=
  ((∑ j ∈ range 16, (X : ℕ[X]) ^ j) ^ n).coeff (15 * n / 2)

private abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => central n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, Even n →
    0 < r.readout false () n ∧ padicValNat 2 (r.readout true () n) = (Nat.digits 2 (15 * n / 2)).sum

private noncomputable def erased (role : Bool) : Realization signature :=
  realize signature (fun j _ n =>
    if j = role then (if role then 2 else 0) else central n) (fun e => nomatch e)

private theorem erased_fails (role : Bool) : ¬ arena.Law (erased role) := by
  intro h
  have hzero := h 0 ⟨0, rfl⟩
  cases role
  · simpa [erased, realize] using hzero.1
  · have hval : padicValNat 2 2 = 0 := by simpa [erased, realize] using hzero.2
    have : padicValNat 2 2 = 1 := padicValNat.self (by decide)
    omega

noncomputable def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, erased false, erased_fails false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased i, ?_, rfl, erased_fails i⟩
      intro j hj
      funext p n
      simp [actual, erased, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change central 0 ≠ central 2
    intro h
    have hzero := (result 0 ⟨0, rfl⟩).2
    have htwo := (result 2 ⟨1, rfl⟩).2
    change padicValNat 2 (central 0) = _ at hzero
    change padicValNat 2 (central 2) = _ at htwo
    rw [h, htwo] at hzero
    exact (by decide : (Nat.digits 2 (15 * 2 / 2)).sum ≠ (Nat.digits 2 (15 * 0 / 2)).sum) hzero

noncomputable def audit :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@result) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => central n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation

end
