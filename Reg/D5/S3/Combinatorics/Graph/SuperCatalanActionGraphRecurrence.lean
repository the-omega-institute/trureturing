import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence

open _root_.D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role _ n => Bool.rec (S 0 (n + 1))
    (∑ r ∈ Finset.range (n + 1), (2 / 2 ^ r : ℚ) *
      ∑ v ∈ Finset.range (n + 1), (K r v n : ℚ)) role)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout false () n = R.readout true () n

def intervention (role : Bool) : Realization signature := realize signature
  (fun j p n => if j = role then actual.readout j p n + 1 else actual.readout j p n)
  (fun e => nomatch e)

theorem intervention_rejected (role : Bool) : ¬ arena.Law (intervention role) := by
  intro h
  have equality := h 0
  have positive := result 0
  cases role <;> simp [intervention, realize, actual] at equality positive <;> linarith

def familyRegistration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, intervention false, intervention_rejected false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_rejected i⟩
      intro j hji
      funext p n
      simp [intervention, realize, hji]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have left0 : S 0 (0 + 1) = 2 := by norm_num [S, Nat.factorial]
    have left1 : S 0 (1 + 1) = 6 := by norm_num [S, Nat.factorial]
    cases i
    · change S 0 (0 + 1) ≠ S 0 (1 + 1)
      rw [left0, left1]
      norm_num
    · change (∑ r ∈ Finset.range (0 + 1), (2 / 2 ^ r : ℚ) *
        ∑ v ∈ Finset.range (0 + 1), (K r v 0 : ℚ)) ≠
        (∑ r ∈ Finset.range (1 + 1), (2 / 2 ^ r : ℚ) *
        ∑ v ∈ Finset.range (1 + 1), (K r v 1 : ℚ))
      rw [← result 0, ← result 1, left0, left1]
      norm_num

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence.result)
    (type_of% (realize signature
      (fun role _ n => Bool.rec (S 0 (n + 1))
        (∑ r ∈ Finset.range (n + 1), (2 / 2 ^ r : ℚ) *
          ∑ v ∈ Finset.range (n + 1), (K r v n : ℚ)) role)
      (fun e => nomatch e))) (type_of% (ℕ)) Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun role _ n => Bool.rec (S 0 (n + 1))
      (∑ r ∈ Finset.range (n + 1), (2 / 2 ^ r : ℚ) *
        ∑ v ∈ Finset.range (n + 1), (K r v n : ℚ)) role)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence
    definition := some {
      owner := `D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence
      name := `D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨familyRegistration⟩⟩
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence
