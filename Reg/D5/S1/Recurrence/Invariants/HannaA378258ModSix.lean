import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Invariants.HannaA378258ModSix
import Reg.Support.DependentFamily

/-! # Source-family audit for Hanna's modulo-six theorem -/

namespace Reg.D5.S1.Recurrence.Invariants.HannaA378258ModSix
open PowerSeries
open _root_.D5.S1.Recurrence.Invariants.HannaA378258ModSix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := PowerSeries ℚ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ A n => coeff n A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∃ A, _root_.D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.IsGF A) ∧
      ∀ A, _root_.D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.IsGF A →
        ∀ n : ℕ, 1 < n → ∃ z : ℤ, r.readout () A n = z ∧ z % 6 ≠ 1 ∧ z % 6 ≠ 5

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA⟩ := h.1
  obtain ⟨z, hz, hne, _⟩ := h.2 A hA 2 (by omega)
  change (1 : ℚ) = (z : ℚ) at hz
  have he : z = 1 := by exact_mod_cast hz.symm
  exact hne (by rw [he]; norm_num)

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨A, hA⟩ := _root_.D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.result.1
    obtain ⟨z₂, hz₂, hp₂⟩ :=
      _root_.D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.result.2 A hA 2 (by omega)
    obtain ⟨z₃, hz₃, hp₃⟩ :=
      _root_.D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.result.2 A hA 3 (by omega)
    have ho₂ : Odd z₂ := hp₂.mpr ⟨1, by norm_num⟩
    have ho₃ : ¬ Odd z₃ := by
      intro h
      obtain ⟨k, hk⟩ := hp₃.mp h
      cases k with
      | zero => norm_num at hk
      | succ k => rw [pow_succ] at hk; omega
    refine ⟨A, 2, 3, ?_⟩
    change coeff 2 A ≠ coeff 3 A
    intro he
    rw [hz₂, hz₃] at he
    have hz : z₂ = z₃ := by exact_mod_cast he
    exact ho₃ (hz ▸ ho₂)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.Invariants.HannaA378258ModSix.unit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.HannaA378258ModSix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A n => coeff n A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.HannaA378258ModSix
    definition := some {
      owner := `D5.S1.Recurrence.Invariants.HannaA378258ModSix
      name := `D5.S1.Recurrence.Invariants.HannaA378258ModSix.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S1.Recurrence.Invariants.HannaA378258ModSix
