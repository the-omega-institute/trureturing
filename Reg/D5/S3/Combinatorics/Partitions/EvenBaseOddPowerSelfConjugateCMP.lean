import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP

/-! Source audit of the power used to select diagrams at each exponent. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP
open _root_.D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP (IsCMP IsMAry)

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m e => m ^ e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law observed := ∀ (m : ℕ), 2 ≤ m → Even m →
    IsLeast {e : ℕ | Odd e ∧ ∃ μ : YoungDiagram,
      μ.card = observed.readout () m e ∧ IsCMP m μ ∧ μ.transpose = μ} (m + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let μ : YoungDiagram := ⊥
  have hself : μ.transpose = μ := by
    apply SetLike.ext
    intro p
    simp [μ, YoungDiagram.mem_transpose, YoungDiagram.notMem_bot]
  have hmary : IsMAry 2 μ := by
    intro i hi
    exact (YoungDiagram.notMem_bot (i, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr hi)).elim
  have hcmp : IsCMP 2 μ := ⟨hmary, hself ▸ hmary⟩
  have hbad : 2 + 1 ≤ (1 : ℕ) :=
    (h 2 (by decide) (by decide)).2 ⟨odd_one, μ, rfl, hcmp, hself⟩
  omega

def familyRegistration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro role
    cases role
    exact ⟨2, 0, 1, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.Combinatorics.Partitions.EvenBaseOddPowerSelfConjugateCMP
