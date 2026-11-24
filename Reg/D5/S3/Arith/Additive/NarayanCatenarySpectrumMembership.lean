import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership

/-! Source audit of the represented value used for the predecessor and least thresholds. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership
open _root_.D5.S3.Arith.Additive.NarayanExpandedGeneratorDeltaRefutation (Z)

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => witness p.1 p.2.1 p.2.2 k) (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun anchor => nomatch anchor)

abbrev arena : Arena where
  signature := signature
  Law observed := ∀ (a h d k : ℕ), 0 < d → a.Coprime d → 1 < k → k < a → 1 < h →
    let g := generators a h d k
    let t := ceilParameter a k
    let n := observed.readout () ⟨a, h, d⟩ k
    let N := t + h + d
    WitnessCheckpoint a h d k ∧
    (∀ z w : Z g n, Chain g n (N - 1) z w ↔
      (Low h d t z.val ∧ Low h d t w.val) ∨ (High a t z.val ∧ High a t w.val)) ∧
    IsLeast {B | ∀ z w : Z g n, Chain g n B z w} N ∧ N ∈ catenarySpectrum g

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let z : Z (generators 3 2 1 2) 0 := ⟨0, by rfl⟩
  have chain : Chain (generators 3 2 1 2) 0 3 z z := Relation.ReflTransGen.refl
  rcases ((law 3 2 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide)).2.1 z z).mp chain with hlo | hhi
  · have h := hlo.1.1
    change 0 = 1 at h
    contradiction
  · have hc := hhi.1.1
    change 0 = 4 at hc
    contradiction

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
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    cases role
    exact ⟨⟨5, 2, 1⟩, 2, 4, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership.familyRegistration
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
    owner := `D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership
