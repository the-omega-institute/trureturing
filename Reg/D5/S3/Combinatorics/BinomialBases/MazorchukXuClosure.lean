import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
import Reg.Support.SingleDependentReadout

/-! Source-bound family registrations for the finite counting interfaces. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MazorchukXu

namespace Triangle

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => Prop)

noncomputable def actual : Realization signature := realize signature
  (fun _ p a => (a, p.2) ∈ triangle p.1) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n a b : ℕ}, R.readout () ⟨n, b⟩ a ↔ a ≤ b ∧ b ≤ n

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  exact (h (n := 0) (a := 0) (b := 0)).mpr ⟨le_rfl, le_rfl⟩

noncomputable def family : Registration arena (type_of% (@mem_triangle)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_triangle, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
    intro heq
    have htrue : actual.readout role ⟨0, 0⟩ 0 := by
      change (0, 0) ∈ triangle 0
      exact mem_triangle.mpr ⟨le_rfl, le_rfl⟩
    have hfalse : ¬ actual.readout role ⟨0, 0⟩ 1 := by
      change (1, 0) ∉ triangle 0
      simp [mem_triangle]
    exact hfalse (Eq.mp heq htrue)

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_triangle) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.MazorchukXu.mem_triangle.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure.Triangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a => (a, p.2) ∈ triangle p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Triangle
namespace StarRules

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Finset (ℕ × ℕ)) (fun _ => Prop)

noncomputable def actual : Realization signature := realize signature
  (fun _ _ Y => Star Y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Finset (ℕ × ℕ)}, (∀ {a b}, (a, b) ∈ Y → a ≤ b) →
    (R.readout () () Y ↔ Rules (pointEdges Y))

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have horder : ∀ {a b : ℕ}, (a, b) ∈ (∅ : Finset (ℕ × ℕ)) → a ≤ b := by simp
  have hstar : Star ∅ := by intro a b c d e f hab; simp at hab
  exact (h horder).mpr ((star_iff_rules horder).mp hstar)

noncomputable def family : Registration arena (type_of% (@star_iff_rules)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@star_iff_rules, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    classical
    intro role
    refine ⟨(), ∅, {(0, 0), (0, 1)}, ?_⟩
    intro heq
    have hstar : Star ∅ := by intro a b c d e f hab; simp at hab
    have hbad : Star {(0, 0), (0, 1)} := Eq.mp heq hstar
    have hx := (hbad 0 0 0 1 0 1 (by simp) (by simp) (by simp)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).2 (by omega)
    norm_num at hx

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@star_iff_rules) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.MazorchukXu.star_iff_rules.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure.StarRules.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Y => Star Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end StarRules

namespace FamilyMembership

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun _ => Finset (ℕ × ℕ)) (fun _ => Prop)

noncomputable def actual : Realization signature := realize signature
  (fun _ p Y => Y ∈ family p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k : ℕ} {Y : Finset (ℕ × ℕ)},
    R.readout () ⟨n, k⟩ Y ↔
      Y ⊆ triangle n ∧ Rules (pointEdges Y) ∧ firstColumnCard Y = k

private theorem empty_member : (∅ : Finset (ℕ × ℕ)) ∈ family 0 0 := by
  classical
  simp [family, D5.S3.Combinatorics.MazorchukXu.Star, firstColumnCard]

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  exact (h (n := 0) (k := 0) (Y := ∅)).mpr (mem_family_iff.mp empty_member)

noncomputable def family_registration : Registration arena (type_of% (@mem_family_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_family_iff, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    classical
    intro role
    refine ⟨⟨0, 0⟩, ∅, {(0, 0)}, ?_⟩
    intro heq
    have hbad : ({(0, 0)} : Finset (ℕ × ℕ)) ∈ family 0 0 := Eq.mp heq empty_member
    have hx := (mem_family_iff.mp hbad).2.2
    norm_num [firstColumnCard] at hx

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_family_iff) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.MazorchukXu.mem_family_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure.FamilyMembership.family_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Y => Y ∈ family p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end FamilyMembership
end Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
