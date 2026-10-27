import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PriorityLattice.TestartTraversal
import Reg.Support.SingleDependentReadout

/-! Full-telescope source audit of the fixed native bijection endpoint. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.PriorityLattice.TestartTraversal.Endpoint
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
open _root_.D5.S3.Combinatorics.PriorityLattice.TestartTraversal
open _root_.D5.S3.Combinatorics.PriorityLattice
open Equiv

abbrev Params := Σ _ : ℕ, ℕ
abbrev signature := Reg.Support.SingleDependentReadout.signature Params
  (fun p => NativeTree (p.1+p.2-1)) (fun p => Perm (Fin (p.1+p.2-1)))
noncomputable def actual : Realization signature := realize signature
  (fun _ _ t => F t) (fun e => nomatch e)
noncomputable def rejected : Realization signature := realize signature
  (fun _ _ t => (F t).trans Fin.revPerm) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
    (∀ t : NativeTree (a+b-1), ForwardSpec t (R.readout () ⟨a,b⟩ t)) ∧
    (∀ s : Perm (Fin (a+b-1)), ReverseSpec s (H s)) ∧
    (∀ t : TreeClass a b, ∀ i, i < F t.val i ↔ i.val+1 < b) ∧
    (∀ s : PermClass a b, ∀ v, Internal (H s.val) v ↔ v.val < a) ∧
    (∀ t : TreeClass a b, H (F t.val) = t.val) ∧
    (∀ s : PermClass a b, F (H s.val) = s.val)

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  let t : NativeTree 2 := (IntervalForestBasic.treeEquivCode 2).symm (fun _ => 0)
  have hh := ((h 1 2 (by omega) (by omega)).1 t).2.2.2.2.1
  change (F t).trans Fin.revPerm = F t at hh
  have hv := congrArg (fun e => e ((F t).symm 0)) hh
  have hn := congrArg Fin.val hv
  norm_num [Equiv.trans_apply,Fin.revPerm] at hn

noncomputable def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    let c₀ : ParentCode 2 := fun _ => 0
    let c₁ : ParentCode 2 := fun v => ⟨v.val, by omega⟩
    let t₀ := (IntervalForestBasic.treeEquivCode 2).symm c₀
    let t₁ := (IntervalForestBasic.treeEquivCode 2).symm c₁
    refine ⟨⟨1,2⟩,t₀,t₁,?_⟩
    intro he
    change F t₀ = F t₁ at he
    have hn : nativeEquiv 2 t₀ = nativeEquiv 2 t₁ := by
      ext i
      have hx := congrArg (fun e => e ((reflectPositions 2).symm i)) he
      have hh := congrArg Fin.rev hx
      have hf : nativeEquiv 2 t₀ i = nativeEquiv 2 t₁ i := by
        simpa [F,dual,Equiv.trans_apply,Fin.revPerm] using hh
      exact congrArg Fin.val hf
    have ht := (nativeEquiv 2).injective hn
    have hc := congrArg (IntervalForestBasic.treeEquivCode 2) ht
    simp only [t₀,t₁,Equiv.apply_symm_apply] at hc
    have hv := congrArg (fun c : ParentCode 2 => (c 1).val) hc
    norm_num [c₀,c₁] at hv

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.PriorityLattice.TestartTraversal.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.TestartTraversal.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => F t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PriorityLattice.TestartTraversal
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.PriorityLattice.TestartTraversal.Endpoint
