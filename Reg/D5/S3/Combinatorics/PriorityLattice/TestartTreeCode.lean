import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of native insertion and the fixed D formulas. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
open Equiv

namespace Insert

abbrev Params := Σ n : ℕ, Σ _ : Fin (n+1), Perm (Fin n)
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Fin (p.1+1)) (fun p => Fin (p.1+1))
noncomputable def actual : Realization signature := realize signature
  (fun _ p x => insertEquiv p.1 (p.2.1,p.2.2) x) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n (p : Fin (n+1)) (s : Perm (Fin n)) (v : Fin (n+1)),
    R.readout () ⟨n,p,s⟩ v = finSuccEquivLast.symm
      (s.optionCongr (swap none (finSuccEquiv n p) (finSuccEquivLast v)))
private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 (Equiv.refl _) (Fin.last 1)
  norm_num [rejected,realize] at hh
noncomputable def family : Registration arena (type_of% (@insert_apply)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@insert_apply, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨⟨1,0,Equiv.refl _⟩,0,1,?_⟩
    intro h
    change insertEquiv 1 (0,Equiv.refl _) 0 = insertEquiv 1 (0,Equiv.refl _) 1 at h
    exact (by decide : insertEquiv 1 (0,Equiv.refl _) 0 ≠
      insertEquiv 1 (0,Equiv.refl _) 1) h

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@insert_apply) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.PriorityLattice.TestartTreeCode.insert_apply.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode.Insert.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => insertEquiv p.1 (p.2.1,p.2.2) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }
end Insert

namespace Parent
abbrev Params := Σ n : ℕ, ParentCode n
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Fin p.1) (fun _ => Option ℕ)
noncomputable def actual : Realization signature := realize signature
  (fun _ p v => (((_root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.treeEquivCode p.1).symm p.2).val.parent v.succ).map Fin.val)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (t : ParentCode n) (v : Fin n),
    R.readout () ⟨n,t⟩ v = some (t v).val
private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (fun _ => 0) 0
  change (none : Option ℕ) = some 0 at hh
  cases hh
noncomputable def family : Registration arena (type_of% (@native_parent_code)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_parent_code, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    let t₀ : ParentCode 2 := fun _ => 0
    let t₁ : ParentCode 2 := fun v => ⟨v.val, by omega⟩
    refine ⟨⟨2,t₁⟩,0,1,?_⟩
    intro h
    change _ = _ at h
    simp only [actual, realize, native_parent_code] at h
    norm_num [t₀,t₁] at h

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_parent_code) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.PriorityLattice.TestartTreeCode.native_parent_code.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode.Parent.family
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
    (fun _ p v => (((_root_.D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.treeEquivCode p.1).symm p.2).val.parent v.succ).map Fin.val)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
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
end Parent

namespace Dual
abbrev Params := Σ n : ℕ, Perm (Fin n)
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Fin p.1) (fun _ => ℕ)
noncomputable def actual : Realization signature := realize signature
  (fun _ p i => (dual p.2 i).val+1) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (s : Perm (Fin n)) (i : Fin n),
    ((reflectPositions n i).val+1 = if i.val+1 < n then n-(i.val+1) else n) ∧
    R.readout () ⟨n,s⟩ i = n+1-((s (reflectPositions n i)).val+1)
private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (Equiv.refl (Fin 1)) 0).2
  norm_num [rejected,realize] at hh
noncomputable def family : Registration arena (type_of% (@dual_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dual_formula, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨⟨2,Equiv.refl _⟩,0,1,?_⟩
    intro h
    change (dual (Equiv.refl (Fin 2)) 0).val+1 = (dual (Equiv.refl (Fin 2)) 1).val+1 at h
    exact (by decide : (dual (Equiv.refl (Fin 2)) 0).val+1 ≠
      (dual (Equiv.refl (Fin 2)) 1).val+1) h

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dual_formula) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.PriorityLattice.TestartTreeCode.dual_formula.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode.Dual.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => (dual p.2 i).val+1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }
end Dual
end Reg.D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
