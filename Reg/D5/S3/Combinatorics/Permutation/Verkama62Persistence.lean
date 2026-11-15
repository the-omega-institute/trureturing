import Reg.D5.S3.Combinatorics.Permutation.Verkama62Local

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Persistence
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open _root_.D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Local
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Count (sampleDouble)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)},
    Fresh π S → ¬ R.readout () n π → IsEmpty (Double π S) ∧
      ∀ x, x ∉ S → (neighbours π S x).card = 2 → IsEmpty (Double π (insert x S))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (@h 6 pattern {0,1,2,4} sampleFresh (by exact id)).1
  exact he.false sampleDouble

def family : Registration arena (type_of% (@Fresh.no_cheap_double)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Fresh.no_cheap_double, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Fresh.no_cheap_double) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.Fresh.no_cheap_double.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Persistence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => Contains pattern π) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Persistence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Singleton
private def witness : Equiv.Perm (Fin 5) where
  toFun := ![2,3,0,1,4]
  invFun := ![2,3,0,1,4]
  left_inv := by decide
  right_inv := by decide
private def fresh : Fresh witness {0,1,2,3} where
  a := 0
  b := 1
  c := 2
  d := 3
  ha := by decide
  hb := by decide
  hc := by decide
  hd := by decide
  hab := by decide
  hbc := by decide
  hcd := by decide
  hval₁ := by decide
  hval₂ := by decide
  hval₃ := by decide
  rightmost := by intro i hi; fin_cases i <;> simp_all
  topmost := by intro i hi; fin_cases i <;> norm_num [witness] at *
  right := by intro i hi; fin_cases i <;> simp_all
  top := by intro i hi; fin_cases i <;> norm_num [witness] at *
private theorem no_terminal : ¬ Nonempty (Terminal witness (insert 4 {0,1,2,3})) := by
  rintro ⟨t⟩
  have hr := t.rightmost 4 (by decide)
  have ht := t.topmost 4 (by decide)
  have hd : t.d = 4 := Fin.ext (by have := t.d.isLt; omega)
  have hbval : witness t.b = 4 := Fin.ext (by
    have := (witness t.b).isLt
    change 4 ≤ (witness t.b).val at ht
    omega)
  have hb : t.b = 4 := witness.injective (hbval.trans (by decide))
  have hbd := t.hbc.trans t.hcd
  rw [hb,hd] at hbd
  exact (lt_irrefl _ hbd)

abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : Equiv.Perm (Fin n), Finset (Fin n)
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => (neighbours p.2.1 p.2.2 x).card) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)},
    Fresh π S → ∀ x : Fin n, x ∉ S → R.readout () ⟨n,π,S⟩ x = 2 →
      Nonempty (Terminal π (insert x S))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact no_terminal (@h 5 witness {0,1,2,3} fresh 4 (by decide) rfl)
def family : Registration arena (type_of% (@Fresh.singleton_terminal)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Fresh.singleton_terminal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨5,witness,{0,1,2,3}⟩, 0, 4, ?_⟩
    change (neighbours witness {0,1,2,3} 0).card ≠ (neighbours witness {0,1,2,3} 4).card
    decide

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Fresh.singleton_terminal) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.Fresh.singleton_terminal.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Persistence.Singleton.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => (neighbours p.2.1 p.2.2 x).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Persistence
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Singleton
end Reg.D5.S3.Combinatorics.Permutation.Verkama62Persistence
