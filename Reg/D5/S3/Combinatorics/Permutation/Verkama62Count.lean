import Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Count
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

abbrev signature : Signature where
  Params := Σ n : ℕ, Equiv.Perm (Fin n)
  State p := Finset (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p S => inversions p.2 S)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

def sampleDouble : Double pattern {0,1,2,4} where
  u := 3
  v := 5
  x := 4
  y := 1
  hx := by decide
  hy := by decide
  hu := by decide
  hv := by decide
  hxy := by decide
  hux := by decide
  hxv := by decide
  hvy := by decide
  hyu := by decide
  old_left := by intro i hi hne; fin_cases i <;> simp_all
  old_below := by intro i hi hne; fin_cases i <;> norm_num [pattern] at *

theorem observation_varies : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3,rev3⟩, ∅, Finset.univ, ?_⟩
  change inversions rev3 ∅ ≠ inversions rev3 Finset.univ
  decide

namespace Insert
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (x : Fin n), x ∉ S → R.readout () ⟨n,π⟩ (insert x S) = inversions π S + (neighbours π S x).card
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 3 rev3 {0} 1 (by decide)
  change 0 = inversions rev3 {0} + (neighbours rev3 {0} 1).card at he
  have hright : inversions rev3 {0} + (neighbours rev3 {0} 1).card = 1 := by decide
  omega
def family : Registration arena (type_of% (@inversions_insert)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inversions_insert, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@inversions_insert) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.inversions_insert.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Count.Insert.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p S => inversions p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Count
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Insert

namespace Double
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)} (e : Double π S), R.readout () ⟨n,π⟩ (insert e.u (insert e.v S)) = inversions π S + 3
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 6 pattern {0,1,2,4} sampleDouble
  change 0 = inversions pattern {0,1,2,4} + 3 at he
  omega
def family : Registration arena (type_of% (@Double.inversion_increment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Double.inversion_increment, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Double.inversion_increment) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.Double.inversion_increment.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Count.Double.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p S => inversions p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Count
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Double
end Reg.D5.S3.Combinatorics.Permutation.Verkama62Count
