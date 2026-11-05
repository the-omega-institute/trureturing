import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraCoreRestore
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Complete actual array reconstruction as a dependent source family. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraCoreRestore
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreContract MiuraCoreRestore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

structure Parameter where
  m : ℕ
  n : ℕ
  hm : 0 < m
  j : Fin n

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter
    (fun p => {h : Cell p.m p.n → ℤ // IsHeight h ∧ frozenColumn h p.j})
    (fun p => Cell p.m p.n → ℤ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) p x =>
    restoreColumn (contractAt x.val p.hm p.j x.property.2) p.j
      x.property.2.1 x.property.2.2.1 (frozenSlope x.val p.hm p.j x.property.2))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j),
    R.readout () ⟨m, n, hm, j⟩ ⟨h, hh, hj⟩ = h

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) p x v => actual.readout () p x v + 1)
    (fun e => nomatch e)

abbrev lineParameter : Parameter := ⟨1, 3, by decide, ⟨1, by decide⟩⟩

def lineState (c : ℤ) : signature.State lineParameter := by
  refine ⟨fun v => (v.2.val : ℤ) + c, ?_, ?_⟩
  · intro p q hpq
    simp only [adj, gdist] at hpq
    have hp : p.1.val = 0 := by have hlt : p.1.val < 1 := p.1.isLt; omega
    have hq : q.1.val = 0 := by have hlt : q.1.val < 1 := q.1.isLt; omega
    dsimp
    rw [add_sub_add_right_eq_sub]
    simpa only [hp, hq, Int.cast_zero, Int.sub_self, Int.natAbs_zero,
      zero_add, Int.natCast_natAbs] using hpq
  · refine ⟨by decide, by decide, ?_⟩
    intro i
    norm_num
    ring

theorem actual_law : arena.Law actual := restoreColumn_contractAt

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro hb
  have he := hb (lineState 0).val (lineState 0).property.1 lineParameter.hm
    lineParameter.j (lineState 0).property.2
  have ha := actual_law (lineState 0).val (lineState 0).property.1 lineParameter.hm
    lineParameter.j (lineState 0).property.2
  have hev := congrFun he ((0 : Fin 1), (0 : Fin 3))
  have hav := congrFun ha ((0 : Fin 1), (0 : Fin 3))
  change actual.readout () lineParameter (lineState 0) ((0 : Fin 1), (0 : Fin 3)) + 1 = _ at hev
  change actual.readout () lineParameter (lineState 0) ((0 : Fin 1), (0 : Fin 3)) = _ at hav
  omega

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨lineParameter, lineState 0, lineState 1, ?_⟩
  have h0 := actual_law (lineState 0).val (lineState 0).property.1 lineParameter.hm
    lineParameter.j (lineState 0).property.2
  have h1 := actual_law (lineState 1).val (lineState 1).property.1 lineParameter.hm
    lineParameter.j (lineState 1).property.2
  intro he
  have hev := congrFun he ((0 : Fin 1), (0 : Fin 3))
  rw [h0, h1] at hev
  norm_num [lineState] at hev

def registration : Registration arena (type_of% (@restoreColumn_contractAt)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@restoreColumn_contractAt)
    (type_of% (realize signature (fun (_ : Unit) p x =>
      restoreColumn (contractAt x.val p.hm p.j x.property.2) p.j
        x.property.2.1 x.property.2.2.1 (frozenSlope x.val p.hm p.j x.property.2))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraCoreRestore.restoreColumn_contractAt.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraCoreRestore.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) p x =>
      restoreColumn (contractAt x.val p.hm p.j x.property.2) p.j
        x.property.2.1 x.property.2.2.1 (frozenSlope x.val p.hm p.j x.property.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.MiuraCoreRestore
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraCoreRestore
