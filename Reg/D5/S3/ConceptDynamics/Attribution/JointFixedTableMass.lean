import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.JointFixedTableMass
import Reg.Support.DependentFamily

/-! The second readout event is required to attain the prescribed second mass. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.JointFixedTableMass

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.JointFixedTableMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe g x y

noncomputable section

abbrev signature : Signature where
  Params := Type y
  State Y := Y → Flags
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ Y := Y → Flags
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{y} :=
  realize signature (fun _ _ flag => flag) (fun e => nomatch e)

def emptyFlags : Realization signature.{y} :=
  realize signature (fun _ _ _ _ => (false, false)) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature.{y}
  Law R :=
    ∀ {G : Type g} {X : Type x} {Y : Type y}
      [Monoid G] [MulAction G Y] [Fintype X] [Fintype Y] (P : X → Y → ℝ),
      (∀ x y, 0 ≤ P x y) → (∀ x, ∑ y, P x y = 1) →
      (∀ (g : G) x y, P x (g • y) = P x y) →
      ∀ (flag : Y → Flags), (∀ (g : G) y, flag (g • y) = flag y) →
      ∀ (m₁ m₂ iMin uMin : ℝ),
      (∀ x, m₁ ≤ rowMass P flag x first) →
      (∀ x, m₂ ≤ rowMass P flag x second) →
      (∀ x, iMin ≤ rowMass P flag x both) →
      (∀ x, uMin ≤ rowMass P flag x either) →
      (∃ x, rowMass P flag x first = m₁) →
      (∃ x, rowMass P flag x second = m₂) →
      (∃ x, rowMass P flag x both = iMin) →
      (∃ x, rowMass P flag x either = uMin) →
      ((∃ w : (X → Y) → ℝ,
        (∀ t, 0 ≤ w t) ∧ (∑ t, w t) = 1 ∧
        (∀ (g : G) t, w (fun x => g • t x) = w t) ∧
        (∀ x y, (∑ t : X → Y, if t x = y then w t else 0) = P x y) ∧
        tableMass w flag first = m₁ ∧ tableMass w (R.readout () Y flag) second = m₂) ↔
      m₁ + m₂ ≤ iMin + uMin)

@[instance_reducible] private def trivialAction (G Y : Type*) [Monoid G] : MulAction G Y where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private theorem empty_flags_fail : ¬ arena.{g,x,y}.Law emptyFlags := by
  classical
  intro law
  let G := PUnit.{g+1}
  let X := PUnit.{x+1}
  let Y := PUnit.{y+1}
  let _ : Monoid G := {
    mul := fun a _ => a
    one := PUnit.unit
    mul_assoc := fun _ _ _ => rfl
    one_mul := fun a => Subsingleton.elim _ a
    mul_one := fun _ => rfl }
  let _ : MulAction G Y := trivialAction G Y
  let _ : Fintype X := inferInstanceAs (Fintype PUnit)
  let _ : Fintype Y := inferInstanceAs (Fintype PUnit)
  let P (_ : X) (_ : Y) : ℝ := 1
  let flag (_ : Y) : Flags := (true, true)
  have mass (x : X) (U : Finset Flags) (member : (true, true) ∈ U) :
      rowMass P flag x U = 1 := by
    simp [rowMass, flag, P, member]
  have a (x : X) : rowMass P flag x first = 1 := mass x first (by decide)
  have b (x : X) : rowMass P flag x second = 1 := mass x second (by decide)
  have i (x : X) : rowMass P flag x both = 1 := mass x both (by decide)
  have u (x : X) : rowMass P flag x either = 1 := mass x either (by decide)
  obtain ⟨w, _, _, _, _, _, impossible⟩ :=
    (law (G := G) P (fun _ _ => zero_le_one) (fun _ => by simp [P]) (fun _ _ _ => rfl)
      flag (fun _ _ => rfl) 1 1 1 1
      (fun x => (a x).symm.le) (fun x => (b x).symm.le)
      (fun x => (i x).symm.le) (fun x => (u x).symm.le)
      ⟨PUnit.unit, a _⟩ ⟨PUnit.unit, b _⟩ ⟨PUnit.unit, i _⟩ ⟨PUnit.unit, u _⟩).mpr le_rfl
  change tableMass w (fun _ : Y => (false, false)) second = 1 at impossible
  have absent : (false, false) ∉ second := by decide
  have noTable (t : X → Y) : ¬ ∀ x : X, (false, false) ∈ second :=
    fun h => absent (h PUnit.unit)
  simp only [tableMass, filter_eq_empty_iff.mpr (fun t _ => noTable t), sum_empty, zero_ne_one] at impossible

def family : Registration arena.{g,x,y} (type_of% (@two_table_masses_attain_row_minima_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_table_masses_attain_row_minima_iff, emptyFlags, empty_flags_fail⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨emptyFlags, ?_, rfl, empty_flags_fail⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{y+1}, (fun _ => (true, true)), (fun _ => (false, false)), ?_⟩
    intro eq
    have distinct := congrFun eq PUnit.unit
    exact Bool.noConfusion (congrArg Prod.fst distinct)


def jointRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_table_masses_attain_row_minima_iff) (Realization signature.{y}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.JointFixedTableMass.secondFlag
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.JointFixedTableMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{g,x,y}⟩
  objectArena := .source ⟨arena.{g,x,y}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{g,x,y} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ flag => flag) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.JointFixedTableMass
    definition := none
    coordinates := #[2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg",
          "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
        stateBinder := 11
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.JointFixedTableMass
