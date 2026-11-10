import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverCollapse

/- UNCOMPILED source-operand registration. Only the first RHS disjunct
   `i.val+1 = 2` of the unchanged `@criticalA_formula.{u}` is observed.
   The original q is the sole coordinate; the original i is the state operand.
   sourceSelection stays none pending actual raw compiled resolution,
   reconstruction, field/shape checks and source audits. No ordinal or path is
   inferred from this source text, and no native acceptance is asserted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse

namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
universe u

-- Retain the public universe parameter without putting V or its dictionary in Params.
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Nat
  State q := Fin (3*q)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ q i =>
      @Decidable.decide (i.val+1 = 2) (Classical.propDecidable (i.val+1 = 2)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (i : Fin (3*q)),
    s i ∈ criticalA q hq s ↔ R.readout () q i = true ∨
      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j+1 ∨ i.val+1 = 3*j+2)

-- Reflect the explicitly supplied decision, rather than changing the proposition.
private theorem decide_true_iff (p : Prop) (d : Decidable p) :
    @Decidable.decide p d = true ↔ p := by
  cases d with
  | isTrue hp =>
    constructor
    · intro _
      exact hp
    · intro _
      rfl
  | isFalse hp =>
    constructor
    · intro h
      cases h
    · intro h
      exact (hp h).elim

private theorem actual_true_iff (q : Nat) (i : Fin (3*q)) :
    actual.readout () q i = true ↔ i.val+1 = 2 := by
  exact decide_true_iff (i.val+1 = 2) (Classical.propDecidable (i.val+1 = 2))

private theorem bridge :
    (type_of% (@criticalA_formula.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv q hq s i
    constructor
    · intro hi
      rcases (@h V fv dv q hq s i).mp hi with hfirst | hrest
      · exact Or.inl ((actual_true_iff q i).mpr hfirst)
      · exact Or.inr hrest
    · intro hi
      apply (@h V fv dv q hq s i).mpr
      rcases hi with hfirst | hrest
      · exact Or.inl ((actual_true_iff q i).mp hfirst)
      · exact Or.inr hrest
  · intro h V fv dv q hq s i
    constructor
    · intro hi
      rcases (@h V fv dv q hq s i).mp hi with hfirst | hrest
      · exact Or.inl ((actual_true_iff q i).mp hfirst)
      · exact Or.inr hrest
    · intro hi
      apply (@h V fv dv q hq s i).mpr
      rcases hi with hfirst | hrest
      · exact Or.inl ((actual_true_iff q i).mpr hfirst)
      · exact Or.inr hrest

private theorem source_law : arena.{u}.Law actual :=
  bridge.mp (@criticalA_formula.{u})

private def testSpokes : Fin (3*1) ↪ ULift.{u} (Fin 3) where
  toFun i := ULift.up i
  inj' := by
    intro i j h
    exact congrArg ULift.down h

private theorem present :
    testSpokes.{u} ⟨1, by omega⟩ ∈ criticalA 1 Nat.zero_lt_one testSpokes.{u} := by
  exact (criticalA_formula 1 Nat.zero_lt_one testSpokes.{u} ⟨1, by omega⟩).mpr
    (Or.inl rfl)

-- This is failure of the full original law, at actual criticalA membership.
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} (Fin 3))
    (inferInstance : Fintype (ULift.{u} (Fin 3)))
    (inferInstance : DecidableEq (ULift.{u} (Fin 3)))
    1 Nat.zero_lt_one testSpokes.{u} ⟨1, by omega⟩
  have hx := hh.mp present
  rcases hx with hfalse | ⟨j, hj, hjq, _⟩
  · change (false : Bool) = true at hfalse
    cases hfalse
  · omega

private theorem actual_one : actual.readout () 1 ⟨1, by omega⟩ = true :=
  (actual_true_iff 1 ⟨1, by omega⟩).mpr rfl

private theorem actual_zero : ¬ (actual.readout () 1 ⟨0, by omega⟩ = true) := by
  intro h
  have hh := (actual_true_iff 1 ⟨0, by omega⟩).mp h
  change 0+1 = 2 at hh
  omega

private theorem actual_nonconstant :
    actual.readout () 1 ⟨1, by omega⟩ ≠
      actual.readout () 1 ⟨0, by omega⟩ := by
  intro he
  exact actual_zero (he.symm.trans actual_one)

private theorem variation : Variation arena.{u} actual :=
  ⟨source_law, rejected, rejected_law⟩

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro role
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro other hne
    exact (hne (Subsingleton.elim other role)).elim
  · intro anchor
    exact nomatch anchor

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  exact ⟨1, ⟨1, by omega⟩, ⟨0, by omega⟩, actual_nonconstant⟩

def family : Registration arena.{u} (type_of% (@criticalA_formula.{u})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@criticalA_formula.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse.family
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
    (fun _ q i =>
      @Decidable.decide (i.val+1 = 2) (Classical.propDecidable (i.val+1 = 2)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Pending actual raw compiled occurrence/state/coordinate resolution and all audits.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
