import D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open RegionFilterQExpressibility CopyProfilePolynomial CopyRegionExpressibility
noncomputable section
open Classical

namespace Classification
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Region
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ R => if i = 0 then decide (CopyQExpressible R) else decide (Tail R)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ R : Region, F.readout 0 () R = true ↔ F.readout 1 () R = true

private theorem positive : arena.Law actual := by
  intro R
  simpa only [actual, realize, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, decide_eq_true_eq]
    using (proposition64 R)

private theorem empty_tail : Tail (∅ : Region) := ⟨0, by
  intro p t t' ht ht'
  simp⟩
private def alternating : Region := {z | z.1 % 2 = 0}
private theorem alternating_not_tail : ¬ Tail alternating := by
  rintro ⟨c,hc⟩
  have h := hc (fun _ => 0) (2 * (min c 0 - 1)) (2 * (min c 0 - 1) - 1)
    (by omega) (by omega)
  change (2 * (min c 0 - 1)) % 2 = 0 ↔ (2 * (min c 0 - 1) - 1) % 2 = 0 at h
  omega

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p R => if j = i then !(actual.readout j p R) else actual.readout j p R)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  have h := law ∅
  have he := tail_implies_copy_q_expressible ∅ empty_tail
  have hq := (q_expressible_iff_tail ∅).mpr empty_tail
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp [changed, realize, actual, he, hq, empty_tail] at h

def evidence : Registration arena (type_of% (@proposition64)) where
  actual := actual
  bridge := by
    change (∀ R : Region, CopyQExpressible R ↔ Tail R) ↔ _
    simp only [actual, realize, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, decide_eq_true_eq]
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p R
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨(), ∅, alternating, ?_⟩
    have he := tail_implies_copy_q_expressible ∅ empty_tail
    have hn : ¬ CopyQExpressible alternating := fun h =>
      alternating_not_tail (copy_q_expressible_implies_tail alternating h)
    have hq := (q_expressible_iff_tail ∅).mpr empty_tail
    have hnq : ¬ QExpressible alternating := fun h =>
      alternating_not_tail ((q_expressible_iff_tail alternating).mp h)
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp [actual, realize, he, hn, hq, hnq, empty_tail, alternating_not_tail]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility.proposition64)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility.proposition64
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility.Classification.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }, { path := #["body","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end Classification

namespace ThreeWay
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Region
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ R => if i = 0 then decide (CopyQExpressible R) else if i = 1 then decide (QExpressible R) else decide (Tail R)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ R : Region, F.readout 0 () R = true ↔ F.readout 1 () R = true ∧ F.readout 2 () R = true

private theorem positive : arena.Law actual := by
  intro R
  simpa only [actual, realize, ite_true, show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false, decide_eq_true_eq]
    using (proposition64_three_way R)

private theorem empty_tail : Tail (∅ : Region) := ⟨0, by
  intro p t t' ht ht'
  simp⟩
private def alternating : Region := {z | z.1 % 2 = 0}
private theorem alternating_not_tail : ¬ Tail alternating := by
  rintro ⟨c,hc⟩
  have h := hc (fun _ => 0) (2 * (min c 0 - 1)) (2 * (min c 0 - 1) - 1)
    (by omega) (by omega)
  change (2 * (min c 0 - 1)) % 2 = 0 ↔ (2 * (min c 0 - 1) - 1) % 2 = 0 at h
  omega

def changed (i : Fin 3) : Realization signature := realize signature
  (fun j p R => if j = i then !(actual.readout j p R) else actual.readout j p R)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 3) : ¬ arena.Law (changed i) := by
  intro law
  have h := law ∅
  have he := tail_implies_copy_q_expressible ∅ empty_tail
  have hq := (q_expressible_iff_tail ∅).mpr empty_tail
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [changed, realize, actual, he, hq, empty_tail] at h

def evidence : Registration arena (type_of% (@proposition64_three_way)) where
  actual := actual
  bridge := by
    change (∀ R : Region, CopyQExpressible R ↔ QExpressible R ∧ Tail R) ↔ _
    simp only [actual, realize, ite_true, show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false, decide_eq_true_eq]
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p R
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 3 at i
    refine ⟨(), ∅, alternating, ?_⟩
    have he := tail_implies_copy_q_expressible ∅ empty_tail
    have hn : ¬ CopyQExpressible alternating := fun h =>
      alternating_not_tail (copy_q_expressible_implies_tail alternating h)
    have hq := (q_expressible_iff_tail ∅).mpr empty_tail
    have hnq : ¬ QExpressible alternating := fun h =>
      alternating_not_tail ((q_expressible_iff_tail alternating).mp h)
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [actual, realize, he, hn, hq, hnq, empty_tail, alternating_not_tail]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility.proposition64_three_way)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility.proposition64_three_way
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility.ThreeWay.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }, { path := #["body","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }, { path := #["body","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end ThreeWay
end
end Reg.D5.S3.ConceptDynamics.Spacetime.CopyRegionExpressibility
