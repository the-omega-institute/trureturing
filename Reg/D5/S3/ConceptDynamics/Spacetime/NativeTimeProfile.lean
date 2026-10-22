import D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
import D5.S3.ConceptDynamics.Spacetime.ComplementFibers
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
open _root_.D5.S0.History.Spacetime.ArchiveCarrier
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ComplementCharge NativeTimeProfile
noncomputable section
open Classical

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Rich 3
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ X => if i = 0 then readout (gamma X) else q X)
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ X : Rich 3, F.readout 0 () X = F.readout 1 () X

private theorem positive : arena.Law actual := readout_gamma

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + 1 else actual.readout j p X)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let X := (ComplementFibers.balancedSection 3 0).val
  have h := law X
  have hp : readout (gamma X) = q X := readout_gamma X
  change (if (0 : Fin 2) = i then readout (gamma X) + 1 else readout (gamma X)) =
    (if (1 : Fin 2) = i then q X + 1 else q X) at h
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> norm_num at h <;> omega

def evidence : Registration arena (type_of% (@readout_gamma)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨(), (ComplementFibers.balancedSection 3 0).val,
      (ComplementFibers.balancedSection 3 1).val, ?_⟩
    have h0 : q (ComplementFibers.balancedSection 3 0).val = 0 :=
      ComplementFibers.balancedSection_readout 3 0
    have h1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
      ComplementFibers.balancedSection_readout 3 1
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · change readout (gamma _) ≠ readout (gamma _)
      rw [readout_gamma, readout_gamma, h0, h1]
      decide
    · simpa only [actual, realize, show (1 : Fin 2) ≠ 0 by decide, ite_false] using
        (show q (ComplementFibers.balancedSection 3 0).val ≠
          q (ComplementFibers.balancedSection 3 1).val from by rw [h0,h1]; decide)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.readout_gamma)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.readout_gamma
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.evidence
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
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
