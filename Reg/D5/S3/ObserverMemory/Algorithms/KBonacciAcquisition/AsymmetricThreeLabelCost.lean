import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost
import Reg.Support.SingleDependentReadout

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel OriginalNarrowCost AsymmetricThreeLabelCost
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

@[reducible] def signature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℕ∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x=y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

@[reducible] def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {Y : Type z} (g u p h r : ℕ)
    (hg : 2 ≤ g) (hu : 3 ≤ u) (hup : u<p) (coprime : Nat.Coprime u p)
    (hp : p=h*u+r) (hr : 1 ≤ r) (hru : r<u)
    (HB HC : Finset ℕ) (nonemptyB : HB.Nonempty) (nonemptyC : HC.Nonempty)
    (disjoint : Disjoint HB HC)
    (boundB : ∀ j ∈ HB, 1 ≤ j ∧ j ≤ u-r)
    (boundC : ∀ j ∈ HC, 1 ≤ j ∧ j < u)
    (A B C : Y) (differentAB : A≠B) (differentAC : A≠C) (differentBC : B≠C) :
    let k := g*p-1
    let m := g*u
    let hk : 0<k := by
      have : 4 ≤ g*p := by nlinarith
      dsimp [k]; omega
    ∀ (f : Option (LiveRecord k) → Y) (v : ZMod 2) (alphabet : Bool),
    (∀ (j : Fin p) (s : ℕ), s<k →
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),s⟩) =
        if j.val ∈ HB then B else if j.val ∈ HC then C else A) →
    R.readout () () (OriginalFiberCost k m hk alphabet f v) ((h+1 : ℕ) : ℕ∞) ∧
      h+1=(p+u-1)/u

private theorem positive : arena.{z}.Law actual := @original_asymmetric_three_label_cost.{z}

private def sampleTarget : Option (LiveRecord 7) → ULift.{z} (Fin 3) := fun q =>
  match q with
  | none => ULift.up 0
  | some q => if (-q.phase).val=2 then ULift.up 1
    else if (-q.phase).val=4 then ULift.up 2 else ULift.up 0

private theorem negative : ¬ arena.{z}.Law rejected := by
  intro law
  have target : ∀ (j : Fin 4) (s : ℕ), s<7 →
      sampleTarget (some ⟨0,-((j.val*2 : ℕ) : ZMod 8),s⟩) =
        if j.val ∈ ({1} : Finset ℕ) then ULift.up 1
        else if j.val ∈ ({2} : Finset ℕ) then ULift.up 2 else ULift.up 0 := by
    intro j s hs
    fin_cases j <;> norm_num [sampleTarget]
  exact (law 2 3 4 1 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) {1} {2} (by simp) (by simp) (by decide)
    (by intro j hj; simp only [Finset.mem_singleton] at hj; subst j; decide)
    (by intro j hj; simp only [Finset.mem_singleton] at hj; subst j; decide)
    (ULift.up 0 : ULift.{z} (Fin 3)) (ULift.up 1) (ULift.up 2)
    (by decide) (by decide) (by decide) sampleTarget 0 false target).1

def evidence : Registration arena.{z}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost.original_asymmetric_three_label_cost.{z})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{z}.Law actual rejected negative
  dependence := by
    intro role
    refine ⟨(),0,1,?_⟩
    intro equal
    have atZero := congrFun equal 0
    change ((0 : ℕ∞)=0) = ((1 : ℕ∞)=0) at atZero
    have impossible : (1 : ℕ∞)=0 := atZero ▸ rfl
    exact one_ne_zero impossible

noncomputable def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost.original_asymmetric_three_label_cost.{z})
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% (ℕ∞)) Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost.informationUnit,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{z}⟩, objectArena := .source ⟨arena.{z}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{z} ⟨evidence.{z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (ℕ∞),
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost
