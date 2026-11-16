import Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Run
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Result (rev3 run3)

abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : Equiv.Perm (Fin n), Finset (Fin n)
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p w => ((valueGraph p.2.1).induce (p.2.1 '' ((p.2.2.erase w : Finset _) : Set _))).Connected)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)},
    EarRun π S → ∀ w, R.readout () ⟨n,π,S⟩ w
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 3 rev3 Finset.univ run3 0

def family : Registration arena (type_of% (@EarRun.robust)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EarRun.robust, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨3,Equiv.refl _,{0}⟩, 1, 0, ?_⟩
    have hg : actual.readout i ⟨3,Equiv.refl _,{0}⟩ 1 := by
      change ((valueGraph (Equiv.refl (Fin 3))).induce
        ((Equiv.refl (Fin 3)) '' ((({0} : Finset (Fin 3)).erase 1) : Set _))).Connected
      have heq : (Equiv.refl (Fin 3)) '' ((({0} : Finset (Fin 3)).erase 1) : Set _) = {0} := by
        ext v; simp
      rw [heq]
      haveI : Nonempty ({0} : Set (Fin 3)) := ⟨⟨0,by simp⟩⟩
      haveI : Subsingleton ({0} : Set (Fin 3)) := ⟨by
        intro a b; apply Subtype.ext
        have ha : a.val = 0 := a.property
        have hb : b.val = 0 := b.property
        exact ha.trans hb.symm⟩
      exact SimpleGraph.Connected.of_subsingleton
    intro h
    have he := Eq.mp h hg
    change ((valueGraph (Equiv.refl (Fin 3))).induce
      ((Equiv.refl (Fin 3)) '' ((({0} : Finset (Fin 3)).erase 0) : Set _))).Connected at he
    obtain ⟨⟨v,hv⟩⟩ := he.nonempty
    simpa using hv

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@EarRun.robust) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.EarRun.robust.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Run.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p w => ((valueGraph p.2.1).induce (p.2.1 '' ((p.2.2.erase w : Finset _) : Set _))).Connected) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Run
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Permutation.Verkama62Run
