import D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridProfile

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

open scoped BigOperators

def observation : ∀ (_ : Unit) (n : ℕ), (Fin n → ℤ) → ℤ := fun _ _ a => ∑ i, a i

def noAnchor : ∀ (_ : Empty) (n : ℕ), Fin n → ℤ := fun e => nomatch e

def actual : Realization signature := realize signature observation noAnchor

def bad : Realization signature := realize signature (fun _ _ _ => 1) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (a : Fin n → ℤ) (A : ℕ) (hA : A%2=1)
    (hodd : ∀ i, a i%2=1) (hupper : ∀ i, a i ≤ A) (ha : Compatible a)
    (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val →
      ¬ (0<a i ∧ 0<a j ∧ 0<a k)),
    r.readout () n a ≤ if n%2=0 then (n : ℤ)-2*(n/3 : ℕ)
      else max (A : ℤ) ((n : ℤ)-2*(n/3 : ℕ))

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (n:=0) (fun i => Fin.elim0 i) 1 (by omega)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
  change (1 : ℤ) ≤ if 0%2=0 then (0 : ℤ)-2*(0/3 : ℕ)
    else max (1 : ℤ) ((0 : ℤ)-2*(0/3 : ℕ)) at hh
  norm_num at hh

abbrev SourceClaim : Prop := ∀ {n : ℕ} (a : Fin n → ℤ) (A : ℕ) (hA : A%2=1)
    (hodd : ∀ i, a i%2=1) (hupper : ∀ i, a i ≤ A) (ha : Compatible a)
    (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val →
      ¬ (0<a i ∧ 0<a j ∧ 0<a k)),
    (∑ i, a i) ≤ if n%2=0 then (n : ℤ)-2*(n/3 : ℕ)
      else max (A : ℤ) ((n : ℤ)-2*(n/3 : ℕ))

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun a A hA hodd hupper ha hthree => profile_bound a A hA hodd hupper ha hthree,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1,(fun _ => 0),(fun _ => 1),?_⟩
    change (∑ _i : Fin 1, (0 : ℤ)) ≠ ∑ _i : Fin 1, (1 : ℤ)
    simp

noncomputable def profileBoundRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.SubQuorum.GridProfile.profile_bound)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubQuorum.GridProfile.profile_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
