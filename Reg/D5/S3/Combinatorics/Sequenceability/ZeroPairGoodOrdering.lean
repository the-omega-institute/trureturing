import D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
universe u v
namespace Reg.D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering

open _root_.D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering
open _root_.D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum (Good)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical BigOperators

abbrev signature : Signature where
  Params := Σ I : Type u, Σ G : Type v, AddCommGroup G × (I → G)
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w =>
    letI := p.2.2.1
    Good (w.map p.2.2.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {I : Type u} {G : Type v} [inst : AddCommGroup G]
    (a : I → G) (ha : Function.Injective a) (X : Finset I) (s t : I)
    (hs : s ∈ X) (ht : t ∈ X) (hst : s ≠ t)
    (hnz : ∀ x ∈ X, a x ≠ 0) (hop : a s + a t = 0)
    (hz : ∀ U ⊆ (X.erase s).erase t, U.Nonempty → (∑ x ∈ U, a x) ≠ 0),
    ∃ W : List I, W.Perm X.toList ∧ R.readout () ⟨I,G,inst,a⟩ W

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let I := ULift.{u} Bool
  let G := ULift.{v} ℤ
  let a : I → G := fun i => ⟨if i.down then (1 : ℤ) else -1⟩
  let s : I := ⟨false⟩
  let t : I := ⟨true⟩
  have ha : Function.Injective a := by
    rintro ⟨i⟩ ⟨j⟩ he
    have hh := congrArg ULift.down he
    cases i <;> cases j <;> norm_num [a] at hh ⊢
  have hst : s ≠ t := by
    intro he
    have hh : false = true := congrArg ULift.down he
    cases hh
  have hnz : ∀ x ∈ ({s,t} : Finset I), a x ≠ 0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num [a,s,t]
  have hz : ∀ U ⊆ (({s,t} : Finset I).erase s).erase t,
      U.Nonempty → (∑ x ∈ U, a x) ≠ 0 := by
    intro U hU hne
    have he : U = ∅ := Finset.subset_empty.mp (by simpa [hst] using hU)
    simpa [he] using hne
  obtain ⟨W, _, hf⟩ := @h I G inferInstance a ha {s,t} s t
    (by simp) (by simp) hst hnz
    (by apply ULift.ext; norm_num [a,s,t])
    (by simpa only [Finset.subset_iff, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton] using hz)
  exact hf

def family : Registration arena.{u,v}
    (type_of% (@exists_good_order_of_zero_pair.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_good_order_of_zero_pair.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; cases e
  dependence := by
    intro i
    let I := ULift.{u} (Fin 3)
    let G := ULift.{v} ℤ
    let a : I → G := fun i => ⟨if i.down = 0 then (1 : ℤ) else if i.down = 1 then -1 else 2⟩
    let p : signature.Params := ⟨I,G,inferInstance,a⟩
    let x : I := ⟨0⟩
    let y : I := ⟨1⟩
    let z : I := ⟨2⟩
    refine ⟨p, [x,z,y], [x,y,z], ?_⟩
    change Good (([x,z,y] : List I).map a) ≠ Good (([x,y,z] : List I).map a)
    have hg : Good ([⟨1⟩,⟨2⟩,⟨-1⟩] : List G) := by
      intro i j hij hj hp
      have hj3 : j ≤ 3 := by simpa using hj
      have hc : (i=0 ∧ j=1) ∨ (i=0 ∧ j=2) ∨ (i=1 ∧ j=2) ∨
          (i=1 ∧ j=3) ∨ (i=2 ∧ j=3) := by
        simp only [List.length_cons, List.length_nil] at hp
        omega
      rcases hc with hc | hc | hc | hc | hc <;> rcases hc with ⟨rfl,rfl⟩
      all_goals
        intro he
        have hh := congrArg ULift.down he
        norm_num at hh
    have hb : ¬ Good ([⟨1⟩,⟨-1⟩,⟨2⟩] : List G) := by
      intro h
      have hh := h 0 2 (by omega) (by simp) (Or.inr (by simp))
      apply hh
      apply ULift.ext
      norm_num
    intro he
    have hg' : Good (([x,z,y] : List I).map a) := by simpa [a,x,y,z] using hg
    apply hb
    simpa [a,x,y,z] using he.mp hg'

-- This is a faithful typed family attempt, not a completed registration:
-- the exact dependent sourceSelection still needs compiler binding evidence.
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_good_order_of_zero_pair.{u,v}) (Realization signature.{u,v})
    (type_of% (@Good)) Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering.exists_good_order_of_zero_pair.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Good)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering
