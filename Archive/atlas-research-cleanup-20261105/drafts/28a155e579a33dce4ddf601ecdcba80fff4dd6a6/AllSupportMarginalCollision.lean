import D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
namespace Reg.D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
universe u
abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : DecidableEq α, α
  State p := Cycle p.1 →₀ ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cycle p.1 →₀ ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p m => letI : DecidableEq p.1 := p.2.1; Finsupp.mapDomain (delete p.2.2) m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ {α : Type u} [inst : DecidableEq α] (A : Finset α) (hA : 4 ≤ A.card),
    ∃ μ ν : Cycle α →₀ ℚ,
      (∀ C ∈ μ.support ∪ ν.support, C.Nodup ∧ C.toFinset = A) ∧
      (∀ C, 0 ≤ μ C ∧ 0 ≤ ν C) ∧
      (Finsupp.mapDomain (fun _ : Cycle α => ()) μ) () = 1 ∧
      (Finsupp.mapDomain (fun _ : Cycle α => ()) ν) () = 1 ∧
      Disjoint μ.support ν.support ∧
      (∀ i ∈ A, f.readout () ⟨α, inst, i⟩ μ = Finsupp.mapDomain (delete i) ν)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A : Finset (ULift.{u} (Fin 4)) := Finset.univ
  obtain ⟨μ,ν,_,_,_,hn,_,hd⟩ := h A (by simp [A])
  have hh := hd (ULift.up 0) (by simp [A])
  change (0 : Cycle (ULift.{u} (Fin 4)) →₀ ℚ) = Finsupp.mapDomain (delete (ULift.up 0)) ν at hh
  have hm := congrArg (fun q : Cycle (ULift.{u} (Fin 4)) →₀ ℚ =>
    (Finsupp.mapDomain (fun _ : Cycle (ULift.{u} (Fin 4)) => ()) q) ()) hh
  simp only [Finsupp.mapDomain_zero, Finsupp.zero_apply,
    ← Finsupp.mapDomain_comp, Function.comp_def] at hm
  have : (0 : ℚ) = 1 := hm.trans hn
  norm_num at this

def family : Registration arena.{u} (type_of% (@all_support_marginal_collision.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@all_support_marginal_collision, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    let p : signature.Params := ⟨ULift.{u} (Fin 4), inferInstance, ULift.up 0⟩
    refine ⟨p, Finsupp.single Cycle.nil 1, 0, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_support_marginal_collision.{u}) (type_of% actual.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision.all_support_marginal_collision.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
    definition := none
    coordinates := #[0,1,6]
    readouts := #[{
      path :=  #["body","body","body","body","arg","body","arg","body","arg","arg","arg","arg","arg","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
end
