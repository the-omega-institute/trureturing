import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Semigroups.Refinement.FiniteFiberTransport
import Mathlib.Algebra.Group.ULift
import Lean.Elab.Tactic.Omega

/-! The source addition in the conicality clause is observed with its full monoid dictionary. -/

namespace Reg.D5.S3.Semigroups.Refinement.FiniteFiberTransport

open Omega.Refinement
open _root_.D5.S3.Semigroups.Refinement.FiniteFiberTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w z
noncomputable section

abbrev signature : Signature where
  Params := Σ K : Type u, Σ _ : AddCommMonoid K, K
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p y => @Add.add p.1 p.2.1.toAdd p.2.2 y)
    (fun e => nomatch e)

def erased : Realization signature.{u} :=
  realize signature (fun _ p _ => @Zero.zero p.1 p.2.1.toZero)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [inst : AddCommMonoid K],
    ((∀ x y : K, R.readout () ⟨K, inst, x⟩ y = 0 → x = 0 ∧ y = 0) ∧
      BinaryRefinement K) ↔ FiniteFiberTransport.{u,v,w,z} K

private theorem natural_conical : Conical (ULift.{u} ℕ) := by
  intro x y h
  constructor <;> apply ULift.ext
  · change x.down + y.down = 0 at h
    change x.down = 0
    omega
  · change x.down + y.down = 0 at h
    change y.down = 0
    omega

private theorem natural_refinement : BinaryRefinement (ULift.{u} ℕ) := by
  intro a b c d h
  change a.down + b.down = c.down + d.down at h
  refine ⟨⟨min a.down c.down⟩, ⟨a.down - min a.down c.down⟩,
    ⟨c.down - min a.down c.down⟩, ⟨b.down - (c.down - min a.down c.down)⟩, ?_, ?_, ?_, ?_⟩
  all_goals apply ULift.ext
  all_goals change _ = _
  all_goals simp only [ULift.down_add, ULift.down_up]
  all_goals omega

private theorem erased_fails : ¬ arena.{u,v,w,z}.Law erased := by
  intro h
  have hf : FiniteFiberTransport.{u,v,w,z} (ULift.{u} ℕ) :=
    finite_fiber_transport natural_conical natural_refinement
  have hc := ((h (ULift.{u} ℕ)).mpr hf).1 (1 : ULift.{u} ℕ) 0 rfl
  exact one_ne_zero hc.1

def family : Registration arena.{u,v,w,z}
    (type_of% @conical_refinement_iff_finite_fiber_transport.{u,v,w,z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conical_refinement_iff_finite_fiber_transport.{u,v,w,z}, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} ℕ, inferInstance, 0⟩, 0, 1, ?_⟩
    change (0 : ULift.{u} ℕ) + 0 ≠ 0 + 1
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,0,_,0,0}
    (@conical_refinement_iff_finite_fiber_transport.{u,v,w,z})
    (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Semigroups.Refinement.FiniteFiberTransport.conical_refinement_iff_finite_fiber_transport.__information_unit
  realizationName := `Reg.D5.S3.Semigroups.Refinement.FiniteFiberTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p y => @Add.add p.1 p.2.1.toAdd p.2.2 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Semigroups.Refinement.FiniteFiberTransport
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Semigroups.Refinement.FiniteFiberTransport
