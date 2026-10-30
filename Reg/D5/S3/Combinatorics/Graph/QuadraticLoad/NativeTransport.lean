import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
open D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem native_nonnegative {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ kappa G := by
  obtain ⟨a,ha,hm⟩ := minimum_attained G
  rw [← hm]
  exact (sum_nonneg fun c _ => sq_nonneg (a (Classical.arbitrary V) c)).trans
    (load_le_maxLoad G a (Classical.arbitrary V))

abbrev injectionArena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} {W : Type v} [Fintype V] [Fintype W] [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : V → W) (_hi : Function.Injective f)
    (_hf : ∀ x y, G.Adj x y → H.Adj (f x) (f y)),
    kappa G ≤ R.readout () () (kappa H)

def injectionFamily : Registration injectionArena.{u,v}
    (type_of% @kappa_le_of_injective_hom.{u,v}) := by
  have hn : ¬injectionArena.{u,v}.Law rejected := by
    intro h
    let V := ULift.{u} Unit
    let W := ULift.{v} Unit
    let G : SimpleGraph V := ⊥
    let H : SimpleGraph W := ⊥
    let f : V → W := fun _ => ULift.up ()
    have hi : Function.Injective f := fun a b _ => Subsingleton.elim a b
    have hf : ∀ x y, G.Adj x y → H.Adj (f x) (f y) := by
      intro x y he
      exact he.elim
    have he := h G H f hi hf
    change kappa G ≤ -1 at he
    have hz := native_nonnegative G
    linarith
  have hp : injectionArena.{u,v}.Law actual := @kappa_le_of_injective_hom.{u,v}
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨hp, rejected, hn⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  · intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def injectionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport.kappa_le_of_injective_hom.{u,v})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport.injectionUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport.injectionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨injectionArena.{u,v}⟩
  objectArena := .source ⟨injectionArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source injectionArena.{u,v} ⟨injectionFamily.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms injectionFamily
end
end Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport
