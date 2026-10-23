import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.ConstrainedProduct
import Reg.Support.DependentFamily
import Mathlib.Topology.Instances.Real.Lemmas

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open Set Filter UniformSpace
open scoped Uniformity

namespace Reg.D5.S1.Dynamics.Shadowing.ConstrainedProduct

noncomputable section
universe u v w t

abbrev signature : Signature where
  Params := Type u
  State I := Finset I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := Finset I
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ _ F => F) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

/-- Preserve the arbitrary dependent metric family and every subspace/entourage.
Only the finite support in the conclusion is observed and varied. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} {Y : I → Type t} [∀ i, MetricSpace (Y i)]
    (S : Set (∀ i, Y i)) (E : Set (S × S)) (_hE : E ∈ 𝓤 S),
    ∃ (F : Finset I) (ε : I → ℝ), (∀ i ∈ R.readout () I F, 0 < ε i) ∧
      ∀ a b : S, (∀ i ∈ R.readout () I F, dist (a.val i) (b.val i) < ε i) → (a, b) ∈ E

private theorem rejected_law : ¬ arena.{u,t}.Law rejected := by
  intro h
  let I := ULift.{u} Unit
  let Y : I → Type t := fun _ => ULift.{t} ℝ
  let S : Set (∀ i, Y i) := univ
  let i : I := ⟨()⟩
  let E : Set (S × S) := {zz | dist (zz.1.val i) (zz.2.val i) < 1}
  have hE : E ∈ 𝓤 S :=
    ((Pi.uniformContinuous_proj Y i).comp uniformContinuous_subtype_val)
      (Metric.dist_mem_uniformity (by norm_num))
  obtain ⟨F, ε, _, ht⟩ := h S E hE
  let a : S := ⟨fun _ => ⟨0⟩, mem_univ _⟩
  let b : S := ⟨fun _ => ⟨2⟩, mem_univ _⟩
  have hh := ht a b (by intro j hj; exact False.elim (Finset.notMem_empty j hj))
  change dist (0 : ℝ) 2 < 1 at hh
  norm_num [Real.dist_eq] at hh

def supportRegistration : Registration arena.{u,t}
    (type_of% (@_root_.D5.S1.Dynamics.Shadowing.finite_support_entourage.{u,t})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Dynamics.Shadowing.finite_support_entourage.{u,t}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let I := ULift.{u} Unit
    refine ⟨I, (∅ : Finset I), ({(⟨()⟩ : I)} : Finset I), ?_⟩
    change (∅ : Finset I) ≠ {(⟨()⟩ : I)}
    simp

/-- Source reconstruction under the returned Finset and its two dependent
membership occurrences remains unfilled. This is an unfinished audit under
https://github.com/the-omega-institute/trureturing/issues/5214. -/
def supportAttempt : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Shadowing.finite_support_entourage.{u,t})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.ConstrainedProduct.support
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.ConstrainedProduct.supportRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,t}⟩
  objectArena := .source ⟨arena.{u,t}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,t} ⟨supportRegistration.{u,t}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- A common-source realization still needs exact reconstruction of the
existential subtype, commonSourceMap and dynamics while preserving arbitrary
index universes, dependent metric instances and the nested shadowing controls.
No whole-family intervention or sensitivity has been supplied for these two
scopes; this remains unfinished under issue #5214.
Exact original public scopes to which the unfinished realization obligation
applies; no finite-index, metric-source, SR-assumed or unconstrained substitute. -/
abbrev shadowing_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.constrained_product_hasShadowing.{u,v,w,t})
def shadowing_actual : shadowing_scope.{u,v,w,t} := @_root_.D5.S1.Dynamics.Shadowing.constrained_product_hasShadowing.{u,v,w,t}
abbrev extension_scope := type_of% (@_root_.D5.S1.Dynamics.Shadowing.constrained_product_extension.{u,v,w,t})
def extension_actual : extension_scope.{u,v,w,t} := @_root_.D5.S1.Dynamics.Shadowing.constrained_product_extension.{u,v,w,t}

#print axioms supportRegistration
#print axioms supportAttempt

end
end Reg.D5.S1.Dynamics.Shadowing.ConstrainedProduct
