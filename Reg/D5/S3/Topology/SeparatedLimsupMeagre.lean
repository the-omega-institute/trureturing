module

import D5.S3.Topology.SeparatedLimsupMeagre
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.Discrete
import Mathlib.Tactic.NormNum

/-! Source-family observations for separated dense limsup classes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped Topology

noncomputable section
universe u

namespace Reg.D5.S3.Topology.SeparatedLimsupMeagre

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Σ X : Type u, TopologicalSpace X × (ℕ → X → ℝ)
  State P := P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x n => P.2.2 n x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [t : TopologicalSpace X]
    (U : ℕ → X → ℝ) (_hU : ∀ n, Continuous (U n))
    (A B : Set X) (_hA : Dense A) (_hB : Dense B) (a b : ℝ) (_hab : a ≠ b)
    (_ha : ∀ x ∈ A, Filter.limsup (fun n => U n x) atTop = a)
    (_hb : ∀ x ∈ B, Filter.limsup (fun n => U n x) atTop = b),
    IsMeagre {x | ∃ L : ℝ, Tendsto (R.readout () ⟨X, t, U⟩ x) atTop (𝓝 L)}

theorem source_bridge :
    (type_of% (@separated_limsup_isMeagre.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl

theorem actual_positive : arena.{u}.Law actual.{u} := @separated_limsup_isMeagre.{u}

local instance : TopologicalSpace (Fin 2) := ⊥
local instance : DiscreteTopology (Fin 2) := ⟨rfl⟩

private abbrev Binary := ℕ → ULift.{u} (Fin 2)

private def binaryU (n : ℕ) (x : Binary.{u}) : ℝ := (x n).down.val

private def binaryClass (c : Fin 2) : Set Binary.{u} :=
  {x | ∀ᶠ n in atTop, (x n).down = c}

private theorem binary_continuous (n : ℕ) : Continuous (binaryU.{u} n) :=
  (continuous_of_discreteTopology : Continuous
    (fun k : ULift.{u} (Fin 2) => (k.down.val : ℝ))).comp (continuous_apply n)

private theorem binary_dense (c : Fin 2) : Dense (binaryClass.{u} c) := by
  intro x
  rw [mem_closure_iff]
  intro O hO hx
  obtain ⟨I, hI⟩ := exists_finset_piecewise_mem_of_mem_nhds (hO.mem_nhds hx)
    (fun _ : ℕ => (ULift.up c : ULift.{u} (Fin 2)))
  refine ⟨I.piecewise x (fun _ => ULift.up c), hI, ?_⟩
  change ∀ᶠ n in atTop, (I.piecewise x (fun _ => ULift.up c) n).down = c
  filter_upwards [eventually_gt_atTop (I.sup id)] with n hn
  have hnI : n ∉ I := by
    intro h
    exact (not_le_of_gt hn) (Finset.le_sup (f := id) h)
  simp [Finset.piecewise, hnI]

private theorem binary_limsup (c : Fin 2) (x : Binary.{u}) (hx : x ∈ binaryClass c) :
    Filter.limsup (fun n => binaryU n x) atTop = (c.val : ℝ) := by
  apply Filter.Tendsto.limsup_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [hx] with n hn
  simp [binaryU, hn]

theorem rejected_negative : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hz := h binaryU binary_continuous (binaryClass 0) (binaryClass 1)
    (binary_dense 0) (binary_dense 1) 0 1 (by norm_num)
    (by simpa using binary_limsup 0) (by simpa using binary_limsup 1)
  have hall : IsMeagre (Set.univ : Set Binary.{u}) := by
    convert hz using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨0, tendsto_const_nhds⟩
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hall

theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 2), inferInstance,
    fun _ x => (x.down.val : ℝ)⟩, ULift.up 0, ULift.up 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def source_registration : Registration arena.{u}
    (type_of% (@separated_limsup_isMeagre.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_negative⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@separated_limsup_isMeagre.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Topology.SeparatedLimsupMeagre.unit
  realizationName := `Reg.D5.S3.Topology.SeparatedLimsupMeagre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ P x n => P.2.2 n x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.SeparatedLimsupMeagre
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "fn", "fn", "arg"]
      stateBinder := 13
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Topology.SeparatedLimsupMeagre
