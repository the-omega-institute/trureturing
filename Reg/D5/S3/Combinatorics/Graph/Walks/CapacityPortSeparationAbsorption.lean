import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption

namespace Reg.D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
open _root_.D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped BigOperators

noncomputable section
universe u w

abbrev familyLaw (denominator : ℕ → ℚ) : Prop :=
  ∀ {V : Type u} {E : Type w} [Fintype V] [Fintype E] [DecidableEq V]
    (src dst : E → V) (r : V → ℕ) (K : ℕ)
    (_hloop : ∀ e, src e ≠ dst e)
    (_hzero : ∀ v, r v = 0 → degree src dst v ≤ 1)
    (_hpos : ∀ v, 0 < r v → degree src dst v ≤ 2 * r v)
    (_hleaf : ∀ e, ¬ (Leaf src dst r (src e) ∧ Leaf src dst r (dst e)))
    (_hK : (leafVertices src dst r).card ≤ K),
    (∀ d : ℕ, 2 ≤ d →
      (∀ v t : V, Leaf src dst r v → Leaf src dst r t → v ≠ t →
        (originalGraph src dst).Reachable v t →
        (d : ℕ∞) ≤ (originalGraph src dst).edist v t) →
      (((∑ v, r v : ℕ) : ℤ) + (K : ℤ) ≥
          ((d : ℤ) + 1) * ((Fintype.card E : ℤ) - ((∑ v, r v : ℕ) : ℤ))) ∧
      (((d : ℚ) + 1) / denominator d) * ((Fintype.card E : ℚ) + (K : ℚ)) ≤
        ((∑ v, r v : ℕ) : ℚ) + (K : ℚ)) ∧
    ((∀ v t : V, Leaf src dst r v → Leaf src dst r t → v ≠ t →
      ¬ (originalGraph src dst).Reachable v t) →
      (Fintype.card E : ℤ) - ((∑ v, r v : ℕ) : ℤ) ≤ 0)

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ d => (d : ℚ) + 2) (fun e => nomatch e)

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law r := familyLaw.{u,w} (r.readout () ())

abbrev sourceScope := type_of% (@actual_capacity_port_separation_absorption.{u,w})

theorem source_bridge : sourceScope.{u,w} ↔ arena.{u,w}.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.{u,w}.Law rejected := by
  intro h
  have hzero : ∀ v : ULift.{u} Bool, (1 : ℕ) = 0 →
      degree (fun _ : ULift.{w} Unit => (⟨false⟩ : ULift.{u} Bool))
        (fun _ => ⟨true⟩) v ≤ 1 := by
    intro v hv
    cases hv
  have hpos : ∀ v : ULift.{u} Bool, 0 < (1 : ℕ) →
      degree (fun _ : ULift.{w} Unit => (⟨false⟩ : ULift.{u} Bool))
        (fun _ => ⟨true⟩) v ≤ 2 * 1 := by
    intro v hv
    calc
      _ ≤ Fintype.card (ULift.{w} Unit × Bool) := Fintype.card_subtype_le _
      _ = _ := by simp
  have hleaf : ∀ e : ULift.{w} Unit,
      ¬ (Leaf (fun _ : ULift.{w} Unit => (⟨false⟩ : ULift.{u} Bool))
          (fun _ => ⟨true⟩) (fun _ => 1) ⟨false⟩ ∧
        Leaf (fun _ : ULift.{w} Unit => (⟨false⟩ : ULift.{u} Bool))
          (fun _ => ⟨true⟩) (fun _ => 1) ⟨true⟩) := by
    simp [Leaf]
  have hbudget : (leafVertices (fun _ : ULift.{w} Unit => (⟨false⟩ : ULift.{u} Bool))
      (fun _ => ⟨true⟩) (fun _ => 1)).card ≤ 0 := by
    simp [leafVertices, Leaf]
  have hp := h (fun _ : ULift.{w} Unit => (⟨false⟩ : ULift.{u} Bool))
    (fun _ => ⟨true⟩) (fun _ => 1) 0 (by intro e; simp) hzero hpos hleaf hbudget
  have hf := (hp.1 2 (by decide) (by
    intro v t hv
    exact False.elim (Nat.one_ne_zero hv.1))).2
  norm_num [rejected, DependentFamily.realize] at hf

def familyEvidence : DependentFamily.Registration arena.{u,w} sourceScope.{u,w} where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@actual_capacity_port_separation_absorption.{u,w}),
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),2,3,?_⟩
    norm_num [actual,DependentFamily.realize]

def contract : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@actual_capacity_port_separation_absorption.{u,w})
    (type_of% (DependentFamily.realize signature
      (fun _ _ d => (d : ℚ) + 2) (fun e => nomatch e))) Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption.actual_capacity_port_separation_absorption
    "Reg.D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption/Reg.D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption.familyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ d => (d : ℚ) + 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyEvidence
#print axioms contract

end
end Reg.D5.S3.Combinatorics.Graph.Walks.CapacityPortSeparationAbsorption
