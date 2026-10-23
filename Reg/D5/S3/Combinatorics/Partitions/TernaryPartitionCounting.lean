import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.TernaryPartitionCounting
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! Each dependent-family law retains the entire original theorem telescope.
The actual readout is the original weight; the intervention changes its full-sum
occurrence while keeping the other weight occurrences fixed. The source-specific
coordinate reconstruction is unspecified, so these remain incomplete binding
attempts until current report evidence validates the source descriptor. -/

namespace Reg.D5.S3.Combinatorics.Partitions.TernaryPartitionCounting

open _root_.D5.S3.Combinatorics.Partitions.TernaryPartitionCounting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open Classical

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

namespace Transport

abbrev signature : Signature where
  Params := Type u × Type v × Type w
  State p := Setoid (Option p.1) → p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Setoid (Option p.1) → p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ f _ => f ⊤) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} {β : Type v} {A : Type w} [AddCommMonoid A]
    (Pα : Finset (α → ZMod 3)) (h0α : (0 : α → ZMod 3) ∉ Pα)
    (hPα : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ Pα ↔ -u ∉ Pα))
    (Pβ : Finset (β → ZMod 3)) (h0β : (0 : β → ZMod 3) ∉ Pβ)
    (hPβ : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ Pβ ↔ -v ∉ Pβ))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (f : Setoid (Option α) → A),
    (∑ v ∈ Pβ, R.readout () (α, β, A) f (pullPartition m v)) =
      ∑ Q ∈ (Pα.image partition).filter (fun Q => Setoid.ker m ≤ Q), f Q

private theorem representatives {α : Type*} [Unique α] :
    ∀ u : α → ZMod 3, u ≠ 0 →
      (u ∈ ({fun _ => 1} : Finset (α → ZMod 3)) ↔
        -u ∉ ({fun _ => 1} : Finset (α → ZMod 3))) := by
  intro f hf
  have hn : f default ≠ 0 := by
    intro h
    apply hf
    funext i
    simpa only [Unique.default_eq i, Pi.zero_apply] using h
  have hh : ∀ z : ZMod 3, z ≠ 0 → (z = 1 ↔ -z ≠ 1) := by decide
  have he (g : α → ZMod 3) : g = (fun _ => 1) ↔ g default = 1 := by
    constructor
    · intro h; exact congrFun h default
    · intro h; funext i; simpa only [Unique.default_eq i, Pi.zero_apply] using h
  simpa only [Finset.mem_singleton, he, Pi.neg_apply] using hh (f default) hn

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let α := PUnit.{u+1}
  let β := PUnit.{v+1}
  let A := ULift.{w} ℕ
  let Pα : Finset (α → ZMod 3) := {fun _ => 1}
  let Pβ : Finset (β → ZMod 3) := {fun _ => 1}
  have h0α : (0 : α → ZMod 3) ∉ Pα := by
    simp only [Pα, Finset.mem_singleton]
    intro he
    have hh := congrFun he PUnit.unit
    exact (by decide : (0 : ZMod 3) ≠ 1) hh
  have h0β : (0 : β → ZMod 3) ∉ Pβ := by
    simp only [Pβ, Finset.mem_singleton]
    intro he
    have hh := congrFun he PUnit.unit
    exact (by decide : (0 : ZMod 3) ≠ 1) hh
  let m : Option α → Option β := Option.map (fun _ => PUnit.unit)
  have hm : Function.Surjective m := by
    intro b
    cases b with
    | none => exact ⟨none, rfl⟩
    | some b => cases b; exact ⟨some PUnit.unit, rfl⟩
  let f : Setoid (Option α) → A := fun Q => if Q = ⊤ then 0 else ⟨1⟩
  have hpart : pullPartition m (fun _ : β => (1 : ZMod 3)) ≠ ⊤ := by
    intro he
    have hh : pullPartition m (fun _ : β => (1 : ZMod 3)) none (some PUnit.unit) := by
      rw [he]; trivial
    change (0 : ZMod 3) = 1 at hh
    exact (by decide : (0 : ZMod 3) ≠ 1) hh
  have hb := h Pα h0α representatives Pβ h0β representatives m hm f
  have ht := merger_sum_transport Pα h0α representatives Pβ h0β representatives m hm f
  change (∑ x ∈ Pβ, f ⊤) = _ at hb
  rw [← ht] at hb
  have hh : (0 : A) = ⟨1⟩ := by simpa [Pβ, f, hpart] using hb
  have := congrArg ULift.down hh
  exact (by decide : (0 : ℕ) ≠ 1) this

private theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro i
  refine ⟨(PUnit.{u+1}, PUnit.{v+1}, ULift.{w} ℕ), (fun _ => ⟨0⟩), (fun _ => ⟨1⟩), ?_⟩
  intro he
  have h := congrArg (fun f => (f ⊤).down) he
  exact (by decide : (0 : ℕ) ≠ 1) h

def source_registration : Registration arena (type_of% (@merger_sum_transport.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@merger_sum_transport.{u,v,w}, rejected, rejected_law⟩
  sensitivity := by
    letI : Subsingleton arena.signature.Role := by
      change Subsingleton Unit
      infer_instance
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

-- Full-telescope proof retained; Contract discovery is unsupported at rigid_universes.
-- Unfinished audit: https://github.com/the-omega-institute/trureturing/issues/20310.
#print axioms source_registration

end Transport

namespace Counting

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 4) (Fin 4) Bool → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 4) (Fin 4) Bool → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀
    (P3 : Finset (Fin 3 → ZMod 3)) (h03 : (0 : Fin 3 → ZMod 3) ∉ P3)
    (hP3 : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P3 ↔ -u ∉ P3))
    (P2 : Finset (Fin 2 → ZMod 3)) (h02 : (0 : Fin 2 → ZMod 3) ∉ P2)
    (hP2 : ∀ u : Fin 2 → ZMod 3, u ≠ 0 → (u ∈ P2 ↔ -u ∉ P2))
    (P1 : Finset (Fin 1 → ZMod 3)) (h01 : (0 : Fin 1 → ZMod 3) ∉ P1)
    (hP1 : ∀ u : Fin 1 → ZMod 3, u ≠ 0 → (u ∈ P1 ↔ -u ∉ P1))
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ),
    partitionSumR 3 P3 id (R.readout () () f) -
      (∑ k : Fin 6, partitionSumR 2 P2 (pairMergers k) f) +
      2 * (∑ k : Fin 4, partitionSumR 1 P1 (singletonCuts k) f) +
      (∑ k : Fin 3, partitionSumR 1 P1 (balancedCuts k) f) = 0

private def P1 : Finset (Fin 1 → ZMod 3) := {![1]}
private def P2 : Finset (Fin 2 → ZMod 3) := {![0,1], ![1,0], ![1,1], ![1,2]}
private def P3 : Finset (Fin 3 → ZMod 3) :=
  {![0,0,1], ![0,1,0], ![0,1,1], ![0,1,2], ![1,0,0], ![1,0,1], ![1,0,2],
   ![1,1,0], ![1,1,1], ![1,1,2], ![1,2,0], ![1,2,1], ![1,2,2]}

set_option maxHeartbeats 2000000 in
-- Normalize the three finite sign-representative hypotheses for the intervention.
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h03 : (0 : Fin 3 → ZMod 3) ∉ P3 := by decide
  have hP3 : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P3 ↔ -u ∉ P3) := by decide
  have h02 : (0 : Fin 2 → ZMod 3) ∉ P2 := by decide
  have hP2 : ∀ u : Fin 2 → ZMod 3, u ≠ 0 → (u ∈ P2 ↔ -u ∉ P2) := by decide
  have h01 : (0 : Fin 1 → ZMod 3) ∉ P1 := by decide
  have hP1 : ∀ u : Fin 1 → ZMod 3, u ≠ 0 → (u ∈ P1 ↔ -u ∉ P1) := by decide
  have hb := h P3 h03 hP3 P2 h02 hP2 P1 h01 hP1 (fun _ => 0)
  have hc : P3.card = 13 := by decide
  norm_num [partitionSumR, rejected, realize, hc] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have h := congrFun he (fun _ _ => false)
  exact (by norm_num : (0 : ℝ) ≠ 1) h

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    letI : Subsingleton arena.signature.Role := by
      change Subsingleton Unit
      infer_instance
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Partitions.TernaryPartitionCounting.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Partitions.TernaryPartitionCounting.Counting.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.TernaryPartitionCounting.Counting.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Counting
end
end Reg.D5.S3.Combinatorics.Partitions.TernaryPartitionCounting
