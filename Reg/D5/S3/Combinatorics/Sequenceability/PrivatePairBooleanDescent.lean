import D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open scoped Classical
open Finset LeanInformationAudit
open _root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
universe u
abbrev Parameters := Σ X : Type u, DecidableEq X
structure SourceState (p : Parameters.{u}) where
  M : Submodule ℤ (p.1 → ℤ)
  E : Finset p.1
  S : Finset p.1
  u : p.1
  v : p.1
abbrev signature : Signature where
  Params := Parameters.{u}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p s => by
    letI := p.2
    exact Covers s.M ((s.E.erase s.u).erase s.v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [DecidableEq X] (M : Submodule ℤ (X → ℤ))
    (E S : Finset X) (hcover : Covers M E) (hS : Minimal M E S)
    (hsize : 3 ≤ S.card) (u v : X) (huS : u ∈ S) (hvS : v ∈ S) (huv : u ≠ v)
    (hprivate : ∀ B, Minimal M E B → (u ∈ B ∨ v ∈ B) → B = S),
    let Y := (E.erase u).erase v
    R.readout () ⟨X, inferInstance⟩ ⟨M,E,S,u,v⟩ ∧ Y.card + 2 = E.card ∧
    (∀ z ∈ reducedSpan M Y, embed Y z ∈ M) ∧
    (∀ B : Finset Y, B.Nonempty → B ≠ univ →
      (row B ∈ reducedSpan M Y ↔ row (B.image Subtype.val) ∈ M)) ∧
    (∀ i : Y, embed Y (Pi.single i (1 : ℤ)) = Pi.single i.val 1) ∧
    (∀ i j : Y, embed Y ((Pi.single i (1 : ℤ) : Y → ℤ) - Pi.single j (1 : ℤ)) =
      (Pi.single i.val (1 : ℤ) : X → ℤ) - Pi.single j.val (1 : ℤ))

private def m4 : Submodule ℤ (Fin 4 → ℤ) where
  carrier := {f | f 0 = f 1 ∧ f 1 = f 2}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ⟨by change a 0 + b 0 = a 1 + b 1; rw [ha.1,hb.1],
      by change a 1 + b 1 = a 2 + b 2; rw [ha.2,hb.2]⟩
  smul_mem' := by
    intro r a ha
    exact ⟨by change r • a 0 = r • a 1; rw [ha.1],
      by change r • a 1 = r • a 2; rw [ha.2]⟩
private def triplet : Finset (Fin 4) := {0,1,2}
private theorem row_meets_triplet {B : Finset (Fin 4)} (hm : row B ∈ m4)
    (hhit : 0 ∈ B ∨ 1 ∈ B ∨ 2 ∈ B) : triplet ⊆ B := by
  change row B 0 = row B 1 ∧ row B 1 = row B 2 at hm
  have h01 : (0 ∈ B ↔ 1 ∈ B) := by
    by_cases h0 : 0 ∈ B <;> by_cases h1 : 1 ∈ B <;> simp_all [row]
  have h12 : (1 ∈ B ↔ 2 ∈ B) := by
    by_cases h1 : 1 ∈ B <;> by_cases h2 : 2 ∈ B <;> simp_all [row]
  have hall : 0 ∈ B ∧ 1 ∈ B ∧ 2 ∈ B := by tauto
  intro i hi
  simp only [triplet,mem_insert,mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> tauto
private theorem triplet_complete : Complete m4 univ triplet := by
  refine ⟨subset_univ _, by decide, by decide, ?_⟩
  change row triplet 0 = row triplet 1 ∧ row triplet 1 = row triplet 2
  norm_num [row,triplet]
private theorem triplet_minimal : Minimal m4 univ triplet := by
  refine ⟨triplet_complete, ?_⟩
  intro B hB hBS
  apply Finset.Subset.antisymm hBS
  apply row_meets_triplet hB.2.2.2
  obtain ⟨i,hi⟩ := hB.2.1
  have hiS := hBS hi
  simp only [triplet,mem_insert,mem_singleton] at hiS
  rcases hiS with rfl | rfl | rfl <;> tauto
private theorem pair_private : ∀ B, Minimal m4 univ B →
    (0 ∈ B ∨ 1 ∈ B) → B = triplet := by
  intro B hB hp
  have hSB := row_meets_triplet hB.1.2.2.2 (by tauto)
  exact (hB.2 triplet triplet_complete hSB).symm
private theorem original_coverage : Covers m4 univ := by
  intro w hn he
  have h3 : (3 : Fin 4) ∈ w := by rw [← List.mem_toFinset,he]; simp
  obtain ⟨l,r,hlr⟩ := List.mem_iff_append.mp h3
  refine ⟨[3],⟨l,r,by simpa using hlr.symm⟩,subset_univ _,by decide,by decide,?_⟩
  change row ({3} : Finset (Fin 4)) 0 = row {3} 1 ∧ row {3} 1 = row {3} 2
  norm_num [row]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h m4 univ triplet original_coverage triplet_minimal
    (by decide) 0 1 (by decide) (by decide) (by decide) pair_private
  exact hh.1
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let p : Parameters := ⟨Fin 4, inferInstance⟩
  let s : SourceState p := ⟨m4,univ,triplet,0,1⟩
  let t : SourceState p := ⟨m4,∅,triplet,0,1⟩
  refine ⟨p,s,t,?_⟩
  intro heq
  have hc := (private_pair_exact_boolean_descent m4 univ triplet original_coverage
    triplet_minimal (by decide) 0 1 (by decide) (by decide) (by decide) pair_private).1
  have hs : actual.readout i p s := hc
  rw [heq] at hs
  change Covers m4 (((∅ : Finset (Fin 4)).erase 0).erase 1) at hs
  simp only [erase_empty] at hs
  obtain ⟨w,hw,hC⟩ := hs [] (by simp) (by simp)
  have hw0 : w = [] := by simpa using hw
  simpa [hw0] using hC.2.1

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent)) where
  actual := actual
  bridge := by rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => by letI := p.2; exact Covers s.M ((s.E.erase s.u).erase s.v))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
