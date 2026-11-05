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

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p s => by
    letI := p.2
    exact Covers s.M ((s.E.erase s.u).erase s.v)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
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

private abbrev Index := ULift.{u} (Fin 4)
private def q0 : Index.{u} := ⟨0⟩
private def q1 : Index.{u} := ⟨1⟩
private def q2 : Index.{u} := ⟨2⟩
private def q3 : Index.{u} := ⟨3⟩
private def m4 : Submodule ℤ (Index.{u} → ℤ) where
  carrier := {f | f q0.{u} = f q1.{u} ∧ f q1.{u} = f q2.{u}}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ⟨by change a q0.{u} + b q0.{u} = a q1.{u} + b q1.{u}; rw [ha.1,hb.1],
      by change a q1.{u} + b q1.{u} = a q2.{u} + b q2.{u}; rw [ha.2,hb.2]⟩
  smul_mem' := by
    intro r a ha
    exact ⟨by change r • a q0.{u} = r • a q1.{u}; rw [ha.1],
      by change r • a q1.{u} = r • a q2.{u}; rw [ha.2]⟩
private def triplet : Finset Index.{u} := {q0.{u},q1.{u},q2.{u}}
private theorem row_meets_triplet {B : Finset Index.{u}} (hm : row B ∈ m4.{u})
    (hhit : q0.{u} ∈ B ∨ q1.{u} ∈ B ∨ q2.{u} ∈ B) : triplet.{u} ⊆ B := by
  change row B q0.{u} = row B q1.{u} ∧ row B q1.{u} = row B q2.{u} at hm
  have h01 : (q0.{u} ∈ B ↔ q1.{u} ∈ B) := by
    by_cases h0 : q0.{u} ∈ B <;> by_cases h1 : q1.{u} ∈ B <;> simp_all [row]
  have h12 : (q1.{u} ∈ B ↔ q2.{u} ∈ B) := by
    by_cases h1 : q1.{u} ∈ B <;> by_cases h2 : q2.{u} ∈ B <;> simp_all [row]
  have hall : q0.{u} ∈ B ∧ q1.{u} ∈ B ∧ q2.{u} ∈ B := by tauto
  intro i hi
  simp only [triplet,mem_insert,mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> tauto
private theorem triplet_complete : Complete m4.{u} univ triplet.{u} := by
  refine ⟨subset_univ _, by decide, by decide, ?_⟩
  change row triplet.{u} q0.{u} = row triplet.{u} q1.{u} ∧ row triplet.{u} q1.{u} = row triplet.{u} q2.{u}
  norm_num [row,triplet,q0,q1,q2,q3]
private theorem triplet_minimal : Minimal m4.{u} univ triplet.{u} := by
  refine ⟨triplet_complete.{u}, ?_⟩
  intro B hB hBS
  apply Finset.Subset.antisymm hBS
  apply row_meets_triplet.{u} hB.2.2.2
  obtain ⟨i,hi⟩ := hB.2.1
  have hiS := hBS hi
  simp only [triplet,mem_insert,mem_singleton] at hiS
  rcases hiS with rfl | rfl | rfl <;> tauto
private theorem pair_private : ∀ B, Minimal m4.{u} univ B →
    (q0.{u} ∈ B ∨ q1.{u} ∈ B) → B = triplet.{u} := by
  intro B hB hp
  have hSB := row_meets_triplet.{u} hB.1.2.2.2 (by tauto)
  exact (hB.2 triplet.{u} triplet_complete.{u} hSB).symm
private theorem original_coverage : Covers m4.{u} univ := by
  intro w hn he
  have h3 : (q3.{u} : Index.{u}) ∈ w := by rw [← List.mem_toFinset,he]; simp
  obtain ⟨l,r,hlr⟩ := List.mem_iff_append.mp h3
  refine ⟨[q3.{u}],⟨l,r,by simpa using hlr.symm⟩,subset_univ _,by decide,by decide,?_⟩
  change row ({q3.{u}} : Finset Index.{u}) q0.{u} = row {q3.{u}} q1.{u} ∧ row {q3.{u}} q1.{u} = row {q3.{u}} q2.{u}
  norm_num [row,q0,q1,q2,q3]
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h (X := Index.{u}) m4.{u} univ triplet.{u} original_coverage.{u} triplet_minimal.{u}
    (by decide) q0.{u} q1.{u} (by decide) (by decide) (by decide) pair_private.{u}
  exact hh.1
private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let p : Parameters.{u} := ⟨Index.{u}, inferInstance⟩
  let s : SourceState p := ⟨m4.{u},univ,triplet.{u},q0.{u},q1.{u}⟩
  let t : SourceState p := ⟨m4.{u},∅,triplet.{u},q0.{u},q1.{u}⟩
  refine ⟨p,s,t,?_⟩
  intro heq
  have hc := (private_pair_exact_boolean_descent m4.{u} univ triplet.{u} original_coverage.{u}
    triplet_minimal.{u} (by decide) q0.{u} q1.{u} (by decide) (by decide) (by decide) pair_private.{u}).1
  have hs : actual.readout i p s := hc
  rw [heq] at hs
  change Covers m4.{u} (((∅ : Finset Index.{u}).erase q0.{u}).erase q1.{u}) at hs
  simp only [erase_empty] at hs
  obtain ⟨w,hw,hC⟩ := hs [] (by simp) (by simp)
  have hw0 : w = [] := by simpa using hw
  simpa [hw0] using hC.2.1

def source_registration : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent.{u})) where
  actual := actual
  bridge := by rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent.{u},
    rejected, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u}⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence.{u}

def audit : Contract.Registration.{u + 1, 0, 1, 0, 0, 0, u + 1, u, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent.{u})
    (Realization signature.{u}) Unit Unit where
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
  readout := some (realize signature.{u}
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
