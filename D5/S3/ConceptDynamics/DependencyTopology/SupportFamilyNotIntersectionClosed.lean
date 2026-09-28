/- GID: D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:476a7166417a98a3f02bd514ac97d66e31a54f3746af81966d3e2ef7debbaf57; result=D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.result; claim=D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.claim
   digest: Lawful proof supports need not be intersection closed or the finite downsets of any fixed digraph. -/

import D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed

open LegalLedgerFixedSet DependencyReachabilityOrder

/-- The exact finite node sets admitting some accepted, closed, acyclic witness selection. -/
def supportFamily {P Proof Ax Model : Type*} (k : KernelData P Proof Ax Model) :
    Set (Set P) :=
  {S | ∃ C : CertifiedNodes k, (↑C.nodes : Set P) = S}

/-- Closure under binary intersection, with no nonemptiness requirement. -/
def IntersectionClosed {P : Type*} (family : Set (Set P)) : Prop :=
  ∀ S ∈ family, ∀ T ∈ family, S ∩ T ∈ family

/-- All finite sets containing every direct predecessor of each of their members. -/
def graphFamily {P : Type*} (edge : P → P → Prop) : Set (Set P) :=
  {S | S.Finite ∧ ∀ p ∈ S, ∀ q, edge q p → q ∈ S}

/-- The proposed universal closure or fixed-digraph representation principle. -/
def claim : Prop :=
  ∀ (P Proof Ax Model : Type) (k : KernelData P Proof Ax Model), SourceLaws k →
    IntersectionClosed (supportFamily k) ∨
      ∃ edge : P → P → Prop, supportFamily k = graphFamily edge

/-- Two alternative root proofs give lawful supports whose intersection has no closed witness.
The same kernel also excludes every fixed digraph representation. -/
theorem result : ¬ claim := by
  classical
  let P := Fin 3 × Bool
  let a : P := (0, true)
  let b : P := (1, true)
  let q : P := (2, true)
  let conclusion : Fin 4 → P := fun π => if π = 0 then a else if π = 1 then b else q
  let references : Fin 4 → Finset P :=
    fun π => if π = 2 then {a} else if π = 3 then {b} else ∅
  let k : KernelData P (Fin 4) Unit Unit :=
    (fun π p => decide (p = conclusion π), fun _ => ∅, references, ∅,
      fun p => (p.1, !p.2), fun _ _ => True, fun _ p => p.2 = true)
  let root : Bool → P := fun right => if right then b else a
  let nodes : Bool → Finset P := fun right => {root right, q}
  let witness : (right : Bool) → {p // p ∈ nodes right} → Fin 4 :=
    fun right p => if p.val = q then (if right then 3 else 2) else (if right then 1 else 0)
  have pairCertificate : ∀ right, ∃ C : CertifiedNodes k, C.nodes = nodes right := by
    intro right
    refine ⟨⟨⟨nodes right, witness right⟩, ?_, ?_, ?_, ?_⟩, rfl⟩
    · cases right <;> decide
    · intro p ax hax
      exact Finset.notMem_empty ax hax
    · cases right <;> decide
    · have increase : ∀ x y : P, (∃ hp : y ∈ nodes right,
          x ∈ k.refs (witness right ⟨y, hp⟩)) → x.1.val < y.1.val := by
        cases right <;> decide
      intro p cycle
      have hc := Relation.TransGen.lift (fun p : P => p.1.val) increase p p cycle
      have impossible : p.1.val < p.1.val := by
        simpa only [Relation.transGen_eq_self] using hc
      exact (Nat.lt_irrefl _) impossible
  obtain ⟨left, hleft⟩ := pairCertificate false
  obtain ⟨right, hright⟩ := pairCertificate true
  have laws : SourceLaws k := by
    refine ⟨?_, ?_, ?_⟩
    · rintro p ⟨π, hπ, _⟩ M _
      have hp : p = conclusion π := of_decide_eq_true hπ
      subst p
      change (conclusion π).2 = true
      have h : ∀ π, (conclusion π).2 = true := by decide
      exact h π
    · rintro p ⟨π, hπ, _⟩
      have hp : p = conclusion π := of_decide_eq_true hπ
      subst p
      have hcases : ∀ π, conclusion π = a ∨ conclusion π = b ∨ conclusion π = q := by
        decide
      rcases hcases π with ha | hb | hq
      · refine ⟨⟨left, ?_⟩⟩
        rw [hleft, ha]
        simp [nodes, root]
      · refine ⟨⟨right, ?_⟩⟩
        rw [hright, hb]
        simp [nodes, root]
      · refine ⟨⟨left, ?_⟩⟩
        rw [hleft, hq]
        simp [nodes]
    · rintro p ⟨⟨π, hπ, _⟩, ⟨ρ, hρ, _⟩⟩
      have hp : p = conclusion π := of_decide_eq_true hπ
      have hn : k.neg p = conclusion ρ := of_decide_eq_true hρ
      rw [hp] at hn
      have h : ∀ π ρ, k.neg (conclusion π) ≠ conclusion ρ := by decide
      exact h π ρ hn
  have left_support : ({a, q} : Set P) ∈ supportFamily k := by
    refine ⟨left, ?_⟩
    rw [hleft]
    simp [nodes, root]
  have right_support : ({b, q} : Set P) ∈ supportFamily k := by
    refine ⟨right, ?_⟩
    rw [hright]
    simp [nodes, root]
  have intersection : ({a, q} : Set P) ∩ {b, q} = {q} := by
    ext p
    have h : ∀ p : P, (p = a ∨ p = q) ∧ (p = b ∨ p = q) ↔ p = q := by decide
    exact h p
  have singleton_impossible : ({q} : Set P) ∉ supportFamily k := by
    rintro ⟨C, hC⟩
    have hq : q ∈ C.nodes := by
      change q ∈ (↑C.nodes : Set P)
      rw [hC]
      exact Set.mem_singleton q
    let π := C.witness ⟨q, hq⟩
    have accepted : q = conclusion π := of_decide_eq_true (C.property.1 ⟨q, hq⟩)
    have required : ∀ π, q = conclusion π → a ∈ k.refs π ∨ b ∈ k.refs π := by decide
    have closed : ∀ x ∈ k.refs π, x = q := by
      intro x hx
      have hmem := C.property.2.2.1 ⟨q, hq⟩ x hx
      have hs : x ∈ ({q} : Set P) := hC ▸ hmem
      exact hs
    rcases required π accepted with ha | hb
    · have h : a ≠ q := by decide
      exact h (closed a ha)
    · have h : b ≠ q := by decide
      exact h (closed b hb)
  have not_closed : ¬ IntersectionClosed (supportFamily k) := by
    intro closed
    have h := closed {a, q} left_support {b, q} right_support
    rw [intersection] at h
    exact singleton_impossible h
  have no_graph : ¬ ∃ edge : P → P → Prop, supportFamily k = graphFamily edge := by
    rintro ⟨edge, heq⟩
    apply not_closed
    rw [heq]
    intro S hS T hT
    exact ⟨hS.1.inter_of_left T, fun p hp x hxp =>
      ⟨hS.2 p hp.1 x hxp, hT.2 p hp.2 x hxp⟩⟩
  intro universal
  exact (universal P (Fin 4) Unit Unit k laws).elim not_closed no_graph

#print axioms result
end D5.S3.ConceptDynamics.DependencyTopology.SupportFamilyNotIntersectionClosed
