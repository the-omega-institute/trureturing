/- GID: D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:0247a4dd9defa2c79544e9e69e14005579025f60e29e9fee07c7d271a7d2c8ec; result=D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.result; claim=D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.claim
   digest: One decidable lawful propositional kernel has infinitely many globally minimal certified supports. -/

import D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization
import Mathlib.Order.Minimal
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.InfiniteMinimalCertifiedSupports

open LegalLedgerFixedSet SupportFamilyNotIntersectionClosed FiniteSupportPatternRealization
open DagSemantics.StrictDependencyCoordinate

/-- Supports are actual certified finite node sets containing the target. -/
def Supports {P Proof Ax Model : Type*} (k : KernelData P Proof Ax Model)
    (p : P) (S : Set P) : Prop := p ∈ S ∧ S ∈ supportFamily k

/-- Inclusion minimality is global over all actual supports of the same target. -/
def minimalSupports {P Proof Ax Model : Type*} (k : KernelData P Proof Ax Model)
    (p : P) : Set (Set P) := {S | Minimal (Supports k p) S}

/-- The unconditional finiteness principle, with no finite candidate-domain premise. -/
def claim : Prop :=
  ∀ (P Proof Ax Model : Type) (k : KernelData P Proof Ax Model), SourceLaws k →
    ∀ p, (minimalSupports k p).Finite

/-- The root variables are distinct from the variable reserved for the target. -/
def a (n : Nat) : Formula := .imp (.atom (n + 1)) (.atom (n + 1))

/-- The usual implication encoding of r or not r, with r the variable numbered zero. -/
def q : Formula := .imp (Formula.neg (.atom 0)) (Formula.neg (.atom 0))

/-- A single countable proof alphabet: false selects a root, true its target proof. -/
def kernel : KernelData Formula (Nat × Bool) Unit (Nat → Bool) :=
  (fun π p => decide (p = if π.2 then q else a π.1),
   fun _ => ∅,
   fun π => if π.2 then {a π.1} else ∅,
   ∅, Formula.neg, fun _ _ => True, fun v p => p.eval v = true)

/-- The same target occurs in every two-node support. -/
def pair (n : Nat) : Set Formula := {a n, q}

private theorem a_ne_q (n : Nat) : a n ≠ q := by
  simp [a, q, Formula.neg]

private theorem a_injective : Function.Injective a := by
  intro n m h
  simpa [a] using h

private theorem accepted_true (π : Nat × Bool) (v : Nat → Bool) :
    (if π.2 then q else a π.1).eval v = true := by
  cases h : π.2 <;> simp [h, a, q, Formula.neg, Formula.eval]

private theorem pair_certificate (n : Nat) :
    ∃ C : CertifiedNodes kernel, (↑C.nodes : Set Formula) = pair n := by
  let nodes : Finset Formula := {a n, q}
  let w : {p // p ∈ nodes} → Nat × Bool :=
    fun p => (n, decide (p.val = q))
  refine ⟨⟨⟨nodes, w⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p
    rcases Finset.mem_insert.mp p.property with hp | hp
    · have he : p.val = a n := hp
      simp [w, he, kernel, KernelData.accept, a_ne_q n]
    · have he : p.val = q := Finset.mem_singleton.mp hp
      simp [w, he, kernel, KernelData.accept]
  · intro p ax hax
    exact Finset.notMem_empty ax hax
  · intro p x hx
    by_cases hp : p.val = q
    · have he : x = a n := by
        simpa [w, hp, kernel, KernelData.refs] using hx
      simp [nodes, he]
    · simp [w, hp, kernel, KernelData.refs] at hx
  · apply acyclic_of_strictCoordinate (coordinate := fun p : Formula => if p = q then 1 else 0)
    rintro x p ⟨hp, hx⟩
    by_cases he : p = q
    · have hx' : x = a n := by
        simpa [w, he, kernel, KernelData.refs] using hx
      simp [he, hx', a_ne_q n]
    · simp [w, he, kernel, KernelData.refs] at hx
  · simp [CertifiedNodes.nodes, nodes, pair]

private theorem source_laws : SourceLaws kernel := by
  have sound : ∀ p, Proved kernel p → ∀ v, p.eval v = true := by
    rintro p ⟨π, hπ, _⟩ v
    have hp : p = if π.2 then q else a π.1 := of_decide_eq_true hπ
    rw [hp]
    exact accepted_true π v
  refine ⟨fun p hp v _ => sound p hp v, ?_, ?_⟩
  · rintro p ⟨π, hπ, _⟩
    have hp : p = if π.2 then q else a π.1 := of_decide_eq_true hπ
    obtain ⟨C, hC⟩ := pair_certificate π.1
    refine ⟨⟨C, ?_⟩⟩
    change p ∈ (↑C.nodes : Set Formula)
    rw [hC, hp]
    cases h : π.2 <;> simp [h, pair]
  · rintro p ⟨hp, hn⟩
    let v : Nat → Bool := fun _ => false
    have ht := sound p hp v
    have hf := sound (Formula.neg p) hn v
    simp [Formula.neg, Formula.eval, ht] at hf

/-- Closure forces an actual root, whichever accepted target proof a certificate selects. -/
private theorem forced_root (S : Set Formula) (hS : Supports kernel q S) :
    ∃ n, a n ∈ S := by
  obtain ⟨hq, C, hC⟩ := hS
  have hqc : q ∈ C.nodes := by
    change q ∈ (↑C.nodes : Set Formula)
    rw [hC]
    exact hq
  let π := C.witness ⟨q, hqc⟩
  have ha : q = if π.2 then q else a π.1 :=
    of_decide_eq_true (C.property.1 ⟨q, hqc⟩)
  have ht : π.2 = true := by
    cases h : π.2
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at ha
      exact False.elim (a_ne_q π.1 ha.symm)
    · rfl
  have href : a π.1 ∈ kernel.refs π := by
    simp [kernel, KernelData.refs, ht]
  have hc := C.property.2.2.1 ⟨q, hqc⟩ (a π.1) href
  exact ⟨π.1, hC ▸ hc⟩

private theorem pair_minimal (n : Nat) : pair n ∈ minimalSupports kernel q := by
  have hs : Supports kernel q (pair n) :=
    ⟨by simp [pair], pair_certificate n⟩
  refine ⟨hs, ?_⟩
  intro S hS hsub
  obtain ⟨m, hm⟩ := forced_root S hS
  have hmn : m = n := by
    have h := hsub hm
    rcases h with h | h
    · exact a_injective h
    · exact False.elim (a_ne_q m h)
  subst m
  intro p hp
  rcases hp with hp | hp
  · exact hp ▸ hm
  · exact hp ▸ hS.1

private theorem pair_injective : Function.Injective pair := by
  intro n m h
  have hn : a n ∈ pair m := h ▸ (by simp [pair] : a n ∈ pair n)
  rcases hn with hn | hn
  · exact a_injective hn
  · exact False.elim (a_ne_q n hn)

private theorem infinitely_many : (minimalSupports kernel q).Infinite :=
  Set.infinite_of_injective_forall_mem pair_injective pair_minimal

/-- One decidable, sound and consistent kernel has infinitely many globally minimal supports. -/
theorem result : ¬ claim := by
  intro universal
  exact infinitely_many (universal Formula (Nat × Bool) Unit (Nat → Bool) kernel source_laws q)

#print axioms result

end D5.S3.ConceptDynamics.DependencyTopology.InfiniteMinimalCertifiedSupports
