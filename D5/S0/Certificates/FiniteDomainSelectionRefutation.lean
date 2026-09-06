/- GID: D5/S0/Certificates/FiniteDomainSelectionRefutation
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteDomainSelectionRefutation
   mirror-E: none(waiver:finite-domain-certificate-soundness)
   anchors: []
   digest: Finite-domain support pruning and exhaustive branching soundly refute shared deterministic table-selection constraints. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/- The existing Skeleton and SlotWitness continue to own machine semantics.
   This module is a proof-checking layer for equations child = table(parent),
   rather than a second automaton definition or a separate SAT semantics.
   Repository searches for propagation preservation found no existing checker
   for these shared table-selection equations. The concrete gap4 B/L files are
   checked externally. Their parsing, scheduled-pruning elaboration and the
   arithmetic/typed-model transport are not asserted as Lean theorems here.
   No Lean executable was available in this session. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteDomainSelectionRefutation

/-- A finite assignment, with the four possible transient colors. -/
abbrev Assignment (variables : Nat) := Fin variables → Fin 4

/-- Allowed values for every transition-table or trace variable. -/
abbrev Domains (variables : Nat) := Fin variables → Finset (Fin 4)

/-- All coordinates of an assignment remain inside the current domains. -/
def InDomains {n : Nat} (D : Domains n) (x : Assignment n) : Prop :=
  ∀ v, x v ∈ D v

/-- A shared transition table is selected by the value of the parent node. -/
structure Selection (n : Nat) where
  parent : Fin n
  child : Fin n
  row : Fin 4 → Fin n

/-- The exact deterministic local equation. -/
def Selection.Holds {n : Nat} (e : Selection n) (x : Assignment n) : Prop :=
  x e.child = x (e.row (x e.parent))

/-- An assignment solves every supplied local equation. -/
def Solves {n m : Nat} (C : Fin m → Selection n) (x : Assignment n) : Prop :=
  ∀ j, (C j).Holds x

/-- Intersect one domain, leaving the other coordinates unchanged. -/
def restrict {n : Nat} (D : Domains n) (v : Fin n) (allowed : Finset (Fin 4)) :
    Domains n := fun w => if w = v then D w ∩ allowed else D w

/-- Restriction is sound whenever the actual value is among the allowed ones. -/
theorem restrict_preserves {n : Nat} {D : Domains n} {x : Assignment n}
    (hD : InDomains D x) (v : Fin n) (allowed : Finset (Fin 4))
    (h : x v ∈ allowed) : InDomains (restrict D v allowed) x := by
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [restrict, if_pos rfl, Finset.mem_inter] using And.intro (hD v) h
  · simpa only [restrict, if_neg hw] using hD w

/-- Remove parent values lacking any compatible transition target. -/
def pruneParent {n : Nat} (e : Selection n) (D : Domains n) : Domains n :=
  restrict D e.parent ((D e.parent).filter fun a =>
    (D (e.row a) ∩ D e.child).Nonempty)

/-- Remove child values lacking a compatible parent and table entry. -/
def pruneChild {n : Nat} (e : Selection n) (D : Domains n) : Domains n :=
  restrict D e.child ((D e.child).filter fun b =>
    ∃ a : Fin 4, a ∈ D e.parent ∧ b ∈ D (e.row a))

/-- When the parent has one value, intersect that table row with the child. -/
def pruneRow {n : Nat} (e : Selection n) (a : Fin 4) (D : Domains n) : Domains n :=
  if D e.parent = {a} then restrict D (e.row a) (D e.child) else D

/-- Removing an unsupported parent never removes a satisfying assignment. -/
theorem pruneParent_preserves {n : Nat} (e : Selection n) {D : Domains n}
    {x : Assignment n} (hD : InDomains D x) (he : e.Holds x) :
    InDomains (pruneParent e D) x := by
  apply restrict_preserves hD
  apply Finset.mem_filter.mpr
  refine ⟨hD e.parent, x e.child, Finset.mem_inter.mpr ⟨?_, hD e.child⟩⟩
  rw [show x e.child = x (e.row (x e.parent)) from he]
  exact hD _

/-- Removing an unsupported child never removes a satisfying assignment. -/
theorem pruneChild_preserves {n : Nat} (e : Selection n) {D : Domains n}
    {x : Assignment n} (hD : InDomains D x) (he : e.Holds x) :
    InDomains (pruneChild e D) x := by
  apply restrict_preserves hD
  apply Finset.mem_filter.mpr
  refine ⟨hD e.child, x e.parent, hD e.parent, ?_⟩
  rw [show x e.child = x (e.row (x e.parent)) from he]
  exact hD _

/-- A singleton-parent table-row intersection is also solution preserving. -/
theorem pruneRow_preserves {n : Nat} (e : Selection n) (a : Fin 4)
    {D : Domains n} {x : Assignment n} (hD : InDomains D x) (he : e.Holds x) :
    InDomains (pruneRow e a D) x := by
  by_cases hs : D e.parent = {a}
  · have ha : x e.parent = a := by
      have hp := hD e.parent
      rw [hs, Finset.mem_singleton] at hp
      exact hp
    have hc : x e.child = x (e.row a) := by
      simpa only [Selection.Holds, ha] using he
    simp only [pruneRow, if_pos hs]
    apply restrict_preserves hD
    rw [← hc]
    exact hD _
  · simpa only [pruneRow, if_neg hs] using hD

/-- A pruning instruction names an existing constraint, never a new premise. -/
inductive Instruction (m : Nat)
  | parent (edge : Fin m)
  | child (edge : Fin m)
  | row (edge : Fin m) (value : Fin 4)

/-- Executable semantics of one support-pruning instruction. -/
def applyInstruction {n m : Nat} (C : Fin m → Selection n) :
    Instruction m → Domains n → Domains n
  | .parent j, D => pruneParent (C j) D
  | .child j, D => pruneChild (C j) D
  | .row j a, D => pruneRow (C j) a D

/-- Every permitted instruction preserves every genuine solution. -/
theorem instruction_preserves {n m : Nat} (C : Fin m → Selection n)
    (instruction : Instruction m) {D : Domains n} {x : Assignment n}
    (hD : InDomains D x) (hC : Solves C x) :
    InDomains (applyInstruction C instruction D) x := by
  cases instruction with
  | parent j => exact pruneParent_preserves (C j) hD (hC j)
  | child j => exact pruneChild_preserves (C j) hD (hC j)
  | row j a => exact pruneRow_preserves (C j) a hD (hC j)

/-- Replay an arbitrary finite pruning schedule. A fixed-point hypothesis is
unnecessary for soundness, so scheduling and early stopping remain untrusted. -/
def applySchedule {n m : Nat} (C : Fin m → Selection n) :
    List (Instruction m) → Domains n → Domains n
  | [], D => D
  | instruction :: rest, D =>
      applySchedule C rest (applyInstruction C instruction D)

/-- Soundness is independent of the choice and order of pruning instructions. -/
theorem schedule_preserves {n m : Nat} (C : Fin m → Selection n)
    (schedule : List (Instruction m)) {D : Domains n} {x : Assignment n}
    (hD : InDomains D x) (hC : Solves C x) :
    InDomains (applySchedule C schedule D) x := by
  induction schedule generalizing D with
  | nil => exact hD
  | cons instruction rest ih =>
      exact ih (instruction_preserves C instruction hD hC)

/-- Finite proof trees retain all four children. A child is skipped only when
its value is absent from the current domain. -/
inductive Refutation (n m : Nat)
  | leaf (schedule : List (Instruction m)) (emptyVariable : Fin n)
  | split (schedule : List (Instruction m)) (variable : Fin n)
      (children : Fin 4 → Refutation n m)

/-- The checker accepts only an empty-domain leaf or all feasible branches.
It does not accept an external UNSAT flag as a premise. -/
def check {n m : Nat} (C : Fin m → Selection n) :
    Refutation n m → Domains n → Bool
  | .leaf schedule v, D => decide ((applySchedule C schedule D) v = ∅)
  | .split schedule v children, D =>
      let next := applySchedule C schedule D
      decide (∀ a : Fin 4, a ∈ next v →
        check C (children a) (restrict next v {a}) = true)

/-- Accepted finite refutations exclude every assignment satisfying both the
original domains and all shared transition equations. -/
theorem accepted_refutation_excludes_solution {n m : Nat}
    (C : Fin m → Selection n) (certificate : Refutation n m)
    (D : Domains n) (accepted : check C certificate D = true) :
    ¬ ∃ x : Assignment n, InDomains D x ∧ Solves C x := by
  induction certificate generalizing D with
  | leaf schedule v =>
      rintro ⟨x, hD, hC⟩
      have hnext := schedule_preserves C schedule hD hC
      have empty : (applySchedule C schedule D) v = ∅ :=
        of_decide_eq_true accepted
      have hv := hnext v
      rw [empty] at hv
      simpa using hv
  | split schedule v children ih =>
      rintro ⟨x, hD, hC⟩
      let next := applySchedule C schedule D
      have hnext : InDomains next x := schedule_preserves C schedule hD hC
      have allChildren : ∀ a : Fin 4, a ∈ next v →
          check C (children a) (restrict next v {a}) = true :=
        of_decide_eq_true accepted
      have childAccepted := allChildren (x v) (hnext v)
      have hbranch : InDomains (restrict next v {x v}) x :=
        restrict_preserves hnext v {x v} (Finset.mem_singleton_self _)
      exact ih (x v) (restrict next v {x v}) childAccepted ⟨x, hbranch, hC⟩

#print axioms pruneParent_preserves
#print axioms pruneRow_preserves
#print axioms accepted_refutation_excludes_solution

end D5.S0.Certificates.FiniteDomainSelectionRefutation
