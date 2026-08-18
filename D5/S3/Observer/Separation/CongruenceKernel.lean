/- GID: D5/S3/Observer/Separation/CongruenceKernel
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/CongruenceKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The all-iterate pullback of an equivalence is its maximal forward congruence. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-18):
   * No exact D5 declaration or pinned-Mathlib theorem packages this all-iterate
     pullback together with all six source clauses and the final iff.
   * The pinned Mathlib exact support hit `Function.iterate_succ_apply`,
     `Function.iterate_succ_apply'`, and `Function.iterate_add_apply`; all are
     applied below to shift and compose iterates.
   * The standard `Equivalence` record and set inclusion operations are used
     directly; no more specialized congruence API was found. -/

namespace D5.S3.Observer.Separation.CongruenceKernel

open Set

/-- A binary relation represented as a set of ordered pairs. -/
abbrev StateRelation (Y : Type*) := Set (Y × Y)

/-- Forward preservation of a relation by an update map. -/
def TauCongruence {Y : Type*} (tau : Y → Y) (S : StateRelation Y) : Prop :=
  ∀ ⦃y y'⦄, (y, y') ∈ S → (tau y, tau y') ∈ S

/-- The intersection of all forward iterated pullbacks of an equivalence. -/
def congruenceKernel {Y : Type*} (tau : Y → Y) (R : StateRelation Y) :
    StateRelation Y :=
  let _chosenUnit : Unit :=
    Classical.choice (show Nonempty Unit from ⟨Unit.unit⟩)
  {pair | ∀ k : Nat, ((tau^[k]) pair.1, (tau^[k]) pair.2) ∈ R}

private theorem congruence_kernel_equivalence {Y : Type*} (tau : Y → Y)
    (R : StateRelation Y) (hR : Equivalence (fun y y' => (y, y') ∈ R)) :
    Equivalence (fun y y' => (y, y') ∈ congruenceKernel tau R) := by
  constructor
  · intro y k
    exact hR.refl ((tau^[k]) y)
  · intro y y' h k
    exact hR.symm (h k)
  · intro y y' y'' hxy hyz k
    exact hR.trans (hxy k) (hyz k)

private theorem congruence_kernel_congruence {Y : Type*} (tau : Y → Y)
    (R : StateRelation Y) : TauCongruence tau (congruenceKernel tau R) := by
  intro y y' h k
  simpa only [Function.iterate_succ_apply] using h (k + 1)

private theorem congruence_kernel_subset {Y : Type*} (tau : Y → Y)
    (R : StateRelation Y) : congruenceKernel tau R ⊆ R := by
  intro pair h
  simpa using h 0

private theorem congruence_kernel_mono {Y : Type*} (tau : Y → Y)
    {R S : StateRelation Y} (hRS : R ⊆ S) :
    congruenceKernel tau R ⊆ congruenceKernel tau S := by
  intro pair h k
  exact hRS (h k)

private theorem congruence_kernel_idempotent {Y : Type*} (tau : Y → Y)
    (R : StateRelation Y) :
    congruenceKernel tau (congruenceKernel tau R) = congruenceKernel tau R := by
  apply Set.Subset.antisymm
  · intro pair h k
    exact h k 0
  · intro pair h k j
    have hiterate := h (j + k)
    simpa only [Function.iterate_add_apply] using hiterate

private theorem tau_congruence_subset_kernel {Y : Type*} (tau : Y → Y)
    (R S : StateRelation Y) (hS : TauCongruence tau S) (hSR : S ⊆ R) :
    S ⊆ congruenceKernel tau R := by
  intro pair hpair k
  have hSiter : ∀ j : Nat,
      ((tau^[j]) pair.1, (tau^[j]) pair.2) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hpair
    | succ j ih =>
        have hnext :
            (tau ((tau^[j]) pair.1), tau ((tau^[j]) pair.2)) ∈ S :=
          hS ih
        simpa only [Function.iterate_succ_apply'] using hnext
  exact hSR (hSiter k)

/-- The all-iterate pullback is the maximal forward congruence inside an
equivalence, with the six source properties and their equivalent maximality form. -/
theorem congruence_kernel_laws {Y : Type*} (tau : Y → Y)
    (R : StateRelation Y)
    (hR : Equivalence (fun y y' => (y, y') ∈ R)) :
    Equivalence (fun y y' => (y, y') ∈ congruenceKernel tau R) ∧
    TauCongruence tau (congruenceKernel tau R) ∧
    congruenceKernel tau R ⊆ R ∧
    (∀ S : StateRelation Y, S ⊆ R →
      congruenceKernel tau S ⊆ congruenceKernel tau R) ∧
    congruenceKernel tau (congruenceKernel tau R) = congruenceKernel tau R ∧
    (∀ S : StateRelation Y, TauCongruence tau S → S ⊆ R →
      S ⊆ congruenceKernel tau R) ∧
    (∀ S : StateRelation Y,
      TauCongruence tau S →
      (S ⊆ R ↔ S ⊆ congruenceKernel tau R)) := by
  have heq := congruence_kernel_equivalence tau R hR
  have hcong := congruence_kernel_congruence tau R
  have hsub := congruence_kernel_subset tau R
  have hmono : ∀ S : StateRelation Y, S ⊆ R →
      congruenceKernel tau S ⊆ congruenceKernel tau R := by
    intro S hSR
    exact congruence_kernel_mono tau hSR
  have hidem := congruence_kernel_idempotent tau R
  have hmax : ∀ S : StateRelation Y, TauCongruence tau S → S ⊆ R →
      S ⊆ congruenceKernel tau R := by
    intro S hS hSR
    exact tau_congruence_subset_kernel tau R S hS hSR
  refine ⟨heq, hcong, hsub, hmono, hidem, hmax, ?_⟩
  intro S hS
  constructor
  · intro hSR
    exact hmax S hS hSR
  · intro hSK pair hpair
    exact hsub (hSK hpair)

#print axioms congruence_kernel_laws

end D5.S3.Observer.Separation.CongruenceKernel
