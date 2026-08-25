/- GID: D5/S3/Observer/Refinement/FinitePrimeTimeTomography
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/FinitePrimeTimeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite complete separation has a finite window; empty and infinite cases are audited. -/

import D5.S3.Observer.Refinement.BiaxialMonotoneRefinement
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Prod
import Mathlib.Order.Preorder.Finite

/- Library-search audit trail (2026-08-25):
   * This session exposed no `lean_loogle`, `lean_leansearch`, or `lean_local_search`
     endpoint; the Lean skill's `smart_search.sh` fallback returned no name match for
     finite directed intersections or finite minimal elements.
   * Direct pinned-Mathlib search found the exact `Set.Finite.exists_minimal` theorem in
     `Mathlib.Order.Preorder.Finite`; it supplies the finite-lattice minimal member below.
   * `Set.toFinite`, `Set.instFinite`, and the finite product instance prove that the
     family of relations is finite when `X` is finite; no finiteness of `O` is required.
   * Repository search found the exact `Indist` definition and `biaxial_monotone` theorem
     in `BiaxialMonotoneRefinement`; both are imported and reused without redefinition.
   * No theorem directly stating stabilization of this prime-time family was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.FinitePrimeTimeTomography

open D5.S3.ConceptDynamics.Experiment.ExperimentExpansionMonotonicity
open D5.S3.Observer.Refinement.BiaxialMonotoneRefinement

/-- Complete observation separates states when the common kernel of every finite
prime-time window is contained in the equality diagonal. -/
def SeparatedByCompleteObservation {X O : Type*}
    (readout : Nat -> X -> O) (T : X -> X) : Prop :=
  (⋂ (J : Finset Nat) (m : Nat), Indist J m readout T) ⊆ Set.diagonal X

/-- On a finite state space, complete separation is already achieved by one finite
prime-time window. Here `J : Finset Nat` follows the existing `Indist` interface. The
compactness argument does not require the indices in `J` to be prime, nor does it require
the readout type `O` to be finite. -/
theorem finite_prime_time_tomography {X O : Type*} [Finite X]
    (readout : Nat -> X -> O) (T : X -> X)
    (hComplete : SeparatedByCompleteObservation readout T) :
    ∃ (J : Finset Nat) (m : Nat), Indist J m readout T ⊆ Set.diagonal X := by
  let family : Set (Set (X × X)) :=
    Set.range fun parameter : Finset Nat × Nat =>
      Indist parameter.1 parameter.2 readout T
  have hFamilyFinite : family.Finite := Set.toFinite family
  have hFamilyNonempty : family.Nonempty := Set.range_nonempty _
  obtain ⟨minimal, hMinimalMember, hMinimal⟩ :=
    hFamilyFinite.exists_minimal hFamilyNonempty
  rcases hMinimalMember with ⟨parameter, rfl⟩
  refine ⟨parameter.1, parameter.2, ?_⟩
  intro pair hPair
  apply hComplete
  simp only [Set.mem_iInter]
  intro K n
  let lowerIndices := parameter.1 ∪ K
  let lowerTime := max parameter.2 n
  have hLowerMember : Indist lowerIndices lowerTime readout T ∈ family := by
    exact ⟨(lowerIndices, lowerTime), rfl⟩
  have hLowerSelected :
      Indist lowerIndices lowerTime readout T ⊆
        Indist parameter.1 parameter.2 readout T := by
    exact biaxial_monotone parameter.1 lowerIndices parameter.2 lowerTime readout T
      Finset.subset_union_left (Nat.le_max_left _ _)
  have hLowerTarget :
      Indist lowerIndices lowerTime readout T ⊆ Indist K n readout T := by
    exact biaxial_monotone K lowerIndices n lowerTime readout T
      Finset.subset_union_right (Nat.le_max_right _ _)
  exact hLowerTarget (hMinimal hLowerMember hLowerSelected hPair)

#print axioms finite_prime_time_tomography

/-- Complete separation cannot be omitted: constant observations on `Bool` leave its two
states indistinguishable in every finite window and in the complete intersection. -/
theorem complete_separation_is_necessary :
    ¬SeparatedByCompleteObservation (fun (_ : Nat) (_ : Bool) => ()) id ∧
      ¬∃ (J : Finset Nat) (m : Nat),
        Indist J m (fun (_ : Nat) (_ : Bool) => ()) id ⊆ Set.diagonal Bool := by
  constructor
  · intro hComplete
    have hPair :
        (false, true) ∈
          ⋂ (J : Finset Nat) (m : Nat),
            Indist J m (fun (_ : Nat) (_ : Bool) => ()) id := by
      simp [Indist, experimentIndistinguishability, observationSchedule,
        orbitExperiment]
    exact Bool.false_ne_true (hComplete hPair)
  · rintro ⟨J, m, hSeparates⟩
    have hPair :
        (false, true) ∈
          Indist J m (fun (_ : Nat) (_ : Bool) => ()) id := by
      simp [Indist, experimentIndistinguishability, observationSchedule,
        orbitExperiment]
    exact Bool.false_ne_true (hSeparates hPair)

#print axioms complete_separation_is_necessary

/-- Finiteness is necessary. Threshold observations separate all natural numbers jointly,
but every finite index set misses two consecutive states beyond its maximum. The transition
is the identity, so increasing the time depth supplies no additional information. -/
theorem finiteness_is_necessary :
    (¬Finite Nat) ∧
      SeparatedByCompleteObservation (fun i x : Nat => decide (x < i)) id ∧
      ¬∃ (J : Finset Nat) (m : Nat),
        Indist J m (fun i x : Nat => decide (x < i)) id ⊆ Set.diagonal Nat := by
  refine ⟨Infinite.not_finite, ?_, ?_⟩
  · rintro ⟨x, y⟩ hPair
    simp only [Set.mem_diagonal_iff]
    by_contra hxy
    simp only [Set.mem_iInter] at hPair
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hWindow := hPair {y} 1
      unfold Indist experimentIndistinguishability at hWindow
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hWindow
      have hReadout := hWindow (y, 0) (by simp [observationSchedule])
      simp [orbitExperiment, hlt] at hReadout
    · have hWindow := hPair {x} 1
      unfold Indist experimentIndistinguishability at hWindow
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hWindow
      have hReadout := hWindow (x, 0) (by simp [observationSchedule])
      simp [orbitExperiment, hgt] at hReadout
  · rintro ⟨J, m, hSeparates⟩
    by_cases hJ : J.Nonempty
    · let bound := J.max' hJ
      have hPair :
          (bound, bound + 1) ∈
            Indist J m (fun i x : Nat => decide (x < i)) id := by
        unfold Indist experimentIndistinguishability
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rintro ⟨i, _⟩ hIndex
        have hi : i ≤ bound := J.le_max' i hIndex.1
        simp [orbitExperiment, not_lt_of_ge hi,
          not_lt_of_ge (hi.trans (Nat.le_succ bound))]
      have hDiagonal := hSeparates hPair
      exact (Nat.ne_of_lt (Nat.lt_succ_self bound)) hDiagonal
    · have hEmpty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      subst J
      have hPair :
          (0, 1) ∈ Indist (∅ : Finset Nat) m
            (fun i x : Nat => decide (x < i)) id := by
        simp [Indist, experimentIndistinguishability, observationSchedule]
      have hDiagonal := hSeparates hPair
      exact Nat.zero_ne_one hDiagonal

#print axioms finiteness_is_necessary

-- Degenerate audit: the empty carrier is separated vacuously, already at `J = ∅, m = 0`.
example :
    SeparatedByCompleteObservation (fun (_ : Nat) (_ : Empty) => ()) id ∧
      Indist (∅ : Finset Nat) 0 (fun (_ : Nat) (_ : Empty) => ()) id ⊆
        Set.diagonal Empty := by
  constructor
  · intro pair _
    exact pair.1.elim
  · intro pair _
    exact pair.1.elim

-- Degenerate audit: a singleton is separated by the empty, zero-time window.
example :
    SeparatedByCompleteObservation (fun (_ : Nat) (_ : Unit) => ()) id ∧
      Indist (∅ : Finset Nat) 0 (fun (_ : Nat) (_ : Unit) => ()) id ⊆
        Set.diagonal Unit := by
  simp [SeparatedByCompleteObservation, Indist, experimentIndistinguishability,
    observationSchedule, Set.diagonal]

-- Degenerate audit: identity dynamics can still separate when one readout separates.
example :
    Indist ({0} : Finset Nat) 1 (fun (_ : Nat) (x : Bool) => x) id ⊆
      Set.diagonal Bool := by
  rintro ⟨x, y⟩ hPair
  simp only [Set.mem_diagonal_iff]
  unfold Indist experimentIndistinguishability at hPair
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hPair
  have hReadout := hPair (0, 0) (by simp [observationSchedule])
  simpa [orbitExperiment] using hReadout

-- Degenerate audit: at time depth zero even an identity readout cannot separate `Bool`.
example :
    ¬Indist ({0} : Finset Nat) 0 (fun (_ : Nat) (x : Bool) => x) id ⊆
      Set.diagonal Bool := by
  intro hSeparates
  have hPair :
      (false, true) ∈
        Indist ({0} : Finset Nat) 0 (fun (_ : Nat) (x : Bool) => x) id := by
    simp [Indist, experimentIndistinguishability, observationSchedule]
  exact Bool.false_ne_true (hSeparates hPair)

end D5.S3.Observer.Refinement.FinitePrimeTimeTomography
