/- GID: D5/S3/Combinatorics/Turnpike/DistinctFullMixtureObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Turnpike/DistinctFullMixtureObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Turnpike/DistinctFullMixtureObstruction.claim; result=D5/S3/Combinatorics/Turnpike/DistinctFullMixtureObstruction.result; claim=D5/S3/Combinatorics/Turnpike/DistinctFullMixtureObstruction.claim
   digest: An all-distinct full containment-pruned feasible assignment is outside every finite mixture of actual rulers. -/
module
public import D5.S3.Combinatorics.Turnpike.DistinctFullMixtureObstructionProofs

/-! The numerical relation and full triangle LP follow Elder, Marçais and
Kingsford, WABI 2026, Sections 3.1–3.5 and 5 (CC BY 4.0).
The same-entire-assignment finite-mixture event and its certificate are repository-derived.
-/
@[expose] public section
namespace D5.S3.Combinatorics.Turnpike.DistinctFullMixtureObstruction
open Omega.Turnpike
open Omega.Turnpike.DistinctFullMixture
noncomputable section

def claim : Prop :=
  ∀ (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ), Admissible n d y μ →
    (∀ q, μ q = 1) →
    (∃ x : Fin n → ℝ, Realizes y μ x) →
    ∀ P : Assignment n d, P ∈ PrunedProjection y μ full → ActualMixture y μ P

/-- The full LP admits an assignment outside the convex hull of all actual rulers. -/
theorem result : ¬ claim := by
  intro h
  exact not_mixture (h 6 15 y μ admissible (fun _ => rfl) ⟨ruler,realizes⟩ assignment full_feasible)

/-- info: 'D5.S3.Combinatorics.Turnpike.DistinctFullMixtureObstruction.result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms result
end
end D5.S3.Combinatorics.Turnpike.DistinctFullMixtureObstruction
