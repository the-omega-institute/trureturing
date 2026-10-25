import CFMPRawFaceCapSlice1053Transient
import D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceClosedRelation1415Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (TruncatedPoint)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure
variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

-- Temporary direct application of the existing finite zero-guarded closure supplier.
theorem original_truncated_relation_closed (P : RawFacePairing T) :
    IsClosed {ab : TruncatedPoint T × TruncatedPoint T |
      Relation.EqvGen (TruncatedStep P) ab.1 ab.2} := by
  let S : Set (Fin 4 → ℝ) := {a |
    (∀ i, 0 ≤ a i ∧ a i ≤ 3/4) ∧ (∑ i, a i) = 1}
  have hI : ∀ (rho : Equiv.Perm (Fin 4)) (z : Fin 4 → ℝ),
      z ∈ S → (fun i => z (rho.symm i)) ∈ S := by
    intro rho z hz
    exact ⟨fun i => hz.1 _, (rho.symm.sum_comp z).trans hz.2⟩
  exact (uniform_transport_and_closed_relation S hI
    (fun x : T × Fin 4 => (P.facePair x).1) (sigma P)).2.2
end D5.S3.Geometry.Gluing.RawFaceClosedRelation1415Candidate

run_cmd do
  let name := ``D5.S3.Geometry.Gluing.RawFaceClosedRelation1415Candidate.original_truncated_relation_closed
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP1415 missing {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP1415 disallowed {ax}"
  Lean.logInfo m!"CFMP1415 CHECKED {name} axioms={axioms}"
