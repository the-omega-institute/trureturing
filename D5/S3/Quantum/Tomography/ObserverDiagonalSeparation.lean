/- GID: D5/S3/Quantum/Tomography/ObserverDiagonalSeparation
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ObserverDiagonalSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An information-complete quantum readout coexists with diagonal escape. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import D5.S3.Quantum.Tomography.CompleteContextTomography

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `complete_context_tomography` supplies injectivity of
     the projector-trace readout under complementary rank-one contexts and is
     applied directly.
   * Exact repository hit `escaped_of_fixedPointFree` supplies the diagonal
     escape clause and is applied directly.
   * The canonical `RankOneContext` carrier is imported from the tomography
     family; no sibling observer or quantum-state carrier is redeclared.
   * Repository searches found no single theorem packaging the two independent
     clauses. Pinned-library searches found no stronger combined existential.
-/

open scoped BigOperators

noncomputable section

namespace D5.S3.Quantum.Tomography.ObserverDiagonalSeparation

open Matrix
open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.CompleteContextTomography

/-- Projector-trace probabilities are the source readout on the exact matrix
carrier supplied by a family of rank-one contexts. -/
def contextReadout {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (rho : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Fin (n + 2) -> Fin (n + 1) -> ℂ :=
  fun l j => trace (rho * (context l).projector j)

private def oneDimensionalContext : RankOneContext 1 where
  projector := fun _ => 1
  rankOne := by
    intro j
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro X
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.trace, Matrix.mul_apply]
  resolvesIdentity := by simp

/-- A complete quantum readout can be realized together with an independent
fixed-point-free diagonal escape. The readout is injective on the full complex
matrix carrier, while the diagonal carrier is the explicitly typed `Unit/Bool`
listing from the source construction. -/
theorem empirical_observer_diagonal_separation :
    ∃ context : Fin 2 -> RankOneContext 1,
      (∀ l k j r,
        trace ((context l).projector j * (context k).projector r) =
          if l = k then (if j = r then 1 else 0) else (1 : ℂ)⁻¹) ∧
      Function.Injective (contextReadout context) ∧
      (∃ (evaluation : Unit -> Unit -> Bool) (twist : Bool -> Bool),
        (∀ y, twist y ≠ y) ∧
          (fun a => twist (evaluation a a)) ∉ Set.range evaluation) := by
  let context : Fin 2 -> RankOneContext 1 := fun _ => oneDimensionalContext
  have hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else (1 : ℂ)⁻¹ := by
    intro l k j r
    have hjr : j = r := Subsingleton.elim _ _
    subst r
    simp [context, oneDimensionalContext]
  refine ⟨context, ?_, ?_, ?_⟩
  · intro l k j r
    have hjr : j = r := Subsingleton.elim _ _
    subst r
    simp [context, oneDimensionalContext]
  · intro rho sigma hreadout
    have hoverlap0 : ∀ (l k : Fin (0 + 2)) (j r : Fin (0 + 1)),
        trace ((context l).projector j * (context k).projector r) =
          if l = k then (if j = r then 1 else 0) else ((0 + 1 : Nat) : ℂ)⁻¹ := by
      simpa using hoverlap
    apply (complete_context_tomography (n := 0) context hoverlap0).2.2 rho sigma
    intro l j
    simpa [contextReadout] using congrFun (congrFun hreadout l) j
  · refine ⟨fun _ _ => true, fun b => !b, ?_, ?_⟩
    · decide
    · change IsEscaped (fun b : Bool => !b) (fun _ _ : Unit => true)
      exact escaped_of_fixedPointFree (fun b : Bool => !b) (by decide)
        (fun _ _ : Unit => true)

#print axioms contextReadout
#print axioms empirical_observer_diagonal_separation

end D5.S3.Quantum.Tomography.ObserverDiagonalSeparation
