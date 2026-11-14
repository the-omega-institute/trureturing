/- GID: D5/S3/Geometry/AlgebraicBoundary/OriginalBoundaryHost
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/OriginalBoundaryHost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original entire boundary, arbitrary positive unit and all-direction closed branch host. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeFiniteBoundary
import D5.S3.Geometry.AlgebraicBoundary.ConeMinimumBranch
import D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry
import D5.S3.Geometry.AlgebraicBoundary.ConeQuantumConsumer
import D5.S3.Geometry.AlgebraicBoundary.ConeSectionBoundary
import D5.S3.Geometry.AlgebraicBoundary.ConeSectionDegree

noncomputable section
open Set Metric
open scoped Topology
open D5.S3.Quantum.Foundation
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
namespace D5.S3.Geometry.AlgebraicBoundary.OriginalBoundaryHost

open private original_finite_boundary_ideal
  from D5.S3.Geometry.AlgebraicBoundary.ConeFiniteBoundary
open private original_minimum_roots_and_branch whole_branch_boundary_vanishing ray_boundary_ideal
  from D5.S3.Geometry.AlgebraicBoundary.ConeMinimumBranch
open private section_radial_geometry
  from D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry
open private original_quantum_consumer
  from D5.S3.Geometry.AlgebraicBoundary.ConeQuantumConsumer
open private linePolynomial affineLinearPolynomial interior_zero_factor
  from D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

open private original_section_boundary
  from D5.S3.Geometry.AlgebraicBoundary.ConeSectionBoundary

open private original_section_degree
  from D5.S3.Geometry.AlgebraicBoundary.ConeSectionDegree
open private affinePullback
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

/-- Original ambient and quantum domains, finite-degree ideal, and every low-degree direction. -/
theorem original_entire_boundary_host {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) (hfull : (interior (C : Set E)).Nonempty)
    (u : E →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    let c : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFunL;
    (    let K : Set {x : E | u x = 1} := {x | (x : E) ∈ C}
    IsCompact K ∧ (interior K).Nonempty ∧
      (∃ b : E, u b = 1 ∧ b ∈ interior (C : Set E)) ∧
      (∀ x : {y : E | u y = 1}, x ∈ frontier K ↔ (x : E) ∈ frontier (C : Set E)) ∧
      (∀ x : E, x ∈ frontier (C : Set E) ∧ x ≠ 0 ↔
        ∃ (r : ℝ) (b : {y : E | u y = 1}), 0 < r ∧ b ∈ frontier K ∧ x = r • (b : E))) ∧
    (IsCompact (base C.toPointedCone u.toLinearMap) ∧
    IsCompact (effects C.toPointedCone u.toLinearMap) ∧
    (∀ p : pure C.toPointedCone u.toLinearMap,
      IsCompact (confirmingEffects C.toPointedCone u.toLinearMap p) ∧
      (confirmingEffects C.toPointedCone u.toLinearMap p).Nonempty) ∧
    ∀ (p : pure C.toPointedCone u.toLinearMap) (x : E), x ∈ C →
      ∃ f : E →L[ℝ] ℝ, f ∈ confirmingEffects C.toPointedCone u.toLinearMap p ∧
        comparison C.toPointedCone u.toLinearMap p x = f x ∧
        ∀ g : E →L[ℝ] ℝ, g ∈ confirmingEffects C.toPointedCone u.toLinearMap p →
          f x ≤ g x) ∧
    (∀ (a : {x : E | u x = 1}),
      a ∈ interior {x : {y : E | u y = 1} | (x : E) ∈ C} →
    let A : Set u.ker := {v | (a : E) + (v : E) ∈ C}
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      closedBall (0 : u.ker) r ⊆ A ∧ A ⊆ closedBall 0 R ∧
      (∀ v : u.ker, ‖v‖ / R ≤ gauge A v ∧ gauge A v ≤ ‖v‖ / r) ∧
      (∀ v w : u.ker, |gauge A v - gauge A w| ≤ ‖v - w‖ / r) ∧
      ∃ h : sphere (0 : u.ker) 1 ≃ₜ
          frontier {x : {y : E | u y = 1} | (x : E) ∈ C},
        (∀ v, ((h v : {y : E | u y = 1}) : E) =
          (a : E) + ((gauge A (v : u.ker))⁻¹ • ((v : u.ker) : E))) ∧
        ∀ v w, dist ((h v : {y : E | u y = 1}) : E)
            ((h w : {y : E | u y = 1}) : E) ≤
          (R + R ^ 2 / r) * dist (v : u.ker) (w : u.ker)) ∧
    (∀ (p : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ), p ≠ 0 →
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) →
    (C : Set E) ∈ MeasureTheory.generateSetAlgebra
      (range (fun r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ => {x : E | MvPolynomial.eval (c x) r = 0}) ∪
        range (fun r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ => {x : E | 0 < MvPolynomial.eval (c x) r})) ∧
    ∃ (d : ℕ) (q : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧ q.totalDegree = d ∧
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ∧
      (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ,
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ q ∣ r) ∧
      (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, r ≠ 0 → r.totalDegree ≤ d →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * q) ∧
      (∀ f g : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, q = f * g →
        f ≠ 0 ∧ g ≠ 0 ∧ f.IsHomogeneous f.totalDegree ∧
          g.IsHomogeneous g.totalDegree ∧ f.totalDegree + g.totalDegree = d)) ∧
    (∀ (p : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ), p ≠ 0 → p.totalDegree ≤ 3 →
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) →
    ∃ (d : ℕ) (q : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ∧
      (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ,
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ q ∣ r) ∧
      (∀ y ∈ interior (C : Set E), 0 < MvPolynomial.eval (c y) q) ∧
      (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, r ≠ 0 → r.totalDegree ≤ d →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * q) ∧
      (let U : Set E := {x | MvPolynomial.eval (c x) p ≠ 0};
        closure (⋃₀ {D ∈ connectedComponentIn U '' U | D ⊆ interior (C : Set E)}) =
          (C : Set E)) ∧
      ∀ e ∈ interior (C : Set E),
        (∀ x : E, (linePolynomial q (-c x) (c e)).natDegree = d ∧
          (linePolynomial q (-c x) (c e)).Splits ∧
          (∀ s : ℝ, x = s • e → linePolynomial q (-c x) (c e) =
            Polynomial.C (MvPolynomial.eval (c e) q) * (Polynomial.X - Polynomial.C s) ^ d)) ∧
        {x : E | ∀ t : ℝ, (linePolynomial q (-c x) (c e)).eval t = 0 → 0 ≤ t} =
          (C : Set E) ∧
        connectedComponentIn {x : E | MvPolynomial.eval (c x) q ≠ 0} e =
          interior (C : Set E) ∧
        closure (connectedComponentIn {x : E | MvPolynomial.eval (c x) q ≠ 0} e) =
          (C : Set E)) ∧
    (∀ (κ : Type) [Fintype κ] (B : Set (κ → ℝ)), Convex ℝ B → IsCompact B →
      ∀ (f : MvPolynomial κ ℝ), f ≠ 0 → f.totalDegree ≤ 3 →
      (∀ x ∈ frontier B, MvPolynomial.eval x f = 0) →
      ∀ a ∈ interior B, MvPolynomial.eval a f = 0 →
      let L := fderiv ℝ (fun x : κ → ℝ => MvPolynomial.eval x f) a
      L ≠ 0 ∧ ∃ g : MvPolynomial κ ℝ, g ≠ 0 ∧ f = affineLinearPolynomial a L * g ∧
        g.totalDegree + 1 = f.totalDegree ∧
        ∀ x ∈ frontier B, MvPolynomial.eval x g = 0) ∧
    (2 ≤ Module.finrank ℝ E →
    let κ := Fin (Module.finrank ℝ u.ker)
    ∃ (b : E) (J : (κ → ℝ) →L[ℝ] E) (A : E →L[ℝ] (κ → ℝ)),
      u b = 1 ∧ b ∈ interior (C : Set E) ∧
      (∀ v, u (J v) = 0) ∧ A b = 0 ∧ (∀ v, A (J v) = v) ∧
      (∀ x, J (A x) = x - u x • b) ∧
      let B : Set (κ → ℝ) := {v | b + J v ∈ C}
      IsCompact B ∧ Convex ℝ B ∧ (interior B).Nonempty ∧ (frontier B).Nonempty ∧
      (∀ v, v ∈ frontier B ↔ b + J v ∈ frontier (C : Set E)) ∧
      (∀ (p : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ) (d : ℕ), p ≠ 0 → p.IsHomogeneous d →
        (∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) p = 0) →
        (∀ q : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, q ≠ 0 →
          (∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) q = 0) →
            p.totalDegree ≤ q.totalDegree) →
        let f := affinePullback p (c b) (c.toContinuousLinearMap.comp J)
        f ≠ 0 ∧ f.totalDegree = p.totalDegree ∧
          (∀ v ∈ frontier B, MvPolynomial.eval v f = 0) ∧
          ∀ g : MvPolynomial κ ℝ, g ≠ 0 →
            (∀ v ∈ frontier B, MvPolynomial.eval v g = 0) → f.totalDegree ≤ g.totalDegree) ∧
      (∀ g : MvPolynomial κ ℝ, g ≠ 0 →
        (∀ v ∈ frontier B, MvPolynomial.eval v g = 0) →
        ∃ G : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, G ≠ 0 ∧ G.IsHomogeneous g.totalDegree ∧
          G.totalDegree = g.totalDegree ∧
          (∀ v, MvPolynomial.eval (c (b + J v)) G = MvPolynomial.eval v g) ∧
          ∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) G = 0)) ∧
    (Module.finrank ℝ E = 1 →
      ∃ (u : E →L[ℝ] ℝ) (b : E) (l : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ),
        u b = 1 ∧ b ∈ interior (C : Set E) ∧
        (∀ x, x = u x • b) ∧ (∀ x, x ∈ C ↔ 0 ≤ u x) ∧
        frontier (C : Set E) = {0} ∧ l ≠ 0 ∧ l.IsHomogeneous 1 ∧ l.totalDegree = 1 ∧
        (∀ x, MvPolynomial.eval (c x) l = u x) ∧
        (∀ r : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ,
          (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ l ∣ r)) ∧
    (∀ (h : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ) (k : ℕ) (e : E), h.IsHomogeneous k →
      e ∈ interior (C : Set E) → MvPolynomial.eval (c e) h ≠ 0 →
      {x : E | ∀ t : ℝ, (linePolynomial h (-c x) (c e)).eval t = 0 → 0 ≤ t} =
        (C : Set E) →
      h ≠ 0 ∧ ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) h = 0) := by
  dsimp only
  let c : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFunL
  refine ⟨original_section_boundary C hs hfull u hu,
    original_quantum_consumer C hfull u hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact section_radial_geometry C u hu a ha
  · intro p hp hvan
    exact original_finite_boundary_ideal c C hs hfull p hp hvan
  · intro p hp hd hvan
    obtain ⟨d, q, hd, hdp, hq, hh, hsq, hv, hm, hi, hpos, huq, _, _, hrec, hroots⟩ :=
      original_minimum_roots_and_branch c C hs hfull p hp hd hvan
    exact ⟨d, q, hd, hdp, hq, hh, hsq, hv, hm, hi, hpos, huq, hrec, hroots⟩
  · intro κ _ B hB hc f hf hd hvan a ha hfa
    exact interior_zero_factor hB hc f hf hd hvan ha hfa

  · intro hdim
    exact original_section_degree c C hs hfull u hu hdim

  · intro hdim
    exact ray_boundary_ideal c C hs hfull hdim
  · intro h k e hh he hhe hbranch
    refine ⟨?_, whole_branch_boundary_vanishing c C h hh he hhe hbranch⟩
    intro hz
    exact hhe (by simp [hz])

end D5.S3.Geometry.AlgebraicBoundary.OriginalBoundaryHost
