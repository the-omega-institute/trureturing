/- GID: D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/ConferenceGraphSedentariness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Conference walks have sharp square-order floors and nonsquare vanishing infima. -/

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.NumberTheory.Real.Irrational
import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
import D5.S3.Fourier.PositiveFourierApproximationRefutation
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

noncomputable section

namespace D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness

open Matrix Complex Real Set Filter
open scoped BigOperators Topology
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (hamiltonianPropagator)
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer (hamiltonianPropagator_neg)

/-- The pointwise sharp classification and the absence of a uniform family floor. -/
def claim : Prop :=
  (∀ (m : ℕ), 1 ≤ m → ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
    (IsSquare (4 * m + 1) →
      (∀ t : ℝ, 1 / (4 * (m : ℝ) + 1) ^ 2 ≤
        ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) ∧
      (∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
        1 / (4 * (m : ℝ) + 1) ^ 2)) ∧
    (¬ IsSquare (4 * m + 1) →
      (∀ t : ℝ, 0 ≤ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2) ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧
        ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < ε)) ∧
  ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ (m : ℕ), 1 ≤ m → N ≤ 4 * m + 1 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
    ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < c

private lemma conference_identity {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) :
    G.adjMatrix ℂ * G.adjMatrix ℂ =
      (m : ℂ) • (1 : Matrix V V ℂ) - G.adjMatrix ℂ +
        (m : ℂ) • Matrix.of (fun _ _ => (1 : ℂ)) := by
  sorry

private lemma conference_projectors {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) :
    let n : ℂ := 4 * (m : ℂ) + 1
    let r : ℂ := (Real.sqrt (4 * (m : ℝ) + 1) : ℝ)
    let θ : ℂ := (-1 + r) / 2
    let τ : ℂ := (-1 - r) / 2
    let P : Matrix V V ℂ := n⁻¹ • Matrix.of (fun _ _ => (1 : ℂ))
    let Q := 1 - P
    let B := G.adjMatrix ℂ - (2 * (m : ℂ)) • P
    let E := r⁻¹ • (B - τ • Q)
    let F := r⁻¹ • (θ • Q - B)
    P * P = P ∧ E * E = E ∧ F * F = F ∧
      P * E = 0 ∧ E * P = 0 ∧ P * F = 0 ∧ F * P = 0 ∧ E * F = 0 ∧ F * E = 0 ∧
      P + E + F = 1 ∧ G.adjMatrix ℂ = (2 * (m : ℂ)) • P + θ • E + τ • F ∧
      ∀ u : V, P u u = 1 / n ∧ E u u = 2 * (m : ℂ) / n ∧
        F u u = 2 * (m : ℂ) / n := by
  sorry

private lemma three_projector_exp {V : Type} [Fintype V] [DecidableEq V]
    (P E F : Matrix V V ℂ) (a b c : ℂ)
    (hPP : P * P = P) (hEE : E * E = E) (hFF : F * F = F)
    (hPE : P * E = 0) (hEP : E * P = 0) (hPF : P * F = 0) (hFP : F * P = 0)
    (hEF : E * F = 0) (hFE : F * E = 0) (hsum : P + E + F = 1) :
    NormedSpace.exp (a • P + b • E + c • F) =
      Complex.exp a • P + Complex.exp b • E + Complex.exp c • F := by
  sorry

private lemma conference_walk {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) (u : V) (t : ℝ) :
    let n : ℂ := 4 * (m : ℂ) + 1
    let r : ℂ := (Real.sqrt (4 * (m : ℝ) + 1) : ℝ)
    hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u =
      Complex.exp ((t : ℂ) * I * (2 * (m : ℂ))) / n +
        (Complex.exp ((t : ℂ) * I * ((-1 + r) / 2)) +
          Complex.exp ((t : ℂ) * I * ((-1 - r) / 2))) * (2 * (m : ℂ) / n) := by
  sorry

private lemma return_formula {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) (u : V) (t : ℝ) :
    ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
      ‖Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
        ((4 * (m : ℝ)) * Real.cos (Real.sqrt (4 * (m : ℝ) + 1) * t / 2) : ℝ)‖ ^ 2 /
          (4 * (m : ℝ) + 1) ^ 2 := by
  sorry

private lemma odd_cos_bound (q : ℕ) (hq : Odd q) (x : ℝ) :
    |Real.cos ((q : ℝ) * x)| ≤ (q : ℝ) * |Real.cos x| := by
  sorry

private lemma square_lower {m : ℕ} (hm : 1 ≤ m) (hs : IsSquare (4 * m + 1)) (t : ℝ) :
    1 ≤ ‖Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
      ((4 * (m : ℝ)) * Real.cos (Real.sqrt (4 * (m : ℝ) + 1) * t / 2) : ℝ)‖ ^ 2 := by
  sorry

private lemma floor_attainment {m : ℕ} (hm : 1 ≤ m)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m) (u : V) :
    ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 =
      1 / (4 * (m : ℝ) + 1) ^ 2 := by
  sorry

private lemma nonsquare_small {m : ℕ} (hm : 1 ≤ m) (hs : ¬ IsSquare (4 * m + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      ‖Complex.exp (((4 * (m : ℝ) + 1) * t / 2 : ℝ) * I) +
        ((4 * (m : ℝ)) * Real.cos (Real.sqrt (4 * (m : ℝ) + 1) * t / 2) : ℝ)‖ ^ 2 /
          (4 * (m : ℝ) + 1) ^ 2 < ε := by
  sorry

private lemma family_small (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ (m : ℕ), 1 ≤ m → N ≤ 4 * m + 1 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m → ∀ u : V,
      ∃ t : ℝ, 0 < t ∧ ‖hamiltonianPropagator (G.adjMatrix ℂ) (-t) u u‖ ^ 2 < c := by
  sorry

/-- Godsil's conference-graph question has a sharp square-order classification. -/
theorem result : claim := by
  constructor
  · intro m hm V _ _ G _ hG u
    constructor
    · intro hs
      refine ⟨?_, floor_attainment hm G hG u⟩
      intro t
      rw [return_formula hm G hG u t]
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (square_lower hm hs t)
    · intro hs
      refine ⟨fun t => sq_nonneg _, ?_⟩
      intro ε hε
      obtain ⟨t, ht, hp⟩ := nonsquare_small hm hs ε hε
      exact ⟨t, ht, by rwa [return_formula hm G hG u t]⟩
  · exact family_small

end D5.S3.Quantum.Dynamics.ConferenceGraphSedentariness
