/- GID: D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/QubitChordFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint observations of a quantum processor constrain the full pure-ended chord and spectral Fisher information of its exact program curve. -/

import D5.S3.Quantum.Information.ActualQubitChordObstruction
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Information.ActualQubitChordObstruction

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily
open DependentFamily

def signature : Signature where
  Params := Unit
  State := fun _ => QuantumChannel (Fin 3 × Fin 2) (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ G => jointObservation G) (fun e => nomatch e)

/-- Keep the x component before the physical processor observes the Bloch vector. -/
def projectX : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := WithLp.toLp 2 ![x 0, 0, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' t x := by ext i; fin_cases i <;> simp

def rejected : Realization signature :=
  realize signature (fun _ _ G => (jointObservation G).comp projectX) (fun e => nomatch e)

/-- The observation changes uniformly at all three occurrences. The original
processor, exactness hypotheses, chord endpoints and spectral QFI remain coupled. -/
def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (a : ℝ) (_ha : 0 < a) (ha1 : a < 1)
    (G : QuantumChannel (Fin 3 × Fin 2) (Fin 3))
    (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hrho : ∀ u ∈ Ioo (2 * a - 1) 1, (rho u).PosSemidef ∧ trace (rho u) = 1)
    (hexact : ∀ u ∈ Ioo (2 * a - 1) 1, ∀ k, programOutput G k (rho u) = probeTarget a u k),
    ((∀ k, (signalProbe k).PosSemidef ∧ trace (signalProbe k) = 1) ∧
    ∃ (c v : EuclideanSpace ℝ (Fin 3)) (b : ℝ),
      v ≠ 0 ∧ 2 * a ^ 2 - 1 ≤ b ∧ b ≤ 2 * a - 1 ∧ b < 1 ∧
      c ∈ (r.readout () () G).kerᗮ ∧ v ∈ (r.readout () () G).kerᗮ ∧
      (∀ u ∈ Ioo (2 * a - 1) 1,
        (r.readout () () G).kerᗮ.starProjection (bloch (rho u)) = c + u • v) ∧
      (∀ (u : ℝ) (k : Fin 2), programOutput G k (blochMatrix 1 (c + u • v)) = probeTarget a u k) ∧
      (∀ u : ℝ, ‖c + u • v‖ ≤ 1 ↔ u ∈ Icc b 1) ∧
      (∀ u : ℝ, (blochMatrix 1 (c + u • v)).PosSemidef ↔ u ∈ Icc b 1) ∧
      (∀ u : ℝ, trace (blochMatrix 1 (c + u • v)) = 1) ∧
      (∀ u ∈ Ioo (2 * a - 1) 1, ‖c + u • v‖ < 1) ∧
      ‖c + v‖ = 1 ∧ ‖c + b • v‖ = 1 ∧
      blochMatrix 1 (c + v) * blochMatrix 1 (c + v) = blochMatrix 1 (c + v) ∧
      blochMatrix 1 (c + b • v) * blochMatrix 1 (c + b • v) = blochMatrix 1 (c + b • v) ∧
      0 ≤ (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ∧
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ≤ (1 + b) / 2 ∧
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re < 1) ∧
    (∀ u (hu : u ∈ Ioo (2 * a - 1) 1), DifferentiableAt ℝ rho u →
      (1 - a ^ 2) / ((1 - u) * (1 + u - 2 * a ^ 2)) ≤
        spectralQFI (rho u) (deriv rho u) (hrho u hu).1)

end D5.S3.ConceptDynamics.InformationEscape.QubitChordFamily
