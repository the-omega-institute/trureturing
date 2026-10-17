/- GID: D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim; result=D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result; claim=D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim
   digest: Coherent discrimination bias violates the triangle inequality on replacement channels. -/

import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option linter.style.longLine false

namespace D5.S3.Quantum.QuantumChannels.CoherentDiscriminationTriangleRefutation

open scoped BigOperators ComplexConjugate
open _root_.Matrix
open D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (IsKrausChannel)

noncomputable section

open scoped Classical

/-- Canonical Kraus isometric extension, with a spectator reference system. -/
def extend {R : Type} (K : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : R × Fin 2 → ℂ) : R × Fin 2 × Fin 4 → ℂ :=
  fun x => ∑ a, K x.2.2 x.2.1 a * ψ (x.1, a)

private def amplitude {R E : Type} [Fintype R] [Fintype E]
    (K : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : R × Fin 2 → ℂ)
    (V : Matrix (R × Fin 2 × E × Fin 2) (R × Fin 2 × E × Fin 2) ℂ)
    (e0 : E) (f : Fin 2) : R × Fin 2 × E → ℂ :=
  fun x => ∑ b, ∑ k, conj (K k b x.2.1) *
    (∑ y : R × Fin 2 × E × Fin 2,
      V (x.1, b, x.2.2, f) y *
        (if y.2.2.1 = e0 ∧ y.2.2.2 = 0 then extend K ψ (y.1, y.2.1, k) else 0))

/-- Equation (17): adjoin the zero ancillas, apply V, uncompute the Kraus extension,
and project the flag onto the channel label. The factor 1/4 is the initial 1/2
multiplied by the 1/2 from the Bell bra. The ancilla zero is specified by e0. -/
def successProbability {R E : Type} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E]
    (K0 K1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : R × Fin 2 → ℂ)
    (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ) (e0 : E) : ℝ :=
  (1 / 4 : ℝ) * ∑ x : R × Fin 2 × E,
    ‖amplitude K0 ψ V.val e0 0 x + amplitude K1 ψ V.val e0 1 x‖ ^ 2

/-- Equation (18), over all finite reference and pointed ancilla systems in Type. -/
def coherentValue (K0 K1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {p : ℝ | ∃ (R E : Type) (_ : Fintype R) (_ : Fintype E)
    (_ : DecidableEq R) (_ : DecidableEq E) (e0 : E)
    (ψ : R × Fin 2 → ℂ) (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ),
    (∑ x, ‖ψ x‖ ^ 2) = 1 ∧ p = successProbability K0 K1 ψ V e0}

/-- Triangle inequality for coherent discrimination bias on four-Kraus qubit channels. -/
def claim : Prop :=
  ∀ K1 K2 K3 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
    IsKrausChannel K1 → IsKrausChannel K2 → IsKrausChannel K3 →
    coherentValue K1 K3 - 1/2 ≤
      (coherentValue K1 K2 - 1/2) + (coherentValue K2 K3 - 1/2)

end

end D5.S3.Quantum.QuantumChannels.CoherentDiscriminationTriangleRefutation
