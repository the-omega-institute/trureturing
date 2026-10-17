/- GID: D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.claim; result=D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result; claim=D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.claim
   digest: An asymmetric three-qutrit state lies outside the Allen–Meyer negativity family. -/

import D5.S3.QuantumBounds.NegativityReductionInclusionRefutation
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Entanglement.AllenMeyerNegativityRegionRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
  (traceNorm_isometry traceNorm_smul_nonneg)

def pairAB (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => ∑ c, ψ (p.1, p.2, c) * star (ψ (q.1, q.2, c))

def pairAC (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => ∑ b, ψ (p.1, b, p.2) * star (ψ (q.1, b, q.2))

def whole (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × (Fin 3 × Fin 3)) (Fin 3 × (Fin 3 × Fin 3)) ℂ :=
  vecMulVec ψ (star ψ)

def negativityTriple (ψ : Fin 3 × Fin 3 × Fin 3 → ℂ) : ℝ × ℝ × ℝ :=
  (negativity (pairAB ψ), negativity (pairAC ψ), negativity (whole ψ))

def familyState (a b c d : ℝ) : Fin 3 × Fin 3 × Fin 3 → ℂ := fun p =>
  if p = (0, 0, 0) then (d : ℂ)
  else if p.1 ≠ 0 ∧ p.2.1 = 0 ∧ p.2.2 = p.1 then (a : ℂ)
  else if p.1 ≠ 0 ∧ p.2.1 = p.1 ∧ p.2.2 = 0 then (b : ℂ)
  else if p.1 ≠ 0 ∧ p.2.1 = p.1 ∧ p.2.2 = p.1 then (c : ℂ)
  else 0

def claim : Prop :=
  ∀ ψ : Fin 3 × Fin 3 × Fin 3 → ℂ, ∑ i, Complex.normSq (ψ i) = 1 →
    ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      d ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 1 ∧
      negativityTriple (familyState a b c d) = negativityTriple ψ

private theorem psd_sub_bound {n : Type} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    traceNorm (P - Q) ≤ P.trace.re + Q.trace.re := by
  have hp := congrArg Complex.re (traceNorm_of_posSemidef hP)
  have hq := congrArg Complex.re (traceNorm_of_posSemidef hQ)
  change traceNorm P = P.trace.re at hp
  change traceNorm Q = Q.trace.re at hq
  simpa only [← sub_eq_add_neg, traceNorm_neg, hp, hq] using traceNorm_add_le P (-Q)

private theorem unitary_bound {n : Type} [Fintype n] [DecidableEq n]
    (M U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    (U * M).trace.re ≤ traceNorm M :=
  (traceNorm_eq_max_re_tr_U M).2 ⟨⟨U, hU⟩, rfl⟩

private def outer {n : Type} (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

private theorem outer_psd {n : Type} [Fintype n] (v : n → ℂ) :
    (outer v).PosSemidef := posSemidef_vecMulVec_self_star v

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Entanglement.AllenMeyerNegativityRegionRefutation
