/- GID: D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/MixedStateInverseSumsetRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.claim; result=D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result; claim=D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.claim
   digest: A two-level qudit state refutes the mixed-state inverse sumset bound. -/

import D5.S3.Observer.WindowRegister
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The single-qudit reading of Bu--Gu--Jaffe, arXiv:2401.14385v3,
Remark 45, equation (58), with its positive-denominator hypotheses.
The certified instance is the equal mixture of levels zero and one in dimension seven. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix Finset
open scoped ComplexOrder MatrixOrder BigOperators Kronecker
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation

/-- The source's odd-dimensional Weyl operator, with the clock preceding the shift. -/
def weyl (d : ℕ) [NeZero d] (p q : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (windowRoot d ^ ((d + 1) / 2)) ^ (- (p * q)).val •
    (clockMatrix d ^ p.val * shiftMatrix d ^ q.val)

/-- The characteristic function uses the negative Weyl argument. -/
def charFun {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ)
    (x : ZMod d × ZMod d) : ℂ := trace (ρ * weyl d (-x.1) (-x.2))

/-- Weyl orthogonality reconstructs the operator whose characteristic function retains
exactly the coefficients of modulus one, as in the source's mean state. -/
def meanState {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) :
    Matrix (ZMod d) (ZMod d) ℂ :=
  (d : ℂ)⁻¹ • ∑ x ∈ univ.filter (fun x => ‖charFun ρ x‖ = 1),
    charFun ρ x • weyl d x.1 x.2

/-- Rank of the mean state. -/
def meanRank {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℕ :=
  (meanState ρ).rank

/-- The source's magic gap, including its empty-set convention. -/
def magicGap {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℝ :=
  let a := univ.filter (fun x => charFun ρ x ≠ 0 ∧ ‖charFun ρ x‖ ≠ 1)
  if h : a.Nonempty then 1 - a.sup' h (fun x => ‖charFun ρ x‖) else 0

/-- The factor denoted lambda in equation (58). -/
def gapFactor {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℝ :=
  (1 - magicGap ρ) ^ 2

/-- Purity is the real trace of the square. -/
def purity {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) : ℝ :=
  (trace (ρ * ρ)).re

/-- Conjugation by the source's linear permutation followed by the right partial trace.
For admissible parameters the matrix in this formula is the unitary U of the source. -/
def convolution {d : ℕ} [NeZero d] (s t : ZMod d)
    (ρ σ : Matrix (ZMod d) (ZMod d) ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  let u : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
    fun a b => if a = (s * b.1 + t * b.2, -t * b.1 + s * b.2) then 1 else 0
  partialTraceRight (u * (ρ ⊗ₖ σ) * uᴴ)

/-- The mixed-state expectation (58) on its stated positive-denominator domain. -/
def claim : Prop :=
  ∀ (d : ℕ) [NeZero d], d.Prime → ∀ (s t : ZMod d),
    s ≠ 0 → t ≠ 0 → s ^ 2 + t ^ 2 = 1 →
    ∀ (ρ σ τ : DensityState (ZMod d)) (c : ℝ),
      σ.1 = CStarMatrix.ofMatrix (meanState ρ.1) →
      τ.1 = CStarMatrix.ofMatrix (convolution s t ρ.1 ρ.1) →
      let δ := Real.exp (vonNeumannEntropy τ - vonNeumannEntropy ρ)
      let r := (meanRank ρ.1 : ℝ)
      let l := gapFactor ρ.1
      1 < δ → δ ≤ c → 0 < 1 + l * (r * purity ρ.1 - 1) →
      0 < Real.log r - Real.log (1 + l * (r * purity ρ.1 - 1)) →
      quantumRelativeEntropy ρ σ ≤
        Real.log r / (Real.log r - Real.log (1 + l * (r * purity ρ.1 - 1))) * Real.log c

private def rhoWeights (i : ZMod 7) : ℝ := if i = 0 ∨ i = 1 then 1 / 2 else 0
private def tauWeights (i : ZMod 7) : ℝ :=
  if i = 0 ∨ i = 4 then 1 / 4 else if i = 2 then 1 / 2 else 0

private lemma rho_density :
    0 ≤ CStarMatrix.ofMatrix (diagonal fun i => (rhoWeights i : ℂ)) ∧
      trace (diagonal fun i => (rhoWeights i : ℂ)) = 1 := by sorry

private lemma sigma_density :
    0 ≤ CStarMatrix.ofMatrix ((7 : ℂ)⁻¹ • (1 : Matrix (ZMod 7) (ZMod 7) ℂ)) ∧
      trace ((7 : ℂ)⁻¹ • (1 : Matrix (ZMod 7) (ZMod 7) ℂ)) = 1 := by sorry

private lemma tau_density :
    0 ≤ CStarMatrix.ofMatrix (diagonal fun i => (tauWeights i : ℂ)) ∧
      trace (diagonal fun i => (tauWeights i : ℂ)) = 1 := by sorry

private def rho : DensityState (ZMod 7) :=
  ⟨CStarMatrix.ofMatrix (diagonal fun i => (rhoWeights i : ℂ)), rho_density⟩
private def sigma : DensityState (ZMod 7) :=
  ⟨CStarMatrix.ofMatrix ((7 : ℂ)⁻¹ • (1 : Matrix (ZMod 7) (ZMod 7) ℂ)), sigma_density⟩
private def tau : DensityState (ZMod 7) :=
  ⟨CStarMatrix.ofMatrix (diagonal fun i => (tauWeights i : ℂ)), tau_density⟩

private lemma convolution_eq : convolution (2 : ZMod 7) 2 rho.1 rho.1 = tau.1 := by sorry

private lemma rho_entropy : vonNeumannEntropy rho = Real.log 2 := by sorry
private lemma tau_entropy : vonNeumannEntropy tau = 3 / 2 * Real.log 2 := by sorry

private lemma characteristic_off_axis (p q : ZMod 7) (hq : q ≠ 0) :
    charFun rho.1 (p, q) = 0 := by sorry

private lemma characteristic_axis (p : ZMod 7) :
    charFun rho.1 (p, 0) = (1 + windowRoot 7 ^ (-p).val) / 2 := by sorry

private lemma characteristic_norm_one (x : ZMod 7 × ZMod 7) :
    ‖charFun rho.1 x‖ = 1 ↔ x = (0, 0) := by sorry

private lemma characteristic_bound (x : ZMod 7 × ZMod 7) :
    ‖charFun rho.1 x‖ ≤ 1 := by sorry

private lemma mean_eq : meanState rho.1 = sigma.1 := by sorry
private lemma rank_eq : meanRank rho.1 = 7 := by sorry
private lemma gap_bounds : 0 ≤ gapFactor rho.1 ∧ gapFactor rho.1 ≤ 1 := by sorry
private lemma purity_eq : purity rho.1 = 1 / 2 := by sorry
private lemma divergence_eq : quantumRelativeEntropy rho sigma = Real.log 7 - Real.log 2 := by sorry

private lemma doubling_eq :
    Real.exp (vonNeumannEntropy tau - vonNeumannEntropy rho) =
      Real.exp (1 / 2 * Real.log 2) := by sorry

private lemma doubling_gt_one : 1 < Real.exp (1 / 2 * Real.log 2) := by sorry

private lemma numerical_bound (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
    0 < 1 + l * (7 * (1 / 2) - 1) ∧
    0 < Real.log 7 - Real.log (1 + l * (7 * (1 / 2) - 1)) ∧
    Real.log 7 / (Real.log 7 - Real.log (1 + l * (7 * (1 / 2) - 1))) *
      Real.log (Real.exp (1 / 2 * Real.log 2)) ≤ 1 / 2 * Real.log 7 := by sorry

private lemma strict_violation : 1 / 2 * Real.log 7 < Real.log 7 - Real.log 2 := by sorry

/-- The registered seven-dimensional mixed state violates equation (58). -/
theorem result : ¬ claim := by
  intro h
  have hb := numerical_bound (gapFactor rho.1) gap_bounds
  have hc := h 7 (by decide) 2 2 (by decide) (by decide) (by decide)
    rho sigma tau (Real.exp (1 / 2 * Real.log 2))
    (by exact congrArg CStarMatrix.ofMatrix mean_eq.symm)
    (by exact congrArg CStarMatrix.ofMatrix convolution_eq.symm)
  dsimp only at hc
  rw [doubling_eq, rank_eq, purity_eq, divergence_eq] at hc
  exact (not_le_of_gt strict_violation) ((hc doubling_gt_one le_rfl hb.1 hb.2.1).trans hb.2.2)

end D5.S3.Quantum.Magic.MixedStateInverseSumsetRefutation
