/- GID: D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SignallingPureProductNegativity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every signalling channel has a pure product input with positive PDM negativity. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity

variable {α β α₁ β₁ α₂ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α₁] [DecidableEq α₁] [Fintype β₁] [DecidableEq β₁]
  [Fintype α₂] [DecidableEq α₂] [Fintype β₂] [DecidableEq β₂]

/-- The input-transposed CJ convention of the source. -/
def cjMatrix (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix (α × β) (α × β) ℂ :=
  ∑ i, ∑ j, single j i (1 : ℂ) ⊗ₖ e (single i j 1)

/-- Trace out A₁ and B₂ from the two-time PDM of a pure product input. -/
def pdmBA (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) : Matrix (β₁ × α₂) (β₁ × α₂) ℂ :=
  let m := cjMatrix p.toCompletelyPositiveMap.toLinearMap
  let ρ := (vecMulVec a (star a) ⊗ₖ vecMulVec b (star b)) ⊗ₖ
    (1 : Matrix (α₂ × β₂) (α₂ × β₂) ℂ)
  partialTraceLeft (((1 / 2 : ℂ) • (m * ρ + ρ * m)).submatrix
    (fun x : (α₁ × β₂) × (β₁ × α₂) => ((x.1.1, x.2.1), (x.2.2, x.1.2)))
    (fun x : (α₁ × β₂) × (β₁ × α₂) => ((x.1.1, x.2.1), (x.2.2, x.1.2))))

/-- The trace norm minus one, using the positive matrix square root. -/
def negativity (r : Matrix α α ℂ) : ℝ :=
  (trace (CFC.sqrt (r * rᴴ))).re - 1

/-- Failure of CPTP factorization through the input A marginal. -/
def IsSignallingBA (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) : Prop :=
  ¬ ∃ t : QuantumChannel α₁ α₂, ∀ x : Matrix (α₁ × β₁) (α₁ × β₁) ℂ,
    partialTraceRight (p.toCompletelyPositiveMap x) =
      t.toCompletelyPositiveMap (partialTraceRight x)

private def conditionalMap (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) : Matrix β₁ β₁ ℂ →ₗ[ℂ] Matrix α₂ α₂ ℂ where
  toFun x := partialTraceRight (p.toCompletelyPositiveMap (vecMulVec a (star a) ⊗ₖ x))
  map_add' := by
    intro x y
    rw [Matrix.kronecker_add, map_add, partialTraceRight_add]
  map_smul' := by
    intro z x
    ext i j
    change (∑ k, p.toCompletelyPositiveMap (vecMulVec a (star a) ⊗ₖ (z • x))
      (i, k) (j, k)) = z * ∑ k, p.toCompletelyPositiveMap
        (vecMulVec a (star a) ⊗ₖ x) (i, k) (j, k)
    rw [Matrix.kronecker_smul, map_smul]
    exact Finset.mul_sum.symm

private def IsReplacement (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∃ σ : Matrix β β ℂ, ∀ x, e x = trace x • σ

private theorem signalling_dichotomy [Nonempty α₁] [Nonempty β₁]
    [Nonempty α₂] [Nonempty β₂]
    (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) (hp : IsSignallingBA p) :
    ∃ a : α₁ → ℂ, star a ⬝ᵥ a = 1 ∧ ¬ IsReplacement (conditionalMap p a) := by
  sorry

private theorem pdm_reduction (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) :
    pdmBA p a b = (1 / 2 : ℂ) •
      (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *
        cjMatrix (conditionalMap p a) +
       cjMatrix (conditionalMap p a) *
        ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ))) := by
  sorry

private theorem orthogonal_pair [Nonempty α]
    (e : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (he : ¬ IsReplacement e) :
    ∃ b c : α → ℂ, star b ⬝ᵥ b = 1 ∧ star c ⬝ᵥ c = 1 ∧
      star b ⬝ᵥ c = 0 ∧ e (vecMulVec c (star b)) ≠ 0 := by
  sorry

private theorem pdm_hermitian_trace (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b : β₁ → ℂ) (ha : star a ⬝ᵥ a = 1)
    (hb : star b ⬝ᵥ b = 1) :
    (pdmBA p a b).IsHermitian ∧ trace (pdmBA p a b) = 1 := by
  sorry

private theorem negative_minor (p : QuantumChannel (α₁ × β₁) (α₂ × β₂))
    (a : α₁ → ℂ) (b c : β₁ → ℂ)
    (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) (hc : star c ⬝ᵥ c = 1)
    (hbc : star b ⬝ᵥ c = 0)
    (he : conditionalMap p a (vecMulVec c (star b)) ≠ 0)
    (hr : pdmBA p a b = (1 / 2 : ℂ) •
      (((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)) *
        cjMatrix (conditionalMap p a) +
       cjMatrix (conditionalMap p a) *
        ((vecMulVec b (star b)) ⊗ₖ (1 : Matrix α₂ α₂ ℂ)))) :
    ¬ (pdmBA p a b).PosSemidef := by
  sorry

private theorem negativity_of_not_posSemidef (r : Matrix α α ℂ)
    (hr : r.IsHermitian) (ht : trace r = 1) (hn : ¬ r.PosSemidef) :
    0 < negativity r := by
  sorry

/-- A signalling channel admits a pure product input with strictly positive PDM negativity. -/
theorem result [Nonempty α₁] [Nonempty β₁] [Nonempty α₂] [Nonempty β₂]
    (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) (hp : IsSignallingBA p) :
    ∃ (a : α₁ → ℂ) (b : β₁ → ℂ), star a ⬝ᵥ a = 1 ∧ star b ⬝ᵥ b = 1 ∧
      0 < negativity (pdmBA p a b) := by
  obtain ⟨a, ha, he⟩ := signalling_dichotomy p hp
  obtain ⟨b, c, hb, hc, hbc, hcross⟩ := orthogonal_pair (conditionalMap p a) he
  obtain ⟨hr, ht⟩ := pdm_hermitian_trace p a b ha hb
  exact ⟨a, b, ha, hb, negativity_of_not_posSemidef _ hr ht
    (negative_minor p a b c ha hb hc hbc hcross (pdm_reduction p a b))⟩

end D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
