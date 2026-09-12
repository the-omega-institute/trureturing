/- GID: D5/S3/Weil/HolonomyBridge/OrbitReversalObservation
   generality: I
   mirror-B: D5/B/S3/Weil/HolonomyBridge/OrbitReversalObservation
   mirror-E: none(waiver:source-identification-bridge)
   anchors: []
   utility: none
   digest: The existing Weil orbit parity channels realize the hidden-idempotent classification of visible negation. -/

import D5.S3.Observer.Reversal.VisibleNegationLifts
import D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition

/-!
# The existing Weil channels as an actual reversal observation

This is a binding bridge, not a new parity theorem. `evenSpectralChannel`,
`oddSpectralChannel`, and the actual four-point orbit are imported unchanged.
The involution swaps the two spectral *samples*. It is not asserted to be
spatial reflection of the test function or physical time reversal.

In particular no arbitrary coefficient pair is asserted to be realizable by
one Weil test, and no prime-side bound or RH conclusion is inferred from the
algebraic classification. The original odd correction remains present.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.HolonomyBridge.OrbitReversalObservation

open D5.S3.Observer.Reversal.VisibleNegationLifts
open D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate BigOperators

/-- Exchange the actual pair of spectral readouts. -/
def pairSwap : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ) where
  toFun := Prod.swap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The frozen odd spectral channel, with its existing normalization. -/
def oddObservation : (ℂ × ℂ) →ₗ[ℝ] ℂ where
  toFun v := oddSpectralChannel v.1 v.2
  map_add' v w := by
    change ((v.1 + w.1) - (v.2 + w.2)) / 2 =
      (v.1 - v.2) / 2 + (w.1 - w.2) / 2
    ring
  map_smul' r v := by
    change (r • v.1 - r • v.2) / 2 = r • ((v.1 - v.2) / 2)
    simp only [Complex.real_smul]
    ring

private theorem swap_involutive : Function.Involutive pairSwap := by
  intro v
  rfl

private theorem odd_swap (v : ℂ × ℂ) : oddObservation (pairSwap v) = -oddObservation v := by
  change (v.2 - v.1) / 2 = -((v.1 - v.2) / 2)
  ring

/-- The hidden fixed part is exactly the existing even spectral channel. -/
theorem fixedPart_eq_even_channel (v : ℂ × ℂ) :
    (fixedPart pairSwap v).1 = evenSpectralChannel v.1 v.2 := by
  change (2 : ℝ)⁻¹ • (v.1 + v.2) = (v.1 + v.2) / (2 : ℂ)
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The same general lift theorem applies to the actual odd Weil readout.
Its entire fixed component is invisible to that readout. -/
theorem weil_visible_negation_lift :
    Function.Involutive pairSwap ∧
      (∀ v, oddObservation (pairSwap v) = -oddObservation v) ∧
      (∀ v, fixedPart pairSwap (fixedPart pairSwap v) = fixedPart pairSwap v) ∧
      (∀ v, oddObservation (fixedPart pairSwap v) = 0) := by
  exact ⟨swap_involutive, odd_swap,
    fixedPart_idempotent pairSwap swap_involutive,
    fixedPart_in_observation_kernel oddObservation pairSwap odd_swap⟩

/-- The source's actual off-line orbit has the same energy decomposition
in the reversal-observation coordinates. This consumes the original theorem. -/
theorem off_line_orbit_in_reversal_coordinates
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hConjugate : Z.conjugation n ≠ n)
    (hOffLine : (Z.zero n).re ≠ criticalAbscissa) :
    let v : ℂ × ℂ := (fourierLaplace g (Z.gamma n),
      fourierLaplace g (conj (Z.gamma n)))
    (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
      zeroSummand Z (convolutionSquare g) k).re =
      4 * (Z.multiplicity n : ℝ) * Complex.normSq ((fixedPart pairSwap v).1) -
      4 * (Z.multiplicity n : ℝ) * Complex.normSq (oddObservation v) := by
  dsimp only
  rw [fixedPart_eq_even_channel]
  exact (off_line_orbit_parity_decomposition Z g n hConjugate hOffLine).1

#print axioms pairSwap
#print axioms oddObservation
#print axioms fixedPart_eq_even_channel
#print axioms weil_visible_negation_lift
#print axioms off_line_orbit_in_reversal_coordinates

end D5.S3.Weil.HolonomyBridge.OrbitReversalObservation
