/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualResiduePairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualResiduePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The P48q restricted-dual signed residue pairs with a reflected native residue. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualPairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueReflection
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates nativeField)
open P48qFieldCarrierTransport (stripResidueOn)
open P48qNativeCurrentLocality (stripResidue stripResidue_coeff)
open P48qNativeDualCoefficients (bpzTerm)
open P48qNativeDualLinearField (dualField)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open SignedFieldResidueLocality (residueField)
open SignedFieldResidueReflection (residue_pair_anti_transpose)
open StateFieldResidueReconstruction (epsilon)

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

/-- The left-hand signed residue of the dual fields pairs with the reflected
native residue of the two finite BPZ sums. -/
theorem gradedPairing_dualField_residue (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b)
    (s t p q n : ℤ) (f : RestrictedDual) (v : State) :
    let pNative (i : ℕ) : ℤ := -p + 2 * (d : ℤ) - (i : ℤ) - 2 - n
    let qNative (l : ℕ) : ℤ := -q + 2 * (e : ℤ) - (l : ℤ) - 2 - n
    let A : VertexOperator ℂ State := (-1 : ℂ) ^ d •
      ∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ •
        stripResidue (s - 3 * pNative i) (nativeField ((L₁ ^ i) a))
    let B : VertexOperator ℂ State := (-1 : ℂ) ^ e •
      ∑ l ∈ Finset.range (e + 1), (l.factorial : ℂ)⁻¹ •
        stripResidue (t - 3 * qNative l) (nativeField ((L₁ ^ l) b))
    gradedPairing ((((residueField 1 n
      (stripResidueOn (-s - 3 * p) (dualField a))
      (stripResidueOn (-t) (dualField b))).operator)[[q]]) f) v =
      -epsilon n * gradedPairing f ((((residueField 1 n A B).operator)[[0]]) v) := by
  classical
  intro pNative qNative A B
  have hMode (c : NativeStates) (weight : ℕ) (hc : L₀ c = (weight : ℂ) • c)
      (r u : ℤ) (nativeIndex : ℕ → ℤ) (k k' : ℤ)
      (hIndex : ∀ i : ℕ,
        -(3 * (-k - 1) + u) - 6 * (weight : ℤ) + 3 * (i : ℤ) =
          3 * (-k' - 1) + (r - 3 * nativeIndex i))
      (g : RestrictedDual) (x : State) :
      gradedPairing (((stripResidueOn u (dualField c))[[k]]) g) x =
        gradedPairing g ((((-1 : ℂ) ^ weight •
          ∑ i ∈ Finset.range (weight + 1), (i.factorial : ℂ)⁻¹ •
            stripResidue (r - 3 * nativeIndex i) (nativeField ((L₁ ^ i) c)))[[k']]) x) := by
    have hDualMode : (stripResidueOn u (dualField c))[[k]] =
        HVertexOperator.coeff (dualField c) (3 * (-k - 1) + u) := rfl
    rw [hDualMode, gradedPairing_dualField_coeff c weight hc]
    apply congrArg (gradedPairing g)
    simp only [VertexOperator.ncoeff_apply, map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, stripResidue_coeff, bpzTerm, hIndex]
  have hA (k : ℤ) (g : RestrictedDual) (x : State) :
      gradedPairing (((stripResidueOn (-s - 3 * p) (dualField a))[[k]]) g) x =
        gradedPairing g ((A[[n - k]]) x) := by
    refine hMode a d ha s (-s - 3 * p) pNative k (n - k) ?_ g x
    intro i
    dsimp only [pNative]
    omega
  have hB (k : ℤ) (g : RestrictedDual) (x : State) :
      gradedPairing (((stripResidueOn (-t) (dualField b))[[k]]) g) x =
        gradedPairing g ((B[[q + 0 + n - k]]) x) := by
    refine hMode b e hb t (-t) qNative k (q + 0 + n - k) ?_ g x
    intro l
    dsimp only [qNative]
    omega
  exact residue_pair_anti_transpose n q 0 A B
    (stripResidueOn (-s - 3 * p) (dualField a)) (stripResidueOn (-t) (dualField b))
    gradedPairing hA hB f v

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
