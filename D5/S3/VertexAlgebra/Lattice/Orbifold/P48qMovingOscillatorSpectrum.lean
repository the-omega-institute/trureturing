/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingOscillatorSpectrum
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The concrete moving oscillator spectrum in the normalized P48q dual bases. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverSixteenPairSpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairingDraft

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverSixteenPairSpectrum

open MvPolynomial Module.End
open ThirdCoverIntegerFactor ThirdCoverComplement
open ThirdEigenspacePairing

/-- In the actual Nebe bases the same index labels a dual pair, so its two
residue grids give one lifted fractional oscillator. -/
theorem p48q_fractionalLZero_spectrum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    (∀ i j : Fin 16,
      p48qForm (p48qBasis hζ i) (p48qOppositeBasis hζ j) = if i = j then 1 else 0) ∧
    (∀ (i : Fin 16) (Q : ComplementFock) (R : MvPolynomial (OtherVariable i) ℂ),
      pairLZero i (rename (Prod.mk i) Q * rename Subtype.val R) =
        rename (Prod.mk i) (fractionalVirasoro 0 Q) * rename Subtype.val R) ∧
    (∀ (d : Occupation) (a : ℂ), fractionalLZero (monomial d a) =
      ((16 / 9 : ℂ) + (totalOccupationEnergy d : ℂ) / 3) • monomial d a) ∧
    IsLeast {x : ℝ | ∃ P : MovingFock, P ≠ 0 ∧ fractionalLZero P = (x : ℂ) • P} (16 / 9) ∧
    fractionalLZero.eigenspace (16 / 9 : ℂ) =
      Submodule.span ℂ ({(1 : MovingFock)} : Set MovingFock) ∧
    Module.finrank ℂ (fractionalLZero.eigenspace (16 / 9 : ℂ)) = 1 :=
  ⟨p48q_pair_bases hζ, pairLZero_separated, fractionalLZero_monomial,
    fractionalLZero_minimum, fractionalLZero_ground_eigenspace, fractionalLZero_ground_finrank⟩

#print axioms p48q_fractionalLZero_spectrum

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverSixteenPairSpectrum
