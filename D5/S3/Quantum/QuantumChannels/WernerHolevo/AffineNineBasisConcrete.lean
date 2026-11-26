/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasisConcrete
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasisConcrete
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The order-nine finite labeling and affine line decomposition give explicit orthogonal unitary bases in every order 9^d for d at least two. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineBasis
import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineFinite

/-!
# The concrete affine construction over F₉

The local matrix and the nine-block labeling come from the finite
construction. This module instantiates the all-exponents theorem.
-/

open Module

namespace AffineNine

noncomputable section

open AffineNineFinite (F9 LabelGroup)

/-- The checked local unitary supplied by the finite construction. -/
def f9Local : FlatHollow F9 where
  matrix := AffineNineFinite.C
  unitary := AffineNineFinite.C_unitary
  symm := AffineNineFinite.C_isSymm
  diag := AffineNineFinite.C_diag
  normSq := AffineNineFinite.C_offDiag_normSq

/-- The checked endpoint sums on the nine base blocks. -/
def f9Labeling : EdgeLabeling F9 F9 LabelGroup where
  label := AffineNineFinite.vertexLabel
  edgeEquiv := AffineNineFinite.edgeLabelEquiv
  edgeEquiv_apply := AffineNineFinite.edgeLabelEquiv_blockEdge

/-- Every complex symmetric matrix space of order 9^d, d ≥ 2, admits a
Hilbert–Schmidt orthogonal unitary basis. -/
theorem exists_f9Basis (d : ℕ) (hd : 2 ≤ d) :
    ∃ b : Basis (Fin ((9 ^ d + 1).choose 2)) ℂ (symmetric (Fin (9 ^ d))),
      (∀ i, (b i : Matrix (Fin (9 ^ d)) (Fin (9 ^ d)) ℂ) ∈
        Matrix.unitaryGroup (Fin (9 ^ d)) ℂ) ∧
      ∀ i j, hs (b i : Matrix (Fin (9 ^ d)) (Fin (9 ^ d)) ℂ)
        (b j : Matrix (Fin (9 ^ d)) (Fin (9 ^ d)) ℂ) =
        if i = j then ((9 ^ d : ℕ) : ℂ) else 0 :=
  exists_affineBasis f9Local f9Labeling AffineNineFinite.two_ne_zero AffineNineFinite.card_f9 d hd

end
end AffineNine
