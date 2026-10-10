/- GID: D5/S3/VertexAlgebra/LatticeActualConformalWard
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualConformalWard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual conformal actions truncate before binomial weighting and satisfy every integer Ward law. -/

import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualStateDerivative

/-
Full integer Ward identities and actual state derivatives. Inner-state finite
support follows from released Sugawara-field truncation and its mode convention,
including negative Virasoro indices.
The state derivative is proved independently from the actual vacuum residue iterate.
See LatticeActualConformalState for primary sources and retained licenses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeActualConformalWard
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeSugawaraCurrents
open LatticeActualStateFieldCalculus LatticeActualConformalState
open LatticeSugawaraConformal FieldNormalProduct
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

theorem omega_ncoeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (j : ℤ) :
    ((Y D (omega D H))[[j]]) = sugawaraMode D H (j - 1) := by
  rw [← omega_modes, sub_add_cancel]

theorem omega_product (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Carrier D) (j : ℤ) :
    mu D (omega D H) j a = sugawaraMode D H (j - 1) a := by
  rw [mu, omega_ncoeff]

def wardTerm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (a : Carrier D) (m q : ℤ) (j : ℕ) : Module.End ℂ (Carrier D) :=
  integerBinomial (m + 1) j •
    ((Y D (sugawaraMode D H ((j : ℤ) - 1) a))[[m + q + 1 - j]])

/-- Full Ward commutator at all integer indices. No primary-state or energy
eigenvector premise is imposed: all higher conformal actions are retained. -/
theorem ward_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Carrier D) (m q : ℤ) :
    sugawaraMode D H m * ((Y D a)[[q]]) -
        ((Y D a)[[q]]) * sugawaraMode D H m =
      ∑ᶠ j : ℕ, wardTerm D H a m q j := by
  have h := mode_commutator D (omega D H) a (m + 1) q
  rw [omega_modes] at h
  convert h using 1
  apply finsum_congr
  intro j
  unfold wardTerm commutatorTerm
  rw [omega_product, show m + 1 + q - (j : ℤ) = m + q + 1 - j by omega]

end
end D5.S3.VertexAlgebra.LatticeActualConformalWard
