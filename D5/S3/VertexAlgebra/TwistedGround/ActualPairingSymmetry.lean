/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.Properties]
   utility: none
   digest: Symmetry of the unchanged selected tensor pairing from the actual scalar commutant. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.BilinearForm.Properties
import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
import D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing

/-!
The comparison with an existing symmetric ground form takes place on the
original selected representation. Its scalar commutant forces every invariant
ground pairing, including the original Classical.choice, to be symmetric.
The definition of actualForm and both tensor factors are unchanged.
This is classical invariant-form theory, with no literature novelty claim.
It does not establish ordered-kernel exchange, three-twisted crossing, an
extension VOA, Monster symmetry, string theory or AdS/CFT.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open InvariantPairing SymmetricPairing OperatorAlgebra
open ActualChargedAdjoint SignedOscillatorWick

open private selected_central from D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
open private selectedGroundPairing from
  D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private wick_symmetric from D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick

private theorem ground_pairing_symmetric (D : LatticeData) (hu : IsUnit D.G.det)
    (B : GroundPairing D hu) : B.form.IsSymm := by
  obtain ⟨S⟩ := actual_symmetric_ground_pairing D hu
  let A := B.form.symmCompOfNondegenerate S.form S.nondegenerate
  have evaluation (x y : ActualGround D hu) : S.form (A x) y = B.form x y :=
    B.form.symmCompOfNondegenerate_left_apply S.nondegenerate y x
  have commutes (g : Extension D ⧸ K D) :
      A * groundRepresentation D hu g = groundRepresentation D hu g * A := by
    apply LinearMap.ext
    intro x
    apply (S.form.toDual S.nondegenerate).injective
    apply LinearMap.ext
    intro y
    change S.form (A (groundRepresentation D hu g x)) y =
      S.form (groundRepresentation D hu g (A x)) y
    calc
      S.form (A (groundRepresentation D hu g x)) y =
          B.form (groundRepresentation D hu g x) y := evaluation _ _
      _ = B.form x (groundRepresentation D hu g⁻¹ y) := by
        conv_lhs => rhs; rw [← (groundRepresentation D hu).self_inv_apply g y]
        exact B.invariant g x _
      _ = S.form (A x) (groundRepresentation D hu g⁻¹ y) := (evaluation _ _).symm
      _ = S.form (groundRepresentation D hu g (A x)) y := by
        conv_rhs => rhs; rw [← (groundRepresentation D hu).self_inv_apply g y]
        exact (S.invariant g (A x) _).symm
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have central : groundRepresentation D hu (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (ActualGround D hu)) := by
    simpa [complexSign] using selected_central D hu 1
  obtain ⟨algebra⟩ := actual_operator_algebra D hu (groundRank D hu) rank_eq
    (groundRepresentation D hu) central
  obtain ⟨c, scalar⟩ := (algebra.scalar_commutant A).mp
    (fun charge => commutes (chargeLift D charge))
  constructor
  intro x y
  calc
    B.form x y = S.form (A x) y := (evaluation _ _).symm
    _ = c * S.form x y := by rw [scalar]; simp
    _ = c * S.form y x := by rw [S.symmetric.eq]
    _ = S.form (A y) x := by rw [scalar]; simp
    _ = B.form y x := evaluation _ _

/-- Symmetry of the literal original selected form on the original ActualTensor. -/
theorem actualForm_symmetric (D : LatticeData) (hu : IsUnit D.G.det) :
    (ActualChargedAdjoint.actualForm D hu).IsSymm := by
  have ground := ground_pairing_symmetric D hu (selectedGroundPairing D hu)
  exact LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.IsSymm.tmul ⟨wick_symmetric D⟩ ⟨ground.eq⟩)

#print axioms actualForm_symmetric

end D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
