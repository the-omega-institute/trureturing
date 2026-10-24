/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualChosenFormSymmetry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualChosenFormSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.TensorProduct]
   utility: none
   digest: The original chosen actual tensor bilinear form is symmetric. -/

import D5.S3.Quantum.Algebra.InvariantFormProportionality
import D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing
import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint

/-! Every original GroundPairing is compared with the symmetric witness on the
unchanged selected representation. The old actualForm and Classical.choice
are preserved. Integral unimodular lattices of rank zero and indefinite
signature remain in scope. Classical Schur duality; no novelty claim. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry
open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open InvariantPairing SymmetricPairing OperatorAlgebra ActualChargedAdjoint
open D5.S3.Quantum.Algebra.InvariantFormProportionality
open SignedOscillatorWick

/-- Unique nonzero scalar comparison on the EXACT original carrier and
representation. This consumed helper specializes the substantive generic
duality argument; it does not supply a new representation or pairing.

proof_shape: bind-only; consumed helper, not independent substantive credit.
consumer: ground_pairing_isSymm.
-/
private theorem ground_pairings_proportional (D : LatticeData) (hu : IsUnit D.G.det)
    (B C : GroundPairing D hu) :
    ∃! c : ℂ, c ≠ 0 ∧ C.form = c • B.form := by
  classical
  have selected := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  let A := Classical.choice (actual_operator_algebra D hu
    (groundRank D hu) selected.1 (groundRepresentation D hu) selected.2.2.1)
  have scalar_commutant (T : Module.End ℂ (ActualGround D hu))
      (hT : ∀ g : Extension D ⧸ K D,
        T * groundRepresentation D hu g = groundRepresentation D hu g * T) :
      ∃ c : ℂ, T = c • (1 : Module.End ℂ (ActualGround D hu)) := by
    apply (A.scalar_commutant T).mp
    intro a
    exact hT (chargeLift D a)
  -- ActualGround = (Half (groundRank D hu) → ℂ), with inhabited index 0.
  -- Thus its existing Nontrivial and FiniteDimensional instances apply even
  -- at rank zero; equivalently its proved dimension is 2^(D.rank/2) > 0.
  have hB0 : B.form ≠ 0 := B.nondegenerate.ne_zero
  have hC0 : C.form ≠ 0 := C.nondegenerate.ne_zero
  obtain ⟨c, hc, unique⟩ := invariant_forms_proportional_of_scalar_commutant
    (groundRepresentation D hu) B.form C.form B.nondegenerate hB0
    B.invariant C.invariant scalar_commutant
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hC0
    rw [hc, hzero, zero_smul]
  refine ⟨c, ⟨hc0, hc⟩, ?_⟩
  intro d hd
  exact unique d hd.2

/-- EVERY original GroundPairing is symmetric. Existence of a symmetric
witness is used only after the original-form proportionality is proved.
The theorem also applies to the old Classical.choice in ActualChargedAdjoint.

proof_shape: bind-only; consumed helper with scalar symmetry transport.
consumer: ActualChosenFormSymmetry.actualForm_isSymm.
Substantive generic content is in InvariantFormProportionality.
Classical Schur consequence; no literature novelty claim.
-/
private theorem ground_pairing_isSymm (D : LatticeData) (hu : IsUnit D.G.det)
    (G : GroundPairing D hu) : G.form.IsSymm := by
  classical
  obtain ⟨S⟩ := actual_symmetric_ground_pairing D hu
  obtain ⟨c, hc, _⟩ := ground_pairings_proportional D hu S.toGroundPairing G
  have hform : G.form = c • S.form := hc.2
  constructor
  intro u v
  rw [hform]
  change c * S.form u v = c * S.form v u
  rw [S.symmetric.eq u v]

/-- Symmetry of the unchanged original form and its exact old choice.
The private comparison helpers above are consumed here; no pairing is replaced.
The proof uses Mathlib's tensor symmetry after deriving symmetry of every
original ground pairing from the scalar commutant and symmetric witness. -/
theorem actualForm_isSymm (D : LatticeData) (hu : IsUnit D.G.det) :
    (ActualChargedAdjoint.actualForm D hu).IsSymm := by
  classical
  let G : GroundPairing D hu := Classical.choice (actual_ground_pairing D hu)
  have hG : G.form.IsSymm := ground_pairing_isSymm D hu G
  change LinearMap.BilinForm.IsSymm ((wick D).tmul G.form)
  apply LinearMap.BilinForm.isSymm_iff.mpr
  exact LinearMap.IsSymm.tmul
    (LinearMap.BilinForm.isSymm_iff.mp ⟨wick_symmetric D⟩)
    (LinearMap.BilinForm.isSymm_iff.mp hG)

#print axioms actualForm_isSymm
end D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry
end
