/- GID: D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockGroundProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The chosen actual quotient representation realizes the native lattice cocycle product. -/


import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeActualProductKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient

noncomputable section

private theorem actual_central_sign (D : LatticeData) (hu : IsUnit D.G.det) :
    groundRepresentation D hu (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (ActualGround D hu)) :=
  (Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.2.1

private theorem actual_natural_sign (D : LatticeData) (hu : IsUnit D.G.det) (degree : ℕ) :
    groundRepresentation D hu (QuotientGroup.mk (⟨(degree : F₂), 0⟩ : Extension D)) =
      complexSign (degree : F₂) • (1 : Module.End ℂ (ActualGround D hu)) := by
  induction degree with
  | zero =>
    change groundRepresentation D hu (1 : Extension D ⧸ K D) = _
    simp [sign_zero]
  | succ degree inductionProof =>
    have product : (⟨((degree + 1 : ℕ) : F₂), 0⟩ : Extension D) =
        (⟨(degree : F₂), 0⟩ : Extension D) * (⟨1, 0⟩ : Extension D) := by
      apply SignExtension.ext
      · change ((degree + 1 : ℕ) : F₂) = (degree : F₂) + 1 + integralCocycle D 0 0
        simp
      · change (0 : Charge D) = 0 + 0
        simp
    rw [product, QuotientGroup.mk_mul, map_mul, inductionProof, actual_central_sign]
    rw [← neg_one_smul ℂ (1 : Module.End ℂ (ActualGround D hu)),
      smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
    rw [Nat.cast_add, Nat.cast_one, complexSign_add, sign_one]

private theorem actual_sign (D : LatticeData) (hu : IsUnit D.G.det) (sign : F₂) :
    groundRepresentation D hu (QuotientGroup.mk (⟨sign, 0⟩ : Extension D)) =
      complexSign sign • (1 : Module.End ℂ (ActualGround D hu)) := by
  simpa only [ZMod.natCast_zmod_val] using actual_natural_sign D hu sign.val

theorem ground_action_product (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) :
    groundAction D hu left * groundAction D hu right =
      epsilon D left right • groundAction D hu (left + right) := by
  have product : (⟨0, left⟩ : Extension D) * (⟨0, right⟩ : Extension D) =
      (⟨integralCocycle D left right, 0⟩ : Extension D) *
        (⟨0, left + right⟩ : Extension D) := by
    apply SignExtension.ext
    · change 0 + 0 + integralCocycle D left right =
        integralCocycle D left right + 0 + integralCocycle D 0 (left + right)
      simp
    · change left + right = 0 + (left + right)
      simp
  unfold groundAction groundLift
  rw [← map_mul, ← QuotientGroup.mk_mul, product, QuotientGroup.mk_mul,
    map_mul, actual_sign, smul_mul_assoc, one_mul]
  change complexSign (lowerCocycleExponent D left right : F₂) • _ = _
  simp only [complexSign_integral, epsilon]

/-- Exchange in the same chosen actual ground module, derived from the cocycle
product above and the current integral-cocycle skew theorem. The physical
locality endpoint consumes this lemma; it is not a new locality assumption. -/
theorem ground_action_exchange (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) :
    groundAction D hu left * groundAction D hu right =
      paritySign (bilinear D left right) •
        (groundAction D hu right * groundAction D hu left) := by
  rw [ground_action_product, ground_action_product,
    LatticeActualGeneratorLocality.epsilon_skew D left right, smul_smul,
    add_comm right left]

end
end D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
