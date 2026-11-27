/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeComplementOddDetection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeComplementOddDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native right-skew modes jointly detect odd untwisted Leech states. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOFullIterate

/-! Native BBO Jacobi and the weight-two vacuum coefficient detect the odd
untwisted carrier through the literal native right-skew modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementOddDetection

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier)
open MixedIntertwiner (normalizedCoefficient normalizedCoefficient_homogeneous_truncation
  weight_two_normalized_vacuum_witness)
open NativeBBOCoefficientTransport (P Q bboDefect_eq_zero_iff_jacobi)
open NativeBBOFullIterate (bboDefect_eq_zero)
open NativeOddTwistedIntertwiner (OddCarrier TwistedOdd leechUnit oddMode)
open OriginalFourMChargeCoset (originalI originalI_three_eq_vacuum_smul)

local notation "ℒ" => leechData

/- proof_shape: content
   admission_basis: escape-witness
   escape_witness: Under common Q-vanishing, the signed BBO Jacobi law at
   labels (-2, 0, 3) reduces by weight truncation to a nonzero vacuum scalar
   times the odd state, forcing that state to vanish. -/
set_option maxHeartbeats 1000000 in
/-- The common kernel of the literal native right-skew modes on the odd
untwisted carrier is zero. -/
theorem eq_zero_of_forall_Q_eq_zero (o : OddCarrier ℒ)
    (hQ : ∀ (b : TwistedOdd) (n : ℤ), Q b n o = 0) : o = 0 := by
  obtain ⟨vac, b, c, hvac, hb, hc, _, hscalar⟩ :=
    weight_two_normalized_vacuum_witness ℒ leechUnit leech_spec.1 leech_spec.2.2.1
  have law := (bboDefect_eq_zero_iff_jacobi b c o (-2) 0 3).mp (by
    rw [bboDefect_eq_zero b c (-2) 0 3, LinearMap.zero_apply])
  change
    -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose ((3 : ℤ) : ℂ) j) •
      P b (0 + 3 - j) (Q c (-2 + j) o)) +
    (∑ᶠ j : ℕ, ((-1 : ℂ)^((3 : ℤ) + j) * Ring.choose ((3 : ℤ) : ℂ) j) •
      P c (-2 + 3 - j) (Q b (0 + j) o)) = _ at law
  simp only [hQ, map_zero, smul_zero, finsum_zero, add_zero] at law
  rw [finsum_eq_single _ 0] at law
  · have hmode :
        oddMode ℒ (originalI ℒ leechUnit leech_spec.2.2.1 3 b c) (-1) o =
          normalizedCoefficient ℒ leechUnit 3 b c 0 vac • o := by
      rw [originalI_three_eq_vacuum_smul ℒ leechUnit leech_spec.2.2.1 leech_spec.1
        b c hb hc vac hvac]
      apply Subtype.ext
      change ((LatticeAllStateField.Y ℒ
        (normalizedCoefficient ℒ leechUnit 3 b c 0 vac • LatticeAllStateField.vacuum ℒ))[[-1]])
          o.val = normalizedCoefficient ℒ leechUnit 3 b c 0 vac • o.val
      rw [map_smul, LatticeAllStateField.stateField_vacuum, map_smul VertexOperator.ncoeff,
        Pi.smul_apply, LatticeAllStateField.identity_modes]
      simp
    have hz : normalizedCoefficient ℒ leechUnit 3 b c 0 vac • o = 0 := by
      calc
        normalizedCoefficient ℒ leechUnit 3 b c 0 vac • o = -(0 : OddCarrier ℒ) := by
          simpa only [Nat.cast_zero, add_zero, sub_zero, Ring.choose_zero_right, one_smul,
            show (-2 : ℤ) + 1 = -1 by decide, hmode] using law.symm
        _ = 0 := by
          apply Subtype.ext
          simp only [Submodule.coe_neg, Submodule.coe_zero, neg_zero]
    exact (smul_eq_zero.mp hz).resolve_left hscalar
  · intro j hj
    have htail : originalI ℒ leechUnit leech_spec.2.2.1 (3 + (j : ℤ)) b c = 0 := by
      change DirectSum.toModule ℂ ℤ (FixedCarrier ℒ) _
        (normalizedCoefficient ℒ leechUnit (3 + (j : ℤ)) b c) = 0
      rw [normalizedCoefficient_homogeneous_truncation ℒ leechUnit leech_spec.2.2.1
        leech_spec.1 2 2 _ b c hb hc (by omega), map_zero]
    have hmode (n : ℤ) : oddMode ℒ (0 : FixedCarrier ℒ) n o = 0 := by
      apply Subtype.ext
      change ((LatticeAllStateField.Y ℒ 0)[[n]]) o.val = 0
      simp
    rw [htail, hmode, smul_zero]

/-- Every nonzero odd untwisted state has a nonzero coefficient under a
literal native right-skew field. -/
theorem exists_Q_ne_zero (o : OddCarrier ℒ) (ho : o ≠ 0) :
    ∃ (b : TwistedOdd) (n : ℤ), Q b n o ≠ 0 := by
  by_contra! h
  exact ho (eq_zero_of_forall_Q_eq_zero o h)

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementOddDetection.exists_Q_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_Q_ne_zero

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementOddDetection
