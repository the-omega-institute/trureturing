/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source-coupled theta transformation in the original mod-two charge sectors. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantShiftedTheta
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDiscriminantCharge
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

/-! # Shifted theta series of the original four-point charge sectors -/

set_option autoImplicit false

open Matrix Complex
open scoped BigOperators
noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMShiftedTheta

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open LatticeDiscriminantTheta LatticeDiscriminantShiftedTheta LatticeDiscriminantWeil
open OriginalFourMDiscriminantCharge

private theorem doubled_sector_pairRaw (D : LatticeData) (hu : IsUnit D.G.det) (q a : Charge D) :
    pairRaw (doubled D) (D.G *ᵥ q) (D.G *ᵥ a) = (bilinear D q a : ℚ) / 2 := by
  rw [pairRaw, dualVector_gram_image D hu]
  simp only [dotProduct, Matrix.mulVec, bilinear,
    Int.cast_sum, Int.cast_mul, mul_assoc, ← Finset.mul_sum]
  ring_nf
  rw [Finset.sum_mul]


open OriginalFourMChargeCoset
open LatticeHalfFockChargedMonodromy
open LatticeHalfFockChargedTensorCoefficients (chargeNorm)
open private pairing_mk from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

private theorem phase_half_integer (k : ℤ) :
    phase ((((k : ℚ) / 2) : ℚ) : QmodZ) = paritySign k := by
  rw [phase_mk]
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      (((k : ℚ) / 2 : ℚ) : ℂ) = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I, neg_one_zpow_eq_ite]
  rfl

/-- The doubled-Gram (T)-phase in the Weil action is exactly the
quadratic sign of the original ground state sector. -/
theorem quadratic_phase_reduceCharge (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal (doubled D)).PosDef) (q : Charge D) :
    phase (quadraticClass (doubled D) (sectorEquiv D hu (reduceCharge D q))) =
      quadraticSign D (reduceCharge D q) := by
  rw [sectorEquiv_reduceCharge, quadraticClass_mk _ hD,
    doubled_sector_pairRaw D hu, quadraticSign_integral]
  have he := norm_even D q
  change Even (bilinear D q q) at he
  obtain ⟨m, hm⟩ := he
  have hm' : (m + m) / 2 = m := by omega
  rw [hm, hm']
  have hhalf : (((m + m : ℤ) : ℚ) / 2) / 2 = (m : ℚ) / 2 := by
    push_cast
    ring
  rw [hhalf, phase_half_integer]

/-- The doubled-Gram Fourier phase on the original two charge sectors is
the same sign as in the original ground exchange identities. -/
theorem pairing_phase_reduceCharge (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal (doubled D)).PosDef) (q a : Charge D) :
    phase (pairing (doubled D) (sectorEquiv D hu (reduceCharge D q))
      (sectorEquiv D hu (reduceCharge D a))) =
      fourierSign D (reduceCharge D q) (reduceCharge D a) := by
  rw [sectorEquiv_reduceCharge, sectorEquiv_reduceCharge, pairing_mk _ hD,
    doubled_sector_pairRaw D hu, phase_half_integer]
  unfold fourierSign
  rw [← mod_two_cocycle_symmetrization, cocycle_reduction, cocycle_reduction]
  change paritySign (bilinear D q a) =
    complexSign ((lowerCocycleExponent D q a : ZMod 2) + (lowerCocycleExponent D a q : ZMod 2))
  rw [← Int.cast_add, integral_cocycle_symmetrization, complexSign_integral]


private theorem doubled_gramReal (D : LatticeData) :
    gramReal (doubled D) = (2 : ℝ) • gramReal D := by
  ext i j
  change ((2 * D.G i j : ℤ) : ℝ) = 2 * (D.G i j : ℝ)
  push_cast
  rfl

private theorem doubled_posDef (D : LatticeData) (hD : (gramReal D).PosDef) :
    (gramReal (doubled D)).PosDef := by
  rw [doubled_gramReal]
  exact hD.smul (by norm_num : (0 : ℝ) < 2)

private theorem reduction_surjective (D : LatticeData) :
    Function.Surjective (reduceCharge D) := by
  intro a
  exact ⟨fun i => (a i).val, funext fun i => by simp [reduceCharge]⟩

private theorem pairing_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal (doubled D)).PosDef) (a b : ModTwoCharge D) :
    pairingCharacter (doubled D) hD (sectorEquiv D hu a) (sectorEquiv D hu b) =
      fourierSign D a b := by
  obtain ⟨q, rfl⟩ := reduction_surjective D a
  obtain ⟨r, rfl⟩ := reduction_surjective D b
  exact pairing_phase_reduceCharge D hu hD q r

/-- The original theta sector, indexed by the mod-two charge. -/
def chargeTheta (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (τ : ℂ) (z : Fin D.rank → ℂ) : ℂ :=
  shiftedTheta (doubled D) (sectorEquiv D hu a) τ z

private theorem card_doubled (D : LatticeData) (hu : IsUnit D.G.det) :
    Nat.card (Discriminant (doubled D)) = 2 ^ D.rank := by
  rw [Nat.card_congr (sectorEquiv D hu).symm.toEquiv, Nat.card_eq_fintype_card]
  simp [ModTwoCharge, ZMod.card]

private theorem sqrt_det_doubled (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal (doubled D)).PosDef) (hr : D.rank = 24) :
    (Real.sqrt (gramReal (doubled D)).det : ℂ) = 2 ^ (12 : ℕ) := by
  rw [← (dual_lattice_realization (doubled D) hD).2.2.1, card_doubled D hu, hr]
  have hs : Real.sqrt (((2 ^ 24 : ℕ) : ℝ)) = (2 : ℝ) ^ (12 : ℕ) := by
    rw [← Real.sqrt_sq (show 0 ≤ (2 : ℝ) ^ (12 : ℕ) by positivity)]
    norm_num
  rw [hs]
  norm_num

/-- Real-source S inversion on the original charge sectors, with the
original Fourier signs and the rank-24 determinant factor. -/
theorem chargeTheta_real_S (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (a : ModTwoCharge D) (τ : ℂ) (hτ : 0 < τ.im) (v : Fin D.rank → ℝ) :
    chargeTheta D hu a τ (fun i => (v i : ℂ)) =
      ((2 : ℂ) ^ (12 : ℕ))⁻¹ * ((-Complex.I * τ) ^ (12 : ℕ))⁻¹ *
      Complex.exp (-Real.pi * Complex.I / τ *
        sourceQuadratic (gramReal (doubled D)) (fun i => (v i : ℂ))) *
      ∑ b : ModTwoCharge D, fourierSign D a b *
        chargeTheta D hu b (-1 / τ) (τ⁻¹ • fun i => (v i : ℂ)) := by
  classical
  let hd := doubled_posDef D hD
  letI : Fact (gramReal (doubled D)).PosDef := ⟨hd⟩
  letI : Fintype (Discriminant (doubled D)) := Fintype.ofFinite _
  have hf := shiftedTheta_real_S (doubled D) hd (sectorEquiv D hu a) τ hτ v
  have hpow : (-(((doubled D).rank : ℕ) : ℂ) / 2) = -(↑(12 : ℕ) : ℂ) := by
    change -(D.rank : ℂ) / 2 = _
    rw [hr]
    norm_num
  dsimp only at hf
  rw [sqrt_det_doubled D hu hd hr, hpow, Complex.cpow_neg, Complex.cpow_natCast] at hf
  unfold chargeTheta
  rw [hf]
  congr 1
  rw [← (sectorEquiv D hu).toEquiv.sum_comp
    (fun b => pairingCharacter (doubled D) hd (sectorEquiv D hu a) b *
      shiftedTheta (doubled D) b (-1 / τ) (τ⁻¹ • fun i => (v i : ℂ)))]
  exact Finset.sum_congr rfl (fun b _ => by
    change pairingCharacter (doubled D) hd (sectorEquiv D hu a) (sectorEquiv D hu b) * _ = _
    rw [pairing_sign D hu hd]
    rfl)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMShiftedTheta
