/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original mod-two charge as a doubled-Gram discriminant sector. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

/-! The literal doubled-Gram quotient uses the representative obtained
by applying the integral Gram automorphism to a charge. -/

set_option autoImplicit false

noncomputable section

open Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDiscriminantCharge

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open LatticeDiscriminantTheta

/-- Keep the original integral coordinates and double the Gram form. -/
abbrev doubled (D : LatticeData) : LatticeData where
  rank := D.rank
  G := (2 : ℤ) • D.G
  symmetric i j := by simp [D.symmetric i j]
  even_diagonal i := ⟨D.G i i, by simp [two_mul]⟩

private theorem gramMap_doubled (D : LatticeData) (n : Charge D) :
    gramMap (doubled D) n = D.G *ᵥ ((2 : ℤ) • n) := by
  change ((2 : ℤ) • D.G) *ᵥ n = _
  rw [smul_mulVec, mulVec_smul]

private theorem reduction_eq_iff (D : LatticeData) (a b : Charge D) :
    reduceCharge D a = reduceCharge D b ↔ ∃ n : Charge D, a - b = (2 : ℤ) • n := by
  constructor
  · intro h
    have hd (i : Fin D.rank) : (2 : ℤ) ∣ a i - b i := by
      have hi : (a i : ZMod 2) = (b i : ZMod 2) := congrFun h i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a i - b i) 2).1 (by simp [hi])
    choose n hn using hd
    exact ⟨n, funext hn⟩
  · rintro ⟨n, hn⟩
    funext i
    change (a i : ZMod 2) = (b i : ZMod 2)
    have hi : (a i - b i : ℤ) = 2 * n i := congrFun hn i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a i - b i) 2).2 ⟨n i, hi⟩
    exact sub_eq_zero.mp (by simpa using hz)

/-- The representatives G*a and G*b agree in the literal doubled-Gram
quotient exactly when the original charges have the same reduction. -/
theorem classOf_gram_eq_iff (D : LatticeData) (hu : IsUnit D.G.det) (a b : Charge D) :
    classOf (doubled D) (D.G *ᵥ a) = classOf (doubled D) (D.G *ᵥ b) ↔
      reduceCharge D a = reduceCharge D b := by
  have cancelGram (x y : Charge D) (h : D.G *ᵥ x = D.G *ᵥ y) : x = y := by
    have he := congrArg (fun v => D.G⁻¹ *ᵥ v) h
    simpa only [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] using he
  unfold classOf
  rw [Submodule.Quotient.eq, reduction_eq_iff, ← mulVec_sub]
  constructor
  · rintro ⟨n, hn⟩
    rw [gramMap_doubled] at hn
    exact ⟨n, cancelGram _ _ hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [gramMap_doubled, hn]⟩

private theorem reduction_lift (D : LatticeData) (a : ModTwoCharge D) :
    reduceCharge D (fun i => ((a i).val : ℤ)) = a := by
  funext i
  change (((a i).val : ℤ) : ZMod 2) = a i
  exact_mod_cast ZMod.natCast_zmod_val (a i)

private theorem reduction_surjective (D : LatticeData) : Function.Surjective (reduceCharge D) :=
  fun a => ⟨fun i => ((a i).val : ℤ), reduction_lift D a⟩

private def sectorMap (D : LatticeData) (a : ModTwoCharge D) : Discriminant (doubled D) :=
  classOf (doubled D) (D.G *ᵥ (fun i => ((a i).val : ℤ)))

private theorem sectorMap_apply (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
    sectorMap D (reduceCharge D a) = classOf (doubled D) (D.G *ᵥ a) :=
  (classOf_gram_eq_iff D hu _ _).2 (reduction_lift D (reduceCharge D a))

/-- The original charge sectors are additively equivalent to the
discriminant sectors of the doubled Gram matrix. -/
def sectorEquiv (D : LatticeData) (hu : IsUnit D.G.det) :
    ModTwoCharge D ≃+ Discriminant (doubled D) :=
  { Equiv.ofBijective (sectorMap D) ⟨by
      intro a b h
      obtain ⟨x, rfl⟩ := reduction_surjective D a
      obtain ⟨y, rfl⟩ := reduction_surjective D b
      rw [sectorMap_apply D hu, sectorMap_apply D hu] at h
      exact (classOf_gram_eq_iff D hu x y).1 h, by
      intro b
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (p := gramRange (doubled D)) b
      obtain ⟨a, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2
        (D.G.isUnit_iff_isUnit_det.2 hu)) y
      exact ⟨reduceCharge D a, sectorMap_apply D hu a⟩⟩ with
    map_add' := by
      intro a b
      obtain ⟨x, rfl⟩ := reduction_surjective D a
      obtain ⟨y, rfl⟩ := reduction_surjective D b
      change sectorMap D _ = sectorMap D _ + sectorMap D _
      rw [← map_add, sectorMap_apply D hu, sectorMap_apply D hu, sectorMap_apply D hu,
        mulVec_add]
      rfl }

/-- The additive equivalence sends a reduced charge to the actual
quotient class of its Gram image. -/
theorem sectorEquiv_reduceCharge (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
    sectorEquiv D hu (reduceCharge D a) = classOf (doubled D) (D.G *ᵥ a) :=
  sectorMap_apply D hu a

private theorem gramRat_doubled (D : LatticeData) :
    gramRat (doubled D) = (2 : ℚ) • gramRat D := by
  ext i j
  change ((2 * D.G i j : ℤ) : ℚ) = 2 * (D.G i j : ℚ)
  push_cast
  rfl

private theorem doubledRat_unit (D : LatticeData) (hu : IsUnit D.G.det) :
    IsUnit (gramRat (doubled D)).det := by
  have hm : IsUnit (gramRat D).det := by
    change IsUnit ((Int.castRingHom ℚ).mapMatrix D.G).det
    rw [← RingHom.map_det]
    exact hu.map (Int.castRingHom ℚ)
  rw [gramRat_doubled, Matrix.det_smul]
  exact ((isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).pow _).mul hm

/-- The rational dual shift of the same representative is a/2. -/
theorem dualVector_gram_image (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
    dualVector (doubled D) (D.G *ᵥ a) = fun i => (a i : ℚ) / 2 := by
  have hd := doubledRat_unit D hu
  have hcast : (fun i => ((D.G *ᵥ a) i : ℚ)) = gramRat D *ᵥ fun i => (a i : ℚ) := by
    ext i
    exact (Int.castRingHom ℚ).map_mulVec D.G a i
  have hv : (fun i => (a i : ℚ) / 2) = (2 : ℚ)⁻¹ • (fun i => (a i : ℚ)) := by
    funext i
    simp [div_eq_mul_inv, mul_comm]
  rw [dualVector, inverseRat, hcast, hv]
  have he : gramRat (doubled D) *ᵥ ((2 : ℚ)⁻¹ • (fun i => (a i : ℚ))) =
      gramRat D *ᵥ (fun i => (a i : ℚ)) := by
    rw [gramRat_doubled, smul_mulVec, mulVec_smul, smul_smul]
    norm_num
  rw [← he, mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]

/-- A point of the existing rational dual lattice lies in the sector of a
exactly when it is a half-charge reducing to a. The sector is recovered
by applying the doubled Gram matrix before taking the literal quotient. -/
theorem dual_sector_iff (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (x : Fin D.rank → ℚ) :
    (∃ h : Charge D, gramRat (doubled D) *ᵥ x = (fun i => (h i : ℚ)) ∧
      classOf (doubled D) h = sectorEquiv D hu a) ↔
    ∃ q : Charge D, reduceCharge D q = a ∧ x = fun i => (q i : ℚ) / 2 := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨q, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2
      (D.G.isUnit_iff_isUnit_det.2 hu)) h
    refine ⟨q, (sectorEquiv D hu).injective ((sectorEquiv_reduceCharge D hu q).trans hc), ?_⟩
    rw [← dualVector_gram_image D hu q, dualVector, inverseRat, ← hh, mulVec_mulVec,
      nonsing_inv_mul _ (doubledRat_unit D hu), one_mulVec]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨D.G *ᵥ q, ?_, (sectorEquiv_reduceCharge D hu q).symm.trans ?_⟩
    · rw [← dualVector_gram_image D hu q, dualVector, inverseRat, mulVec_mulVec,
        mul_nonsing_inv _ (doubledRat_unit D hu), one_mulVec]
    · rw [hq]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDiscriminantCharge
