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

/-- The forward rank-24 S law on the actual original sectors. -/
theorem chargeTheta_S (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (a : ModTwoCharge D) (τ : ℂ) (hτ : 0 < τ.im) (z : Fin D.rank → ℂ) :
    chargeTheta D hu a (-1 / τ) (τ⁻¹ • z) =
      (-Complex.I * τ) ^ (12 : ℕ) *
      Complex.exp (Real.pi * Complex.I / τ * sourceQuadratic (gramReal (doubled D)) z) *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ *
        ∑ b : ModTwoCharge D, fourierSign D a b * chargeTheta D hu b τ z) := by
  classical
  let d := doubled D
  let hd := doubled_posDef D hD
  letI : Fact (gramReal d).PosDef := ⟨hd⟩
  letI : Fintype (Discriminant d) := Fintype.ofFinite _
  let f (b : Discriminant d) := shiftedTheta d b τ z
  let g (b : Discriminant d) := shiftedTheta d b (-1 / τ) (τ⁻¹ • z)
  let α := (-Complex.I * τ) ^ (12 : ℕ) *
    Complex.exp (Real.pi * Complex.I / τ * sourceQuadratic (gramReal d) z)
  have hpow : (-(d.rank : ℂ) / 2) = -(↑(12 : ℕ) : ℂ) := by
    change -(D.rank : ℂ) / 2 = _
    rw [hr]
    norm_num
  have hρ : rho d = (2 : ℂ) ^ (12 : ℕ) := by
    unfold rho
    rw [(dual_lattice_realization d hd).2.2.1]
    exact sqrt_det_doubled D hu hd hr
  have hf : f = α⁻¹ • weilSplus d g := by
    ext b
    have hb := shiftedTheta_S d hd b τ hτ z
    change shiftedTheta d b τ z = _
    change shiftedTheta d b τ z = _ at hb
    rw [hb, hpow, Complex.cpow_neg, Complex.cpow_natCast, sqrt_det_doubled D hu hd hr]
    change _ = α⁻¹ * ((rho d)⁻¹ * ∑ c : Discriminant d, pairingCharacter d hd b c * g c)
    dsimp only [α]
    rw [hρ, mul_inv, ← Complex.exp_neg]
    have hsign : -(Real.pi * Complex.I / τ * sourceQuadratic (gramReal d) z) =
        -Real.pi * Complex.I / τ * sourceQuadratic (gramReal d) z := by ring
    rw [hsign]
    ring
  have hτ₀ : τ ≠ 0 := by intro he; simp [he] at hτ
  have hα : α ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ₀))
      (Complex.exp_ne_zero _)
  have hg : g = α • weilS d f := by
    have h := congrArg (fun k => α • weilS d k) hf
    rw [LinearMap.map_smul, smul_smul, mul_inv_cancel₀ hα, one_smul] at h
    have hcomp := (finite_weil_relations d).2.2.2.2.1
    rw [← LinearMap.comp_apply, hcomp, LinearMap.id_apply] at h
    exact h.symm
  have hneg (b : ModTwoCharge D) : -(sectorEquiv D hu b) = sectorEquiv D hu b := by
    obtain ⟨q, rfl⟩ := reduction_surjective D b
    rw [← map_neg, ← map_neg]
    congr 1
    ext i
    change ((-q i : ℤ) : ZMod 2) = (q i : ZMod 2)
    rw [Int.cast_neg, ZMod.neg_eq_self_mod_two]
  change g (sectorEquiv D hu a) = _
  rw [hg]
  change α * ((rho d)⁻¹ * ∑ b : Discriminant d,
    pairingCharacter d hd (sectorEquiv D hu a) (-b) * f b) = _
  rw [hρ, ← (sectorEquiv D hu).toEquiv.sum_comp
    (fun b => pairingCharacter d hd (sectorEquiv D hu a) (-b) * f b)]
  congr 2
  apply Finset.sum_congr rfl
  intro b _
  change pairingCharacter d hd (sectorEquiv D hu a) (-(sectorEquiv D hu b)) *
    f (sectorEquiv D hu b) = _
  rw [hneg, pairing_sign D hu hd]
  rfl

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open OriginalFourMActualChart (parameter periodRoot)
open OriginalFourMPeriodSource (dPeriod chart_source_exponents)
open private gramQuadratic
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

private theorem sourceQuadratic_doubled (D : LatticeData) (z : Fin D.rank → ℂ) :
    sourceQuadratic (gramReal (doubled D)) z = 2 * gramQuadratic D z := by
  have h : (gramReal (doubled D)).map Complex.ofReal =
      (2 : ℂ) • D.G.map (Int.cast : ℤ → ℂ) := by
    rw [doubled_gramReal]
    ext i j
    change ((2 * (D.G i j : ℝ) : ℝ) : ℂ) = 2 * (D.G i j : ℂ)
    push_cast
    rfl
  rw [sourceQuadratic, h, smul_mulVec, dotProduct_smul, gramQuadratic, smul_eq_mul]

/-- The forward S multiplier at each chart source is the exponential of one
half the corresponding complementary covariance discrepancy, contracted
against the original Gram form. -/
theorem chart_source_multipliers (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (D : LatticeData) (MB MD : Fin D.rank → ℂ) :
    let pB := slitPeriod (1 - (x : ℂ))
    let qB := slitPeriod (x : ℂ)
    let pD := slitPeriod (parameter .A (x : ℂ))
    let qD := dPeriod upperA (parameter .D (x : ℂ))
    let aB := periodRoot .A x * (-Complex.I * (Real.sqrt x : ℂ))
    let zB := (Complex.I / (2 * (Real.pi : ℂ) * pB) * aB) • MB
    let zD := (Complex.I / (2 * (Real.pi : ℂ) * pD) * Complex.I) • MD
    Complex.exp (Real.pi * Complex.I / (Complex.I * qB / pB) *
        sourceQuadratic (gramReal (doubled D)) zB) =
      Complex.exp ((1 / ((Real.pi : ℂ) * pB * qB)) *
        (MB ⬝ᵥ (D.G.map (Int.cast : ℤ → ℂ)) *ᵥ MB) / 2) ∧
    Complex.exp (Real.pi * Complex.I / (Complex.I * qD / pD) *
        sourceQuadratic (gramReal (doubled D)) zD) =
      Complex.exp ((1 / ((Real.pi : ℂ) * pD * qD)) *
        (MD ⬝ᵥ (D.G.map (Int.cast : ℤ → ℂ)) *ᵥ MD) / 2) := by
  dsimp only
  simp only [sourceQuadratic_doubled]
  have h := chart_source_exponents upperA hx hx1 D MB MD
  dsimp only at h
  have he (t q : ℂ) :
      Real.pi * Complex.I / t * (2 * q) = 2 * Real.pi * Complex.I * q / t := by ring
  simp only [he]
  exact ⟨congrArg Complex.exp h.1, congrArg Complex.exp h.2⟩

/-- The actual doubled-Gram finite Weil operators satisfy the rank-24
involution and cubic relations. -/
theorem original_finite_weil (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24) :
    let d := doubled D
    letI : Fact (gramReal d).PosDef := ⟨doubled_posDef D hD⟩
    let S := weilS d
    let T := weilT d
    S.comp S = LinearMap.id ∧ (S.comp T).comp ((S.comp T).comp (S.comp T)) = LinearMap.id := by
  let d := doubled D
  letI : Fact (gramReal d).PosDef := ⟨doubled_posDef D hD⟩
  have hn (b : Discriminant d) : -b = b := by
    obtain ⟨a, rfl⟩ := (sectorEquiv D hu).surjective b
    rw [← map_neg]
    congr 1
    ext i
    exact ZMod.neg_eq_self_mod_two _
  have hc : chargeConjugation d = LinearMap.id := by
    ext f a
    change f (-a) = f a
    rw [hn]
  have hp := milgram d (doubled_posDef D hD)
  have he : (d.rank : ℂ) = 24 := by change (D.rank : ℂ) = _; rw [hr]; norm_num
  have harg : (Real.pi : ℂ) * Complex.I * 24 / 4 = (6 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I] at hp
  norm_num at hp
  have hw := finite_weil_relations d
  dsimp only
  exact ⟨hw.2.2.1.trans hc, by rw [hw.2.2.2.2.2.2, hp, hc, one_smul]⟩

open D5.S3.Fourier.MatrixGaussian (quadratic)
open private thetaTerm
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantShiftedTheta
open private class_representative
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private reduction_eq_iff
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDiscriminantCharge

private def chargeFiberEquiv (D : LatticeData) (a : Charge D) :
    Charge D ≃ {q : Charge D // reduceCharge D q = reduceCharge D a} :=
  Equiv.ofBijective (fun n => ⟨(2 : ℤ) • n + a,
    (reduction_eq_iff D _ _).2 ⟨n, add_sub_cancel_right _ _⟩⟩) ⟨by
      intro n m h
      have hn := congrArg Subtype.val h
      have he := add_right_cancel hn
      ext i
      have hi : 2 * n i = 2 * m i := congrFun he i
      omega, by
      rintro ⟨q, hq⟩
      obtain ⟨n, hn⟩ := (reduction_eq_iff D q a).1 hq
      refine ⟨n, Subtype.ext ?_⟩
      exact (eq_sub_iff_add_eq.mp hn.symm)⟩

/-- In integral charge coordinates the sector consists of the original
mod-two fiber, with quadratic energy divided by two and the original
Gram-linear source term. -/
theorem chargeTheta_eq_charge_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (τ : ℂ) (z : Fin D.rank → ℂ) :
    chargeTheta D hu a τ z =
    ∑' q : {q : Charge D // reduceCharge D q = a},
      Complex.exp (Real.pi * Complex.I * τ * (bilinear D q.val q.val : ℂ) / 2 +
        2 * Real.pi * Complex.I *
          ((D.G.map (Int.cast : ℤ → ℂ) *ᵥ (fun i => (q.val i : ℂ))) ⬝ᵥ z)) := by
  let d := doubled D
  let r := representative d (sectorEquiv D hu a)
  obtain ⟨p, hp⟩ := (Matrix.mulVec_surjective_iff_isUnit.2
    (D.G.isUnit_iff_isUnit_det.2 hu)) r
  have hsector : reduceCharge D p = a := by
    apply (sectorEquiv D hu).injective
    rw [sectorEquiv_reduceCharge, hp]
    exact class_representative d _
  subst a
  rw [← (chargeFiberEquiv D p).tsum_eq]
  apply tsum_congr
  intro n
  let q : Charge D := (2 : ℤ) • n + p
  let x : Fin D.rank → ℝ := (fun i => (q i : ℝ) / 2)
  have hx : (fun i => (n i : ℝ)) + shift d r = x := by
    rw [← hp]
    have hshift := dualVector_gram_image D hu p
    ext i
    change (n i : ℝ) + (dualVector d (D.G *ᵥ p) i : ℝ) = _
    rw [hshift]
    dsimp [x, q]
    push_cast
    ring
  change thetaTerm (gramReal d) τ z ((fun i => (n i : ℝ)) + shift d r) =
    Complex.exp (Real.pi * Complex.I * τ * (bilinear D q q : ℂ) / 2 +
      2 * Real.pi * Complex.I *
        ((D.G.map (Int.cast : ℤ → ℂ) *ᵥ (fun i => (q i : ℂ))) ⬝ᵥ z))
  rw [hx]
  have hG : gramReal d *ᵥ x = gramReal D *ᵥ fun i => (q i : ℝ) := by
    rw [doubled_gramReal, smul_mulVec, ← mulVec_smul]
    congr 1
    ext i
    change 2 * ((q i : ℝ) / 2) = _
    ring
  have hquad : quadratic (gramReal d) x = (bilinear D q q : ℝ) / 2 := by
    rw [quadratic, hG]
    simp only [x, bilinear, gramReal, dotProduct, mulVec, map_apply, Int.cast_sum, Int.cast_mul]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcast : (fun i => (↑((gramReal d *ᵥ x) i) : ℂ)) =
      D.G.map (Int.cast : ℤ → ℂ) *ᵥ (fun i => (q i : ℂ)) := by
    rw [hG]
    ext i
    simp [gramReal, mulVec, dotProduct]
  rw [thetaTerm, hquad, hcast]
  congr 1
  push_cast
  ring

open private term_T
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

/-- Translation of the period by one multiplies the entire charge sector
by the original quadratic sign, with its complex source fixed. -/
theorem chargeTheta_T (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (a : ModTwoCharge D) (τ : ℂ) (z : Fin D.rank → ℂ) :
    chargeTheta D hu a (τ + 1) z = quadraticSign D a * chargeTheta D hu a τ z := by
  obtain ⟨p, rfl⟩ := reduction_surjective D a
  let d := doubled D
  let hd := doubled_posDef D hD
  let r := representative d (sectorEquiv D hu (reduceCharge D p))
  have hsign : phase ((pairRaw d r r / 2 : ℚ) : QmodZ) =
      quadraticSign D (reduceCharge D p) := by
    rw [← quadraticClass_mk d hd r, class_representative]
    exact quadratic_phase_reduceCharge D hu hd p
  simp only [chargeTheta, shiftedTheta, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [thetaTerm, Complex.exp_add]
  rw [term_T d hd r n τ, hsign, mul_assoc]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMShiftedTheta
