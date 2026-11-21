/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forward S and unit T on the actual mod-two charge theta sectors with complex source. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantShiftedTheta
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

/-! # Shifted theta series of the original four-point charge sectors -/

set_option autoImplicit false

open Matrix Complex
open scoped BigOperators

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMShiftedTheta

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open LatticeDiscriminantTheta LatticeDiscriminantShiftedTheta LatticeDiscriminantWeil
open OriginalFourMChargeCoset (fourierSign quadraticSign quadraticSign_integral)
open LatticeHalfFockChargedMonodromy (norm_even)

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
private theorem classOf_gram_eq_iff (D : LatticeData) (hu : IsUnit D.G.det) (a b : Charge D) :
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

private def sectorMap (D : LatticeData) (a : ModTwoCharge D) : Discriminant (doubled D) :=
  classOf (doubled D) (D.G *ᵥ (fun i => ((a i).val : ℤ)))

private theorem sectorMap_apply (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
    sectorMap D (reduceCharge D a) = classOf (doubled D) (D.G *ᵥ a) :=
  (classOf_gram_eq_iff D hu _ _).2 (reduction_lift D (reduceCharge D a))

/-- The original charge sectors are additively equivalent to the
discriminant sectors of the doubled Gram matrix. -/
def sectorEquiv (D : LatticeData) (hu : IsUnit D.G.det) :
    ModTwoCharge D ≃+ Discriminant (doubled D) :=
  let hreduce : Function.Surjective (reduceCharge D) :=
    Function.Surjective.piMap (fun _ : Fin D.rank => ZMod.intCast_surjective (n := 2))
  { Equiv.ofBijective (sectorMap D) ⟨by
      intro a b h
      obtain ⟨x, rfl⟩ := hreduce a
      obtain ⟨y, rfl⟩ := hreduce b
      rw [sectorMap_apply D hu, sectorMap_apply D hu] at h
      exact (classOf_gram_eq_iff D hu x y).1 h, by
      intro b
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (p := gramRange (doubled D)) b
      obtain ⟨a, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2
        (D.G.isUnit_iff_isUnit_det.2 hu)) y
      exact ⟨reduceCharge D a, sectorMap_apply D hu a⟩⟩ with
    map_add' := by
      intro a b
      obtain ⟨x, rfl⟩ := hreduce a
      obtain ⟨y, rfl⟩ := hreduce b
      change sectorMap D _ = sectorMap D _ + sectorMap D _
      rw [← map_add, sectorMap_apply D hu, sectorMap_apply D hu, sectorMap_apply D hu,
        mulVec_add]
      rfl }

/-- The additive equivalence sends a reduced charge to the actual
quotient class of its Gram image. -/
private theorem sectorEquiv_reduceCharge (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
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
private theorem dualVector_gram_image (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
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

private theorem doubled_sector_pairRaw (D : LatticeData) (hu : IsUnit D.G.det) (q a : Charge D) :
    pairRaw (doubled D) (D.G *ᵥ q) (D.G *ᵥ a) = (bilinear D q a : ℚ) / 2 := by
  rw [pairRaw, dualVector_gram_image D hu]
  simp only [dotProduct, Matrix.mulVec, bilinear,
    Int.cast_sum, Int.cast_mul, mul_assoc, ← Finset.mul_sum]
  ring_nf
  rw [Finset.sum_mul]

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
private theorem quadratic_phase_reduceCharge (D : LatticeData) (hu : IsUnit D.G.det)
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
private theorem pairing_phase_reduceCharge (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem pairing_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal (doubled D)).PosDef) (a b : ModTwoCharge D) :
    pairingCharacter (doubled D) hD (sectorEquiv D hu a) (sectorEquiv D hu b) =
      fourierSign D a b := by
  have hreduce : Function.Surjective (reduceCharge D) :=
    Function.Surjective.piMap (fun _ : Fin D.rank => ZMod.intCast_surjective (n := 2))
  obtain ⟨q, rfl⟩ := hreduce a
  obtain ⟨r, rfl⟩ := hreduce b
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
    have hreduce : Function.Surjective (reduceCharge D) :=
      Function.Surjective.piMap (fun _ : Fin D.rank => ZMod.intCast_surjective (n := 2))
    obtain ⟨q, rfl⟩ := hreduce b
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

open D5.S3.Fourier.MatrixGaussian (quadratic)

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
    exact Submodule.Quotient.mk_out (sectorEquiv D hu a)
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

/-- Translation of the period by one multiplies the entire charge sector
by the original quadratic sign, with its complex source fixed. -/
theorem chargeTheta_T (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (a : ModTwoCharge D) (τ : ℂ) (z : Fin D.rank → ℂ) :
    chargeTheta D hu a (τ + 1) z = quadraticSign D a * chargeTheta D hu a τ z := by
  have hreduce : Function.Surjective (reduceCharge D) :=
    Function.Surjective.piMap (fun _ : Fin D.rank => ZMod.intCast_surjective (n := 2))
  obtain ⟨p, rfl⟩ := hreduce a
  let d := doubled D
  let hd := doubled_posDef D hD
  let r := representative d (sectorEquiv D hu (reduceCharge D p))
  have hsign : phase ((pairRaw d r r / 2 : ℚ) : QmodZ) =
      quadraticSign D (reduceCharge D p) := by
    have hclass : classOf d r = sectorEquiv D hu (reduceCharge D p) :=
      Submodule.Quotient.mk_out _
    rw [← quadraticClass_mk d hd r, hclass]
    exact quadratic_phase_reduceCharge D hu hd p
  simp only [chargeTheta, shiftedTheta, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [thetaTerm, Complex.exp_add]
  rw [term_T d hd r n τ, hsign, mul_assoc]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMShiftedTheta
