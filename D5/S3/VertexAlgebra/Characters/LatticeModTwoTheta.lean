/-
Original mod-two charge fibres and the discriminant theta of 2G.

Original source proposal: sha256
a208a3d341c2ebe1735b7c3d68c9eb39bc0824995cfea2fed33450e93cfbb7d8.
Native API repairs retain the complete original endpoint.
Source base: 65a253616c22829023b8ff1c09cf1d5e6a221cf6.
The S supplier is the existing LatticeDiscriminantWeil.sector_S, source
sha256 c51ff733bdd1b782eac84229d59e0dc690090d52722647d2f4088ba400f560e8,
frozen statement_id sha256
c08980a00edfdcf326eeedc53c845bdc7f1564a6e83305c54665e046954de765.
The T and representative-series suppliers are LatticeDiscriminantTheta,
sha256 ce85e541745bf747f408a7a2d114864f105d8d155da7de1bd6617f4feaeee31c.
Original signs are OriginalFourMChargeCoset, sha256
2dcee0cc8f9189579b8b0c6d84af51b1d3b2c80947ec999df21004f482814e1e.

The mathematical construction is the classical identification of L/2L with
the discriminant of L with its form doubled, for integral unimodular L.
The cocycle, characters, Gaussian, complex power and S/T conventions are
inherited from the cited sources. No claim of mathematical novelty is made.
This module supplies only charge-coset modular transport. Both original
chargeScalar factors, the half-average with reflection, the oscillator
kernels and their inverse-Gram/factorial dual remain to be transported.
It asserts no identityK, unrestricted fourM crossing, Monster realization,
VOA/CFT completion, string or AdS/CFT result.
-/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace D5.S3.VertexAlgebra.LatticeModTwoTheta

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open LatticeDiscriminantTheta
open D5.S3.Fourier.MatrixGaussian

open private pairRaw pairing_mk quadraticClass_mk phase_mk rat_unit
  integral_dot_gram real_det class_add from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

noncomputable section

/-- Same coordinates and original even integral form, multiplied by two. -/
def Gram2G (D : LatticeData) : LatticeData where
  rank := D.rank
  G i j := 2 * D.G i j
  symmetric i j := by rw [D.symmetric i j]
  even_diagonal i := ⟨D.G i i, by ring⟩

/-- The coordinatewise integer lift of the actual original F₂ charge. -/
def chargeLift (D : LatticeData) (a : ModTwoCharge D) : Charge D :=
  fun i => ((a i).val : ℤ)

private lemma reduce_lift (D : LatticeData) (a : ModTwoCharge D) :
    reduceCharge D (chargeLift D a) = a := by
  ext i
  simp [reduceCharge, chargeLift]

private def twice (D : LatticeData) (n : Charge D) : Charge D :=
  fun i => 2 * n i

private lemma reduce_twice (D : LatticeData) (n : Charge D) :
    reduceCharge D (twice D n) = 0 := by
  ext i
  change ((2 * n i : ℤ) : ZMod 2) = 0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ⟨n i, rfl⟩

private lemma same_reduction (D : LatticeData) (p q : Charge D) :
    reduceCharge D p = reduceCharge D q ↔ ∃ n : Charge D, p - q = twice D n := by
  constructor
  · intro h
    have hz : reduceCharge D (p - q) = 0 := by rw [map_sub, h, sub_self]
    have hd (i : Fin D.rank) : (2 : ℤ) ∣ (p - q) i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      exact congrFun hz i
    choose n hn using hd
    exact ⟨n, funext hn⟩
  · rintro ⟨n, hn⟩
    have h := congrArg (reduceCharge D) hn
    rw [map_sub, reduce_twice] at h
    exact sub_eq_zero.mp h

private lemma gram_twice (D : LatticeData) (n : Charge D) :
    gramMap (Gram2G D) n = gramMap D (twice D n) := by
  ext i
  simp only [gramMap, Matrix.toLin'_apply, Gram2G, twice, mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- This inverse is integral: it is not an inverse chosen in the rational extension. -/
private def integralInverse (D : LatticeData) (p : Charge D) : Charge D :=
  D.G⁻¹ *ᵥ p

private lemma integralInverse_left (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Charge D) : integralInverse D (gramMap D p) = p := by
  change D.G⁻¹ *ᵥ (D.G *ᵥ p) = p
  rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

private lemma integralInverse_right (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Charge D) : gramMap D (integralInverse D p) = p := by
  change D.G *ᵥ (D.G⁻¹ *ᵥ p) = p
  rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

private lemma gram_injective (D : LatticeData) (hu : IsUnit D.G.det) :
    Function.Injective (gramMap D) := by
  intro p q h
  simpa only [integralInverse_left D hu] using congrArg (integralInverse D) h

private lemma class_gram_iff (D : LatticeData) (hu : IsUnit D.G.det)
    (p q : Charge D) :
    classOf (Gram2G D) (gramMap D p) = classOf (Gram2G D) (gramMap D q) ↔
      reduceCharge D p = reduceCharge D q := by
  rw [same_reduction]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (gramRange (Gram2G D))).mp h
    change gramMap (Gram2G D) n = gramMap D p - gramMap D q at hn
    rw [gram_twice, ← map_sub] at hn
    exact ⟨n, (gram_injective D hu hn).symm⟩
  · rintro ⟨n, hn⟩
    apply (Submodule.Quotient.eq (gramRange (Gram2G D))).mpr
    refine ⟨n, ?_⟩
    change gramMap (Gram2G D) n = gramMap D p - gramMap D q
    rw [gram_twice, ← map_sub, hn]

private def chargeClass (D : LatticeData) (hu : IsUnit D.G.det) :
    ModTwoCharge D →+ Discriminant (Gram2G D) where
  toFun a := classOf (Gram2G D) (gramMap D (chargeLift D a))
  map_zero' := by
    calc
      _ = classOf (Gram2G D) (gramMap D 0) :=
        (class_gram_iff D hu _ _).mpr (by rw [reduce_lift, map_zero])
      _ = 0 := by simp [classOf]
  map_add' a b := by
    change classOf (Gram2G D) (gramMap D (chargeLift D (a + b))) =
      classOf (Gram2G D) (gramMap D (chargeLift D a)) +
        classOf (Gram2G D) (gramMap D (chargeLift D b))
    calc
      _ = classOf (Gram2G D) (gramMap D (chargeLift D a + chargeLift D b)) :=
        (class_gram_iff D hu _ _).mpr (by
          rw [reduce_lift, map_add, reduce_lift, reduce_lift])
      _ = _ := by rw [map_add, class_add]

private lemma chargeClass_reduce (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Charge D) :
    chargeClass D hu (reduceCharge D p) = classOf (Gram2G D) (gramMap D p) :=
  (class_gram_iff D hu _ _).mpr (reduce_lift D _)

/-- The original mod-two charges, additively identified with the actual 2G cokernel. -/
def phi (D : LatticeData) (hu : IsUnit D.G.det) :
    ModTwoCharge D ≃+ Discriminant (Gram2G D) :=
  AddEquiv.ofBijective (chargeClass D hu) (by
    constructor
    · intro a b hab
      have h := (class_gram_iff D hu (chargeLift D a) (chargeLift D b)).mp hab
      simpa only [reduce_lift] using h
    · intro a
      induction a using Submodule.Quotient.induction_on with
      | H r =>
        refine ⟨reduceCharge D (integralInverse D r), ?_⟩
        rw [chargeClass_reduce, integralInverse_right D hu]
        rfl)

private lemma phi_reduce (D : LatticeData) (hu : IsUnit D.G.det) (p : Charge D) :
    phi D hu (reduceCharge D p) = classOf (Gram2G D) (gramMap D p) :=
  chargeClass_reduce D hu p

private lemma phi_lift (D : LatticeData) (hu : IsUnit D.G.det) (a : ModTwoCharge D) :
    phi D hu a = classOf (Gram2G D) (gramMap D (chargeLift D a)) := rfl

private lemma phi_neg (D : LatticeData) (hu : IsUnit D.G.det) (a : ModTwoCharge D) :
    -(phi D hu a) = phi D hu a := by
  have ha : -a = a := by ext i; exact CharTwo.neg_eq _
  rw [← map_neg, ha]

private lemma double_real (D : LatticeData) :
    gramReal (Gram2G D) = (2 : ℝ) • gramReal D := by
  ext i j
  change ((2 * D.G i j : ℤ) : ℝ) = (2 : ℝ) * (D.G i j : ℝ)
  push_cast
  ring

private lemma double_posDef (D : LatticeData) (hD : (gramReal D).PosDef) :
    (gramReal (Gram2G D)).PosDef := by
  have he : gramReal (Gram2G D) = gramReal D + gramReal D := by
    ext i j
    change ((2 * D.G i j : ℤ) : ℝ) = (D.G i j : ℝ) + (D.G i j : ℝ)
    push_cast
    ring
  rw [he]
  exact hD.add hD

private lemma det_one (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) : D.G.det = 1 := by
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · have hp := hD.det_pos
    rw [real_det, h] at hp
    norm_num at hp

private lemma det_double (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) :
    (gramReal (Gram2G D)).det = (2 : ℝ) ^ D.rank := by
  rw [double_real, Matrix.det_smul, Fintype.card_fin, real_det, det_one D hu hD]
  norm_num [Gram2G]

/-- The dual shift is computed using the supplier's actual rational inverse. -/
private lemma dual_half (D : LatticeData) (h2 : (gramReal (Gram2G D)).PosDef)
    (p : Charge D) :
    dualVector (Gram2G D) (gramMap D p) = fun i => (p i : ℚ) / 2 := by
  have hc : (fun i => (gramMap D p i : ℚ)) =
      gramRat (Gram2G D) *ᵥ (fun i => (p i : ℚ) / 2) := by
    ext i
    simp only [gramMap, Matrix.toLin'_apply, gramRat, Gram2G,
      Matrix.map_apply, mulVec, dotProduct]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    dualVector (Gram2G D) (gramMap D p) =
        (gramRat (Gram2G D))⁻¹ *ᵥ
          (gramRat (Gram2G D) *ᵥ (fun i => (p i : ℚ) / 2)) :=
      congrArg (fun v : Fin D.rank → ℚ => (gramRat (Gram2G D))⁻¹ *ᵥ v) hc
    _ = _ := by
      rw [mulVec_mulVec, nonsing_inv_mul _ (rat_unit (Gram2G D) h2), one_mulVec]
      rfl

private lemma shift_half (D : LatticeData) (h2 : (gramReal (Gram2G D)).PosDef)
    (p : Charge D) :
    shift (Gram2G D) (gramMap D p) = fun i => (p i : ℝ) / 2 := by
  ext i
  simp only [shift, dual_half D h2]
  push_cast
  ring

private lemma raw_pair (D : LatticeData) (h2 : (gramReal (Gram2G D)).PosDef)
    (p q : Charge D) :
    pairRaw (Gram2G D) (gramMap D p) (gramMap D q) = (bilinear D p q : ℚ) / 2 := by
  rw [pairRaw, dual_half D h2]
  calc
    (fun i => (p i : ℚ) / 2) ⬝ᵥ (fun i => (gramMap D q i : ℚ)) =
        ((fun i => (p i : ℚ)) ⬝ᵥ (fun i => (gramMap D q i : ℚ))) / 2 := by
      simp only [dotProduct, div_mul_eq_mul_div, Finset.sum_div]
    _ = (bilinear D p q : ℚ) / 2 := by
      apply congrArg (fun x : ℚ => x / 2)
      calc
        _ = ((p ⬝ᵥ gramMap D q : ℤ) : ℚ) :=
          ((Int.castRingHom ℚ).map_dotProduct p (gramMap D q)).symm
        _ = _ := congrArg (fun z : ℤ => (z : ℚ)) (integral_dot_gram D p q)

private lemma raw_quadratic (D : LatticeData) (h2 : (gramReal (Gram2G D)).PosDef)
    (p : Charge D) :
    pairRaw (Gram2G D) (gramMap D p) (gramMap D p) / 2 =
      (bilinear D p p : ℚ) / 4 := by
  rw [raw_pair D h2]
  ring

private lemma exp_pi_integer (z : ℤ) :
    Complex.exp (Real.pi * Complex.I * (z : ℂ)) = paritySign z := by
  by_cases he : Even z
  · rw [paritySign, if_pos he]
    obtain ⟨k, hk⟩ := he
    rw [show (Real.pi : ℂ) * Complex.I * (z : ℂ) =
      (k : ℂ) * (2 * Real.pi * Complex.I) by rw [hk]; push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  · have hz := Int.emod_add_mul_ediv z 2
    have hr : z % 2 = 1 := by
      have hnonneg := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
      have hne : z % 2 ≠ 0 := by
        intro hzero
        apply he
        refine ⟨z / 2, ?_⟩
        omega
      omega
    have hodd : z = 2 * (z / 2) + 1 := by omega
    rw [paritySign, if_neg he]
    rw [show (Real.pi : ℂ) * Complex.I * (z : ℂ) =
      ((z / 2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I by
        conv_lhs => rw [hodd]
        push_cast
        ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

private lemma phase_half (z : ℤ) :
    phase (((z : ℚ) / 2 : ℚ) : QmodZ) = paritySign z := by
  rw [phase_mk]
  calc
    Complex.exp (2 * Real.pi * Complex.I * (((z : ℚ) / 2 : ℚ) : ℂ)) =
        Complex.exp (Real.pi * Complex.I * (z : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = paritySign z := exp_pi_integer z

private lemma fourier_integral (D : LatticeData) (p q : Charge D) :
    TwistedGround.OriginalFourMChargeCoset.fourierSign D
      (reduceCharge D p) (reduceCharge D q) = paritySign (bilinear D p q) := by
  unfold TwistedGround.OriginalFourMChargeCoset.fourierSign
  have h : modTwoPairing D (reduceCharge D p) (reduceCharge D q) =
      (bilinear D p q : F₂) := by
    simp [modTwoPairing, Matrix.toBilin'_apply, bilinear, reduceCharge, Matrix.map_apply]
  rw [h, complexSign_integral]

private lemma fourier_phase (D : LatticeData) (hu : IsUnit D.G.det)
    (h2 : (gramReal (Gram2G D)).PosDef) (a b : ModTwoCharge D) :
    pairingCharacter (Gram2G D) h2 (phi D hu a) (-(phi D hu b)) =
      TwistedGround.OriginalFourMChargeCoset.fourierSign D a b := by
  rw [phi_neg, phi_lift, phi_lift]
  change phase (pairing (Gram2G D)
    (classOf (Gram2G D) (gramMap D (chargeLift D a)))
    (classOf (Gram2G D) (gramMap D (chargeLift D b)))) = _
  rw [pairing_mk (Gram2G D) h2, raw_pair D h2, phase_half]
  have h := fourier_integral D (chargeLift D a) (chargeLift D b)
  rw [reduce_lift, reduce_lift] at h
  exact h.symm

private lemma quadratic_phase (D : LatticeData) (hu : IsUnit D.G.det)
    (h2 : (gramReal (Gram2G D)).PosDef) (a : ModTwoCharge D) :
    phase (quadraticClass (Gram2G D) (phi D hu a)) =
      TwistedGround.OriginalFourMChargeCoset.quadraticSign D a := by
  rw [phi_lift, quadraticClass_mk (Gram2G D) h2, raw_quadratic D h2]
  have he : (bilinear D (chargeLift D a) (chargeLift D a) : ℚ) / 4 =
      (chargeEnergy D (chargeLift D a) : ℚ) / 2 := by
    rw [← two_chargeEnergy D (chargeLift D a)]
    push_cast
    ring
  rw [he, phase_half]
  have h := TwistedGround.OriginalFourMChargeCoset.quadraticSign_integral D (chargeLift D a)
  rw [reduce_lift] at h
  exact h.symm

private def fibreCharge (D : LatticeData) (a : ModTwoCharge D) (n : Charge D) :
    Charge D := fun i => 2 * n i + chargeLift D a i

private lemma reduce_fibreCharge (D : LatticeData) (a : ModTwoCharge D) (n : Charge D) :
    reduceCharge D (fibreCharge D a n) = a := by
  ext i
  change ((2 * n i + chargeLift D a i : ℤ) : ZMod 2) = a i
  apply (ZMod.intCast_eq_iff 2 _ _).mpr
  exact ⟨n i, by dsimp [chargeLift]; omega⟩

private def fibreEquiv (D : LatticeData) (a : ModTwoCharge D) :
    Charge D ≃ {p : Charge D // reduceCharge D p = a} :=
  Equiv.ofBijective (fun n => ⟨fibreCharge D a n, reduce_fibreCharge D a n⟩) (by
    constructor
    · intro m n h
      have hv := congrArg Subtype.val h
      ext i
      have hi := congrFun hv i
      dsimp [fibreCharge] at hi
      omega
    · intro p
      have hd (i : Fin D.rank) : ∃ k : ℤ, p.val i = (a i).val + 2 * k := by
        apply (ZMod.intCast_eq_iff 2 (p.val i) (a i)).mp
        exact congrFun p.property i
      choose n hn using hd
      refine ⟨n, Subtype.ext ?_⟩
      ext i
      change 2 * n i + chargeLift D a i = p.val i
      dsimp [chargeLift]
      have hi := hn i
      omega)

private def chargeTerm (D : LatticeData) (τ : ℂ) (p : Charge D) : ℂ :=
  Complex.exp ((Real.pi * Complex.I * τ / 2) * (bilinear D p p : ℂ))

/-- Literal unbounded sum over the original parity fibre, not a sector definition. -/
def parityTheta (D : LatticeData) (a : ModTwoCharge D) (τ : ℂ) : ℂ :=
  ∑' p : {p : Charge D // reduceCharge D p = a},
    Complex.exp ((Real.pi * Complex.I * τ / 2) * (bilinear D p.val p.val : ℂ))

private lemma quadratic_half (D : LatticeData) (p : Charge D) :
    quadratic (gramReal (Gram2G D)) (fun i => (p i : ℝ) / 2) =
      (bilinear D p p : ℝ) / 2 := by
  simp only [quadratic, gramReal, Gram2G, Matrix.map_apply, dotProduct, mulVec, bilinear]
  push_cast
  simp only [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma fibre_term (D : LatticeData) (h2 : (gramReal (Gram2G D)).PosDef)
    (a : ModTwoCharge D) (n : Charge D) (τ : ℂ) :
    Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal (Gram2G D))
        (fun i : Fin D.rank => (n i : ℝ) + shift (Gram2G D) (gramMap D (chargeLift D a)) i) : ℂ)) =
      chargeTerm D τ (fibreCharge D a n) := by
  have hv : (fun i : Fin D.rank => (n i : ℝ) +
      shift (Gram2G D) (gramMap D (chargeLift D a)) i) =
      (fun i => (fibreCharge D a n i : ℝ) / 2) := by
    rw [shift_half D h2]
    ext i
    simp only [Pi.add_apply, fibreCharge]
    push_cast
    ring
  have hq := (congrArg (quadratic (gramReal (Gram2G D))) hv).trans
    (quadratic_half D (fibreCharge D a n))
  calc
    _ = Complex.exp (Real.pi * Complex.I * τ *
        (((bilinear D (fibreCharge D a n) (fibreCharge D a n) : ℝ) / 2 : ℝ) : ℂ)) :=
      congrArg (fun x : ℝ => Complex.exp (Real.pi * Complex.I * τ * (x : ℂ))) hq
    _ = _ := by
      unfold chargeTerm
      congr 1
      push_cast
      ring

private lemma fibre_theta (D : LatticeData) (hu : IsUnit D.G.det)
    (h2 : (gramReal (Gram2G D)).PosDef) (a : ModTwoCharge D)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun p : {p : Charge D // reduceCharge D p = a} =>
      ‖Complex.exp ((Real.pi * Complex.I * τ / 2) * (bilinear D p.val p.val : ℂ))‖) ∧
    parityTheta D a τ = sectorTheta (Gram2G D) (phi D hu a) τ := by
  classical
  let e := fibreEquiv D a
  let r := gramMap D (chargeLift D a)
  have hr : classOf (Gram2G D) r = phi D hu a := rfl
  have hrep := sector_summable_representative (Gram2G D) h2 (phi D hu a) r hr τ hτ
  have hn : Summable (fun n : Charge D => ‖chargeTerm D τ (e n).val‖) := by
    apply hrep.1.congr
    intro n
    exact congrArg (fun z : ℂ => ‖z‖) (fibre_term D h2 a n τ)
  have hf : Summable (fun p : {p : Charge D // reduceCharge D p = a} =>
      ‖chargeTerm D τ p.val‖) := by
    have h := hn.comp_injective e.symm.injective
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using h
  refine ⟨hf, ?_⟩
  have ht : parityTheta D a τ = representativeTheta (Gram2G D) r τ := by
    calc
      parityTheta D a τ = ∑' n : Charge D, chargeTerm D τ (e n).val :=
        (e.tsum_eq (fun p => chargeTerm D τ p.val)).symm
      _ = representativeTheta (Gram2G D) r τ := by
        apply tsum_congr
        intro n
        exact (fibre_term D h2 a n τ).symm
  exact ht.trans hrep.2.symm

private lemma upper_S (τ : ℂ) (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hτ0 : τ ≠ 0 := by intro h; simpa [h] using hτ
  rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]
  simpa only [neg_div, neg_neg] using div_pos hτ (Complex.normSq_pos.mpr hτ0)

private lemma parity_S (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h2 : (gramReal (Gram2G D)).PosDef)
    (a : ModTwoCharge D) (τ : ℂ) (hτ : 0 < τ.im) :
    parityTheta D a (-1 / τ) = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
      (Real.sqrt ((2 : ℝ) ^ D.rank) : ℂ) * ∑ b : ModTwoCharge D,
        TwistedGround.OriginalFourMChargeCoset.fourierSign D a b * parityTheta D b τ := by
  letI : Fact (gramReal (Gram2G D)).PosDef := ⟨h2⟩
  letI : Fintype (Discriminant (Gram2G D)) := Fintype.ofFinite _
  have hs := LatticeDiscriminantWeil.sector_S (Gram2G D) h2 (phi D hu a) τ hτ
  calc
    parityTheta D a (-1 / τ) = sectorTheta (Gram2G D) (phi D hu a) (-1 / τ) :=
      (fibre_theta D hu h2 a _ (upper_S τ hτ)).2
    _ = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
        (Real.sqrt (gramReal (Gram2G D)).det : ℂ) *
        ∑ c : Discriminant (Gram2G D),
          pairingCharacter (Gram2G D) h2 (phi D hu a) (-c) *
            sectorTheta (Gram2G D) c τ := hs
    _ = _ := by
      rw [det_double D hu hD]
      congr 1
      calc
        (∑ c : Discriminant (Gram2G D),
          pairingCharacter (Gram2G D) h2 (phi D hu a) (-c) * sectorTheta (Gram2G D) c τ) =
            ∑ b : ModTwoCharge D,
              pairingCharacter (Gram2G D) h2 (phi D hu a) (-(phi D hu b)) *
                sectorTheta (Gram2G D) (phi D hu b) τ :=
          ((phi D hu).toEquiv.sum_comp (fun c =>
            pairingCharacter (Gram2G D) h2 (phi D hu a) (-c) *
              sectorTheta (Gram2G D) c τ)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          rw [fourier_phase D hu h2, ← (fibre_theta D hu h2 b τ hτ).2]

private lemma parity_T (D : LatticeData) (hu : IsUnit D.G.det)
    (h2 : (gramReal (Gram2G D)).PosDef) (a : ModTwoCharge D)
    (τ : ℂ) (hτ : 0 < τ.im) :
    parityTheta D a (τ + 1) =
      TwistedGround.OriginalFourMChargeCoset.quadraticSign D a * parityTheta D a τ := by
  have hτT : 0 < (τ + 1).im := by simpa using hτ
  rw [(fibre_theta D hu h2 a (τ + 1) hτT).2,
    sector_T (Gram2G D) h2 (phi D hu a) τ hτ,
    quadratic_phase D hu h2, ← (fibre_theta D hu h2 a τ hτ).2]

/-- One consumed bridge: original quotient, shifts, phases, fibres, convergence and S/T.
All hypotheses concern the original integral lattice; no identification certificate
or phase, shift, coset or modular-law hypothesis is an input. The witness `h2` is
constructed by doubling the supplied positive definite form. Empty rank is included. -/
theorem original_modTwo_theta_bridge (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) :
    ∃ h2 : (gramReal (Gram2G D)).PosDef,
      D.G.det = 1 ∧
      (gramReal (Gram2G D)).det = (2 : ℝ) ^ D.rank ∧
      (∀ p : Charge D,
        phi D hu (reduceCharge D p) = classOf (Gram2G D) (gramMap D p)) ∧
      (∀ p : Charge D,
        dualVector (Gram2G D) (gramMap D p) = fun i => (p i : ℚ) / 2) ∧
      (∀ a : ModTwoCharge D, -(phi D hu a) = phi D hu a) ∧
      (∀ a b : ModTwoCharge D,
        pairingCharacter (Gram2G D) h2 (phi D hu a) (-(phi D hu b)) =
          TwistedGround.OriginalFourMChargeCoset.fourierSign D a b) ∧
      (∀ a : ModTwoCharge D,
        phase (quadraticClass (Gram2G D) (phi D hu a)) =
          TwistedGround.OriginalFourMChargeCoset.quadraticSign D a) ∧
      (∀ a : ModTwoCharge D,
        ∃ e : Charge D ≃ {p : Charge D // reduceCharge D p = a},
          ∀ n : Charge D, (e n).val = fun i => 2 * n i + chargeLift D a i) ∧
      (∀ (τ : ℂ), 0 < τ.im → ∀ a : ModTwoCharge D,
        Summable (fun p : {p : Charge D // reduceCharge D p = a} =>
          ‖Complex.exp ((Real.pi * Complex.I * τ / 2) * (bilinear D p.val p.val : ℂ))‖) ∧
        parityTheta D a τ = sectorTheta (Gram2G D) (phi D hu a) τ ∧
        parityTheta D a (-1 / τ) = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
          (Real.sqrt ((2 : ℝ) ^ D.rank) : ℂ) * ∑ b : ModTwoCharge D,
            TwistedGround.OriginalFourMChargeCoset.fourierSign D a b * parityTheta D b τ) ∧
      (∀ (τ : ℂ), 0 < τ.im → ∀ a : ModTwoCharge D,
        parityTheta D a (τ + 1) =
          TwistedGround.OriginalFourMChargeCoset.quadraticSign D a * parityTheta D a τ) := by
  let h2 := double_posDef D hD
  refine ⟨h2, det_one D hu hD, det_double D hu hD, phi_reduce D hu,
    dual_half D h2, phi_neg D hu, fourier_phase D hu h2, quadratic_phase D hu h2, ?_, ?_, ?_⟩
  · intro a
    exact ⟨fibreEquiv D a, fun _ => rfl⟩
  · intro τ hτ a
    have ht := fibre_theta D hu h2 a τ hτ
    exact ⟨ht.1, ht.2, parity_S D hu hD h2 a τ hτ⟩
  · intro τ hτ a
    exact parity_T D hu h2 a τ hτ

end
end D5.S3.VertexAlgebra.LatticeModTwoTheta
