/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipScales
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipScales
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed scalar normalization of the original D four-point chart. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipSignedProjector

/-! The chosen D square roots give the physical Laurent scalar. -/

open Complex

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open OriginalFourMActualChart (Chart Puncture scaleRoot relativeD parameter)
open LatticeGeneratingFieldLocality MvPolynomial
open LatticeHalfFockChargedCoefficients (omega)
open private creationWord punctureWords from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private relative from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private root_ne from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
open private wordScale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private rootZ rootZ_sq from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

private theorem I_cube : I ^ (3 : ℕ) = -I := by
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, I_sq, neg_one_mul]

private theorem odd_I_zpow (n : ℤ) : I ^ (2*n-3) = I * (-1 : ℂ) ^ n := by
  have h₃ : I ^ (-3 : ℤ) = I := by
    rw [zpow_neg, zpow_ofNat, I_cube, inv_neg, inv_I, neg_neg]
  rw [sub_eq_add_neg, zpow_add₀ I_ne_zero, zpow_mul, zpow_ofNat, I_sq, h₃, mul_comm]

private theorem odd_neg_I_zpow (n : ℤ) : (-I) ^ (2*n-3) = (-I) * (-1 : ℂ) ^ n := by
  have h₃ : (-I) ^ (-3 : ℤ) = -I := by
    rw [zpow_neg, zpow_ofNat, neg_pow, I_cube]
    norm_num [inv_I]
  rw [sub_eq_add_neg, zpow_add₀ (neg_ne_zero.mpr I_ne_zero), zpow_mul,
    show (-I) ^ (2 : ℤ) = (-1 : ℂ) by rw [zpow_ofNat, neg_sq, I_sq], h₃, mul_comm]

/-- The D phase and Laurent monomial come from the chosen four local
square roots, the relative puncture signs and the original cubic factor. -/
theorem dLip_scale_factor (K L N : ℤ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℂ) ^ L * (1 - parameter .D (x : ℂ)) ^ (3 : ℕ) *
      (relativeD .Q / scaleRoot .D x .Q) ^ (2*K-3) *
      (relativeD .R / scaleRoot .D x .R) ^ (2*L-3) *
      (relativeD .S / scaleRoot .D x .S) ^ (2*N-3) =
    -I * (-1 : ℂ) ^ (K+N) * (x : ℂ) ^ (N-K-3) * (1 - (x : ℂ)) ^ (3 : ℕ) := by
  let y := rootZ x
  have hx₀ : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hy : y ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hy2 : y ^ (2 : ℤ) = (x : ℂ) := by
    rw [zpow_ofNat]
    exact rootZ_sq hx
  have hQ : relativeD .Q / scaleRoot .D x .Q = I * y⁻¹ := by
    change (-1 : ℂ) / (I * y) = _
    simp only [div_eq_mul_inv, mul_inv_rev, inv_I]
    ring
  have hR : relativeD .R / scaleRoot .D x .R = I := by
    change (-1 : ℂ) / I = I
    rw [div_eq_mul_inv, inv_I]
    ring
  have hS : relativeD .S / scaleRoot .D x .S = (-I) * y := by
    change (1 : ℂ) / (I / y) = _
    rw [one_div, inv_div, div_eq_mul_inv, inv_I]
    ring
  have hphase : (-1 : ℂ) ^ L * I ^ (2*K-3) * I ^ (2*L-3) * (-I) ^ (2*N-3) =
      I * (-1 : ℂ) ^ (K+N) := by
    rw [odd_I_zpow, odd_I_zpow, odd_neg_I_zpow, zpow_add₀ (by norm_num)]
    have hp : (-1 : ℂ) ^ L * (-1 : ℂ) ^ L = 1 := by
      rw [← mul_zpow]
      norm_num
    linear_combination
      (I * (-1 : ℂ) ^ K * (-1 : ℂ) ^ N) * hp -
      (I * (-1 : ℂ) ^ L * (-1 : ℂ) ^ L * (-1 : ℂ) ^ K * (-1 : ℂ) ^ N) * I_sq
  have hyPow : (y⁻¹) ^ (2*K-3) * y ^ (2*N-3) = (x : ℂ) ^ (N-K) := by
    rw [inv_zpow, ← zpow_neg, ← zpow_add₀ hy,
      show -(2*K-3) + (2*N-3) = 2*(N-K) by ring, zpow_mul, hy2]
  have hcube : (1 - parameter .D (x : ℂ)) ^ (3 : ℕ) =
      -((1 - (x : ℂ)) ^ (3 : ℕ)) * ((x : ℂ) ^ (3 : ℕ))⁻¹ := by
    change (1 - (x : ℂ)⁻¹) ^ (3 : ℕ) = _
    field_simp [hx₀]
    ring
  rw [hQ, hR, hS, mul_zpow, mul_zpow]
  calc
    _ = ((-1 : ℂ) ^ L * I ^ (2*K-3) * I ^ (2*L-3) * (-I) ^ (2*N-3)) *
        ((y⁻¹) ^ (2*K-3) * y ^ (2*N-3)) * (1 - parameter .D (x : ℂ)) ^ (3 : ℕ) := by
      ring
    _ = _ := by
      rw [hphase, hyPow, hcube, sub_eq_add_neg (N-K) 3, zpow_add₀ hx₀,
        zpow_neg, zpow_ofNat]
      ring

private theorem relativeD_on_word (D : LatticeData) (s : Puncture)
    (xs : List (Index D)) (w : ℤ)
    (hw : (creationWord D xs).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) w) :
    relativeD s ^ xs.length = relativeD s ^ w := by
  let deg (l : List (Index D)) := (l.map fun i => (omega D i : ℤ)).sum
  have hhom (l : List (Index D)) :
      (creationWord D l).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (deg l) := by
    induction l with
    | nil => exact isWeightedHomogeneous_one (R := ℂ) (fun i : Index D => (omega D i : ℤ))
    | cons i l ih =>
      exact (isWeightedHomogeneous_X (R := ℂ) (fun i => (omega D i : ℤ)) i).mul ih
  have hnz (l : List (Index D)) : creationWord D l ≠ 0 := by
    induction l with
    | nil => exact one_ne_zero
    | cons i l ih => exact mul_ne_zero (X_ne_zero i) ih
  have hd := MvPolynomial.IsWeightedHomogeneous.inj_right (hnz xs) (hhom xs) hw
  rw [← hd]
  clear hd hw
  have h₀ : relativeD s ≠ 0 := by cases s <;> norm_num [relativeD]
  have h₂ : relativeD s ^ (2 : ℕ) = 1 := by cases s <;> norm_num [relativeD]
  induction xs with
  | nil => simp [deg]
  | cons i l ih =>
    change relativeD s ^ (l.length + 1) = relativeD s ^ ((omega D i : ℤ) + deg l)
    rw [pow_succ, ih, zpow_add₀ h₀, zpow_natCast]
    have hi : relativeD s ^ omega D i = relativeD s := by
      rw [omega, pow_succ, pow_mul, h₂, one_pow, one_mul]
    rw [hi, mul_comm]

private theorem dLip_word_scale (D : LatticeData) (s : Puncture) (xs : List (Index D))
    (w : ℤ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hw : (creationWord D xs).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) w) :
    relativeD s ^ xs.length * wordScale D .D x s xs =
      (relativeD s / scaleRoot .D x s) ^ w := by
  have hroot : scaleRoot .D x s ≠ 0 := root_ne hx hx₁ .D s
  rw [relativeD_on_word D s xs w hw, wordScale_of_homogeneous D .D x s xs w hroot hw,
    div_eq_mul_inv, mul_zpow]

/-- The relative signs on the four labelled creation words and the
inverse scales give the D Laurent factor at their signed detector weight. -/
theorem dLip_marked_scale_factor (D : LatticeData) (H K L N : ℤ) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) {X : Type*}
    (slot : X → Puncture) (mode : X → Index D) (marks : Puncture → List X)
    (hslot : ∀ s i, i ∈ marks s → slot i = s)
    (hP : (creationWord D ((marks .P).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2*H-3))
    (hQ : (creationWord D ((marks .Q).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2*K-3))
    (hR : (creationWord D ((marks .R).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2*L-3))
    (hS : (creationWord D ((marks .S).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2*N-3)) :
    let scale := fun s => wordScale D .D x s ((marks s).map mode)
    let l := (punctureWords marks).flatMap Prod.snd
    (-1 : ℂ) ^ L * (l.map fun i => relative .D (slot i)).prod *
      (1 - parameter .D (x : ℂ)) ^ (3 : ℕ) *
      (scale .P * scale .R * scale .Q * scale .S) =
      -I * (-1 : ℂ) ^ (K+N) * (x : ℂ) ^ (N-K-3) * (1-(x : ℂ)) ^ (3 : ℕ) := by
  dsimp only
  let scale := fun s => wordScale D .D x s ((marks s).map mode)
  have hProd (s : Puncture) : ((marks s).map fun i => relative .D (slot i)).prod =
      relativeD s ^ ((marks s).map mode).length := by
    rw [List.map_congr_left (g := fun _ => relativeD s) (fun i hi => by rw [hslot s i hi]; rfl),
      List.length_map]
    generalize marks s = xs
    induction xs with
    | nil => simp
    | cons i xs ih => simp only [List.length_cons, List.map_cons, List.prod_cons, ih, pow_succ,
        mul_comm]
  simp only [punctureWords, List.flatMap_cons, List.flatMap_nil, Prod.snd, List.append_nil,
    List.map_append, List.prod_append, hProd]
  calc
    _ = (-1 : ℂ) ^ L * (1 - parameter .D (x : ℂ)) ^ (3 : ℕ) *
        (relativeD .P ^ ((marks .P).map mode).length * scale .P) *
        (relativeD .Q ^ ((marks .Q).map mode).length * scale .Q) *
        (relativeD .R ^ ((marks .R).map mode).length * scale .R) *
        (relativeD .S ^ ((marks .S).map mode).length * scale .S) := by
      dsimp only [scale]
      ring
    _ = _ := by
      dsimp only [scale]
      rw [dLip_word_scale D .P _ _ hx hx₁ hP, dLip_word_scale D .Q _ _ hx hx₁ hQ,
        dLip_word_scale D .R _ _ hx hx₁ hR, dLip_word_scale D .S _ _ hx hx₁ hS,
        show relativeD .P / scaleRoot .D x .P = 1 by norm_num [relativeD, scaleRoot],
        one_zpow, mul_one]
      exact dLip_scale_factor K L N hx

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
