/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial equations for compatible nonzero-product four-site triplets. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualFormula
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualRank

/-! The left cubic, left conic and right conic pulled back by the adjugate. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualSystem

open PeriodicMPSFourSiteSextic (sextic)
open PeriodicMPSFourSiteResidualFormula
open Matrix MvPolynomial
open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

local notation "M₃" => Matrix (Fin 3) (Fin 3) R
local notation "CP" => (C : R →+* MvPolynomial (Fin 3) R)

/-- The cyclic-vector choice used by the modular certificate. -/
def cyclicVector : Fin 3 → R := ![1, 0, 0]

private def leftMoment (T : M₃) : M₃ →ₗ[R] R :=
  singletLinear.comp (LinearMap.mulRight R T)

private def rightMoment (U : M₃) : M₃ →ₗ[R] R :=
  singletLinear.comp (LinearMap.mulLeft R U)

@[simp] private lemma leftMoment_apply (T X : M₃) :
    leftMoment T X = singlet (X * T) := rfl

@[simp] private lemma rightMoment_apply (U X : M₃) :
    rightMoment U X = singlet (U * X) := rfl

/-- The first factor's singlet product constraint. -/
def compatibility (T U K : M₃) : R :=
  productConstraint (singlet (K * T)) (singlet T * singlet U) (rightMoment U) K

/-- The conic on the left pencil. -/
def leftConic (T U K : M₃) : R :=
  residualConic (T * U) K cyclicVector (rightMoment U) (rightMoment T.adjugate)
    (singlet (K * T)) T.det (singlet T * singlet U)

/-- The conic on the right pencil. -/
def rightConic (T U K : M₃) : R :=
  residualConic (T * U) K cyclicVector (leftMoment T) (leftMoment U.adjugate)
    (singlet (U * K)) U.det (singlet T * singlet U)

section ChangeCoefficients

variable {S : Type*} [CommRing S] (f : R →+* S)

private lemma map_singlet (T : M₃) : f (singlet T) = singlet (f.mapMatrix T) := by
  simp only [singlet, map_sub, map_mul, map_ofNat, RingHom.mapMatrix_apply, Matrix.map_apply]

private lemma map_cyclicVector : f ∘ cyclicVector = (cyclicVector : Fin 3 → S) := by
  funext i
  fin_cases i <;> simp [cyclicVector]

private lemma map_leftMoment (T X : M₃) :
    f (leftMoment T X) = leftMoment (f.mapMatrix T) (f.mapMatrix X) := by
  simp only [leftMoment_apply, map_singlet, map_mul]

private lemma map_rightMoment (U X : M₃) :
    f (rightMoment U X) = rightMoment (f.mapMatrix U) (f.mapMatrix X) := by
  simp only [rightMoment_apply, map_singlet, map_mul]

/-- The compatibility equation is preserved by every coefficient specialization. -/
theorem map_compatibility (T U K : M₃) :
    f (compatibility T U K) = compatibility (f.mapMatrix T) (f.mapMatrix U) (f.mapMatrix K) := by
  simp only [compatibility, map_productConstraint f _ _ (map_rightMoment f U),
    map_singlet, map_mul]

/-- The left conic is preserved by every coefficient specialization. -/
theorem map_leftConic (T U K : M₃) :
    f (leftConic T U K) = leftConic (f.mapMatrix T) (f.mapMatrix U) (f.mapMatrix K) := by
  simp only [leftConic, map_residualConic f _ _ _ _ (map_rightMoment f U)
    (map_rightMoment f T.adjugate), map_cyclicVector, map_singlet, map_mul, f.map_adjugate, f.map_det]

/-- The right conic is preserved by every coefficient specialization. -/
theorem map_rightConic (T U K : M₃) :
    f (rightConic T U K) = rightConic (f.mapMatrix T) (f.mapMatrix U) (f.mapMatrix K) := by
  simp only [rightConic, map_residualConic f _ _ _ _ (map_leftMoment f T)
    (map_leftMoment f U.adjugate), map_cyclicVector, map_singlet, map_mul, f.map_adjugate, f.map_det]

end ChangeCoefficients

/-- The polynomial matrix with indeterminates as the pencil coordinates. -/
noncomputable def formalPencil (T U : M₃) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) R) :=
  pencil (C.mapMatrix (T * U)) X

/-- The residual cubics and conics over the coefficient ring, with the right
conic pulled back along the adjugate of the left pencil. -/
noncomputable def residualEquations (T U : M₃) : Fin 3 → MvPolynomial (Fin 3) R :=
  let first := C.mapMatrix T
  let second := C.mapMatrix U
  let K := formalPencil T U
  ![compatibility first second K, leftConic first second K, rightConic first second K.adjugate]

/-- The coefficient-level residual equations evaluate to the corresponding
matrix formulas on each actual pencil coordinate. -/
theorem eval_residualEquations (T U : M₃) (q : Fin 3 → R) :
    (fun i => eval q (residualEquations T U i)) =
      ![compatibility T U (pencil (T * U) q), leftConic T U (pencil (T * U) q),
        rightConic T U (pencil (T * U) q).adjugate] := by
  let read := eval q
  have hconst (M : M₃) : read.mapMatrix ((CP).mapMatrix M) = M := by
    apply Matrix.ext
    intro i j
    exact eval_C (M i j)
  have hread : read.mapMatrix (formalPencil T U) = pencil (T * U) q := by
    rw [formalPencil, map_pencil, hconst]
    congr 1
    funext i
    exact eval_X i
  funext i
  fin_cases i
  · change read (compatibility (C.mapMatrix T) (C.mapMatrix U) (formalPencil T U)) = _
    rw [map_compatibility, hconst, hconst, hread]
    rfl
  · change read (leftConic (C.mapMatrix T) (C.mapMatrix U) (formalPencil T U)) = _
    rw [map_leftConic, hconst, hconst, hread]
    rfl
  · change read (rightConic (C.mapMatrix T) (C.mapMatrix U) (formalPencil T U).adjugate) = _
    rw [map_rightConic, hconst, hconst, read.map_adjugate, hread]
    rfl

/-- The degree-eight coefficient matrix can be reduced modulo a prime by
reducing the two source triplets. -/
theorem map_residualEquations {S : Type*} [CommRing S] (f : R →+* S) (T U : M₃) :
    (fun i => map f (residualEquations T U i)) =
      residualEquations (f.mapMatrix T) (f.mapMatrix U) := by
  let m := map (σ := Fin 3) f
  have hc (M : M₃) : m.mapMatrix ((CP).mapMatrix M) = C.mapMatrix (f.mapMatrix M) := by
    apply Matrix.ext
    intro i j
    exact map_C f (M i j)
  have hk : m.mapMatrix (formalPencil T U) = formalPencil (f.mapMatrix T) (f.mapMatrix U) := by
    rw [formalPencil, map_pencil, hc, map_mul, formalPencil]
    congr 1
    funext i
    exact map_X _ _
  funext i
  fin_cases i
  · change m (compatibility (C.mapMatrix T) (C.mapMatrix U) (formalPencil T U)) = _
    rw [map_compatibility, hc, hc, hk]
    rfl
  · change m (leftConic (C.mapMatrix T) (C.mapMatrix U) (formalPencil T U)) = _
    rw [map_leftConic, hc, hc, hk]
    rfl
  · change m (rightConic (C.mapMatrix T) (C.mapMatrix U) (formalPencil T U).adjugate) = _
    rw [map_rightConic, hc, hc, m.map_adjugate, hk]
    rfl

section Homogeneous

local notation "P" => MvPolynomial (Fin 3) R
local notation "PM" => Matrix (Fin 3) (Fin 3) P

private def MatrixHomogeneous (M : PM) (n : ℕ) : Prop :=
  ∀ i j, (M i j).IsHomogeneous n

private lemma coefficientMatrix_degree (T : M₃) : MatrixHomogeneous ((CP).mapMatrix T) 0 :=
  fun i j => isHomogeneous_C _ _

private lemma matrixMul_degree {A B : PM} {m n : ℕ} (ha : MatrixHomogeneous A m)
    (hb : MatrixHomogeneous B n) : MatrixHomogeneous (A * B) (m + n) := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsHomogeneous.sum _ _ _ fun k _ => (ha i k).mul (hb k j)

private lemma singlet_degree {A : PM} {n : ℕ} (h : MatrixHomogeneous A n) :
    (singlet A).IsHomogeneous n := by
  apply (h 1 1).sub
  simpa only [map_ofNat] using (h 0 2).C_mul 2

private lemma det_degree {A : PM} {n : ℕ} (h : MatrixHomogeneous A n) :
    A.det.IsHomogeneous (3 * n) := by
  rw [Matrix.det_fin_three]
  have hmul (i j k l r s : Fin 3) :
      (A i j * A k l * A r s).IsHomogeneous (3 * n) := by
    convert ((h i j).mul (h k l)).mul (h r s) using 1 <;> omega
  exact ((((hmul ..).sub (hmul ..)).sub (hmul ..)).add (hmul ..)).add (hmul ..) |>.sub (hmul ..)

set_option maxHeartbeats 1000000 in
private lemma adjugate_degree {A : PM} {n : ℕ} (h : MatrixHomogeneous A n) :
    MatrixHomogeneous A.adjugate (2 * n) := by
  have hp (i j k l : Fin 3) : (A i j * A k l).IsHomogeneous (2 * n) := by
    simpa only [two_mul] using (h i j).mul (h k l)
  have hn (i j k l : Fin 3) : (-(A i j * A k l)).IsHomogeneous (2 * n) :=
    (hp ..).neg
  intro i j
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first | apply IsHomogeneous.sub <;> apply hp | apply IsHomogeneous.add <;> first | apply hn | apply hp

private lemma formalPencil_degree (T U : M₃) : MatrixHomogeneous (formalPencil T U) 1 := by
  intro i j
  simp only [formalPencil, pencil, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply IsHomogeneous.sum _ _ _
  intro k _
  rw [← map_pow]
  change (X k * C (((T * U) ^ k.val) i j)).IsHomogeneous 1
  rw [mul_comm]
  exact (isHomogeneous_X R k).C_mul _

private lemma leftMoment_degree (T : M₃) {K : PM} {d : ℕ} (h : MatrixHomogeneous K d) :
    (leftMoment ((CP).mapMatrix T) K).IsHomogeneous d := by
  simpa using singlet_degree (matrixMul_degree h (coefficientMatrix_degree T))

private lemma rightMoment_degree (U : M₃) {K : PM} {d : ℕ} (h : MatrixHomogeneous K d) :
    (rightMoment ((CP).mapMatrix U) K).IsHomogeneous d := by
  simpa using singlet_degree (matrixMul_degree (coefficientMatrix_degree U) h)

private lemma scale_degree {a b : P} {d : ℕ}
    (ha : a.IsHomogeneous 0) (hb : b.IsHomogeneous d) : (a * b).IsHomogeneous d := by
  simpa only [zero_add] using ha.mul hb

private lemma degree_scale {a b : P} {d : ℕ}
    (ha : a.IsHomogeneous d) (hb : b.IsHomogeneous 0) : (a * b).IsHomogeneous d := by
  simpa only [add_zero] using ha.mul hb

private lemma conic_degree (G : M₃) (β η : M₃ →ₗ[R] R) (β' η' : PM →ₗ[P] P)
    (hβ : ∀ M, C (β M) = β' ((CP).mapMatrix M))
    (hη : ∀ M, C (η M) = η' ((CP).mapMatrix M))
    (d : ℕ) (K : PM) (A : P) (τ g : R)
    (hk : MatrixHomogeneous K d) (ha : A.IsHomogeneous d)
    (degreeBeta : ∀ {M n}, MatrixHomogeneous M n → (β' M).IsHomogeneous n)
    (degreeEta : ∀ {M n}, MatrixHomogeneous M n → (η' M).IsHomogeneous n) :
    (residualConic ((CP).mapMatrix G) K cyclicVector β' η' A (C τ) (C g)).IsHomogeneous (2 * d) := by
  let v : Fin 3 → R := cyclicVector
  let J := cyclicMatrix G v
  let H := hankel G β
  let L := hankelSolver G β η
  let r := cyclicSolver G β v
  have hv : CP ∘ v = (cyclicVector : Fin 3 → P) := map_cyclicVector CP
  have hJ : cyclicMatrix ((CP).mapMatrix G) cyclicVector = (CP).mapMatrix J := by
    rw [← hv, ← map_cyclicMatrix]
  have hH : hankel ((CP).mapMatrix G) β' = (CP).mapMatrix H := (map_hankel CP β β' hβ G).symm
  have hL : hankelSolver ((CP).mapMatrix G) β' η' = (CP).mapMatrix L :=
    (map_hankelSolver CP β η β' η' hβ hη G).symm
  have hr : cyclicSolver ((CP).mapMatrix G) β' cyclicVector = CP ∘ r := by
    rw [← hv, ← map_cyclicSolver CP β β' hβ]
  have hB := degreeBeta (adjugate_degree hk)
  have hE := degreeEta (adjugate_degree hk)
  have hZ : (β' ((CP).mapMatrix L * ((CP).mapMatrix L * K.adjugate))).IsHomogeneous (2 * d) := by
    simpa only [zero_add] using degreeBeta (matrixMul_degree (coefficientMatrix_degree L)
      (matrixMul_degree (coefficientMatrix_degree L) (adjugate_degree hk)))
  have const (u : R) : (C u : P).IsHomogeneous 0 := isHomogeneous_C _ _
  have hW : ((cyclicVector ⨯₃ ((CP).mapMatrix L *ᵥ cyclicVector)) ⬝ᵥ
      (K *ᵥ ((CP ∘ r) ⨯₃ ((CP ∘ r) ᵥ* (CP).mapMatrix L)))).IsHomogeneous d := by
    have hp : (cyclicVector ⨯₃ ((CP).mapMatrix L *ᵥ cyclicVector)) =
        CP ∘ (v ⨯₃ (L *ᵥ v)) := by rw [map_cross, map_mulVec, hv]
    have hq : ((CP ∘ r) ⨯₃ ((CP ∘ r) ᵥ* (CP).mapMatrix L)) = CP ∘ (r ⨯₃ (r ᵥ* L)) := by
      rw [map_cross, map_vecMul]
    rw [hp, hq, dotProduct]
    apply IsHomogeneous.sum _ _ _
    intro i _
    apply scale_degree (const _)
    rw [Matrix.mulVec, dotProduct]
    exact IsHomogeneous.sum _ _ _ fun j _ => degree_scale (hk i j) (const _)
  unfold residualConic
  simp only [hJ, hH, hL, hr, ← RingHom.map_det]
  have hA2 : (A ^ 2).IsHomogeneous (2 * d) := by
    simpa only [Nat.mul_comm d 2] using ha.pow 2
  have h2 : (-2 : P).IsHomogeneous 0 := by
    simpa only [map_ofNat, map_neg] using const (-2)
  have h4 : (4 : P).IsHomogeneous 0 := by simpa only [map_ofNat] using const 4
  have hfirst := degree_scale (degree_scale (degree_scale
    (scale_degree (h2.mul (const τ)) hE) (const g)) ((const J.det).pow 2)) ((const H.det).pow 2)
  have hsecond := degree_scale (degree_scale (degree_scale
    (scale_degree (h4.mul (const τ)) hA2) (const g)) ((const J.det).pow 2)) ((const H.det).pow 2)
  have hthird := degree_scale (degree_scale
    (scale_degree ((const τ).pow 2) hB) ((const J.det).pow 2)) ((const H.det).pow 2)
  have hfourth := scale_degree (((const g).pow 2).mul ((const J.det).pow 2)) hZ
  have hfifth := (scale_degree (const g) ha).mul hW
  exact ((((hfirst.sub hsecond).sub hthird).sub hfourth).add
    (by simpa only [two_mul] using hfifth))

/-- The degree of each equation in the eliminated residual system. -/
theorem residualEquations_degree (T U : M₃) (i : Fin 3) :
    (residualEquations T U i).IsHomogeneous (![3, 2, 4] i) := by
  let K := formalPencil T U
  have hk : MatrixHomogeneous K 1 := formalPencil_degree T U
  have hKadj : MatrixHomogeneous K.adjugate 2 := adjugate_degree hk
  have hm : (CP).mapMatrix T * (CP).mapMatrix U = (CP).mapMatrix (T * U) := (map_mul (CP).mapMatrix T U).symm
  have hg : singlet ((CP).mapMatrix T) * singlet ((CP).mapMatrix U) = C (singlet T * singlet U) := by
    rw [map_mul, map_singlet, map_singlet]
  fin_cases i
  · change (compatibility ((CP).mapMatrix T) ((CP).mapMatrix U) K).IsHomogeneous 3
    unfold compatibility productConstraint
    rw [hg]
    exact ((leftMoment_degree T hk).mul (rightMoment_degree U hKadj)).sub
      (scale_degree (isHomogeneous_C _ _) (det_degree hk))
  · change (leftConic ((CP).mapMatrix T) ((CP).mapMatrix U) K).IsHomogeneous 2
    unfold leftConic
    rw [hm, hg, ← RingHom.map_det, ← RingHom.map_adjugate CP T]
    exact conic_degree (T * U) (rightMoment U) (rightMoment T.adjugate) _ _
      (map_rightMoment CP U) (map_rightMoment CP T.adjugate) 1 K _ T.det _
      hk (leftMoment_degree T hk) (rightMoment_degree U) (rightMoment_degree T.adjugate)
  · change (rightConic ((CP).mapMatrix T) ((CP).mapMatrix U) K.adjugate).IsHomogeneous 4
    unfold rightConic
    rw [hm, hg, ← RingHom.map_det, ← RingHom.map_adjugate CP U]
    exact conic_degree (T * U) (leftMoment T) (leftMoment U.adjugate) _ _
      (map_leftMoment CP T) (map_leftMoment CP U.adjugate) 2 K.adjugate _ U.det _
      hKadj (rightMoment_degree U hKadj) (leftMoment_degree T) (leftMoment_degree U.adjugate)

end Homogeneous

/-- The fourfold sextic value expressed directly on a triplet block. -/
def tripletEquation (M : M₃) : R :=
  -(M.det + singlet M * singlet M.adjugate) ^ 2 -
    4 * singlet M ^ 3 * M.det

/-- The triplet equation vanishes at any necklace sextic zero. -/
theorem tripletEquation_zero (a b c d e f : R) (h : sextic a b c d e f = 0) :
    tripletEquation (triplet a b c d e f) = 0 := by
  have he := four_mul_sextic a b c d e f
  dsimp only at he
  have h' : 4 * sextic a b c d e f = tripletEquation (triplet a b c d e f) := he
  rwa [h, mul_zero, eq_comm] at h'

private lemma singlet_smul (r : R) (M : M₃) : singlet (r • M) = r * singlet M := by
  exact (singletLinear (R := R)).map_smul r M

private lemma tripletEquation_smul (r : R) (M : M₃) :
    tripletEquation (r • M) = r ^ 6 * tripletEquation M := by
  simp only [tripletEquation, Matrix.det_smul, Matrix.adjugate_smul, Fintype.card_fin,
    Nat.reduceSub, singlet_smul]
  ring

/-- The shared singlet product and the sextic of the left compatible
factor force both of its residual equations. -/
theorem compatibility_leftConic_zero [IsDomain R] (T U K : M₃)
    (hc : Commute K (T * U)) (hj : (cyclicMatrix (T * U) cyclicVector).det ≠ 0)
    (hd : K.det ≠ 0) (ha : singlet (K * T) ≠ 0)
    (hs : tripletEquation (K * T) = 0)
    (hpair : singlet (K * T) * singlet (U * K.adjugate) =
      singlet T * singlet U * K.det) :
    compatibility T U K = 0 ∧ leftConic T U K = 0 := by
  have hC : compatibility T U K = 0 := sub_eq_zero.mpr hpair
  refine ⟨hC, ?_⟩
  apply residual_conic_zero_of_sextic (hV := adjugate_commutes_of_det_ne_zero hc hd)
    (hj := hj) (hA := ha) (hD := hd) (hC := hC)
  simp only [rightMoment_apply]
  rw [tripletEquation, Matrix.det_mul, Matrix.adjugate_mul_distrib] at hs
  linear_combination hs

/-- The partner conic vanishes on the adjugate of the first pencil coordinate,
including when the partner is represented by a different nonzero scale. -/
theorem pulledRightConic_zero [IsDomain R] (T U K V : M₃)
    (hc : Commute K (T * U)) (hj : (cyclicMatrix (T * U) cyclicVector).det ≠ 0)
    (hd : K.det ≠ 0) (hV : U * K.adjugate = K.det • V)
    (ha : singlet V ≠ 0) (hs : tripletEquation V = 0)
    (hpair : singlet (K * T) * singlet V = singlet T * singlet U) :
    rightConic T U K.adjugate = 0 := by
  have hdet : K.adjugate.det = K.det ^ 2 := by simp [Matrix.det_adjugate]
  have hsa : singlet (U * K.adjugate) = K.det * singlet V := by rw [hV, singlet_smul]
  have hsb : singlet (K.adjugate.adjugate * T) = K.det * singlet (K * T) := by
    rw [Matrix.adjugate_adjugate', Matrix.smul_mul, singlet_smul]
    simp
  have hG : Commute K.adjugate.adjugate (T * U) :=
    adjugate_commutes_of_det_ne_zero (adjugate_commutes_of_det_ne_zero hc hd)
      (by rw [hdet]; exact pow_ne_zero _ hd)
  have hc' : productConstraint (singlet (U * K.adjugate)) (singlet T * singlet U)
      (leftMoment T) K.adjugate = 0 := by
    simp only [productConstraint, leftMoment_apply, hsa, hsb, hdet]
    linear_combination (K.det ^ 2) * hpair
  unfold rightConic
  apply residual_conic_zero_of_sextic (hV := hG) (hj := hj)
    (hA := hsa.symm ▸ mul_ne_zero hd ha) (hD := hdet.symm ▸ pow_ne_zero 2 hd) (hC := hc')
  have hEquation : tripletEquation (U * K.adjugate) = 0 := by
    rw [hV, tripletEquation_smul, hs, mul_zero]
  simpa only [tripletEquation, Matrix.det_mul, Matrix.adjugate_mul_distrib,
    leftMoment_apply, mul_assoc] using hEquation

/-- The ideal of residual constraints after eliminating the projective partner. -/
noncomputable def residualIdeal (T U : M₃) : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span (Set.range (residualEquations T U))

/-- Every compatible pair with nonzero product and vanishing sextics satisfies the
three equations used by the degree-eight rank certificate. -/
theorem residualEquations_zero [IsDomain R] (T U : M₃) (q : Fin 3 → R) (V : M₃)
    (hj : (cyclicMatrix (T * U) cyclicVector).det ≠ 0)
    (hd : (pencil (T * U) q).det ≠ 0)
    (hV : U * (pencil (T * U) q).adjugate = (pencil (T * U) q).det • V)
    (hA : singlet (pencil (T * U) q * T) ≠ 0) (hB : singlet V ≠ 0)
    (hs : tripletEquation (pencil (T * U) q * T) = 0)
    (ht : tripletEquation V = 0)
    (hpair : singlet (pencil (T * U) q * T) * singlet V = singlet T * singlet U) :
    ∀ p ∈ residualIdeal T U, eval q p = 0 := by
  let K := pencil (T * U) q
  have hc : Commute K (T * U) := (pencil_commutes (Commute.refl (T * U)) q).symm
  have hpair' : singlet (K * T) * singlet (U * K.adjugate) = singlet T * singlet U * K.det := by
    rw [hV, singlet_smul, ← mul_left_comm, hpair, mul_comm]
  obtain ⟨hC, hQ⟩ := compatibility_leftConic_zero T U K hc hj hd hA hs hpair'
  have hR := pulledRightConic_zero T U K V hc hj hd hV hB ht hpair
  have hrel i : eval q (residualEquations T U i) = 0 := by
    have he := congr_fun (eval_residualEquations T U q) i
    rw [he]
    fin_cases i
    · exact hC
    · exact hQ
    · exact hR
  have hspan : residualIdeal T U ≤ RingHom.ker (eval q) := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hrel i)
  intro p hp
  exact RingHom.mem_ker.mp (hspan hp)

section CompatiblePairs

variable {K : Type*} [Field K]

local notation "Triplet" => Matrix (Fin 3) (Fin 3) K

private lemma pencil_scale (G : Triplet) (c : K) (q : Fin 3 → K) :
    pencil G (c • q) = c • pencil G q := by
  unfold pencil
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

private lemma pencil_origin (G : Triplet) : pencil G cyclicVector = 1 := by
  simp [pencil, cyclicVector, Fin.sum_univ_three]

private lemma commutant_pencil {G X : Triplet}
    (hc : Commute X G) (hj : (cyclicMatrix G cyclicVector).det ≠ 0) :
    ∃ q, pencil G q = X := by
  let J := cyclicMatrix G cyclicVector
  let u := J.adjugate *ᵥ (X *ᵥ cyclicVector)
  have he : J.det • X = pencil G u := cyclic_commutant_scaled cyclicVector hc hj
  refine ⟨J.det⁻¹ • u, ?_⟩
  rw [pencil_scale, ← he, smul_smul, inv_mul_cancel₀ hj, one_smul]

/-- The degree-eight quotient bound enforces proportionality against every
compatible invertible pair satisfying the triplet sextics. -/
theorem triplets_proportional (T U T' U' : Triplet)
    (hL : T' * U' = T * U) (hR : U' * T' = U * T)
    (hS : singlet T' * singlet U' = singlet T * singlet U)
    (hT : T.det ≠ 0) (hU : U.det ≠ 0) (hgs : singlet T * singlet U ≠ 0)
    (hj : (cyclicMatrix (T * U) cyclicVector).det ≠ 0)
    (hs : tripletEquation T = 0) (ht : tripletEquation U = 0)
    (hs' : tripletEquation T' = 0) (ht' : tripletEquation U' = 0)
    (hD : Module.finrank K (LinearMap.range
      ((Ideal.Quotient.mkₐ K (residualIdeal T U)).toLinearMap.comp
        (homogeneousSubmodule (Fin 3) K 8).subtype)) ≤ 1) :
    ∃ c : K, T' = c • T := by
  let X := T' * T⁻¹
  have hTi : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  have hX : X * T = T' := by
    rw [show X = T' * T⁻¹ by rfl, mul_assoc, Matrix.nonsing_inv_mul T hTi, mul_one]
  have hXt : Commute X (T * U) := by
    change X * (T * U) = (T * U) * X
    calc
      X * (T * U) = T' * U := by rw [← mul_assoc, hX]
      _ = (T' * U') * X := by
        unfold X
        rw [mul_assoc, ← mul_assoc U', hR, mul_assoc, Matrix.mul_nonsing_inv T hTi, mul_one]
      _ = (T * U) * X := by rw [hL]
  obtain ⟨q, hq⟩ := commutant_pencil hXt hj
  let P := pencil (T * U) q
  have hPT : P * T = T' := by rw [show P = X from hq, hX]
  have hprod : P * (T * U') = T * U := by rw [← mul_assoc, hPT, hL]
  have hd : P.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hprod
    simp only [Matrix.det_mul, hz, zero_mul] at he
    exact (mul_ne_zero hT hU) he.symm
  have hpartner : U * P.adjugate = P.det • U' := by
    have hcomm : Commute P (T * U) := (pencil_commutes (Commute.refl _) _).symm
    have hscaled : P * (T * (U * P.adjugate)) = P * (T * (P.det • U')) := by
      calc
        P * (T * (U * P.adjugate)) = (P * (T * U)) * P.adjugate := by simp only [mul_assoc]
        _ = (T * U) * (P.det • 1) := by
          rw [hcomm.eq, mul_assoc, Matrix.mul_adjugate]
        _ = P * (T * (P.det • U')) := by
          rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, mul_one, hprod]
    have hinv : IsUnit P.det := isUnit_iff_ne_zero.mpr hd
    have he := congrArg (P⁻¹ * ·) hscaled
    simp only [← mul_assoc, Matrix.nonsing_inv_mul P hinv, one_mul] at he
    have he' := congrArg (T⁻¹ * ·) he
    simpa only [← mul_assoc, Matrix.nonsing_inv_mul T hTi, one_mul] using he'
  have hS' : singlet T' * singlet U' ≠ 0 := hS.symm ▸ hgs
  have hzQ := residualEquations_zero T U q U' hj hd hpartner
    (hPT.symm ▸ left_ne_zero_of_mul hS') (right_ne_zero_of_mul hS')
    (hPT.symm ▸ hs') ht' (hPT.symm ▸ hS)
  have hz0 : ∀ p ∈ residualIdeal T U, eval cyclicVector p = 0 := by
    apply residualEquations_zero T U cyclicVector U hj
    · rw [pencil_origin, Matrix.det_one]; exact one_ne_zero
    · rw [pencil_origin, Matrix.det_one, Matrix.adjugate_one, mul_one, one_smul]
    · rw [pencil_origin, one_mul]; exact left_ne_zero_of_mul hgs
    · exact right_ne_zero_of_mul hgs
    · rwa [pencil_origin, one_mul]
    · exact ht
    · rw [pencil_origin, one_mul]
  have h0 : (cyclicVector : Fin 3 → K) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  have hz0' : ∀ p ∈ residualIdeal T U, aeval (cyclicVector : Fin 3 → K) p = 0 := by
    simpa only [aeval_eq_eval] using hz0
  have hzQ' : ∀ p ∈ residualIdeal T U, aeval q p = 0 := by
    simpa only [aeval_eq_eval] using hzQ
  obtain ⟨c, hc⟩ := PeriodicMPSFourSiteInterpolation.common_zeros_proportional_of_finrank_le_one
    (residualIdeal T U) 8 (by decide) cyclicVector q h0 hz0' hzQ' hD
  refine ⟨c, ?_⟩
  rw [← hPT, show P = pencil (T * U) q from rfl, hc, pencil_scale, pencil_origin,
    Matrix.smul_mul, one_mul]

end CompatiblePairs

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualSystem
