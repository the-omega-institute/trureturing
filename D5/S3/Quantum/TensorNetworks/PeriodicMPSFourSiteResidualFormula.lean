/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjugate identities for the four-site residual equations. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteSextic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Tactic.LinearCombination

/-! Coefficient formulas for removing the determinant divisor from a pencil sextic. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualFormula

open Matrix
open scoped Matrix BigOperators
open PeriodicMPSFourSiteSextic (sextic sextic_square_and_triplet hankelDet)

variable {R : Type*} [CommRing R]

/-- The triplet block in the rational swap basis, ordered by the six necklace amplitudes. -/
def triplet (a b c d e f : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, 2 * b, c; b, c + d, e; c, 2 * e, f]

/-- The singlet amplitude prescribed by a triplet block in the rational swap basis. -/
def singlet (M : Matrix (Fin 3) (Fin 3) R) : R :=
  M 1 1 - 2 * M 0 2

/-- The mixed two-by-two minor of a three-by-three bilinear pairing is the
adjugate pairing of the two cross products. -/
theorem mixed_adjugate_minor (M : Matrix (Fin 3) (Fin 3) R) (r s v w : Fin 3 → R) :
    dotProduct r (M *ᵥ v) * dotProduct s (M *ᵥ w) -
      dotProduct r (M *ᵥ w) * dotProduct s (M *ᵥ v) =
    dotProduct (crossProduct v w) (M.adjugate *ᵥ crossProduct r s) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply, Matrix.adjugate_fin_three]
  ring

private lemma twice_cubic (a b c d e f : R) :
    let T := triplet a b c d e f
    let k := d - c
    T.det + k * singlet T.adjugate =
      2 * (hankelDet a b c e f + k * (a * f - 2 * b * e + c ^ 2) + c * k ^ 2) := by
  dsimp only
  simp [triplet, singlet, Matrix.det_fin_three, Matrix.adjugate_fin_three, hankelDet]
  ring

private lemma triplet_det (a b c d e f : R) :
    (triplet a b c d e f).det =
      2 * hankelDet a b c e f + (d - c) * (a * f - c ^ 2) := by
  simp [triplet, Matrix.det_fin_three, hankelDet]
  ring

private lemma triplet_singlet (a b c d e f : R) :
    singlet (triplet a b c d e f) = d - c := by
  simp [singlet, triplet]
  ring

/-- A division-free expression of the pencil sextic in terms of the triplet determinant
and the singlet amplitudes of the triplet and its adjugate. -/
theorem four_mul_sextic (a b c d e f : R) :
    let T := triplet a b c d e f
    let A := singlet T
    4 * sextic a b c d e f =
      -(T.det + A * singlet T.adjugate) ^ 2 - 4 * A ^ 3 * T.det := by
  dsimp only
  rw [sextic_square_and_triplet, triplet_singlet, twice_cubic, triplet_det]
  ring

local notation "M₃" => Matrix (Fin 3) (Fin 3) R

/-- A quadratic polynomial in a triplet block, in power coordinates. -/
def pencil (G : M₃) (q : Fin 3 → R) : M₃ :=
  ∑ i : Fin 3, q i • G ^ i.val

/-- The columns are the first three iterates of the chosen cyclic vector. -/
def cyclicMatrix (G : M₃) (v : Fin 3 → R) : M₃ :=
  Matrix.of fun i j => (G ^ j.val *ᵥ v) i

lemma pencil_commutes {G M : M₃} (h : Commute M G) (q : Fin 3 → R) :
    Commute M (pencil G q) := by
  apply Commute.sum_right
  intro i _
  change _ * _ = _ * _
  rw [Matrix.mul_smul, Matrix.smul_mul, (h.pow_right i.val).eq]

private lemma pencil_mulVec (G : M₃) (v q : Fin 3 → R) :
    pencil G q *ᵥ v = cyclicMatrix G v *ᵥ q := by
  rw [pencil, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j : Fin 3, q j * (G ^ j.val *ᵥ v) i) =
    ∑ j : Fin 3, (G ^ j.val *ᵥ v) i * q j
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The cyclic-vector argument without division. Multiplying a commuting
matrix by the determinant of the cyclic matrix puts it in the power pencil. -/
theorem cyclic_commutant_scaled {G M : M₃} (v : Fin 3 → R) (h : Commute M G)
    [IsDomain R] (hj : (cyclicMatrix G v).det ≠ 0) :
    let J := cyclicMatrix G v
    J.det • M = pencil G (J.adjugate *ᵥ (M *ᵥ v)) := by
  dsimp only
  let J := cyclicMatrix G v
  let N := pencil G (J.adjugate *ᵥ (M *ᵥ v))
  change J.det • M = N
  have hv : (J.det • M) *ᵥ v = N *ᵥ v := by
    dsimp only [N]
    rw [pencil_mulVec, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, J]
  have hm (i : ℕ) : Commute (J.det • M) (G ^ i) := by
    change _ * _ = _ * _
    rw [Matrix.smul_mul, Matrix.mul_smul, (h.pow_right i).eq]
  have hn (i : ℕ) : Commute N (G ^ i) :=
    ((pencil_commutes (Commute.refl G) _).symm.pow_right i)
  have hcols : (J.det • M) * J = N * J := by
    ext i j
    change (((J.det • M) * J).col j) i = ((N * J).col j) i
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col]
    change (((J.det • M) *ᵥ (G ^ j.val *ᵥ v)) i) = ((N *ᵥ (G ^ j.val *ᵥ v)) i)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hm j.val).eq, (hn j.val).eq,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv]
  have hcancel := congrArg (· * J.adjugate) hcols
  simp only [mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, mul_one] at hcancel
  ext i j
  exact mul_left_cancel₀ hj (congr_fun (congr_fun hcancel i) j)

private lemma same_on_pencil {G M : M₃} (v : Fin 3 → R) [IsDomain R]
    (h : Commute M G) (hj : (cyclicMatrix G v).det ≠ 0)
    (f g : M₃ →ₗ[R] R) (he : ∀ i : Fin 3, f (G ^ i.val) = g (G ^ i.val)) :
    f M = g M := by
  apply mul_left_cancel₀ hj
  change (cyclicMatrix G v).det • f M = (cyclicMatrix G v).det • g M
  rw [← map_smul, ← map_smul, cyclic_commutant_scaled v h hj]
  simp only [pencil, map_sum, map_smul, he]

/-- The moment matrix pairing the three powers by a linear functional. -/
def hankel (G : M₃) (β : M₃ →ₗ[R] R) : M₃ :=
  Matrix.of fun i j => β (G ^ (i.val + j.val))

/-- The adjugate solution for the Hankel moments of the second functional. -/
def hankelSolver (G : M₃) (β η : M₃ →ₗ[R] R) : M₃ :=
  pencil G ((hankel G β).adjugate *ᵥ fun i => η (G ^ i.val))

/-- The adjugate solution for the row pairing on the cyclic vectors. -/
def cyclicSolver (G : M₃) (β : M₃ →ₗ[R] R) (v : Fin 3 → R) : Fin 3 → R :=
  (fun i : Fin 3 => β (G ^ i.val)) ᵥ* (cyclicMatrix G v).adjugate

private def matrixPairing (r v : Fin 3 → R) : M₃ →ₗ[R] R where
  toFun M := r ⬝ᵥ (M *ᵥ v)
  map_add' A B := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by rw [Matrix.smul_mulVec, dotProduct_smul]; rfl

private lemma cyclicSolver_pairing {G M : M₃} [IsDomain R] (β : M₃ →ₗ[R] R) (v : Fin 3 → R)
    (hm : Commute M G) (hj : (cyclicMatrix G v).det ≠ 0) :
    matrixPairing (cyclicSolver G β v) v M = (cyclicMatrix G v).det * β M := by
  change matrixPairing (cyclicSolver G β v) v M = ((cyclicMatrix G v).det • β) M
  apply same_on_pencil v hm hj
  intro i
  let J := cyclicMatrix G v
  let b : Fin 3 → R := fun j => β (G ^ j.val)
  have hsolve : (b ᵥ* J.adjugate) ᵥ* J = J.det • b := by
    rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
  exact congr_fun hsolve i

private lemma hankelSolver_pairing {G M : M₃} [IsDomain R] (β η : M₃ →ₗ[R] R) (v : Fin 3 → R)
    (hm : Commute M G) (hj : (cyclicMatrix G v).det ≠ 0) :
    β (hankelSolver G β η * M) = (hankel G β).det * η M := by
  change (β.comp (LinearMap.mulLeft R (hankelSolver G β η))) M = ((hankel G β).det • η) M
  apply same_on_pencil v hm hj
  intro i
  let H := hankel G β
  let b := H.adjugate *ᵥ fun j : Fin 3 => η (G ^ j.val)
  have hsolve : H *ᵥ b = H.det • (fun j : Fin 3 => η (G ^ j.val)) := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  change β (pencil G b * G ^ i.val) = H.det * η (G ^ i.val)
  rw [pencil, Finset.sum_mul, map_sum]
  simp only [Matrix.smul_mul, map_smul, ← pow_add]
  have he : (H *ᵥ b) i = H.det * η (G ^ i.val) := congr_fun hsolve i
  rw [← he]
  change (∑ j : Fin 3, b j * β (G ^ (j.val + i.val))) =
    ∑ j : Fin 3, β (G ^ (i.val + j.val)) * b j
  exact Finset.sum_congr rfl fun j _ => by
    rw [Nat.add_comm j.val i.val, mul_comm]

/-- The cleared determinant identity for the residual pencil. The matrices
in the cyclic and Hankel systems may be formed over the coefficient ring. -/
theorem cleared_pencil_minor {G K : M₃} [IsDomain R] (β η : M₃ →ₗ[R] R) (v : Fin 3 → R)
    (hV : Commute K.adjugate G) (hj : (cyclicMatrix G v).det ≠ 0) :
    let J := cyclicMatrix G v
    let H := hankel G β
    let L := hankelSolver G β η
    let r := cyclicSolver G β v
    let V := K.adjugate
    let W := (v ⨯₃ (L *ᵥ v)) ⬝ᵥ (K *ᵥ (r ⨯₃ (r ᵥ* L)))
    J.det ^ 2 * (β V * β (L * (L * V)) - H.det ^ 2 * η V ^ 2) = K.det * W := by
  dsimp only
  let J := cyclicMatrix G v
  let H := hankel G β
  let L := hankelSolver G β η
  let r := cyclicSolver G β v
  let V := K.adjugate
  have hL : Commute L G := (pencil_commutes (Commute.refl G) _).symm
  have hVL : Commute V L := pencil_commutes hV _
  have hpair {M : M₃} (hm : Commute M G) :
      r ⬝ᵥ (M *ᵥ v) = J.det * β M := cyclicSolver_pairing β v hm hj
  have hleft : (r ᵥ* L) ⬝ᵥ (V *ᵥ v) = J.det * (H.det * η V) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hpair (hL.mul_left hV),
      hankelSolver_pairing β η v hV hj]
  have hright : r ⬝ᵥ (V *ᵥ (L *ᵥ v)) = J.det * (H.det * η V) := by
    rw [Matrix.mulVec_mulVec, hVL.eq, hpair (hL.mul_left hV),
      hankelSolver_pairing β η v hV hj]
  have hboth : (r ᵥ* L) ⬝ᵥ (V *ᵥ (L *ᵥ v)) = J.det * β (L * (L * V)) := by
    have hvec : V *ᵥ (L *ᵥ v) = (L * V) *ᵥ v := by rw [Matrix.mulVec_mulVec, hVL.eq]
    rw [hvec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hpair (hL.mul_left (hL.mul_left hV))]
  have hadj : V.adjugate = K.det • K := by
    simpa [V] using Matrix.adjugate_adjugate' K
  have he := mixed_adjugate_minor V r (r ᵥ* L) v (L *ᵥ v)
  rw [hpair hV, hleft, hright, hboth, hadj, Matrix.smul_mulVec, dotProduct_smul] at he
  change J.det ^ 2 * (β V * β (L * (L * V)) - H.det ^ 2 * η V ^ 2) =
    K.det * ((v ⨯₃ (L *ᵥ v)) ⬝ᵥ (K *ᵥ (r ⨯₃ (r ᵥ* L))))
  linear_combination he

private lemma cancel_right_of_det_ne_zero {P X Y : M₃} [IsDomain R]
    (hP : P.det ≠ 0) (h : X * P = Y * P) : X = Y := by
  have he := congrArg (· * P.adjugate) h
  simp only [mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, mul_one] at he
  ext i j
  exact mul_left_cancel₀ hP (congr_fun (congr_fun he i) j)

/-- The adjugate of an invertible pencil coordinate commutes with the
observed triplet block. -/
theorem adjugate_commutes_of_det_ne_zero {G K : M₃} [IsDomain R]
    (h : Commute K G) (hd : K.det ≠ 0) : Commute K.adjugate G := by
  change K.adjugate * G = G * K.adjugate
  apply cancel_right_of_det_ne_zero hd
  simp only [mul_assoc, ← h.eq, ← mul_assoc K.adjugate K, Matrix.adjugate_mul,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

/-- The singlet coordinate as a linear map on triplet matrices. -/
def singletLinear : M₃ →ₗ[R] R where
  toFun := singlet
  map_add' A B := by simp only [singlet, Matrix.add_apply]; ring
  map_smul' c A := by simp only [singlet, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The polynomial equation imposing singlet compatibility once the
partner triplet is supplied by the adjugate. -/
def productConstraint (A g : R) (β : M₃ →ₗ[R] R) (K : M₃) : R :=
  A * β K.adjugate - g * K.det

/-- The quotient of the sextic after clearing the denominators of the
cyclic and Hankel systems and removing the determinant divisor. -/
def residualConic (G K : M₃) (v : Fin 3 → R) (β η : M₃ →ₗ[R] R) (A τ g : R) : R :=
  let J := (cyclicMatrix G v).det
  let H := (hankel G β).det
  let L := hankelSolver G β η
  let r := cyclicSolver G β v
  let B := β K.adjugate
  let E := η K.adjugate
  let Z := β (L * (L * K.adjugate))
  let W := (v ⨯₃ (L *ᵥ v)) ⬝ᵥ (K *ᵥ (r ⨯₃ (r ᵥ* L)))
  (-2) * τ * E * g * J ^ 2 * H ^ 2 - 4 * τ * A ^ 2 * g * J ^ 2 * H ^ 2 -
    τ ^ 2 * B * J ^ 2 * H ^ 2 - g ^ 2 * J ^ 2 * Z + g * A * W

section ChangeCoefficients

variable {S : Type*} [CommRing S] (f : R →+* S)

private lemma matrix_map_smul (c : R) (M : M₃) :
    f.mapMatrix (c • M) = f c • f.mapMatrix M := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

/-- A polynomial pencil commutes with change of coefficients. -/
theorem map_pencil (G : M₃) (q : Fin 3 → R) :
    f.mapMatrix (pencil G q) = pencil (f.mapMatrix G) (f ∘ q) := by
  simp only [pencil, map_sum, matrix_map_smul, map_pow, Function.comp_apply]

/-- The cyclic determinant is a polynomial in the block and vector entries. -/
theorem map_cyclicMatrix (G : M₃) (v : Fin 3 → R) :
    f.mapMatrix (cyclicMatrix G v) = cyclicMatrix (f.mapMatrix G) (f ∘ v) := by
  ext i j
  change f ((G ^ j.val *ᵥ v) i) = (f.mapMatrix G ^ j.val *ᵥ (f ∘ v)) i
  rw [f.map_mulVec, ← RingHom.mapMatrix_apply, map_pow]

lemma map_mulVec (M : M₃) (v : Fin 3 → R) :
    f ∘ (M *ᵥ v) = f.mapMatrix M *ᵥ (f ∘ v) :=
  funext (f.map_mulVec M v)

lemma map_vecMul (v : Fin 3 → R) (M : M₃) :
    f ∘ (v ᵥ* M) = (f ∘ v) ᵥ* f.mapMatrix M :=
  funext (f.map_vecMul M v)

lemma map_cross (v w : Fin 3 → R) :
    f ∘ (v ⨯₃ w) = (f ∘ v) ⨯₃ (f ∘ w) := by
  funext i
  fin_cases i <;> simp [cross_apply]

lemma map_hankel (β : M₃ →ₗ[R] R)
    (β' : Matrix (Fin 3) (Fin 3) S →ₗ[S] S) (hβ : ∀ M, f (β M) = β' (f.mapMatrix M))
    (G : M₃) :
    f.mapMatrix (hankel G β) = hankel (f.mapMatrix G) β' := by
  ext i j
  change f (β (G ^ (i.val + j.val))) = β' (f.mapMatrix G ^ (i.val + j.val))
  rw [hβ, map_pow]

lemma map_hankelSolver (β η : M₃ →ₗ[R] R)
    (β' η' : Matrix (Fin 3) (Fin 3) S →ₗ[S] S)
    (hβ : ∀ M, f (β M) = β' (f.mapMatrix M))
    (hη : ∀ M, f (η M) = η' (f.mapMatrix M)) (G : M₃) :
    f.mapMatrix (hankelSolver G β η) = hankelSolver (f.mapMatrix G) β' η' := by
  unfold hankelSolver
  rw [map_pencil, map_mulVec, f.map_adjugate, map_hankel f β β' hβ]
  have he : (f ∘ (fun i : Fin 3 => η (G ^ i.val))) =
      (fun i : Fin 3 => η' (f.mapMatrix G ^ i.val)) := by
    funext i
    change f (η (G ^ i.val)) = η' (f.mapMatrix G ^ i.val)
    rw [hη, map_pow]
  rw [he]

lemma map_cyclicSolver (β : M₃ →ₗ[R] R)
    (β' : Matrix (Fin 3) (Fin 3) S →ₗ[S] S) (hβ : ∀ M, f (β M) = β' (f.mapMatrix M))
    (G : M₃) (v : Fin 3 → R) :
    f ∘ cyclicSolver G β v = cyclicSolver (f.mapMatrix G) β' (f ∘ v) := by
  unfold cyclicSolver
  rw [map_vecMul, f.map_adjugate, map_cyclicMatrix]
  congr 1
  funext i
  change f (β (G ^ i.val)) = β' (f.mapMatrix G ^ i.val)
  rw [hβ, map_pow]

/-- The cubic product constraint specializes with its input linear functional. -/
theorem map_productConstraint (β : M₃ →ₗ[R] R)
    (β' : Matrix (Fin 3) (Fin 3) S →ₗ[S] S) (hβ : ∀ M, f (β M) = β' (f.mapMatrix M))
    (A g : R) (K : M₃) :
    f (productConstraint A g β K) = productConstraint (f A) (f g) β' (f.mapMatrix K) := by
  simp only [productConstraint, map_sub, map_mul, hβ, f.map_adjugate, f.map_det]

/-- The cleared residual conic specializes without any assumption on inverses. -/
theorem map_residualConic (β η : M₃ →ₗ[R] R)
    (β' η' : Matrix (Fin 3) (Fin 3) S →ₗ[S] S)
    (hβ : ∀ M, f (β M) = β' (f.mapMatrix M))
    (hη : ∀ M, f (η M) = η' (f.mapMatrix M)) (G K : M₃) (v : Fin 3 → R) (A τ g : R) :
    f (residualConic G K v β η A τ g) =
      residualConic (f.mapMatrix G) (f.mapMatrix K) (f ∘ v) β' η' (f A) (f τ) (f g) := by
  unfold residualConic
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, hβ, hη,
    f.map_det, f.map_adjugate, map_cyclicMatrix, map_hankel f β β' hβ,
    map_hankelSolver f β η β' η' hβ hη, f.map_dotProduct, map_cross, map_mulVec, map_vecMul,
    map_cyclicSolver f β β' hβ]

end ChangeCoefficients

/-- A mixed adjugate minor yields a sextic decomposition with coefficients obtained
by clearing the cyclic and Hankel determinants from the two linear systems. -/
theorem cleared_sextic_decomposition (A B D E Z W τ G J H : R)
    (hminor : J ^ 2 * (B * Z - H ^ 2 * E ^ 2) = D * W) :
    let C := A * B - G * D
    let P := A * D
    let S := τ ^ 2 * D * J ^ 2 * H ^ 2 - G * A * J ^ 2 * Z
    let Q := -2 * τ * E * G * J ^ 2 * H ^ 2 - 4 * τ * A ^ 2 * G * J ^ 2 * H ^ 2 -
      τ ^ 2 * B * J ^ 2 * H ^ 2 - G ^ 2 * J ^ 2 * Z + G * A * W
    G * J ^ 2 * H ^ 2 * (-(τ * D + A * E) ^ 2 - 4 * A ^ 3 * τ * D) =
      C * S + P * Q := by
  dsimp only
  linear_combination (G * A ^ 2) * hminor

/-- For an invertible compatible pair, vanishing of the pencil sextic
forces vanishing of the residual conic. -/
theorem residual_conic_zero_of_sextic {G K : M₃} [IsDomain R]
    (β η : M₃ →ₗ[R] R) (v : Fin 3 → R) (A τ g : R)
    (hV : Commute K.adjugate G) (hj : (cyclicMatrix G v).det ≠ 0)
    (hA : A ≠ 0) (hD : K.det ≠ 0)
    (hC : productConstraint A g β K = 0)
    (hs : -(τ * K.det + A * η K.adjugate) ^ 2 - 4 * A ^ 3 * τ * K.det = 0) :
    residualConic G K v β η A τ g = 0 := by
  have h := cleared_pencil_minor β η v hV hj
  dsimp only at h
  have hh := cleared_sextic_decomposition A (β K.adjugate) K.det (η K.adjugate)
    (β (hankelSolver G β η * (hankelSolver G β η * K.adjugate)))
    ((v ⨯₃ (hankelSolver G β η *ᵥ v)) ⬝ᵥ
      (K *ᵥ (cyclicSolver G β v ⨯₃ (cyclicSolver G β v ᵥ* hankelSolver G β η))))
    τ g (cyclicMatrix G v).det (hankel G β).det h
  dsimp only at hh
  change _ * (-(τ * K.det + A * η K.adjugate) ^ 2 - 4 * A ^ 3 * τ * K.det) =
    productConstraint A g β K * _ + (A * K.det) * residualConic G K v β η A τ g at hh
  rw [hs, hC, zero_mul, zero_add, mul_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero hA hD)

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualFormula
