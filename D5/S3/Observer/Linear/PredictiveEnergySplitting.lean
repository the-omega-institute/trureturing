/- GID: D5/S3/Observer/Linear/PredictiveEnergySplitting
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/PredictiveEnergySplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the energy-orthogonal predictive lift and derive its dynamical intertwining. -/

import Mathlib

/-!
The inverse witnesses below are equations for the actual matrices S and
O C O-transpose. Neither lift intertwining nor zero energy cross terms are
assumed. The final constructor chooses C=S-inverse and Q=(O C O-transpose)-inverse
from positive definiteness and injectivity of the observation transpose.
This module does not prove a Gaussian change-of-variables formula or construct
an infinite-dimensional metaplectic representation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.PredictiveEnergySplitting

variable {n r h : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype h] [DecidableEq h]

noncomputable def covariance (O : Matrix r n ℝ) (C : Matrix n n ℝ) : Matrix r r ℝ :=
  O * C * O.transpose

noncomputable def lift (C : Matrix n n ℝ) (O : Matrix r n ℝ)
    (Q : Matrix r r ℝ) : Matrix n r ℝ := C * O.transpose * Q

noncomputable def hidden (L : Matrix n r ℝ) (O : Matrix r n ℝ) : Matrix n n ℝ :=
  1 - L * O

/-- The Hamiltonian generator is skew with respect to the inverse energy matrix. -/
theorem hamiltonian_covariance (J S C : Matrix n n ℝ)
    (hJ : J.transpose = -J) (hS : S.transpose = S)
    (hSC : S * C = 1) (hCS : C * S = 1) :
    (J * S) * C + C * (J * S).transpose = 0 := by
  have h1 : (J * S) * C = J := by rw [Matrix.mul_assoc, hSC, Matrix.mul_one]
  have h2 : C * (J * S).transpose = -J := by
    rw [Matrix.transpose_mul, hS, hJ, ← Matrix.mul_assoc, hCS, Matrix.one_mul]
  rw [h1, h2, add_neg_cancel]

/-- Covariance skewness descends along an actual observation intertwiner. -/
theorem reduced_covariance_skew (A C : Matrix n n ℝ) (O : Matrix r n ℝ)
    (K : Matrix r r ℝ) (hAC : A * C + C * A.transpose = 0)
    (hObs : O * A = K * O) :
    K * covariance O C + covariance O C * K.transpose = 0 := by
  have ht : A.transpose * O.transpose = O.transpose * K.transpose := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hObs
  unfold covariance
  calc
    K * (O * C * O.transpose) + O * C * O.transpose * K.transpose =
        (K * O) * C * O.transpose + O * C * (O.transpose * K.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = (O * A) * C * O.transpose + O * C * (A.transpose * O.transpose) := by
      rw [← hObs, ← ht]
    _ = O * (A * C + C * A.transpose) * O.transpose := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hAC, Matrix.mul_zero, Matrix.zero_mul]

private theorem inverse_covariance_skew (P Q K : Matrix r r ℝ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hk : K * P + P * K.transpose = 0) :
    Q * K + K.transpose * Q = 0 := by
  have ht := congrArg (fun M : Matrix r r ℝ => Q * M * Q) hk
  have h1 : Q * (K * P) * Q = Q * K := by
    calc
      Q * (K * P) * Q = (Q * K) * (P * Q) := by simp only [Matrix.mul_assoc]
      _ = Q * K := by rw [hPQ, Matrix.mul_one]
  have h2 : Q * (P * K.transpose) * Q = K.transpose * Q := by
    calc
      Q * (P * K.transpose) * Q = (Q * P) * K.transpose * Q := by
        simp only [Matrix.mul_assoc]
      _ = K.transpose * Q := by rw [hQP, Matrix.one_mul]
  simpa only [Matrix.mul_add, Matrix.add_mul, h1, h2,
    Matrix.mul_zero, Matrix.zero_mul] using ht

theorem lift_right_inverse (C : Matrix n n ℝ) (O : Matrix r n ℝ)
    (Q : Matrix r r ℝ) (hPQ : covariance O C * Q = 1) :
    O * lift C O Q = 1 := by
  simpa only [lift, covariance, Matrix.mul_assoc] using hPQ

/-- The minimum-energy lift intertwines the generators; this is a derived result. -/
theorem lift_intertwines (A C : Matrix n n ℝ) (O : Matrix r n ℝ)
    (K Q : Matrix r r ℝ) (hAC : A * C + C * A.transpose = 0)
    (hObs : O * A = K * O) (hPQ : covariance O C * Q = 1)
    (hQP : Q * covariance O C = 1) :
    A * lift C O Q = lift C O Q * K := by
  have hred := reduced_covariance_skew A C O K hAC hObs
  have hdual := inverse_covariance_skew (covariance O C) Q K hPQ hQP hred
  have h1 : A * C = -(C * A.transpose) := by
    apply eq_neg_iff_add_eq_zero.mpr
    exact hAC
  have h2 : -(K.transpose * Q) = Q * K := by
    symm
    exact eq_neg_iff_add_eq_zero.mpr hdual
  have ht : A.transpose * O.transpose = O.transpose * K.transpose := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hObs
  unfold lift
  calc
    A * (C * O.transpose * Q) = (A * C) * O.transpose * Q := by
      simp only [Matrix.mul_assoc]
    _ = (-(C * A.transpose)) * O.transpose * Q := by rw [h1]
    _ = -(C * (A.transpose * O.transpose)) * Q := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(C * (O.transpose * K.transpose)) * Q := by rw [ht]
    _ = (C * O.transpose) * (-(K.transpose * Q)) := by
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    _ = (C * O.transpose) * (Q * K) := by rw [h2]
    _ = (C * O.transpose * Q) * K := by rw [Matrix.mul_assoc]

private theorem inverse_symmetric (P Q : Matrix r r ℝ)
    (hP : P.transpose = P) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Q.transpose = Q := by
  have ht : P * Q.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, hP] using
      congrArg Matrix.transpose hQP
  calc
    Q.transpose = 1 * Q.transpose := by rw [Matrix.one_mul]
    _ = (Q * P) * Q.transpose := by rw [hQP]
    _ = Q * (P * Q.transpose) := Matrix.mul_assoc _ _ _
    _ = Q := by rw [ht, Matrix.mul_one]

/-- The lifted quadratic form is Q and the lift is S-orthogonal to the hidden kernel. -/
theorem lift_energy_blocks (S C : Matrix n n ℝ) (O : Matrix r n ℝ)
    (Q : Matrix r r ℝ) (R : Matrix n h ℝ)
    (hC : C.transpose = C) (hCS : C * S = 1)
    (hPQ : covariance O C * Q = 1) (hQP : Q * covariance O C = 1)
    (hOR : O * R = 0) :
    (lift C O Q).transpose * S = Q * O ∧
      (lift C O Q).transpose * S * lift C O Q = Q ∧
      (lift C O Q).transpose * S * R = 0 := by
  have hP : (covariance O C).transpose = covariance O C := by
    simp only [covariance, Matrix.transpose_mul, Matrix.transpose_transpose, hC,
      Matrix.mul_assoc]
  have hQ := inverse_symmetric (covariance O C) Q hP hPQ hQP
  have hL : (lift C O Q).transpose * S = Q * O := by
    unfold lift
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hC, hQ]
    calc
      (Q * (O * C)) * S = (Q * O) * (C * S) := by simp only [Matrix.mul_assoc]
      _ = Q * O := by rw [hCS, Matrix.mul_one]
  refine ⟨hL, ?_, ?_⟩
  · rw [hL, Matrix.mul_assoc, lift_right_inverse C O Q hPQ, Matrix.mul_one]
  · rw [hL, Matrix.mul_assoc, hOR, Matrix.mul_zero]

/-- Constructed hidden projection is idempotent, kills the lift, and commutes with A. -/
theorem hidden_projection (A : Matrix n n ℝ) (O : Matrix r n ℝ)
    (L : Matrix n r ℝ) (K : Matrix r r ℝ)
    (hOL : O * L = 1) (hOA : O * A = K * O) (hAL : A * L = L * K) :
    O * hidden L O = 0 ∧ hidden L O * L = 0 ∧
      hidden L O * hidden L O = hidden L O ∧
      A * hidden L O = hidden L O * A := by
  have hp : (L * O) * (L * O) = L * O := by
    calc
      (L * O) * (L * O) = L * (O * L) * O := by simp only [Matrix.mul_assoc]
      _ = L * O := by rw [hOL, Matrix.mul_one]
  have hl : (L * O) * L = L := by rw [Matrix.mul_assoc, hOL, Matrix.mul_one]
  have ho : O * (L * O) = O := by rw [← Matrix.mul_assoc, hOL, Matrix.one_mul]
  have ha : A * (L * O) = (L * O) * A := by
    calc
      A * (L * O) = (A * L) * O := (Matrix.mul_assoc _ _ _).symm
      _ = (L * K) * O := by rw [hAL]
      _ = L * (O * A) := by rw [Matrix.mul_assoc, hOA]
      _ = (L * O) * A := (Matrix.mul_assoc _ _ _).symm
  unfold hidden
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, ho, sub_self]
  · rw [Matrix.sub_mul, Matrix.one_mul, hl, sub_self]
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hp]
    abel
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ha]

/-- The complete coordinate Hessian has no visible-hidden energy terms. -/
theorem coordinate_hessian (S C : Matrix n n ℝ) (O : Matrix r n ℝ)
    (Q : Matrix r r ℝ) (R : Matrix n h ℝ)
    (hS : S.transpose = S) (hC : C.transpose = C) (hCS : C * S = 1)
    (hPQ : covariance O C * Q = 1) (hQP : Q * covariance O C = 1)
    (hOR : O * R = 0) :
    (Matrix.fromCols (lift C O Q) R).transpose * S *
        Matrix.fromCols (lift C O Q) R =
      Matrix.fromBlocks Q 0 0 (R.transpose * S * R) := by
  obtain ⟨_, hLL, hLR⟩ := lift_energy_blocks S C O Q R hC hCS hPQ hQP hOR
  have hRL : R.transpose * S * lift C O Q = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero, hS, Matrix.mul_assoc] using congrArg Matrix.transpose hLR
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · change ((lift C O Q).transpose * S * lift C O Q) a b = Q a b
    rw [hLL]
  · change ((lift C O Q).transpose * S * R) a b = 0
    rw [hLR]
  · change (R.transpose * S * lift C O Q) a b = 0
    rw [hRL]
  · rfl

/-- Every hidden initial condition remains hidden at all polynomial generator orders. -/
theorem observation_powers (A : Matrix n n ℝ) (O : Matrix r n ℝ)
    (K : Matrix r r ℝ) (hOA : O * A = K * O) (j : ℕ) :
    O * A ^ j = K ^ j * O := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hOA]
      rw [← Matrix.mul_assoc, ← pow_succ]

/-- Positive definiteness and full row rank supply the inverses used above. -/
theorem canonical_lift_data (S : Matrix n n ℝ) (O : Matrix r n ℝ)
    (hS : S.PosDef) (hO : Function.Injective O.transpose.mulVec) :
    S * S⁻¹ = 1 ∧ S⁻¹ * S = 1 ∧
      (covariance O S⁻¹).PosDef ∧
      covariance O S⁻¹ * (covariance O S⁻¹)⁻¹ = 1 ∧
      (covariance O S⁻¹)⁻¹ * covariance O S⁻¹ = 1 := by
  have hsunit : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS.isUnit
  have hP : (covariance O S⁻¹).PosDef := by
    simpa [covariance] using hS.inv.conjTranspose_mul_mul_same (B := O.transpose) hO
  have hpunit : IsUnit (covariance O S⁻¹).det :=
    (covariance O S⁻¹).isUnit_iff_isUnit_det.mp hP.isUnit
  exact ⟨Matrix.mul_nonsing_inv S hsunit, Matrix.nonsing_inv_mul S hsunit,
    hP, Matrix.mul_nonsing_inv _ hpunit, Matrix.nonsing_inv_mul _ hpunit⟩


noncomputable def poisson (O : Matrix r n ℝ) (J : Matrix n n ℝ) : Matrix r r ℝ :=
  O * J * O.transpose

/-- Over the reals an invertible skew matrix has even dimension. -/
theorem skew_unit_even (P : Matrix r r ℝ) (hP : P.transpose = -P)
    (hu : IsUnit P) : Even (Fintype.card r) := by
  have hd : P.det ≠ 0 := isUnit_iff_ne_zero.mp (P.isUnit_iff_isUnit_det.mp hu)
  by_contra h
  have ho : Odd (Fintype.card r) := Nat.not_even_iff_odd.mp h
  have he : P.det = (-1 : ℝ) ^ Fintype.card r * P.det := by
    calc
      P.det = P.transpose.det := (Matrix.det_transpose P).symm
      _ = (-P).det := by rw [hP]
      _ = (-1 : ℝ) ^ Fintype.card r * P.det := Matrix.det_neg P
  rw [ho.neg_one_pow] at he
  apply hd
  linarith

/-- Positive energy rules out a radical of the invariant visible Poisson form.
This is a finite-dimensional symplectic theorem, not a finite-dimensional CCR. -/
theorem predictive_poisson_nondegenerate (J S : Matrix n n ℝ) (O : Matrix r n ℝ)
    (K : Matrix r r ℝ) (hJ : J.transpose = -J) (hJu : IsUnit J)
    (hS : S.PosDef) (hSym : S.transpose = S)
    (hO : Function.Injective O.transpose.mulVec)
    (hObs : O * (J * S) = K * O) :
    IsUnit (poisson O J) ∧ Even (Fintype.card r) := by
  have hJI : J⁻¹ * J = 1 :=
    Matrix.nonsing_inv_mul J (J.isUnit_iff_isUnit_det.mp hJu)
  have hB : Function.Injective (J * O.transpose).mulVec := by
    intro x y hxy
    apply hO
    have hh : J.mulVec (O.transpose.mulVec x) =
        J.mulVec (O.transpose.mulVec y) := by
      simpa only [Matrix.mulVec_mulVec] using hxy
    have ht := congrArg (fun v => J⁻¹.mulVec v) hh
    simpa only [Matrix.mulVec_mulVec, hJI, Matrix.one_mulVec] using ht
  have ht : (J * S).transpose * O.transpose = O.transpose * K.transpose := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hObs
  have hG : poisson O J * K.transpose =
      (J * O.transpose).transpose * S * (J * O.transpose) := by
    unfold poisson
    calc
      O * J * O.transpose * K.transpose = O * J * (O.transpose * K.transpose) := by
        simp only [Matrix.mul_assoc]
      _ = O * J * ((J * S).transpose * O.transpose) := by rw [← ht]
      _ = (J * O.transpose).transpose * S * (J * O.transpose) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym, hJ,
          Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hpos : (poisson O J * K.transpose).PosDef := by
    rw [hG]
    simpa using hS.conjTranspose_mul_mul_same hB
  have hd : (poisson O J * K.transpose).det ≠ 0 :=
    isUnit_iff_ne_zero.mp
      ((poisson O J * K.transpose).isUnit_iff_isUnit_det.mp hpos.isUnit)
  have hp : (poisson O J).det ≠ 0 := by
    intro hz
    apply hd
    rw [Matrix.det_mul, hz, zero_mul]
  have hu : IsUnit (poisson O J) :=
    (poisson O J).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hp)
  have hskew : (poisson O J).transpose = -(poisson O J) := by
    simp only [poisson, Matrix.transpose_mul, Matrix.transpose_transpose, hJ,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  exact ⟨hu, skew_unit_even _ hskew hu⟩

#print axioms hamiltonian_covariance
#print axioms lift_intertwines
#print axioms lift_energy_blocks
#print axioms hidden_projection
#print axioms coordinate_hessian
#print axioms observation_powers
#print axioms canonical_lift_data
#print axioms predictive_poisson_nondegenerate

end D5.S3.Observer.Linear.PredictiveEnergySplitting
