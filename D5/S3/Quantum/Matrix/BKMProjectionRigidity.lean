/- GID: D5/S3/Quantum/Matrix/BKMProjectionRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/BKMProjectionRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The BKM power integral on a projection detects commutation with its base. -/

import D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
import D5.S3.Weil.ZetaLinear.RankTrace

/-! # Projection rigidity for the actual BKM power integral -/

noncomputable section

open Matrix Complex
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Matrix.BKMProjectionRigidity

open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction (basisChange logMean omega)
open private diagReal conjugated_cfc omega_entry strict_mean logMean_symm
  from D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev Mat (n : Type*) := Matrix n n ℂ

private theorem power_star (D : Mat n) (s : ℝ) : (mpow D s)ᴴ = mpow D s :=
  IsSelfAdjoint.cfc (f := fun x : ℝ => x ^ s) (a := D)

omit [DecidableEq n] in
private theorem projection_psd {P : Mat n} (hp : P.IsHermitian) (hp2 : P * P = P) :
    P.PosSemidef := by
  simpa only [hp.eq, hp2] using Matrix.posSemidef_conjTranspose_mul_self P

private theorem diag_base (D : Mat n) (hD : D.PosDef) :
    (basisChange hD.isHermitian.eigenvectorUnitary).symm D =
      diagonal (fun i => (hD.isHermitian.eigenvalues i : ℂ)) := by
  change (Unitary.conjStarAlgAut ℂ (Mat n) hD.isHermitian.eigenvectorUnitary).symm D = _
  rw [Unitary.conjStarAlgAut_symm]
  exact hD.isHermitian.conjStarAlgAut_star_eigenvectorUnitary

private theorem normMean_diag (x : ℝ) (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * logMean x x * x ^ (-(1 / 2 : ℝ)) = 1 := by
  rw [logMean, ite_eq_left rfl, mul_right_comm, ← Real.rpow_add hx]
  rw [show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one,
    inv_mul_cancel₀ hx.ne']

private theorem normMean_gt_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    1 < x ^ (-(1 / 2 : ℝ)) * logMean x y * y ^ (-(1 / 2 : ℝ)) := by
  have hmean : Real.sqrt (x * y) < logMean x y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [mul_comm x y, logMean_symm x y]
      exact strict_mean y x hx h
    · exact strict_mean x y hy h
  calc
    1 = x ^ (-(1 / 2 : ℝ)) * Real.sqrt (x * y) * y ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_mul hx.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [show x ^ (-(1 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) *
          y ^ (-(1 / 2 : ℝ)) =
          (x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ)) *
            (y ^ (1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ))) by ring]
      rw [← Real.rpow_add hx, ← Real.rpow_add hy]
      norm_num
    _ < _ := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hmean
      (Real.rpow_pos_of_pos hx _)) (Real.rpow_pos_of_pos hy _)

private theorem normalized_entry (D X : Mat n) (hD : D.PosDef) (i j : n) :
    let U := (basisChange hD.isHermitian.eigenvectorUnitary).symm
    let eigI := hD.isHermitian.eigenvalues i
    let eigJ := hD.isHermitian.eigenvalues j
    U (mpow D (-(1 / 2 : ℝ)) * omega D X * mpow D (-(1 / 2 : ℝ))) i j =
      ((eigI ^ (-(1 / 2 : ℝ)) * logMean eigI eigJ * eigJ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * U X i j := by
  dsimp only
  rw [map_mul, map_mul, mpow, conjugated_cfc D hD]
  simp only [diagReal, diagonal_mul, mul_diagonal, Function.comp_apply]
  rw [omega_entry D X hD]
  push_cast
  ring

private theorem representation_trace (U : Matrix.unitaryGroup n ℂ) (X : Mat n) :
    ((basisChange U).symm X).trace = X.trace := by
  change ((Unitary.conjStarAlgAut ℂ (Mat n) U).symm X).trace = X.trace
  rw [Unitary.conjStarAlgAut_symm_apply, Matrix.trace_mul_cycle,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]

/-- A commuting direction is multiplied by the base by the actual power integral. -/
theorem omega_of_commute (D X : Mat n) (hD : D.PosDef) (hDX : Commute D X) :
    omega D X = D * X := by
  let U := (basisChange hD.isHermitian.eigenvectorUnitary).symm
  have h := fun (i j : n) => congrArg (fun A : Mat n => U A i j) hDX.eq
  have he (i j : n) (hne : hD.isHermitian.eigenvalues i ≠ hD.isHermitian.eigenvalues j) :
      U X i j = 0 := by
    have hh := h i j
    simp only [map_mul, U, diag_base D hD, diagonal_mul, mul_diagonal] at hh
    exact (mul_eq_zero.mp (show
        ((hD.isHermitian.eigenvalues i : ℂ) - (hD.isHermitian.eigenvalues j : ℂ)) *
        U X i j = 0 by linear_combination hh)).resolve_left (by exact_mod_cast sub_ne_zero.mpr hne)
  apply U.injective
  ext i j
  change (basisChange hD.isHermitian.eigenvectorUnitary).symm (omega D X) i j = _
  rw [omega_entry D X hD]
  simp only [map_mul, U, diag_base D hD, diagonal_mul]
  by_cases hij : hD.isHermitian.eigenvalues i = hD.isHermitian.eigenvalues j
  · rw [logMean, ite_eq_left hij]
  · simp [he i j hij, U]

/-- For a Hermitian idempotent of any rank, its actual BKM image is positive
semidefinite exactly when it commutes with the faithful base. -/
theorem omega_projection_posSemidef_iff (D P : Mat n) (hD : D.PosDef)
    (hp : P.IsHermitian) (hp2 : P * P = P) :
    (omega D P).PosSemidef ↔ Commute D P := by
  let V := hD.isHermitian.eigenvectorUnitary
  let U := (basisChange V).symm
  let eig := hD.isHermitian.eigenvalues
  let p := U P
  let w := fun i j => eig i ^ (-(1 / 2 : ℝ)) * logMean (eig i) (eig j) * eig j ^ (-(1 / 2 : ℝ))
  have hpStar : p.IsHermitian := by
    change star ((Unitary.conjStarAlgAut ℂ (Mat n) V).symm P) = _
    rw [← map_star]
    exact congrArg _ hp.eq
  have hd (i : n) : w i i = 1 := normMean_diag _ (hD.eigenvalues_pos i)
  constructor
  · intro h
    let T := mpow D (-(1 / 2 : ℝ))
    let K := T * omega D P * T
    have hK : K.PosSemidef := by
      have hT : Tᴴ = T := power_star D _
      simpa only [K, hT] using h.mul_mul_conjTranspose_same T
    have hQ : (1 - P).PosSemidef :=
      projection_psd (isHermitian_one.sub hp) (by
        rw [sub_mul, one_mul, mul_sub, mul_one, hp2, sub_self, sub_zero])
    have hnonneg : 0 ≤ ((1 - P) * K).trace.re :=
      RHLinalg.trace_mul_nonneg_of_posSemidef hQ hK
    have hKcoord (i j : n) : U K i j = (w i j : ℂ) * p i j :=
      normalized_entry D P hD i j
    have hTr : K.trace = P.trace := by
      rw [← representation_trace V K, ← representation_trace V P]
      unfold Matrix.trace
      exact Finset.sum_congr rfl (fun i _ => by
        change U K i i = p i i
        rw [hKcoord, hd, Complex.ofReal_one, one_mul])
    have hPair (A : Mat n) (c : n → n → ℝ) (hA : ∀ i j, A i j = (c i j : ℂ) * p i j) :
        (p * A).trace.re = ∑ i, ∑ j, c j i * Complex.normSq (p j i) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hstar : p i j = star (p j i) := (congrFun (congrFun hpStar.eq i) j).symm
      rw [hA, hstar]
      rw [show star (p j i) * ((c j i : ℂ) * p j i) =
          (c j i : ℂ) * (star (p j i) * p j i) by ring,
        Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      simp
    have hPairK := hPair (U K) w hKcoord
    have hPairP : (p * p).trace.re = ∑ i, ∑ j, Complex.normSq (p j i) := by
      simpa using hPair p (fun _ _ => 1) (by simp)
    have hsum : (∑ i, ∑ j, (w j i - 1) * Complex.normSq (p j i)) ≤ 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, one_mul]
      rw [← hPairK, ← hPairP]
      change (U P * U K).trace.re - (U P * U P).trace.re ≤ 0
      rw [← map_mul, ← map_mul]
      change ((basisChange V).symm (P * K)).trace.re -
        ((basisChange V).symm (P * P)).trace.re ≤ 0
      rw [representation_trace, representation_trace, hp2, sub_nonpos]
      rwa [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, hTr, sub_nonneg] at hnonneg
    have hterm (i j : n) : 0 ≤ (w j i - 1) * Complex.normSq (p j i) := by
      apply mul_nonneg _ (Complex.normSq_nonneg _)
      apply sub_nonneg.mpr
      by_cases hij : eig j = eig i
      · change 1 ≤ eig j ^ (-(1 / 2 : ℝ)) * logMean (eig j) (eig i) * eig i ^ (-(1 / 2 : ℝ))
        rw [← hij, normMean_diag _ (hD.eigenvalues_pos j)]
      · exact (normMean_gt_one (hD.eigenvalues_pos j) (hD.eigenvalues_pos i) hij).le
    have hvanish (i j : n) (hne : eig i ≠ eig j) : p i j = 0 := by
      have hle := (Finset.single_le_sum (fun k _ => hterm j k) (Finset.mem_univ i)).trans
        ((Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hterm k l))
          (Finset.mem_univ j)).trans hsum)
      have hpos : 0 < w i j - 1 :=
        sub_pos.mpr (normMean_gt_one (hD.eigenvalues_pos i) (hD.eigenvalues_pos j) hne)
      exact Complex.normSq_eq_zero.mp (le_antisymm
        (nonpos_of_mul_nonpos_right hle hpos) (Complex.normSq_nonneg _))
    change D * P = P * D
    apply U.injective
    ext i j
    simp only [map_mul, U, V, diag_base D hD, diagonal_mul, mul_diagonal]
    by_cases hij : eig i = eig j
    · change (eig i : ℂ) * p i j = p i j * (eig j : ℂ)
      rw [hij, mul_comm]
    · change (eig i : ℂ) * p i j = p i j * (eig j : ℂ)
      simp [hvanish i j hij]
  · intro h
    have hDP : D * P = P * D * P := by
      calc
        D * P = D * (P * P) := by rw [hp2]
        _ = P * D * P := by rw [← mul_assoc, h.eq]
    rw [omega_of_commute D P hD h, hDP]
    simpa only [hp.eq] using hD.posSemidef.mul_mul_conjTranspose_same P

#print axioms omega_projection_posSemidef_iff

end D5.S3.Quantum.Matrix.BKMProjectionRigidity
