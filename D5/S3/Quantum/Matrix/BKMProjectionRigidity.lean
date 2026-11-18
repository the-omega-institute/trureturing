/- GID: D5/S3/Quantum/Matrix/BKMProjectionRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/BKMProjectionRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The BKM power integral on a projection detects commutation with its base. -/

import D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Projection rigidity for the actual BKM power integral -/

noncomputable section

open Matrix Complex
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

namespace D5.S3.Quantum.Matrix.BKMProjectionRigidity

open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
  (basisChange logMean omega diagReal conjugated_cfc omega_entry strict_mean logMean_symm)

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

private theorem normalized_trace (D P : Mat n) (hD : D.PosDef)
    (hp : P.IsHermitian) (hp2 : P * P = P) :
    let eig := hD.isHermitian.eigenvalues
    let p := (basisChange hD.isHermitian.eigenvectorUnitary).symm P
    let T := mpow D (-(1 / 2 : ℝ))
    (-((1 - P) * (T * omega D P * T)).trace.re) =
      ∑ i, ∑ j, (eig j ^ (-(1 / 2 : ℝ)) * logMean (eig j) (eig i) *
        eig i ^ (-(1 / 2 : ℝ)) - 1) * Complex.normSq (p j i) := by
  dsimp only
  let V := hD.isHermitian.eigenvectorUnitary
  let U := (basisChange V).symm
  let eig := hD.isHermitian.eigenvalues
  let p := U P
  let w := fun i j => eig i ^ (-(1 / 2 : ℝ)) * logMean (eig i) (eig j) * eig j ^ (-(1 / 2 : ℝ))
  let T := mpow D (-(1 / 2 : ℝ))
  let K := T * omega D P * T
  have hpStar : p.IsHermitian := by
    change star ((Unitary.conjStarAlgAut ℂ (Mat n) V).symm P) = _
    rw [← map_star]
    exact congrArg _ hp.eq
  have hd (i : n) : w i i = 1 := normMean_diag _ (hD.eigenvalues_pos i)
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
  change -((1 - P) * K).trace.re = ∑ i, ∑ j, (w j i - 1) * Complex.normSq (p j i)
  simp only [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, hTr, neg_sub,
    Finset.sum_sub_distrib]
  rw [← hPairK, ← hPairP]
  change _ = (U P * U K).trace.re - (U P * U P).trace.re
  rw [← map_mul, ← map_mul]
  change _ = ((basisChange V).symm (P * K)).trace.re -
    ((basisChange V).symm (P * P)).trace.re
  rw [representation_trace, representation_trace, hp2]

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
    have hsum : (∑ i, ∑ j, (w j i - 1) * Complex.normSq (p j i)) ≤ 0 := by
      have hw := normalized_trace D P hD hp hp2
      change -((1 - P) * K).trace.re = ∑ i, ∑ j, (w j i - 1) * Complex.normSq (p j i) at hw
      rw [← hw]
      exact neg_nonpos.mpr hnonneg
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

private theorem normalized_mean_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Real.log x - Real.log y) ^ 2 / 24 ≤
      x ^ (-(1 / 2 : ℝ)) * logMean x y * y ^ (-(1 / 2 : ℝ)) - 1 := by
  suffices h : ∀ {x y : ℝ}, 0 < y → y < x → (Real.log x - Real.log y) ^ 2 / 24 ≤
      x ^ (-(1 / 2 : ℝ)) * logMean x y * y ^ (-(1 / 2 : ℝ)) - 1 by
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have h' := h hx hxy
      rw [show Real.log x - Real.log y = -(Real.log y - Real.log x) by ring, neg_sq,
        logMean_symm x y]
      convert h' using 1 <;> ring
    · rw [sub_self, normMean_diag _ hy]
      norm_num
    · exact h hy hyx
  intro x y hy hyx
  have hx := hy.trans hyx
  let u := (Real.log x - Real.log y) / 2
  let v := (Real.log x + Real.log y) / 2
  have hu : 0 < u := half_pos (sub_pos.mpr (Real.log_lt_log hy hyx))
  have hx' : Real.exp v * Real.exp u = x := by
    rw [← Real.exp_add, show v + u = Real.log x by dsimp [v, u]; ring, Real.exp_log hx]
  have hy' : Real.exp v * Real.exp (-u) = y := by
    rw [← Real.exp_add, show v + -u = Real.log y by dsimp [v, u]; ring, Real.exp_log hy]
  have hseries : u + u ^ 3 / 6 ≤ Real.sinh u := by
    have hs := (Real.hasSum_sinh u).summable.sum_le_tsum (Finset.range 2)
      (fun k _ => div_nonneg (pow_nonneg hu.le _) (by positivity))
    norm_num [Real.sinh_eq_tsum, Finset.sum_range_succ, Nat.factorial] at hs ⊢
    exact hs
  have hcoeff : x ^ (-(1 / 2 : ℝ)) * logMean x y * y ^ (-(1 / 2 : ℝ)) =
      Real.sinh u / u := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy,
      mul_right_comm, ← Real.exp_add,
      show Real.log x * -(1 / 2 : ℝ) + Real.log y * -(1 / 2 : ℝ) = -v by dsimp [v]; ring,
      Real.exp_neg, logMean, ite_eq_right hyx.ne', Real.sinh_eq]
    rw [show Real.log x - Real.log y = 2 * u by dsimp [u]; ring]
    rw [← hx', ← hy', ← mul_sub]
    change (Real.exp v)⁻¹ * (Real.exp v * (Real.exp u - Real.exp (-u)) / (2 * u)) =
      (Real.exp u - Real.exp (-u)) / 2 / u
    field_simp [(Real.exp_pos v).ne', hu.ne']
  rw [hcoeff, le_sub_iff_add_le, le_div_iff₀ hu]
  convert hseries using 1
  dsimp [u]
  ring

private theorem difference_le_log_difference {x y u : ℝ} (hx : 0 < x) (hy : 0 < y)
    (_hu : 0 < u) (hxu : x ≤ u) (hyu : y ≤ u) :
    (x - y) ^ 2 ≤ u ^ 2 * (Real.log x - Real.log y) ^ 2 := by
  suffices h : ∀ {a b : ℝ}, 0 < b → b ≤ a → a ≤ u →
      (a - b) ^ 2 ≤ u ^ 2 * (Real.log a - Real.log b) ^ 2 by
    rcases le_total y x with hxy | hyx
    · exact h hy hxy hxu
    · rw [← neg_sub y x, neg_sq, ← neg_sub (Real.log y) (Real.log x), neg_sq]
      exact h hx hyx hyu
  intro a b hb hba hau
  have ha := hb.trans_le hba
  have hs := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne', inv_div] at hs
  have hlog : 0 ≤ Real.log a - Real.log b := sub_nonneg.mpr (Real.log_le_log hb hba)
  have hh : a - b ≤ a * (Real.log a - Real.log b) := by
    rw [mul_comm a]
    apply (div_le_iff₀ ha).mp
    convert hs using 1
    field_simp
  rw [← mul_pow]
  exact pow_le_pow_left₀ (sub_nonneg.mpr hba)
    (hh.trans (mul_le_mul_of_nonneg_right hau hlog)) _

/-- The mass of the negative spectral part of the actual matrix. -/
def negTrace (H : Mat n) : ℝ := (H⁻).trace.re

private theorem omega_hermitian (D P : Mat n) (hD : D.PosDef) (hp : P.IsHermitian) :
    (omega D P).IsHermitian := by
  let V := hD.isHermitian.eigenvectorUnitary
  let U := (Unitary.conjStarAlgAut ℂ (Mat n) V).symm
  change star (omega D P) = omega D P
  apply U.injective
  have hmap (X : Mat n) : U (star X) = star (U X) := map_star U X
  change U (star (omega D P)) = U (omega D P)
  rw [hmap]
  ext i j
  change star (U (omega D P) j i) = U (omega D P) i j
  have hat : ∀ i j, U (omega D P) i j =
      (logMean (hD.isHermitian.eigenvalues i) (hD.isHermitian.eigenvalues j) : ℂ) * U P i j :=
    omega_entry D P hD
  rw [hat, hat, star_mul, logMean_symm (hD.isHermitian.eigenvalues j),
    Complex.star_def, Complex.conj_ofReal]
  have hstar : (star (U P)) i j = U P i j := by
    rw [← hmap]
    exact congrArg (fun A : Mat n => U A i j) hp.eq
  rw [mul_comm ((starRingEnd ℂ) (U P j i))]
  exact congrArg (fun z : ℂ => (logMean (hD.isHermitian.eigenvalues i)
    (hD.isHermitian.eigenvalues j) : ℂ) * z) hstar

private theorem neg_pair_le (H F : Mat n) (hH : H.IsHermitian)
    (hF : F.PosSemidef) (c : ℝ) (hc : F ≤ c • (1 : Mat n)) :
    -(F * H).trace.re ≤ c * negTrace H := by
  let B := H⁺
  let N := H⁻
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)
  have hN : N.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hdec : B - N = H := CFC.posPart_sub_negPart H hH
  have hle : (c • (1 : Mat n) - F).PosSemidef := Matrix.le_iff.mp hc
  have h1 : 0 ≤ (F * B).trace.re := RHLinalg.trace_mul_nonneg_of_posSemidef hF hB
  have h2 : 0 ≤ ((c • (1 : Mat n) - F) * N).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hle hN
  simp only [sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h2
  nth_rw 1 [← hdec]
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  change _ ≤ c * N.trace.re
  linarith

private theorem frobSq_commutator (D P : Mat n) (hd : D.IsHermitian) (hp : P.IsHermitian)
    (hp2 : P * P = P) :
    RHLinalg.frobSq (D * P - P * D) = 2 * RHLinalg.frobSq (P * D * (1 - P)) := by
  let A := P * D * (1 - P)
  have ha : Aᴴ = (1 - P) * D * P := by
    simp [A, hp.eq, hd.eq, Matrix.mul_assoc]
  have hdif : D * P - P * D = Aᴴ - A := by
    rw [ha]
    unfold A
    noncomm_ring
  have hz : A * A = 0 := by
    have hpq : (1 - P) * P = 0 := by simp [sub_mul, hp2]
    calc
      A * A = P * D * ((1 - P) * P) * D * (1 - P) := by dsimp [A]; noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hz' : Aᴴ * Aᴴ = 0 := by
    rw [← Matrix.conjTranspose_mul, hz, Matrix.conjTranspose_zero]
  rw [hdif]
  change ((Aᴴ - A)ᴴ * (Aᴴ - A)).trace.re = 2 * (Aᴴ * A).trace.re
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
    sub_mul, mul_sub, hz, hz', sub_zero, zero_sub, sub_neg_eq_add, Matrix.trace_add, Complex.add_re]
  rw [Matrix.trace_mul_comm A Aᴴ]
  ring

private theorem spectral_commutator (D P : Mat n) (hD : D.PosDef) :
    let eig := hD.isHermitian.eigenvalues
    let p := (basisChange hD.isHermitian.eigenvectorUnitary).symm P
    RHLinalg.frobSq (D * P - P * D) =
      ∑ i, ∑ j, (eig j - eig i) ^ 2 * Complex.normSq (p j i) := by
  dsimp only
  let V := hD.isHermitian.eigenvectorUnitary
  let U := (basisChange V).symm
  let p := U P
  let A := D * P - P * D
  have hstar : U Aᴴ = (U A)ᴴ :=
    map_star (Unitary.conjStarAlgAut ℂ (Mat n) V).symm A
  change (Aᴴ * A).trace.re = _
  rw [← representation_trace V (Aᴴ * A)]
  change (U (Aᴴ * A)).trace.re = _
  rw [map_mul, hstar]
  have he (i j : n) :
      U A i j = (((hD.isHermitian.eigenvalues i - hD.isHermitian.eigenvalues j) : ℝ) : ℂ) * p i j := by
    change U (D * P - P * D) i j = _
    rw [map_sub, map_mul, map_mul]
    have hdiag := diag_base D hD
    change U D = _ at hdiag
    rw [hdiag, Matrix.sub_apply, diagonal_mul, mul_diagonal, Complex.ofReal_sub]
    ring
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (star (U A j i) * U A j i).re = _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, he, Complex.normSq_mul,
    Complex.normSq_ofReal, pow_two]

/-- The negative BKM spectral mass bounds the squared off-diagonal corner of the base. -/
theorem omega_projection_leakage
    (D P : Mat n) (hD : D.PosDef) (hp : P.IsHermitian) (hp2 : P * P = P)
    (l u : ℝ) (hl : 0 < l) (hu : 0 < u)
    (hlD : l • (1 : Mat n) ≤ D) (hDu : D ≤ u • (1 : Mat n)) :
    RHLinalg.frobSq (P * D * (1 - P)) ≤ (12 * u ^ 2 / l) * negTrace (omega D P) := by
  let T := mpow D (-(1 / 2 : ℝ))
  let eig := hD.isHermitian.eigenvalues
  let p := (basisChange hD.isHermitian.eigenvectorUnitary).symm P
  let F := T * (1 - P) * T
  have ht : Tᴴ = T := power_star D _
  have hQ : (1 - P).PosSemidef :=
    projection_psd (isHermitian_one.sub hp) (by
      rw [sub_mul, one_mul, mul_sub, mul_one, hp2, sub_self, sub_zero])
  have hF : F.PosSemidef := by
    simpa only [F, ht] using hQ.mul_mul_conjTranspose_same T
  have hlo := (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hD.isHermitian l).mpr hlD
  have hhi := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hD.isHermitian u).mpr hDu
  have hprod : T * T = mpow D (-1 : ℝ) := by
    let U := (basisChange hD.isHermitian.eigenvectorUnitary).symm
    apply U.injective
    change U (mpow D (-(1 / 2 : ℝ)) * mpow D (-(1 / 2 : ℝ))) = U (mpow D (-1 : ℝ))
    simp only [map_mul, U, mpow, conjugated_cfc D hD, diagReal, diagonal_mul_diagonal,
      Function.comp_apply, ← Complex.ofReal_mul]
    congr 1
    funext i
    rw [← Real.rpow_add (hD.eigenvalues_pos i)]
    norm_num
  have hpowbound : mpow D (-1 : ℝ) ≤ l⁻¹ • (1 : Mat n) := by
    let V := hD.isHermitian.eigenvectorUnitary
    let Q : Mat n := diagonal (fun i => (((eig i)⁻¹ : ℝ) : ℂ))
    have hdiag : (basisChange V).symm (mpow D (-1 : ℝ)) = Q := by
      rw [mpow, conjugated_cfc D hD]
      simp [Q, diagReal, Real.rpow_neg_one, eig]
    have hq : Q ≤ l⁻¹ • (1 : Mat n) := by
      have hsc : l⁻¹ • (1 : Mat n) = diagonal (fun _ : n => ((l⁻¹ : ℝ) : ℂ)) := by
        ext i j
        by_cases h : i = j <;> simp [h, Complex.real_smul]
      rw [hsc]
      apply Matrix.PosSemidef.diagonal_mono
      intro i
      change (((eig i)⁻¹ : ℝ) : ℂ) ≤ ((l⁻¹ : ℝ) : ℂ)
      exact_mod_cast inv_le_inv₀ (hD.eigenvalues_pos i) hl |>.mpr (hlo i)
    have hh := Matrix.PosSemidef.mul_mul_conjTranspose_mono (V : Mat n) hq
    have hL : (V : Mat n) * Q * (V : Mat n)ᴴ = mpow D (-1 : ℝ) := by
      rw [← hdiag]
      exact (basisChange V).apply_symm_apply _
    have hR : (V : Mat n) * (l⁻¹ • (1 : Mat n)) * (V : Mat n)ᴴ = l⁻¹ • 1 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, mul_one]
      congr 1
      exact Unitary.coe_mul_star_self V
    rwa [hL, hR] at hh
  have hFb : F ≤ l⁻¹ • (1 : Mat n) := by
    have hh := Matrix.PosSemidef.mul_mul_conjTranspose_mono T
      (sub_le_self (1 : Mat n) (projection_psd hp hp2).nonneg)
    rw [ht, mul_one, hprod] at hh
    exact hh.trans hpowbound
  have huv := neg_pair_le (omega D P) F (omega_hermitian D P hD hp) hF l⁻¹ hFb
  have hcycle : (F * omega D P).trace = ((1 - P) * (T * omega D P * T)).trace := by
    change ((T * (1 - P)) * T * omega D P).trace = _
    rw [show T * (1 - P) * T * omega D P =
      T * ((1 - P) * (T * omega D P)) by noncomm_ring, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  rw [hcycle] at huv
  have hTrace := normalized_trace D P hD hp hp2
  rw [hTrace] at huv
  have hspectral := spectral_commutator D P hD
  have hsum : RHLinalg.frobSq (D * P - P * D) ≤ (24 * u ^ 2) *
      (∑ i, ∑ j, (eig j ^ (-(1 / 2 : ℝ)) * logMean (eig j) (eig i) *
        eig i ^ (-(1 / 2 : ℝ)) - 1) * Complex.normSq (p j i)) := by
    rw [hspectral]
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
    have h1 := difference_le_log_difference (hD.eigenvalues_pos j) (hD.eigenvalues_pos i)
      hu (hhi j) (hhi i)
    have h2 := normalized_mean_lower (hD.eigenvalues_pos j) (hD.eigenvalues_pos i)
    exact h1.trans (by nlinarith only [mul_le_mul_of_nonneg_left h2 (sq_nonneg u)])
  have hv := hsum.trans (mul_le_mul_of_nonneg_left huv (by positivity : 0 ≤ 24 * u ^ 2))
  rw [frobSq_commutator D P hD.isHermitian hp hp2] at hv
  calc
    _ ≤ (24 * u ^ 2 * (l⁻¹ * negTrace (omega D P))) / 2 := by linarith
    _ = _ := by ring

#print axioms omega_projection_posSemidef_iff
#print axioms omega_projection_leakage

end D5.S3.Quantum.Matrix.BKMProjectionRigidity
