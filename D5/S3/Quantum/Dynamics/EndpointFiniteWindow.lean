/- GID: D5/S3/Quantum/Dynamics/EndpointFiniteWindow
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/EndpointFiniteWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-window endpoint transition bounds retaining off-diagonal spectral mass. -/

import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
import D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform finite-window estimates for separated real frequencies. -/

set_option maxRecDepth 2048

noncomputable section

open Matrix Finset Complex MeasureTheory
open scoped BigOperators

namespace D5.S3.Quantum.Dynamics.EndpointFiniteWindow

def phase (x t : ℝ) : ℂ := Complex.exp (-Complex.I * (x : ℂ) * t)

private lemma phase_continuous (x : ℝ) : Continuous (phase x) := by
  unfold phase
  fun_prop

private lemma phase_norm (x t : ℝ) : ‖phase x t‖ = 1 := by
  have h : -Complex.I * (x : ℂ) * t = ((-x * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [phase, h, Complex.norm_exp_ofReal_mul_I]

private lemma phase_mul_star (x y t : ℝ) :
    phase x t * star (phase y t) = phase (x - y) t := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, map_neg,
    Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add, Complex.ofReal_sub]
  congr 1
  ring

private lemma phase_integral_bound {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, phase x t‖ ≤ 2 / δ := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; linarith
  have hc : -Complex.I * (x : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hx0)
  have he : (∫ t in (0 : ℝ)..T, phase x t) =
      (phase x T - 1) / (-Complex.I * (x : ℂ)) := by
    simpa [phase, mul_assoc] using (integral_exp_mul_complex (a := 0) (b := T) hc)
  rw [he, norm_div]
  have hn : ‖-Complex.I * (x : ℂ)‖ = |x| := by simp
  rw [hn]
  calc
    ‖phase x T - 1‖ / |x| ≤ 2 / |x| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg x)
      calc
        ‖phase x T - 1‖ ≤ ‖phase x T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [phase_norm]; norm_num
    _ ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num) hδ hx

private lemma probability_expansion {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (t : ℝ) :
    Complex.normSq (∑ i, (a i : ℂ) * phase (lam i) t) =
      ∑ i, ∑ j, a i * a j * (phase (lam i - lam j) t).re := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation.OpLidarTwinProbability.normSq_finite_sum
      (fun i => (a i : ℂ) * phase (lam i) t))
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  have he : (a i : ℂ) * phase (lam i) t * ((a j : ℂ) * star (phase (lam j) t)) =
      ((a i * a j : ℝ) : ℂ) * phase (lam i - lam j) t := by
    rw [Complex.ofReal_mul, ← phase_mul_star]
    ring
  change (↑(a i) * phase (lam i) t * (↑(a j) * star (phase (lam j) t))).re = _
  rw [he, Complex.re_ofReal_mul]

/-- Averaging separated frequencies retains the exact off-diagonal coefficient mass. -/
theorem finite_window_lower_bound {ι : Type*} [Fintype ι]
    (a lam w : ι → ℝ) (hw : ∀ i, |a i| = w i) (hsum : ∑ i, w i = 1)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hgap : ∀ i j, i ≠ j → δ ≤ |lam i - lam j|) :
    (∑ i, w i ^ 2) - (2 / (T * δ)) * (1 - ∑ i, w i ^ 2) ≤
      T⁻¹ * ∫ t in (0 : ℝ)..T, Complex.normSq (∑ i, (a i : ℂ) * phase (lam i) t) := by
  classical
  have hi (i j : ι) : IntervalIntegrable
      (fun t => a i * a j * (phase (lam i - lam j) t).re) volume 0 T :=
    (continuous_const.mul (Complex.continuous_re.comp (phase_continuous _))).intervalIntegrable _ _
  have he : (∫ t in (0 : ℝ)..T,
      Complex.normSq (∑ i, (a i : ℂ) * phase (lam i) t)) =
      ∑ i, ∑ j, a i * a j * (∫ t in (0 : ℝ)..T, phase (lam i - lam j) t).re := by
    simp_rw [probability_expansion]
    rw [intervalIntegral.integral_finsetSum
      (f := fun i t => ∑ j, a i * a j * (phase (lam i - lam j) t).re)
      (fun i _ => by
        have hh := IntervalIntegrable.sum univ (fun j _ => hi i j)
        convert hh using 1
        ext t
        simp only [Finset.sum_apply])]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.intervalIntegral_re ((phase_continuous _).intervalIntegrable 0 T)
  have hdiag (i : ι) :
      a i * a i * (∫ t in (0 : ℝ)..T, phase (lam i - lam i) t).re = T * w i ^ 2 := by
    have hs : a i ^ 2 = w i ^ 2 := by rw [← hw, sq_abs]
    simp [phase, hs, ← pow_two, mul_comm]
  have hterm (i j : ι) (hij : i ≠ j) :
      -(2 / δ) * (w i * w j) ≤
        a i * a j * (∫ t in (0 : ℝ)..T, phase (lam i - lam j) t).re := by
    have hb := phase_integral_bound hδ (hgap i j hij) T
    have hr := Complex.abs_re_le_norm (∫ t in (0 : ℝ)..T, phase (lam i - lam j) t)
    have hh : |a i * a j * (∫ t in (0 : ℝ)..T, phase (lam i - lam j) t).re| ≤
        (w i * w j) * (2 / δ) := by
      rw [abs_mul, abs_mul, hw, hw]
      exact mul_le_mul_of_nonneg_left (hr.trans hb)
        (mul_nonneg (by rw [← hw]; positivity) (by rw [← hw]; positivity))
    linarith [neg_abs_le (a i * a j * (∫ t in (0 : ℝ)..T, phase (lam i - lam j) t).re)]
  have hmass : (∑ i, ∑ j ∈ univ.erase i, w i * w j) = 1 - ∑ i, w i ^ 2 := by
    have hrow (i : ι) : (∑ j ∈ univ.erase i, w i * w j) = w i - w i ^ 2 := by
      rw [Finset.sum_erase_eq_sub (mem_univ i), ← Finset.mul_sum, hsum]
      ring
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib, hsum]
  have htotal : T * (∑ i, w i ^ 2) - (2 / δ) * (1 - ∑ i, w i ^ 2) ≤
      ∫ t in (0 : ℝ)..T, Complex.normSq (∑ i, (a i : ℂ) * phase (lam i) t) := by
    rw [he, ← hmass, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hdiag]
    have hh := Finset.sum_le_sum (fun j (hj : j ∈ univ.erase i) =>
      hterm i j (ne_of_mem_erase hj).symm)
    simp only [neg_mul, Finset.sum_neg_distrib] at hh
    rw [← Finset.mul_sum] at hh
    linarith
  have h := mul_le_mul_of_nonneg_left htotal (inv_pos.mpr hT).le
  convert h using 1 <;> field_simp


private lemma real_spectral_exp {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (s : ℂ) :
    NormedSpace.exp (s • A.map Complex.ofReal) =
      (hA.eigenvectorUnitary.val.map Complex.ofReal) *
        diagonal (fun k => Complex.exp (s * hA.eigenvalues k)) *
          (star hA.eigenvectorUnitary.val).map Complex.ofReal := by
  let W := hA.eigenvectorUnitary.val
  let P := W.map Complex.ofReal
  let Q := (star W).map Complex.ofReal
  have hQP : Q * P = 1 := by
    change (Complex.ofRealHom.mapMatrix (star W)) * (Complex.ofRealHom.mapMatrix W) = 1
    rw [← map_mul, Unitary.coe_star_mul_self, map_one]
  have hunit : IsUnit P := (show IsUnit W from Unitary.isUnit_coe).map
    Complex.ofRealHom.mapMatrix
  have hinv : P⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have hdiag : (diagonal hA.eigenvalues).map Complex.ofReal =
      diagonal (fun k => (hA.eigenvalues k : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  have hdec : A.map Complex.ofReal = P * diagonal (fun k => (hA.eigenvalues k : ℂ)) * Q := by
    have hh := congrArg (Complex.ofRealHom.mapMatrix) hA.spectral_theorem
    change A.map Complex.ofReal =
      (W * diagonal hA.eigenvalues * star W).map Complex.ofReal at hh
    calc
      A.map Complex.ofReal = (W * diagonal hA.eigenvalues * star W).map Complex.ofReal := hh
      _ = P * (diagonal hA.eigenvalues).map Complex.ofReal * Q := by
        exact map_mul Complex.ofRealHom.mapMatrix (W * diagonal hA.eigenvalues) (star W) |>.trans
          (congrArg (fun M => M * Q) (map_mul Complex.ofRealHom.mapMatrix W (diagonal hA.eigenvalues)))
      _ = _ := by rw [hdiag]
  have hs : s • A.map Complex.ofReal = P * diagonal (s • fun k => (hA.eigenvalues k : ℂ)) * P⁻¹ := by
    rw [hdec, hinv, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hexp : NormedSpace.exp (s • fun k => (hA.eigenvalues k : ℂ)) =
      fun k => Complex.exp (s * hA.eigenvalues k) := by
    funext k
    rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [hs, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, hinv, hexp]

private lemma involution_eigenvector_pairing {V : Type*} [Fintype V] [DecidableEq V]
    {A R : Matrix V V ℝ} (hA : A.IsHermitian)
    (hinj : Function.Injective hA.eigenvalues) (hc : Commute A R) (hRR : R * R = 1)
    (p : Equiv.Perm V) (hRp : R = p.permMatrix ℝ) (v : V) :
    ∀ k, |hA.eigenvectorUnitary.val (p v) k * hA.eigenvectorUnitary.val v k| =
      hA.eigenvectorUnitary.val v k ^ 2 := by
  let U := hA.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) (star U)
  let B := C R
  have hdiagA : C A = diagonal hA.eigenvalues := by
    simpa only [C, U, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hcomm : Commute (diagonal hA.eigenvalues) B := by
    simpa only [← hdiagA] using hc.map C
  have hdiagB : B.IsDiag := by
    intro i j hij
    have he := congrFun (congrFun hcomm.eq i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    exact (mul_eq_zero.mp (show (hA.eigenvalues i - hA.eigenvalues j) * B i j = 0 by
      nlinarith)).resolve_left (sub_ne_zero.mpr (fun h => hij (hinj h)))
  have hB : B = diagonal (Matrix.diag B) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, hij, hdiagB hij]
  have hBB : B * B = 1 := by
    change C R * C R = 1
    rw [← map_mul, hRR, map_one]
  have hmu (k : V) : B k k ^ 2 = 1 := by
    have hh := congrFun (congrFun hBB k) k
    rw [hB, Matrix.diagonal_mul_diagonal] at hh
    simpa [pow_two] using hh
  have hRW : R * U.val = U.val * B := by
    change R * U.val = U.val * (star U.val * R * U.val)
    calc
      R * U.val = (U.val * star U.val) * R * U.val := by
        rw [show U.val * star U.val = 1 by
          simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  intro k
  have he := congrFun (congrFun hRW v) k
  rw [hRp, PEquiv.toMatrix_toPEquiv_mul, hB, Matrix.mul_diagonal] at he
  change U.val (p v) k = U.val v k * B k k at he
  have hm : |B k k| = 1 := by
    have hs : |B k k| ^ 2 = 1 := by rw [sq_abs, hmu]
    nlinarith [abs_nonneg (B k k)]
  change |U.val (p v) k * U.val v k| = U.val v k ^ 2
  rw [he, abs_mul, abs_mul, hm, mul_one, ← pow_two, sq_abs]

open D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

private lemma central_hermitian (n : ℕ) (hn : 1 ≤ n) :
    (centralDefect n hn).IsHermitian := by
  unfold centralDefect D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
  simpa only [add_assoc, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.isHermitian_diagonal (0 : Fin (2 * n - 1 + 1) → ℝ)).add
      (Matrix.isHermitian_add_transpose_self
        (D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand (2 * n - 1) (centralEdges n hn)))

private lemma central_reversal (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin (2 * n - 1 + 1)) :
    centralDefect n hn i.rev j.rev = centralDefect n hn i j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [centralDefect, D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
    D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand, centralEdges,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Pi.zero_apply, Fin.val_rev]
  split_ifs <;> first | omega | ring

private lemma central_commute (n : ℕ) (hn : 1 ≤ n) :
    Commute (centralDefect n hn) ((Fin.revPerm).permMatrix ℝ) := by
  change centralDefect n hn * Fin.revPerm.permMatrix ℝ = Fin.revPerm.permMatrix ℝ * centralDefect n hn
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  change centralDefect n hn i j.rev = centralDefect n hn i.rev j
  simpa only [Fin.rev_rev] using (central_reversal n hn i j.rev).symm

private lemma central_pairwise_gap (n : ℕ) (hn : 1 ≤ n) :
    ∀ i j, i ≠ j →
      (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n : ℝ) ^ 3 ≤
        |(central_hermitian n hn).eigenvalues i - (central_hermitian n hn).eigenvalues j| := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hroots : Finset.univ.val.map (central_hermitian (m + 1) hn).eigenvalues =
      (centralDefect (m + 1) hn).charpoly.roots := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, Function.comp_def] using
      (central_hermitian (m + 1) hn).roots_charpoly_eq_eigenvalues.symm
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    central_spectral_gap m (central_hermitian (m + 1) hn).eigenvalues hroots


/-- The complete real eigenvalue enumeration, including algebraic multiplicities. -/
def eigenvalues (n : ℕ) (hn : 1 ≤ n) : Fin (2 * n - 1 + 1) → ℝ :=
  (central_hermitian n hn).eigenvalues

/-- The minimum separation over all distinct indices of the full spectrum. -/
def spectralGap (n : ℕ) (hn : 1 ≤ n) : ℝ :=
  (univ.offDiag : Finset (Fin (2 * n - 1 + 1) × Fin (2 * n - 1 + 1))).inf'
    (by
      refine ⟨(0, Fin.last (2 * n - 1)), ?_⟩
      simp only [mem_offDiag, mem_univ, true_and]
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hh
      omega)
    (fun ij => |eigenvalues n hn ij.1 - eigenvalues n hn ij.2|)

private lemma spectralGap_pos (n : ℕ) (hn : 1 ≤ n) : 0 < spectralGap n hn := by
  unfold spectralGap
  apply (Finset.lt_inf'_iff _).2
  intro ij hij
  have hne := (mem_offDiag.mp hij).2.2
  exact lt_of_lt_of_le (by positivity : 0 <
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n : ℝ) ^ 3)
    (central_pairwise_gap n hn ij.1 ij.2 hne)

private lemma spectralGap_le (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin (2 * n - 1 + 1)) (hij : i ≠ j) :
    spectralGap n hn ≤ |eigenvalues n hn i - eigenvalues n hn j| := by
  unfold spectralGap
  exact Finset.inf'_le (fun ij => |eigenvalues n hn ij.1 - eigenvalues n hn ij.2|)
    (show (i, j) ∈ (univ : Finset (Fin (2 * n - 1 + 1))).offDiag from
      mem_offDiag.mpr ⟨mem_univ i, mem_univ j, hij⟩)

/-- The actual central-defect endpoint transition averaged over a uniform finite interval. -/
theorem actual_endpoint_average (n : ℕ) (hn : 1 ≤ n) (ε T : ℝ) (hε : 0 < ε)
    (hT : 4 * (n : ℝ) / (ε * spectralGap n hn) ≤ T) :
    (1 - ε) / (2 * (n : ℝ)) <
      T⁻¹ * ∫ t in (0 : ℝ)..T,
        Complex.normSq (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          (centralDefect n hn).map Complex.ofReal) (Fin.last (2 * n - 1)) 0) := by
  let V := Fin (2 * n - 1 + 1)
  let hA := central_hermitian n hn
  let W := hA.eigenvectorUnitary.val
  let w : V → ℝ := fun k => W 0 k ^ 2
  let a : V → ℝ := fun k => W (Fin.last (2 * n - 1)) k * W 0 k
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ := spectralGap_pos n hn
  have hTp : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hinj : Function.Injective hA.eigenvalues := by
    intro i j he
    by_contra hij
    have hh := spectralGap_le n hn i j hij
    change spectralGap n hn ≤ |hA.eigenvalues i - hA.eigenvalues j| at hh
    rw [he, sub_self, abs_zero] at hh
    linarith
  have hRR : (Fin.revPerm.permMatrix ℝ : Matrix V V ℝ) * Fin.revPerm.permMatrix ℝ = 1 := by
    rw [← Matrix.permMatrix_mul]
    have he : (Fin.revPerm : Equiv.Perm V) * Fin.revPerm = 1 := by
      apply Equiv.ext
      intro i
      exact Fin.rev_rev i
    rw [he, Matrix.permMatrix_one]
  have hw : ∀ k, |a k| = w k := by
    intro k
    simpa only [a, w, W, hA, Fin.revPerm_apply, Fin.rev_zero] using
      involution_eigenvector_pairing (central_hermitian n hn) hinj
        (central_commute n hn) hRR Fin.revPerm rfl 0 k
  have hw0 : ∀ k, 0 ≤ w k := fun k => sq_nonneg _
  have hsum : ∑ k, w k = 1 := by
    have hh := congrFun (congrFun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) 0) 0
    rw [Unitary.coe_star] at hh
    simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
      w, W, pow_two] using hh
  have he (t : ℝ) :
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • (centralDefect n hn).map Complex.ofReal)
        (Fin.last (2 * n - 1)) 0 = ∑ k, (a k : ℂ) * phase (eigenvalues n hn k) t := by
    rw [real_spectral_exp hA, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.star_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro k _
    simp only [a, W, eigenvalues, hA, phase, Complex.ofReal_mul]
    have hex : (-Complex.I * (t : ℂ)) * (hA.eigenvalues k : ℂ) =
        -Complex.I * (hA.eigenvalues k : ℂ) * t := by ring
    rw [hex]
    ring
  have hb := finite_window_lower_bound a (eigenvalues n hn) w hw hsum hδ hTp
    (spectralGap_le n hn)
  simp_rw [← he] at hb
  let D := ∑ k, w k ^ 2
  let d : ℝ := 2 * n
  have hd : 0 < d := by dsimp [d]; positivity
  have hcard : (Fintype.card V : ℝ) = d := by
    simp only [V, Fintype.card_fin]
    have he : 2 * n - 1 + 1 = 2 * n := by omega
    rw [he]
    push_cast
    rfl
  have hlo : 1 / d ≤ D := by
    have hh := sq_sum_le_card_mul_sum_sq (s := univ) (f := w)
    rw [hsum] at hh
    simp only [Finset.card_univ, hcard, one_pow] at hh
    exact (div_le_iff₀ hd).mpr (by simpa [D, mul_comm] using hh)
  have hhi : D ≤ 1 := by
    have hh := sum_sq_le_sq_sum_of_nonneg (s := univ) (f := w) (fun k _ => hw0 k)
    simpa [D, hsum] using hh
  have hk : 2 / (T * spectralGap n hn) ≤ ε / d := by
    apply (div_le_div_iff₀ (mul_pos hTp hδ) hd).mpr
    have hh := (div_le_iff₀ (mul_pos hε hδ)).mp hT
    dsimp [d]
    nlinarith
  have hnoise := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hhi)
  have hstrict : (1 - ε) / d < D - (ε / d) * (1 - D) := by
    have hp : 0 < ε / d ^ 2 := by positivity
    have hm := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ 1 + ε / d by positivity)
    have hid : D - (ε / d) * (1 - D) - (1 - ε) / d =
        (D - 1 / d) * (1 + ε / d) + ε / d ^ 2 := by field_simp; ring
    linarith
  change (1 - ε) / d < _
  change D - (2 / (T * spectralGap n hn)) * (1 - D) ≤ _ at hb
  linarith

end D5.S3.Quantum.Dynamics.EndpointFiniteWindow
