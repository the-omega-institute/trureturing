/- GID: D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetDistortion
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetDistortion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp trace-distance converse for diagonal-reset qutrit compression. -/

import D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
import D5.S3.Weil.ZetaLinear.Sylvester

/-! The attainable real Bell Rayleigh bound in joint trace distance. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open UnitaryReconstruction.LiuWildChoiObstruction (bell normalizedChoi pairMatrix)
open D5.S3.Quantum.Recovery.LocalCompression.QutritPure
open D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset

namespace D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion

open private trace_difference source_matrix correlated ket recovered recovered_matrix
  from D5.S3.Quantum.Recovery.LocalCompression.QutritPure
open private attenuating_block from D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset

private theorem exists_pos_eigenvalue_of_trace_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htrace : A.trace = 0) (hne : A ≠ 0) :
    ∃ i, 0 < hA.eigenvalues i := by
  classical
  by_contra! hnonpos
  have hsum : (∑ i, hA.eigenvalues i) = 0 := by
    have h : (∑ i, (hA.eigenvalues i : ℂ)) = 0 :=
      hA.trace_eq_sum_eigenvalues.symm.trans htrace
    exact_mod_cast h
  apply hne (hA.eigenvalues_eq_zero_iff.mp ?_)
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hnonpos j)).mp hsum i (Finset.mem_univ i)

private theorem traceNorm_eq_twice_pos_mass {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htrace : A.trace = 0) :
    traceNorm A = 2 * ∑ i, (hA.eigenvalues i)⁺ := by
  have hpos : (posPart A : Matrix n n ℂ) = RHLinalg.hermPosPart hA := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
    rfl
  have hneg : (negPart A : Matrix n n ℂ) = RHLinalg.hermNegPart hA := by
    rw [CFC.negPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
    rfl
  have hzero : RHLinalg.rtrace A = 0 := by simp [RHLinalg.rtrace, htrace]
  have hbalance := RHLinalg.rtrace_sub_decomp hA
  rw [hzero, RHLinalg.rtrace_hermPosPart] at hbalance
  have hnorm := trace_norm_jordan_mass A hA
  rw [hpos, hneg] at hnorm
  change traceNorm A = RHLinalg.rtrace (RHLinalg.hermPosPart hA) +
    RHLinalg.rtrace (RHLinalg.hermNegPart hA) at hnorm
  rw [RHLinalg.rtrace_hermPosPart] at hnorm
  linarith

private theorem hermForm_le_half_traceNorm {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htrace : A.trace = 0) (v : n → ℂ) :
    RHLinalg.hermForm A v ≤ (traceNorm A / 2) * ∑ i, ‖v i‖ ^ 2 := by
  classical
  rw [traceNorm_eq_twice_pos_mass hA htrace, mul_comm (2 : ℝ),
    mul_div_cancel_right₀ _ (by norm_num)]
  apply RHLinalg.hermForm_le_of_eigenvalues_le hA
  intro i
  exact (le_posPart _).trans
    (Finset.single_le_sum (fun j _ => posPart_nonneg (hA.eigenvalues j)) (Finset.mem_univ i))

private theorem traceNorm_sub_eq_twice_pos_eigenvalue {n : Type*}
    [Fintype n] [DecidableEq n] {P Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hrank : P.rank ≤ 1)
    (htrace : (P - Q).trace = 0) (i : n)
    (hi : 0 < (hP.isHermitian.sub hQ.isHermitian).eigenvalues i) :
    traceNorm (P - Q) = 2 * (hP.isHermitian.sub hQ.isHermitian).eigenvalues i := by
  classical
  let A := P - Q
  let hA : A.IsHermitian := hP.isHermitian.sub hQ.isHermitian
  change 0 < hA.eigenvalues i at hi
  change traceNorm A = 2 * hA.eigenvalues i
  let W := LinearMap.range (RHLinalg.hermPosPart hA).mulVecLin
  have hW : RHLinalg.PosDefOn P W := by
    intro v hv hne
    have hpositive := RHLinalg.posDefOn_range_hermPosPart hA v hv hne
    have hnonnegative := RHLinalg.hermForm_nonneg_of_posSemidef hQ v
    change 0 < RHLinalg.hermForm (P - Q) v at hpositive
    rw [RHLinalg.hermForm_sub] at hpositive
    linarith
  have hcount : RHLinalg.posIndex hA ≤ 1 := calc
    _ = Module.finrank ℂ W := (RHLinalg.finrank_range_hermPosPart hA).symm
    _ ≤ RHLinalg.posIndex hP.isHermitian :=
      RHLinalg.finrank_le_posIndex_of_posDefOn hP.isHermitian hW
    _ = P.rank := RHLinalg.posIndex_eq_rank_of_posSemidef hP
    _ ≤ 1 := hrank
  change (Finset.univ.filter (fun j => 0 < hA.eigenvalues j)).card ≤ 1 at hcount
  have hother (j : n) (hji : j ≠ i) : hA.eigenvalues j ≤ 0 := by
    by_contra! hj
    exact hji (Finset.card_le_one_iff.mp hcount (by simp [hj]) (by simp [hi]))
  have hmass : (∑ j, (hA.eigenvalues j)⁺) = hA.eigenvalues i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · exact posPart_eq_self.mpr hi.le
    · exact fun j _ hji => posPart_eq_zero.mpr (hother j hji)
  rw [traceNorm_eq_twice_pos_mass hA htrace, hmass]

private abbrev Joint := Qutrit × Qutrit
private abbrev JointMatrix := Matrix Joint Joint ℂ

private def difference (C : QuantumChannel Qutrit Qutrit) : JointMatrix :=
  pairMatrix source - pairMatrix (normalizedChoi C)

/-- The real quadratic form of the matched Bell block. -/
def quadratic (A : Matrix Qutrit Qutrit ℝ) (v : Qutrit → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

private theorem effect_le_error (C : QuantumChannel Qutrit Qutrit)
    (v : Joint → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    (star v ⬝ᵥ (difference C *ᵥ v)).re ≤ error C := by
  have hA : (difference C).IsHermitian :=
    (density_posSemidef source).isHermitian.sub (density_posSemidef (normalizedChoi C)).isHermitian
  have hb := hermForm_le_half_traceNorm hA (trace_difference C) v
  rw [hv, mul_one] at hb
  exact hb

private theorem quadratic_reindex (C : QuantumChannel Qutrit Qutrit) (e : Qutrit ≃ Qutrit)
    (v : Qutrit → ℝ) :
    quadratic (fun i j => matchedBlock C (e i) (e j)) v =
      quadratic (matchedBlock C) (fun i => v (e.symm i)) := by
  unfold quadratic
  rw [← e.sum_comp (fun i => ∑ j, v (e.symm i) * matchedBlock C i j * v (e.symm j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp (fun j => v (e.symm (e i)) * matchedBlock C (e i) j * v (e.symm j))]
  simp

private theorem correlated_normalized (v : Qutrit → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    ∑ a : Joint, ‖correlated (fun i => (v i : ℂ)) a‖ ^ 2 = 1 := by
  simpa [Fintype.sum_prod_type, Fin.sum_univ_three, correlated, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using hv

private theorem correlated_expectation (C : QuantumChannel Qutrit Qutrit) (v : Qutrit → ℝ) :
    quadratic (matchedBlock C) v =
      3 * (star (correlated fun i => (v i : ℂ)) ⬝ᵥ
        (difference C *ᵥ (correlated fun i => (v i : ℂ)))).re := by
  simp only [quadratic, matchedBlock, Matrix.mulVec, dotProduct, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, correlated, difference,
    Matrix.sub_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

private theorem quadratic_le_error (C : QuantumChannel Qutrit Qutrit) (e : Qutrit ≃ Qutrit)
    (v : Qutrit → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    quadratic (fun i j => matchedBlock C (e i) (e j)) v ≤ 3 * error C := by
  rw [quadratic_reindex, correlated_expectation]
  have hv' : (∑ i, v (e.symm i) ^ 2) = 1 := by
    rw [e.symm.sum_comp (fun i => v i ^ 2), hv]
  exact mul_le_mul_of_nonneg_left
    (effect_le_error C _ (correlated_normalized _ hv')) (by norm_num)

private theorem model_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i j : Qutrit) :
    0 ≤ modelBlock x i j := by
  fin_cases i <;> fin_cases j <;> norm_num [modelBlock]
  all_goals first | exact hx1 | exact sq_nonneg x | simpa only [abs_of_nonneg hx0] using hx1

private theorem quadratic_le_of_abs_entries (A B : Matrix Qutrit Qutrit ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (v : Qutrit → ℝ) :
    quadratic A v ≤ quadratic B (fun i => |v i|) := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [show v i * A i j * v j = A i j * (v i * v j) by ring,
    show |v i| * B i j * |v j| = B i j * (|v i| * |v j|) by ring]
  calc
    A i j * (v i * v j) ≤ A i j * |v i * v j| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (hA i j)
    _ ≤ B i j * (|v i| * |v j|) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hAB i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem model_rayleigh_le (E : QuantumChannel Qutrit Qubit)
    (D : QuantumChannel Qubit Qutrit) (t : ℝ) (hE : DiagonalReset E t)
    (v : Qutrit → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    quadratic (modelBlock (amplitude D)) v ≤ 3 * error (D.comp E) := by
  obtain ⟨x, y, h, rfl, hx0, hx1, hy, hblock, hentry⟩ :=
    diagonal_reset_bell_comparison E D t hE
  have habs : (∑ i, |v i| ^ 2) = 1 := by simpa only [sq_abs] using hv
  exact (quadratic_le_of_abs_entries _ _ (model_nonneg hx0 hx1) hentry v).trans
    (quadratic_le_error _ _ _ habs)

private def jointBlock (M : Matrix Qutrit Qutrit ℝ) : JointMatrix :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 then (M a.1 b.1 : ℂ) else 0

private def unmatchedLoss (x y : ℝ) (a : Joint) : ℂ :=
  if a = (1, 2) then (y : ℂ) ^ 2 else if a = (2, 1) then (x : ℂ) ^ 2 else 0

set_option maxHeartbeats 3000000 in
private theorem explicit_difference (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    difference ((decoder x y h).comp encoder) =
      (1 / 3 : ℂ) • (jointBlock (modelBlock x) - diagonal (unmatchedLoss x y)) := by
  have hc : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hy : (y : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by linear_combination hc
  change pairMatrix source - pairMatrix (normalizedChoi (recovered x y h)) = _
  rw [show pairMatrix source = _ from source_matrix,
    show pairMatrix (normalizedChoi (recovered x y h)) = _ from recovered_matrix x y h]
  ext ⟨i, u⟩ ⟨j, v⟩
  fin_cases i <;> fin_cases u <;> fin_cases j <;> fin_cases v <;>
    norm_num [jointBlock, unmatchedLoss, modelBlock, correlated, ket,
      vecMulVec_apply, diagonal_apply, Prod.mk.injEq] <;>
    push_cast <;> (try rw [hy]) <;> ring

private theorem unmatchedLoss_nonneg (x y : ℝ) (a : Joint) :
    0 ≤ unmatchedLoss x y a := by
  by_cases h₁ : a = (1, 2)
  · simp only [unmatchedLoss, ite_eq_left h₁, ← Complex.ofReal_pow]
    exact_mod_cast sq_nonneg y
  by_cases h₂ : a = (2, 1)
  · simp only [unmatchedLoss, ite_eq_right h₁, ite_eq_left h₂, ← Complex.ofReal_pow]
    exact_mod_cast sq_nonneg x
  simp [unmatchedLoss, h₁, h₂]

private theorem positive_eigenvector_matched (x y : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (w : Joint → ℂ)
    (hw : ((1 / 3 : ℂ) • (jointBlock (modelBlock x) - diagonal (unmatchedLoss x y))) *ᵥ w =
      (lam : ℂ) • w) (a : Joint) (ha : a.1 ≠ a.2) : w a = 0 := by
  have he := congrFun hw a
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec] at he
  have hzero : (jointBlock (modelBlock x) *ᵥ w) a = 0 := by
    simp [Matrix.mulVec, dotProduct, jointBlock, ha]
  have hrow : (-(unmatchedLoss x y a) / 3) * w a = (lam : ℂ) * w a := by
    simpa [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hzero, mulVec_diagonal,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using he
  by_contra hwa
  have hn := congrArg Complex.re (mul_right_cancel₀ hwa hrow)
  have hp := (Complex.nonneg_iff.mp (unmatchedLoss_nonneg x y a)).1
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re] at hn
  norm_num [Complex.inv_re, Complex.inv_im] at hn
  linarith

private theorem matched_complex_bound {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (w : Joint → ℂ)
    (hw : ∀ a, a.1 ≠ a.2 → w a = 0) :
    3 * RHLinalg.hermForm (difference ((decoder x y h).comp encoder)) w ≤
      quadratic (modelBlock x) (fun i => ‖w (i, i)‖) := by
  have hform :
      3 * RHLinalg.hermForm (difference ((decoder x y h).comp encoder)) w =
        ∑ i : Qutrit, ∑ j : Qutrit,
          (star (w (i, i)) * ((modelBlock x i j : ℂ) * w (j, j))).re := by
    rw [explicit_difference]
    simp only [RHLinalg.hermForm, RCLike.re_to_complex, Matrix.mulVec, dotProduct, Pi.star_apply,
       Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, jointBlock, diagonal_apply, unmatchedLoss]
    norm_num [Prod.mk.injEq, hw, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im]
    ring
  rw [hform]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hN := model_nonneg hx0 hx1 i j
  calc
    _ ≤ ‖star (w (i, i)) * ((modelBlock x i j : ℂ) * w (j, j))‖ :=
      Complex.re_le_norm _
    _ = ‖w (i, i)‖ * modelBlock x i j * ‖w (j, j)‖ := by
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
      ring

private theorem explicit_rayleigh (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsGreatest {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
      quadratic (modelBlock x) v = s} (3 * error ((decoder x y h).comp encoder)) := by
  let C := (decoder x y h).comp encoder
  let P := pairMatrix source
  let Q := pairMatrix (normalizedChoi C)
  have hP : P.PosSemidef := density_posSemidef source
  have hQ : Q.PosSemidef := density_posSemidef (normalizedChoi C)
  let hA := hP.isHermitian.sub hQ.isHermitian
  have htrace : (P - Q).trace = 0 := trace_difference C
  have hne : P - Q ≠ 0 := by
    change difference C ≠ 0
    dsimp only [C]
    rw [explicit_difference x y h]
    intro he
    have hh := congrArg (fun M : JointMatrix => M (0, 0) (2, 2)) he
    norm_num [jointBlock, modelBlock] at hh
  have hrank : P.rank ≤ 1 := by
    change (vecMulVec (bell Qutrit) (star (bell Qutrit))).rank ≤ 1
    exact rank_vecMulVec_le _ _
  obtain ⟨k, hk⟩ := exists_pos_eigenvalue_of_trace_zero hA htrace hne
  let w : Joint → ℂ := ⇑(hA.eigenvectorBasis k)
  have hw := hA.mulVec_eigenvectorBasis k
  change difference C *ᵥ w = (hA.eigenvalues k : ℂ) • w at hw
  have hsupport (a : Joint) (ha : a.1 ≠ a.2) : w a = 0 := by
    dsimp only [C] at hw
    rw [explicit_difference] at hw
    exact positive_eigenvector_matched x y hk w hw a ha
  have hn : (∑ a : Joint, ‖w a‖ ^ 2) = 1 := by
    change (∑ a : Joint, ‖(hA.eigenvectorBasis k) a‖ ^ 2) = 1
    rw [← EuclideanSpace.norm_sq_eq, hA.eigenvectorBasis.orthonormal.1 k]
    norm_num
  have hv : (∑ i : Qutrit, ‖w (i, i)‖ ^ 2) = 1 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_three, hsupport] using hn
  have hnorm := traceNorm_sub_eq_twice_pos_eigenvalue hP hQ hrank htrace k hk
  have he : error C = hA.eigenvalues k := by
    change traceNorm (P - Q) / 2 = _
    rw [hnorm]
    ring
  have hquad (v : Qutrit → ℝ) (hv : (∑ i, v i ^ 2) = 1) :
      quadratic (modelBlock x) v ≤ 3 * error C := by
    rw [← attenuating_block x y h]
    exact quadratic_le_error C (Equiv.refl _) v hv
  have heig : RHLinalg.hermForm (difference C) w = hA.eigenvalues k :=
    (hA.eigenvalues_eq k).symm
  have hlow := matched_complex_bound h hx0 hx1 w hsupport
  change 3 * RHLinalg.hermForm (difference C) w ≤ _ at hlow
  rw [heig, ← he] at hlow
  refine ⟨⟨fun i => ‖w (i, i)‖, hv, le_antisymm (hquad _ hv) hlow⟩, ?_⟩
  rintro r ⟨v, hv', rfl⟩
  exact hquad v hv'

/-- Every decoder after a plane-preserving diagonal reset is matched or improved
by the explicit pure reset and two-Kraus attenuating decoder at its induced amplitude. -/
theorem diagonal_reset_distortion_converse (E : QuantumChannel Qutrit Qubit)
    (D : QuantumChannel Qubit Qutrit) (t : ℝ) (hE : DiagonalReset E t) :
    ∃ (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1),
      x = amplitude D ∧ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧
      IsGreatest {s : ℝ | ∃ v : Qutrit → ℝ, (∑ i, v i ^ 2) = 1 ∧
        quadratic (modelBlock x) v = s} (3 * error ((decoder x y h).comp encoder)) ∧
      error ((decoder x y h).comp encoder) ≤ error (D.comp E) := by
  obtain ⟨x, y, h, hx, hx0, hx1, hy, _, _⟩ := diagonal_reset_bell_comparison E D t hE
  have hgreatest := explicit_rayleigh x y h hx0 hx1
  obtain ⟨v, hv, hval⟩ := hgreatest.1
  have hb := model_rayleigh_le E D t hE v hv
  rw [← hx, hval] at hb
  exact ⟨x, y, h, hx, hx0, hx1, hy, hgreatest, by linarith⟩

end D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetDistortion
