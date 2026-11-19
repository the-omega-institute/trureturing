import D5.S3.Quantum.Measurement.AuricCompressionSpectrum
import D5.S3.Quantum.Measurement.AuricBranchDualScratch
import D5.S3.Quantum.Measurement.AuricFiveLevelTilt

/-! # The rank-one and rank-four competitor in five-level AURIC -/

noncomputable section

namespace D5.S3.Quantum.Measurement.AuricRankOneFour

open Matrix RHLinalg Set
open scoped ComplexOrder MatrixOrder BigOperators
open D5.S3.Quantum.Measurement.AuricBranchDual (rootTrace flaggedChoiScore
  two_flag_cp_branch_score_le)
open D5.S3.Quantum.Measurement.AuricCompressionSpectrum (eigenvalue_compression_le)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

def weights (r t : ℝ) : Fin 5 → ℝ := ![t, t, 1 - t, 1 - t, r ^ 2]

/-- The five-level mixture of the two squared flag tests. -/
def mixedTest (r t : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal fun i => (weights r t i : ℂ)

private theorem weights_nonneg {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 5) :
    0 ≤ weights r t i := by
  fin_cases i <;> simp [weights, ht.1, sub_nonneg.mpr ht.2, sq_nonneg]

theorem mixedTest_psd {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (mixedTest r t).PosSemidef :=
  PosSemidef.diagonal fun i => Complex.nonneg_iff.mpr ⟨weights_nonneg ht i, rfl⟩

private def orderedEigenvalue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (i : Fin n) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

private theorem orderedEigenvalue_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (i : Fin n) :
    orderedEigenvalue hA i =
      hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
        (Fin.cast (Fintype.card_fin n).symm i)) := by
  simp [orderedEigenvalue, Matrix.IsHermitian.eigenvalues]

private theorem rootTrace_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) :
    rootTrace A = ∑ i : Fin n, Real.sqrt (orderedEigenvalue hA.1 i) := by
  have hS : CFC.sqrt A = specMap hA.1 Real.sqrt := by
    apply CFC.sqrt_unique
    · rw [← specMap_mul]
      calc
        _ = specMap hA.1 id := by
          unfold specMap
          congr 1
          apply congrArg diagonal
          funext i
          simp only [Pi.mul_apply, id_eq, ← pow_two, Real.sq_sqrt (hA.eigenvalues_nonneg i)]
        _ = A := specMap_id hA.1
    · exact (specMap_posSemidef hA.1 (f := Real.sqrt) (fun _ => Real.sqrt_nonneg _)).nonneg
  unfold rootTrace
  rw [hS]
  change rtrace (specMap hA.1 Real.sqrt) = _
  rw [rtrace_specMap]
  let e := (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))
  symm
  apply Fintype.sum_equiv e
  intro i
  exact congrArg Real.sqrt (orderedEigenvalue_eq hA.1 i)

private theorem spectralOrdering {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (d : Fin n → ℝ) (hd : Antitone d)
    (hp : A.charpoly = (diagonal fun i => (d i : ℂ)).charpoly) :
    hA.eigenvalues₀ ∘ Fin.cast (Fintype.card_fin n).symm = d := by
  have hm : A.charpoly.roots.map Complex.re = Finset.univ.val.map d := by
    rw [hp, charpoly_diagonal, Polynomial.roots_prod]
    · simp [Function.comp_def]
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  change (A.charpoly.roots.map Complex.re).sort (· ≥ ·) = _ at hsort
  rw [hm, Fin.univ_val_map, Multiset.coe_sort, List.mergeSort_of_pairwise] at hsort
  · ext i
    have h := congrArg (fun l : List ℝ => l[(i : ℕ)]?)
      hsort
    simpa [List.getElem?_ofFn, Function.comp_def] using h.symm
  · simpa only [List.pairwise_ofFn, decide_eq_true_eq] using
      (fun (i j : Fin n) (hij : i < j) => hd hij.le)

private def orderedWeights (r t : ℝ) : Fin 5 → ℝ :=
  ![r ^ 2, max t (1 - t), max t (1 - t), min t (1 - t), min t (1 - t)]

private theorem orderedWeights_antitone {r t : ℝ} (hr : 1 ≤ r ^ 2)
    (ht : t ∈ Icc (0 : ℝ) 1) : Antitone (orderedWeights r t) := by
  have ht' : 1 - t ≤ 1 := by linarith [ht.1]
  have ha : max t (1 - t) ≤ r ^ 2 := (max_le ht.2 ht').trans hr
  have hb : min t (1 - t) ≤ max t (1 - t) :=
    (min_le_left _ _).trans (le_max_left _ _)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [orderedWeights]

private theorem orderedWeights_charpoly (r t : ℝ) :
    (mixedTest r t).charpoly = (diagonal fun i => (orderedWeights r t i : ℂ)).charpoly := by
  simp only [mixedTest, charpoly_diagonal, Fin.prod_univ_succ, Fin.prod_univ_zero, weights,
    orderedWeights, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rcases le_total t (1 - t) with h | h
  · rw [max_eq_right h, min_eq_left h]
    ac_rfl
  · rw [max_eq_left h, min_eq_right h]
    ac_rfl

private theorem eigenvalues_compress_tail (W : Matrix (Fin 5) (Fin 4) ℂ)
    (hW : Wᴴ * W = 1) {r t : ℝ} (hr : 1 ≤ r ^ 2) (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin 4) :
    orderedEigenvalue ((mixedTest_psd ht (r := r)).conjTranspose_mul_mul_same W).1 i ≤
      orderedWeights r t (Fin.castLE (by decide) i) := by
  let hA := (mixedTest_psd ht (r := r)).1
  have hs := spectralOrdering hA _ (orderedWeights_antitone hr ht)
    (orderedWeights_charpoly r t)
  have h := eigenvalue_compression_le hA W hW
    (Fin.cast (Fintype.card_fin 4).symm i)
    (by simpa using (show (i : ℕ) < 5 by omega))
  exact h.trans_eq (congrFun hs (Fin.castLE (by decide) i))

private theorem form_mixedTest_le {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (y : Fin 5 → ℂ) :
    hermForm (mixedTest r t) y ≤ ∑ i, ‖y i‖ ^ 2 + (r ^ 2 - 1) * ‖y 4‖ ^ 2 := by
  have hform : hermForm (mixedTest r t) y = ∑ i, weights r t i * ‖y i‖ ^ 2 := by
    unfold hermForm mixedTest
    simp only [mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_left_comm, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow]
    change ((weights r t i : ℂ) * ((‖y i‖ ^ 2 : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hform]
  have hentry (i : Fin 5) :
      weights r t i ≤ 1 + (if i = 4 then r ^ 2 - 1 else 0) := by
    have ht' : 1 - t ≤ 1 := by linarith [ht.1]
    fin_cases i <;> simp [weights, ht.2, ht']
  calc
    _ ≤ ∑ i, (1 + (if i = 4 then r ^ 2 - 1 else 0)) * ‖y i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hentry i) (sq_nonneg _)
    _ = _ := by simp [add_mul, Finset.sum_add_distrib, ite_mul]

private theorem row_action_sq_le {n : ℕ} (W : Matrix (Fin 5) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖(W *ᵥ x) 4‖ ^ 2 ≤ (∑ i, ‖W 4 i‖ ^ 2) * (∑ i, ‖x i‖ ^ 2) := by
  have h := norm_sum_le (Finset.univ : Finset (Fin n)) (fun i => W 4 i * x i)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

private def spectatorWeight {n : ℕ} (W : Matrix (Fin 5) (Fin n) ℂ) : ℝ :=
  ∑ i, ‖W 4 i‖ ^ 2

private theorem spectatorWeight_eq {n : ℕ} (W : Matrix (Fin 5) (Fin n) ℂ) :
    spectatorWeight W = ((W * Wᴴ) 4 4).re := by
  unfold spectatorWeight
  simp only [mul_apply, conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow]
  rfl

private theorem eigenvalue_compress_spectator {n : ℕ}
    (W : Matrix (Fin 5) (Fin n) ℂ) (hW : Wᴴ * W = 1)
    {r t : ℝ} (hr : 1 ≤ r ^ 2) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    ((mixedTest_psd ht (r := r)).conjTranspose_mul_mul_same W).1.eigenvalues i ≤
      1 + (r ^ 2 - 1) * spectatorWeight W := by
  let hB := ((mixedTest_psd ht (r := r)).conjTranspose_mul_mul_same W).1
  let x : Fin n → ℂ := ⇑(hB.eigenvectorBasis i)
  have hx : ∑ j, ‖x j‖ ^ 2 = 1 := by
    change ∑ j, ‖(hB.eigenvectorBasis i) j‖ ^ 2 = 1
    rw [← EuclideanSpace.norm_sq_eq, hB.eigenvectorBasis.orthonormal.1 i, one_pow]
  have hWx : ∑ j, ‖(W *ᵥ x) j‖ ^ 2 = 1 := by
    rw [← hermForm_one, ← hermForm_conj 1 W, Matrix.mul_one, hW, hermForm_one, hx]
  have hrow := row_action_sq_le W x
  rw [hx, mul_one] at hrow
  change hB.eigenvalues i ≤ _
  rw [hB.eigenvalues_eq]
  change hermForm (Wᴴ * mixedTest r t * W) x ≤ _
  rw [hermForm_conj]
  have h := form_mixedTest_le (r := r) ht (W *ᵥ x)
  rw [hWx] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left hrow (sub_nonneg.mpr hr)) _)

private theorem background_root_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    2 * Real.sqrt (max t (1 - t)) + Real.sqrt (min t (1 - t)) ≤ Real.sqrt 5 := by
  have ha : 0 ≤ max t (1 - t) := ht.1.trans (le_max_left _ _)
  have hb : 0 ≤ min t (1 - t) := le_min ht.1 (sub_nonneg.mpr ht.2)
  have hab : max t (1 - t) + min t (1 - t) = 1 := by
    rcases le_total t (1 - t) with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]; ring
  apply (Real.le_sqrt (by positivity) (by norm_num)).2
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    sq_nonneg (Real.sqrt (max t (1 - t)) - 2 * Real.sqrt (min t (1 - t)))]

/-- Complementary rank-one and rank-four frames obey the uniform trace-root score
bound for independent mixtures of the squared tests. Interlacing bounds the
three smaller eigenvalues of the rank-four compression, while the spectator
overlap controls its largest eigenvalue and the rank-one contribution. -/
theorem rank_one_four_trace_root_bound
    (U : Matrix (Fin 5) (Fin 1) ℂ) (W : Matrix (Fin 5) (Fin 4) ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hcompl : U * Uᴴ + W * Wᴴ = 1)
    {r t s : ℝ} (hr : 1 ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    rootTrace (Uᴴ * mixedTest r t * U) ^ 2 + rootTrace (Wᴴ * mixedTest r s * W) ^ 2 ≤
      6 + r ^ 2 + 2 * r * Real.sqrt 5 := by
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hcomp : spectatorWeight U + spectatorWeight W = 1 := by
    rw [spectatorWeight_eq, spectatorWeight_eq, ← Complex.add_re]
    exact congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => (M 4 4).re) hcompl
  have hu0 : 0 ≤ spectatorWeight U := by unfold spectatorWeight; positivity
  have hw0 : 0 ≤ spectatorWeight W := by unfold spectatorWeight; positivity
  let a := 1 + (r ^ 2 - 1) * spectatorWeight U
  let b := 1 + (r ^ 2 - 1) * spectatorWeight W
  have hb0 : 0 ≤ b := add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hr2) hw0)
  have hb : b ≤ r ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (show spectatorWeight W ≤ 1 by linarith)
      (sub_nonneg.mpr hr2)
    dsimp [b]
    linarith
  have hab : a + b = 1 + r ^ 2 := by
    dsimp [a, b]
    linear_combination (r ^ 2 - 1) * hcomp
  have hu : rootTrace (Uᴴ * mixedTest r t * U) ^ 2 ≤ a := by
    let hA := (mixedTest_psd ht (r := r)).conjTranspose_mul_mul_same U
    rw [rootTrace_eigenvalues hA, Fin.sum_univ_one, orderedEigenvalue_eq,
      Real.sq_sqrt (hA.eigenvalues_nonneg _)]
    exact eigenvalue_compress_spectator U hU hr2 ht _
  let hB := (mixedTest_psd hs (r := r)).conjTranspose_mul_mul_same W
  have hfour : rootTrace (Wᴴ * mixedTest r s * W) ≤ Real.sqrt b + Real.sqrt 5 := by
    rw [rootTrace_eigenvalues hB, Fin.sum_univ_four]
    have h0 : Real.sqrt (orderedEigenvalue hB.1 0) ≤ Real.sqrt b := by
      rw [orderedEigenvalue_eq]
      exact Real.sqrt_le_sqrt (eigenvalue_compress_spectator W hW hr2 hs _)
    have h1 := Real.sqrt_le_sqrt (eigenvalues_compress_tail W hW hr2 hs 1)
    have h2 := Real.sqrt_le_sqrt (eigenvalues_compress_tail W hW hr2 hs 2)
    have h3 := Real.sqrt_le_sqrt (eigenvalues_compress_tail W hW hr2 hs 3)
    change _ ≤ Real.sqrt (max s (1 - s)) at h1 h2
    change _ ≤ Real.sqrt (min s (1 - s)) at h3
    linarith [background_root_bound hs]
  have hnonneg : 0 ≤ rootTrace (Wᴴ * mixedTest r s * W) :=
    (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1
  have hsq := pow_le_pow_left₀ hnonneg hfour 2
  have hsqrtb : Real.sqrt b ≤ r := (Real.sqrt_le_left (by linarith)).2 hb
  have hcross := mul_le_mul_of_nonneg_right hsqrtb (Real.sqrt_nonneg 5)
  nlinarith [Real.sq_sqrt hb0, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

/-- The two flag tests before squaring. -/
def flagTest (r : ℝ) (j : Fin 2) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal (if j = 0 then ![1, 1, 0, 0, (r : ℂ)] else ![0, 0, 1, 1, (r : ℂ)])

theorem mixed_flag_gram {n : ℕ} (V : Matrix (Fin 5) (Fin n) ℂ) (r t : ℝ) :
    t • ((flagTest r 0 * V)ᴴ * (flagTest r 0 * V)) +
      (1 - t) • ((flagTest r 1 * V)ᴴ * (flagTest r 1 * V)) = Vᴴ * mixedTest r t * V := by
  have hD : t • ((flagTest r 0)ᴴ * flagTest r 0) +
      (1 - t) • ((flagTest r 1)ᴴ * flagTest r 1) = mixedTest r t := by
    simp only [flagTest, mixedTest, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
      diagonal_conjTranspose, diagonal_mul_diagonal, ← Matrix.diagonal_smul,
      Matrix.diagonal_add, Matrix.diagonal_eq_diagonal_iff]
    intro i
    fin_cases i <;> simp [weights, pow_two, Complex.real_smul, Complex.ofReal_sub]
    ring
  rw [← hD, Matrix.mul_add, Matrix.add_mul]
  simp only [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Applying the finite CP branch bound separately to the two blocks gives
the rank-one and rank-four competitor score bound. -/
theorem rank_one_four_cp_score_le
    (U : Matrix (Fin 5) (Fin 1) ℂ) (W : Matrix (Fin 5) (Fin 4) ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hcompl : U * Uᴴ + W * Wᴴ = 1)
    (r : ℝ) (hr : 1 ≤ r)
    (Φ : Fin 2 → MatrixMap (Fin 1) (Fin 5) ℂ)
    (Ψ : Fin 2 → MatrixMap (Fin 4) (Fin 5) ℂ)
    (hΦ : ∀ j, (Φ j).IsCompletelyPositive) (hΨ : ∀ j, (Ψ j).IsCompletelyPositive)
    (hΦtp : (∑ j, Φ j).IsTracePreserving) (hΨtp : (∑ j, Ψ j).IsTracePreserving) :
    flaggedChoiScore (fun j => flagTest r j * U) Φ +
      flaggedChoiScore (fun j => flagTest r j * W) Ψ ≤ 6 + r ^ 2 + 2 * r * Real.sqrt 5 := by
  obtain ⟨t, ht, _, h1⟩ := two_flag_cp_branch_score_le (fun j => flagTest r j * U) Φ hΦ hΦtp
  obtain ⟨s, hs, _, h4⟩ := two_flag_cp_branch_score_le (fun j => flagTest r j * W) Ψ hΨ hΨtp
  dsimp only at h1 h4
  rw [mixed_flag_gram] at h1 h4
  exact (add_le_add h1 h4).trans (rank_one_four_trace_root_bound U W hU hW hcompl hr ht hs)

/-- On the witness interval the rank-one and rank-four competitor is strictly
below the untilted score from the complementary rank-three and rank-two split. -/
theorem rank_one_four_constant_lt_tiltScore
    (r : D5.S3.Quantum.Measurement.AuricFiveLevelTilt.WitnessInterval) :
    6 + (r : ℝ) ^ 2 + 2 * (r : ℝ) * Real.sqrt 5 <
      D5.S3.Quantum.Measurement.AuricFiveLevelTilt.tiltScore r 0 := by
  have h := (D5.S3.Quantum.Measurement.AuricFiveLevelTilt.other_rank_bounds_lt r).1
  rw [show 6 + (r : ℝ) ^ 2 + 2 * (r : ℝ) * Real.sqrt 5 =
      (Real.sqrt 5 + (r : ℝ)) ^ 2 + 1 by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]]
  exact h

#print axioms rank_one_four_trace_root_bound
#print axioms rank_one_four_cp_score_le
#print axioms rank_one_four_constant_lt_tiltScore

end D5.S3.Quantum.Measurement.AuricRankOneFour
