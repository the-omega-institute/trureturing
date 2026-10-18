/- GID: D5/S3/Quantum/Schatten/LowerGelfandNaimark
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/LowerGelfandNaimark
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-subset lower multiplicative singular-value bounds. -/

import D5.S3.Quantum.Schatten.SingularValueOrder
import D5.S3.Quantum.Foundation.FiniteTraceDistance

noncomputable section
open Matrix Finset
open scoped BigOperators ComplexOrder
namespace D5.S3.Quantum.Schatten

private theorem prod_singularValues_eq_norm_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∏ i, singularValues A i) = ‖A.det‖ := by
  have hs (i : Fin n) : singularValues A i ^ 2 =
      (isHermitian_conjTranspose_mul_self A).eigenvalues i := by
    simp only [singularValues, conjTranspose_conjTranspose]
    apply Real.sq_sqrt
    exact eigenvalues_conjTranspose_mul_self_nonneg A i
  have he : (∏ i, singularValues A i) ^ 2 = ‖A.det‖ ^ 2 := by
    rw [← Finset.prod_pow]
    simp_rw [hs]
    have hd := congrArg Complex.re
      (isHermitian_conjTranspose_mul_self A).det_eq_prod_eigenvalues
    simp only [det_mul, det_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_prod, Complex.ofReal_re] at hd
    rw [← hd]
    simp [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
  exact (sq_eq_sq₀ (Finset.prod_nonneg (fun i _ => singularValues_nonneg A i))
    (norm_nonneg _)).mp he

private theorem prod_sorted_eq_norm_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∏ i, singularValuesSorted A i) = ‖A.det‖ := by
  obtain ⟨σ, hσ⟩ := exists_sorting_equiv A
  rw [← prod_singularValues_eq_norm_det A, ← σ.prod_comp]
  exact Finset.prod_congr rfl (fun i _ => (hσ i).symm)

private theorem sorted_pos_of_isUnit_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (i : Fin (Fintype.card (Fin n))) : 0 < singularValuesSorted A i := by
  have hp : (∏ j, singularValuesSorted A j) ≠ 0 := by
    rw [prod_sorted_eq_norm_det]
    exact norm_ne_zero_iff.mpr hA.ne_zero
  exact lt_of_le_of_ne (singularValuesSorted_nonneg A i)
    (Ne.symm ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)))

private theorem prod_clipped_eq {m k : ℕ} (c : Fin m → ℝ) (hc : Antitone c)
    (hc0 : ∀ i, 0 < c i) (hk0 : 0 < k) (hk : k ≤ m) :
    let r := c ⟨k - 1, by omega⟩
    (∏ i, max (c i / r) 1) =
      (∏ j : Fin k, c ⟨j.val, by omega⟩) / r ^ k := by
  dsimp only
  let r := c ⟨k - 1, by omega⟩
  change (∏ i, max (c i / r) 1) =
    (∏ j : Fin k, c ⟨j.val, by omega⟩) / r ^ k
  have hr : 0 < r := hc0 _
  have he (i : Fin m) : max (c i / r) 1 = if i.val < k then c i / r else 1 := by
    split_ifs with hi
    · exact max_eq_left ((le_div_iff₀ hr).mpr (by
        simpa only [one_mul] using hc (show i ≤ ⟨k - 1, by omega⟩ by
          exact Nat.le_sub_one_of_lt hi)))
    · exact max_eq_right ((div_le_iff₀ hr).mpr (by
        simpa only [one_mul] using hc (show (⟨k - 1, by omega⟩ : Fin m) ≤ i by
          change k - 1 ≤ i.val; omega)))
  simp_rw [he]
  rw [← Finset.prod_filter]
  have hprod : (∏ i ∈ Finset.univ.filter (fun i : Fin m => i.val < k), c i / r) =
      ∏ j : Fin k, c ⟨j.val, by omega⟩ / r := by
    apply Finset.prod_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k))
    · intro i hi; exact Finset.mem_univ _
    · intro i hi j hj hij
      exact Fin.ext (congrArg (fun u : Fin k => u.val) hij)
    · intro j hj
      refine ⟨⟨j.val, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact j.isLt
    · intro i hi; rfl
  rw [hprod, Finset.prod_div_distrib]
  simp

private theorem diagonal_gram_mono {n : ℕ} (d e : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hde : ∀ i, d i ≤ e i)
    (F : Matrix (Fin n) (Fin n) ℂ) :
    ((diagonal (fun i => (e i : ℂ)) * F)ᴴ * (diagonal (fun i => (e i : ℂ)) * F) -
      (diagonal (fun i => (d i : ℂ)) * F)ᴴ * (diagonal (fun i => (d i : ℂ)) * F)).PosSemidef := by
  have hp : (diagonal (fun i => ((e i ^ 2 - d i ^ 2 : ℝ) : ℂ))).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    have h := hde i
    have h0 := hd i
    change (0 : ℂ) ≤ ((e i ^ 2 - d i ^ 2 : ℝ) : ℂ)
    exact_mod_cast (by nlinarith : 0 ≤ e i ^ 2 - d i ^ 2)
  convert hp.conjTranspose_mul_mul_same F using 1
  simp only [conjTranspose_mul, diagonal_conjTranspose, Complex.conj_ofReal,
    Matrix.mul_assoc, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_mul_diagonal,
    ← diagonal_sub]
  congr 2
  ext i
  simp [pow_two] <;> ring

set_option maxHeartbeats 1000000 in
/-- For any index subset, singular-value ratios of an invertible right factor
are bounded by the corresponding initial product of the left factor. -/
theorem lower_gelfand_naimark_ratio {n : ℕ}
    (C D : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C.det) (hD : IsUnit D.det)
    (I : Finset (Fin (Fintype.card (Fin n)))) :
    (∏ i ∈ I, singularValuesSorted (C * D) i / singularValuesSorted D i) ≤
      ∏ j : Fin I.card, singularValuesSorted C ⟨j.val, by
        have := Finset.card_le_card (Finset.subset_univ I)
        simp only [Finset.card_univ, Fintype.card_fin] at this ⊢
        omega⟩ := by
  classical
  by_cases hk0 : I.card = 0
  · have hI : I = ∅ := Finset.card_eq_zero.mp hk0
    subst I
    rw [Finset.prod_empty]
    exact le_of_eq (Finset.prod_eq_one (fun j _ => Fin.elim0 j)).symm
  have hkpos : 0 < I.card := Nat.pos_of_ne_zero hk0
  have hk : I.card ≤ Fintype.card (Fin n) := by
    simpa using Finset.card_le_card (Finset.subset_univ I)
  let r := singularValuesSorted C ⟨I.card - 1, by omega⟩
  have hr : 0 < r := sorted_pos_of_isUnit_det C hC _
  obtain ⟨U, V, hsvd⟩ := Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues C
  have hsvd : C = U.val * diagonal (fun i => (singularValues C i : ℂ)) * V.valᴴ := by
    simpa only [singularValues, conjTranspose_conjTranspose] using hsvd
  let c := singularValues C
  let F := V.valᴴ * D
  let E : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (fun i => ((max (c i / r) 1 : ℝ) : ℂ))
  have hF : singularValuesSorted F = singularValuesSorted D :=
    funext (singularValuesSorted_unitary_mul V.valᴴ D (star V).property)
  have hCD : singularValuesSorted (C * D) =
      singularValuesSorted (diagonal (fun i => (c i : ℂ)) * F) := by
    rw [hsvd]
    funext i
    simpa only [Matrix.mul_assoc, F, c] using
      singularValuesSorted_unitary_mul U.val
        (diagonal (fun i => (singularValues C i : ℂ)) * (V.valᴴ * D)) U.property i
  have hscale : diagonal (fun i => ((c i / r : ℝ) : ℂ)) * F =
      ((r⁻¹ : ℝ) : ℂ) • (diagonal (fun i => (c i : ℂ)) * F) := by
    rw [← smul_mul_assoc]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, div_eq_mul_inv, mul_comm]
  have hupper (i : Fin (Fintype.card (Fin n))) :
      singularValuesSorted (C * D) i / r ≤ singularValuesSorted (E * F) i := by
    have hh := gram_singularValuesSorted_mono _ _
      (diagonal_gram_mono (fun i => c i / r) (fun i => max (c i / r) 1)
        (fun i => div_nonneg (singularValues_nonneg C i) hr.le)
        (fun i => le_max_left _ _) F) i
    rw [hscale, singularValuesSorted_smul_nonneg _ _ (inv_nonneg.mpr hr.le)] at hh
    simpa only [hCD, div_eq_mul_inv, mul_comm, E] using hh
  have hlower (i : Fin (Fintype.card (Fin n))) :
      singularValuesSorted D i ≤ singularValuesSorted (E * F) i := by
    have hh := gram_singularValuesSorted_mono _ _
      (diagonal_gram_mono (fun _ => 1) (fun i => max (c i / r) 1)
        (fun _ => zero_le_one) (fun _ => le_max_right _ _) F) i
    simpa only [Complex.ofReal_one, diagonal_one, Matrix.one_mul, hF, E] using hh
  have hsmall : (∏ i ∈ I, (singularValuesSorted (C * D) i / r) /
      singularValuesSorted D i) ≤
      ∏ i ∈ I, singularValuesSorted (E * F) i / singularValuesSorted D i := by
    exact Finset.prod_le_prod₀ (fun i _ => div_nonneg
      (div_nonneg (singularValuesSorted_nonneg _ _) hr.le)
      (singularValuesSorted_nonneg _ _)) (fun i _ =>
      div_le_div_of_nonneg_right (hupper i) (singularValuesSorted_nonneg D i))
  have hlarge : (∏ i ∈ I, singularValuesSorted (E * F) i / singularValuesSorted D i) ≤
      ∏ i, singularValuesSorted (E * F) i / singularValuesSorted D i := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ I)
    · intro i hi
      exact div_nonneg (singularValuesSorted_nonneg _ _) (singularValuesSorted_nonneg _ _)
    · intro i hi hni
      exact (one_le_div (sorted_pos_of_isUnit_det D hD i)).mpr (hlower i)
  have htotal : (∏ i, singularValuesSorted (E * F) i / singularValuesSorted D i) =
      ∏ i, max (c i / r) 1 := by
    rw [Finset.prod_div_distrib, prod_sorted_eq_norm_det,
      ← hF, prod_sorted_eq_norm_det, det_mul, norm_mul, mul_div_cancel_right₀]
    · simp only [E, det_diagonal, norm_prod, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.prod_congr rfl
      intro i hi
      exact abs_of_nonneg (le_trans (zero_le_one : (0 : ℝ) ≤ 1) (le_max_right _ _))
    · rw [← prod_sorted_eq_norm_det F, hF, prod_sorted_eq_norm_det]
      exact norm_ne_zero_iff.mpr hD.ne_zero
  have hclip : (∏ i, max (c i / r) 1) =
      (∏ j : Fin I.card, singularValuesSorted C ⟨j.val, by omega⟩) / r ^ I.card := by
    obtain ⟨σ, hσ⟩ := exists_sorting_equiv C
    rw [← σ.prod_comp]
    simp only [Function.comp_def, c, hσ]
    exact prod_clipped_eq (singularValuesSorted C) (singularValuesSorted_antitone C)
      (sorted_pos_of_isUnit_det C hC) hkpos hk
  have hleft : (∏ i ∈ I, (singularValuesSorted (C * D) i / r) /
      singularValuesSorted D i) =
      (∏ i ∈ I, singularValuesSorted (C * D) i / singularValuesSorted D i) /
        r ^ I.card := by
    simp_rw [div_right_comm]
    rw [Finset.prod_div_distrib]
    simp
  have hh := hsmall.trans hlarge
  rw [hleft, htotal, hclip] at hh
  exact (div_le_div_iff_of_pos_right (pow_pos hr _)).mp hh

end D5.S3.Quantum.Schatten
