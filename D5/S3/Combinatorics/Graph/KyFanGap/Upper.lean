/- GID: D5/S3/Combinatorics/Graph/KyFanGap/Upper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/Upper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal square-root upper bounds for symmetric zero-one matrices. -/

import D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational

/-! The centering decomposition and Bessel's inequality bound every Ky Fan prefix. -/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace D5.S3.Combinatorics.Graph.KyFanGap

open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

theorem kyFan_eq_of_ge {k n : ℕ} (hnk : n ≤ k)
    (M : Matrix (Fin n) (Fin n) ℝ) : kyFan k M = kyFan n M := by
  classical
  simp only [kyFan, kyFanSum, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hnk)
  intro i _ hi
  exact (Matrix.toEuclideanLin M).singularValues_of_finrank_le (by
    simpa using (Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hi)))

private theorem map_coordinate {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (r : Fin n) :
    Matrix.toEuclideanLin M v r =
      ⟪v, (WithLp.toLp 2 (M r) : EuclideanSpace ℝ (Fin n))⟫_ℝ := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    PiLp.inner_apply, mul_comm]

private theorem sum_norm_map_sq_le {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ‖Matrix.toEuclideanLin M (W.vectors i)‖ ^ 2) ≤
      ∑ r, ∑ s, M r s ^ 2 := by
  classical
  simp_rw [EuclideanSpace.real_norm_sq_eq, map_coordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r _
  have h := W.orthonormal_vectors.sum_inner_products_le
    (s := Finset.univ) (WithLp.toLp 2 (M r))
  simpa [EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs] using h

private theorem signed_pairing_le_frobenius {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    signedPairing W M ≤ Real.sqrt k * Real.sqrt (∑ r, ∑ s, M r s ^ 2) := by
  classical
  have hsign (i : Fin k) : |W.signs i| = 1 := by
    nlinarith [sq_abs (W.signs i), abs_nonneg (W.signs i), W.signs_sq i]
  calc
    signedPairing W M ≤ ∑ i, ‖Matrix.toEuclideanLin M (W.vectors i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ |W.signs i * ⟪W.vectors i, Matrix.toEuclideanLin M (W.vectors i)⟫_ℝ| := le_abs_self _
        _ = |⟪W.vectors i, Matrix.toEuclideanLin M (W.vectors i)⟫_ℝ| := by
          rw [abs_mul, hsign, one_mul]
        _ ≤ _ := by
          simpa [W.orthonormal_vectors.norm_eq_one i] using
            (abs_real_inner_le_norm (W.vectors i) (Matrix.toEuclideanLin M (W.vectors i)))
    _ ≤ Real.sqrt k * Real.sqrt (∑ i, ‖Matrix.toEuclideanLin M (W.vectors i)‖ ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin k => (1 : ℝ))
        (fun i => ‖Matrix.toEuclideanLin M (W.vectors i)‖)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (sum_norm_map_sq_le W M)) (Real.sqrt_nonneg _)

private theorem signed_pairing_ones_le {k n : ℕ} (W : SignedWitness k n) :
    signedPairing W (Matrix.of fun _ _ => (1 : ℝ)) ≤ n := by
  classical
  let e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have hterm (i : Fin k) :
      ⟪W.vectors i, Matrix.toEuclideanLin (Matrix.of fun _ _ => (1 : ℝ)) (W.vectors i)⟫_ℝ =
        ⟪W.vectors i, e⟫_ℝ ^ 2 := by
    have hcoord (r : Fin n) :
        Matrix.toEuclideanLin (Matrix.of fun _ _ => (1 : ℝ)) (W.vectors i) r =
          ∑ s, W.vectors i s := by
      rw [map_coordinate]
      simp [PiLp.inner_apply]
    simp [PiLp.inner_apply, hcoord, e, Finset.mul_sum, Finset.sum_mul, pow_two]
  have hsign (i : Fin k) : W.signs i ≤ 1 := by
    nlinarith [W.signs_sq i, sq_nonneg (W.signs i - 1)]
  calc
    signedPairing W (Matrix.of fun _ _ => (1 : ℝ)) = ∑ i, W.signs i * ⟪W.vectors i, e⟫_ℝ ^ 2 := by
      simp only [signedPairing, hterm]
    _ ≤ ∑ i, ⟪W.vectors i, e⟫_ℝ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left (sq_nonneg _) (hsign i)
    _ ≤ ‖e‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using
        W.orthonormal_vectors.sum_inner_products_le (s := Finset.univ) e
    _ = n := by simp [EuclideanSpace.real_norm_sq_eq, e]

private theorem kyFan_le_of_zero_one_of_le {k n : ℕ} (hk : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    kyFan k A ≤ (1 + Real.sqrt k) * n / 2 := by
  classical
  obtain ⟨W, hW⟩ := exists_signed_pairing_eq_kyFan hk A hA
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => 2 * A i j - 1
  have hB : (∑ r, ∑ s, B r s ^ 2) = (n : ℝ) ^ 2 := by
    have hentry (r s : Fin n) : B r s ^ 2 = 1 := by
      rcases h01 r s with h | h <;> norm_num [B, h]
    simp [hentry, pow_two]
  have hcentering : 2 * signedPairing W A =
      signedPairing W B + signedPairing W (Matrix.of fun _ _ => (1 : ℝ)) := by
    have hmat : (2 : ℝ) • A =
        B + (Matrix.of fun _ _ => (1 : ℝ)) := by
      ext i j
      simp [B] <;> ring
    have hlin : (2 : ℝ) • Matrix.toEuclideanLin A =
        Matrix.toEuclideanLin B + Matrix.toEuclideanLin (Matrix.of fun _ _ => (1 : ℝ)) := by
      simpa only [map_smul, map_add] using
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => Matrix.toEuclideanLin M) hmat
    have happ (i : Fin k) := congrArg (fun L => L (W.vectors i)) hlin
    simp only [LinearMap.smul_apply, LinearMap.add_apply] at happ
    have hinner (i : Fin k) := congrArg (fun x => ⟪W.vectors i, x⟫_ℝ) (happ i)
    simp only [inner_smul_right, inner_add_right] at hinner
    simp only [signedPairing, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      2 * (W.signs i * ⟪W.vectors i, Matrix.toEuclideanLin A (W.vectors i)⟫_ℝ) =
          W.signs i * (2 * ⟪W.vectors i, Matrix.toEuclideanLin A (W.vectors i)⟫_ℝ) := by ring
      _ = W.signs i *
          (⟪W.vectors i, Matrix.toEuclideanLin B (W.vectors i)⟫_ℝ +
            ⟪W.vectors i, Matrix.toEuclideanLin (Matrix.of fun _ _ => (1 : ℝ)) (W.vectors i)⟫_ℝ) := by
        rw [hinner i]
      _ = _ := by ring
  have hfirst := signed_pairing_le_frobenius W B
  rw [hB, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ n)] at hfirst
  have hsecond := signed_pairing_ones_le W
  rw [hW] at hcentering
  nlinarith

theorem kyFan_le_of_zero_one {k n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    kyFan k A ≤ (1 + Real.sqrt k) * n / 2 := by
  by_cases hkn : k ≤ n
  · exact kyFan_le_of_zero_one_of_le hkn A hA h01
  · have hnk : n ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkn)
    rw [kyFan_eq_of_ge hnk]
    calc
      kyFan n A ≤ (1 + Real.sqrt n) * n / 2 :=
        kyFan_le_of_zero_one_of_le le_rfl A hA h01
      _ ≤ _ := by
        have hs : Real.sqrt (n : ℝ) ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hnk)
        have ha : 1 + Real.sqrt (n : ℝ) ≤ 1 + Real.sqrt k := by linarith
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right ha (by positivity)) (by norm_num)

end D5.S3.Combinatorics.Graph.KyFanGap
