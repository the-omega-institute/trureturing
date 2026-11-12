/- GID: D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation
   mirror-E: none(waiver:external-counterexample)
   anchors: [lake/module/D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.claim; result=D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.result; claim=D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation.claim
   digest: Strict ordered spectral domination of actual matrix means does not imply near order. -/

import D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

/-!
Ma–Zhang revision2, Theorem 1 and the first reverse consequence, issue #29594,
CC BY 4.0. Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI,
Singapore. The original actual equal-weight witness, CFC mean identification,
argmin identification, and failure of near order are reused, not rediscovered.
The new estimate locates both ordered eigenvalues strictly below those of
the barycenter. Its live consumer refutes the strict-spectral converse.
This does not concern BJL's norm/weak-majorization Conjecture 1.

The local trace/product rewrites are bind-only consumed helpers. The interval
estimate and eigenvalue-root exclusion supply the new inference. The result
is a certified refutation, not an unconsumed positive finite instance.
-/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open private rootU z rootU_bounds rootZ_bounds witnessA witnessB witnessW witnessL
  witnessA_pos witnessB_pos witnessL_pos witnessW_pos witnessL_det witnessW_det
  witnessW_trace witnessL_trace witnessD witnessD_pos logEuclidean_witness wasserstein_witness
  nearOrder_riccati trace_obstruction witness_trace_test
  from D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimStrictSpectralConverseRefutation

/-- Every decreasingly ordered Hermitian eigenvalue is strictly compared. -/
def StrictSpectralOrder {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ hX : X.IsHermitian, ∃ hY : Y.IsHermitian,
    ∀ i : Fin (Fintype.card (Fin m)), hX.eigenvalues₀ i < hY.eigenvalues₀ i

/-- The proposed strict-spectral converse for actual admissible matrix means. -/
def claim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (n : ℕ), 2 ≤ n → ∀ (w : Fin n → ℝ),
    (∀ j, 0 < w j) → (∑ j, w j) = 1 →
    ∀ A : Fin n → Matrix (Fin m) (Fin m) ℂ, (∀ j, (A j).PosDef) →
    StrictSpectralOrder (logEuclidean w A) (wassersteinBarycenter w A) →
      NearOrder (logEuclidean w A) (wassersteinBarycenter w A)

private theorem spectral_interval_bounds {u z : ℝ}
    (hu0 : (11892 : ℝ) / 10000 < u) (hu1 : u < (11893 : ℝ) / 10000)
    (hz0 : (16278 : ℝ) / 1000 < z) (hz1 : z < (16279 : ℝ) / 1000) :
    2*u < 25/16+265/(16*z) ∧
    2/u < 25/16+265/(16*z) ∧
    0 < (1/u)^2 - (25/16+265/(16*z))/u + (5/8+10/z)^2 := by
  have hu : 0 < u := lt_trans (by norm_num) hu0
  have hz : 0 < z := lt_trans (by norm_num) hz0
  refine ⟨?_, ?_, ?_⟩
  · calc
      2*u ≤ 2*(11893/10000 : ℝ) := by gcongr
      _ < 25/16+265/(16*(16279/1000 : ℝ)) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      2/u ≤ 2/(11892/10000 : ℝ) := by gcongr
      _ < 25/16+265/(16*(16279/1000 : ℝ)) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      0 < (1/(11893/10000 : ℝ))^2 -
          (25/16+265/(16*(16278/1000 : ℝ)))/(11892/10000 : ℝ) +
          (5/8+10/(16279/1000 : ℝ))^2 := by norm_num
      _ ≤ _ := by gcongr

private theorem witness_strict : StrictSpectralOrder witnessL witnessW := by
  let l := witnessL_pos.isHermitian.eigenvalues₀
  let w := witnessW_pos.isHermitian.eigenvalues₀
  have trace_sum (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) :
      M.trace.re = hM.eigenvalues₀ 0 + hM.eigenvalues₀ 1 := by
    rw [hM.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_sum, Complex.ofReal_re]
    calc
      _ = ∑ i, hM.eigenvalues₀ i :=
        Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm
          hM.eigenvalues₀
      _ = _ := Fin.sum_univ_two _
  have det_prod (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) :
      M.det.re = hM.eigenvalues₀ 0 * hM.eigenvalues₀ 1 := by
    rw [hM.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
    calc
      _ = ∏ i, hM.eigenvalues₀ i :=
        Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm
          hM.eigenvalues₀
      _ = _ := Fin.prod_univ_two _
  have hlSum : l 0 + l 1 = rootU + 1/rootU :=
    (trace_sum witnessL witnessL_pos.isHermitian).symm.trans witnessL_trace
  have hlProd : l 0 * l 1 = 1 := by
    rw [← det_prod witnessL witnessL_pos.isHermitian, witnessL_det]
    norm_num
  have hwSum : w 0 + w 1 = 25/16+265/(16*z) :=
    (trace_sum witnessW witnessW_pos.isHermitian).symm.trans witnessW_trace
  have hwProd : w 0 * w 1 = witnessD^2 := by
    rw [← det_prod witnessW witnessW_pos.isHermitian, witnessW_det]
    simp [pow_two]
  have hu1 : 1 < rootU := lt_trans (by norm_num) rootU_bounds.1
  have hu : 0 < rootU := by linarith
  have hinv : rootU * (1/rootU) = 1 := by field_simp
  have h_inv : 1/rootU < rootU :=
    lt_trans ((div_lt_one hu).mpr hu1) hu1
  have hlOrder : l 1 ≤ l 0 := witnessL_pos.isHermitian.eigenvalues₀_antitone (by decide)
  have hl0 : l 0 = rootU := by
    have hr : (l 0-rootU)*(l 0-1/rootU) = 0 := by nlinarith [hlSum, hlProd, hinv]
    rcases mul_eq_zero.mp hr with hr | hr
    · linarith
    · have h0 : l 0 = 1/rootU := sub_eq_zero.mp hr
      have h1 : l 1 = rootU := by linarith
      rw [h0, h1] at hlOrder
      linarith
  have hl1 : l 1 = 1/rootU := by linarith
  obtain ⟨hb0, hb1, hpoly⟩ := spectral_interval_bounds
    (lt_trans (by norm_num) rootU_bounds.1) (lt_trans rootU_bounds.2 (by norm_num))
    (lt_trans (by norm_num) rootZ_bounds.1) (lt_trans rootZ_bounds.2 (by norm_num))
  have hwOrder : w 1 ≤ w 0 := witnessW_pos.isHermitian.eigenvalues₀_antitone (by decide)
  have hw0 : rootU < w 0 := by linarith
  have hx0 : 1/rootU < w 0 := by linarith
  have hw1 : 1/rootU < w 1 := by
    by_contra hn
    have hn : w 1 ≤ 1/rootU := le_of_not_gt hn
    have hmul := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hx0.le) (sub_nonneg.mpr hn)
    change 0 < (1/rootU)^2 - (25/16+265/(16*z))/rootU + witnessD^2 at hpoly
    have hf : (1/rootU-w 0)*(1/rootU-w 1) =
        (1/rootU)^2 - (25/16+265/(16*z))/rootU + witnessD^2 := by
      rw [← hwSum, ← hwProd]
      ring
    rw [hf] at hmul
    linarith
  refine ⟨witnessL_pos.isHermitian, witnessW_pos.isHermitian, ?_⟩
  intro i
  change l i < w i
  fin_cases i
  · change l 0 < w 0
    rw [hl0]
    exact hw0
  · change l 1 < w 1
    rw [hl1]
    exact hw1

/-- The original witness has strict domination of both ordered eigenvalues,
so it refutes the strict-spectral converse for actual admissible means. -/
theorem result : ¬ claim := by
  intro hc
  have ha : ∀ j : Fin 2, (![witnessA,witnessB] j).PosDef := by
    intro j
    fin_cases j
    · exact witnessA_pos
    · exact witnessB_pos
  have hs : StrictSpectralOrder
      (logEuclidean (fun _ : Fin 2 => (1/2 : ℝ)) ![witnessA,witnessB])
      (wassersteinBarycenter (fun _ : Fin 2 => (1/2 : ℝ)) ![witnessA,witnessB]) := by
    rw [logEuclidean_witness, wasserstein_witness]
    exact witness_strict
  have hn := hc 2 (by norm_num) 2 (by norm_num) (fun _ => (1/2 : ℝ))
    (by intro j; norm_num) (by norm_num [Fin.sum_univ_two]) ![witnessA,witnessB] ha hs
  rw [logEuclidean_witness, wasserstein_witness] at hn
  have hr := nearOrder_riccati witnessL_pos witnessW_pos
  exact trace_obstruction witnessL_pos hr.1 witnessD_pos witnessL_det
    witnessW_det hr.2 (lt_trans (by norm_num) witness_trace_test) hn

end D5.S3.Quantum.Matrix.HwangKimStrictSpectralConverseRefutation
