/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/Entropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy on the full bosonic Hilbert space. -/
/-
finiteDiagonal_entropy:
  proof_shape: content
  escape_witness: Conclusion witness: a uniform lower bound over every complete countable basis from the subprobability Jensen rows and Parseval columns, with attainment by the occupation basis.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Entropy/MaxEntropy.shannonEntropy
  statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Entropy.MaxEntropy

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy
def finiteDiagonal {N : ℕ} (p : Fin N → ℝ) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  exact ∑ k : Fin N, (p k : ℂ) • InnerProductSpace.rankOne ℂ (h_FockAttTwoMode_fock k) (h_FockAttTwoMode_fock k)


def basisEntropy (T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) (b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) : ℝ≥0∞ := by
  exact ∑' n : ℕ, ENNReal.ofReal (Real.negMulLog ((inner ℂ (b n) (T (b n))).re))

def vonNeumannEntropy (T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) : ℝ≥0∞ := by
  exact ⨅ b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2), basisEntropy T b

theorem finiteDiagonal_entropy {N : ℕ} (p : Fin N → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
    vonNeumannEntropy (finiteDiagonal p) = ENNReal.ofReal (D5.S3.Entropy.MaxEntropy.shannonEntropy p) := by
  have h_FockAttProbe_negMulLog_subprob_jensen {N : ℕ} (w p : Fin N → ℝ)
      (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1) (hp : ∀ j, 0 ≤ p j) :
      (∑ j, w j * Real.negMulLog (p j)) ≤ Real.negMulLog (∑ j, w j * p j) := by
    have h := Real.concaveOn_negMulLog.map_add_sum_le
      (t := Finset.univ) (w := w) (p := p) (v := 1 - ∑ j, w j) (q := 0)
      (fun j _ => hw j) (by ring) (fun j _ => hp j)
      (sub_nonneg.mpr hw1) (by simp)
    simpa only [smul_eq_mul, Real.negMulLog_zero, mul_zero, zero_add] using h
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  have h_FockAttProbe_finiteDiagonal_quadratic {N : ℕ} (p : Fin N → ℝ) (v : (lp (fun _ : ℕ => ℂ) 2)) :
      (inner ℂ v (finiteDiagonal p v)).re = ∑ j : Fin N, p j * ‖v j‖ ^ 2 := by
    simp only [finiteDiagonal, sum_apply, smul_apply, inner_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [inner_smul_right, InnerProductSpace.rankOne_apply, h_FockAttTwoMode_fock,
      lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply, map_one, one_mul, mul_one]
    rw [RCLike.mul_conj]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    norm_cast
  have h_FockAttProbe_parseval_norm_sq (b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) (v : (lp (fun _ : ℕ => ℂ) 2)) :
      HasSum (fun n : ℕ => ‖inner ℂ (b n) v‖ ^ 2) (‖v‖ ^ 2) := by
    have hs := b.hasSum_inner_mul_inner v v
    have hpoint (n : ℕ) :
        inner ℂ v (b n) * inner ℂ (b n) v = (‖inner ℂ (b n) v‖ ^ 2 : ℝ) := by
      calc
        _ = (starRingEnd ℂ) (inner ℂ (b n) v) * inner ℂ (b n) v := by
          rw [inner_conj_symm]
        _ = ((‖inner ℂ (b n) v‖ : ℝ) : ℂ) ^ 2 := RCLike.conj_mul _
        _ = ((‖inner ℂ (b n) v‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    have hs' : HasSum (fun n : ℕ => ((‖inner ℂ (b n) v‖ ^ 2 : ℝ) : ℂ))
        ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      have hval : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; norm_cast
      rw [← hval]
      exact HasSum.congr_fun hs (fun n => (hpoint n).symm)
    exact Complex.hasSum_ofReal.mp hs'
  have h_FockAttProbe_finiteDiagonal_entropy_lower {N : ℕ} (p : Fin N → ℝ)
      (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) :
      ENNReal.ofReal (D5.S3.Entropy.MaxEntropy.shannonEntropy p) ≤ basisEntropy (finiteDiagonal p) b := by
    let w : ℕ → Fin N → ℝ := fun n j => ‖b n j‖ ^ 2
    have hrow (n : ℕ) : ∑ j : Fin N, w n j ≤ 1 := by
      have h := ((default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)).orthonormal.comp (fun j : Fin N => (j : ℕ)) Fin.val_injective)
        |>.sum_inner_products_le (b n) (s := Finset.univ)
      have hf (j : Fin N) : (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) j = h_FockAttTwoMode_fock j := by
        rw [← (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)).repr_symm_single]
        rfl
      simpa only [Function.comp_apply, hf, h_FockAttTwoMode_fock, lp.inner_single_left, RCLike.inner_apply,
        map_one, one_mul, mul_one, w,
        b.orthonormal.norm_eq_one n, one_pow] using h
    have hcol (j : Fin N) : HasSum (fun n : ℕ => w n j) 1 := by
      have hs := h_FockAttProbe_parseval_norm_sq b (h_FockAttTwoMode_fock j)
      have hn : ‖h_FockAttTwoMode_fock j‖ = 1 := by simp [h_FockAttTwoMode_fock, lp.norm_single]
      rw [hn, one_pow] at hs
      apply HasSum.congr_fun hs
      intro n
      simp only [w, h_FockAttTwoMode_fock, lp.inner_single_right, RCLike.inner_apply, one_mul, RCLike.norm_conj]
    have hnonneg (j : Fin N) := Real.negMulLog_nonneg (hp0 j) (hp1 j)
    have hpoint (n : ℕ) :
        (∑ j : Fin N, ENNReal.ofReal (w n j * Real.negMulLog (p j))) ≤
        ENNReal.ofReal (Real.negMulLog ((inner ℂ (b n) (finiteDiagonal p (b n))).re)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (hnonneg j))]
      apply ENNReal.ofReal_le_ofReal
      rw [h_FockAttProbe_finiteDiagonal_quadratic]
      have h := h_FockAttProbe_negMulLog_subprob_jensen (w n) p (fun j => sq_nonneg _) (hrow n) hp0
      simpa only [w, mul_comm] using h
    have hsum := ENNReal.tsum_le_tsum hpoint
    have hleft : (∑' n : ℕ, ∑ j : Fin N, ENNReal.ofReal (w n j * Real.negMulLog (p j))) =
        ENNReal.ofReal (D5.S3.Entropy.MaxEntropy.shannonEntropy p) := by
      unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hnonneg j)]
      simp_rw [← tsum_fintype (L := SummationFilter.unconditional (Fin N))]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro j
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (sq_nonneg _) (hnonneg j))
        ((hcol j).summable.mul_right _), (hcol j).summable.tsum_mul_right,
        (hcol j).tsum_eq, one_mul]
    rw [hleft] at hsum
    exact hsum
  have h_FockAttProbe_finiteDiagonal_fock_value {N : ℕ} (p : Fin N → ℝ) (n : ℕ) :
      (inner ℂ (h_FockAttTwoMode_fock n) (finiteDiagonal p (h_FockAttTwoMode_fock n))).re =
        if hn : n < N then p ⟨n, hn⟩ else 0 := by
    rw [h_FockAttProbe_finiteDiagonal_quadratic]
    split_ifs with hn
    · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin N)]
      · simp [h_FockAttTwoMode_fock, lp.single_apply]
      · intro j _ hj
        have hval : (j : ℕ) ≠ n := fun h => hj (Fin.ext h)
        simp [h_FockAttTwoMode_fock, lp.single_apply, Pi.single_apply, hval]
      · simp
    · apply Finset.sum_eq_zero
      intro j _
      have hval : (j : ℕ) ≠ n := by
        intro h
        exact hn (h ▸ j.isLt)
      simp [h_FockAttTwoMode_fock, lp.single_apply, Pi.single_apply, hval]
  have h_FockAttProbe_finiteDiagonal_entropy_basis {N : ℕ} (p : Fin N → ℝ)
      (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
      basisEntropy (finiteDiagonal p) (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) = ENNReal.ofReal (D5.S3.Entropy.MaxEntropy.shannonEntropy p) := by
    have hf (n : ℕ) : (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) n = h_FockAttTwoMode_fock n := by
      rw [← (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)).repr_symm_single]; rfl
    unfold basisEntropy
    simp only [hf, h_FockAttProbe_finiteDiagonal_fock_value]
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp [show ¬ n < N by omega, Real.negMulLog_zero])]
    unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.negMulLog_nonneg (hp0 j) (hp1 j))]
    calc
      _ = ∑ j : Fin N, ENNReal.ofReal (Real.negMulLog
          (if hn : (j : ℕ) < N then p ⟨j, hn⟩ else 0)) :=
        (Fin.sum_univ_eq_sum_range _ N).symm
      _ = _ := by simp
  apply le_antisymm
  · calc
      vonNeumannEntropy (finiteDiagonal p) ≤ basisEntropy (finiteDiagonal p) (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) :=
        iInf_le _ (default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2))
      _ = ENNReal.ofReal (D5.S3.Entropy.MaxEntropy.shannonEntropy p) := h_FockAttProbe_finiteDiagonal_entropy_basis p hp0 hp1
  · exact le_iInf (h_FockAttProbe_finiteDiagonal_entropy_lower p hp0 hp1)

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy
