/- GID: D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ThreeByThreeModulusEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entrywise modulus increases the entropy of positive semidefinite three by three matrices. -/

/-
admission_basis: escape-witness (#19184).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19212.
escape_witness: entryModulus_entropy_mono.
The entropy is the direct trace-log expression; no trace normalization is required.
Direct frozen dependency keys (declaration statement_id):
F1: D5/S3/Quantum/Matrix/CartesianVariance + D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
F2: D5/S3/Resource/LogDet/PathSpectralClassical + D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum sha256:2afdc1322560955083985858579c052c3f1e7fed0978a76f0182f08e177e3b35
F3: D5/S3/Weil/ZetaLinear/HermitianPosPart + RHLinalg.frobSq_specMap sha256:80f25164798374b84ed1f478e403177e67a5d63f6b5738ecd22c9489bb106e27
F4: D5/S3/Weil/ZetaLinear/HermitianPosPart + RHLinalg.specMap sha256:c67313b99e4225f9fcb609e9d3128cede06e325302faf08e992e27b5eb0d99de
F5: D5/S3/Weil/ZetaLinear/HermitianPosPart + RHLinalg.specMap_id sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
F6: D5/S3/Weil/ZetaLinear/PosIndex + RHLinalg.frobSq sha256:87344d8035a8c18278b7631968fd9b17dbe3a4221dfb10f55432779f1064e116
Declaration classifications (consumers → prerequisite):
esymm_three: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_posSemidef, resolventMass_identity, resolventMass_mono_product, second_eq_mass_sq_sub_squares, shiftedProduct_expansion; Direct frozen dependencies: none.
shiftedProduct: proof_shape: bind-only; escape_witness: none; consumers: nonneg_of_coeff_nonneg, resolventMass_identity, resolventMass_mono_product, shiftedProduct_expansion, shiftedProduct_pos; Direct frozen dependencies: none.
resolventMass: proof_shape: bind-only; escape_witness: none; consumers: entropy_mono_product, hasDerivAt_shiftedLogMass, resolventMass_identity, resolventMass_mono_product; Direct frozen dependencies: none.
shiftedLogMass: proof_shape: bind-only; escape_witness: none; consumers: continuousOn_shiftedLogMass, entropy_mono_product, hasDerivAt_shiftedLogMass, shiftedLogMass_difference_tendsto_zero; Direct frozen dependencies: none.
shiftedProduct_expansion: proof_shape: bind-only; escape_witness: none; consumers: nonneg_of_coeff_nonneg, resolventMass_mono_product; Direct frozen dependencies: none.
shiftedProduct_pos: proof_shape: bind-only; escape_witness: none; consumers: resolventMass_mono_product; Direct frozen dependencies: none.
resolventMass_identity: proof_shape: bind-only; escape_witness: none; consumers: resolventMass_mono_product; Direct frozen dependencies: none.
resolventMass_mono_product: proof_shape: bind-only; escape_witness: none; consumers: entropy_mono_product; Direct frozen dependencies: none.
hasDerivAt_shiftedLogMass: proof_shape: bind-only; escape_witness: none; consumers: entropy_mono_product; Direct frozen dependencies: none.
continuousOn_shiftedLogMass: proof_shape: bind-only; escape_witness: none; consumers: entropy_mono_product; Direct frozen dependencies: none.
shiftedLogMass_difference_tendsto_zero: proof_shape: bind-only; escape_witness: none; consumers: entropy_mono_product; Direct frozen dependencies: none.
entropy_mono_product: proof_shape: content; escape_witness: D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_mono_product; consumers: entryModulus_entropy_mono; Direct frozen dependencies: none.
nonneg_of_coeff_nonneg: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_posSemidef; Direct frozen dependencies: none.
second_eq_mass_sq_sub_squares: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_second; Direct frozen dependencies: none.
entropy_eq_spectrum: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.entropy_eq_roots, D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.entropy_owner_eq_trace_log, entryModulus_entropy_mono; Direct frozen dependencies: F2.
sum_eigenvalue_squares: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_second; Direct frozen dependencies: F3,F4,F5,F6.
hermitian_trace_square: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_trace_square; Direct frozen dependencies: F1,F6.
entryModulus: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.blockHolevo_le_entropy_root, D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.modulus_gram_sum, D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.modulus_sum_entropy, entryModulus_det_difference, entryModulus_det_mono, entryModulus_diag, entryModulus_entropy_mono, entryModulus_hermitian, entryModulus_posSemidef, entryModulus_second, entryModulus_trace, entryModulus_trace_square; Direct frozen dependencies: none.
entryModulus_hermitian: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_det_difference, entryModulus_entropy_mono, entryModulus_posSemidef, entryModulus_second, entryModulus_trace_square; Direct frozen dependencies: none.
entryModulus_diag: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.blockHolevo_le_entropy_root, D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.modulus_sum_entropy, entryModulus_det_difference, entryModulus_trace; Direct frozen dependencies: none.
entryModulus_trace: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.modulus_sum_entropy, entryModulus_entropy_mono, entryModulus_posSemidef, entryModulus_second; Direct frozen dependencies: none.
det_hermitian_parameters: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_det_difference; Direct frozen dependencies: none.
hermitian_as_parameters: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_det_difference; Direct frozen dependencies: none.
entryModulus_det_difference: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_det_mono; Direct frozen dependencies: none.
entryModulus_det_mono: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_entropy_mono, entryModulus_posSemidef; Direct frozen dependencies: none.
eigen_mass: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_entropy_mono, entryModulus_posSemidef, entryModulus_second; Direct frozen dependencies: none.
eigen_product: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_entropy_mono, entryModulus_posSemidef; Direct frozen dependencies: none.
entryModulus_trace_square: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_second; Direct frozen dependencies: F1,F6.
entryModulus_second: proof_shape: bind-only; escape_witness: none; consumers: entryModulus_entropy_mono, entryModulus_posSemidef; Direct frozen dependencies: F1,F3,F4,F5,F6.
entryModulus_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.modulus_sum_entropy, entryModulus_entropy_mono; Direct frozen dependencies: F1,F3,F4,F5,F6.
entryModulus_entropy_mono: proof_shape: content; escape_witness: D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_mono_product; consumers: D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.modulus_sum_entropy; Direct frozen dependencies: F1,F2,F3,F4,F5,F6.
-/

import D5.S3.Resource.LogDet.PathSpectralClassical
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Weil.ZetaLinear.HermitianPosPart

open Matrix Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy

private theorem esymm_three (x : Fin 3 → ℝ) :
    Multiset.esymm ({x 0, x 1, x 2} : Multiset ℝ) 2 =
      x 0*x 1 + x 0*x 2 + x 1*x 2 := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
    add_comm, add_assoc]

private def shiftedProduct (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (t+x 0)*(t+x 1)*(t+x 2)
private def resolventMass (x : Fin 3 → ℝ) (t : ℝ) : ℝ := ∑ i, x i/(t+x i)
private def shiftedLogMass (x : Fin 3 → ℝ) (t : ℝ) : ℝ := ∑ i, x i*Real.log (t+x i)

private theorem shiftedProduct_expansion (x : Fin 3 → ℝ) (t : ℝ) :
    shiftedProduct x t = t^3 + (∑ i, x i)*t^2 + (Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2)*t + (∏ i, x i) := by
  simp only [shiftedProduct, esymm_three, Fin.sum_univ_three, Fin.prod_univ_three]
  ring

private theorem shiftedProduct_pos {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) {t : ℝ} (ht : 0<t) :
    0 < shiftedProduct x t := by
  exact mul_pos (mul_pos (by linarith [hx 0]) (by linarith [hx 1])) (by linarith [hx 2])

private theorem resolventMass_identity {x : Fin 3 → ℝ} {t : ℝ}
    (h0 : t+x 0 ≠ 0) (h1 : t+x 1 ≠ 0) (h2 : t+x 2 ≠ 0) :
    resolventMass x t = 3 - t*(3*t^2 + 2*(∑ i, x i)*t + (Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2))/shiftedProduct x t := by
  simp only [resolventMass, shiftedProduct, esymm_three, Fin.sum_univ_three]
  field_simp [h0, h1, h2]
  ring

private theorem resolventMass_mono_product {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hm : (∑ i, x i) = (∑ i, y i)) (hs : (Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2) = (Multiset.esymm ({(y) 0, (y) 1, (y) 2} : Multiset ℝ) 2)) (hd : (∏ i, x i) ≤ (∏ i, y i))
    {t : ℝ} (ht : 0<t) : resolventMass x t ≤ resolventMass y t := by
  have hp : shiftedProduct x t ≤ shiftedProduct y t := by
    rw [shiftedProduct_expansion, shiftedProduct_expansion, hm, hs]
    linarith
  have hinv : 1 / shiftedProduct y t ≤ 1 / shiftedProduct x t :=
    one_div_le_one_div_of_le (shiftedProduct_pos hx ht) hp
  have hm0 : 0 ≤ (∑ i, y i) := Finset.sum_nonneg (fun i _ => hy i)
  have hs0 : 0 ≤ (Multiset.esymm ({(y) 0, (y) 1, (y) 2} : Multiset ℝ) 2) := by
    rw [esymm_three]
    exact add_nonneg (add_nonneg (mul_nonneg (hy 0) (hy 1)) (mul_nonneg (hy 0) (hy 2)))
      (mul_nonneg (hy 1) (hy 2))
  have hfac : 0 ≤ t*(3*t^2 + 2*(∑ i, y i)*t + (Multiset.esymm ({(y) 0, (y) 1, (y) 2} : Multiset ℝ) 2)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hinv hfac
  rw [resolventMass_identity (by linarith [hx 0]) (by linarith [hx 1]) (by linarith [hx 2]),
      resolventMass_identity (by linarith [hy 0]) (by linarith [hy 1]) (by linarith [hy 2]), hm, hs]
  simp only [div_eq_mul_inv, one_mul] at hmul ⊢
  linarith

private theorem hasDerivAt_shiftedLogMass {x : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) {t : ℝ} (ht : 0<t) :
    HasDerivAt (shiftedLogMass x) (resolventMass x t) t := by
  have h (i : Fin 3) : HasDerivAt (fun u => x i*Real.log (u+x i)) (x i/(t+x i)) t := by
    simpa only [id_eq, div_eq_mul_inv, one_mul] using
      ((((hasDerivAt_id t).add_const (x i)).log (by linarith [hx i] : t+x i ≠ 0)).const_mul (x i))
  convert (HasDerivAt.sum (u := Finset.univ) (fun i _ => h i)) using 1
  · ext u
    simp [shiftedLogMass]
  · rfl

private theorem continuousOn_shiftedLogMass {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ContinuousOn (shiftedLogMass x) (Ici 0) := by
  apply continuousOn_finsetSum
  intro i _
  by_cases hz : x i = 0
  · simp only [hz, zero_mul]
    exact continuousOn_const
  · apply ContinuousOn.const_mul
    apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
    intro t ht
    dsimp
    have hi : 0<x i := lt_of_le_of_ne (hx i) (Ne.symm hz)
    linarith [ht.out]

private theorem shiftedLogMass_difference_tendsto_zero {x y : Fin 3 → ℝ} (hm : (∑ i, x i) = (∑ i, y i)) :
    Tendsto (fun t => shiftedLogMass y t - shiftedLogMass x t) atTop (𝓝 0) := by
  have hlim (z : Fin 3 → ℝ) :
      Tendsto (fun t => ∑ i, z i*(Real.log (t+z i) - Real.log t)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ =>
      (Real.tendsto_log_comp_add_sub_log (z i)).const_mul (z i))
    simpa only [mul_zero, Finset.sum_const_zero] using h
  convert (hlim y).sub (hlim x) using 1
  · funext t
    simp only [shiftedLogMass, Fin.sum_univ_three] at hm ⊢
    linear_combination -(Real.log t)*hm
  · simp

private theorem entropy_mono_product {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hm : (∑ i, x i) = (∑ i, y i)) (hs : (Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2) = (Multiset.esymm ({(y) 0, (y) 1, (y) 2} : Multiset ℝ) 2)) (hd : (∏ i, x i) ≤ (∏ i, y i)) :
    -(∑ i, x i*Real.log (x i)) ≤ -(∑ i, y i*Real.log (y i)) := by
  let f : ℝ → ℝ := fun t => shiftedLogMass y t - shiftedLogMass x t
  have hcont : ContinuousOn f (Ici 0) :=
    (continuousOn_shiftedLogMass hy).sub (continuousOn_shiftedLogMass hx)
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hasDerivAt_shiftedLogMass hy ht).sub
        (hasDerivAt_shiftedLogMass hx ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [show deriv f t = resolventMass y t-resolventMass x t from
        ((hasDerivAt_shiftedLogMass hy ht).sub (hasDerivAt_shiftedLogMass hx ht)).deriv]
      exact sub_nonneg.mpr (resolventMass_mono_product hx hy hm hs hd ht)
  have hle : f 0 ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (shiftedLogMass_difference_tendsto_zero hm)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hmono (by simp) ht ht
  simpa only [f, shiftedLogMass, zero_add] using (by linarith [hle] :
    -shiftedLogMass x 0 ≤ -shiftedLogMass y 0)

private theorem nonneg_of_coeff_nonneg (x : Fin 3 → ℝ)
    (hm : 0 ≤ (∑ i, x i)) (hs : 0 ≤ (Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2)) (hd : 0 ≤ (∏ i, x i)) : ∀ i, 0 ≤ x i := by
  intro i
  by_contra hi
  have ht : 0 < -x i := neg_pos.mpr (lt_of_not_ge hi)
  have hz : shiftedProduct x (-x i) = 0 := by
    fin_cases i <;> simp [shiftedProduct]
  have hp : 0 < (-x i)^3 + (∑ i, x i)*(-x i)^2 + (Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2)*(-x i) + (∏ i, x i) := by
    positivity
  rw [← shiftedProduct_expansion, hz] at hp
  exact lt_irrefl 0 hp

private theorem second_eq_mass_sq_sub_squares (x : Fin 3 → ℝ) :
    2*(Multiset.esymm ({(x) 0, (x) 1, (x) 2} : Multiset ℝ) 2) = ((∑ i, x i))^2 - ∑ i, (x i)^2 := by
  simp only [Fin.sum_univ_three, esymm_three]
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem entropy_eq_spectrum (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (-(Matrix.trace (A * CFC.log A)).re) = -(∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i)) := by
  unfold CFC.log
  have hm : A * cfc Real.log A = cfc (fun x : ℝ => x * Real.log x) A := by
    conv_lhs => lhs; rw [← cfc_id ℝ A hA]
    exact (cfc_mul id Real.log A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)).symm
  rw [hm, D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum A hA]

private theorem sum_eigenvalue_squares (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i)^2) = (A*A).trace.re := by
  have h := RHLinalg.frobSq_specMap hA id
  rw [RHLinalg.specMap_id] at h
  change (Aᴴ * A).trace.re = ∑ i, (hA.eigenvalues i)^2 at h
  rw [hA.eq] at h
  exact h.symm

omit [DecidableEq n] in
private theorem hermitian_trace_square (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsHermitian) :
    (A*A).trace.re = ∑ i, ∑ j, ‖A i j‖^2 := by
  have h := D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum A
  change (Aᴴ * A).trace.re = ∑ i, ∑ j, Complex.normSq (A j i) at h
  rw [hA] at h
  simp only [Complex.normSq_eq_norm_sq] at h
  exact h.trans (Finset.sum_comm)

def entryModulus (G : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  G.map (fun z => (‖z‖ : ℂ))

private theorem entryModulus_hermitian {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.IsHermitian) :
    (entryModulus G).IsHermitian := by
  ext i j
  simp only [entryModulus, Matrix.map_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← hG.apply i j, norm_star]

theorem entryModulus_diag {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.PosSemidef)
    (i : Fin 3) : entryModulus G i i = G i i := by
  exact (Complex.eq_coe_norm_of_nonneg hG.diag_nonneg).symm

theorem entryModulus_trace {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.PosSemidef) :
    (entryModulus G).trace = G.trace := by
  unfold Matrix.trace Matrix.diag
  exact Finset.sum_congr rfl fun i _ => entryModulus_diag hG i

private theorem det_hermitian_parameters (a b c : ℝ) (x y z : ℂ) :
    (Matrix.det (!![(a : ℂ), x, star z; star x, (b : ℂ), y; z, star y, (c : ℂ)])).re =
      a*b*c - a*‖y‖^2 - b*‖z‖^2 - c*‖x‖^2 + 2*(x*y*z).re := by
  simp only [← Complex.normSq_eq_norm_sq]
  norm_num [Matrix.det_fin_three, Matrix.of_apply, Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im]
  ring

private theorem hermitian_as_parameters {G : Matrix (Fin 3) (Fin 3) ℂ}
    (hG : G.IsHermitian) :
    G = !![((G 0 0).re : ℂ), G 0 1, star (G 2 0);
           star (G 0 1), ((G 1 1).re : ℂ), G 1 2;
           G 2 0, star (G 1 2), ((G 2 2).re : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons]
  · exact (RCLike.conj_eq_iff_re.mp (hG.apply 0 0)).symm
  · rfl
  · exact (hG.apply 0 2).symm
  · exact (hG.apply 1 0).symm
  · exact (RCLike.conj_eq_iff_re.mp (hG.apply 1 1)).symm
  · rfl
  · rfl
  · exact (hG.apply 2 1).symm
  · exact (RCLike.conj_eq_iff_re.mp (hG.apply 2 2)).symm

private theorem entryModulus_det_difference {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.PosSemidef) :
    (entryModulus G).det.re - G.det.re =
      2 * (‖G 0 1 * G 1 2 * G 2 0‖ - (G 0 1 * G 1 2 * G 2 0).re) := by
  have hg := det_hermitian_parameters (G 0 0).re (G 1 1).re (G 2 2).re
    (G 0 1) (G 1 2) (G 2 0)
  rw [← hermitian_as_parameters hG.isHermitian] at hg
  have hk := det_hermitian_parameters (G 0 0).re (G 1 1).re (G 2 2).re
    (‖G 0 1‖ : ℂ) (‖G 1 2‖ : ℂ) (‖G 2 0‖ : ℂ)
  have hreal (i : Fin 3) : (G i i).re = ‖G i i‖ := by
    simpa only [entryModulus, Matrix.map_apply,Complex.ofReal_re] using
      (congrArg Complex.re (entryModulus_diag hG i)).symm
  have hK : entryModulus G =
      !![((G 0 0).re : ℂ), (‖G 0 1‖ : ℂ), star (‖G 2 0‖ : ℂ);
        star (‖G 0 1‖ : ℂ), ((G 1 1).re : ℂ), (‖G 1 2‖ : ℂ);
        (‖G 2 0‖ : ℂ), star (‖G 1 2‖ : ℂ), ((G 2 2).re : ℂ)] := by
    convert hermitian_as_parameters (entryModulus_hermitian hG.isHermitian) using 1
    all_goals simp only [entryModulus, Matrix.map_apply, Complex.ofReal_re, hreal]
  rw [← hK] at hk
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero] at hk
  rw [norm_mul, norm_mul]
  linarith

private theorem entryModulus_det_mono {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.PosSemidef) :
    G.det.re ≤ (entryModulus G).det.re := by
  have h := entryModulus_det_difference hG
  have hn := Complex.re_le_norm (G 0 1 * G 1 2 * G 2 0)
  linarith

private theorem eigen_mass (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsHermitian) :
    (∑ i, hA.eigenvalues i) = A.trace.re := by
  have h := congrArg Complex.re hA.trace_eq_sum_eigenvalues
  simpa only [Complex.re_sum,RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_re,Complex.add_re,
    Fin.sum_univ_three] using h.symm

private theorem eigen_product (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsHermitian) :
    (∏ i, hA.eigenvalues i) = A.det.re := by
  have h := congrArg Complex.re hA.det_eq_prod_eigenvalues
  simpa only [Fin.prod_univ_three,RCLike.ofReal_eq_complex_ofReal,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using h.symm

private theorem entryModulus_trace_square {G : Matrix (Fin 3) (Fin 3) ℂ}
    (hG : G.IsHermitian) :
    (entryModulus G*entryModulus G).trace.re = (G*G).trace.re := by
  rw [hermitian_trace_square _ (entryModulus_hermitian hG),hermitian_trace_square _ hG]
  simp only [entryModulus, Matrix.map_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]

private theorem entryModulus_second {G : Matrix (Fin 3) (Fin 3) ℂ}
    (hG : G.PosSemidef) :
    (Multiset.esymm ({((entryModulus_hermitian hG.isHermitian).eigenvalues) 0, ((entryModulus_hermitian hG.isHermitian).eigenvalues) 1, ((entryModulus_hermitian hG.isHermitian).eigenvalues) 2} : Multiset ℝ) 2) = (Multiset.esymm ({(hG.isHermitian.eigenvalues) 0, (hG.isHermitian.eigenvalues) 1, (hG.isHermitian.eigenvalues) 2} : Multiset ℝ) 2) := by
  have hm : (∑ i, (entryModulus_hermitian hG.isHermitian).eigenvalues i) = (∑ i, hG.isHermitian.eigenvalues i) := by
    rw [eigen_mass,eigen_mass,entryModulus_trace hG]
  have hs : (∑ i, ((entryModulus_hermitian hG.isHermitian).eigenvalues i)^2) =
      ∑ i, (hG.isHermitian.eigenvalues i)^2 := by
    rw [sum_eigenvalue_squares, sum_eigenvalue_squares,entryModulus_trace_square hG.isHermitian]
  have h1 := second_eq_mass_sq_sub_squares (entryModulus_hermitian hG.isHermitian).eigenvalues
  have h2 := second_eq_mass_sq_sub_squares hG.isHermitian.eigenvalues
  rw [hm,hs] at h1
  linarith

theorem entryModulus_posSemidef {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.PosSemidef) :
    (entryModulus G).PosSemidef := by
  let hK := entryModulus_hermitian hG.isHermitian
  apply hK.posSemidef_iff_eigenvalues_nonneg.mpr
  apply nonneg_of_coeff_nonneg hK.eigenvalues
  · rw [eigen_mass,entryModulus_trace hG]
    exact (Complex.nonneg_iff.mp hG.trace_nonneg).1
  · rw [entryModulus_second hG, esymm_three]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hG.eigenvalues_nonneg 0) (hG.eigenvalues_nonneg 1))
        (mul_nonneg (hG.eigenvalues_nonneg 0) (hG.eigenvalues_nonneg 2)))
      (mul_nonneg (hG.eigenvalues_nonneg 1) (hG.eigenvalues_nonneg 2))
  · rw [eigen_product]
    exact (Complex.nonneg_iff.mp hG.det_nonneg).1.trans (entryModulus_det_mono hG)

theorem entryModulus_entropy_mono {G : Matrix (Fin 3) (Fin 3) ℂ} (hG : G.PosSemidef) :
    (-(Matrix.trace (G * CFC.log G)).re) ≤ (-(Matrix.trace ((entryModulus G) * CFC.log (entryModulus G))).re) := by
  let hK := entryModulus_hermitian hG.isHermitian
  have hpsd := entryModulus_posSemidef hG
  rw [entropy_eq_spectrum G hG.isHermitian,entropy_eq_spectrum (entryModulus G) hK]
  apply entropy_mono_product hG.eigenvalues_nonneg hpsd.eigenvalues_nonneg
  · rw [eigen_mass,eigen_mass,entryModulus_trace hG]
  · exact (entryModulus_second hG).symm
  · rw [eigen_product,eigen_product]
    exact entryModulus_det_mono hG

end D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy
