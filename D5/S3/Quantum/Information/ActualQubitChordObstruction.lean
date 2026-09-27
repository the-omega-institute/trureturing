/- GID: D5/S3/Quantum/Information/ActualQubitChordObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualQubitChordObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two exact signal probes force a pure-ended qubit chord, an endpoint overlap bound, and a pointwise spectral QFI lower bound on the original curve. -/

import D5.S3.Quantum.Information.ActualPureQubitFisherRank
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Information.ActualQubitChordObstruction

/-- The uniform signal and the balanced signal on coordinates zero and two. -/
def signalProbe (k : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  if k = 0 then (1 / 3 : ℂ) • Matrix.vecMulVec (![1, 1, 1] : Fin 3 → ℂ) (star ![1, 1, 1])
  else (1 / 2 : ℂ) • Matrix.vecMulVec (![1, 0, 1] : Fin 3 → ℂ) (star ![1, 0, 1])

/-- Required outputs for the two actual signals. -/
def probeTarget (a u : ℝ) (k : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  if k = 0 then (1 / 3 : ℂ) • !![1, (a : ℂ), (u : ℂ); a, 1, a; u, a, 1]
  else (1 / 2 : ℂ) • !![1, 0, (u : ℂ); 0, 0, 0; u, 0, 1]

/-- The canonical channel acts on the tensor of a fixed signal and a program. -/
def programOutput
    (G : QuantumChannel (Fin 3 × Fin 2) (Fin 3)) (k : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ :=
    ((CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ).comp
      (G.toCompletelyPositiveMap.toLinearMap.restrictScalars ℝ)).comp
      ((CStarMatrix.ofMatrixStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ).comp
        (Matrix.kroneckerBilinear (R := ℝ) (signalProbe k)))

/-- Joint real observation of the traceless Bloch part by the two fixed probes. -/
def jointObservation (G : QuantumChannel (Fin 3 × Fin 2) (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) := by
  let B : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := {
    toFun := blochMatrix 0
    map_add' r s := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring
    map_smul' t r := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring }
  exact LinearMap.pi fun k => (programOutput G k).comp B

/-- Global exactness of one canonical processor on two actual signals forces a
nonconstant affine program chord with pure endpoints and a bounded overlap.
At each interior point where the original curve is differentiable, its pointwise
support-safe spectral QFI satisfies the sharp global lower bound.
The affine replacement is asserted exact only for the two specified signals. -/
theorem actual_two_probe_chord_and_qfi (a : ℝ) (_ha : 0 < a) (ha1 : a < 1)
    (G : QuantumChannel (Fin 3 × Fin 2) (Fin 3))
    (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hrho : ∀ u ∈ Ioo (2 * a - 1) 1, (rho u).PosSemidef ∧ trace (rho u) = 1)
    (hexact : ∀ u ∈ Ioo (2 * a - 1) 1, ∀ k, programOutput G k (rho u) = probeTarget a u k) :
    ((∀ k, (signalProbe k).PosSemidef ∧ trace (signalProbe k) = 1) ∧
    ∃ (c v : EuclideanSpace ℝ (Fin 3)) (b : ℝ),
      v ≠ 0 ∧ 2 * a ^ 2 - 1 ≤ b ∧ b ≤ 2 * a - 1 ∧ b < 1 ∧
      c ∈ (jointObservation G).kerᗮ ∧ v ∈ (jointObservation G).kerᗮ ∧
      (∀ u ∈ Ioo (2 * a - 1) 1,
        (jointObservation G).kerᗮ.starProjection (bloch (rho u)) = c + u • v) ∧
      (∀ (u : ℝ) (k : Fin 2), programOutput G k (blochMatrix 1 (c + u • v)) = probeTarget a u k) ∧
      (∀ u : ℝ, ‖c + u • v‖ ≤ 1 ↔ u ∈ Icc b 1) ∧
      (∀ u : ℝ, (blochMatrix 1 (c + u • v)).PosSemidef ↔ u ∈ Icc b 1) ∧
      (∀ u : ℝ, trace (blochMatrix 1 (c + u • v)) = 1) ∧
      (∀ u ∈ Ioo (2 * a - 1) 1, ‖c + u • v‖ < 1) ∧
      ‖c + v‖ = 1 ∧ ‖c + b • v‖ = 1 ∧
      blochMatrix 1 (c + v) * blochMatrix 1 (c + v) = blochMatrix 1 (c + v) ∧
      blochMatrix 1 (c + b • v) * blochMatrix 1 (c + b • v) = blochMatrix 1 (c + b • v) ∧
      0 ≤ (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ∧
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ≤ (1 + b) / 2 ∧
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re < 1) ∧
    (∀ u (hu : u ∈ Ioo (2 * a - 1) 1), DifferentiableAt ℝ rho u →
      (1 - a ^ 2) / ((1 - u) * (1 + u - 2 * a ^ 2)) ≤
        spectralQFI (rho u) (deriv rho u) (hrho u hu).1) := by
  classical
  have chord :
    ((∀ k, (signalProbe k).PosSemidef ∧ trace (signalProbe k) = 1) ∧
    ∃ (c v : EuclideanSpace ℝ (Fin 3)) (b : ℝ),
      v ≠ 0 ∧ 2 * a ^ 2 - 1 ≤ b ∧ b ≤ 2 * a - 1 ∧ b < 1 ∧
      c ∈ (jointObservation G).kerᗮ ∧ v ∈ (jointObservation G).kerᗮ ∧
      (∀ u ∈ Ioo (2 * a - 1) 1,
        (jointObservation G).kerᗮ.starProjection (bloch (rho u)) = c + u • v) ∧
      (∀ (u : ℝ) (k : Fin 2), programOutput G k (blochMatrix 1 (c + u • v)) = probeTarget a u k) ∧
      (∀ u : ℝ, ‖c + u • v‖ ≤ 1 ↔ u ∈ Icc b 1) ∧
      (∀ u : ℝ, (blochMatrix 1 (c + u • v)).PosSemidef ↔ u ∈ Icc b 1) ∧
      (∀ u : ℝ, trace (blochMatrix 1 (c + u • v)) = 1) ∧
      (∀ u ∈ Ioo (2 * a - 1) 1, ‖c + u • v‖ < 1) ∧
      ‖c + v‖ = 1 ∧ ‖c + b • v‖ = 1 ∧
      blochMatrix 1 (c + v) * blochMatrix 1 (c + v) = blochMatrix 1 (c + v) ∧
      blochMatrix 1 (c + b • v) * blochMatrix 1 (c + b • v) = blochMatrix 1 (c + b • v) ∧
      0 ≤ (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ∧
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ≤ (1 + b) / 2 ∧
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re < 1 ∧
      (∀ x : ℝ, ‖c + x • v‖ ^ 2 = 1 + ‖v‖ ^ 2 * (x - b) * (x - 1)) ∧
      b = 1 - 2 * ⟪c + v, v⟫_ℝ / ‖v‖ ^ 2) ∧
      (∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ ≤ 1 → (blochMatrix 1 r).PosSemidef) ∧
      (∀ r s : EuclideanSpace ℝ (Fin 3),
        (trace (blochMatrix 1 r * blochMatrix 1 s)).re = (1 + ⟪r, s⟫_ℝ) / 2) ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.IsHermitian → trace M = 1 →
        M = blochMatrix 1 (bloch M)) := by
    classical
    have herm (r : EuclideanSpace ℝ (Fin 3)) : (blochMatrix 1 r).IsHermitian := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blochMatrix, Matrix.conjTranspose_apply, sub_eq_add_neg]
    have trace_bloch (r : EuclideanSpace ℝ (Fin 3)) : trace (blochMatrix 1 r) = 1 := by
      simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, blochMatrix,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    have det_bloch (r : EuclideanSpace ℝ (Fin 3)) :
        (blochMatrix 1 r).det = (((1 - ‖r‖ ^ 2) / 4 : ℝ) : ℂ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Complex.ext <;>
        simp [blochMatrix, Matrix.det_fin_two, Fin.sum_univ_three, pow_two] <;> ring
    have pure (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ = 1) :
        blochMatrix 1 r * blochMatrix 1 r = blochMatrix 1 r := by
      have he : adjugate (blochMatrix 1 r) = 1 - blochMatrix 1 r := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, blochMatrix] <;> ring
      have hh := Matrix.mul_adjugate (blochMatrix 1 r)
      rw [he, det_bloch, hr] at hh
      norm_num [mul_sub] at hh
      exact (sub_eq_zero.mp hh).symm
    have physical (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) :
        (blochMatrix 1 r).PosSemidef := by
      have ht := congrArg Complex.re ((herm r).trace_eq_sum_eigenvalues)
      rw [trace_bloch] at ht
      simp only [Fin.sum_univ_two, Complex.add_re, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.one_re] at ht
      have hd := congrArg Complex.re ((herm r).det_eq_prod_eigenvalues)
      rw [det_bloch] at hd
      simp only [Fin.prod_univ_two, Complex.mul_re, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] at hd
      have hp : 0 ≤ (herm r).eigenvalues 0 * (herm r).eigenvalues 1 := by
        nlinarith only [hd, hr, norm_nonneg r]
      apply (herm r).posSemidef_iff_eigenvalues_nonneg.mpr
      have h0 : 0 ≤ (herm r).eigenvalues 0 := by
        nlinarith only [ht, hp, sq_nonneg ((herm r).eigenvalues 0)]
      have h1 : 0 ≤ (herm r).eigenvalues 1 := by
        nlinarith only [ht, hp, sq_nonneg ((herm r).eigenvalues 1)]
      intro i
      fin_cases i
      · exact h0
      · exact h1
    have pair_bloch (r s : EuclideanSpace ℝ (Fin 3)) :
        (trace (blochMatrix 1 r * blochMatrix 1 s)).re = (1 + ⟪r, s⟫_ℝ) / 2 := by
      simp only [trace, blochMatrix, Fin.isValue, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sub,
        cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, Matrix.smul_empty,
        tail_cons, empty_vecMul, add_zero, add_cons, empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, diag_apply,
        of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two, cons_val_zero, cons_val_one, Complex.add_re,
        Complex.mul_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im,
        Complex.one_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero, Complex.sub_re, Complex.I_re, Complex.I_im,
        mul_one, sub_self, Complex.sub_im, Complex.mul_im, zero_sub, zero_add, PiLp.inner_apply, RCLike.inner_apply,
        Real.ringHom_apply, Fin.sum_univ_three]
      ring
    have represent (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian)
        (ht : trace M = 1) : M = blochMatrix 1 (bloch M) := by
      have h00 : (M 0 0).im = 0 := by
        have h := congrArg Complex.im (hM.apply 0 0)
        simp at h
        linarith
      have h11 : (M 1 1).im = 0 := by
        have h := congrArg Complex.im (hM.apply 1 1)
        simp at h
        linarith
      have h10r : (M 1 0).re = (M 0 1).re := by
        have h := congrArg Complex.re (hM.apply 1 0)
        simpa using h.symm
      have h10i : (M 1 0).im = -(M 0 1).im := by
        have h := congrArg Complex.im (hM.apply 1 0)
        simpa using h.symm
      have htr := congrArg Complex.re ht
      simp [Matrix.trace, Fin.sum_univ_two] at htr
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp only [Fin.zero_eta, Fin.isValue, blochMatrix, bloch, neg_mul, Matrix.cons_val, Complex.ofReal_add,
          Complex.ofReal_one, Complex.ofReal_sub, cons_val_zero, Complex.ofReal_mul, Complex.ofReal_ofNat,
          cons_val_one, Complex.ofReal_neg, sub_neg_eq_add, of_apply, cons_val', cons_val_fin_one,
          Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.sub_re, Complex.ofReal_re, h00,
          Complex.div_ofNat_im, Complex.add_im, Complex.one_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, add_zero, zero_div, Fin.mk_one, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul, Complex.I_im, mul_one, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, zero_add, h10r, Complex.neg_re,
          neg_zero, h10i, Complex.neg_im, h11] <;> linarith
    have radius (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef)
        (ht : trace M = 1) : ‖bloch M‖ ≤ 1 := by
      have hd := (Complex.nonneg_iff.mp hM.det_nonneg).1
      rw [represent M hM.isHermitian ht, det_bloch, Complex.ofReal_re] at hd
      nlinarith only [hd, norm_nonneg (bloch M)]
    have probes (k : Fin 2) : (signalProbe k).PosSemidef ∧ trace (signalProbe k) = 1 := by
      fin_cases k
      · constructor
        · simpa [signalProbe] using
            (Matrix.posSemidef_vecMulVec_self_star (![1, 1, 1] : Fin 3 → ℂ)).smul
              (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 3)
        · norm_num [signalProbe, Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_succ]
      · constructor
        · simpa [signalProbe] using
            (Matrix.posSemidef_vecMulVec_self_star (![1, 0, 1] : Fin 3 → ℂ)).smul
              (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 2)
        · norm_num [signalProbe, Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_succ]
    let O := programOutput G
    have hO (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) : O k M = programOutput G k M := rfl
    have positive (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
        (O k M).PosSemidef := by
      exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg G.toCompletelyPositiveMap
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ((probes k).1.kronecker hM).nonneg))).posSemidef
    have preserving (k : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) : trace (O k M) = trace M := by
      have h := G.trace_preserving (CStarMatrix.ofMatrix (Matrix.kronecker (signalProbe k) M))
      change trace (O k M) = trace (Matrix.kronecker (signalProbe k) M) at h
      simpa [Matrix.trace_kronecker, (probes k).2] using h
    have split (r : EuclideanSpace ℝ (Fin 3)) :
        blochMatrix 1 r = blochMatrix 1 0 + blochMatrix 0 r := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring
    let A : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) :=
      jointObservation G
    let p : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
      fun k => probeTarget a 0 k - O k (blochMatrix 1 0)
    let q : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
      fun k => probeTarget a 1 k - probeTarget a 0 k
    have target_affine (u : ℝ) (k : Fin 2) :
        probeTarget a u k = probeTarget a 0 k + u • q k := by
      fin_cases k <;> simp [probeTarget, q] <;> ring
    have hq : q ≠ 0 := by
      intro hz
      have h := congrArg (fun f : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ => (f 1 0 2).re) hz
      norm_num [q, probeTarget, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h
    have readout (u : ℝ) (hu : u ∈ Ioo (2 * a - 1) 1) :
        A (bloch (rho u)) = p + u • q := by
      ext k i j
      have h := hexact u hu k
      rw [represent (rho u) (hrho u hu).1.isHermitian (hrho u hu).2,
        split, ← hO, map_add, target_affine] at h
      have hh := congrFun₂ h i j
      change (O k (blochMatrix 0 (bloch (rho u)))) i j =
        (probeTarget a 0 k - O k (blochMatrix 1 0) + u • q k) i j
      simp only [Matrix.add_apply, Matrix.sub_apply] at hh ⊢
      linear_combination hh
    let K := LinearMap.ker A
    let P := Kᗮ.starProjection
    have hAP (z : EuclideanSpace ℝ (Fin 3)) : A (P z) = A z := by
      have hz : z - P z ∈ K := by
        simpa only [Submodule.orthogonal_orthogonal] using
          (Submodule.sub_starProjection_mem_orthogonal (K := Kᗮ) z)
      have hz' := LinearMap.mem_ker.mp hz
      exact (sub_eq_zero.mp (by simpa only [map_sub] using hz')).symm
    have hPker {z : EuclideanSpace ℝ (Fin 3)} (hz : A z = 0) : P z = 0 := by
      have h := Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        (show z ∈ Kᗮᗮ by simpa [K] using LinearMap.mem_ker.mpr hz)
      exact congrArg Subtype.val h
    let t := (a + 1) / 2
    have haI : a ∈ Ioo (2 * a - 1) 1 := by constructor <;> linarith
    have htI : t ∈ Ioo (2 * a - 1) 1 := by dsimp [t]; constructor <;> linarith
    have hta : 0 < t - a := by dsimp [t]; linarith
    let w := (t - a)⁻¹ • (bloch (rho t) - bloch (rho a))
    have hAw : A w = q := by
      simp only [w, map_smul, map_sub, readout _ htI, readout _ haI]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, inv_mul_cancel₀ hta.ne', one_smul]
    let c := P (bloch (rho a)) - a • P w
    let v := P w
    have hv : v ≠ 0 := by
      intro hz
      apply hq
      rw [← hAw, ← hAP]
      change A v = 0
      rw [hz, map_zero]
    have projected (u : ℝ) (hu : u ∈ Ioo (2 * a - 1) 1) :
        P (bloch (rho u)) = c + u • v := by
      have hz : A (bloch (rho u) - bloch (rho a) - (u - a) • w) = 0 := by
        simp only [map_sub, map_smul, readout _ hu, readout _ haI, hAw]
        module
      have h := hPker hz
      simp only [map_sub, map_smul] at h
      have h' := sub_eq_zero.mp h
      rw [sub_smul] at h'
      dsimp only [c, v]
      calc
        P (bloch (rho u)) = (u • P w - a • P w) + P (bloch (rho a)) := sub_eq_iff_eq_add.mp h'
        _ = _ := by abel
    have norm_le (u : ℝ) (hu : u ∈ Ioo (2 * a - 1) 1) :
        ‖c + u • v‖ ≤ ‖bloch (rho u)‖ := by
      rw [← projected u hu]
      exact Submodule.norm_starProjection_apply_le _ _
    have inside (u : ℝ) (hu : u ∈ Ioo (2 * a - 1) 1) : ‖c + u • v‖ ≤ 1 :=
      (norm_le u hu).trans (radius _ (hrho u hu).1 (hrho u hu).2)
    have affine_output (u : ℝ) (k : Fin 2) :
        O k (blochMatrix 1 (c + u • v)) = probeTarget a u k := by
      have hAc : A c = p := by
        simp only [c, map_sub, map_smul, hAP, readout _ haI, hAw]
        module
      have hAv : A v = q := (hAP w).trans hAw
      have hh : A (c + u • v) = p + u • q := by rw [map_add, map_smul, hAc, hAv]
      have hk := congrFun hh k
      change O k (blochMatrix 0 (c + u • v)) = p k + u • q k at hk
      rw [split, map_add, hk, target_affine]
      dsimp [p]
      abel
    have bounds (u : ℝ) (hu : ‖c + u • v‖ ≤ 1) : 2 * a ^ 2 - 1 ≤ u ∧ u ≤ 1 := by
      have hp := positive 0 _ (physical _ hu)
      rw [affine_output] at hp
      have hx := (Complex.nonneg_iff.mp
        (hp.dotProduct_mulVec_nonneg (![1, 0, -1] : Fin 3 → ℂ))).1
      have hy := (Complex.nonneg_iff.mp
        (hp.dotProduct_mulVec_nonneg (![1, (-2 * a : ℝ), 1] : Fin 3 → ℂ))).1
      norm_num [probeTarget, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hx hy
      constructor <;> nlinarith only [hx, hy]
    have line_cont : Continuous fun u : ℝ => ‖c + u • v‖ := by fun_prop
    have closed_inside (u : ℝ) (hu : u ∈ Icc (2 * a - 1) 1) : ‖c + u • v‖ ≤ 1 := by
      have hs : IsClosed {u : ℝ | ‖c + u • v‖ ≤ 1} := isClosed_le line_cont continuous_const
      have hi : Ioo (2 * a - 1) 1 ⊆ {u : ℝ | ‖c + u • v‖ ≤ 1} := inside
      have hcl := hs.closure_subset_iff.mpr hi
      rw [closure_Ioo (by linarith : 2 * a - 1 ≠ 1)] at hcl
      exact hcl hu
    have plus_norm : ‖c + v‖ = 1 := by
      have hle : ‖c + v‖ ≤ 1 := by
        simpa using closed_inside 1 (by constructor <;> linarith)
      apply le_antisymm hle
      by_contra hn
      have hlt : ‖c + (1 : ℝ) • v‖ < 1 := by simpa using lt_of_not_ge hn
      have hopen : IsOpen {u : ℝ | ‖c + u • v‖ < 1} := isOpen_lt line_cont continuous_const
      obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hopen 1 hlt
      have hi : ‖c + (1 + δ / 2) • v‖ < 1 := hb (by
        rw [Metric.mem_ball, Real.dist_eq]
        have he : 1 + δ / 2 - 1 = δ / 2 := by ring
        rw [he, abs_of_pos (half_pos hδ)]
        linarith)
      have := (bounds (1 + δ / 2) hi.le).2
      linarith
    let d := ‖v‖ ^ 2
    have hd : 0 < d := sq_pos_of_pos (norm_pos_iff.mpr hv)
    let b := 1 - 2 * ⟪c + v, v⟫_ℝ / d
    have factor (u : ℝ) : ‖c + u • v‖ ^ 2 = 1 + d * (u - b) * (u - 1) := by
      have hr : c + u • v = (c + v) + (u - 1) • v := by module
      rw [hr, norm_add_sq_real, plus_norm, inner_smul_right, norm_smul]
      dsimp [b, d]
      rw [mul_pow, sq_abs]
      field_simp
      ring
    have b_le : b ≤ 2 * a - 1 := by
      have hn := closed_inside (2 * a - 1) (by constructor <;> linarith)
      have hs : ‖c + (2 * a - 1) • v‖ ^ 2 ≤ 1 := by nlinarith only [hn, norm_nonneg (c + (2 * a - 1) • v)]
      rw [factor] at hs
      have hneg : 2 * a - 1 - 1 < 0 := by linarith
      have hprod : 0 ≤ d * (2 * a - 1 - b) := by nlinarith only [hs, hneg]
      have : 0 ≤ 2 * a - 1 - b := nonneg_of_mul_nonneg_right hprod hd
      linarith
    have b_lt : b < 1 := by linarith
    have minus_norm : ‖c + b • v‖ = 1 := by
      have hs := factor b
      simp only [sub_self, mul_zero, zero_mul, add_zero] at hs
      nlinarith only [hs, norm_nonneg (c + b • v)]
    have lower : 2 * a ^ 2 - 1 ≤ b := (bounds b minus_norm.le).1
    have chord (u : ℝ) : ‖c + u • v‖ ≤ 1 ↔ u ∈ Icc b 1 := by
      have hs := factor u
      constructor
      · intro hu
        have hsq : ‖c + u • v‖ ^ 2 ≤ 1 := by nlinarith only [hu, norm_nonneg (c + u • v)]
        have hprod : (u - b) * (u - 1) ≤ 0 := by nlinarith only [hs, hsq, hd]
        constructor <;> nlinarith only [hprod, b_lt, sq_nonneg (u - 1), sq_nonneg (u - b)]
      · rintro ⟨hbu, hu1⟩
        have hprod : (u - b) * (u - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        have : d * ((u - b) * (u - 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le hprod
        nlinarith only [this, hs, norm_nonneg (c + u • v)]
    have strict_inside (u : ℝ) (hu : u ∈ Ioo (2 * a - 1) 1) : ‖c + u • v‖ < 1 := by
      have hs := factor u
      have hprod : (u - b) * (u - 1) < 0 := mul_neg_of_pos_of_neg (by linarith [hu.1]) (by linarith [hu.2])
      have : d * ((u - b) * (u - 1)) < 0 := mul_neg_of_pos_of_neg hd hprod
      nlinarith only [this, hs, norm_nonneg (c + u • v)]
    have complement : (1 - signalProbe 1).PosSemidef := by
      have hi : signalProbe 1 * signalProbe 1 = signalProbe 1 := by
        simp only [signalProbe, show (1 : Fin 2) ≠ 0 by decide, if_false,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
        norm_num [dotProduct, Fin.sum_univ_succ]
      have hP : IsStarProjection (signalProbe 1) := ⟨hi, (probes 1).1.isHermitian⟩
      exact hP.one_sub_nonneg.posSemidef
    let f : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ := {
      toFun M := (trace (signalProbe 1 * O 1 M)).re
      map_add' M N := by simp [map_add, Matrix.mul_add, Matrix.trace_add]
      map_smul' t M := by
        simp [map_smul, Matrix.trace_smul] }
    have f_bounds (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) (ht : trace M = 1) :
        0 ≤ f M ∧ f M ≤ 1 := by
      have hp := positive 1 M hM
      have hl := RHLinalg.trace_mul_nonneg_of_posSemidef (probes 1).1 hp
      have hu := RHLinalg.trace_mul_nonneg_of_posSemidef complement hp
      rw [sub_mul, one_mul, Matrix.trace_sub, preserving, ht] at hu
      change 0 ≤ (1 - trace (signalProbe 1 * O 1 M)).re at hu
      simp only [Complex.sub_re, Complex.one_re] at hu
      exact ⟨hl, by change (trace (signalProbe 1 * O 1 M)).re ≤ 1; linarith only [hu]⟩
    let qf : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := {
      toFun r := (trace (signalProbe 1 * (A r) 1)).re
      map_add' r s := by simp [map_add, Matrix.mul_add, Matrix.trace_add]
      map_smul' t r := by simp [map_smul, Matrix.trace_smul] }
    let z : EuclideanSpace ℝ (Fin 3) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm
        (LinearMap.toContinuousLinearMap qf)
    let α := f (blochMatrix 1 0)
    have pairing (r : EuclideanSpace ℝ (Fin 3)) : f (blochMatrix 1 r) = α + ⟪z, r⟫_ℝ := by
      have hz : ⟪z, r⟫_ℝ = qf r := InnerProductSpace.toDual_symm_apply
      rw [split, map_add, hz]
      rfl
    have effect_bounds (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) :
        0 ≤ α + ⟪z, r⟫_ℝ ∧ α + ⟪z, r⟫_ℝ ≤ 1 := by
      rw [← pairing]
      exact f_bounds _ (physical r hr) (trace_bloch r)
    have spectral_bounds : ‖z‖ ≤ α ∧ α + ‖z‖ ≤ 1 := by
      by_cases hz : z = 0
      · simpa [hz] using effect_bounds 0 (by simp)
      · have hnorm : ‖‖z‖⁻¹ • z‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hz]
        have hp := (effect_bounds (‖z‖⁻¹ • z) hnorm.le).2
        have hm := (effect_bounds (-(‖z‖⁻¹ • z)) (by simpa using hnorm.le)).1
        have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        have he : ⟪z, ‖z‖⁻¹ • z⟫_ℝ = ‖z‖ := by
          rw [inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        rw [he] at hp
        rw [inner_neg_right, he] at hm
        exact ⟨by linarith, hp⟩
    have readout_line (u : ℝ) : f (blochMatrix 1 (c + u • v)) = (1 + u) / 2 := by
      change (trace (signalProbe 1 * O 1 (blochMatrix 1 (c + u • v)))).re = _
      rw [affine_output]
      simp only [trace, signalProbe, Fin.isValue, one_ne_zero, ↓reduceIte, Nat.succ_eq_add_one, Nat.reduceAdd,
        one_div, vecMulVec, Pi.star_apply, RCLike.star_def, smul_of, probeTarget, smul_cons, smul_eq_mul, mul_one, mul_zero,
        Matrix.smul_empty, diag_apply, Matrix.mul_apply, of_apply, Pi.smul_apply, cons_val', cons_val_fin_one,
        Fin.sum_univ_succ, cons_val_zero, map_one, cons_val_succ, map_zero, zero_mul, Finset.univ_unique,
        Fin.default_eq_zero, sum_const, Finset.card_singleton, one_smul, zero_add, add_zero, smul_add, Complex.add_re,
        Complex.mul_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im,
        Complex.im_ofNat, neg_zero, zero_div, sub_zero, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
      ring
    have saturated : α + ⟪z, c + v⟫_ℝ = 1 := by
      have h := readout_line 1
      rw [pairing] at h
      simpa using h
    have inner_le : ⟪z, c + v⟫_ℝ ≤ ‖z‖ := by
      simpa [plus_norm] using real_inner_le_norm z (c + v)
    have aligned : z = ‖z‖ • (c + v) := by
      have he : ⟪z, c + v⟫_ℝ = ‖z‖ * ‖c + v‖ := by
        rw [plus_norm]
        linarith only [saturated, inner_le, spectral_bounds.2]
      have hh := inner_eq_norm_mul_iff_real.mp he
      simpa [plus_norm] using hh
    have overlap_bound : (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re ≤
        (1 + b) / 2 := by
      rw [pair_bloch]
      have hline := readout_line b
      rw [pairing, aligned, inner_smul_left] at hline
      simp only [starRingEnd_apply, star_trivial] at hline
      have hα : α + ‖z‖ = 1 := by linarith only [saturated, inner_le, spectral_bounds.2]
      have hzhalf : ‖z‖ ≤ 1 / 2 := by linarith only [hα, spectral_bounds.1]
      have hi : ⟪c + v, c + b • v⟫_ℝ ≤ 1 := by
        simpa [plus_norm, minus_norm] using real_inner_le_norm (c + v) (c + b • v)
      have hprod := mul_nonneg (by linarith : 0 ≤ 1 / 2 - ‖z‖) (by linarith : 0 ≤ 1 - ⟪c + v, c + b • v⟫_ℝ)
      nlinarith only [hline, hα, hprod]
    have inverse_bloch (r : EuclideanSpace ℝ (Fin 3)) : bloch (blochMatrix 1 r) = r := by
      ext i
      fin_cases i <;> simp [bloch, blochMatrix] <;> ring
    refine ⟨?_, physical, pair_bloch, represent⟩
    refine ⟨probes, c, v, b, hv, lower, b_le, b_lt, ?_, ?_, projected,
      affine_output, chord, ?_, fun u => trace_bloch (c + u • v), strict_inside,
      plus_norm, minus_norm, pure _ plus_norm, pure _ minus_norm, ?_, overlap_bound, ?_, factor, rfl⟩
    · exact Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _)
        (Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _))
    · exact Submodule.starProjection_apply_mem _ _
    · intro u
      constructor
      · intro hp
        apply (chord u).mp
        have hh := radius _ hp (trace_bloch _)
        rwa [inverse_bloch] at hh
      · intro hu
        exact physical _ ((chord u).mpr hu)
    · exact RHLinalg.trace_mul_nonneg_of_posSemidef
        (physical _ plus_norm.le) (physical _ minus_norm.le)
    · exact lt_of_le_of_lt overlap_bound (by linarith only [b_lt])
  obtain ⟨chord, physical, pair_bloch, represent⟩ := chord
  obtain ⟨probes, c, v, b, hv, lower, b_le, b_lt, hcK, hvK, projected,
    affine_output, chord_norm, chord_psd, chord_trace, strict_inside,
    plus_norm, minus_norm, plus_pure, minus_pure, overlap_nonneg,
    overlap_bound, overlap_lt, factor, bdef⟩ := chord
  refine ⟨⟨probes, c, v, b, hv, lower, b_le, b_lt, hcK, hvK, projected,
    affine_output, chord_norm, chord_psd, chord_trace, strict_inside, plus_norm,
    minus_norm, plus_pure, minus_pure, overlap_nonneg, overlap_bound, overlap_lt⟩, ?_⟩
  intro u hu hdiff
  let r := c + u • v
  let d := ‖v‖ ^ 2
  let β := 1 - ‖r‖ ^ 2
  let A := ⟪r, v⟫_ℝ
  have hd : 0 < d := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hr : ‖r‖ < 1 := strict_inside u hu
  have hβ : 0 < β := sub_pos.mpr (pow_lt_one₀ (norm_nonneg r) hr (by decide))
  let Q := d + A ^ 2 / β
  have hQ : 0 < Q := add_pos_of_pos_of_nonneg hd (div_nonneg (sq_nonneg A) hβ.le)
  let ell := v + (A / β) • r
  have ell_v : ⟪ell, v⟫_ℝ = Q := by
    simp only [ell, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [Q, d, A]
    ring
  have ell_r : ⟪ell, r⟫_ℝ = A / β := by
    have hvr : ⟪v, r⟫_ℝ = A := real_inner_comm r v
    simp only [ell, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hvr]
    field_simp [hβ.ne']
    dsimp [β]
    ring
  have ell_energy : ‖ell‖ ^ 2 - ⟪ell, r⟫_ℝ ^ 2 = Q := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 1; arg 2; change v + (A / β) • r
    rw [inner_add_right, inner_smul_right, ell_v, ell_r]
    ring
  have hell : ell ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at ell_v
    linarith only [ell_v, hQ]
  have hellnorm : 0 < ‖ell‖ := norm_pos_iff.mpr hell
  let n := ‖ell‖⁻¹ • ell
  have hn : ‖n‖ = 1 := by simp [n, norm_smul, hellnorm.ne']
  have hrK : r ∈ (jointObservation G).kerᗮ :=
    Submodule.add_mem _ hcK (Submodule.smul_mem _ u hvK)
  have hellK : ell ∈ (jointObservation G).kerᗮ :=
    Submodule.add_mem _ hvK (Submodule.smul_mem _ (A / β) hrK)
  have hnK : n ∈ (jointObservation G).kerᗮ := Submodule.smul_mem _ _ hellK
  have observed (x : ℝ) (hx : x ∈ Ioo (2 * a - 1) 1) :
      ⟪n, bloch (rho x)⟫_ℝ = ⟪n, c + x • v⟫_ℝ := by
    rw [← projected x hx, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hnK]
  let z := ⟪n, r⟫_ℝ
  let w := ⟪n, v⟫_ℝ
  have hz : |z| < 1 := by
    calc
      |z| ≤ ‖n‖ * ‖r‖ := abs_real_inner_le_norm n r
      _ < 1 := by simpa [hn] using hr
  have hzp : 0 < 1 + z := by linarith [(abs_lt.mp hz).1]
  have hzm : 0 < 1 - z := by linarith [(abs_lt.mp hz).2]
  have hden : 0 < 1 - z ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one z).mpr hz)
  let N : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![blochMatrix 1 n, blochMatrix 1 (-n)]
  have hN : ∀ j, (N j).PosSemidef := by
    intro j
    fin_cases j
    · exact physical n hn.le
    · exact physical (-n) (by simpa using hn.le)
  have hNsum : ∑ j, N j = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N, Fin.sum_univ_two, blochMatrix] <;> ring
  let p : Fin 2 → ℝ := ![(1 + z) / 2, (1 - z) / 2]
  let vel : Fin 2 → ℝ := ![w / 2, -w / 2]
  have hp : ∀ j, 0 < p j := by
    intro j
    fin_cases j
    · exact half_pos hzp
    · exact half_pos hzm
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, u + t ∈ Ioo (2 * a - 1) 1 := by
    have ht : Tendsto (fun t : ℝ => u + t) (𝓝 0) (𝓝 u) := by
      have hc : Continuous (fun t : ℝ => u + t) := continuous_const.add continuous_id
      simpa using hc.tendsto 0
    exact ht (isOpen_Ioo.mem_nhds hu)
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, (rho (u + t)).PosSemidef := by
    filter_upwards [hnear] with t ht
    exact (hrho _ ht).1
  have hshift : DifferentiableAt ℝ (fun t : ℝ => rho (u + t)) 0 := by
    apply (differentiableAt_comp_add_left (𝕜 := ℝ) (f := rho) u (x := (0 : ℝ))).mpr
    convert! hdiff using 1 <;> simp only [add_zero]
  have hderiv : deriv (fun t : ℝ => rho (u + t)) 0 = deriv rho u := by
    convert! deriv_comp_const_add rho u 0 using 1 <;> simp only [add_zero] <;> rfl
  have hread : ∀ᶠ t : ℝ in 𝓝 0, ∀ j,
      (trace (N j * rho (u + t))).re = p j + t * vel j := by
    filter_upwards [hnear] with t ht
    intro j
    rw [represent _ (hrho _ ht).1.isHermitian (hrho _ ht).2]
    have he : ⟪n, c + (u + t) • v⟫_ℝ = z + t * w := by
      simp only [z, w, r, inner_add_right, inner_smul_right]
      ring
    fin_cases j
    · change (trace (blochMatrix 1 n * blochMatrix 1 (bloch (rho (u + t))))).re = _
      rw [pair_bloch, observed _ ht, he]
      dsimp [p, vel]
      ring
    · change (trace (blochMatrix 1 (-n) * blochMatrix 1 (bloch (rho (u + t))))).re = _
      rw [pair_bloch, inner_neg_left, observed _ ht, he]
      dsimp [p, vel]
      ring
  have hf := actual_fisher N (fun t : ℝ => rho (u + t)) p vel hN hNsum hp
    hshift hpos hread
  have fisher_normalization : (∑ j, vel j ^ 2 / p j) = Q := by
    have hw : w = Q / ‖ell‖ := by
      simp only [w, n, real_inner_smul_left, ell_v]
      ring
    have hz' : z = ⟪ell, r⟫_ℝ / ‖ell‖ := by
      simp only [z, n, real_inner_smul_left]
      ring
    have hbinary : (∑ j, vel j ^ 2 / p j) = w ^ 2 / (1 - z ^ 2) := by
      simp only [vel, p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp [hzp.ne', hzm.ne', hden.ne']
      ring
    rw [hbinary]
    apply (div_eq_iff hden.ne').mpr
    rw [hw, hz']
    field_simp [hellnorm.ne']
    nlinarith only [ell_energy]
  have hQFI : Q ≤ spectralQFI (rho u) (deriv rho u) (hrho u hu).1 := by
    simpa only [fisher_normalization, hderiv, add_zero] using hf
  -- The endpoint identities determine the quadratic norm deficit and the
  -- measurement energy. These are scalar normalizations of the live chord.
  have hup : ⟪c + v, v⟫_ℝ = (1 - b) * d / 2 := by
    change b = 1 - 2 * ⟪c + v, v⟫_ℝ / d at bdef
    field_simp [hd.ne'] at bdef
    linear_combination bdef / 2
  have hA : A = (u - (1 + b) / 2) * d := by
    have hrv : r = (c + v) + (u - 1) • v := by dsimp [r]; module
    dsimp only [A]
    rw [hrv, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hup]
    change (1 - b) * d / 2 + (u - 1) * d = _
    ring
  have hfactor : β = d * (u - b) * (1 - u) := by
    have h := factor u
    change ‖r‖ ^ 2 = 1 + d * (u - b) * (u - 1) at h
    dsimp only [β]
    linear_combination -h
  let s := (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re
  have hs : s = 1 - d * (1 - b) ^ 2 / 4 := by
    have hdiff : (c + v) - (c + b • v) = (1 - b) • v := by module
    have h := norm_sub_sq_real (c + v) (c + b • v)
    rw [hdiff, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, plus_norm, minus_norm] at h
    dsimp only [s]
    rw [pair_bloch]
    dsimp only [d]
    linear_combination h / 4
  have hub : 0 < u - b := sub_pos.mpr (b_le.trans_lt hu.1)
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  have hgeom : Q = (1 - s) / ((u - b) * (1 - u)) := by
    dsimp [Q]
    rw [hA, hfactor, hs]
    field_simp [hd.ne', hub.ne', hu1.ne']
    ring
  have hfirst : (1 - b) / (2 * (u - b) * (1 - u)) ≤ Q := by
    rw [hgeom]
    have he : (1 - b) / (2 * (u - b) * (1 - u)) =
        ((1 - b) / 2) / ((u - b) * (1 - u)) := by
      simp only [div_div, mul_assoc]
    rw [he]
    apply div_le_div_of_nonneg_right _ (mul_nonneg hub.le hu1.le)
    change (1 - b) / 2 ≤ 1 - s
    calc
      (1 - b) / 2 = 1 - (1 + b) / 2 := by ring
      _ ≤ 1 - s := sub_le_sub_left overlap_bound 1
  have hul : 0 < 1 + u - 2 * a ^ 2 := by linarith only [lower, hub]
  have hcompare : (1 - a ^ 2) / ((1 - u) * (1 + u - 2 * a ^ 2)) ≤
      (1 - b) / (2 * (u - b) * (1 - u)) := by
    apply (div_le_div_iff₀ (mul_pos hu1 hul) (mul_pos (mul_pos zero_lt_two hub) hu1)).mpr
    have hprod := mul_nonneg (sub_nonneg.mpr lower) (sq_nonneg (1 - u))
    linear_combination hprod
  exact hcompare.trans (hfirst.trans hQFI)

#print axioms actual_two_probe_chord_and_qfi

end D5.S3.Quantum.Information.ActualQubitChordObstruction
