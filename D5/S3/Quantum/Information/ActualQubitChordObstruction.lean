/- GID: D5/S3/Quantum/Information/ActualQubitChordObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualQubitChordObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two exact signal probes of a canonical qubit processor force a pure-ended affine chord and an endpoint overlap obstruction. -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
open scoped InnerProductSpace ComplexOrder MatrixOrder Topology
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
The affine replacement is asserted exact only for the two specified signals. -/
theorem actual_two_probe_chord_obstruction (a : ℝ) (_ha : 0 < a) (ha1 : a < 1)
    (G : QuantumChannel (Fin 3 × Fin 2) (Fin 3))
    (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hrho : ∀ u ∈ Ioo (2 * a - 1) 1, (rho u).PosSemidef ∧ trace (rho u) = 1)
    (hexact : ∀ u ∈ Ioo (2 * a - 1) 1, ∀ k, programOutput G k (rho u) = probeTarget a u k) :
    (∀ k, (signalProbe k).PosSemidef ∧ trace (signalProbe k) = 1) ∧
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
      (trace (blochMatrix 1 (c + v) * blochMatrix 1 (c + b • v))).re < 1 := by
  classical
  have herm (r : EuclideanSpace ℝ (Fin 3)) : (blochMatrix 1 r).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blochMatrix, Matrix.conjTranspose_apply, sub_eq_add_neg]
  have trace_bloch (r : EuclideanSpace ℝ (Fin 3)) : trace (blochMatrix 1 r) = 1 := by
    simp [blochMatrix, Matrix.trace, Fin.sum_univ_two]
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
    simp [blochMatrix, Matrix.trace, Fin.sum_univ_two,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]
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
      simp [blochMatrix, bloch, h00, h11, h10r, h10i] <;> linarith
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
    simp [signalProbe, probeTarget, Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_succ]
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
  refine ⟨probes, c, v, b, hv, lower, b_le, b_lt, ?_, ?_, projected,
    affine_output, chord, ?_, fun u => trace_bloch (c + u • v), strict_inside,
    plus_norm, minus_norm, pure _ plus_norm, pure _ minus_norm, ?_, overlap_bound, ?_⟩
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

#print axioms actual_two_probe_chord_obstruction

end D5.S3.Quantum.Information.ActualQubitChordObstruction
