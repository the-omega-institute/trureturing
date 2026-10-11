/- GID: D5/S3/Quantum/Matrix/NumericalRange
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/NumericalRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel-line lifting and two-vector compression prove numerical-range convexity. -/

/-
admission_basis: escape-witness
proof_shape: sphere_image_eq_ball_image: content; escape_witness: sphere_image_eq_ball_image
proof_shape: convex_sphere_image: content; escape_witness: sphere_image_eq_ball_image
proof_shape: bloch_map_has_kernel: bind-only; consumer: convex_bloch_sphere_image; escape_witness: none
proof_shape: convex_bloch_sphere_image: content; escape_witness: sphere_image_eq_ball_image
proof_shape: blochPure_norm: bind-only; consumer: qubit_numericalRange_eq_bloch_image; escape_witness: none
proof_shape: blochPure_surjective: content; escape_witness: blochPure_surjective
proof_shape: bloch_expectation: bind-only; consumer: qubit_numericalRange_eq_bloch_image; escape_witness: none
proof_shape: qubit_numericalRange_eq_bloch_image: content; escape_witness: blochPure_surjective
proof_shape: qubit_numericalRange_convex: content; escape_witness: sphere_image_eq_ball_image, blochPure_surjective
proof_shape: compression_inner: bind-only; consumer: compression_numericalRange_subset, finite_numericalRange_convex, subspace_numericalRange_convex; escape_witness: none
proof_shape: compression_numericalRange_subset: bind-only; consumer: finite_numericalRange_convex; escape_witness: none
proof_shape: one_dimensional_numericalRange: bind-only; consumer: small_matrix_numericalRange_convex; escape_witness: none
proof_shape: small_matrix_numericalRange_convex: content; escape_witness: sphere_image_eq_ball_image, blochPure_surjective
proof_shape: small_operator_numericalRange_convex: content; escape_witness: sphere_image_eq_ball_image, blochPure_surjective
proof_shape: finite_numericalRange_convex: content; escape_witness: sphere_image_eq_ball_image, blochPure_surjective
proof_shape: toeplitz_hausdorff: content; escape_witness: sphere_image_eq_ball_image, blochPure_surjective
proof_shape: subspace_numericalRange_convex: content; escape_witness: sphere_image_eq_ball_image, blochPure_surjective
escape_witness: sphere_image_eq_ball_image / finite_numericalRange_convex
Direct frozen dependencies:
  owner GID: D5/S3/Quantum/Information/ActualPureQubitGeometry; declaration: D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch
    declaration statement_id: sha256:cc88c714292e1a1b7f96163a344340fa2144c8b2caffc5cb2196fb9df44fd3e5
  Other lane imports are same-delivery prerequisites, not baseline-frozen dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Information.ActualPureQubitGeometry

noncomputable section
open Matrix Set Unitary
open scoped ComplexInnerProductSpace ComplexOrder
namespace D5.S3.Quantum.Matrix.NumericalRange
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def innerNumericalRange (A : E →L[ℂ] E) : Set ℂ :=
  {z | ∃ v : E, ‖v‖ = 1 ∧ z = inner ℂ v (A v)}

theorem sphere_image_eq_ball_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (k : E) (hk : k ≠ 0) (hLk : L k = 0) :
    L '' Metric.sphere (0 : E) 1 = L '' Metric.closedBall (0 : E) 1 := by
  apply Set.Subset.antisymm
  · exact Set.image_mono Metric.sphere_subset_closedBall
  · rintro y ⟨x, hx, rfl⟩
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hkp : 0 < ‖k‖ := norm_pos_iff.mpr hk
    let T : ℝ := (1 + ‖x‖) / ‖k‖
    have hT : 0 ≤ T := div_nonneg (by positivity) (le_of_lt hkp)
    have hTk : T * ‖k‖ = 1 + ‖x‖ := div_mul_cancel₀ _ (ne_of_gt hkp)
    have hbound : 1 ≤ ‖x + T • k‖ := by
      have htri := norm_le_add_norm_add (T • k) x
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT, hTk] at htri
      simpa [add_comm] using (show 1 ≤ ‖T • k + x‖ by linarith)
    have hc : Continuous (fun t : ℝ => ‖x + t • k‖) := by fun_prop
    obtain ⟨t, ht, hn⟩ := intermediate_value_Icc hT hc.continuousOn ⟨by simpa, hbound⟩
    refine ⟨x + t • k, ?_, ?_⟩
    · simpa using hn
    · simp [hLk]

private theorem convex_sphere_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (k : E) (hk : k ≠ 0) (hLk : L k = 0) :
    Convex ℝ (L '' Metric.sphere (0 : E) 1) := by
  rw [sphere_image_eq_ball_image L k hk hLk]
  exact (convex_closedBall (0 : E) 1).linear_image L

private theorem bloch_map_has_kernel (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ) :
    ∃ k, k ≠ 0 ∧ L k = 0 := by
  have hni : ¬ Function.Injective L := by
    intro hi
    have hdim := LinearMap.finrank_le_finrank_of_injective hi
    norm_num [Complex.finrank_real_complex] at hdim
  change ¬ (∀ x y, L x = L y → x = y) at hni
  push Not at hni
  obtain ⟨x, y, hxy, hne⟩ := hni
  refine ⟨x-y, sub_ne_zero.mpr hne, ?_⟩
  simp [map_sub, hxy]

private theorem convex_bloch_sphere_image (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ) :
    Convex ℝ (L '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  obtain ⟨k,hk,hLk⟩ := bloch_map_has_kernel L
  exact convex_sphere_image L k hk hLk

private theorem blochPure_norm (v : (EuclideanSpace ℂ (Fin 2))) (hv : ‖v‖ = 1) : ‖(fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v‖ = 1 := by
  have hsq : ‖(fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v‖^2 = (‖v‖^2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.norm_sq_eq]
    simp [bloch,Matrix.vecMulVec,Fin.sum_univ_succ,Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [hv] at hsq
  nlinarith [norm_nonneg ((fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v)]

private theorem blochPure_surjective (r : (EuclideanSpace ℝ (Fin 3))) (hr : ‖r‖ = 1) :
    ∃ v : (EuclideanSpace ℂ (Fin 2)), ‖v‖ = 1 ∧ (fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v = r := by
  have hrsq : (r 0)^2 + (r 1)^2 + (r 2)^2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq r
    rw [hr] at h
    simpa [Fin.sum_univ_three] using h.symm
  have hlow : -1 ≤ r 2 := by nlinarith [sq_nonneg (r 0),sq_nonneg (r 1)]
  by_cases hz : r 2 = -1
  · have hx : r 0 = 0 := by nlinarith [sq_nonneg (r 1)]
    have hy : r 1 = 0 := by nlinarith [sq_nonneg (r 0)]
    refine ⟨WithLp.toLp 2 ![0,1], ?_, ?_⟩
    · simp [EuclideanSpace.norm_eq,Fin.sum_univ_two]
    · ext i; fin_cases i <;> simp [bloch,Matrix.vecMulVec,hx,hy,hz]
  · let p : ℝ := Real.sqrt ((1+r 2)/2)
    have hlt : -1 < r 2 := lt_of_le_of_ne hlow (Ne.symm hz)
    have hp0 : 0 < p := Real.sqrt_pos.2 (by linarith)
    have hp : p^2 = (1+r 2)/2 := Real.sq_sqrt (by linarith)
    have hpne : p ≠ 0 := ne_of_gt hp0
    let v : (EuclideanSpace ℂ (Fin 2)) := WithLp.toLp 2 ![(p : ℂ),
      (⟨r 0/(2*p),r 1/(2*p)⟩ : ℂ)]
    have hq : (r 0/(2*p))^2+(r 1/(2*p))^2 = (1-r 2)/2 := by
      field_simp [hpne]
      nlinarith [hp]
    refine ⟨v, ?_, ?_⟩
    · have hv : ‖v‖^2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [v,Fin.sum_univ_two,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
        nlinarith [hp,hq]
      nlinarith [norm_nonneg v]
    · ext i; fin_cases i <;>
        simp [bloch,Matrix.vecMulVec,v,Complex.mul_re,Complex.mul_im]
      · field_simp [hpne]
      · field_simp [hpne]
      · nlinarith [hp,hq]

private def blochReadout (A : (Matrix (Fin 2) (Fin 2) ℂ)) : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] ℂ :=
  let coord := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
  ((A 0 0-A 1 1)/2) •
      (Complex.ofRealLI.toLinearMap.comp ((LinearMap.proj 2).comp coord)) +
    ((A 0 1+A 1 0)/2) •
      (Complex.ofRealLI.toLinearMap.comp ((LinearMap.proj 0).comp coord)) +
    (Complex.I*(A 0 1-A 1 0)/2) •
      (Complex.ofRealLI.toLinearMap.comp ((LinearMap.proj 1).comp coord))

private def blochCenter (A : (Matrix (Fin 2) (Fin 2) ℂ)) : ℂ := Matrix.trace A / 2

private theorem bloch_expectation (A : (Matrix (Fin 2) (Fin 2) ℂ)) (v : (EuclideanSpace ℂ (Fin 2))) (hv : ‖v‖ = 1) :
    inner ℂ v (Matrix.toEuclideanLin A v) = blochCenter A + blochReadout A ((fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v) := by
  have hid : dotProduct (star v.ofLp) (A *ᵥ v.ofLp) =
      blochCenter A * ((‖v‖^2 : ℝ) : ℂ) + blochReadout A ((fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v) := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Complex.ext <;>
      simp [blochCenter,Matrix.trace,Matrix.diag,blochReadout,bloch,Matrix.vecMulVec,dotProduct,
        Matrix.mulVec,Fin.sum_univ_two,Complex.sq_norm,Complex.normSq_apply] <;> ring
  simpa [hv,Matrix.toEuclideanLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm] using hid

private theorem qubit_numericalRange_eq_bloch_image (A : (Matrix (Fin 2) (Fin 2) ℂ)) :
    (innerNumericalRange (Matrix.toEuclideanLin A).toContinuousLinearMap) = (fun z => blochCenter A + z) ''
      (blochReadout A '' Metric.sphere (0 : (EuclideanSpace ℝ (Fin 3))) 1) := by
  ext z
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨blochReadout A ((fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v), ?_, ?_⟩
    · exact ⟨(fun (v : EuclideanSpace ℂ (Fin 2)) => bloch (Matrix.vecMulVec v.ofLp (star v.ofLp))) v,by simpa using blochPure_norm v hv,rfl⟩
    · exact (bloch_expectation A v hv).symm
  · rintro ⟨w,⟨r,hr,rfl⟩,rfl⟩
    have hr' : ‖r‖ = 1 := by simpa using hr
    obtain ⟨v,hv,hvr⟩ := blochPure_surjective r hr'
    refine ⟨v,hv,?_⟩
    change blochCenter A + blochReadout A r = inner ℂ v (Matrix.toEuclideanLin A v)
    rw [bloch_expectation A v hv,hvr]

private theorem qubit_numericalRange_convex (A : (Matrix (Fin 2) (Fin 2) ℂ)) : Convex ℝ ((innerNumericalRange (Matrix.toEuclideanLin A).toContinuousLinearMap)) := by
  rw [qubit_numericalRange_eq_bloch_image]
  exact (convex_bloch_sphere_image (blochReadout A)).translate (blochCenter A)



private def compressionOp {k : ℕ} (A : E →L[ℂ] E)
    (i : EuclideanSpace ℂ (Fin k) →ₗᵢ[ℂ] E) :
    EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
  i.toContinuousLinearMap.adjoint ∘L A ∘L i.toContinuousLinearMap

private theorem compression_inner {k : ℕ} (A : E →L[ℂ] E)
    (i : EuclideanSpace ℂ (Fin k) →ₗᵢ[ℂ] E) (v : EuclideanSpace ℂ (Fin k)) :
    inner ℂ v (compressionOp A i v) = inner ℂ (i v) (A (i v)) := by
  simp [compressionOp,ContinuousLinearMap.adjoint_inner_right]

private theorem compression_numericalRange_subset {k : ℕ} (A : E →L[ℂ] E)
    (i : EuclideanSpace ℂ (Fin k) →ₗᵢ[ℂ] E) :
    innerNumericalRange (compressionOp A i) ⊆ innerNumericalRange A := by
  rintro z ⟨v,hv,rfl⟩
  exact ⟨i v,by simpa using hv,(compression_inner A i v)⟩

private theorem one_dimensional_numericalRange (A : (Matrix (Fin 1) (Fin 1) ℂ)) :
    (innerNumericalRange (Matrix.toEuclideanLin A).toContinuousLinearMap) = {A 0 0} := by
  ext z
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hnorm : Complex.normSq (v 0) = 1 := by
      have h := EuclideanSpace.norm_sq_eq v
      simpa [hv,←Complex.normSq_eq_norm_sq] using h.symm
    simp only [mem_singleton_iff]
    simp [Matrix.toEuclideanLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    have hstar : star (v 0) * v 0 = 1 := by
      have h := Complex.normSq_eq_conj_mul_self (z := v 0)
      rw [hnorm] at h
      simpa only [starRingEnd_apply,Complex.ofReal_one] using h.symm
    calc
      A 0 0 * v 0 * star (v 0) = A 0 0 * (star (v 0) * v 0) := by ring
      _ = A 0 0 := by rw [hstar,mul_one]
  · rintro rfl
    refine ⟨WithLp.toLp 2 (fun _ => 1), ?_, ?_⟩
    · simp [EuclideanSpace.norm_eq,Fin.sum_univ_succ]
    · simp [Matrix.toEuclideanLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

private theorem small_matrix_numericalRange_convex {n : ℕ} (hn : n ≤ 2) (A : (Matrix (Fin n) (Fin n) ℂ)) :
    Convex ℝ ((innerNumericalRange (Matrix.toEuclideanLin A).toContinuousLinearMap)) := by
  interval_cases n
  · have he : (innerNumericalRange (Matrix.toEuclideanLin A).toContinuousLinearMap) = ∅ := by
      ext z
      simp only [mem_empty_iff_false,iff_false]
      rintro ⟨v,hv,_⟩
      have hv0 : ‖v‖ = 0 := by simp [EuclideanSpace.norm_eq]
      linarith
    rw [he]
    exact convex_empty
  · rw [one_dimensional_numericalRange]
    exact convex_singleton _
  · exact qubit_numericalRange_convex A

private theorem small_operator_numericalRange_convex {n : ℕ} (hn : n ≤ 2)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    Convex ℝ (innerNumericalRange A) := by
  let M : (Matrix (Fin n) (Fin n) ℂ) := Matrix.toEuclideanLin.symm A.toLinearMap
  have hM : (Matrix.toEuclideanLin M).toContinuousLinearMap = A := by
    apply ContinuousLinearMap.coe_injective
    simp [M]
  rw [← hM]
  exact small_matrix_numericalRange_convex hn M

theorem finite_numericalRange_convex (A : E →L[ℂ] E) :
    Convex ℝ (innerNumericalRange A) := by
  classical
  rintro z ⟨v,hv,rfl⟩ w ⟨u,hu,rfl⟩ a b ha hb hab
  let K : Submodule ℂ E := Submodule.span ℂ ({v,u} : Set E)
  have hvK : v ∈ K := Submodule.subset_span (by simp)
  have huK : u ∈ K := Submodule.subset_span (by simp)
  let d := Module.finrank ℂ K
  have hd : d ≤ 2 := by
    have h := finrank_span_le_card (R := ℂ) ({v,u} : Set E)
    dsimp [d,K]
    exact h.trans (by
      rw [← Set.ncard_eq_toFinset_card']
      exact (Set.ncard_insert_le _ _).trans (by simp))
  let basis := stdOrthonormalBasis ℂ K
  let i : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] E :=
    K.subtypeₗᵢ.comp basis.repr.symm.toLinearIsometry
  let v' : EuclideanSpace ℂ (Fin d) := basis.repr ⟨v,hvK⟩
  let u' : EuclideanSpace ℂ (Fin d) := basis.repr ⟨u,huK⟩
  have hiv : i v' = v := by simp [i,v']
  have hiu : i u' = u := by simp [i,u']
  have hv' : ‖v'‖ = 1 := by simpa [v'] using hv
  have hu' : ‖u'‖ = 1 := by simpa [u'] using hu
  have hvr : inner ℂ v (A v) ∈ innerNumericalRange (compressionOp A i) := by
    refine ⟨v',hv',?_⟩
    rw [compression_inner,hiv]
  have hur : inner ℂ u (A u) ∈ innerNumericalRange (compressionOp A i) := by
    refine ⟨u',hu',?_⟩
    rw [compression_inner,hiu]
  have hcombo := small_operator_numericalRange_convex hd (compressionOp A i) hvr hur ha hb hab
  exact compression_numericalRange_subset A i hcombo

private theorem toeplitz_hausdorff : (∀ n (A : (Matrix (Fin n) (Fin n) ℂ)), Convex ℝ ((innerNumericalRange (Matrix.toEuclideanLin A).toContinuousLinearMap))) := by
  intro n A

  exact finite_numericalRange_convex _

def subspaceNumericalRange {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ))
    (K : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : Set ℂ :=
  {z | ∃ v : K, ‖v‖ = 1 ∧ z = inner ℂ (v : EuclideanSpace ℂ (Fin n))
    (Matrix.toEuclideanLin A (v : EuclideanSpace ℂ (Fin n)))}

theorem subspace_numericalRange_convex {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ))
    (K : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : Convex ℝ (subspaceNumericalRange A K) := by
  let basis := stdOrthonormalBasis ℂ K
  let d := Module.finrank ℂ K
  let i : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) :=
    K.subtypeₗᵢ.comp basis.repr.symm.toLinearIsometry
  let T := compressionOp (Matrix.toEuclideanLin A).toContinuousLinearMap i
  let M : (Matrix (Fin d) (Fin d) ℂ) := Matrix.toEuclideanLin.symm T.toLinearMap
  have hMat : (Matrix.toEuclideanLin M).toContinuousLinearMap = T := by
    apply ContinuousLinearMap.coe_injective
    simp [M]
  have hc : Convex ℝ (innerNumericalRange T) := by
    rw [←hMat]
    exact toeplitz_hausdorff d M
  have he : subspaceNumericalRange A K = innerNumericalRange T := by
    ext z
    constructor
    · rintro ⟨v,hv,hz⟩
      refine ⟨basis.repr v,by simpa using hv,?_⟩
      rw [compression_inner]
      have hiv : i (basis.repr v) = (v : EuclideanSpace ℂ (Fin n)) := by simp [i]
      rw [hiv]
      exact hz
    · rintro ⟨w,hw,hz⟩
      refine ⟨basis.repr.symm w,by simpa using hw,?_⟩
      rw [compression_inner] at hz
      exact hz
  rw [he]
  exact hc

#print axioms sphere_image_eq_ball_image
#print axioms finite_numericalRange_convex
#print axioms subspace_numericalRange_convex

end D5.S3.Quantum.Matrix.NumericalRange
