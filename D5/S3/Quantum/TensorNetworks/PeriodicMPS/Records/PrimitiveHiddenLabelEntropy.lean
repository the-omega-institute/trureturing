/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryRecordRate]
   utility: none
   digest: The Umegaki information lost by a two-site observer. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryRecordRate
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Algebra.GramUnitaryExtension
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Resource.LogDet.PathSpectralClassical
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! The fair ensemble of the primitive periodic MPS collision, using the literal
two-site partial trace and the repository's support-aware Umegaki entropy. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PrimitiveHiddenLabelEntropy

open Matrix Polynomial Filter
open scoped Matrix MatrixOrder ComplexOrder CStarAlgebra Topology InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Information.PartialTraceMutualInformation (marginalRight partialTraceRight partialTraceRight_add)
open D5.S3.Resource.LogDet.PathSpectralClassical (trace_cfc_eq_sum)

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary matrix of a canonical density state. -/
def matrix (P : DensityState ι) : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm P.1

private theorem matrix_posSemidef (P : DensityState ι) : (matrix P).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm P.2.1)

private def ray (u : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec u (star u)

/-- A normalized amplitude vector determines a pure density state. -/
def pureDensity (u : ι → ℂ) (hu : u ⬝ᵥ star u = 1) : DensityState ι :=
  ⟨CStarMatrix.ofMatrix (ray u),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_vecMulVec_self_star u)),
    (Matrix.trace_vecMulVec u (star u)).trans hu⟩

/-- The equal mixture of two density states. -/
def fairMixture (P Q : DensityState ι) : DensityState ι :=
  ⟨(1 / 2 : ℝ) • (P.1 + Q.1),
    smul_nonneg (by norm_num) (add_nonneg P.2.1 Q.2.1), by
      change Matrix.trace ((1 / 2 : ℝ) • (matrix P + matrix Q)) = 1
      rw [Matrix.trace_smul, Matrix.trace_add, show (matrix P).trace = 1 from P.2.2,
        show (matrix Q).trace = 1 from Q.2.2]
      norm_num [Complex.real_smul]⟩

private def columns (u v : ι → ℂ) : Matrix ι (Fin 2) ℂ :=
  fun i k => ![u i, v i] k

omit [DecidableEq ι] in
private theorem columns_gram (u v : ι → ℂ)
    (hu : u ⬝ᵥ star u = 1) (hv : v ⬝ᵥ star v = 1) :
    (columns u v)ᴴ * columns u v =
      !![1, star (u ⬝ᵥ star v); u ⬝ᵥ star v, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change star u ⬝ᵥ u = 1
    rwa [dotProduct_comm]
  · change star u ⬝ᵥ v = star (u ⬝ᵥ star v)
    rw [dotProduct_comm, dotProduct_star v u]
  · change star v ⬝ᵥ u = u ⬝ᵥ star v
    exact dotProduct_comm _ _
  · change star v ⬝ᵥ v = 1
    rwa [dotProduct_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem columns_outer (u v : ι → ℂ) :
    columns u v * (columns u v)ᴴ = ray u + ray v := by
  ext i j
  simp [columns, ray, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply]

private theorem half_gram_charpoly (s : ℂ) :
    (((1 / 2 : ℝ) • (!![1, star s; s, 1] : Matrix (Fin 2) (Fin 2) ℂ))).charpoly =
      (X - C (((1 + ‖s‖) / 2 : ℝ) : ℂ)) * (X - C (((1 - ‖s‖) / 2 : ℝ) : ℂ)) := by
  have hs : star s * s = (‖s‖ : ℂ) ^ 2 := by
    exact RCLike.conj_mul s
  have hp := congrArg (C : ℂ →+* ℂ[X]) hs
  simp only [map_mul, map_pow] at hp
  simp [Matrix.charpoly_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, Complex.real_smul,
    map_mul, map_sub, map_add, div_eq_mul_inv]
  change C ((starRingEnd ℂ) s) * C s = _ at hp
  linear_combination -(C (2⁻¹ : ℂ)) ^ 2 * hp

/-- The nonzero spectral multiset of the fair mixture, with algebraic multiplicity,
including the coincident roots and the proportional-vector endpoint. -/
theorem fairMixture_nonzero_spectrum (u v : ι → ℂ)
    (hu : u ⬝ᵥ star u = 1) (hv : v ⬝ᵥ star v = 1) :
    ((matrix (fairMixture (pureDensity u hu) (pureDensity v hv))).charpoly.roots.filter (· ≠ 0)) =
      ({(((1 + ‖u ⬝ᵥ star v‖) / 2 : ℝ) : ℂ),
        (((1 - ‖u ⬝ᵥ star v‖) / 2 : ℝ) : ℂ)} : Multiset ℂ).filter (· ≠ 0) := by
  classical
  let A := columns u v
  let B := (1 / 2 : ℝ) • Aᴴ
  have hm : A * B = matrix (fairMixture (pureDensity u hu) (pureDensity v hv)) := by
    change A * ((1 / 2 : ℝ) • Aᴴ) = (1 / 2 : ℝ) • (ray u + ray v)
    rw [Matrix.mul_smul, columns_outer]
  have hg : (B * A).charpoly =
      (X - C (((1 + ‖u ⬝ᵥ star v‖) / 2 : ℝ) : ℂ)) *
        (X - C (((1 - ‖u ⬝ᵥ star v‖) / 2 : ℝ) : ℂ)) := by
    change (((1 / 2 : ℝ) • Aᴴ) * A).charpoly = _
    rw [Matrix.smul_mul, columns_gram u v hu hv, half_gram_charpoly]
  have hroots : (B * A).charpoly.roots =
      ({(((1 + ‖u ⬝ᵥ star v‖) / 2 : ℝ) : ℂ),
        (((1 - ‖u ⬝ᵥ star v‖) / 2 : ℝ) : ℂ)} : Multiset ℂ) := by
    rw [hg, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C]
    rfl
  have h := congrArg (fun p : ℂ[X] => p.roots.filter (· ≠ 0)) (A.charpoly_mul_comm' B)
  change (_ : Multiset ℂ) = _ at h
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (Matrix.charpoly_monic _).ne_zero)] at h
  have hx (k : ℕ) : ((X ^ k : ℂ[X]).roots.filter (· ≠ 0)) = 0 := by
    simp [Multiset.filter_nsmul, Multiset.filter_singleton]
  simpa only [Multiset.filter_add, hx, zero_add, hm, hroots] using h

/-- The repository von Neumann entropy, on the definitionally equal density carrier. -/
abbrev entropy (P : DensityState ι) : ℝ :=
  D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy P

private theorem log_matrix (P : DensityState ι) :
    CStarMatrix.ofMatrix (cfc Real.log (matrix P)) = CFC.log P.1 :=
  StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log (matrix P)
    ((matrix P).finite_real_spectrum.continuousOn _)
    CStarMatrix.ofMatrixL.continuous (matrix_posSemidef P).isHermitian
    (IsSelfAdjoint.of_nonneg P.2.1)

private theorem entropy_eq_raw (P : DensityState ι) :
    entropy P = -((matrix P * cfc Real.log (matrix P)).trace.re) := by
  change -(Matrix.trace (P.1 * CFC.log P.1)).re = _
  rw [← log_matrix]
  rfl

private theorem entropy_eq_roots (P : DensityState ι) :
    entropy P = ((matrix P).charpoly.roots.map (fun z => Real.negMulLog z.re)).sum := by
  let A := matrix P
  have hA : A.IsHermitian := (matrix_posSemidef P).isHermitian
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA
  rw [entropy_eq_raw]
  change -(A * cfc Real.log A).trace.re =
    (A.charpoly.roots.map (fun z => Real.negMulLog z.re)).sum
  calc
    _ = -(cfc (fun x : ℝ => x) A * cfc Real.log A).trace.re := by rw [hid]
    _ = -(cfc (fun x : ℝ => x * Real.log x) A).trace.re := by
      rw [cfc_mul (fun x : ℝ => x) Real.log A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by
      rw [trace_cfc_eq_sum A hA, hA.roots_charpoly_eq_eigenvalues]
      simp [Real.negMulLog, Finset.sum_neg_distrib]

private theorem sum_nonzero_roots (roots : Multiset ℂ) :
    ((roots.filter (· ≠ 0)).map (fun z => Real.negMulLog z.re)).sum =
      (roots.map (fun z => Real.negMulLog z.re)).sum := by
  classical
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons a roots ih =>
    by_cases h : a = 0 <;> simp [h, ih]

private theorem entropy_eq_nonzero_roots (P : DensityState ι) :
    entropy P = (((matrix P).charpoly.roots.filter (· ≠ 0)).map (fun z => Real.negMulLog z.re)).sum := by
  rw [sum_nonzero_roots, entropy_eq_roots]

/-- The fair ensemble has exactly the binary entropy of its larger spectral weight. -/
theorem fairMixture_entropy (u v : ι → ℂ) (hu : u ⬝ᵥ star u = 1) (hv : v ⬝ᵥ star v = 1) :
    entropy (fairMixture (pureDensity u hu) (pureDensity v hv)) =
      Real.binEntropy ((1 + ‖u ⬝ᵥ star v‖) / 2) := by
  classical
  let p : ℝ := (1 + ‖u ⬝ᵥ star v‖) / 2
  let q : ℝ := (1 - ‖u ⬝ᵥ star v‖) / 2
  have hq : 1 - p = q := by dsimp [p, q]; ring
  rw [entropy_eq_nonzero_roots, fairMixture_nonzero_spectrum, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  change ((({(p : ℂ), (q : ℂ)} : Multiset ℂ).filter (· ≠ 0)).map
    (fun z => Real.negMulLog z.re)).sum = Real.negMulLog p + Real.negMulLog (1 - p)
  rw [hq]
  rw [sum_nonzero_roots]
  simp

private theorem null_of_add_left (P Q : DensityState ι) {x : ι → ℂ}
    (hx : (matrix P + matrix Q) *ᵥ x = 0) : matrix P *ᵥ x = 0 := by
  let p := star x ⬝ᵥ (matrix P *ᵥ x)
  let q := star x ⬝ᵥ (matrix Q *ᵥ x)
  have hp := Complex.nonneg_iff.mp ((matrix_posSemidef P).dotProduct_mulVec_nonneg x)
  have hq := Complex.nonneg_iff.mp ((matrix_posSemidef Q).dotProduct_mulVec_nonneg x)
  have hsum : p + q = 0 := by
    have h := congrArg (fun y : ι → ℂ => star x ⬝ᵥ y) hx
    rw [Matrix.add_mulVec, dotProduct_add, dotProduct_zero] at h
    exact h
  have hre : p.re + q.re = 0 := by
    simpa only [Complex.add_re, Complex.zero_re] using congrArg Complex.re hsum
  have hp₀ : p.re = 0 := le_antisymm (by linarith [hq.1]) hp.1
  apply (matrix_posSemidef P).dotProduct_mulVec_zero_iff.mp
  exact Complex.ext hp₀ (by simpa only [Complex.zero_im] using hp.2.symm)

/-- Each summand is supported in the fair mixture, even when it is singular. -/
theorem fairMixture_support (P Q : DensityState ι) :
    SupportContained P (fairMixture P Q) ∧ SupportContained Q (fairMixture P Q) := by
  constructor
  · intro x hx
    change ((1 / 2 : ℝ) • (matrix P + matrix Q)) *ᵥ x = 0 at hx
    rw [Matrix.smul_mulVec] at hx
    exact null_of_add_left P Q ((smul_eq_zero.mp hx).resolve_left (by norm_num))
  · intro x hx
    change ((1 / 2 : ℝ) • (matrix P + matrix Q)) *ᵥ x = 0 at hx
    rw [Matrix.smul_mulVec, add_comm (matrix P)] at hx
    exact null_of_add_left Q P ((smul_eq_zero.mp hx).resolve_left (by norm_num))

omit [DecidableEq ι] in
private theorem ray_idempotent (u : ι → ℂ) (hu : u ⬝ᵥ star u = 1) :
    IsIdempotentElem (ray u) := by
  change Matrix.vecMulVec u (star u) * Matrix.vecMulVec u (star u) = _
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm (star u), hu, one_smul]
  rfl

private theorem pure_log_zero (u : ι → ℂ) (hu : u ⬝ᵥ star u = 1) :
    cfc Real.log (matrix (pureDensity u hu)) = 0 := by
  change cfc Real.log (ray u) = 0
  calc
    _ = cfc (fun _ : ℝ => 0) (ray u) := by
      apply cfc_congr
      intro x hx
      have h := (ray_idempotent u hu).spectrum_subset ℝ hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> simp
    _ = 0 := by simp

omit [Fintype ι] [DecidableEq ι] in
private theorem ray_phase (u : ι → ℂ) {c : ℂ} (hc : c * star c = 1) :
    ray (c • u) = ray u := by
  ext i j
  change (c * u i) * star (c * u j) = _
  rw [star_mul]
  calc
    _ = (c * star c) * (u i * star (u j)) := by ring
    _ = _ := by rw [hc, one_mul]; rfl

omit [DecidableEq ι] in
private theorem ray_conjugate (U : Matrix ι ι ℂ) (u : ι → ℂ) :
    U * ray u * Uᴴ = ray (U *ᵥ u) := by
  simp only [ray, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- A unitary on the common ambient space exchanges the two rank-one states. -/
private theorem exists_ray_swap (u v : ι → ℂ)
    (hu : u ⬝ᵥ star u = 1) (hv : v ⬝ᵥ star v = 1) :
    ∃ U : Matrix.unitaryGroup ι ℂ,
      U.val * ray u * U.valᴴ = ray v ∧ U.val * ray v * U.valᴴ = ray u := by
  let s := u ⬝ᵥ star v
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℂ, c * star c = 1 ∧ c * s = star s := by
    by_cases hs : s = 0
    · exact ⟨1, by simp, by simp [hs]⟩
    · refine ⟨star s / s, ?_, div_mul_cancel₀ _ hs⟩
      have hs' : star s ≠ 0 := by simpa using hs
      change star s / s * (starRingEnd ℂ) (star s / s) = 1
      rw [map_div₀]
      change star s / s * (star (star s) / star s) = 1
      rw [star_star, div_mul_div_comm, mul_comm s (star s)]
      exact div_self (mul_ne_zero hs' hs)
  have hcu : (c • u) ⬝ᵥ star (c • u) = 1 := by
    rw [star_smul, smul_dotProduct, dotProduct_smul]
    rw [hu, smul_smul]
    change (c * star c) • (1 : ℂ) = 1
    rw [hc, one_smul]
  have hcross : (c • u) ⬝ᵥ star v = star s := by
    rw [smul_dotProduct]
    exact hcs
  have hcross' : v ⬝ᵥ star (c • u) = s := by
    rw [dotProduct_star v (c • u), hcross, star_star]
  have hg : (columns v (c • u))ᴴ * columns v (c • u) = (columns u v)ᴴ * columns u v := by
    rw [columns_gram _ _ hv hcu, columns_gram u v hu hv, hcross']
  obtain ⟨U, hU⟩ :=
    D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
      (columns v (c • u)) (columns u v) hg
  have hUu : U.val *ᵥ u = v := (congrArg (fun A : Matrix ι (Fin 2) ℂ => A.col 0) hU).symm
  have hUv : U.val *ᵥ v = c • u := (congrArg (fun A : Matrix ι (Fin 2) ℂ => A.col 1) hU).symm
  refine ⟨U, ?_, ?_⟩
  · rw [ray_conjugate, hUu]
  · rw [ray_conjugate, hUv, ray_phase u hc]

private theorem relativeEntropy_eq_raw (P Q : DensityState ι) :
    finiteTraceLogRelativeEntropy P Q =
      (matrix P * (cfc Real.log (matrix P) - cfc Real.log (matrix Q))).trace.re := by
  unfold finiteTraceLogRelativeEntropy
  rw [← log_matrix P, ← log_matrix Q]
  rfl

/-- Each pure label has the same finite relative entropy to the fair mixture. -/
theorem fairMixture_relativeEntropy (u v : ι → ℂ)
    (hu : u ⬝ᵥ star u = 1) (hv : v ⬝ᵥ star v = 1) :
    let P := pureDensity u hu
    let Q := pureDensity v hv
    let M := fairMixture P Q
    extendedQuantumRelativeEntropy P M = (entropy M : WithTop ℝ) ∧
      extendedQuantumRelativeEntropy Q M = (entropy M : WithTop ℝ) := by
  dsimp only
  let P := pureDensity u hu
  let Q := pureDensity v hv
  let M := fairMixture P Q
  change extendedQuantumRelativeEntropy P M = (entropy M : WithTop ℝ) ∧
    extendedQuantumRelativeEntropy Q M = (entropy M : WithTop ℝ)
  have hm : matrix M = (1 / 2 : ℝ) • (ray u + ray v) := rfl
  obtain ⟨U, huU, hvU⟩ := exists_ray_swap u v hu hv
  have huunit : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  have hM : U.val * matrix M * U.valᴴ = matrix M := by
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, huU, hvU, add_comm]
  let L := cfc Real.log (matrix M)
  have hL : U.val * L * U.valᴴ = L := by
    have h := Matrix.cfc_conj_unitary (A := matrix M) Real.log U
    change cfc Real.log (U.val * matrix M * U.valᴴ) = U.val * L * U.valᴴ at h
    rwa [hM, eq_comm] at h
  have hcross : (ray v * L).trace = (ray u * L).trace := by
    calc
      _ = ((U.val * ray u * U.valᴴ) * (U.val * L * U.valᴴ)).trace := by rw [huU, hL]
      _ = (U.val * (ray u * L) * U.valᴴ).trace := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U.valᴴ U.val, huunit, Matrix.one_mul]
      _ = _ := by rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, huunit, Matrix.one_mul]
  have hent : entropy M = - (ray u * L).trace.re := by
    rw [entropy_eq_raw]
    change - (matrix M * L).trace.re = _
    rw [hm, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, hcross,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re]
    ring
  have hs := fairMixture_support P Q
  constructor
  · rw [extendedQuantumRelativeEntropy_eq_coe_of_support hs.1, relativeEntropy_eq_raw,
      pure_log_zero u hu, zero_sub, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, hent]
    rfl
  · rw [extendedQuantumRelativeEntropy_eq_coe_of_support hs.2, relativeEntropy_eq_raw,
      pure_log_zero v hv, zero_sub, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, hent]
    change ((- (ray v * L).trace.re : ℝ) : WithTop ℝ) = _
    rw [hcross]

open PeriodicMPSPrimitiveCollision
open ComplementaryRecordRate (collisionFlattening collisionFlattening_common_visible collisionFlattening_overlap)
open PeriodicMPSParentIntersection (Word)
open PeriodicMPSProjectiveCoordinates (mass)
open UniformMPSExpectedDimensionRefutation (traceWord)

abbrev Visible := Fin 2 × Fin 2

/-- The normalized periodic trace amplitude with its first two sites separated. -/
def collisionAmplitude (b : Bool) (m : ℕ) : Visible × Word m → ℂ :=
  fun x => collisionFlattening b m x.1 x.2

private theorem collisionAmplitude_overlap (m : ℕ) :
    collisionAmplitude false m ⬝ᵥ star (collisionAmplitude true m) =
      collisionNormalizedOverlap (2 + m) := by
  rw [← collisionFlattening_overlap]
  simp [dotProduct, Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply, collisionAmplitude]

private theorem collisionAmplitude_unit (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    collisionAmplitude b m ⬝ᵥ star (collisionAmplitude b m) = 1 := by
  have h := congrArg Matrix.trace (collisionFlattening_common_visible b m hm)
  rw [(primitive_two_site_collision (2 + m) (by omega)).2.2.2.2.1] at h
  simpa [dotProduct, Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply, collisionAmplitude] using h

omit [DecidableEq ι] in
private theorem overlap_norm_lt_one (u v : ι → ℂ)
    (hu : u ⬝ᵥ star u = 1) (hv : v ⬝ᵥ star v = 1) (hne : ∀ c : ℂ, v ≠ c • u) :
    ‖u ⬝ᵥ star v‖ < 1 := by
  let U : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  let V : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hnorm (x : EuclideanSpace ℂ ι) (hx : ⟪x, x⟫_ℂ = 1) : ‖x‖ = 1 := by
    have hs : ‖x‖ ^ 2 = 1 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), hx]
      rfl
    nlinarith [norm_nonneg x, hs]
  have hU : ‖U‖ = 1 := hnorm U hu
  have hV : ‖V‖ = 1 := hnorm V hv
  have hU0 : U ≠ 0 := by intro h; simp [h] at hU
  have hV0 : V ≠ 0 := by intro h; simp [h] at hV
  have hle := norm_inner_le_norm (𝕜 := ℂ) U V
  rw [hU, hV, mul_one] at hle
  have hlt : ‖⟪U, V⟫_ℂ‖ < 1 := by
    refine lt_of_le_of_ne hle fun h => ?_
    have heq : ‖⟪U, V⟫_ℂ‖ = ‖U‖ * ‖V‖ := by simpa [hU, hV] using h
    obtain ⟨c, _, hc⟩ := (norm_inner_eq_norm_iff (𝕜 := ℂ) hU0 hV0).mp heq
    exact hne c (congrArg (fun x : EuclideanSpace ℂ ι => x.ofLp) hc)
  change ‖v ⬝ᵥ star u‖ < 1 at hlt
  rwa [dotProduct_star v u, norm_star] at hlt

private theorem collisionAmplitude_not_proportional (m : ℕ) (hm : 5 ≤ m) (c : ℂ) :
    collisionAmplitude true m ≠ c • collisionAmplitude false m := by
  intro h
  let u := traceWord 2 2 (2 + m) (cores false)
  let v := traceWord 2 2 (2 + m) (cores true)
  let a : ℂ := (Real.sqrt (mass u) : ℂ)
  let d : ℂ := (Real.sqrt (mass v) : ℂ)
  have hd : d ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2
      (PeriodicMPSProjectiveCoordinates.mass_pos v ((primitive_two_site_collision (2 + m) (by omega)).1 true))).ne'
  let e : Visible × Word m ≃ Word (2 + m) :=
    (Equiv.prodCongr (finTwoArrowEquiv (Fin 2)).symm (Equiv.refl _)).trans (Fin.appendEquiv 2 m)
  apply (primitive_two_site_collision (2 + m) (by omega)).2.1 (d * c / a)
  change v = (d * c / a) • u
  funext w
  obtain ⟨x, rfl⟩ := e.surjective w
  have hx := congrFun h x
  change v (e x) / d = c * (u (e x) / a) at hx
  change v (e x) = (d * c / a) * u (e x)
  calc
    _ = (v (e x) / d) * d := (div_mul_cancel₀ _ hd).symm
    _ = _ := by rw [hx]; simp only [div_eq_mul_inv]; ring

/-- The two verified rays are distinct, so the mixture has two positive weights. -/
theorem collision_overlap_norm_lt_one (m : ℕ) (hm : 5 ≤ m) :
    ‖collisionNormalizedOverlap (2 + m)‖ < 1 := by
  rw [← collisionAmplitude_overlap]
  exact overlap_norm_lt_one _ _ (collisionAmplitude_unit false m hm)
    (collisionAmplitude_unit true m hm) (collisionAmplitude_not_proportional m hm)

/-- The two global pure states on a ring of length `2 + m`. -/
def collisionPure (b : Bool) (m : ℕ) (hm : 5 ≤ m) : DensityState (Visible × Word m) :=
  pureDensity (collisionAmplitude b m) (collisionAmplitude_unit b m hm)

/-- The unconditioned state of the fair hidden label. -/
def collisionMixture (m : ℕ) (hm : 5 ≤ m) : DensityState (Visible × Word m) :=
  fairMixture (collisionPure false m hm) (collisionPure true m hm)

/-- The actual periodic mixture has two positive eigenvalues, counted with multiplicity. -/
theorem collisionMixture_nonzero_spectrum (m : ℕ) (hm : 5 ≤ m) :
    ((matrix (collisionMixture m hm)).charpoly.roots.filter (· ≠ 0)) =
      ({(((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2 : ℝ) : ℂ),
        (((1 - ‖collisionNormalizedOverlap (2 + m)‖) / 2 : ℝ) : ℂ)} : Multiset ℂ) := by
  have hPlus : 0 < (1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2 := by positivity
  have hMinus : 0 < (1 - ‖collisionNormalizedOverlap (2 + m)‖) / 2 :=
    div_pos (sub_pos.mpr (collision_overlap_norm_lt_one m hm)) (by norm_num)
  rw [collisionMixture, collisionPure, collisionPure, fairMixture_nonzero_spectrum,
    collisionAmplitude_overlap]
  apply Multiset.filter_eq_self.mpr
  intro z hz
  change z ∈ (((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2 : ℝ) : ℂ) ::ₘ
    {(((1 - ‖collisionNormalizedOverlap (2 + m)‖) / 2 : ℝ) : ℂ)} at hz
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact Complex.ofReal_ne_zero.mpr hPlus.ne'
  · exact Complex.ofReal_ne_zero.mpr hMinus.ne'

/-- The global mixture has rank exactly two at every ring length at least seven. -/
theorem collisionMixture_rank (m : ℕ) (hm : 5 ≤ m) :
    (matrix (collisionMixture m hm)).rank = 2 := by
  classical
  let A := matrix (collisionMixture m hm)
  have hA : A.IsHermitian := (matrix_posSemidef (collisionMixture m hm)).isHermitian
  have hcard : A.rank = (A.charpoly.roots.filter (· ≠ 0)).card := by
    rw [hA.rank_eq_card_non_zero_eigs, hA.roots_charpoly_eq_eigenvalues]
    simp only [Multiset.filter_map, Function.comp_def, Multiset.card_map,
      ← Finset.filter_val, ← Finset.card_def, Fintype.subtype_card]
    congr 1
    apply Finset.filter_congr
    intro i _
    exact not_congr Complex.ofReal_eq_zero.symm
  change A.rank = 2
  rw [hcard]
  change (((matrix (collisionMixture m hm)).charpoly.roots.filter (· ≠ 0)).card) = 2
  rw [collisionMixture_nonzero_spectrum]
  rfl

/-- Exact entropy of the unconditioned state of the primitive pair. -/
theorem collisionMixture_entropy (m : ℕ) (hm : 5 ≤ m) :
    entropy (collisionMixture m hm) = Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2) := by
  rw [collisionMixture, collisionPure, collisionPure, fairMixture_entropy, collisionAmplitude_overlap]

/-- The common output is positive definite, with trace one. -/
def collisionObserved : DensityState Visible :=
  ⟨CStarMatrix.ofMatrix collisionMarginal,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.nonneg_iff_posSemidef.mpr (primitive_two_site_collision 7 (by omega)).2.2.2.1.posSemidef),
    (primitive_two_site_collision 7 (by omega)).2.2.2.2.1⟩

theorem collisionObserved_posDef : (matrix collisionObserved).PosDef :=
  (primitive_two_site_collision 7 (by omega)).2.2.2.1

/-- The literal partial trace over all but the first two sites forgets the label. -/
theorem collision_partialTrace_pure (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    partialTraceRight (matrix (collisionPure b m hm)) = matrix collisionObserved := by
  change partialTraceRight (ray (collisionAmplitude b m)) = collisionMarginal
  rw [← collisionFlattening_common_visible b m hm]
  ext i j
  simp [partialTraceRight, ray, collisionAmplitude, Matrix.mul_apply, Matrix.vecMulVec_apply]

theorem collision_partialTrace_mixture (m : ℕ) (hm : 5 ≤ m) :
    partialTraceRight (matrix (collisionMixture m hm)) = matrix collisionObserved := by
  change partialTraceRight ((1 / 2 : ℝ) •
    (matrix (collisionPure false m hm) + matrix (collisionPure true m hm))) = _
  have hs (A : Matrix (Visible × Word m) (Visible × Word m) ℂ) :
      partialTraceRight ((1 / 2 : ℝ) • A) = (1 / 2 : ℝ) • partialTraceRight A := by
    ext i j
    simp [partialTraceRight, Complex.real_smul, Finset.mul_sum]
  rw [hs, partialTraceRight_add, collision_partialTrace_pure, collision_partialTrace_pure]
  rw [← two_smul ℝ, smul_smul]
  norm_num

private theorem collision_marginalRight_pure (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    marginalRight (collisionPure b m hm) = collisionObserved :=
  Subtype.ext (collision_partialTrace_pure b m hm)

private theorem collision_marginalRight_mixture (m : ℕ) (hm : 5 ≤ m) :
    marginalRight (collisionMixture m hm) = collisionObserved :=
  Subtype.ext (collision_partialTrace_mixture m hm)

private theorem collision_support (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    SupportContained (collisionPure b m hm) (collisionMixture m hm) := by
  have hs := fairMixture_support (collisionPure false m hm) (collisionPure true m hm)
  cases b
  · exact hs.1
  · exact hs.2

/-- Each label has finite global Umegaki divergence given by the binary entropy,
and both observed divergences are zero. -/
theorem collision_relativeEntropy (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    extendedQuantumRelativeEntropy (collisionPure b m hm) (collisionMixture m hm) =
      (Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2) : WithTop ℝ) ∧
    extendedQuantumRelativeEntropy (marginalRight (collisionPure b m hm))
      (marginalRight (collisionMixture m hm)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← collisionMixture_entropy m hm]
    have h := fairMixture_relativeEntropy _ _ (collisionAmplitude_unit false m hm)
      (collisionAmplitude_unit true m hm)
    cases b
    · exact h.1
    · exact h.2
  · rw [collision_marginalRight_pure, collision_marginalRight_mixture]
    exact extendedQuantumRelativeEntropy_self _

/-- Difference of the two finite Umegaki values across the two-site partial trace. -/
def collisionDefect (b : Bool) (m : ℕ) (hm : 5 ≤ m) : ℝ :=
  finiteTraceLogRelativeEntropy (collisionPure b m hm) (collisionMixture m hm) -
    finiteTraceLogRelativeEntropy (marginalRight (collisionPure b m hm))
      (marginalRight (collisionMixture m hm))

/-- The two-site observer loses the same exact amount of relative information for either label. -/
theorem collision_defect (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    collisionDefect b m hm = entropy (collisionMixture m hm) ∧
    collisionDefect b m hm = Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2) := by
  have h := (collision_relativeEntropy b m hm).1
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support (collision_support b m hm)] at h
  have h' := WithTop.coe_eq_coe.mp h
  have hd : collisionDefect b m hm = Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2) := by
    rw [collisionDefect, collision_marginalRight_pure, collision_marginalRight_mixture,
      finiteTraceLogRelativeEntropy_self, sub_zero, h']
  exact ⟨hd.trans (collisionMixture_entropy m hm).symm, hd⟩

/-- Overlap decay makes the binary entropy converge to one bit, in nats. -/
theorem collision_binary_entropy_limit :
    Tendsto (fun m : ℕ => Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2))
      atTop (𝓝 (Real.log 2)) := by
  have hg : Tendsto (fun m : ℕ => 4 * (19 / 20 : ℝ) ^ (2 + m)) atTop (𝓝 0) := by
    simpa [pow_add, ← mul_assoc] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (19 / 20 : ℝ)) (by norm_num)).const_mul
        (4 * (19 / 20 : ℝ) ^ 2)
  have hs : Tendsto (fun m : ℕ => ‖collisionNormalizedOverlap (2 + m)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun m => collision_normalized_overlap_bound (2 + m) (by omega)) hg
  have hp : Tendsto (fun m : ℕ => (1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by simpa using (hs.const_add 1).div_const 2
  simpa [Function.comp_def] using
    ((Real.binEntropy_continuous.continuousAt (x := (1 / 2 : ℝ))).tendsto.comp hp)

/-- Starting at ring length seven, the Umegaki defect converges to `log 2` for either label. -/
theorem collision_defect_limit (b : Bool) :
    Tendsto (fun k : ℕ => collisionDefect b (k + 5) (by omega)) atTop (𝓝 (Real.log 2)) := by
  refine (collision_binary_entropy_limit.comp (tendsto_add_atTop_nat 5)).congr ?_
  intro k
  exact (collision_defect b (k + 5) (by omega)).2.symm

#print axioms fairMixture_nonzero_spectrum
#print axioms fairMixture_entropy
#print axioms fairMixture_support
#print axioms fairMixture_relativeEntropy
#print axioms collision_overlap_norm_lt_one
#print axioms collisionMixture_nonzero_spectrum
#print axioms collisionMixture_rank
#print axioms collisionMixture_entropy
#print axioms collisionObserved_posDef
#print axioms collision_partialTrace_pure
#print axioms collision_partialTrace_mixture
#print axioms collision_relativeEntropy
#print axioms collision_defect
#print axioms collision_defect_limit

end

end D5.S3.Quantum.TensorNetworks.PrimitiveHiddenLabelEntropy
