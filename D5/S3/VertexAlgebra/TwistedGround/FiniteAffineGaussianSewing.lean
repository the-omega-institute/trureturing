/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteAffineGaussianSewing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteAffineGaussianSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-mean finite Gaussian absolute convergence and sewing. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
import D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientScaling
import D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation
import D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing

/-!
Finite complex Gaussian sewing uses ordinary transpose and the existing native
affine coefficients. Auxiliary scaling supplies a factorial square majorant
for unrestricted means before any infinite regrouping. No infinite-mode,
source identity, or physical realization claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing

open FactorialFockQuadraticEstimate OriginalChargedRowSource
open FactorialFockMetric (weight)
open WithLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

private abbrev coeff (A : Matrix I I ℂ) (mu : I → ℂ) (d : I →₀ ℕ) (k : ℕ) :=
  gaussianCoefficient (affineKernel A mu) (d.sumElim (Finsupp.single () k))

private abbrev majorant (A : Matrix I I ℂ) (mu : I → ℂ) (d : I →₀ ℕ) :=
  ∑ k ∈ Finset.range (d.degree + 1), ‖coeff A mu d k‖

private theorem zero_extension_bound (A : Matrix I I ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel A 0)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℂ I := toLp 2 (fun i => x (Sum.inl i))
  have hy : ‖y‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    change (∑ i, ‖x (Sum.inl i)‖ ^ 2) ≤ _
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hout : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel A 0) x‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    have hx : x = toLp 2 (ofLp x) := rfl
    rw [hx, Matrix.toEuclideanCLM_toLp]
    simp [affineKernel, ElementaryGaussianContraction.leftKernel,
      y, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct]
  rw [hout]
  exact (ContinuousLinearMap.le_opNorm _ y).trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _))

private theorem exists_scale (A : Matrix I I ℂ) (mu : I → ℂ)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel A (fun i => (ε : ℂ) * mu i))‖ < 1 := by
  let a := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
  let M := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel 0 mu)‖
  let ε := (1 - a) / (2 * (M + 1))
  have hM : 0 ≤ M := norm_nonneg _
  have he : 0 < ε := div_pos (sub_pos.mpr hA) (by positivity)
  have hid : affineKernel A (fun i => (ε : ℂ) * mu i) =
      affineKernel A 0 + (ε : ℂ) • affineKernel 0 mu := by
    ext (i | i) (j | j) <;>
      simp [affineKernel, ElementaryGaussianContraction.leftKernel, mul_comm]
  refine ⟨ε, he, ?_⟩
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel A 0)‖ + ε * M := by
      rw [hid, map_add, map_smul]
      simpa [norm_smul, Complex.norm_real, abs_of_pos he, M] using
        norm_add_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel A 0))
          ((ε : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (affineKernel 0 mu))
    _ ≤ a + ε * M := add_le_add (zero_extension_bound A) le_rfl
    _ < 1 := by
      have hidε : ε * (2 * (M + 1)) = 1 - a :=
        div_mul_cancel₀ _ (by positivity)
      change a < 1 at hA
      nlinarith

private theorem scale_coeff (A : Matrix I I ℂ) (mu : I → ℂ)
    (r : ℂ) (d : I →₀ ℕ) (k : ℕ) :
    coeff A (fun i => r * mu i) d k = r ^ k * coeff A mu d k := by
  let w : I ⊕ Unit → ℂ := Sum.elim (fun _ => 1) (fun _ => r)
  have hm : (fun i j => w i * affineKernel A mu i j * w j) =
      affineKernel A (fun i => r * mu i) := by
    ext (i | i) (j | j) <;>
      simp [w, affineKernel, ElementaryGaussianContraction.leftKernel, mul_comm]
  have h := GaussianCoefficientScaling.finite_diagonal_congruence
    (affineKernel A mu) w (d.sumElim (Finsupp.single () k))
  rw [hm, Finsupp.prod_sumElim] at h
  simpa [w, Function.comp_def, Finsupp.prod_single_index] using h

omit [Fintype I] [DecidableEq I] in
private theorem join_injective : Function.Injective
    (fun p : (I →₀ ℕ) × ℕ => p.1.sumElim (Finsupp.single () p.2)) := by
  intro p q h
  apply Prod.ext
  · ext i
    exact congrArg (fun d => d (Sum.inl i)) h
  · simpa only [Finsupp.sumElim_inr, Finsupp.single_eq_same] using
      congrArg (fun d => d (Sum.inr ())) h

omit [Fintype I] [DecidableEq I] in
private theorem weight_join (d : I →₀ ℕ) (k : ℕ) :
    weight (d.sumElim (Finsupp.single () k)) = weight d * k.factorial := by
  rw [weight, Finsupp.prod_sumElim]
  simp [weight, Finsupp.prod_single_index, Function.comp_def]

private theorem finite_majorant_bound (A : Matrix I I ℂ) (mu : I → ℂ)
    (t : ℝ) (ht : 0 ≤ t) (d : I →₀ ℕ) :
    (majorant A (fun i => (t : ℂ) * mu i) d) ^ 2 ≤ Real.exp (t ^ 2) *
      ∑ k ∈ Finset.range (d.degree + 1), (k.factorial : ℝ) * ‖coeff A mu d k‖ ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.range (d.degree + 1))
    (r := fun k => ‖coeff A (fun i => (t : ℂ) * mu i) d k‖)
    (f := fun k => (t ^ 2) ^ k / (k.factorial : ℝ))
    (g := fun k => (k.factorial : ℝ) * ‖coeff A mu d k‖ ^ 2)
    (fun k _ => by positivity) (fun k _ => by positivity) (by
      intro k _
      have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [scale_coeff, norm_mul, norm_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
      apply le_of_eq
      field_simp)
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (Real.sum_le_exp_of_nonneg (sq_nonneg t) _) (by positivity))

/-- Strong factorial square summability with norms taken before the auxiliary
sum. The mean is unrestricted and the finite mode type may be empty. -/
theorem affine_majorant_summable (A : Matrix I I ℂ) (mu : I → ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) :
    Summable (fun d : I →₀ ℕ => (weight d : ℝ) *
      (∑ k ∈ Finset.range (d.degree + 1),
        ‖gaussianCoefficient (affineKernel A mu) (d.sumElim (Finsupp.single () k))‖) ^ 2) := by
  obtain ⟨ε, he, hC⟩ := exists_scale A mu hA
  let nu : I → ℂ := fun i => (ε : ℂ) * mu i
  let C := affineKernel A nu
  have hsC : ∀ i j, C i j = C j i :=
    ElementaryGaussianContraction.left_symm A (fun i (_ : Unit) => nu i) hsym
  have hc := (occupation_summable C hsC (norm_nonneg _) hC le_rfl).comp_injective
    (join_injective (I := I))
  have hj : Summable (fun p : (I →₀ ℕ) × ℕ =>
      (weight p.1 : ℝ) * (p.2.factorial : ℝ) * ‖coeff A nu p.1 p.2‖ ^ 2) := by
    simpa only [Function.comp_def, weight_join, Nat.cast_mul] using hc
  have hnonneg : ∀ p : (I →₀ ℕ) × ℕ,
      0 ≤ (weight p.1 : ℝ) * (p.2.factorial : ℝ) * ‖coeff A nu p.1 p.2‖ ^ 2 := by
    intro p; positivity
  obtain ⟨hfiber, houter⟩ := (summable_prod_of_nonneg hnonneg).mp hj
  have hmu : (fun i => ((ε⁻¹ : ℝ) : ℂ) * nu i) = mu := by
    ext i
    simp [nu, ne_of_gt he]
  apply Summable.of_nonneg_of_le (fun d => by positivity) _
    (houter.mul_left (Real.exp ((ε⁻¹) ^ 2)))
  intro d
  have hb := finite_majorant_bound A nu (ε⁻¹) (le_of_lt (inv_pos.mpr he)) d
  rw [hmu] at hb
  calc
    _ ≤ (weight d : ℝ) * (Real.exp ((ε⁻¹) ^ 2) *
        ∑ k ∈ Finset.range (d.degree + 1), (k.factorial : ℝ) * ‖coeff A nu d k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = Real.exp ((ε⁻¹) ^ 2) *
        ∑ k ∈ Finset.range (d.degree + 1),
          (weight d : ℝ) * (k.factorial : ℝ) * ‖coeff A nu d k‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((hfiber d).sum_le_tsum _ (fun k _ => hnonneg (d, k))) (Real.exp_nonneg _)

private theorem coeff_vanish (A : Matrix I I ℂ) (mu : I → ℂ)
    (hsym : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (k : ℕ)
    (hk : d.degree < k) : coeff A mu d k = 0 := by
  have h := ElementaryGaussianContraction.left_vanish A (fun i (_ : Unit) => mu i)
    hsym d (Finsupp.single () k) (by simpa only [Finsupp.degree_single] using hk)
  change (weight (d.sumElim (Finsupp.single () k)) : ℂ) * coeff A mu d k = 0 at h
  exact (mul_eq_zero.mp h).resolve_left
    (Nat.cast_ne_zero.mpr (ne_of_gt (FactorialFockMetric.weight_pos _)))

private abbrev term (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (d : I →₀ ℕ) (p : ℕ × ℕ) : ℂ :=
  (weight d : ℂ) * coeff A mu d p.1 * coeff B nu d p.2

private theorem term_support (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (d : I →₀ ℕ) (p : ℕ × ℕ)
    (hp : p ∉ Finset.range (d.degree + 1) ×ˢ Finset.range (d.degree + 1)) :
    term A B mu nu d p = 0 := by
  have h : ¬(p.1 < d.degree + 1 ∧ p.2 < d.degree + 1) := by
    simpa only [Finset.mem_product, Finset.mem_range] using hp
  rcases not_and_or.mp h with h | h
  · simp [term, coeff_vanish A mu hAsym d p.1 (by omega)]
  · simp [term, coeff_vanish B nu hBsym d p.2 (by omega)]

private theorem norm_fiber (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (d : I →₀ ℕ) :
    (∑' p : ℕ × ℕ, ‖term A B mu nu d p‖) =
      (weight d : ℝ) * majorant A mu d * majorant B nu d := by
  rw [tsum_eq_sum (s := Finset.range (d.degree + 1) ×ˢ Finset.range (d.degree + 1))
    (fun p hp => by rw [term_support A B mu nu hAsym hBsym d p hp, norm_zero])]
  simp only [term, norm_mul, Complex.norm_natCast, Finset.sum_product,
    majorant, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem majorant_pair_summable (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    Summable (fun d : I →₀ ℕ => (weight d : ℝ) * majorant A mu d * majorant B nu d) := by
  apply Summable.of_nonneg_of_le (fun d => by positivity) _
    ((affine_majorant_summable A mu hAsym hA).add
      (affine_majorant_summable B nu hBsym hB))
  intro d
  have hw : 0 ≤ (weight d : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hw (sq_nonneg (majorant A mu d - majorant B nu d))]

/-- Absolute summability before exchanging internal and auxiliary occupations.
There is one internal factorial weight and no auxiliary factorial weight. -/
theorem affine_joint_norm_summable (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    Summable (fun p : (I →₀ ℕ) × (ℕ × ℕ) => ‖(weight p.1 : ℂ) *
      gaussianCoefficient (affineKernel A mu) (p.1.sumElim (Finsupp.single () p.2.1)) *
      gaussianCoefficient (affineKernel B nu) (p.1.sumElim (Finsupp.single () p.2.2))‖) := by
  apply (summable_prod_of_nonneg (fun p => norm_nonneg (term A B mu nu p.1 p.2))).mpr
  constructor
  · intro d
    apply summable_of_ne_finset_zero
      (s := Finset.range (d.degree + 1) ×ˢ Finset.range (d.degree + 1))
    intro p hp
    rw [term_support A B mu nu hAsym hBsym d p hp, norm_zero]
  · simpa only [norm_fiber A B mu nu hAsym hBsym] using
      majorant_pair_summable A B mu nu hAsym hBsym hA hB

private theorem complex_fiber (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (d : I →₀ ℕ) :
    (∑' p : ℕ × ℕ, term A B mu nu d p) =
      (weight d : ℂ) * affineCoefficient A mu d * affineCoefficient B nu d := by
  rw [tsum_eq_sum (s := Finset.range (d.degree + 1) ×ˢ Finset.range (d.degree + 1))
    (fun p hp => term_support A B mu nu hAsym hBsym d p hp)]
  simp only [term, affineCoefficient, coeff, Finset.sum_product,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem fixed_auxiliary_sewing (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) (k l : ℕ) :
    (∑' d : I →₀ ℕ, term A B mu nu d (k, l)) =
      Complex.exp ((1 / 2 : ℂ) *
        ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) *
      gaussianCoefficient
        (FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ) A B
          (fun _ i => mu i) (fun i _ => nu i))
        ((Finsupp.single () k).sumElim (Finsupp.single () l)) := by
  have hswap (d : I →₀ ℕ) :
      gaussianCoefficient
        (Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) (fun _ i => mu i)
          (Matrix.transpose (fun (_ : Unit) i => mu i)) A) ((Finsupp.single () k).sumElim d) = coeff A mu d k := by
    have h := InfiniteGaussianFock.gaussianCoefficient_enlarge (affineKernel A mu)
      Sum.swap (fun _ _ h => by simpa only [Sum.swap_swap] using congrArg Sum.swap h)
      ((Finsupp.single () k).sumElim d)
    rw [Finsupp.mapDomain_swap_sumElim] at h
    have hm : (fun i j => affineKernel A mu (Sum.swap i) (Sum.swap j)) =
        Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) (fun _ i => mu i)
          (Matrix.transpose (fun (_ : Unit) i => mu i)) A := by
      ext (i | i) (j | j) <;> rfl
    rw [hm] at h
    exact h.symm
  have h := (FiniteGaussianSewing.finite_sewing (0 : Matrix Unit Unit ℂ) 0 A B
    (fun _ i => mu i) (fun i _ => nu i) (fun _ _ => rfl) (fun _ _ => rfl)
    hAsym hBsym hA hB (Finsupp.single () k) (Finsupp.single () l)).2
  have hright : Matrix.fromBlocks B (fun i (_ : Unit) => nu i)
      (Matrix.transpose (fun i (_ : Unit) => nu i)) (0 : Matrix Unit Unit ℂ) =
      affineKernel B nu := rfl
  simpa only [hswap, hright, term, coeff] using h

private def auxiliaryEquiv : (ℕ × ℕ) ≃ ((Unit ⊕ Unit) →₀ ℕ) where
  toFun p := (Finsupp.single () p.1).sumElim (Finsupp.single () p.2)
  invFun d := (d (Sum.inl ()), d (Sum.inr ()))
  left_inv p := by simp
  right_inv d := by
    ext (i | i) <;> cases i <;> simp

set_option maxHeartbeats 1000000 in
/-- Full finite affine Gaussian sewing on the native coefficients, for arbitrary
complex means. Absolute convergence is established before the regrouping.
Only the two internal matrices must be strict Euclidean contractions. -/
theorem finite_affine_sewing (A B : Matrix I I ℂ) (mu nu : I → ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    Summable (fun d : I →₀ ℕ => ‖(weight d : ℂ) *
      affineCoefficient A mu d * affineCoefficient B nu d‖) ∧
    (∑' d : I →₀ ℕ, (weight d : ℂ) * affineCoefficient A mu d * affineCoefficient B nu d) =
      Complex.exp ((1 / 2 : ℂ) *
        ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) *
      Complex.exp ((1 / 2 : ℂ) * ∑ x, ∑ y,
        FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ) A B
          (fun _ i => mu i) (fun i _ => nu i) x y) := by
  have hn := affine_joint_norm_summable A B mu nu hAsym hBsym hA hB
  have hj : Summable (fun p : (I →₀ ℕ) × (ℕ × ℕ) => term A B mu nu p.1 p.2) :=
    hn.of_norm
  constructor
  · apply Summable.of_nonneg_of_le (fun d => norm_nonneg _) _ hn.prod
    intro d
    rw [← complex_fiber A B mu nu hAsym hBsym d]
    exact norm_tsum_le_tsum_norm (hn.prod_factor d)
  · let E := FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ) A B
      (fun _ i => mu i) (fun i _ => nu i)
    calc
      _ = ∑' d : I →₀ ℕ, ∑' p : ℕ × ℕ, term A B mu nu d p :=
        tsum_congr (fun d => (complex_fiber A B mu nu hAsym hBsym d).symm)
      _ = ∑' p : ℕ × ℕ, ∑' d : I →₀ ℕ, term A B mu nu d p := hj.tsum_comm.symm
      _ = ∑' p : ℕ × ℕ,
          Complex.exp ((1 / 2 : ℂ) *
            ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) *
          gaussianCoefficient E (auxiliaryEquiv p) := by
        apply tsum_congr
        intro p
        exact fixed_auxiliary_sewing A B mu nu hAsym hBsym hA hB p.1 p.2
      _ = _ := by
        rw [tsum_mul_left, auxiliaryEquiv.tsum_eq,
          GaussianEntireEvaluation.gaussianCoefficient_tsum]

end D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
