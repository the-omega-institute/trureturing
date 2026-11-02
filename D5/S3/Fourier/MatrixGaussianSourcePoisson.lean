/- GID: D5/S3/Fourier/MatrixGaussianSourcePoisson
   generality: G
   mirror-B: D5/B/S3/Fourier/MatrixGaussianSourcePoisson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent complex sources and normal convergence for positive matrix Gaussians. -/

import D5.S3.Fourier.MatrixGaussianPoisson

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Matrix
open scoped BigOperators

namespace D5.S3.Fourier.MatrixGaussian
noncomputable section
variable {r : ℕ}

/-- The Gaussian with independently complex coordinate sources. -/
def sourceGaussianMap (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ) (z : Fin r → ℂ) :
    C(Fin r → ℝ, ℂ) where
  toFun x := Complex.exp (-Real.pi * b * (quadratic A x : ℂ) + ∑ i, z i * (x i : ℂ))
  continuous_toFun := by unfold quadratic dotProduct Matrix.mulVec; fun_prop

private lemma real_source_absorption (s R : ℝ) (hs : 0 < s) (u x : ℝ)
    (hu : |u| ≤ R) : u * x ≤ s / 2 * x^2 + R^2 / (2*s) := by
  have hR : 0 ≤ R := (abs_nonneg u).trans hu
  have hu2 : u^2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) hR).mpr hu
  have hd : 0 < 2*s := by positivity
  apply le_of_mul_le_mul_left (a := 2*s) _ hd
  have he : (s / 2 * x^2 + R^2 / (2*s)) * (2*s) = s^2*x^2 + R^2 := by field_simp; ring
  nlinarith [he, sq_nonneg (s*x-u)]

/-- A source bounded in every coordinate is absorbed uniformly by half the
original Gaussian. The bound is independent of the lattice point and source. -/
theorem source_gaussian_bound (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (hb : 0 < b.re) (t : ℝ) (ht : 0 < t)
    (hq : ∀ x : Fin r → ℝ, t * (∑ i, x i^2) ≤ quadratic A x)
    (R : ℝ) (z : Fin r → ℂ) (hz : ∀ i, |(z i).re| ≤ R) (x : Fin r → ℝ) :
    ‖sourceGaussianMap A b z x‖ ≤
      Real.exp ((r : ℝ) * R^2 / (2 * (Real.pi * b.re * t))) *
        ‖gaussianMap A (b/2) x‖ := by
  let s := Real.pi * b.re * t
  have hs : 0 < s := by dsimp [s]; positivity
  have hlin := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    real_source_absorption s R hs (z i).re (x i) (hz i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlin
  have hquad := mul_le_mul_of_nonneg_left (hq x) (show 0 ≤ Real.pi * b.re / 2 by positivity)
  change ‖Complex.exp (-Real.pi * b * (quadratic A x : ℂ) + ∑ i, z i * (x i : ℂ))‖ ≤
    _ * ‖Complex.exp (-Real.pi * (b/2) * (quadratic A x : ℂ))‖
  rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, Complex.sum_re, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.div_ofNat_re]
  dsimp [s] at hlin
  nlinarith

/-- Every fixed polynomial degree is uniformly absorbed, simultaneously for
all sources in a coordinate bound. No summability premise is imposed. -/
theorem polynomial_source_gaussian_bound (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ)
    (hb : 0 < b.re) (t : ℝ) (ht : 0 < t)
    (hq : ∀ x : Fin r → ℝ, t*(∑ i, x i^2) ≤ quadratic A x)
    (R : ℝ) (z : Fin r → ℂ) (hz : ∀ i, |(z i).re| ≤ R) (k : ℕ) (x : Fin r → ℝ) :
    ‖x‖^k * ‖sourceGaussianMap A b z x‖ ≤
      ((k.factorial : ℝ) * Real.exp ((r : ℝ)*(R+1)^2/(2*(Real.pi*b.re*t)))) *
        ‖gaussianMap A (b/2) x‖ := by
  have hn : ‖x‖ ≤ ∑ i, |x i| := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))).mpr
    intro i
    simpa only [Real.norm_eq_abs] using
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (x j))
        (Finset.mem_univ i))
  have hp : ‖x‖^k ≤ (k.factorial : ℝ)*Real.exp (∑ i, |x i|) := by
    have h := (div_le_iff₀ (show (0 : ℝ) < k.factorial by positivity)).mp
      (Real.pow_div_factorial_le_exp (norm_nonneg x) k)
    have he := Real.exp_le_exp.mpr hn
    nlinarith [mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ k.factorial by positivity)]
  let z' : Fin r → ℂ := fun i => z i + (if 0 ≤ x i then 1 else -1)
  have hz' (i : Fin r) : |(z' i).re| ≤ R+1 := by
    dsimp [z']
    split_ifs <;> simp only [Complex.add_re, Complex.one_re, Complex.neg_re]
    · exact (abs_add _ _).trans (by simpa using add_le_add_right (hz i) 1)
    · exact (abs_add _ _).trans (by simpa using add_le_add_right (hz i) 1)
  have hlin : (∑ i, (z' i).re*x i) = (∑ i, (z i).re*x i) + ∑ i, |x i| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : 0 ≤ x i
    · simp [z', h, Complex.add_re, abs_of_nonneg h]; ring
    · simp [z', h, Complex.add_re, abs_of_neg (lt_of_not_ge h)]; ring
  have he : Real.exp (∑ i, |x i|) * ‖sourceGaussianMap A b z x‖ =
      ‖sourceGaussianMap A b z' x‖ := by
    change Real.exp (∑ i, |x i|) *
      ‖Complex.exp (-Real.pi*b*(quadratic A x : ℂ) + ∑ i, z i*(x i : ℂ))‖ =
      ‖Complex.exp (-Real.pi*b*(quadratic A x : ℂ) + ∑ i, z' i*(x i : ℂ))‖
    rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp only [Complex.add_re, Complex.sum_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [hlin]
    ring
  calc
    _ ≤ ((k.factorial : ℝ)*Real.exp (∑ i, |x i|)) * ‖sourceGaussianMap A b z x‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = (k.factorial : ℝ) * ‖sourceGaussianMap A b z' x‖ := by rw [mul_assoc, he]
    _ ≤ (k.factorial : ℝ) *
        (Real.exp ((r : ℝ)*(R+1)^2/(2*(Real.pi*b.re*t))) * ‖gaussianMap A (b/2) x‖) :=
      mul_le_mul_of_nonneg_left (source_gaussian_bound A b hb t ht hq (R+1) z' hz' x)
        (by positivity)
    _ = _ := by ring

/-- Absolute lattice summability with arbitrary independent complex sources. -/
theorem summable_norm_source_gaussian (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (z : Fin r → ℂ) :
    Summable (fun a : Fin r → ℤ => ‖sourceGaussianMap A b z (fun i => (a i : ℝ))‖) := by
  obtain ⟨t, ht, hq⟩ := exists_quadratic_lower_bound A hA
  have hb2 : 0 < (b/2).re := by simpa using half_pos hb
  refine ((summable_norm_gaussian A hA (b/2) hb2).mul_left
    (Real.exp ((r : ℝ) * ‖z‖^2 / (2 * (Real.pi * b.re * t))))).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun a => ?_)
  apply source_gaussian_bound A b hb t ht hq ‖z‖ z
  intro i
  exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)

/-- Normal convergence of integer translates in real coordinates. -/
theorem locally_summable_norm_source_gaussian (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (z : Fin r → ℂ)
    (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
    Summable (fun a : Fin r → ℤ =>
      ‖((sourceGaussianMap A b z).comp
        (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖) := by
  obtain ⟨t, ht, hq⟩ := exists_quadratic_lower_bound A hA
  let c := Real.exp ((r : ℝ) * ‖z‖^2 / (2 * (Real.pi * b.re * t)))
  have hb2 : 0 < (b/2).re := by simpa using half_pos hb
  refine ((locally_summable_norm_gaussian A hA (b/2) hb2 K).mul_left c).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun a => ?_)
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro x
  exact (source_gaussian_bound A b hb t ht hq ‖z‖ z
    (fun i => (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i))
    ((x : Fin r → ℝ) + fun i => (a i : ℝ))).trans
      (mul_le_mul_of_nonneg_left
        (((gaussianMap A (b/2)).comp
          (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K |>.norm_coe_le_norm x)
        (Real.exp_pos _).le)

/-- Each lattice term as an entire-source continuous function. -/
def latticeSourceMap (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ) (a : Fin r → ℤ) :
    C(Fin r → ℂ, ℂ) where
  toFun z := sourceGaussianMap A b z (fun i => (a i : ℝ))
  continuous_toFun := by
    change Continuous (fun z : Fin r → ℂ => Complex.exp
      (-Real.pi*b*(quadratic A (fun i => (a i : ℝ)) : ℂ) + ∑ i, z i*(a i : ℂ)))
    fun_prop

/-- Fixed-degree coordinate-norm weight, continuous in the whole complex source. -/
def weightedLatticeSourceMap (A : Matrix (Fin r) (Fin r) ℝ) (b : ℂ) (k : ℕ)
    (a : Fin r → ℤ) : C(Fin r → ℂ, ℂ) :=
  (‖(fun i => (a i : ℝ))‖^k : ℂ) • latticeSourceMap A b a

/-- A genuine summable Gaussian dominates all fixed finite polynomial orders,
uniformly on each compact subset of the independent complex source space. -/
theorem locally_summable_norm_polynomial_source (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (k : ℕ) (K : TopologicalSpace.Compacts (Fin r → ℂ)) :
    Summable (fun a : Fin r → ℤ => ‖(weightedLatticeSourceMap A b k a).restrict K‖) := by
  obtain ⟨t, ht, hq⟩ := exists_quadratic_lower_bound A hA
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let c := (k.factorial : ℝ)*Real.exp ((r : ℝ)*(R+1)^2/(2*(Real.pi*b.re*t)))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb2 : 0 < (b/2).re := by simpa using half_pos hb
  refine ((summable_norm_gaussian A hA (b/2) hb2).mul_left c).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun a => ?_)
  apply (ContinuousMap.norm_le _ (mul_nonneg hc (norm_nonneg _))).mpr
  intro z
  have hz : ‖(z : Fin r → ℂ)‖ ≤ R := by simpa using hR z.property
  have h := polynomial_source_gaussian_bound A b hb t ht hq R z
    (fun i => (Complex.abs_re_le_norm (z i)).trans ((norm_le_pi_norm _ i).trans hz))
    k (fun i => (a i : ℝ))
  simpa only [weightedLatticeSourceMap, ContinuousMap.restrict_apply, ContinuousMap.smul_apply,
    smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _), latticeSourceMap, ContinuousMap.coe_mk]
    using h

private lemma complexQuadratic_sub_smul (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : Aᵀ = A) (z w : Fin r → ℂ) (c : ℂ) :
    complexQuadratic A (z - c • w) = complexQuadratic A z -
      2*c*(w ⬝ᵥ (A.map Complex.ofRealHom) *ᵥ z) + c^2*complexQuadratic A w := by
  have hmap : (A.map Complex.ofRealHom)ᵀ = A.map Complex.ofRealHom := by
    rw [← Matrix.transpose_map, hA]
  have hx : z ⬝ᵥ (A.map Complex.ofRealHom) *ᵥ w =
      w ⬝ᵥ (A.map Complex.ofRealHom) *ᵥ z := by
    rw [← hmap, dotProduct_transpose_mulVec, hmap]
  simp only [complexQuadratic, mulVec_sub, sub_dotProduct, dotProduct_sub,
    mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hx]
  ring

private lemma complexQuadratic_cast (A : Matrix (Fin r) (Fin r) ℝ) (x : Fin r → ℝ) :
    complexQuadratic A (fun i => (x i : ℂ)) = (quadratic A x : ℂ) := by
  simp [complexQuadratic, quadratic, dotProduct, Matrix.mulVec,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]

private lemma fourier_source_exponent (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : Aᵀ = A) (b : ℂ) (hb : b ≠ 0) (z : Fin r → ℂ) (w : Fin r → ℝ) :
    complexQuadratic A (fun i => z i - 2*Real.pi*Complex.I*(w i : ℂ)) /
        (4*Real.pi*b) =
      complexQuadratic A z / (4*Real.pi*b) +
        (-Real.pi*b⁻¹*(quadratic A w : ℂ) +
          ∑ i, (-Complex.I/b*((A.map Complex.ofRealHom *ᵥ z) i)) * (w i : ℂ)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (fun i => z i - 2*Real.pi*Complex.I*(w i : ℂ)) =
      z - (2*Real.pi*Complex.I) • (fun i => (w i : ℂ)) by rfl,
    complexQuadratic_sub_smul A hA z _ _, complexQuadratic_cast]
  have hsum : (∑ i, (-Complex.I/b*((A.map Complex.ofRealHom *ᵥ z) i))*(w i : ℂ)) =
      (-Complex.I/b) * ((fun i => (w i : ℂ)) ⬝ᵥ (A.map Complex.ofRealHom) *ᵥ z) := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp
  simp [Complex.I_sq]
  <;> ring

/-- The genuine Fourier integral is a source Gaussian for the inverse Gram matrix. -/
theorem integral_fourier_source_gaussian (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (z : Fin r → ℂ) (w : Fin r → ℝ) :
    (∫ x : Fin r → ℝ, Complex.exp (-2*Real.pi*Complex.I*(w ⬝ᵥ x : ℝ)) *
      sourceGaussianMap A b z x) =
      ((Real.sqrt A.det : ℂ)⁻¹ * b^(-(r : ℂ)/2) *
        Complex.exp (complexQuadratic A⁻¹ z / (4*Real.pi*b))) *
        sourceGaussianMap A⁻¹ b⁻¹
          (fun i => -Complex.I/b*((A⁻¹.map Complex.ofRealHom *ᵥ z) i)) w := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hsym : (A⁻¹)ᵀ = A⁻¹ := by
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.inv.isHermitian
  rw [show (fun x : Fin r → ℝ => Complex.exp (-2*Real.pi*Complex.I*(w ⬝ᵥ x : ℝ)) *
      sourceGaussianMap A b z x) =
    (fun x => Complex.exp (-2*Real.pi*Complex.I*(w ⬝ᵥ x : ℝ)) *
      Complex.exp (-Real.pi*b*(quadratic A x : ℂ) + ∑ i, z i*(x i : ℂ))) by rfl,
    integral_fourier_gaussian_source A hA b hb z w,
    fourier_source_exponent A⁻¹ hsym b hb0 z w, Complex.exp_add]
  simp only [sourceGaussianMap, ContinuousMap.coe_mk, mul_assoc]

/-- Sourceful matrix Poisson summation. Its analytic hypotheses are proved from
positive definiteness; the coordinate periodization engine is reused unchanged. -/
theorem poisson_gaussian_source (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (b : ℂ) (hb : 0 < b.re) (z : Fin r → ℂ) :
    (∑' a : Fin r → ℤ, sourceGaussianMap A b z (fun i => (a i : ℝ))) =
      ((Real.sqrt A.det : ℂ)⁻¹ * b^(-(r : ℂ)/2) *
        Complex.exp (complexQuadratic A⁻¹ z / (4*Real.pi*b))) *
      ∑' k : Fin r → ℤ, sourceGaussianMap A⁻¹ b⁻¹
        (fun i => -Complex.I/b*((A⁻¹.map Complex.ofRealHom *ᵥ z) i))
        (fun i => (k i : ℝ)) := by
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  have hi : Integrable (sourceGaussianMap A b z) := by
    convert integrable_gaussian_source A hA ((Real.pi : ℂ)*b)
      (by simpa using mul_pos Real.pi_pos hb) z using 1
    funext x
    simp [sourceGaussianMap, neg_mul]
  have hs := (summable_norm_source_gaussian A⁻¹ hA.inv b⁻¹ hbi
    (fun i => -Complex.I/b*((A⁻¹.map Complex.ofRealHom *ᵥ z) i))).of_norm
  have hsf := hs.mul_left ((Real.sqrt A.det : ℂ)⁻¹ * b^(-(r : ℂ)/2) *
    Complex.exp (complexQuadratic A⁻¹ z / (4*Real.pi*b)))
  have hft (k : Fin r → ℤ) := integral_fourier_source_gaussian A hA b hb z (fun i => (k i : ℝ))
  have hp := CoordinatePoisson.tsum_eq_tsum_integral hi
    (locally_summable_norm_source_gaussian A hA b hb z)
    (hsf.congr (fun k => by simpa [dotProduct] using (hft k).symm))
  calc
    _ = ∑' k : Fin r → ℤ, ∫ x : Fin r → ℝ,
        Complex.exp (-2*Real.pi*Complex.I*(∑ i, (k i : ℝ)*x i : ℝ)) *
          sourceGaussianMap A b z x := hp
    _ = ∑' k : Fin r → ℤ,
        ((Real.sqrt A.det : ℂ)⁻¹ * b^(-(r : ℂ)/2) *
          Complex.exp (complexQuadratic A⁻¹ z / (4*Real.pi*b))) *
          sourceGaussianMap A⁻¹ b⁻¹
            (fun i => -Complex.I/b*((A⁻¹.map Complex.ofRealHom *ᵥ z) i))
            (fun i => (k i : ℝ)) := tsum_congr (fun k => by simpa [dotProduct] using hft k)
    _ = _ := tsum_mul_left

#print axioms integral_fourier_source_gaussian
#print axioms poisson_gaussian_source

#print axioms locally_summable_norm_polynomial_source
#print axioms polynomial_source_gaussian_bound
#print axioms source_gaussian_bound
#print axioms summable_norm_source_gaussian
#print axioms locally_summable_norm_source_gaussian

end
end D5.S3.Fourier.MatrixGaussian
