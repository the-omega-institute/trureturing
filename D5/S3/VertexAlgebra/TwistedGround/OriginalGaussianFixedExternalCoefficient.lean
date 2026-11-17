/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed external extraction of the original normally sewn Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Topology ContDiff Ring Matrix
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open OriginalChargedRowSource OriginalGaussianExternalBlocks OriginalGaussianSourceMeans
open OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic NativeAffineExternalCoefficient
open OriginalGaussianOccupationCoefficients NativeAffineTransport

universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The two actual full rows with one internal factorial. -/
def fullRowTerm (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D)
    (h k : X →₀ ℕ) (d : Internal D N →₀ ℕ) (z : ℂ) : ℂ :=
  (FactorialFockMetric.weight d : ℂ) *
    affineCoefficient (leftRow D N e z) (leftMean D a N e z) (d.sumElim h) *
    affineCoefficient (rightRow D N e z) (rightMean D a N e z) (d.sumElim k)

/-- Undamped actual rows, retaining complete inverse colour transport. -/
def rawFullRowTerm (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D)
    (h k : X →₀ ℕ) (d : Internal D N →₀ ℕ) : ℂ :=
  (FactorialFockMetric.weight d : ℂ) *
    affineCoefficient (originalRow D N e) (originalMean D a N e) (d.sumElim h) *
    affineCoefficient
      (transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
        (originalRow D N e)) (originalInverseMean D a N e) (d.sumElim k)

private theorem external_term (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (h k : X →₀ ℕ) (d : Internal D N →₀ ℕ) (z : ℂ) :
    externalPairCoefficient h k (fun x y => occupationTerm D a N e d (z, x, y)) =
      fullRowTerm D a N e h k d z := by
  exact externalPair_mixed (leftRow D N e z) (rightRow D N e z)
    (leftMean D a N e z) (rightMean D a N e z) (original_rows_symm D N e z).1
    (original_rows_symm D N e z).2 d h k

private theorem eval_affine {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (m x : I → ℂ) :
    MvPolynomial.eval x (affineExponent A m) =
      (1 / 2 : ℂ) * ∑ i, ∑ j, A i j * x i * x j + ∑ i, m i * x i := by
  simp only [affineExponent, FactorialFockQuadraticEstimate.quadratic,
    map_add, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem external_sewn (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (h k : X →₀ ℕ) (z : ℂ)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((leftRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((rightRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1) :
    externalPairCoefficient h k (fun x y =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
        Complex.exp (finiteMixedExponent D a N e (z, x, y))) =
      finiteSewn D a e (h.sumElim k) N z := by
  have hs := original_rows_symm D N e z
  have hE : (originalEffectiveKernel D N e z).IsSymm :=
    FiniteGaussianSewing.effectiveKernel_symm _ _ _ _ _ _
      (fun i j => hs.1 (.inr i) (.inr j))
      (fun i j => hs.2 (.inr i) (.inr j))
      (fun i j => hs.1 (.inl i) (.inl j))
      (fun i j => hs.2 (.inl i) (.inl j)) hA hB
  have he : (fun x y =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
        Complex.exp (finiteMixedExponent D a N e (z, x, y))) =
      (fun x y =>
        (Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
          Complex.exp (effectiveConstant D a N e z)) *
        Complex.exp (MvPolynomial.eval (Sum.elim x y)
          (affineExponent (originalEffectiveKernel D N e z) (effectiveMean D a N e z)))) := by
    funext x y
    rw [original_finite_mixed_exponent_collect D a N e z x y hA hB, eval_affine]
    simp only [Complex.exp_add]
    ring
  rw [he, externalPair_affine _ _ (fun i j => hE.apply j i)]
  rfl

/-- Fixed external ordinary coefficients pass through the actual occupation
sum on a positive fixed-cutoff germ. The bound is uniform only in this germ;
no lower bound for its radius across cutoffs is asserted. -/
theorem original_fixed_external_sewing_on_germ (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ) (e : X → External D)
    (h k : X →₀ ℕ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ B : (Internal D N →₀ ℕ) → ℝ, Summable B ∧
      (∀ z, ‖z‖ ≤ r → ∀ d, ‖fullRowTerm D a N e h k d z‖ ≤ B d) ∧
      ∀ z, ‖z‖ ≤ r → HasSum (fun d => fullRowTerm D a N e h k d z)
        (finiteSewn D a e (h.sumElim k) N z) := by
  obtain ⟨r₀, hr₀, hr₀1, M, hM, hb⟩ := original_occupation_majorant_on_germ D a N e
  obtain ⟨r₁, hr₁, hr₁1, hn, he⟩ := original_occupation_sewing_on_germ D hu a N e
  obtain ⟨r₂, hr₂, hr₂1, hc⟩ := original_rows_contract_on_germ D N e
  let r := min r₀ (min r₁ r₂)
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrr₁ : r ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_right _ _)
  let F := fun d (z : {z : ℂ // ‖z‖ ≤ r}) x y => occupationTerm D a N e d (z.val, x, y)
  have hF d z : ContDiff ℂ (⊤ : ℕ∞ω)
      (fun v : (X ⊕ X) → ℂ => F d z (v ∘ Sum.inl) (v ∘ Sum.inr)) :=
    mixed_external_contDiff (leftRow D N e z.val) (rightRow D N e z.val)
      (leftMean D a N e z.val) (rightMean D a N e z.val) d
  have hv (v : (X ⊕ X) → ℂ) (hv : ‖v‖ < 1) :
      (∀ j, ‖(v ∘ Sum.inl) j‖ ≤ 1) ∧ ∀ j, ‖(v ∘ Sum.inr) j‖ ≤ 1 := by
    constructor <;> intro j <;> exact (norm_le_pi_norm v _).trans hv.le
  have hbound d z v (hw : ‖v‖ < 1) : ‖F d z (v ∘ Sum.inl) (v ∘ Sum.inr)‖ ≤ M d :=
    hb _ ⟨z.property.trans hrr₀, (hv v hw).1, (hv v hw).2⟩ d
  obtain ⟨B, hB, hbound', hsum⟩ := externalPair_normal_family F M hM 1 zero_lt_one hF hbound h k
  refine ⟨r, hr, hrr₀.trans_lt hr₀1, B, hB, ?_, ?_⟩
  · intro z hz d
    simpa only [F, external_term] using hbound' ⟨z, hz⟩ d
  · intro z hz
    have hh := hsum ⟨z, hz⟩
    simp only [F, external_term] at hh
    have hext := externalPair_congr_ball h k
      (fun x y => ∑' d, occupationTerm D a N e d (z, x, y))
      (fun x y =>
        Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
          Complex.exp (finiteMixedExponent D a N e (z, x, y))) zero_lt_one
      (fun v hw => he _ ⟨hz.trans hrr₁, (hv v hw).1, (hv v hw).2⟩)
    rw [hext, external_sewn D a N e h k z (hc z (hz.trans hrr₂)).1
      (hc z (hz.trans hrr₂)).2.1] at hh
    exact hh

private theorem full_row_scales (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (h k : X →₀ ℕ) (d : Internal D N →₀ ℕ) (z : ℂ) :
    fullRowTerm D a N e h k d z =
      z ^ (2 * internalEnergy D N d) * rawFullRowTerm D a N e h k d :=
  original_row_product_scales D a N e z d h k

private theorem full_row_contDiff (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (h k : X →₀ ℕ) (d : Internal D N →₀ ℕ) :
    ContDiff ℂ (⊤ : ℕ∞ω) (fullRowTerm D a N e h k d) := by
  simp_rw [show fullRowTerm D a N e h k d = fun z =>
    z ^ (2 * internalEnergy D N d) * rawFullRowTerm D a N e h k d by
      funext z; exact full_row_scales D a N e h k d z]
  exact (contDiff_id.pow _).mul contDiff_const

private theorem full_row_coefficient (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (h k : X →₀ ℕ) (d : Internal D N →₀ ℕ) (n : ℕ) :
    coefficient (2 * n) (fullRowTerm D a N e h k d) =
      if internalEnergy D N d = n then rawFullRowTerm D a N e h k d else 0 := by
  have he : fullRowTerm D a N e h k d = fun z =>
      z ^ (2 * internalEnergy D N d) * rawFullRowTerm D a N e h k d := by
    funext z
    exact full_row_scales D a N e h k d z
  rw [he, coefficient, iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]
  by_cases hd : internalEnergy D N d = n
  · simp [hd, Nat.factorial_ne_zero]
  · have hn : 2 * n ≠ 2 * internalEnergy D N d := by omega
    simp [hd, hn]

/-- The literal finite sewn coefficient is the original full-row energy
layer, after justified external extraction and source differentiation. -/
theorem original_finiteSewn_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (N : ℕ) (e : X → External D) (h k : X →₀ ℕ) (n : ℕ) :
    coefficient (2 * n) (finiteSewn D a e (h.sumElim k) N) =
      ∑ᶠ d : {d : Internal D N →₀ ℕ // internalEnergy D N d = n},
        rawFullRowTerm D a N e h k d.val := by
  classical
  obtain ⟨r, hr, hr1, M, hM, hb, he⟩ := original_fixed_external_sewing_on_germ D hu a N e h k
  let F := fullRowTerm D a N e h k
  have hn : TendstoLocallyUniformlyOn
      (fun s : Finset (Internal D N →₀ ℕ) => fun z => ∑ d ∈ s, F d z)
      (fun z => ∑' d, F d z) atTop (ball (0 : ℂ) r) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact tendstoUniformlyOn_tsum hM (fun d z hz => hb z (mem_ball_zero_iff.mp hz).le d)
  have hd (m : ℕ) : TendstoLocallyUniformlyOn
      (fun s : Finset (Internal D N →₀ ℕ) => iteratedDeriv m (fun z => ∑ d ∈ s, F d z))
      (iteratedDeriv m (fun z => ∑' d, F d z)) atTop (ball (0 : ℂ) r) := by
    induction m with
    | zero => simpa using hn
    | succ m ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv
        (Eventually.of_forall (fun s =>
          (iterated_partial_diff (fun d => full_row_contDiff D a N e h k d) s m).differentiableOn))
        isOpen_ball
  have hs : HasSum (fun d => coefficient (2 * n) (F d))
      (coefficient (2 * n) (fun z => ∑' d, F d z)) := by
    have ht := ((hd (2 * n)).tendsto_at (a := (0 : ℂ)) (by simpa using hr)).div_const
      ((2 * n).factorial : ℂ)
    change Tendsto _ atTop (𝓝 _) at ht
    rw [HasSum]
    have hsum (s : Finset (Internal D N →₀ ℕ)) :
        iteratedDeriv (2 * n) (fun z => ∑ d ∈ s, F d z) 0 /
            ((2 * n).factorial : ℂ) = ∑ d ∈ s, coefficient (2 * n) (F d) := by
      rw [iteratedDeriv_fun_sum]
      · simp only [coefficient, Finset.sum_div]
      · intro d hd
        exact (full_row_contDiff D a N e h k d).contDiffAt.of_le (by simp)
    simp_rw [hsum] at ht
    exact ht
  have hg : (fun z => ∑' d, F d z) =ᶠ[𝓝 (0 : ℂ)] finiteSewn D a e (h.sumElim k) N := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact (he z (mem_ball_zero_iff.mp hz).le).tsum_eq
  have hfin : Function.HasFiniteSupport (fun d : Internal D N →₀ ℕ =>
      if internalEnergy D N d = n then rawFullRowTerm D a N e h k d else 0) := by
    apply (energy_layer_finite D N n).subset
    intro d hd
    by_contra hx
    exact hd (if_neg hx)
  have ht := hs.tsum_eq
  simp only [F, full_row_coefficient] at ht
  rw [tsum_eq_finsum hfin] at ht
  have hc := congrArg (fun v : ℂ => v / ((2 * n).factorial : ℂ))
    (hg.iteratedDeriv_eq (2 * n))
  change coefficient (2 * n) (fun z => ∑' d, F d z) =
    coefficient (2 * n) (finiteSewn D a e (h.sumElim k) N) at hc
  rw [← hc, ← ht]
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient
