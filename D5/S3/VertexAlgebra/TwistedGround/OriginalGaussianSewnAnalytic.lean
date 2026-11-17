/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analytic cutoff passage for literal finite sewn source coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
import D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientContinuity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-! The finite sewn function uses the actual ordered inverse kernels, actual
opposite-charge means, and actual trace logarithm. Its proposed limit retains
the full chargeNorm times sourceConstant, including its inverse frequency.
Finite holomorphy and analytic cutoff limits are independent of the raw
occupation series and do not identify its coefficients without the source
sewing and stabilization bridges. Classical finite Gaussian and complex
analytic calculus are reused; no physical realization is asserted. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Topology Kronecker
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open OriginalChargedRowSource OriginalGaussianExternalBlocks OriginalGaussianSourceMeans
open OriginalGaussianDeterminant OriginalGaussianUniformDeterminant OriginalGaussianMatrix
open OriginalGaussianSourceGerm FactorialFockQuadraticEstimate MvPolynomial

universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

def explicitMean (D : LatticeData) (a : Charge D) (e : X → External D)
    (z : ℂ) : X ⊕ X → ℂ :=
  Sum.elim
    (fun x => (bilinear D (unitCharge D (e x).2.1) a : ℂ) *
      (-1 + sourceExternal (e x).1 (e x).2.2 z))
    (fun x => (bilinear D (unitCharge D (e x).2.1) a : ℂ) *
      (1 - sourceExternal (e x).1 (e x).2.2 z))

def finiteSewn (D : LatticeData) (a : Charge D) (e : X → External D)
    (d : (X ⊕ X) →₀ ℕ) (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(D.rank : ℂ) / 2 * finiteLog N z) *
    Complex.exp (effectiveConstant D a N e z) *
    affineCoefficient (originalEffectiveKernel D N e z) (effectiveMean D a N e z) d

def sewn (D : LatticeData) (a : Charge D) (e : X → External D)
    (d : (X ⊕ X) →₀ ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(D.rank : ℂ) / 2 * gaussianLogDet z) *
    Complex.exp ((chargeNorm D a : ℂ) * sourceConstant z) *
    affineCoefficient (explicitEffectiveKernel D e z) (explicitMean D a e z) d

/-- The ordinary scalar Taylor coefficient, with the complete factorial. -/
def coefficient (m : ℕ) (f : ℂ → ℂ) : ℂ := iteratedDeriv m f 0 / (m.factorial : ℂ)

private lemma affine_kernel_continuous {I : Type*} [Fintype I] [DecidableEq I] :
    Continuous (fun p : Matrix I I ℂ × (I → ℂ) => affineKernel p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;>
    simp only [affineKernel, ElementaryGaussianContraction.leftKernel,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
      Matrix.zero_apply] <;> fun_prop

private lemma affine_coefficient_continuous {I : Type*} [Fintype I] [DecidableEq I]
    (d : I →₀ ℕ) :
    Continuous (fun p : Matrix I I ℂ × (I → ℂ) => affineCoefficient p.1 p.2 d) := by
  apply continuous_finset_sum
  intro k hk
  exact (GaussianCoefficientContinuity.coefficient_continuous _).comp affine_kernel_continuous

private lemma uniform_error {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℂ → E} {f : ℂ → E} {s : Set ℂ} :
    TendstoUniformlyOn F f atTop s ↔
      Tendsto (fun x : ℕ × ℂ => F x.1 x.2 - f x.2) (atTop ×ˢ 𝓟 s) (𝓝 0) := by
  rw [Metric.tendstoUniformlyOn_iff, Metric.tendsto_nhds]
  simp only [eventually_prod_principal_iff, dist_eq_norm, sub_zero, norm_sub_rev]

private lemma uniform_pi {I : Type*} [Fintype I] {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℂ → I → E} {f : ℂ → I → E} {s : Set ℂ}
    (h : ∀ i, TendstoUniformlyOn (fun N z => F N z i) (fun z => f z i) atTop s) :
    TendstoUniformlyOn F f atTop s := by
  apply uniform_error.mpr
  exact tendsto_pi_nhds.mpr (fun i => uniform_error.mp (h i))

private lemma uniform_pair {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {A : ℕ → ℂ → E} {B : ℕ → ℂ → F} {a : ℂ → E} {b : ℂ → F} {s : Set ℂ}
    (hA : TendstoUniformlyOn A a atTop s) (hB : TendstoUniformlyOn B b atTop s) :
    TendstoUniformlyOn (fun N z => (A N z, B N z)) (fun z => (a z, b z)) atTop s := by
  apply uniform_error.mpr
  exact (uniform_error.mp hA).prodMk_nhds (uniform_error.mp hB)

private lemma power_coefficient_differentiableOn {I : Type*} [Fintype I] [DecidableEq I]
    {A : ℂ → Matrix I I ℂ} {s : Set ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s) (k : ℕ) (d : I →₀ ℕ) :
    DifferentiableOn ℂ (fun z => (quadratic (A z) ^ k).coeff d) s := by
  induction k generalizing d with
  | zero => simp only [pow_zero]; exact differentiableOn_const _
  | succ k ih =>
    simp only [pow_succ, coeff_mul]
    apply DifferentiableOn.fun_sum
    intro p hp
    apply (ih p.1).mul
    simp only [quadratic, coeff_smul, coeff_sum, smul_eq_mul]
    fun_prop

private lemma affine_coefficient_differentiableOn {I : Type*} [Fintype I] [DecidableEq I]
    {A : ℂ → Matrix I I ℂ} {mu : ℂ → I → ℂ} {s : Set ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (hm : ∀ i, DifferentiableOn ℂ (fun z => mu z i) s) (d : I →₀ ℕ) :
    DifferentiableOn ℂ (fun z => affineCoefficient (A z) (mu z) d) s := by
  have ha : ∀ i j, DifferentiableOn ℂ (fun z => affineKernel (A z) (mu z) i j) s := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hA i j
      | inr j => exact hm i
    | inr i =>
      cases j with
      | inl j => exact hm j
      | inr j => exact differentiableOn_const 0
  simp only [affineCoefficient, gaussianCoefficient, gaussianPiece, coeff_smul, smul_eq_mul]
  apply DifferentiableOn.fun_sum
  intro k hk
  exact (power_coefficient_differentiableOn ha _ _).const_mul _

section Inverse
open scoped Matrix.Norms.L2Operator

private def matrixEntryCLM {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    Matrix I I ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => A i j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private lemma section_differentiable (N : ℕ) :
    Differentiable ℂ (fun z => finiteSection N z) := by
  have he : (fun z => finiteSection N z) =
      fun z => ∑ i : Fin N, ∑ j : Fin N,
        (finiteSection N z i j) • Matrix.single i j (1 : ℂ) := by
    funext z
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single (finiteSection N z)
  rw [he]
  apply Differentiable.fun_sum
  intro i hi
  apply Differentiable.fun_sum
  intro j hj
  have hd : Differentiable ℂ (fun z => finiteSection N z i j) := by
    simp only [finiteSection, matrixEntry]
    fun_prop
  exact hd.smul_const _

private lemma square_unit (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit (1 - finiteSection N z ^ 2) := by
  apply isUnit_one_sub_of_norm_lt_one
  have hk : ‖finiteSection N z‖ < 1 := (finiteSection_opNorm_le N z hz).trans_lt
    (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))
  rw [pow_two]
  exact (norm_mul_le _ _).trans_lt
    (by simpa only [pow_two] using
      pow_lt_one₀ (norm_nonneg _) hk (by norm_num : (2 : ℕ) ≠ 0))

private lemma square_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (finiteSquare N) (ball (0 : ℂ) 1) := by
  have hd := ((differentiable_const (1 : Matrix (Fin N) (Fin N) ℂ)).sub ((section_differentiable N).pow 2)).differentiableOn
    (s := ball (0 : ℂ) 1)
  exact hd.inverse (fun z hz => square_unit N (mem_ball_zero_iff.mp hz))

private lemma square_entry_differentiableOn (N : ℕ) (i j : Fin N) :
    DifferentiableOn ℂ (fun z => finiteSquare N z i j) (ball (0 : ℂ) 1) :=
  (matrixEntryCLM i j).differentiable.comp_differentiableOn (square_differentiableOn N)

end Inverse

open scoped Matrix.Norms.Elementwise

private lemma inverse_entry_differentiableOn (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (e : X → External D) (i j : Internal D N) :
    DifferentiableOn ℂ (fun z =>
      Ring.inverse (1 - (rightRow D N e z).submatrix Sum.inl Sum.inl *
        (leftRow D N e z).submatrix Sum.inl Sum.inl) i j) (ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ (fun z =>
      Ring.inverse (1 - (leftRow D N e z).submatrix Sum.inl Sum.inl *
        (rightRow D N e z).submatrix Sum.inl Sum.inl) i j) (ball (0 : ℂ) 1) := by
  have hpoly (P Q : Matrix (Fin N) (Fin N) ℂ) :
      DifferentiableOn ℂ (fun z =>
        ((1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
          (P * finiteSquare N z * Q)) i j) (ball (0 : ℂ) 1) := by
    change DifferentiableOn ℂ (fun z =>
      (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) i.1 j.1 *
        (P * finiteSquare N z * Q) i.2 j.2) (ball (0 : ℂ) 1)
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro k hk
    apply DifferentiableOn.mul_const
    apply DifferentiableOn.fun_sum
    intro l hl
    exact (square_entry_differentiableOn N l k).const_mul _
  constructor
  · apply (hpoly (inverseFrequencyRoot N) (frequencyRoot N)).congr
    intro z hz
    exact congrArg (fun M => M i j)
      (original_internal_inverse_similarities D hu N e (mem_ball_zero_iff.mp hz)).1
  · apply (hpoly (frequencyRoot N) (inverseFrequencyRoot N)).congr
    intro z hz
    exact congrArg (fun M => M i j)
      (original_internal_inverse_similarities D hu N e (mem_ball_zero_iff.mp hz)).2

private lemma matrix_mul_diff {I J K : Type*} [Fintype J]
    {s : Set ℂ} {A : ℂ → Matrix I J ℂ} {B : ℂ → Matrix J K ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (hB : ∀ j k, DifferentiableOn ℂ (fun z => B z j k) s) (i : I) (k : K) :
    DifferentiableOn ℂ (fun z => (A z * B z) i k) s := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum (fun j _ => (hA i j).mul (hB j k))

private lemma matrix_vec_diff {I J : Type*} [Fintype J]
    {s : Set ℂ} {A : ℂ → Matrix I J ℂ} {v : ℂ → J → ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (hv : ∀ j, DifferentiableOn ℂ (fun z => v z j) s) (i : I) :
    DifferentiableOn ℂ (fun z => (A z).mulVec (v z) i) s := by
  exact DifferentiableOn.fun_sum (fun j _ => (hA i j).mul (hv j))

private lemma effective_kernel_diff {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {s : Set ℂ} {P : ℂ → Matrix J J ℂ} {Q : ℂ → Matrix K K ℂ}
    {A B : ℂ → Matrix I I ℂ} {R : ℂ → Matrix J I ℂ} {S : ℂ → Matrix I K ℂ}
    (hP : ∀ i j, DifferentiableOn ℂ (fun z => P z i j) s)
    (hQ : ∀ i j, DifferentiableOn ℂ (fun z => Q z i j) s)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (hB : ∀ i j, DifferentiableOn ℂ (fun z => B z i j) s)
    (hR : ∀ i j, DifferentiableOn ℂ (fun z => R z i j) s)
    (hS : ∀ i j, DifferentiableOn ℂ (fun z => S z i j) s)
    (hU : ∀ i j, DifferentiableOn ℂ (fun z => Ring.inverse (1 - B z * A z) i j) s)
    (hV : ∀ i j, DifferentiableOn ℂ (fun z => Ring.inverse (1 - A z * B z) i j) s)
    (i j : J ⊕ K) : DifferentiableOn ℂ (fun z =>
      FiniteGaussianSewing.effectiveKernel (P z) (Q z) (A z) (B z) (R z) (S z) i j) s := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact (hP i j).add
        (matrix_mul_diff (matrix_mul_diff (matrix_mul_diff hR hU) hB) (fun i j => hR j i) i j)
    | inr j => exact matrix_mul_diff (matrix_mul_diff hR hU) hS i j
  | inr i =>
    cases j with
    | inl j =>
      exact matrix_mul_diff (matrix_mul_diff (fun i j => hS j i) hV)
        (fun i j => hR j i) i j
    | inr j =>
      exact (hQ i j).add
        (matrix_mul_diff (matrix_mul_diff (matrix_mul_diff (fun i j => hS j i) hV) hA) hS i j)

private lemma finite_data_differentiableOn (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (N : ℕ) :
    (∀ i j, DifferentiableOn ℂ (fun z => originalEffectiveKernel D N e z i j)
      (ball (0 : ℂ) 1)) ∧
    (∀ i, DifferentiableOn ℂ (fun z => effectiveMean D a N e z i) (ball (0 : ℂ) 1)) ∧
    DifferentiableOn ℂ (fun z => effectiveConstant D a N e z) (ball (0 : ℂ) 1) := by
  have hL (i j) := (left_entry_differentiable D N e i j).differentiableOn
    (s := ball (0 : ℂ) 1)
  have hR (i j) := (right_entry_differentiable D N e i j).differentiableOn
    (s := ball (0 : ℂ) 1)
  have hU (i j) := (inverse_entry_differentiableOn D hu N e i j).1
  have hV (i j) := (inverse_entry_differentiableOn D hu N e i j).2
  have hm (b : Charge D) (i) :
      DifferentiableOn ℂ (fun z => leftMean D b N e z i) (ball (0 : ℂ) 1) := by
    cases i <;> simp only [leftMean, damp] <;> fun_prop
  have hn (i) : DifferentiableOn ℂ (fun z => rightMean D a N e z i)
      (ball (0 : ℂ) 1) := by
    cases i <;> simp only [rightMean, damp] <;> fun_prop
  have hA (i j) := hL (.inl i) (.inl j)
  have hB (i j) := hR (.inl i) (.inl j)
  have hE (i j) : DifferentiableOn ℂ
      (fun z => originalEffectiveKernel D N e z i j) (ball (0 : ℂ) 1) :=
    effective_kernel_diff (fun i j => hL (.inr i) (.inr j))
      (fun i j => hR (.inr i) (.inr j)) hA hB
      (fun i j => hL (.inr i) (.inl j)) (fun i j => hR (.inl i) (.inr j)) hU hV i j
  have heta (i) : DifferentiableOn ℂ (fun z => effectiveMean D a N e z i)
      (ball (0 : ℂ) 1) := by
    cases i with
    | inl i => exact (hm a (.inr i)).add (matrix_vec_diff
        (fun i j => hL (.inr i) (.inl j))
        (matrix_vec_diff hU (fun i => (hn (.inl i)).add
          (matrix_vec_diff hB (fun j => hm a (.inl j)) i))) i)
    | inr i => exact (hn (.inr i)).add (matrix_vec_diff
        (fun i j => hR (.inl j) (.inr i))
        (matrix_vec_diff hV (fun i => (hm a (.inl i)).add
          (matrix_vec_diff hA (fun j => hn (.inl j)) i))) i)
  have hc (i j : Unit ⊕ Unit) : DifferentiableOn ℂ (fun z =>
      FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ)
        ((leftRow D N e z).submatrix Sum.inl Sum.inl)
        ((rightRow D N e z).submatrix Sum.inl Sum.inl)
        (fun _ k => leftMean D a N e z (.inl k))
        (fun k _ => rightMean D a N e z (.inl k)) i j) (ball (0 : ℂ) 1) :=
    effective_kernel_diff (fun _ _ => differentiableOn_const 0)
      (fun _ _ => differentiableOn_const 0) hA hB
      (fun _ i => hm a (.inl i)) (fun i _ => hn (.inl i)) hU hV i j
  refine ⟨hE, heta, ?_⟩
  exact ((((hc (.inl ()) (.inl ())).add (hc (.inl ()) (.inr ()))).add
    (hc (.inr ()) (.inl ()))).add (hc (.inr ()) (.inr ()))).div_const 2

/-- The literal finite sewn function is holomorphic on a common disk,
independently of the cutoff-dependent raw occupation contraction germ. -/
theorem finiteSewn_differentiableOn (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) (N : ℕ) :
    DifferentiableOn ℂ (finiteSewn D a e d N) (ball (0 : ℂ) 1) := by
  obtain ⟨hE, heta, hc⟩ := finite_data_differentiableOn D hu a e N
  exact (((finiteLog_diff N).const_mul _).cexp.mul hc.cexp).mul
    (affine_coefficient_differentiableOn hE heta d)

private lemma continuous_comp_uniform {E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {F : ℕ → ℂ → E} {f : ℂ → E} {s : Set ℂ}
    (h : TendstoUniformlyOn F f atTop s) (hf : ContinuousOn f s) (hs : IsCompact s)
    {g : E → ℂ} (hg : Continuous g) :
    TendstoUniformlyOn (fun N z => g (F N z)) (fun z => g (f z)) atTop s := by
  obtain ⟨C, hC⟩ := (hs.image_of_continuousOn hf).isBounded.exists_norm_le
  have he : ∀ᶠ N in atTop, ∀ z ∈ s, dist (f z) (F N z) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp h) 1 zero_lt_one
  apply ((isCompact_closedBall (0 : E) (C + 1)).uniformContinuousOn_of_continuous
    hg.continuousOn).comp_tendstoUniformlyOn_eventually ?_ ?_ h
  · filter_upwards [he] with N hN z hz
    apply mem_closedBall_zero_iff.mpr
    calc
      ‖F N z‖ ≤ ‖f z‖ + ‖F N z - f z‖ := norm_le_insert' _ _
      _ ≤ C + 1 := add_le_add (hC _ ⟨z, hz, rfl⟩)
        (by simpa only [dist_eq_norm, norm_sub_rev] using (hN z hz).le)
  · intro z hz
    exact mem_closedBall_zero_iff.mpr ((hC _ ⟨z, hz, rfl⟩).trans (by linarith))

private abbrev SourceData (X : Type*) :=
  ℂ × ℂ × Matrix (X ⊕ X) (X ⊕ X) ℂ × ((X ⊕ X) → ℂ)

private def finiteData (D : LatticeData) (a : Charge D) (e : X → External D)
    (N : ℕ) (z : ℂ) : SourceData X :=
  (finiteLog N z, effectiveConstant D a N e z,
    originalEffectiveKernel D N e z, effectiveMean D a N e z)

private def limitData (D : LatticeData) (a : Charge D) (e : X → External D)
    (z : ℂ) : SourceData X :=
  (gaussianLogDet z, (chargeNorm D a : ℂ) * sourceConstant z,
    explicitEffectiveKernel D e z, explicitMean D a e z)

private lemma data_uniform (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    TendstoUniformlyOn (finiteData D a e) (limitData D a e) atTop
      {z : ℂ | ‖z‖ ≤ ρ} := by
  have hE : TendstoUniformlyOn (fun N z => originalEffectiveKernel D N e z)
      (fun z => explicitEffectiveKernel D e z) atTop {z : ℂ | ‖z‖ ≤ ρ} :=
    uniform_pi (fun i => uniform_pi (fun j =>
      original_effectiveKernel_blocks_tendsto_explicit D hu e hρ hρ1 i j))
  obtain ⟨hm, hc⟩ := original_opposite_charge_means_explicit D hu a e hρ hρ1
  have heta : TendstoUniformlyOn (fun N z => effectiveMean D a N e z)
      (fun z => explicitMean D a e z) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    apply uniform_pi
    intro i
    cases i with
    | inl x => exact (hm x).1
    | inr x => exact (hm x).2
  have hEm := uniform_pair (E := Matrix (X ⊕ X) (X ⊕ X) ℂ)
    (F := (X ⊕ X) → ℂ) hE heta
  have hcEm := uniform_pair (E := ℂ)
    (F := Matrix (X ⊕ X) (X ⊕ X) ℂ × ((X ⊕ X) → ℂ)) hc hEm
  exact uniform_pair (E := ℂ)
    (F := ℂ × Matrix (X ⊕ X) (X ⊕ X) ℂ × ((X ⊕ X) → ℂ))
    (finiteLog_tendstoUniformlyOn hρ hρ1) hcEm

private lemma data_continuousOn (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (N : ℕ) {ρ : ℝ} (hρ1 : ρ < 1) :
    ContinuousOn (finiteData D a e N) {z : ℂ | ‖z‖ ≤ ρ} := by
  have hsub : {z : ℂ | ‖z‖ ≤ ρ} ⊆ ball (0 : ℂ) 1 :=
    fun z hz => mem_ball_zero_iff.mpr (hz.trans_lt hρ1)
  obtain ⟨hEn, hmn, hcn⟩ := finite_data_differentiableOn D hu a e N
  exact ((finiteLog_diff N).continuousOn.prodMk
    (hcn.continuousOn.prodMk ((continuousOn_pi.mpr (fun i =>
      continuousOn_pi.mpr (fun j => (hEn i j).continuousOn))).prodMk
        (continuousOn_pi.mpr (fun i => (hmn i).continuousOn))))).mono hsub

private def sewnMap (D : LatticeData) (d : (X ⊕ X) →₀ ℕ) (p : SourceData X) : ℂ :=
  Complex.exp (-(D.rank : ℂ) / 2 * p.1) * Complex.exp p.2.1 *
    affineCoefficient p.2.2.1 p.2.2.2 d

private lemma sewnMap_continuous (D : LatticeData) (d : (X ⊕ X) →₀ ℕ) :
    Continuous (sewnMap D d) := by
  have ha := (affine_coefficient_continuous d).comp
    (by fun_prop : Continuous (fun p : SourceData X => (p.2.2.1, p.2.2.2)))
  exact ((Complex.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
    (Complex.continuous_exp.comp (by fun_prop))).mul ha

/-- Uniform cutoff convergence of the actual finite sewn function on every
closed subdisk. All limiting entries are the accepted explicit source data. -/
theorem finiteSewn_tendstoUniformlyOn (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    TendstoUniformlyOn (finiteSewn D a e d) (sewn D a e d) atTop
      {z : ℂ | ‖z‖ ≤ ρ} := by
  change TendstoUniformlyOn (fun N z => sewnMap D d (finiteData D a e N z))
    (fun z => sewnMap D d (limitData D a e z)) atTop {z : ℂ | ‖z‖ ≤ ρ}
  have hF := data_uniform D hu a e hρ hρ1
  exact continuous_comp_uniform (E := SourceData X)
    (g := sewnMap D d) hF
    (hF.continuousOn (Eventually.of_forall (fun N => data_continuousOn D hu a e N hρ1)).frequently)
    (by simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : ℂ) ρ) (sewnMap_continuous D d)

/-- Local uniform convergence uses closed subdisks of the common holomorphic
domain, with no uniform raw occupation majorant. -/
theorem finiteSewn_tendstoLocallyUniformlyOn (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) :
    TendstoLocallyUniformlyOn (finiteSewn D a e d) (sewn D a e d) atTop
      (ball (0 : ℂ) 1) := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between (mem_ball_zero_iff.mp hz)
  refine ⟨{w : ℂ | ‖w‖ ≤ ρ}, ?_,
    finiteSewn_tendstoUniformlyOn D hu a e d ((norm_nonneg z).trans hzρ.le) hρ1⟩
  apply mem_nhdsWithin_of_mem_nhds
  exact Filter.mem_of_superset (isOpen_lt continuous_norm continuous_const |>.mem_nhds hzρ)
    (fun w hw => show ‖w‖ ≤ ρ from le_of_lt hw)

/-- The literal explicit limiting source function is holomorphic. -/
theorem sewn_differentiableOn (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) :
    DifferentiableOn ℂ (sewn D a e d) (ball (0 : ℂ) 1) :=
  (finiteSewn_tendstoLocallyUniformlyOn D hu a e d).differentiableOn
    (Eventually.of_forall (finiteSewn_differentiableOn D hu a e d)) isOpen_ball

private lemma iterated_differentiableOn {f : ℂ → ℂ} {s : Set ℂ}
    (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) (m : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv m f) s := by
  induction m with
  | zero => simpa using hf
  | succ m ih => simpa only [iteratedDeriv_succ] using ih.deriv hs

/-- Every fixed ordinary scalar coefficient passes to the literal limit.
This does not identify it with the original source energy sum. -/
theorem finiteSewn_coefficient_tendsto (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) (m : ℕ) :
    Tendsto (fun N => coefficient m (finiteSewn D a e d N)) atTop
      (𝓝 (coefficient m (sewn D a e d))) := by
  have hd (k : ℕ) : TendstoLocallyUniformlyOn
      (fun N => iteratedDeriv k (finiteSewn D a e d N))
      (iteratedDeriv k (sewn D a e d)) atTop (ball (0 : ℂ) 1) := by
    induction k with
    | zero => simpa using finiteSewn_tendstoLocallyUniformlyOn D hu a e d
    | succ k ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv
        (Eventually.of_forall (fun N => iterated_differentiableOn
          (finiteSewn_differentiableOn D hu a e d N) isOpen_ball k)) isOpen_ball
  exact ((hd m).tendsto_at (by simp)).div_const _

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
