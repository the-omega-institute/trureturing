/- GID: D5/S3/Quantum/Subentropy/PinchingGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/PinchingGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Bool]
   utility: none
   digest: Gaussian entropy gives concavity and convex nonnegative block-pinching gaps. -/

import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.ClassicalQuantumGram
import D5.S3.Quantum.Subentropy.EntropyJensenGap
import D5.S3.Quantum.Subentropy.GaussianMatrix
import D5.S3.Quantum.Subentropy.GaussianQuadratic
import Mathlib.Logic.Equiv.Bool

/-! Exact finite sign-twirl algebra, including empty coordinate blocks.
Escape audit unfinished for sign_unitary and signTwirl_eq_blockPinch: https://github.com/the-omega-institute/trureturing/issues/19176. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Subentropy.PinchingGap
open _root_.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open _root_.D5.S3.Quantum.Subentropy.EntropyJensenGap
open _root_.D5.S3.Quantum.Subentropy.GaussianQuadratic
open _root_.D5.S3.Quantum.Subentropy.GaussianMatrix
open _root_.D5.S3.Quantum.Subentropy.Basic

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- One independent real sign for each classical block. -/
def blockSign (s : X → Bool) (x : X) : ℂ := if s x then -1 else 1

/-- The diagonal sign unitary acts identically within each classical block. -/
def signUnitary (s : X → Bool) : Matrix (X × B) (X × B) ℂ :=
  diagonal (fun i => blockSign s i.1)

/-- The uniform finite twirl over all independent choices of block signs. -/
def signTwirl (A : Matrix (X × B) (X × B) ℂ) : Matrix (X × B) (X × B) ℂ :=
  (Fintype.card (X → Bool) : ℂ)⁻¹ •
    ∑ s : X → Bool, signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose

private theorem sign_adjoint (s : X → Bool) :
    (signUnitary (B := B) s).conjTranspose = signUnitary (B := B) s := by
  simp only [signUnitary, diagonal_conjTranspose]
  congr 1
  funext i
  cases h : s i.1 <;> simp [blockSign, h]

private theorem sign_square (s : X → Bool) :
    signUnitary (B := B) s * signUnitary (B := B) s = 1 := by
  simp only [signUnitary, diagonal_mul_diagonal]
  have hs : (fun i : X × B => blockSign s i.1 * blockSign s i.1) = fun _ => (1 : ℂ) := by
    funext i
    cases h : s i.1 <;> simp [blockSign, h]
  rw [hs, diagonal_one]

theorem sign_unitary (s : X → Bool) :
    (signUnitary (B := B) s).conjTranspose * signUnitary (B := B) s = 1 ∧
      signUnitary (B := B) s * (signUnitary (B := B) s).conjTranspose = 1 := by
  constructor <;> rw [sign_adjoint, sign_square]

private theorem sign_conjugate_entries (s : X → Bool)
    (A : Matrix (X × B) (X × B) ℂ) (i j : X × B) :
    (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) i j =
      blockSign s i.1 * blockSign s j.1 * A i j := by
  rw [sign_adjoint]
  simp only [signUnitary, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

private theorem sign_correlation (x y : X) :
    ∑ s : X → Bool, blockSign s x * blockSign s y =
      if x = y then (Fintype.card (X → Bool) : ℂ) else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    have hs : ∀ s : X → Bool, blockSign s x * blockSign s x = 1 := by
      intro s
      cases h : s x <;> simp [blockSign, h]
    simp only [ite_true, hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · simp only [if_neg hxy]
    let e : (X → Bool) ≃ (X → Bool) := Equiv.piCongrRight
      (fun k => if k = x then Equiv.boolNot else Equiv.refl Bool)
    have hx : ∀ s : X → Bool, e s x = !(s x) := by
      intro s
      simp [e, Equiv.piCongrRight_apply]
    have hy : ∀ s : X → Bool, e s y = s y := by
      intro s
      simp [e, Equiv.piCongrRight_apply, Ne.symm hxy]
    have hflip : ∀ s : X → Bool,
        blockSign (e s) x * blockSign (e s) y = -(blockSign s x * blockSign s y) := by
      intro s
      cases hs : s x <;> cases ht : s y <;> simp [blockSign, hx, hy, hs, ht]
    have hneg : (∑ s : X → Bool, blockSign s x * blockSign s y) =
        -(∑ s : X → Bool, blockSign s x * blockSign s y) := by
      calc
        _ = ∑ s : X → Bool, blockSign (e s) x * blockSign (e s) y :=
          (e.sum_comp (fun s => blockSign s x * blockSign s y)).symm
        _ = ∑ s : X → Bool, -(blockSign s x * blockSign s y) :=
          Finset.sum_congr rfl (fun s _ => hflip s)
        _ = _ := Finset.sum_neg_distrib _
    exact CharZero.eq_neg_self_iff.mp hneg

theorem signTwirl_eq_blockPinch (A : Matrix (X × B) (X × B) ℂ) :
    signTwirl A = blockPinch A := by
  have hn : (Fintype.card (X → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp only [signTwirl, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    sign_conjugate_entries]
  rw [← Finset.sum_mul, sign_correlation]
  by_cases hij : i.1 = j.1
  · simp [blockPinch, hij, hn]
  · simp [blockPinch, hij]

private theorem quadratic_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ)
    (A : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    gaussianQuadratic (c • A) z = c * gaussianQuadratic A z := by
  unfold gaussianQuadratic
  rw [LinearMapClass.map_smul_of_tower, LinearMap.smul_apply]
  rw [inner_smul_right_eq_smul, Complex.smul_re]
  change c * (inner ℂ z (Matrix.toEuclideanLin A z)).re / 2 =
    c * ((inner ℂ z (Matrix.toEuclideanLin A z)).re / 2)
  ring

private theorem quadratic_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Type*} [Fintype T]
    (A : T → Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    gaussianQuadratic (∑ t, A t) z = ∑ t, gaussianQuadratic (A t) z := by
  simp only [gaussianQuadratic, map_sum, LinearMap.sum_apply, inner_sum,
    Complex.re_sum, Finset.sum_div]

private theorem quadratic_twirl_mean (A : Matrix (X × B) (X × B) ℂ)
    (z : EuclideanSpace ℂ (X × B)) :
    gaussianQuadratic (blockPinch A) z = finiteAverage
      (fun s : X → Bool => gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z) := by
  rw [← signTwirl_eq_blockPinch A]
  unfold signTwirl
  have hscale (M : Matrix (X × B) (X × B) ℂ) :
      (Fintype.card (X → Bool) : ℂ)⁻¹ • M =
        (Fintype.card (X → Bool) : ℝ)⁻¹ • M := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hscale, quadratic_real_smul, quadratic_sum]
  rfl

/-- The pointwise entropy defect of a PSD matrix along its actual sign orbit. -/
def signOrbitEntropyGap (A : Matrix (X × B) (X × B) ℂ)
    (z : EuclideanSpace ℂ (X × B)) : ℝ :=
  Real.negMulLog (gaussianQuadratic (blockPinch A) z) -
    finiteAverage (fun s : X → Bool => Real.negMulLog
      (gaussianQuadratic (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z))

private theorem sign_orbit_entropy_laws (A : Matrix (X × B) (X × B) ℂ)
    (hA : A.PosSemidef) (z : EuclideanSpace ℂ (X × B)) :
    (∀ s : X → Bool,
      (signUnitary (B := B) s).conjTranspose * signUnitary (B := B) s = 1 ∧
        signUnitary (B := B) s * (signUnitary (B := B) s).conjTranspose = 1) ∧
    signTwirl A = blockPinch A ∧
    signOrbitEntropyGap A z = entropyJensenGap
      (fun s : X → Bool => gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z) ∧
    0 ≤ signOrbitEntropyGap A z := by
  have heq : signOrbitEntropyGap A z = entropyJensenGap
      (fun s : X → Bool => gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z) := by
    unfold signOrbitEntropyGap entropyJensenGap
    rw [quadratic_twirl_mean]
  refine ⟨sign_unitary, signTwirl_eq_blockPinch A, heq, ?_⟩
  rw [heq]
  apply entropyJensenGap_laws.1
  intro s
  exact quadratic_nonnegative (hA.mul_mul_conjTranspose_same (signUnitary (B := B) s)) z

private theorem quadratic_add {ι : Type*} [Fintype ι] [DecidableEq ι] (A C : Matrix ι ι ℂ)
    (z : EuclideanSpace ℂ ι) :
    gaussianQuadratic (A + C) z = gaussianQuadratic A z + gaussianQuadratic C z := by
  simp only [gaussianQuadratic, map_add, LinearMap.add_apply, inner_add_right,
    Complex.add_re, add_div]

private theorem sign_orbit_gap_convex (z : EuclideanSpace ℂ (X × B)) :
    ConvexOn ℝ {A : Matrix (X × B) (X × B) ℂ | A.PosSemidef}
      (fun A => signOrbitEntropyGap A z) := by
  refine ⟨?_, ?_⟩
  · intro A hA C hC c d hc hd _
    exact (hA.smul hc).add (hC.smul hd)
  · intro A hA C hC c d hc hd hcd
    have hM := (hA.smul hc).add (hC.smul hd)
    change signOrbitEntropyGap (c • A + d • C) z ≤
      c * signOrbitEntropyGap A z + d * signOrbitEntropyGap C z
    rw [(sign_orbit_entropy_laws _ hM z).2.2.1,
      (sign_orbit_entropy_laws _ hA z).2.2.1,
      (sign_orbit_entropy_laws _ hC z).2.2.1]
    have heq : (fun s : X → Bool => gaussianQuadratic
        (signUnitary (B := B) s * (c • A + d • C) *
          (signUnitary (B := B) s).conjTranspose) z) =
      c • (fun s : X → Bool => gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z) +
      d • (fun s : X → Bool => gaussianQuadratic
        (signUnitary (B := B) s * C * (signUnitary (B := B) s).conjTranspose) z) := by
      funext s
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        quadratic_add, quadratic_real_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact entropyJensenGap_laws.2.2.2
      (fun s => quadratic_nonnegative (hA.mul_mul_conjTranspose_same _) z)
      (fun s => quadratic_nonnegative (hC.mul_mul_conjTranspose_same _) z) hc hd hcd

private theorem pinch_positive (A : Matrix (X × B) (X × B) ℂ)
    (hA : A.PosSemidef) : (blockPinch A).PosSemidef := by
  rw [← signTwirl_eq_blockPinch A]
  have hscale (M : Matrix (X × B) (X × B) ℂ) :
      (Fintype.card (X → Bool) : ℂ)⁻¹ • M =
        (Fintype.card (X → Bool) : ℝ)⁻¹ • M := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [signTwirl, hscale]
  exact (Matrix.posSemidef_sum Finset.univ
    (fun s _ => hA.mul_mul_conjTranspose_same (signUnitary (B := B) s))).smul
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem pinch_trace (A : Matrix (X × B) (X × B) ℂ) :
    (blockPinch A).trace = A.trace := by
  simp [Matrix.trace, blockPinch]

private theorem orbit_trace (A : Matrix (X × B) (X × B) ℂ) (s : X → Bool) :
    (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, (sign_unitary s).1, Matrix.one_mul]

private theorem pinch_gap_integral (A : Matrix (X × B) (X × B) ℂ)
    (hA : A.PosSemidef) (htr : A.trace = 1) (i₀ : X × B) :
    Integrable (signOrbitEntropyGap A) (stdGaussian (EuclideanSpace ℂ (X × B))) ∧
    matrixSubentropy (blockPinch A) - matrixSubentropy A =
      ∫ z, signOrbitEntropyGap A z ∂stdGaussian (EuclideanSpace ℂ (X × B)) := by
  let γ := stdGaussian (EuclideanSpace ℂ (X × B))
  have hpa := matrix_subentropy_gaussian_entropy A hA htr i₀
  have hpp := matrix_subentropy_gaussian_entropy (blockPinch A) (pinch_positive A hA)
    (by rw [pinch_trace, htr]) i₀
  have ho (s : X → Bool) := matrix_subentropy_gaussian_entropy
    (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose)
    (hA.mul_mul_conjTranspose_same _) (by rw [orbit_trace, htr]) i₀
  have havg : Integrable (fun z => finiteAverage (fun s : X → Bool =>
      Real.negMulLog (gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z))) γ :=
    (integrable_finsetSum Finset.univ (fun s _ => (ho s).1)).const_mul _
  have hint : (∫ z, finiteAverage (fun s : X → Bool =>
      Real.negMulLog (gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z)) ∂γ) =
      ∫ z, Real.negMulLog (gaussianQuadratic A z) ∂γ := by
    unfold finiteAverage
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun s _ => (ho s).1)]
    have heach (s : X → Bool) :
        (∫ z, Real.negMulLog (gaussianQuadratic
          (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z) ∂γ) =
        ∫ z, Real.negMulLog (gaussianQuadratic A z) ∂γ := by
      have hq := matrixSubentropy_isometric_embedding A (signUnitary (B := B) s)
        (sign_unitary s).1
      rw [(ho s).2, hpa.2] at hq
      linarith
    change (Fintype.card (X → Bool) : ℝ)⁻¹ *
      (∑ s : X → Bool, ∫ z, Real.negMulLog (gaussianQuadratic
        (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z) ∂γ) = _
    simp_rw [heach]
    have hn : (Fintype.card (X → Bool) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hn]
  refine ⟨hpp.1.sub havg, ?_⟩
  change _ = ∫ z, Real.negMulLog (gaussianQuadratic (blockPinch A) z) -
    finiteAverage (fun s : X → Bool => Real.negMulLog (gaussianQuadratic
      (signUnitary (B := B) s * A * (signUnitary (B := B) s).conjTranspose) z)) ∂γ
  rw [integral_sub hpp.1 havg, hint, hpp.2, hpa.2]
  ring

/-- Matrix subentropy is concave on the positive trace-one cone. -/
theorem matrix_subentropy_concave {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) :
    Convex ℝ {A : Matrix ι ι ℂ | A.PosSemidef ∧ A.trace = 1} ∧
    ∀ ⦃A : Matrix ι ι ℂ⦄, A.PosSemidef ∧ A.trace = 1 →
    ∀ ⦃C : Matrix ι ι ℂ⦄, C.PosSemidef ∧ C.trace = 1 →
    ∀ ⦃c d : ℝ⦄, 0 ≤ c → 0 ≤ d → c + d = 1 →
      c • matrixSubentropy A + d • matrixSubentropy C ≤
        matrixSubentropy (c • A + d • C) := by
  have hdomain : Convex ℝ
      {A : Matrix ι ι ℂ | A.PosSemidef ∧ A.trace = 1} := by
    intro A hA C hC c d hc hd hcd
    refine ⟨(hA.1.smul hc).add (hC.1.smul hd), ?_⟩
    simp only [Matrix.trace_add, Matrix.trace_smul, hA.2, hC.2]
    rw [← add_smul, hcd, one_smul]
  refine ⟨hdomain, ?_⟩
  intro A hA C hC c d hc hd hcd
  have hM := hdomain hA hC hc hd hcd
  have ha := matrix_subentropy_gaussian_entropy A hA.1 hA.2 i₀
  have hb := matrix_subentropy_gaussian_entropy C hC.1 hC.2 i₀
  have hm := matrix_subentropy_gaussian_entropy _ hM.1 hM.2 i₀
  have hbound : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℂ ι),
      c * Real.negMulLog (gaussianQuadratic A z) +
        d * Real.negMulLog (gaussianQuadratic C z) ≤
      Real.negMulLog (gaussianQuadratic (c • A + d • C) z) := by
    apply Filter.Eventually.of_forall
    intro z
    rw [quadratic_add, quadratic_real_smul, quadratic_real_smul]
    exact Real.concaveOn_negMulLog.2 (quadratic_nonnegative hA.1 z)
      (quadratic_nonnegative hC.1 z) hc hd hcd
  have hh := integral_mono_ae ((ha.1.const_mul c).add (hb.1.const_mul d)) hm.1 hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add (ha.1.const_mul c) (hb.1.const_mul d), integral_const_mul,
    integral_const_mul] at hh
  rw [ha.2, hb.2, hm.2]
  simp only [smul_eq_mul]
  have hk : c * (∫ z : (ι × Fin 2) → ℝ,
        Real.negMulLog (((z (i₀,0))^2 + (z (i₀,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) +
      d * (∫ z : (ι × Fin 2) → ℝ,
        Real.negMulLog (((z (i₀,0))^2 + (z (i₀,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) =
      (∫ z : (ι × Fin 2) → ℝ,
        Real.negMulLog (((z (i₀,0))^2 + (z (i₀,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) := by
    rw [← add_mul, hcd, one_mul]
  linarith

/-- The subentropy increase under a fixed coordinate block pinching is nonnegative
and convex throughout the positive trace-one state space. -/
theorem actual_pinching_gap_laws (i₀ : X × B) :
    ConvexOn ℝ {A : Matrix (X × B) (X × B) ℂ | A.PosSemidef ∧ A.trace = 1}
      (fun A => matrixSubentropy (blockPinch A) - matrixSubentropy A) ∧
    ∀ A : Matrix (X × B) (X × B) ℂ, A.PosSemidef → A.trace = 1 →
      0 ≤ matrixSubentropy (blockPinch A) - matrixSubentropy A := by
  have hdomain : Convex ℝ
      {A : Matrix (X × B) (X × B) ℂ | A.PosSemidef ∧ A.trace = 1} := by
    intro A hA C hC c d hc hd hcd
    refine ⟨(hA.1.smul hc).add (hC.1.smul hd), ?_⟩
    simp only [Matrix.trace_add, Matrix.trace_smul, hA.2, hC.2]
    rw [← add_smul, hcd, one_smul]
  refine ⟨⟨hdomain, ?_⟩, ?_⟩
  · intro A hA C hC c d hc hd hcd
    have hM := hdomain hA hC hc hd hcd
    have hia := pinch_gap_integral A hA.1 hA.2 i₀
    have hic := pinch_gap_integral C hC.1 hC.2 i₀
    have him := pinch_gap_integral _ hM.1 hM.2 i₀
    change matrixSubentropy (blockPinch (c • A + d • C)) -
      matrixSubentropy (c • A + d • C) ≤
      c * (matrixSubentropy (blockPinch A) - matrixSubentropy A) +
      d * (matrixSubentropy (blockPinch C) - matrixSubentropy C)
    rw [hia.2, hic.2, him.2]
    have hb : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℂ (X × B)),
        signOrbitEntropyGap (c • A + d • C) z ≤
          c * signOrbitEntropyGap A z + d * signOrbitEntropyGap C z :=
      Filter.Eventually.of_forall (fun z => (sign_orbit_gap_convex z).2 hA.1 hC.1 hc hd hcd)
    have hh := integral_mono_ae him.1 ((hia.1.const_mul c).add (hic.1.const_mul d)) hb
    simp only [Pi.add_apply] at hh
    simpa only [integral_add (hia.1.const_mul c) (hic.1.const_mul d), integral_const_mul,
      smul_eq_mul] using hh
  · intro A hA htr
    rw [(pinch_gap_integral A hA htr i₀).2]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z =>
      (sign_orbit_entropy_laws A hA z).2.2.2)

end D5.S3.Quantum.Subentropy.PinchingGap
