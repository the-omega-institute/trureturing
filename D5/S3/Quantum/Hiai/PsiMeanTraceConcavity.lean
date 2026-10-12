/- GID: D5/S3/Quantum/Hiai/PsiMeanTraceConcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/PsiMeanTraceConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Hiai mean-trace concavity by triple joint concavity and endpoint optimizers. -/

import D5.S3.Quantum.Hiai.HSMeanTraceConcavity
import D5.S3.Quantum.Hiai.ForwardTraceYoung
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

noncomputable section
namespace D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix InverseMeanVariational GeneralizedPerspectiveFunction LiebAndoTrace LownerHeinzTheorem
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

private lemma map_strict {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (φ : A ≃⋆ₐ[ℂ] B) {X : A} (hX : IsStrictlyPositive X) : IsStrictlyPositive (φ X) := by
  obtain ⟨Q, hQ, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hX
  rw [map_mul, map_star]
  exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr ⟨φ Q, hQ.map φ, rfl⟩

private lemma map_power {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (φ : A ≃⋆ₐ[ℂ] B) {X : A} (hX : IsStrictlyPositive X) (s : ℝ) :
    φ (X ^ s) = (φ X) ^ s := by
  rw [CFC.rpow_def, CFC.rpow_def]
  exact StarAlgHomClass.map_cfc φ (fun x : NNReal ↦ x ^ s) X
    (NNReal.continuousOn_rpow_const (.inl (spectrum.zero_notMem NNReal hX.isUnit)))
    (StarAlgEquiv.isometry φ).continuous hX.nonneg (map_strict φ hX).nonneg

/-- The classical base-first geometric mean, with spectral matrix powers. -/
def geometricMean (θ : ℝ) (B A : Matrix d d ℂ) : Matrix d d ℂ :=
  B ^ (1 / 2 : ℝ) * (B ^ (-1 / 2 : ℝ) * A * B ^ (-1 / 2 : ℝ)) ^ θ * B ^ (1 / 2 : ℝ)

private lemma mean_strict {A B : Matrix d d ℂ} (hA : A.PosDef) (hB : B.PosDef) (θ : ℝ) :
    IsStrictlyPositive (geometricMean θ B A) := by
  have hI := hB.isStrictlyPositive.rpow B (-1 / 2)
  have hS := hB.isStrictlyPositive.rpow B (1 / 2)
  have hm := (hI.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint A
    (B ^ (-1 / 2 : ℝ)) hI.isSelfAdjoint).2 hA.isStrictlyPositive
  exact (hS.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint
    ((B ^ (-1 / 2 : ℝ) * A * B ^ (-1 / 2 : ℝ)) ^ θ) (B ^ (1 / 2 : ℝ))
    hS.isSelfAdjoint).2 (hm.rpow _ θ)

private abbrev φ : Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)

private lemma φ_pd {A : Matrix d d ℂ} (hA : A.PosDef) : φ A ∈ pdSet := by
  have h := map_strict φ hA.isStrictlyPositive
  exact ⟨h.isSelfAdjoint, fun _ hx ↦ h.spectrum_pos hx⟩

private lemma φ_mean {A B : Matrix d d ℂ} (hA : A.PosDef) (hB : B.PosDef) (θ : ℝ) :
    φ (geometricMean θ B A) = HiaiGeometricMean.mean θ (φ B) (φ A) := by
  have hI := hB.isStrictlyPositive.rpow B (-1 / 2)
  have hm := (hI.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint A
    (B ^ (-1 / 2 : ℝ)) hI.isSelfAdjoint).2 hA.isStrictlyPositive
  have hsB := map_strict φ hB.isStrictlyPositive
  have his : CFC.sqrt (Ring.inverse (φ B)) = (φ B) ^ (-1 / 2 : ℝ) := by
    rw [CFC.sqrt_eq_rpow, CFC.inverse_eq_rpow_neg_one hsB,
      CFC.rpow_rpow (φ B) (-1) (1 / 2) (by norm_num) hsB]
    norm_num
  unfold geometricMean HiaiGeometricMean.mean
  simp only [CFC.conjSqrt_apply]
  rw [his, CFC.sqrt_eq_rpow, map_mul, map_mul, map_power φ hm,
    map_power φ hB.isStrictlyPositive, map_mul, map_mul, map_power φ hB.isStrictlyPositive]

private lemma mix_pd {A B : Matrix d d ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ((1 - t) • A + t • B).PosDef :=
  (CStarAlgebra.convexOn_ringInverse (A := Matrix d d ℂ)).1 hA.isStrictlyPositive
    hB.isStrictlyPositive (sub_nonneg.mpr ht1) ht0 (by ring) |>.posDef

/-- Gamma retains arbitrary Z and one common mixing coefficient for A, B and W. -/
def gamma (p θ : ℝ) (Z A B W : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z * W ^ (1 - p))).re

private lemma φ_gamma (p θ : ℝ) (Z : Matrix d d ℂ) {A B W : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hW : W.PosDef) :
    HiaiHSMeanTrace.gamma p θ (φ Z) (φ A) (φ B) (φ W) = gamma p θ Z A B W := by
  unfold HiaiHSMeanTrace.gamma gamma
  rw [← map_power φ hA.isStrictlyPositive, ← map_power φ hB.isStrictlyPositive,
    ← φ_mean (hA.isStrictlyPositive.rpow A p).posDef (hB.isStrictlyPositive.rpow B p).posDef,
    ← map_power φ hW.isStrictlyPositive, ← map_star φ Z,
    ← map_mul φ, ← map_mul φ, ← map_mul φ]
  change (LinearMap.trace ℂ (EuclideanSpace ℂ d)
    (Matrix.toEuclideanLin (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z * W ^ (1 - p)))).re = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun d ℂ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- Matrix triple concavity, including the empty matrix dimension and arbitrary Z. -/
theorem gamma_triple_concave {p θ t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (Z : Matrix d d ℂ)
    {A₀ A₁ B₀ B₁ W₀ W₁ : Matrix d d ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    (hW₀ : W₀.PosDef) (hW₁ : W₁.PosDef) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * gamma p θ Z A₀ B₀ W₀ + t * gamma p θ Z A₁ B₁ W₁ ≤
      gamma p θ Z ((1 - t) • A₀ + t • A₁) ((1 - t) • B₀ + t • B₁)
        ((1 - t) • W₀ + t • W₁) := by
  cases isEmpty_or_nonempty d with
  | inl hd =>
    letI := hd
    simp [gamma, Matrix.trace]
  | inr hd =>
    letI := hd
    have h := HiaiHSMeanTrace.gamma_triple_concave hp hθ (φ Z)
      (φ_pd hA₀) (φ_pd hA₁) (φ_pd hB₀) (φ_pd hB₁) (φ_pd hW₀) (φ_pd hW₁) ht0 ht1
    have hm (X Y : Matrix d d ℂ) :
        (1 - t) • φ X + t • φ Y = φ ((1 - t) • X + t • Y) := by
      simp only [map_add, ← Complex.coe_smul, map_smul]
    rw [hm, hm, hm, φ_gamma p θ Z hA₀ hB₀ hW₀, φ_gamma p θ Z hA₁ hB₁ hW₁,
      φ_gamma p θ Z (mix_pd hA₀ hA₁ ht0 ht1) (mix_pd hB₀ hB₁ ht0 ht1)
        (mix_pd hW₀ hW₁ ht0 ht1)] at h
    exact h

/-- The actual outer spectral trace power; the geometric mean base is B^p. -/
def psi (p θ : ℝ) (Z A B : Matrix d d ℂ) : ℝ :=
  tracePower (1 / p) (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z)

private lemma congruence_pd (p θ : ℝ) {A B Z : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hZ : IsUnit Z) :
    (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z).PosDef := by
  exact ((mean_strict (hA.isStrictlyPositive.rpow A p).posDef
    (hB.isStrictlyPositive.rpow B p).posDef θ).posDef).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr hZ)

/-- Exact Psi joint concavity by mixing the attained endpoint optimizers. -/
theorem psi_jointly_concave {p θ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (Z : Matrix d d ℂ) (hZ : IsUnit Z) :
    JointlyConcaveOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (psi p θ Z) := by
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  let M₀ := Zᴴ * geometricMean θ (B₀ ^ p) (A₀ ^ p) * Z
  let M₁ := Zᴴ * geometricMean θ (B₁ ^ p) (A₁ ^ p) * Z
  obtain ⟨W₀, hW₀, _, heq₀, _⟩ :=
    ForwardTraceYoung.maximum_and_attainment (congruence_pd p θ hA₀ hB₀ hZ) hp hp1
  obtain ⟨W₁, hW₁, _, heq₁, _⟩ :=
    ForwardTraceYoung.maximum_and_attainment (congruence_pd p θ hA₁ hB₁ hZ) hp hp1
  have hAm := mix_pd hA₀ hA₁ ht0 ht1
  have hBm := mix_pd hB₀ hB₁ ht0 ht1
  have hWm := mix_pd hW₀ hW₁ ht0 ht1
  have hh := gamma_triple_concave ⟨hp.le, hp1⟩ hθ Z hA₀ hA₁ hB₀ hB₁ hW₀ hW₁ ht0 ht1
  have hb := ForwardTraceYoung.forward_trace_young (congruence_pd p θ hAm hBm hZ) hWm hp hp1
  have htrace : (Matrix.trace ((1 - t) • W₀ + t • W₁)).re =
      (1 - t) * (Matrix.trace W₀).re + t * (Matrix.trace W₁).re := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hobj : (1 - t) * ForwardTraceYoung.objective p M₀ W₀ +
      t * ForwardTraceYoung.objective p M₁ W₁ ≤
      ForwardTraceYoung.objective p
        (Zᴴ * geometricMean θ (((1 - t) • B₀ + t • B₁) ^ p)
          (((1 - t) • A₀ + t • A₁) ^ p) * Z) ((1 - t) • W₀ + t • W₁) := by
    unfold ForwardTraceYoung.objective
    rw [htrace]
    dsimp [M₀, M₁]
    unfold gamma at hh
    nlinarith [hh]
  have hc := hobj.trans hb
  rw [heq₀, heq₁] at hc
  change (1 - t) * psi p θ Z A₀ B₀ + t * psi p θ Z A₁ B₁ ≤ _
  unfold psi
  nlinarith [hc]

#print axioms psi_jointly_concave
end D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
