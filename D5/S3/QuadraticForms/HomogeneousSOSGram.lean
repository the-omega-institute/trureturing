/- GID: D5/S3/QuadraticForms/HomogeneousSOSGram
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/HomogeneousSOSGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Gram matrices for native homogeneous real sums of squares. -/

import D5.S3.QuadraticForms.HomogeneousSOS
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Batteries.Tactic.OpenPrivate

/-! Finite positive Gram matrices represent the native unrestricted SOS
predicate on homogeneous forms. This is a polynomial prerequisite, not an
assumed extension-cone or GNP characterization. -/

open scoped BigOperators MatrixOrder
open MvPolynomial Matrix

namespace D5.S3.QuadraticForms.HomogeneousSOSGram

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Exponents of monomials of exactly the prescribed total degree. -/
abbrev Exponent (σ : Type*) (d : ℕ) := {a : σ →₀ ℕ // a.degree = d}

noncomputable instance (d : ℕ) : Fintype (Exponent σ d) :=
  (Finsupp.finite_of_degree_eq d).fintype

/-- The actual homogeneous polynomial with the given coefficient vector. -/
def form (d : ℕ) (v : Exponent σ d → ℝ) : MvPolynomial σ ℝ :=
  ∑ a, monomial a.val (v a)

/-- The actual monomial Gram polynomial, with no normalization factors. -/
def gram (d : ℕ) (M : Matrix (Exponent σ d) (Exponent σ d) ℝ) :
    MvPolynomial σ ℝ :=
  ∑ a, ∑ b, monomial (a.val + b.val) (M a b)

private lemma form_coeff (d : ℕ) (v : Exponent σ d → ℝ) (a : Exponent σ d) :
    (form d v).coeff a.val = v a := by
  simp only [form,coeff_sum,coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    rw [if_neg (fun h => hba (Subtype.ext h))]
  · simp

private lemma form_homogeneous (d : ℕ) (v : Exponent σ d → ℝ) :
    (form d v).IsHomogeneous d := by
  exact IsHomogeneous.sum _ _ _ (fun a _ => isHomogeneous_monomial _ a.property)

private lemma homogeneous_eq_form (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) : p = form d (fun a => p.coeff a.val) := by
  ext c
  by_cases hc : c.degree = d
  · exact (form_coeff d (fun a => p.coeff a.val) ⟨c,hc⟩).symm
  · rw [hp.coeff_eq_zero hc]
    simp only [form,coeff_sum,coeff_monomial]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have hne : a.val ≠ c := by
      intro h
      apply hc
      rw [← h]
      exact a.property
    rw [if_neg hne]

private lemma gram_rank_one (d : ℕ) (v : Exponent σ d → ℝ) :
    gram d (vecMulVec v v) = form d v * form d v := by
  simp only [gram,form,vecMulVec_apply,Finset.sum_mul,Finset.mul_sum,
    monomial_mul_monomial]
  rw [Finset.sum_comm]

private lemma gram_sum {J : Type*} [Fintype J] (d : ℕ)
    (M : J → Matrix (Exponent σ d) (Exponent σ d) ℝ) :
    gram d (∑ j, M j) = ∑ j, gram d (M j) := by
  simp only [gram,Matrix.sum_apply,map_sum]
  calc
    (∑ a, ∑ b, ∑ j, monomial (a.val + b.val) (M j a b)) =
        ∑ a, ∑ j, ∑ b, monomial (a.val + b.val) (M j a b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private lemma gram_of_square (d : ℕ)
    (A : Matrix (Exponent σ d) (Exponent σ d) ℝ) :
    gram d (Aᴴ * A) = ∑ j, form d (A j) * form d (A j) := by
  have he : Aᴴ * A = ∑ j, vecMulVec (A j) (A j) := by
    ext a b
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,Matrix.vecMulVec_apply]
  rw [he,gram_sum]
  simp_rw [gram_rank_one]

/-- A real homogeneous degree-`2*d` form is a native sum of squares if and
only if it is the actual monomial Gram polynomial of a PSD real matrix.
Zero forms, degree zero, and the empty variable type are included. -/
theorem homogeneous_sos_iff_gram (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous (2 * d)) :
    IsSumSq p ↔ ∃ M : Matrix (Exponent σ d) (Exponent σ d) ℝ,
      M.PosSemidef ∧ p = gram d M := by
  constructor
  · intro hs
    obtain ⟨m,q,hq,he⟩ := (HomogeneousSOS.homogeneous_sos_iff p d hp).mp hs
    let v (i : Fin m) (a : Exponent σ d) := (q i).coeff a.val
    refine ⟨∑ i, vecMulVec (v i) (v i),?_,?_⟩
    · exact Matrix.posSemidef_sum Finset.univ (fun i _ => by
        simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v i))
    · rw [gram_sum]
      simp_rw [gram_rank_one]
      exact he.trans (Finset.sum_congr rfl fun i _ => by
        rw [← homogeneous_eq_form (q i) d (hq i)])
  · rintro ⟨M,hM,rfl⟩
    obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
    rw [hA,Matrix.star_eq_conjTranspose,gram_of_square]
    exact IsSumSq.sum_mul_self Finset.univ _

#print axioms homogeneous_sos_iff_gram

private lemma gram_homogeneous (d : ℕ)
    (M : Matrix (Exponent σ d) (Exponent σ d) ℝ) :
    (gram d M).IsHomogeneous (2 * d) := by
  apply IsHomogeneous.sum
  intro a ha
  apply IsHomogeneous.sum
  intro b hb
  apply isHomogeneous_monomial
  rw [map_add,a.property,b.property,two_mul]

open private sum_squares_zero from D5.S3.QuadraticForms.HomogeneousSOS

private lemma gram_psd_kernel (d : ℕ)
    (M : Matrix (Exponent σ d) (Exponent σ d) ℝ)
    (hM : M.PosSemidef) (hz : gram d M = 0) : M = 0 := by
  obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  rw [hA,Matrix.star_eq_conjTranspose,gram_of_square] at hz
  have hf := sum_squares_zero _ hz
  have hAz : A = 0 := by
    ext i j
    change A i j = 0
    have hh := congrArg (fun p : MvPolynomial σ ℝ => p.coeff j.val) (hf i)
    simpa only [form_coeff,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hh
  rw [hA,hAz,star_zero,mul_zero]

private lemma closed_image_without_kernel
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (C : Set V) (hC : IsClosed C)
    (hsmul : ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → a • x ∈ C)
    (f : V →L[ℝ] W) (hker : ∀ x ∈ C, f x = 0 → x = 0) :
    IsClosed (f '' C) := by
  let K := C ∩ Metric.sphere (0 : V) 1
  have hK : IsCompact K := (isCompact_sphere 0 1).inter_left hC
  have hzero : (0 : W) ∉ f '' K := by
    rintro ⟨x,hx,hfx⟩
    have hz := hker x hx.1 hfx
    have hh := hx.2
    simp only [Metric.mem_sphere,dist_zero_right,hz,norm_zero] at hh
    norm_num at hh
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hK.image f.continuous).isClosed.isOpen_compl
    0 hzero
  have bound (x : V) (hx : x ∈ C) : ‖x‖ ≤ ‖f x‖ / ε := by
    by_cases hz : x = 0
    · simp [hz,le_of_lt hε]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hz
    have hy : ‖x‖⁻¹ • x ∈ K := by
      refine ⟨hsmul x hx _ (inv_nonneg.mpr hn.le),?_⟩
      simp [Metric.mem_sphere,dist_zero_right,norm_smul,abs_of_pos hn,ne_of_gt hn]
    have he : ε ≤ ‖f (‖x‖⁻¹ • x)‖ := by
      by_contra! hh
      exact hball (by simpa only [Metric.mem_ball,dist_zero_right] using hh) ⟨_,hy,rfl⟩
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le)] at he
    apply (le_div_iff₀ hε).mpr
    have hh := mul_le_mul_of_nonneg_right he hn.le
    field_simp at hh
    nlinarith
  rw [← isSeqClosed_iff_isClosed]
  intro u y hu hy
  choose x hx hfx using hu
  obtain ⟨R,hR,hRu⟩ := (Metric.isBounded_range_of_tendsto _ hy).exists_pos_norm_le
  have hRx (k : ℕ) : ‖x k‖ ≤ R / ε :=
    (bound _ (hx k)).trans (div_le_div_of_nonneg_right
      (by rw [hfx]; exact hRu _ ⟨k,rfl⟩) hε.le)
  obtain ⟨x₀,_,φ,hφ,hxlim⟩ := (isCompact_closedBall (0 : V) (R / ε)).tendsto_subseq
    (fun k => by simpa only [Metric.mem_closedBall,dist_zero_right] using hRx k)
  refine ⟨x₀,hC.mem_of_tendsto hxlim (Filter.Eventually.of_forall fun k => hx (φ k)),?_⟩
  have hf := f.continuous.tendsto x₀ |>.comp hxlim
  have he : (fun k => f (x (φ k))) = u ∘ φ := by
    funext k
    exact hfx (φ k)
  change Filter.Tendsto (fun k => f (x (φ k))) Filter.atTop (nhds (f x₀)) at hf
  rw [he] at hf
  exact tendsto_nhds_unique hf (hy.comp hφ.tendsto_atTop)

/-- The coefficients of the actual Gram polynomial in degree `2*d`. -/
def gramMap (d : ℕ) : Matrix (Exponent σ d) (Exponent σ d) ℝ →ₗ[ℝ]
    (Exponent σ (2 * d) → ℝ) where
  toFun M c := (gram d M).coeff c.val
  map_add' M N := by
    ext c
    simp [gram,Matrix.add_apply,Finset.sum_add_distrib]
  map_smul' a M := by
    ext c
    simp [gram,Matrix.smul_apply,Finset.mul_sum,mul_ite]

/-- Native homogeneous SOS forms, expressed in their actual monomial coefficients. -/
def sosCoefficients (d : ℕ) : Set (Exponent σ (2 * d) → ℝ) :=
  {v | IsSumSq (form (2 * d) v)}

/-- The cone of homogeneous real sums of squares of a fixed degree is closed.
The proof uses genuine PSD Gram matrices: their positive kernel is zero, so
the finite coefficient projection has closed image. -/
theorem sosCoefficients_closed (d : ℕ) : IsClosed (sosCoefficients (σ := σ) d) := by
  letI : NormedAddCommGroup (Matrix (Exponent σ d) (Exponent σ d) ℝ) :=
    inferInstanceAs (NormedAddCommGroup ((Exponent σ d) → (Exponent σ d) → ℝ))
  letI : NormedSpace ℝ (Matrix (Exponent σ d) (Exponent σ d) ℝ) :=
    inferInstanceAs (NormedSpace ℝ ((Exponent σ d) → (Exponent σ d) → ℝ))
  let f := (gramMap (σ := σ) d).toContinuousLinearMap
  have heq : sosCoefficients (σ := σ) d = f '' {M | M.PosSemidef} := by
    ext v
    constructor
    · intro hv
      obtain ⟨M,hM,hm⟩ := (homogeneous_sos_iff_gram _ d
        (form_homogeneous _ _)).mp hv
      refine ⟨M,hM,?_⟩
      funext c
      change (gram d M).coeff c.val = v c
      rw [← hm,form_coeff]
    · rintro ⟨M,hM,rfl⟩
      apply (homogeneous_sos_iff_gram _ d (form_homogeneous _ _)).mpr
      refine ⟨M,hM,?_⟩
      exact (homogeneous_eq_form _ _ (gram_homogeneous d M)).symm
  rw [heq]
  refine closed_image_without_kernel
    {M : Matrix (Exponent σ d) (Exponent σ d) ℝ | M.PosSemidef}
    Matrix.posSemidef_is_closed
    (fun M hM a ha => (show (a • M).PosSemidef from hM.smul ha)) f ?_
  intro M hM hz
  apply gram_psd_kernel d M hM
  calc
    gram d M = form (2 * d) (f M) := homogeneous_eq_form _ _ (gram_homogeneous d M)
    _ = 0 := by rw [hz]; simp [form]

#print axioms sosCoefficients_closed

end
end D5.S3.QuadraticForms.HomogeneousSOSGram
