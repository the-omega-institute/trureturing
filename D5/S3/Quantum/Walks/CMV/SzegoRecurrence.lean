/- GID: D5/S3/Quantum/Walks/CMV/SzegoRecurrence
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/CMV/SzegoRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Riesz moment and CMV identities for scale-four self-similarity. -/

/- admission_basis: escape-witness
   Module witness: monic_szego
   Direct frozen dependencies:
   D5.S3.Weil.Szego.CanonicalTransfer.szegoRho
     declaration statement_id: sha256:8155eeaa9dd1f2640bb6365ddd75a4cc9fdb1ac7d21883d8cba593787c925834
   D5.S3.Weil.Szego.CanonicalTransfer.szego_rho_pos
     declaration statement_id: sha256:b440986d62bb484d69935806c23cf6449a0f9f409fcb9c6371e31974b2b92c99
   Core.T_mem_spanOn: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeCoefficients.secondStar_window, Riesz.Decimation.Parity.odd_test_zero, Riesz.Decimation.Parity.parity_weighted_projection, Riesz.Decimation.Assembly.small_projection, Riesz.Decimation.Assembly.J_into_residue, Riesz.Decimation.Assembly.J_W_into_V, Riesz.Decimation.Assembly.large_projection.
   Core.spanOn_mono: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.SzegoRecurrence.Core.E_le_W, CMV.SzegoRecurrence.Core.E_le_even, CMV.SzegoRecurrence.OPUCNormalization.phiStar_below, Riesz.Decimation.Assembly.E_le_V.
   Core.form_zero_on_span: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.SzegoRecurrence.Core.residue_class_orthogonal, CMV.SzegoRecurrence.OPUCFinite.phi_orthogonal_span, CMV.SzegoRecurrence.OPUCRecurrence.zero_of_window_orthogonal, CMV.SzegoRecurrence.GramOPUC.gram_even, CMV.SzegoRecurrence.GramOPUC.gram_odd, Riesz.Decimation.Parity.parity_weighted_projection, Riesz.Decimation.Assembly.small_projection, Riesz.Decimation.Assembly.large_projection.
   Core.residue_class_orthogonal: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Parity.odd_test_zero, Riesz.Decimation.Assembly.large_projection.
   Core.E_le_W: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.SzegoRecurrence.Windows.E_finite, Riesz.Decimation.Parity.parity_weighted_projection.
   Core.E_le_even: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Parity.parity_weighted_projection, Riesz.Decimation.Assembly.small_projection.
   Core.projection_unique: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.SzegoRecurrence.GramOPUC.gram_characterization, Riesz.Decimation.FiniteScaling.projection_norm_scale_four.
   Existence.finite_projection_exists: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: Riesz.Decimation.FiniteScaling.scaled_projections_exist.
   ProjectionNorm.finite_orthonormal_projection: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Representation.SpectralReduction.cumulative_projection.
   GramBasis.chi_orthonormal: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: RieszWalkSelfSimilarity.cumulative_scale_four.
   GramBasis.chi_window: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: RieszWalkSelfSimilarity.cumulative_scale_four.
   GramBasis.chi_zero: proof_shape: content; escape_witness: Riesz.Moments.coeff_outside
     Direct frozen dependencies: none; consumers: CMV.Representation.CMVFromGramParameters.pair_relations_of_parameters, RieszWalkSelfSimilarity.cumulative_scale_four.
   FormSymmetries.sigma_shift: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.numerator_leading, CMV.SzegoRecurrence.FormSymmetries.sigma_shift_adjoint, CMV.SzegoRecurrence.OPUCFinite.phiStar_norm, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_orthogonal, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.OPUCNormalization.normSquare_succ, CMV.SzegoRecurrence.GramOPUC.gram_even, CMV.SzegoRecurrence.GramOPUC.gram_odd, CMV.SzegoRecurrence.GramOPUC.chi_even, CMV.SzegoRecurrence.GramOPUC.chi_odd.
   FormSymmetries.sigma_shift_adjoint: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Representation.BandedBridge.one_step_of_pair_relations.
   OPUCFinite.coeffLM_T: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PolynomialSeries.polynomial_expansion, CMV.Geronimus.PolynomialSeries.asPS_T, CMV.Geronimus.PadeLeadingTerms.denominator_leading, CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.SzegoRecurrence.OPUCFinite.coeff_window_zero, CMV.SzegoRecurrence.OPUCFinite.phi_monic, CMV.SzegoRecurrence.OPUCRecurrence.coeffLM_shift, CMV.SzegoRecurrence.GramOPUC.gram_even, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCFinite.mem_spanOn_iff: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.denominator_leading, CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.Geronimus.PadeRecurrence.second_window, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_mem_window, CMV.SzegoRecurrence.OPUCRecurrence.reverse_orthogonal_unique, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.GramOPUC.gram_even, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCFinite.phi_mem_window: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.denominator_coefficient, CMV.Geronimus.PadeLeadingTerms.denominator_leading, CMV.Geronimus.PadeNumerator.star_product_above, CMV.Geronimus.PadeRecurrence.secondStar_succ, CMV.Geronimus.numerator_succ, CMV.Geronimus.denominator_succ, CMV.Geronimus.phi_zero, CMV.Representation.CMVFromGramParameters.normalizedPhi_zero, CMV.SzegoRecurrence.OPUCFinite.phi_monic, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_coeff_zero, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCFinite.coeff_window_zero: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PolynomialSeries.polynomial_expansion, CMV.Geronimus.SeriesShift.asPS_shift, CMV.Geronimus.PadeLeadingTerms.denominator_leading, CMV.Geronimus.PadeRecurrence.second_window, CMV.Geronimus.PadeRecurrence.secondStar_succ, CMV.SzegoRecurrence.OPUCFinite.phi_monic, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_coeff_zero, CMV.SzegoRecurrence.OPUCRecurrence.reverse_orthogonal_unique, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCFinite.phi_monic: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.denominator_leading, CMV.Geronimus.phi_zero, CMV.Representation.CMVFromGramParameters.normalizedPhi_zero, CMV.SzegoRecurrence.OPUCFinite.phi_nonzero, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_constant, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCFinite.phi_orthogonal: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.denominator_low_zero, CMV.Geronimus.PadeNumerator.numerator_leading, CMV.SzegoRecurrence.OPUCFinite.phi_orthogonal_span, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_orthogonal, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCFinite.phi_orthogonal_span: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeLeadingTerms.denominator_leading, CMV.SzegoRecurrence.OPUCNormalization.cross_moment.
   OPUCFinite.phiStar_norm: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.SzegoRecurrence.OPUCNormalization.cross_moment, CMV.SzegoRecurrence.OPUCNormalization.normSquare_succ, CMV.SzegoRecurrence.GramOPUC.chi_even.
   OPUCRecurrence.coeffLM_shift: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeCoefficients.phiStar_coeff_reflected, CMV.Geronimus.PadeCoefficients.second_coeff, CMV.Geronimus.SeriesShift.asPS_shift, CMV.Geronimus.PadeRecurrence.second_window, CMV.Geronimus.PadeRecurrence.secondStar_succ, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_constant, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_coeff_zero, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego, CMV.SzegoRecurrence.GramOPUC.gram_even, CMV.SzegoRecurrence.GramOPUC.gram_odd.
   OPUCRecurrence.coeffLM_invert: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeCoefficients.phiStar_coeff_reflected, CMV.Geronimus.PadeCoefficients.second_coeff, CMV.Geronimus.PadeRecurrence.second_window, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_constant, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_coeff_zero.
   OPUCRecurrence.phiStar_constant: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.SzegoRecurrence.OPUCRecurrence.reverse_orthogonal_unique, CMV.SzegoRecurrence.GramOPUC.gram_even.
   OPUCRecurrence.phiStar_coeff_zero: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.SzegoRecurrence.OPUCRecurrence.phiStar_mem_window, CMV.SzegoRecurrence.OPUCRecurrence.reverse_orthogonal_unique, CMV.SzegoRecurrence.GramOPUC.gram_even.
   OPUCRecurrence.phiStar_orthogonal: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.phiStar_origin_moment, CMV.SzegoRecurrence.OPUCRecurrence.reverse_orthogonal_unique, CMV.SzegoRecurrence.GramOPUC.gram_even.
   OPUCRecurrence.phiStar_mem_window: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeCoefficients.second_coeff_sum, CMV.Geronimus.PadeNumerator.star_product_above, CMV.SzegoRecurrence.OPUCNormalization.phiStar_below.
   OPUCRecurrence.monic_szego: proof_shape: content; escape_witness: CMV.SzegoRecurrence.OPUCRecurrence.monic_szego
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeNumerator.numerator_leading, CMV.Geronimus.denominator_succ, CMV.SzegoRecurrence.OPUCNormalization.cross_moment, CMV.SzegoRecurrence.OPUCNormalization.normSquare_succ, CMV.SzegoRecurrence.OPUCNormalization.normalized_szego, CMV.SzegoRecurrence.OPUCStarRecurrence.monic_star_szego, CMV.SzegoRecurrence.OPUCStarRecurrence.normalized_star_inverse.
   OPUCNormalization.normSquare_pos: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: none; consumers: CMV.Geronimus.schur_equals_gram, CMV.SzegoRecurrence.OPUCNormalization.verblunsky_sq_lt_one, CMV.SzegoRecurrence.OPUCNormalization.gramNorm_pos, CMV.SzegoRecurrence.GramOPUC.norm_of_gram_square.
   OPUCNormalization.verblunsky_sq_lt_one: proof_shape: content; escape_witness: CMV.SzegoRecurrence.OPUCRecurrence.monic_szego
     Direct frozen dependencies: none; consumers: CMV.Geronimus.schur_equals_gram, CMV.SzegoRecurrence.OPUCNormalization.gramRho_pos, CMV.SzegoRecurrence.OPUCNormalization.gramNorm_succ, CMV.SzegoRecurrence.OPUCStarRecurrence.normalized_star_inverse.
   OPUCNormalization.normalized_szego: proof_shape: content; escape_witness: CMV.SzegoRecurrence.OPUCRecurrence.monic_szego
     Direct frozen dependencies: szegoRho, szego_rho_pos; consumers: CMV.Representation.CMVFromGramParameters.pair_relations_of_parameters.
   OPUCStarRecurrence.monic_star_szego: proof_shape: content; escape_witness: CMV.SzegoRecurrence.OPUCRecurrence.monic_szego
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PadeRecurrence.secondStar_succ, CMV.Geronimus.numerator_succ, CMV.SzegoRecurrence.OPUCStarRecurrence.normalized_star_inverse.
   OPUCStarRecurrence.normalized_star_inverse: proof_shape: content; escape_witness: CMV.SzegoRecurrence.OPUCRecurrence.monic_szego
     Direct frozen dependencies: szegoRho, szego_rho_pos; consumers: CMV.Representation.CMVFromGramParameters.pair_relations_of_parameters.
   GramOPUC.chi_even: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: none; consumers: CMV.Representation.CMVFromGramParameters.pair_relations_of_parameters.
   GramOPUC.chi_odd: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: none; consumers: CMV.Representation.CMVFromGramParameters.pair_relations_of_parameters.
   Finite projection uses BilinForm.restrict and BilinForm.toDual;
   Gram-Schmidt and its orthonormality and span laws use Mathlib owners.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15854
-/

import D5.S3.Quantum.Walks.Riesz.Moments
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import D5.S3.Weil.Szego.CanonicalTransfer

open LaurentPolynomial
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive
open LaurentPolynomial

def residue (d a : ℤ) : Submodule ℝ (LaurentPolynomial ℝ) := (Submodule.span ℝ (T '' {e | e % d = a}))
def W (x : ℕ) : Submodule ℝ (LaurentPolynomial ℝ) := (Submodule.span ℝ (T '' {e | -(2*x : ℤ) ≤ e ∧ e ≤ 2*x}))
def E (x : ℕ) : Submodule ℝ (LaurentPolynomial ℝ) := (Submodule.span ℝ (T '' {e | -(2*x : ℤ) ≤ e ∧ e ≤ 2*x ∧ e % 2 = 0}))

def IsProjection (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (V : Submodule ℝ (LaurentPolynomial ℝ)) (f h : (LaurentPolynomial ℝ)) : Prop :=
  h ∈ V ∧ ∀ q ∈ V, B q (f-h) = 0

theorem T_mem_spanOn {S : Set ℤ} {e : ℤ} (he : e ∈ S) :
    (T e : (LaurentPolynomial ℝ)) ∈ (Submodule.span ℝ (T '' S)) :=
  Submodule.subset_span ⟨e, he, rfl⟩

theorem spanOn_mono {S S' : Set ℤ} (h : S ⊆ S') :
    Submodule.span ℝ ((T : ℤ → LaurentPolynomial ℝ) '' S) ≤ Submodule.span ℝ (T '' S') :=
  Submodule.span_mono (Set.image_mono h)

theorem form_zero_on_span (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (S : Set ℤ) (r : (LaurentPolynomial ℝ))
    (h : ∀ e ∈ S, B (T e) r = 0) : ∀ q ∈ (Submodule.span ℝ (T '' S)), B q r = 0 := by
  intro q hq
  induction hq using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨e, he, rfl⟩ := hq
      exact h e he
  | zero => simp
  | add q q' hq hq' ih ih' => simp [ih, ih']
  | smul a q hq ih => simp [ih]

theorem residue_class_orthogonal (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (d a b : ℤ) (hab : a ≠ b)
    (hmon : ∀ i j : ℤ, i % d ≠ j % d → B (T i) (T j) = 0) :
    ∀ p ∈ residue d a, ∀ q ∈ residue d b, B p q = 0 := by
  intro p hp q hq
  apply form_zero_on_span B _ q ?_ p hp
  intro i hi
  change i % d = a at hi
  induction hq using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨j, hj, rfl⟩ := hq
      change j % d = b at hj
      exact hmon i j (by simpa [hi, hj] using hab)
  | zero => simp
  | add q q' hq hq' ih ih' => simp [ih, ih']
  | smul c q hq ih => simp [ih]

theorem E_le_W (x : ℕ) : E x ≤ W x :=
  spanOn_mono (by intro e he; exact ⟨he.1, he.2.1⟩)

theorem E_le_even (x : ℕ) : E x ≤ residue 2 0 :=
  spanOn_mono (by intro e he; exact he.2.2)

/-- Positive definiteness makes the finite projection equations unambiguous. -/
theorem projection_unique (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (V : Submodule ℝ (LaurentPolynomial ℝ))
    (hpos : ∀ p : (LaurentPolynomial ℝ), p ≠ 0 → 0 < B p p)
    {f h k : (LaurentPolynomial ℝ)} (hh : IsProjection B V f h) (hk : IsProjection B V f k) : h = k := by
  have hdiff := V.sub_mem hh.1 hk.1
  have h1 := hh.2 (h-k) hdiff
  have h2 := hk.2 (h-k) hdiff
  have heq : B (h-k) (h-k) = 0 := by
    have hex : h-k = (f-k) - (f-h) := by abel
    calc
      B (h-k) (h-k) = B (h-k) ((f-k) - (f-h)) := congrArg (B (h-k)) hex
      _ = 0 := by rw [map_sub, h2, h1]; simp
  by_contra hne
  have hn : h-k ≠ 0 := sub_ne_zero.mpr hne
  exact (ne_of_gt (hpos _ hn)) heq

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core

/-- The finite Gram system has a unique solution even in an infinite ambient
Laurent space. No completion or measure existence is needed. -/
theorem finite_projection_exists (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (V : Submodule ℝ (LaurentPolynomial ℝ))
    [FiniteDimensional ℝ V] (hpos : ∀ p : (LaurentPolynomial ℝ), p ≠ 0 → 0 < B p p) (f : (LaurentPolynomial ℝ)) :
    ∃ h : (LaurentPolynomial ℝ), IsProjection B V f h := by
  let C := (LinearMap.BilinForm.restrict B V).flip
  have hn : C.Nondegenerate := by
    constructor <;> intro v hv <;> apply Subtype.ext <;>
      by_contra hne
    · exact (ne_of_gt (hpos v hne)) (hv v)
    · exact (ne_of_gt (hpos v hne)) (hv v)
  let rhs : Module.Dual ℝ V := (B.flip f).comp V.subtype
  let h : V := (C.toDual hn).symm rhs
  refine ⟨h, h.property, ?_⟩
  intro q hq
  have heq := LinearMap.BilinForm.apply_toDual_symm_apply (B := C) (hB := hn) rhs ⟨q,hq⟩
  change B q (h : LaurentPolynomial ℝ) = B q f at heq
  rw [map_sub,heq,sub_self]

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.ProjectionNorm
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core

/-- The finite Parseval step used by Lemma 1. -/
theorem finite_orthonormal_projection (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (v : ℕ → (LaurentPolynomial ℝ))
    (horth : ∀ i j : ℕ, B (v i) (v j) = if i=j then 1 else 0)
    (N : ℕ) (f : (LaurentPolynomial ℝ)) :
    let V := Submodule.span ℝ (v '' {j | j<N})
    let h := ∑ j ∈ Finset.range N, B (v j) f • v j
    IsProjection B V f h ∧ B h h = ∑ j ∈ Finset.range N, (B (v j) f)^2 := by
  dsimp
  let h := ∑ j ∈ Finset.range N, B (v j) f • v j
  have hh : h ∈ Submodule.span ℝ (v '' {j | j<N}) := by
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j,Finset.mem_range.mp hj,rfl⟩
  have hi : ∀ i : ℕ, i<N → B (v i) h = B (v i) f := by
    intro i hi
    dsimp [h]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul,horth]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji,Ne.symm hji]
    · intro hnot; exact (hnot (Finset.mem_range.mpr hi)).elim
  constructor
  · refine ⟨hh,?_⟩
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i,hiN,rfl⟩ := hq
      change B (v i) (f-h)=0
      rw [map_sub,hi i hiN,sub_self]
    | zero => simp
    | add p q hp hq ih ih' => simp [ih,ih']
    | smul a q hq ih => simp [ih]
  · change B h h = _
    dsimp [h] at ⊢
    rw [map_sum B]
    simp only [LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hiN
    have hi' := hi i (Finset.mem_range.mp hiN)
    change B (v i) f * B (v i) h = (B (v i) f)^2
    rw [hi',pow_two]

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.ProjectionNorm
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence
/-- The asymmetric physical-site window from the paper's Gram-Schmidt order. -/
def V (Y : ℕ) : Submodule ℝ (LaurentPolynomial ℝ) := (Submodule.span ℝ (T '' {e | -(Y:ℤ) ≤ e ∧ e ≤ (Y:ℤ)+1}))

instance W_finite (x : ℕ) : FiniteDimensional ℝ (W x) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Icc (-(2*x:ℤ)) (2*x:ℤ)).image T)

instance E_finite (x : ℕ) : FiniteDimensional ℝ (E x) :=
  Submodule.finiteDimensional_of_le (E_le_W x)


end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence
open D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows LaurentPolynomial

/-- Real symmetry of the Toeplitz form. -/
private theorem sigma_symm (p q : (LaurentPolynomial ℝ)) : sigma p q = sigma q p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => simp only [map_add,LinearMap.add_apply,hp,hp']
  | C_mul_T i a =>
    rw [←smul_eq_C_mul]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    congr 1
    induction q using LaurentPolynomial.induction_on' with
    | add q q' hq hq' => simp only [map_add,LinearMap.add_apply,hq,hq']
    | C_mul_T j b =>
      rw [←smul_eq_C_mul]
      simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,sigma,momentForm_T_T]
      have hneg : i-j=-(j-i) := by ring
      rw [hneg,moment_neg]

@[instance, instance_reducible] def innerCore : InnerProductSpace.Core ℝ (LaurentPolynomial ℝ) where
  inner := fun x y => sigma x y
  conj_inner_symm x y := by simpa using sigma_symm y x
  re_inner_nonneg x := by
    by_cases hx : x=0
    · simp [hx]
    · exact le_of_lt (riesz_positive_definite x hx)
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hn
    exact (ne_of_gt (riesz_positive_definite x hn)) hx

private instance rieszInstance2 : NormedAddCommGroup (LaurentPolynomial ℝ) := innerCore.toNormedAddCommGroup
private instance rieszInstance3 : InnerProductSpace ℝ (LaurentPolynomial ℝ) := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (LaurentPolynomial ℝ))

/-- The literal exponent ordering 0,1,-1,2,-2,... . -/
def exponent (j : ℕ) : ℤ := if j%2=0 then -(j/2:ℕ) else (j/2:ℕ)+1

private theorem exponent_even (j : ℕ) : exponent (2*j)=-(j:ℤ) := by simp [exponent]
private theorem exponent_odd (j : ℕ) : exponent (2*j+1)=(j:ℤ)+1 := by
  have hm : (2*j+1)%2=1 := by omega
  have hd : (2*j+1)/2=j := by omega
  simp [exponent,hm,hd]

private theorem exponent_injective : Function.Injective exponent := by
  intro i j hij
  by_cases hi : i%2=0 <;> by_cases hj : j%2=0 <;>
    simp only [exponent,hi,hj,ite_true,ite_false] at hij <;> omega

def monomials (j : ℕ) : (LaurentPolynomial ℝ) := T (exponent j)
def chi : ℕ → (LaurentPolynomial ℝ) := InnerProductSpace.gramSchmidtNormed ℝ monomials

private theorem monomials_independent : LinearIndependent ℝ monomials := by
  have h := (AddMonoidAlgebra.basis ℤ ℝ).linearIndependent.comp exponent exponent_injective
  convert h using 1
  funext j
  rw [Function.comp_apply,AddMonoidAlgebra.basis_apply]
  rfl

theorem chi_orthonormal : ∀ i j : ℕ, sigma (chi i) (chi j)=if i=j then 1 else 0 := by
  have h := InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜:=ℝ) monomials_independent
  intro i j
  exact (orthonormal_iff_ite.mp h) i j

/-- The endpoint bookkeeping in Lemma 1 is faithful to the paper's ordering. -/
private theorem monomial_window (Y : ℕ) :
    monomials '' {j | j<2*Y+2} = T '' {e : ℤ | -(Y:ℤ)≤e ∧ e≤(Y:ℤ)+1} := by
  ext p
  constructor
  · rintro ⟨j,hj,rfl⟩
    change j<2*Y+2 at hj
    refine ⟨exponent j,?_,rfl⟩
    dsimp [exponent]
    split_ifs <;> omega
  · rintro ⟨e,he,rfl⟩
    change -(Y:ℤ)≤e ∧ e≤(Y:ℤ)+1 at he
    by_cases hs : e≤0
    · refine ⟨2*(-e).toNat,?_,?_⟩
      · change 2*(-e).toNat<2*Y+2
        have he0 : 0≤-e := by omega
        have hen : ((-e).toNat:ℤ)=-e := Int.toNat_of_nonneg he0
        omega
      · change T (exponent (2*(-e).toNat))=T e
        rw [exponent_even,Int.toNat_of_nonneg (by omega)]
        congr 1
        ring
    · refine ⟨2*(e-1).toNat+1,?_,?_⟩
      · change 2*(e-1).toNat+1<2*Y+2
        have hen : ((e-1).toNat:ℤ)=e-1 := Int.toNat_of_nonneg (by omega)
        omega
      · change T (exponent (2*(e-1).toNat+1))=T e
        rw [exponent_odd,Int.toNat_of_nonneg (by omega)]
        congr 1
        ring

theorem chi_window (Y : ℕ) : Submodule.span ℝ (chi '' {j | j<2*Y+2})=V Y := by
  rw [chi,InnerProductSpace.span_gramSchmidtNormed]
  change Submodule.span ℝ (InnerProductSpace.gramSchmidt ℝ monomials ''
    Set.Iio (2*Y+2))=V Y
  rw [InnerProductSpace.span_gramSchmidt_Iio]
  change Submodule.span ℝ (monomials '' {j | j<2*Y+2})=V Y
  rw [monomial_window]
  rfl

/-- Normalization at the cyclic vector. -/
theorem chi_zero : chi 0 = T 0 := by
  have hm : rieszMoment 0=1 := by
    simpa using moment_closed_form SignedRep.base
  have hsq : ‖(T 0 : (LaurentPolynomial ℝ))‖^2=1 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℝ)]
    change sigma (T 0) (T 0)=1
    simp only [sigma,momentForm_T_T,sub_self,hm]
    norm_num
  have hn : ‖(T 0 : (LaurentPolynomial ℝ))‖=1 := by nlinarith [norm_nonneg (T 0 : (LaurentPolynomial ℝ))]
  have hg : InnerProductSpace.gramSchmidt ℝ monomials 0=monomials 0 :=
    InnerProductSpace.gramSchmidt_bot (𝕜:=ℝ) monomials
  rw [chi,InnerProductSpace.gramSchmidtNormed,hg]
  change ‖(T 0 : (LaurentPolynomial ℝ))‖⁻¹ • T 0 = T 0
  rw [hn,inv_one,one_smul]


end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis LaurentPolynomial

/-- Multiplication by any Laurent monomial preserves the moment form. -/
theorem sigma_shift (e : ℤ) (p q : (LaurentPolynomial ℝ)) :
    sigma (T e*p) (T e*q)=sigma p q := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => simp only [mul_add,map_add,LinearMap.add_apply,hp,hp']
  | C_mul_T i a =>
    rw [←smul_eq_C_mul]
    simp only [mul_smul_comm,map_smul,LinearMap.smul_apply,smul_eq_mul]
    congr 1
    induction q using LaurentPolynomial.induction_on' with
    | add q q' hq hq' => simp only [mul_add,map_add,hq,hq']
    | C_mul_T j b =>
      rw [←smul_eq_C_mul]
      simp only [mul_smul_comm,map_smul,smul_eq_mul]
      congr 1
      rw [←T_add,←T_add]
      simp only [sigma,momentForm_T_T]
      congr 2
      ring

/-- The adjoint relation needed for the paper's transpose convention. -/
theorem sigma_shift_adjoint (e : ℤ) (p q : (LaurentPolynomial ℝ)) :
    sigma p (T (-e)*q)=sigma (T e*p) q := by
  have h := sigma_shift e p (T (-e)*q)
  rw [←mul_assoc,←T_add,add_neg_cancel,T_zero,one_mul] at h
  exact h.symm

/-- Real Laurent inversion is an isometry because the moments are symmetric. -/
private theorem sigma_invert (p q : (LaurentPolynomial ℝ)) : sigma (invert p) (invert q)=sigma p q := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => simp only [map_add,LinearMap.add_apply,hp,hp']
  | C_mul_T i a =>
    rw [←smul_eq_C_mul]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    congr 1
    induction q using LaurentPolynomial.induction_on' with
    | add q q' hq hq' => simp only [map_add,hq,hq']
    | C_mul_T j b =>
      rw [←smul_eq_C_mul]
      simp only [map_smul,smul_eq_mul,invert_T,sigma,momentForm_T_T]
      congr 1
      rw [show -j- -i=-(j-i) by ring,D5.S3.Quantum.Walks.Riesz.Moments.moment_neg]

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries LaurentPolynomial

def coeffLM (e : ℤ) : (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ :=
  (Finsupp.lapply e).comp (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem coeffLM_T (e j : ℤ) : coeffLM e (T j)=if e=j then 1 else 0 := by
  simp [coeffLM,T,Finsupp.single_apply,-LaurentPolynomial.single_eq_C_mul_T,eq_comm]

theorem mem_spanOn_iff (S : Set ℤ) (p : (LaurentPolynomial ℝ)) :
    p ∈ (Submodule.span ℝ (T '' S)) ↔ ∀ e ∉ S, coeffLM e p=0 := by
  change p ∈ Submodule.span ℝ ((fun e : ℤ => AddMonoidAlgebra.single e 1) '' S) ↔ _
  rw [←AddMonoidAlgebra.supported_eq_span_single,AddMonoidAlgebra.mem_supported']
  rfl

def polyWindow (n : ℕ) : Submodule ℝ (LaurentPolynomial ℝ) := (Submodule.span ℝ (T '' {e | 0≤e ∧ e≤(n:ℤ)}))
def polyBelow (n : ℕ) : Submodule ℝ (LaurentPolynomial ℝ) := (Submodule.span ℝ (T '' {e | 0≤e ∧ e<(n:ℤ)}))
def phi : ℕ → (LaurentPolynomial ℝ) := InnerProductSpace.gramSchmidt ℝ (fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ))

theorem phi_mem_window (n : ℕ) : phi n ∈ polyWindow n := by
  have h := InnerProductSpace.gramSchmidt_mem_span ℝ (fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ)) (le_refl n)
  apply Submodule.span_mono ?_ h
  rintro p ⟨j,hj,rfl⟩
  change j≤n at hj
  refine ⟨(j:ℤ),⟨by omega,by omega⟩,rfl⟩

theorem coeff_window_zero (n : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n)
    (e : ℤ) (he : e<0 ∨ (n:ℤ)<e) : coeffLM e p=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨j,hj,rfl⟩ := hp
    rw [coeffLM_T]
    have hne : e≠j := by change 0≤j ∧ j≤(n:ℤ) at hj; omega
    simp [hne]
  | zero => simp
  | add p q hp hq ih ih' => simp [ih,ih']
  | smul a p hp ih => simp [ih]

/-- Every monic Gram polynomial has degree exactly n, without any measure
completion or abstract polynomial-degree normalization. -/
theorem phi_monic (n : ℕ) : coeffLM (n:ℤ) (phi n)=1 := by
  have h := congrArg (coeffLM (n:ℤ))
    (InnerProductSpace.gramSchmidt_def'' ℝ (fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ)) n)
  change coeffLM (n:ℤ) (T (n:ℤ)) = coeffLM (n:ℤ) (phi n) +
    coeffLM (n:ℤ) (∑ i ∈ Finset.Iio n,
      (inner ℝ (phi i) ((fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ)) n) / (‖phi i‖:ℝ)^2) • phi i) at h
  have hz : coeffLM (n:ℤ) (∑ i ∈ Finset.Iio n,
      (inner ℝ (phi i) ((fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ)) n) / (‖phi i‖:ℝ)^2) • phi i)=0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul,coeff_window_zero i (phi_mem_window i) (n:ℤ)
      (Or.inr (by have h := Finset.mem_Iio.mp hi; omega))]
    simp
  simp only [hz,coeffLM_T,if_pos rfl,add_zero] at h
  exact h.symm

private theorem phi_nonzero (n : ℕ) : phi n≠0 := by
  intro h
  have hc := phi_monic n
  rw [h,map_zero] at hc
  norm_num at hc

/-- The finite orthogonality conditions defining OPUC. -/
theorem phi_orthogonal (n : ℕ) (e : ℤ) (he : 0≤e ∧ e<(n:ℤ)) :
    sigma (T e) (phi n)=0 := by
  have hen : (e.toNat:ℤ)=e := Int.toNat_of_nonneg he.1
  have hlt : e.toNat<n := by omega
  have h := InnerProductSpace.gramSchmidt_inv_triangular ℝ (fun n : ℕ => (T (n:ℤ) : LaurentPolynomial ℝ)) hlt
  change sigma (phi n) (T (e.toNat:ℤ))=0 at h
  rw [hen,←sigma_symm] at h
  exact h

/-- Orthogonality extends to the whole lower polynomial window. -/
theorem phi_orthogonal_span (n : ℕ) : ∀ q ∈ polyBelow n, sigma q (phi n)=0 :=
  form_zero_on_span sigma _ _ (fun e he => phi_orthogonal n e he)

/-- The reverse polynomial is explicit Laurent inversion and shift. -/
def phiStar (n : ℕ) : (LaurentPolynomial ℝ) := T (n:ℤ)*invert (phi n)

theorem phiStar_norm (n : ℕ) : sigma (phiStar n) (phiStar n)=sigma (phi n) (phi n) := by
  rw [phiStar,sigma_shift,sigma_invert]

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite
end

open LaurentPolynomial
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite LaurentPolynomial

/-- Coefficient-level identities for polynomial reflection. -/
theorem coeffLM_shift (e i : ℤ) (p : (LaurentPolynomial ℝ)) : coeffLM e (T i*p)=coeffLM (e-i) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | C_mul_T j a =>
    rw [←smul_eq_C_mul]
    simp only [mul_smul_comm,map_smul,smul_eq_mul]
    rw [←T_add,coeffLM_T,coeffLM_T]
    congr 1
    simp only [show e=i+j ↔ e-i=j by omega]

theorem coeffLM_invert (e : ℤ) (p : (LaurentPolynomial ℝ)) : coeffLM e (invert p)=coeffLM (-e) p := by
  change (invert p).coeff e=p.coeff (-e)
  exact invert_apply p e

theorem phiStar_constant (n : ℕ) : coeffLM 0 (phiStar n)=1 := by
  rw [phiStar,coeffLM_shift,zero_sub,coeffLM_invert,neg_neg,phi_monic]

theorem phiStar_coeff_zero (n : ℕ) (e : ℤ) (he : e<0 ∨ (n:ℤ)<e) :
    coeffLM e (phiStar n)=0 := by
  rw [phiStar,coeffLM_shift,coeffLM_invert]
  apply coeff_window_zero n (phi_mem_window n)
  omega

/-- Reflecting the finite orthogonality window gives tests 1,...,n. -/
theorem phiStar_orthogonal (n : ℕ) (e : ℤ) (he : 1≤e ∧ e≤(n:ℤ)) :
    sigma (T e) (phiStar n)=0 := by
  have h := sigma_shift (n:ℤ) (T (e-n)) (invert (phi n))
  have hexp : (n:ℤ)+(e-n)=e := by ring
  rw [←T_add,hexp] at h
  rw [phiStar,h]
  have h' := sigma_invert (T ((n:ℤ)-e)) (phi n)
  rw [invert_T,show -((n:ℤ)-e)=e-n by ring] at h'
  rw [h']
  exact phi_orthogonal n ((n:ℤ)-e) (by omega)

theorem phiStar_mem_window (n : ℕ) : phiStar n ∈ polyWindow n := by
  apply (mem_spanOn_iff _ _).mpr
  intro e he
  apply phiStar_coeff_zero
  change ¬(0≤e ∧ e≤(n:ℤ)) at he
  omega

private theorem zero_of_window_orthogonal (S : Set ℤ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ (Submodule.span ℝ (T '' S)))
    (horth : ∀ e ∈ S, sigma (T e) p=0) : p=0 := by
  have hz := form_zero_on_span sigma S p horth p hp
  by_contra hn
  exact (ne_of_gt (riesz_positive_definite p hn)) hz

/-- A polynomial orthogonal to z,...,z^n is a scalar multiple of Phi_n*. -/
private theorem reverse_orthogonal_unique (n : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n)
    (horth : ∀ e : ℤ, 1≤e → e≤(n:ℤ) → sigma (T e) p=0) :
    p=coeffLM 0 p • phiStar n := by
  let r := p-coeffLM 0 p • phiStar n
  have hr : r ∈ (Submodule.span ℝ (T '' {e : ℤ | 1≤e ∧ e≤(n:ℤ)})) := by
    apply (mem_spanOn_iff _ _).mpr
    intro e he
    change ¬(1≤e ∧ e≤(n:ℤ)) at he
    by_cases he0 : e=0
    · subst e
      simp [r,phiStar_constant]
    · have heout : e<0 ∨ (n:ℤ)<e := by omega
      dsimp [r]
      rw [map_sub,map_smul,coeff_window_zero n hp e heout,phiStar_coeff_zero n e heout]
      simp
  have hz : r=0 := zero_of_window_orthogonal _ hr (by
    intro e he
    change 1≤e ∧ e≤(n:ℤ) at he
    simp [r,horth e he.1 he.2,phiStar_orthogonal n e he])
  exact sub_eq_zero.mp hz

/-- The monic Szego coefficient is a finite Gram quantity, before Geronimus. -/
def verblunsky (n : ℕ) : ℝ := -coeffLM 0 (phi (n+1))

/-- Szego recursion derived solely from finite orthogonality and positivity. -/
theorem monic_szego (n : ℕ) :
    phi (n+1)=T 1*phi n-verblunsky n • phiStar n := by
  let r := T 1*phi n-phi (n+1)
  have hr : r ∈ polyWindow n := by
    apply (mem_spanOn_iff _ _).mpr
    intro e he
    change ¬(0≤e ∧ e≤(n:ℤ)) at he
    dsimp [r]
    rw [map_sub,coeffLM_shift]
    by_cases het : e=(n:ℤ)+1
    · subst e
      rw [show (n:ℤ)+1-1=(n:ℤ) by ring,phi_monic,
        show (n:ℤ)+1=((n+1:ℕ):ℤ) by push_cast; rfl,phi_monic,sub_self]
    · have hlow : e<0 ∨ (n:ℤ)+1<e := by omega
      rw [coeff_window_zero n (phi_mem_window n) (e-1) (by omega),
        coeff_window_zero (n+1) (phi_mem_window (n+1)) e (by push_cast; omega)]
      simp
  have hort : ∀ e : ℤ, 1≤e → e≤(n:ℤ) → sigma (T e) r=0 := by
    intro e hlo hhi
    dsimp [r]
    rw [map_sub]
    have hs := sigma_shift 1 (T (e-1)) (phi n)
    rw [←T_add,show (1:ℤ)+(e-1)=e by ring] at hs
    rw [hs,phi_orthogonal n (e-1) (by omega),
      phi_orthogonal (n+1) e (by push_cast; omega),sub_self]
  have hu := reverse_orthogonal_unique n hr hort
  have hconst : coeffLM 0 r=verblunsky n := by
    dsimp [r,verblunsky]
    rw [map_sub,coeffLM_shift,show (0:ℤ)-1=-1 by ring,coeff_window_zero n (phi_mem_window n) (-1) (by omega)]
    simp
  rw [hconst] at hu
  dsimp [r] at hu
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hu).symm

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence LaurentPolynomial

def normSquare (n : ℕ) : ℝ := sigma (phi n) (phi n)

theorem normSquare_pos (n : ℕ) : 0<normSquare n :=
  riesz_positive_definite _ (phi_nonzero n)

private theorem phiStar_below (n : ℕ) : phiStar n ∈ polyBelow (n+1) := by
  apply spanOn_mono ?_ (phiStar_mem_window n)
  intro e he
  change 0≤e ∧ e≤(n:ℤ) at he
  change 0≤e ∧ e<((n+1:ℕ):ℤ)
  push_cast
  omega

private theorem cross_moment (n : ℕ) :
    sigma (phiStar n) (T 1*phi n)=verblunsky n*normSquare n := by
  have h := phi_orthogonal_span (n+1) _ (phiStar_below n)
  rw [monic_szego,map_sub,map_smul,smul_eq_mul,phiStar_norm] at h
  exact sub_eq_zero.mp h

/-- The norm identity makes every recursion denominator strictly positive. -/
private theorem normSquare_succ (n : ℕ) :
    normSquare (n+1)=(1-verblunsky n^2)*normSquare n := by
  change sigma (phi (n+1)) (phi (n+1))=_
  rw [monic_szego]
  simp only [map_sub,LinearMap.sub_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [sigma_shift,phiStar_norm,cross_moment,
    sigma_symm (T 1*phi n) (phiStar n),cross_moment]
  change normSquare n - verblunsky n*(verblunsky n*normSquare n) -
    verblunsky n*(verblunsky n*normSquare n-verblunsky n*normSquare n) = _
  ring

theorem verblunsky_sq_lt_one (n : ℕ) : verblunsky n^2<1 := by
  have h := normSquare_pos (n+1)
  rw [normSquare_succ] at h
  nlinarith [normSquare_pos n]

def gramNorm (n : ℕ) : ℝ := Real.sqrt (normSquare n)

private theorem gramRho_pos (n : ℕ) : 0<(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ)) := by
  apply D5.S3.Weil.Szego.CanonicalTransfer.szego_rho_pos
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact ((sq_lt_one_iff_abs_lt_one _).mp (verblunsky_sq_lt_one n))

private theorem gramNorm_pos (n : ℕ) : 0<gramNorm n := Real.sqrt_pos.mpr (normSquare_pos n)

private theorem gramNorm_succ (n : ℕ) : gramNorm (n+1)=(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ))*gramNorm n := by
  simp only [D5.S3.Weil.Szego.CanonicalTransfer.szegoRho, Complex.normSq_ofReal, ← pow_two]
  rw [gramNorm,normSquare_succ,Real.sqrt_mul (by linarith [verblunsky_sq_lt_one n])]
  rfl

def normalizedPhi (n : ℕ) : (LaurentPolynomial ℝ) := (gramNorm n)⁻¹ • phi n
def normalizedPhiStar (n : ℕ) : (LaurentPolynomial ℝ) := (gramNorm n)⁻¹ • phiStar n

/-- The normalized Szego recurrence, established from the finite Gram form. -/
theorem normalized_szego (n : ℕ) :
    (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ)) • normalizedPhi (n+1)=
      T 1*normalizedPhi n-verblunsky n • normalizedPhiStar n := by
  rw [normalizedPhi,normalizedPhi,normalizedPhiStar,gramNorm_succ,monic_szego]
  simp only [smul_sub,smul_smul,mul_smul_comm]
  have hr : (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ))≠0 := ne_of_gt (gramRho_pos n)
  have hn : gramNorm n≠0 := ne_of_gt (gramNorm_pos n)
  congr 1 <;> field_simp <;> ring

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCStarRecurrence
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization LaurentPolynomial

/-- Reflection of the monic Szego recurrence. -/
theorem monic_star_szego (n : ℕ) :
    phiStar (n+1)=phiStar n-verblunsky n • (T 1*phi n) := by
  rw [phiStar,monic_szego,map_sub,map_mul,map_smul,phiStar,map_mul,invert_T,
    involutive_invert]
  simp only [mul_sub,mul_smul_comm,invert_T,←mul_assoc,←T_add]
  rw [show ((n+1:ℕ):ℤ)+-(1:ℤ)=(n:ℤ) by push_cast; ring,
    show ((n+1:ℕ):ℤ)+-(n:ℤ)=1 by push_cast; ring]

/-- The second normalized recursion in the form used by the CMV blocks. -/
theorem normalized_star_inverse (n : ℕ) :
    normalizedPhiStar (n+1)=(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ)) • normalizedPhiStar n-
      verblunsky n • normalizedPhi (n+1) := by
  have hs : phiStar (n+1)=(1-verblunsky n^2) • phiStar n-
      verblunsky n • phi (n+1) := by
    rw [monic_star_szego,monic_szego]
    simp only [smul_sub,smul_smul]
    module
  have hr : (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ))≠0 := ne_of_gt (gramRho_pos n)
  have hn : gramNorm n≠0 := ne_of_gt (gramNorm_pos n)
  have hr2 : (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ))^2=1-verblunsky n^2 :=
    by
      have hAlpha : ‖(verblunsky n : ℂ)‖ < 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (sq_lt_one_iff_abs_lt_one _).mp (verblunsky_sq_lt_one n)
      simpa only [Complex.normSq_ofReal, ← pow_two] using
        D5.S3.Weil.Szego.CanonicalTransfer.szego_rho_sq hAlpha
  rw [normalizedPhiStar,normalizedPhiStar,normalizedPhi,hs,gramNorm_succ]
  simp only [smul_sub,smul_smul]
  congr 1
  · apply congrArg (fun a : ℝ => a • phiStar n)
    rw [←hr2]
    field_simp
  · module

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCStarRecurrence
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramOPUC
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization LaurentPolynomial

private def previous (j : ℕ) : Submodule ℝ (LaurentPolynomial ℝ) :=
  Submodule.span ℝ (monomials '' Set.Iio j)
private def gram : ℕ → (LaurentPolynomial ℝ) := InnerProductSpace.gramSchmidt ℝ monomials

private theorem gram_residual (j : ℕ) : monomials j-gram j ∈ previous j := by
  rw [gram,InnerProductSpace.gramSchmidt_def'' ℝ monomials j]
  rw [add_sub_cancel_left]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have hi' : i<j := Finset.mem_Iio.mp hi
  apply Submodule.span_mono ?_ (InnerProductSpace.gramSchmidt_mem_span ℝ monomials (le_refl i))
  apply Set.image_mono
  intro k hk
  change k ≤ i at hk
  change k < j
  omega

private theorem gram_orthogonal (j : ℕ) : ∀ p ∈ previous j, sigma p (gram j)=0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i,hi,rfl⟩ := hp
    have h := InnerProductSpace.gramSchmidt_inv_triangular ℝ monomials hi
    exact (sigma_symm _ _).trans h
  | zero => simp
  | add p q hp hq ih ih' => simp [ih,ih']
  | smul a p hp ih => simp [ih]

private theorem gram_characterization (j : ℕ) (q : (LaurentPolynomial ℝ))
    (hres : monomials j-q ∈ previous j)
    (hort : ∀ p ∈ previous j, sigma p q=0) : gram j=q := by
  have hg : IsProjection sigma (previous j) (monomials j) (monomials j-gram j) := by
    refine ⟨gram_residual j,?_⟩
    intro p hp
    have h : monomials j-(monomials j-gram j)=gram j := by abel
    rw [h]
    exact gram_orthogonal j p hp
  have hq : IsProjection sigma (previous j) (monomials j) (monomials j-q) := by
    refine ⟨hres,?_⟩
    intro p hp
    have h : monomials j-(monomials j-q)=q := by abel
    rw [h]
    exact hort p hp
  have heq := projection_unique sigma (previous j) riesz_positive_definite hg hq
  exact (sub_right_inj.mp heq)

private theorem previous_even (k : ℕ) :
    previous (2*k)=(Submodule.span ℝ (T '' {e : ℤ | -(k:ℤ)+1≤e ∧ e≤(k:ℤ)})) := by
  by_cases hk : k=0
  · subst k
    simp [previous]
    have he : {e : ℤ | (1:ℤ)≤e ∧ e≤0}=∅ := by ext e; simp; omega
    rw [he]
    simp
  · have hk1 : 1≤k := by omega
    have hw := monomial_window (k-1)
    have hidx : 2*(k-1)+2=2*k := by omega
    rw [hidx] at hw
    unfold previous
    change Submodule.span ℝ (monomials '' {j | j<2*k})=_
    rw [hw]
    congr 2
    ext e
    change (-((k-1:ℕ):ℤ)≤e ∧ e≤((k-1:ℕ):ℤ)+1) ↔ _
    rw [Nat.cast_sub hk1]
    norm_num
    omega

private theorem previous_odd (k : ℕ) :
    previous (2*k+1)=(Submodule.span ℝ (T '' {e : ℤ | -(k:ℤ)≤e ∧ e≤(k:ℤ)})) := by
  unfold previous
  congr 1
  ext p
  constructor
  · rintro ⟨j,hj,rfl⟩
    change j<2*k+1 at hj
    refine ⟨exponent j,?_,rfl⟩
    dsimp [exponent]
    split_ifs <;> omega
  · rintro ⟨e,he,rfl⟩
    change -(k:ℤ)≤e ∧ e≤(k:ℤ) at he
    by_cases hs : e≤0
    · refine ⟨2*(-e).toNat,?_,?_⟩
      · change 2*(-e).toNat<2*k+1
        have hen : ((-e).toNat:ℤ)=-e := Int.toNat_of_nonneg (by omega)
        omega
      · change T (exponent (2*(-e).toNat))=T e
        rw [exponent_even,Int.toNat_of_nonneg (by omega)]
        congr 1
        ring
    · refine ⟨2*(e-1).toNat+1,?_,?_⟩
      · change 2*(e-1).toNat+1<2*k+1
        have hen : ((e-1).toNat:ℤ)=e-1 := Int.toNat_of_nonneg (by omega)
        omega
      · change T (exponent (2*(e-1).toNat+1))=T e
        rw [exponent_odd,Int.toNat_of_nonneg (by omega)]
        congr 1
        ring

/-- The even Laurent Gram vector is the shifted reverse monic OPUC. -/
private theorem gram_even (k : ℕ) : gram (2*k)=T (-(k:ℤ))*phiStar (2*k) := by
  apply gram_characterization
  · rw [previous_even,mem_spanOn_iff]
    intro e he
    change ¬(-(k:ℤ)+1≤e ∧ e≤(k:ℤ)) at he
    rw [monomials,exponent_even,map_sub,coeffLM_T,coeffLM_shift]
    by_cases heq : e=-(k:ℤ)
    · subst e
      rw [if_pos rfl,show -(k:ℤ)- -(k:ℤ)=0 by ring,phiStar_constant,sub_self]
    · have hout : e- -(k:ℤ)<0 ∨ ((2*k:ℕ):ℤ)<e- -(k:ℤ) := by push_cast; omega
      rw [phiStar_coeff_zero (2*k) _ hout,if_neg heq,sub_self]
  · rw [previous_even]
    apply form_zero_on_span
    intro e he
    change -(k:ℤ)+1≤e ∧ e≤(k:ℤ) at he
    have h := sigma_shift (-(k:ℤ)) (T (e+k)) (phiStar (2*k))
    rw [←T_add,show -(k:ℤ)+(e+k)=e by ring] at h
    rw [h]
    apply phiStar_orthogonal
    push_cast
    omega

/-- The odd Laurent Gram vector is the shifted monic OPUC. -/
private theorem gram_odd (k : ℕ) : gram (2*k+1)=T (-(k:ℤ))*phi (2*k+1) := by
  apply gram_characterization
  · rw [previous_odd,mem_spanOn_iff]
    intro e he
    change ¬(-(k:ℤ)≤e ∧ e≤(k:ℤ)) at he
    rw [monomials,exponent_odd,map_sub,coeffLM_T,coeffLM_shift]
    by_cases heq : e=(k:ℤ)+1
    · subst e
      rw [if_pos rfl,show (k:ℤ)+1- -(k:ℤ)=((2*k+1:ℕ):ℤ) by push_cast; ring,
        phi_monic,sub_self]
    · have hout : e- -(k:ℤ)<0 ∨ ((2*k+1:ℕ):ℤ)<e- -(k:ℤ) := by push_cast; omega
      rw [coeff_window_zero (2*k+1) (phi_mem_window _) _ hout,if_neg heq,sub_self]
  · rw [previous_odd]
    apply form_zero_on_span
    intro e he
    change -(k:ℤ)≤e ∧ e≤(k:ℤ) at he
    have h := sigma_shift (-(k:ℤ)) (T (e+k)) (phi (2*k+1))
    rw [←T_add,show -(k:ℤ)+(e+k)=e by ring] at h
    rw [h]
    apply phi_orthogonal
    push_cast
    omega

private theorem norm_of_gram_square (n : ℕ) (p : (LaurentPolynomial ℝ)) (h : sigma p p=normSquare n) :
    ‖p‖=gramNorm n := by
  have hs : ‖p‖^2=normSquare n := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℝ)]
    exact h
  have hsq : gramNorm n^2=normSquare n := Real.sq_sqrt (normSquare_pos n).le
  have hn : 0≤gramNorm n := Real.sqrt_nonneg _
  nlinarith [norm_nonneg p]

/-- Simon's CMV-basis formula, in the source's exact Laurent ordering. -/
theorem chi_even (k : ℕ) : chi (2*k)=T (-(k:ℤ))*normalizedPhiStar (2*k) := by
  have hg := gram_even k
  have hn : ‖gram (2*k)‖=gramNorm (2*k) := norm_of_gram_square _ _ (by
    rw [hg,sigma_shift,phiStar_norm]
    rfl)
  change ‖gram (2*k)‖⁻¹ • gram (2*k)=_
  rw [hn,hg,normalizedPhiStar,mul_smul_comm]

theorem chi_odd (k : ℕ) : chi (2*k+1)=T (-(k:ℤ))*normalizedPhi (2*k+1) := by
  have hg := gram_odd k
  have hn : ‖gram (2*k+1)‖=gramNorm (2*k+1) := norm_of_gram_square _ _ (by
    rw [hg,sigma_shift]
    rfl)
  change ‖gram (2*k+1)‖⁻¹ • gram (2*k+1)=_
  rw [hn,hg,normalizedPhi,mul_smul_comm]

end D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramOPUC
end
