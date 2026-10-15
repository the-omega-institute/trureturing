/- GID: D5/S3/Quantum/Walks/Riesz/Decimation
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/Riesz/Decimation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Riesz moment and CMV identities for scale-four self-similarity. -/

/- admission_basis: escape-witness
   Module witness: parity_weighted_projection
   Direct frozen dependencies: none.
   Parity.parity_weighted_projection: proof_shape: content; escape_witness: Riesz.Decimation.Parity.parity_weighted_projection
     Direct frozen dependencies: none; consumers: Riesz.Decimation.Assembly.projection_scale_four.
   FiniteScaling.projection_norm_scale_four: proof_shape: content; escape_witness: Riesz.Decimation.Parity.parity_weighted_projection
     Direct frozen dependencies: none; consumers: RieszWalkSelfSimilarity.Scaling.cumulative_scale_four.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15854
-/

import D5.S3.Quantum.Walks.CMV.SzegoRecurrence

open LaurentPolynomial
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.Riesz.Decimation.Parity
open LaurentPolynomial
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
/-- An even residual has vanishing odd tests under the unweighted form. -/
private theorem odd_test_zero (B : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ))
    (hmon : ∀ i j : ℤ, i % 2 ≠ j % 2 → B (T i) (T j) = 0)
    {r : (LaurentPolynomial ℝ)} (hr : r ∈ residue 2 0) {e : ℤ} (he : e % 2 ≠ 0) :
    B (T e) r = 0 := by
  apply residue_class_orthogonal B 2 (e % 2) 0 he hmon _ ?_ r hr
  exact T_mem_spanOn rfl

/-- Lemma 3, as a projection characterization. The hypotheses are the monomial
form of the density change and parity orthogonality. -/
theorem parity_weighted_projection (B C : ((LaurentPolynomial ℝ) →ₗ[ℝ] (LaurentPolynomial ℝ) →ₗ[ℝ] ℝ)) (x t : ℕ)
    (hpar : ∀ i j : ℤ, i % 2 ≠ j % 2 → B (T i) (T j) = 0)
    (hweight : ∀ (e : ℤ) (q : (LaurentPolynomial ℝ)),
      C (T e) q = B (T e) q + (B (T (e-1)) q + B (T (e+1)) q)/2)
    (h : (LaurentPolynomial ℝ)) (hp : IsProjection B (E x) (T (-(2*t : ℤ))) h) :
    IsProjection C (W x) (T (-(2*t : ℤ))) h ∧ C h h = B h h := by
  have hhEven := E_le_even x hp.1
  have hfEven : (T (-(2*t : ℤ)) : (LaurentPolynomial ℝ)) ∈ residue 2 0 := by
    apply T_mem_spanOn
    change (-(2*t : ℤ)) % 2 = 0
    omega
  have hrEven : T (-(2*t : ℤ)) - h ∈ residue 2 0 :=
    (residue 2 0).sub_mem hfEven hhEven
  have hz : ∀ e : ℤ, -(2*x : ℤ) ≤ e → e ≤ 2*x →
      C (T e) (T (-(2*t : ℤ))-h) = 0 := by
    intro e hlo hhi
    rw [hweight]
    by_cases he : e % 2 = 0
    · have heE : (T e : (LaurentPolynomial ℝ)) ∈ E x := T_mem_spanOn ⟨hlo, hhi, he⟩
      rw [hp.2 _ heE,
        odd_test_zero B hpar hrEven (by omega : (e-1) % 2 ≠ 0),
        odd_test_zero B hpar hrEven (by omega : (e+1) % 2 ≠ 0)]
      simp
    · have hmE : (T (e-1) : (LaurentPolynomial ℝ)) ∈ E x :=
        T_mem_spanOn ⟨by omega, by omega, by omega⟩
      have hpE : (T (e+1) : (LaurentPolynomial ℝ)) ∈ E x :=
        T_mem_spanOn ⟨by omega, by omega, by omega⟩
      rw [odd_test_zero B hpar hrEven he, hp.2 _ hmE, hp.2 _ hpE]
      simp
  constructor
  · exact ⟨E_le_W x hp.1, form_zero_on_span C _ _ (by intro e he; exact hz e he.1 he.2)⟩
  · have hn : ∀ q ∈ residue 2 0, (C - B) q h = 0 := by
      apply form_zero_on_span
      intro e he
      change e % 2 = 0 at he
      change C (T e) h - B (T e) h = 0
      rw [hweight,
        odd_test_zero B hpar hhEven (by omega : (e-1) % 2 ≠ 0),
        odd_test_zero B hpar hhEven (by omega : (e+1) % 2 ≠ 0)]
      simp
    exact sub_eq_zero.mp (hn h hhEven)


end D5.S3.Quantum.Walks.Riesz.Decimation.Parity
end

noncomputable section
namespace D5.S3.Quantum.Walks.Riesz.Decimation.Assembly
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms LaurentPolynomial

private theorem E_le_V (x : ℕ) : E x ≤ V (2*x) := by
  apply spanOn_mono
  intro e he
  change -(2*x:ℤ) ≤ e ∧ e ≤ ((2*x:ℕ):ℤ)+1
  push_cast
  change -(2*x:ℤ) ≤ e ∧ e ≤ 2*x ∧ e%2=0 at he
  exact ⟨he.1, he.2.1.trans (by omega)⟩

private theorem small_projection (x t : ℕ) (h : (LaurentPolynomial ℝ))
    (hp : IsProjection sigma (E x) (T (-(2*t:ℤ))) h) :
    IsProjection sigma (V (2*x)) (T (-(2*t:ℤ))) h := by
  have hf : (T (-(2*t:ℤ)) : (LaurentPolynomial ℝ)) ∈ residue 2 0 := by
    apply T_mem_spanOn; change (-(2*t:ℤ))%2=0; omega
  have hr : T (-(2*t:ℤ))-h ∈ residue 2 0 :=
    (residue 2 0).sub_mem hf (E_le_even x hp.1)
  refine ⟨E_le_V x hp.1,?_⟩
  apply form_zero_on_span
  intro e he
  change -((2*x:ℕ):ℤ) ≤ e ∧ e ≤ ((2*x:ℕ):ℤ)+1 at he
  by_cases hpar : e%2=0
  · apply hp.2
    apply T_mem_spanOn
    refine ⟨?_,?_,hpar⟩ <;> push_cast at he <;> omega
  · exact odd_test_zero sigma riesz_parity_orthogonality hr hpar

private theorem J_into_residue (p : (LaurentPolynomial ℝ)) : J p ∈ residue 4 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using (residue 4 0).add_mem hp hq
  | C_mul_T i a =>
    rw [←smul_eq_C_mul,map_smul,J_T]
    apply (residue 4 0).smul_mem
    apply T_mem_spanOn
    change (4*i)%4=0
    omega

private theorem J_W_into_V (x : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ W x) : J p ∈ V (8*x) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨e,he,rfl⟩ := hp
    rw [J_T]
    apply T_mem_spanOn
    change -((8*x:ℕ):ℤ) ≤ 4*e ∧ 4*e ≤ ((8*x:ℕ):ℤ)+1
    change -(2*x:ℤ) ≤ e ∧ e ≤ 2*x at he
    push_cast
    omega
  | zero => simp
  | add p q hp hq ih ih' => simpa only [map_add] using (V (8*x)).add_mem ih ih'
  | smul a p hp ih => simpa only [map_smul] using (V (8*x)).smul_mem a ih

private theorem large_projection (x t : ℕ) (h : (LaurentPolynomial ℝ))
    (hp : IsProjection tau (W x) (T (-(2*t:ℤ))) h) :
    IsProjection sigma (V (8*x)) (T (-(8*t:ℤ))) (J h) := by
  have hf : (T (-(8*t:ℤ)) : (LaurentPolynomial ℝ)) = J (T (-(2*t:ℤ))) := by
    rw [J_T]; congr 1; ring
  rw [hf]
  refine ⟨J_W_into_V x hp.1,?_⟩
  have hr : J (T (-(2*t:ℤ)))-J h = J (T (-(2*t:ℤ))-h) := (map_sub J _ _).symm
  apply form_zero_on_span
  intro e he
  rw [hr]
  by_cases hm : e%4=0
  · have heq : e=4*(e/4) := by omega
    have heW : (T (e/4) : (LaurentPolynomial ℝ)) ∈ W x := by
      apply T_mem_spanOn
      change -(2*x:ℤ) ≤ e/4 ∧ e/4 ≤ 2*x
      change -((8*x:ℕ):ℤ) ≤ e ∧ e ≤ ((8*x:ℕ):ℤ)+1 at he
      push_cast at he
      omega
    have hT : (T e : (LaurentPolynomial ℝ)) = J (T (e/4)) := by rw [J_T]; congr 1
    rw [hT,decimation_isometry]
    exact hp.2 _ heW
  · exact residue_class_orthogonal sigma 4 (e%4) 0 hm riesz_residue_orthogonality
      _ (T_mem_spanOn rfl) _ (J_into_residue _)

/-- The complete finite projection calculation, before the Schur/CMV bridge. -/
private theorem projection_scale_four (x t : ℕ) (h : (LaurentPolynomial ℝ))
    (hp : IsProjection sigma (E x) (T (-(2*t:ℤ))) h) :
    IsProjection sigma (V (2*x)) (T (-(2*t:ℤ))) h ∧
    IsProjection sigma (V (8*x)) (T (-(8*t:ℤ))) (J h) ∧
    sigma (J h) (J h) = sigma h h := by
  obtain ⟨htau,hnorm⟩ := parity_weighted_projection sigma tau x t
    riesz_parity_orthogonality tau_density h hp
  exact ⟨small_projection x t h hp,large_projection x t h htau,by rw [decimation_isometry,hnorm]⟩

end D5.S3.Quantum.Walks.Riesz.Decimation.Assembly
end

noncomputable section
namespace D5.S3.Quantum.Walks.Riesz.Decimation.FiniteScaling
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Decimation.Assembly D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive LaurentPolynomial

/-- Unconditional existence of both finite projections, with equal norms. -/
private theorem scaled_projections_exist (x t : ℕ) :
    ∃ h k : (LaurentPolynomial ℝ),
      IsProjection sigma (V (2*x)) (T (-(2*t:ℤ))) h ∧
      IsProjection sigma (V (8*x)) (T (-(8*t:ℤ))) k ∧
      sigma h h = sigma k k := by
  obtain ⟨h,hp⟩ := D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence.finite_projection_exists sigma (E x)
    riesz_positive_definite (T (-(2*t:ℤ)))
  obtain ⟨hs,hl,hn⟩ := projection_scale_four x t h hp
  exact ⟨h,J h,hs,hl,hn.symm⟩

/-- Equality for any solutions of the two positive-definite Gram systems. -/
theorem projection_norm_scale_four (x t : ℕ) {h k : (LaurentPolynomial ℝ)}
    (hh : IsProjection sigma (V (2*x)) (T (-(2*t:ℤ))) h)
    (hk : IsProjection sigma (V (8*x)) (T (-(8*t:ℤ))) k) :
    sigma h h = sigma k k := by
  obtain ⟨h',k',hh',hk',hn⟩ := scaled_projections_exist x t
  have heh := projection_unique sigma (V (2*x)) riesz_positive_definite hh hh'
  have hek := projection_unique sigma (V (8*x)) riesz_positive_definite hk hk'
  simpa only [heh,hek] using hn

end D5.S3.Quantum.Walks.Riesz.Decimation.FiniteScaling
end
