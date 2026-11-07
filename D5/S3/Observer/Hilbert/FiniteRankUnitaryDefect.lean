/- GID: D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/FiniteRankUnitaryDefect
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Finite-rank projection defects have their genuine ambient Hilbert-Schmidt square sums. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Finite-rank operators are measured on arbitrary, possibly uncountable Hilbert bases. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Hilbert.FiniteRankUnitaryDefect

open scoped InnerProductSpace
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite sum of genuine ambient rank-one operators. -/
def finiteOperator {ι : Type*} [Fintype ι] (v w : ι → H) : H →L[ℂ] H :=
  ∑ i, rankOne ℂ (v i) (w i)

private theorem finite_operator_energy {ι β : Type*} [Fintype ι]
    (v w : ι → H) (b : HilbertBasis β ℂ H) :
    HasSum (fun l => ‖finiteOperator v w (b l)‖ ^ 2)
      (Complex.re (∑ i, ∑ j, inner ℂ (v i) (v j) * inner ℂ (w j) (w i))) := by
  classical
  have hp (i j : ι) :=
    ((b.hasSum_inner_mul_inner (w j) (w i)).mul_left (inner ℂ (v i) (v j)))
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => hp i j))
  have he (l : β) :
      inner ℂ (finiteOperator v w (b l)) (finiteOperator v w (b l)) =
        ∑ i, ∑ j, inner ℂ (v i) (v j) *
          (inner ℂ (w j) (b l) * inner ℂ (b l) (w i)) := by
    simp only [finiteOperator, sum_apply, rankOne_apply,
      sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← inner_conj_symm (b l) (w i)]
    ring
  have hh := hs.mapL Complex.reCLM
  simpa only [Complex.reCLM_apply, ← he, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.ofReal_re] using hh

private theorem orthonormal_pair_energy {ι β : Type*} [Fintype ι]
    (u v : ι → H) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (b : HilbertBasis β ℂ H) :
    HasSum (fun l => ‖(finiteOperator u u - finiteOperator v v) (b l)‖ ^ 2)
      (2 * Fintype.card ι - 2 * ∑ i, ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2) := by
  classical
  let x : Sum ι ι → H := Sum.elim u (fun j => -v j)
  let y : Sum ι ι → H := Sum.elim u v
  have hp := finite_operator_energy x y b
  have heq : finiteOperator x y = finiteOperator u u - finiteOperator v v := by
    ext z
    simp [finiteOperator, x, y, Fintype.sum_sum_type, rankOne_apply,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [heq] at hp
  have hreal : RCLike.re (K := ℂ) (∑ i, ∑ j, inner ℂ (x i) (x j) * inner ℂ (y j) (y i)) =
      2 * Fintype.card ι - 2 * ∑ i, ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 := by
    simp only [x, y, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      inner_neg_neg, inner_neg_left, inner_neg_right, neg_mul, mul_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, map_add, map_neg, map_sum, Complex.re_sum, Complex.add_re, Complex.neg_re]
    have hm (a c : H) : (inner ℂ a c * inner ℂ c a).re = ‖inner ℂ a c‖ ^ 2 := by
      change RCLike.re (inner ℂ a c * inner ℂ c a) = _
      rw [inner_mul_symm_re_eq_norm, norm_mul, norm_inner_symm c a, pow_two]
    simp_rw [hm]
    have hd (w : ι → H) (hw : Orthonormal ℂ w) :
        ∑ i, ∑ j, ‖inner ℂ (w i) (w j)‖ ^ 2 = Fintype.card ι := by
      simp [orthonormal_iff_ite.mp hw]
    rw [hd u hu, hd v hv]
    have hc : (∑ i, ∑ j, ‖inner ℂ (v i) (u j)‖ ^ 2) =
        ∑ i, ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [norm_inner_symm (v _) (u _)]
    rw [hc]
    ring
  rwa [hreal] at hp


/-- Conjugating a finite-rank orthogonal projection has exactly twice the
cross-block energy, measured on any ambient Hilbert basis. -/
theorem unitary_projection_defect_hasSum {ι β : Type*} [Fintype ι]
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (c : OrthonormalBasis ι ℂ S) (U : H ≃ₗᵢ[ℂ] H) (b : HilbertBasis β ℂ H) :
    HasSum (fun l => ‖(U.toContinuousLinearMap.comp
      (S.starProjection.comp U.symm.toContinuousLinearMap) - S.starProjection) (b l)‖ ^ 2)
      (2 * ∑ i, ‖Sᗮ.starProjection (U (c i : H))‖ ^ 2) := by
  classical
  let v : ι → H := fun i => c i
  let u : ι → H := fun i => U (v i)
  have hv : Orthonormal ℂ v := c.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hu : Orthonormal ℂ u := hv.comp_linearIsometryEquiv U
  have hp := orthonormal_pair_energy u v hu hv b
  have hvp : finiteOperator v v = S.starProjection := by
    exact c.starProjection_eq_sum_rankOne.symm
  have hup : finiteOperator u u = U.toContinuousLinearMap.comp
      (S.starProjection.comp U.symm.toContinuousLinearMap) := by
    rw [← hvp]
    ext z
    simp only [finiteOperator, ContinuousLinearMap.comp_apply, sum_apply, rankOne_apply,
      map_sum, map_smul, u]
    apply Finset.sum_congr rfl
    intro i _
    rw [← U.inner_map_eq_flip]
  rw [hup, hvp] at hp
  have he (i : ι) :
      ‖Sᗮ.starProjection (u i)‖ ^ 2 =
        1 - ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 := by
    have hpy := S.norm_sq_eq_add_norm_sq_starProjection (u i)
    have hparse := c.sum_sq_norm_inner_left (S.orthogonalProjectionOnto (u i))
    have hparse' : (∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2) =
        ‖S.starProjection (u i)‖ ^ 2 := by
      simpa only [v, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hparse
    rw [hu.1 i, one_pow] at hpy
    linarith
  simp_rw [he]
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, mul_sub] using hp

#print axioms unitary_projection_defect_hasSum

end D5.S3.Observer.Hilbert.FiniteRankUnitaryDefect
