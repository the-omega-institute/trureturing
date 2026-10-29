/- GID: D5/S3/HilbertOperators/Approximation/SupportedSingular
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/Approximation/SupportedSingular
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Full-carrier approximation numbers from complete real supported singular coordinates. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! Approximation is over all bounded competitors with actual cardinal rank at most n.
The finite-rank truncation and finite-dimensional obstruction are the classical
approximation-number argument; the supported coordinate hypothesis retains the
entire input carrier and an arbitrary orthogonal kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.HilbertOperators.Approximation.SupportedSingular

open scoped InnerProductSpace Topology ENNReal
open ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The zero-based infimum over all real bounded maps of actual rank at most n. -/
def approximationNumber (T : E →L[ℝ] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[ℝ] F // R.rank ≤ (n : Cardinal)}, ‖T - R.val‖

private theorem error_bddBelow (T : E →L[ℝ] F) (n : ℕ) :
    BddBelow (Set.range fun R : {R : E →L[ℝ] F // R.rank ≤ (n : Cardinal)} =>
      ‖T - R.val‖) := ⟨0, by rintro _ ⟨R,rfl⟩; exact norm_nonneg _⟩

private def cut (e : HilbertBasis ℕ ℝ G) (n : ℕ) : G →L[ℝ] G :=
  ∑ i ∈ Finset.range n, (innerSL ℝ (e i)).smulRight (e i)

/-- Complete supported coordinates determine the best arbitrary finite-rank error.
The isometry J includes the whole output support in its original ambient carrier. -/
theorem approximationNumber_eq_supported
    (T : E →L[ℝ] F) (A : E →L[ℝ] G) (J : G →ₗᵢ[ℝ] F)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (k : HilbertBasis ℕ ℝ K) (e : HilbertBasis ℕ ℝ G)
    (d : ℕ → ℝ) (h0 : ∀ i, 0 ≤ d i) (ha : Antitone d)
    (hT : ∀ x, T x = J (A x))
    (hc : ∀ x i, e.repr (A x) i = d i * k.repr (K.orthogonalProjectionOnto x) i)
    (n : ℕ) : approximationNumber T n = d n := by
  classical
  let R : E →L[ℝ] F := J.toContinuousLinearMap.comp ((cut e n).comp A)
  have hRrank : R.rank ≤ (n : Cardinal) := by
    let s : Finset F := (Finset.range n).image (fun i => J (e i))
    have hrange : R.range ≤ Submodule.span ℝ (s : Set F) := by
      rintro _ ⟨x,rfl⟩
      change J (cut e n (A x)) ∈ _
      simp only [cut, sum_apply, smulRight_apply, innerSL_apply_apply, map_sum, map_smul]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    have hdim : Module.finrank ℝ (Submodule.span ℝ (s : Set F)) ≤ n :=
      (finrank_span_finset_le_card s).trans ((Finset.card_image_le).trans (by simp))
    calc
      R.rank ≤ Module.rank ℝ (Submodule.span ℝ (s : Set F)) := Submodule.rank_mono hrange
      _ = (Module.finrank ℝ (Submodule.span ℝ (s : Set F)) : Cardinal) :=
        (Module.finrank_eq_rank _ _).symm
      _ ≤ (n : Cardinal) := by exact_mod_cast hdim
  have herr : ‖T - R‖ ≤ d n := by
    apply opNorm_le_bound _ (h0 n)
    intro x
    have hn : ‖A x - cut e n (A x)‖ ≤ d n * ‖K.orthogonalProjectionOnto x‖ := by
      rw [← e.repr.norm_map (A x - cut e n (A x))]
      calc
        ‖e.repr (A x - cut e n (A x))‖ ≤
            ‖d n • k.repr (K.orthogonalProjectionOnto x)‖ := by
          apply lp.norm_mono (by norm_num : (0 : ℝ≥0∞) < 2)
          intro i
          have hcut : e.repr (cut e n (A x)) i = if i < n then e.repr (A x) i else 0 := by
            simp [cut, map_sum, map_smul, e.repr_self, lp.single_apply, Pi.single_apply,
              e.repr_apply_apply, innerSL_apply_apply]
          simp only [map_sub, lp.sub_apply, hcut, hc, lp.coeFn_smul, Pi.smul_apply,
            smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (h0 n)]
          split_ifs with hi
          · simp [mul_nonneg (h0 n) (abs_nonneg _)]
          · rw [sub_zero, abs_of_nonneg (h0 i)]
            exact mul_le_mul_of_nonneg_right (ha (Nat.le_of_not_lt hi)) (abs_nonneg _)
        _ = d n * ‖K.orthogonalProjectionOnto x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h0 n), k.repr.norm_map]
    calc
      ‖(T - R) x‖ = ‖A x - cut e n (A x)‖ := by
        rw [sub_apply, hT]
        change ‖J (A x) - J (cut e n (A x))‖ = _
        rw [← map_sub, J.norm_map]
      _ ≤ d n * ‖K.orthogonalProjectionOnto x‖ := hn
      _ ≤ d n * ‖x‖ := mul_le_mul_of_nonneg_left (K.norm_orthogonalProjectionOnto_apply_le x) (h0 n)
  have hu : approximationNumber T n ≤ d n :=
    (ciInf_le (error_bddBelow T n) ⟨R,hRrank⟩).trans herr
  have hl : d n ≤ approximationNumber T n := by
    letI : Nonempty {R : E →L[ℝ] F // R.rank ≤ (n : Cardinal)} := ⟨⟨0,by simp [LinearMap.rank_zero]⟩⟩
    apply le_ciInf
    rintro ⟨Q,hQ⟩
    let v : Fin (n+1) → Q.range := fun i => ⟨Q (k i.val).val, ⟨(k i.val).val,rfl⟩⟩
    have hdep : ¬ LinearIndependent ℝ v := by
      intro hv
      have h := hv.cardinal_lift_le_rank.trans (Cardinal.lift_le.mpr hQ)
      simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast,
        Cardinal.natCast_le] at h
      omega
    obtain ⟨c,hcQ,j,hcj⟩ := Fintype.not_linearIndependent_iff.mp hdep
    let x : K := ∑ i : Fin (n+1), c i • k i.val
    let y : G := ∑ i : Fin (n+1), (c i * d i.val) • e i.val
    have hx0 : x ≠ 0 := by
      intro hx
      have hlin := k.orthonormal.linearIndependent.comp (fun i : Fin (n+1) => i.val) Fin.val_injective
      exact hcj ((Fintype.linearIndependent_iff.mp hlin) c hx j)
    have hQx : Q x.val = 0 := by
      have hh := congrArg (fun z : Q.range => z.val) hcQ
      simpa [x,v,map_sum,map_smul] using hh
    have hAx : A x.val = y := by
      have hb (i : ℕ) : A (k i).val = d i • e i := by
        apply e.repr.injective
        apply lp.ext
        funext q
        rw [hc]
        have hp : K.orthogonalProjectionOnto (k i).val = k i := by simp
        rw [hp]
        simp [map_smul, e.repr_self, k.repr_self, lp.single_apply, Pi.single_apply]
        split_ifs <;> simp_all
      simp only [x,y,Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hb, smul_smul]
    have hxnorm : ‖x‖^2 = ∑ i : Fin (n+1), (c i)^2 := by
      rw [← real_inner_self_eq_norm_sq]
      simpa only [x, pow_two, star_trivial] using
        (k.orthonormal.comp (fun i : Fin (n+1) => i.val) Fin.val_injective).inner_sum c c Finset.univ
    have hynorm : ‖y‖^2 = ∑ i : Fin (n+1), (c i * d i.val)^2 := by
      rw [← real_inner_self_eq_norm_sq]
      simpa only [y, pow_two, star_trivial] using
        (e.orthonormal.comp (fun i : Fin (n+1) => i.val) Fin.val_injective).inner_sum
          (fun i => c i * d i.val) (fun i => c i * d i.val) Finset.univ
    have hlo : d n * ‖x‖ ≤ ‖y‖ := by
      have hs : (d n)^2 * ‖x‖^2 ≤ ‖y‖^2 := by
        rw [hxnorm,hynorm,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hd := ha (show i.val ≤ n by omega)
        have hd0 := h0 i.val
        nlinarith [sq_nonneg (c i), sq_nonneg (d i.val - d n)]
      nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (h0 n) (norm_nonneg x)]
    have ht : ‖T x.val‖ = ‖y‖ := by rw [hT,J.norm_map,hAx]
    have hb : d n * ‖x‖ ≤ ‖T-Q‖ * ‖x‖ := by
      calc
        d n * ‖x‖ ≤ ‖T x.val‖ := ht ▸ hlo
        _ = ‖(T-Q) x.val‖ := by simp [hQx]
        _ ≤ ‖T-Q‖ * ‖x‖ := (T-Q).le_opNorm x.val
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx0)).mp hb
  exact le_antisymm hu hl

#print axioms approximationNumber_eq_supported

end D5.S3.HilbertOperators.Approximation.SupportedSingular
