/- GID: D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoKrausRankOneAttenuation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Operator norm loss for nilpotent CAR two-Kraus maps on pure states. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Two Kraus images of a unit vector and the determinant of their Gram defect. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The no-jump filter of the unital attenuation map. -/
def jumpFilter (J : Matrix n n ℂ) (q : ℝ) : Matrix n n ℂ :=
  1 - J * J.conjTranspose + (Real.sqrt (1 - q) : ℂ) • (J * J.conjTranspose)

/-- The actual two-Kraus map, without a trace-preservation requirement. -/
def jumpMap (J : Matrix n n ℂ) (q : ℝ) :=
  let K : Fin 2 → Matrix n n ℂ := ![jumpFilter J q, (Real.sqrt q : ℂ) • J]
  FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus K K

private theorem car_projection (J : Matrix n n ℂ) (hJ : J * J = 0)
    (hCAR : J * J.conjTranspose + J.conjTranspose * J = 1) :
    let F := J * J.conjTranspose
    F.conjTranspose = F ∧ F * F = F ∧ F * J = J ∧ J * F = 0 ∧
      J.conjTranspose * J = 1 - F := by
  dsimp only
  have hjf : J * (J * J.conjTranspose) = 0 := by rw [← mul_assoc, hJ, zero_mul]
  have hcomp : J.conjTranspose * J = 1 - J * J.conjTranspose := by
    exact eq_sub_of_add_eq' hCAR
  have hfj : J * J.conjTranspose * J = J := by
    rw [mul_assoc, hcomp, mul_sub, mul_one, hjf, sub_zero]
  exact ⟨by simp, by rw [← mul_assoc, hfj], hfj, hjf, hcomp⟩

private theorem filter_algebra (J : Matrix n n ℂ) (hJ : J * J = 0)
    (hCAR : J * J.conjTranspose + J.conjTranspose * J = 1)
    (q : ℝ) (hq : q ≤ 1) :
    (jumpFilter J q).conjTranspose = jumpFilter J q ∧
    jumpFilter J q * jumpFilter J q = 1 - (q : ℂ) • (J * J.conjTranspose) ∧
    jumpFilter J q * J = (Real.sqrt (1 - q) : ℂ) • J := by
  obtain ⟨hF,hFF,hFJ,hJF,hcomp⟩ := car_projection J hJ hCAR
  have hs : (Real.sqrt (1-q) : ℂ) * (Real.sqrt (1-q) : ℂ) = 1 - (q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hq)
  refine ⟨?_,?_,?_⟩
  · simp [jumpFilter, conjTranspose_sub, conjTranspose_smul]
  · unfold jumpFilter
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, hFF, sub_self, zero_add,
      _root_.smul_smul, hs]
    module
  · simp [jumpFilter, sub_mul, add_mul, smul_mul, hFJ]

theorem jumpMap_apply (J : Matrix n n ℂ) (q : ℝ) (hq : 0 ≤ q)
    (X : Matrix n n ℂ) :
    jumpMap J q X = jumpFilter J q * X * (jumpFilter J q).conjTranspose +
      (q : ℂ) • (J * X * J.conjTranspose) := by
  have hs : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hq
  unfold jumpMap FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change _ + (((Real.sqrt q : ℂ) • J) * X * ((Real.sqrt q : ℂ) • J).conjTranspose) = _
  rw [conjTranspose_smul]
  rw [show star (Real.sqrt q : ℂ) = (Real.sqrt q : ℂ) from Complex.conj_ofReal _]
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, _root_.smul_smul, hs]
  rfl

private theorem jumpMap_unital (J : Matrix n n ℂ) (hJ : J * J = 0)
    (hCAR : J * J.conjTranspose + J.conjTranspose * J = 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : jumpMap J q 1 = 1 := by
  obtain ⟨hR,hRR,_⟩ := filter_algebra J hJ hCAR q hq1
  rw [jumpMap_apply J q hq0, hR, mul_one, mul_one, hRR]
  module

private theorem pure_projection_le_one (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) :
    vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) ≤ 1 := by
  let P := vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))
  have hu : star (WithLp.ofLp ψ) ⬝ᵥ WithLp.ofLp ψ = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hPP : P * P = P := by
    simp [P, vecMulVec_mul_vecMulVec, hu]
  have hPs : P.conjTranspose = P := by simp [P]
  have hnorm : ‖P‖ ≤ 1 := by
    have hh := l2_opNorm_conjTranspose_mul_self P
    rw [hPs, hPP] at hh
    nlinarith [norm_nonneg P]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg P
    (posSemidef_vecMulVec_self_star _).nonneg).mp hnorm

theorem jumpMap_positive (J : Matrix n n ℂ) (q : ℝ) (hq : 0 ≤ q)
    {X : Matrix n n ℂ} (hX : 0 ≤ X) : 0 ≤ jumpMap J q X := by
  rw [jumpMap_apply J q hq]
  exact ((hX.posSemidef.mul_mul_conjTranspose_same _).add
    ((hX.posSemidef.mul_mul_conjTranspose_same J).smul
      (show (0 : ℂ) ≤ (q : ℂ) by exact_mod_cast hq))).nonneg

private theorem jumpMap_mono (J : Matrix n n ℂ) (q : ℝ) (hq : 0 ≤ q)
    {X Y : Matrix n n ℂ} (hXY : X ≤ Y) : jumpMap J q X ≤ jumpMap J q Y := by
  have h := jumpMap_positive J q hq (sub_nonneg.mpr hXY)
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A unital CAR attenuation is an operator-norm contraction on Hermitian inputs. -/
theorem jumpMap_norm_le (J : Matrix n n ℂ) (hJ : J * J = 0)
    (hCAR : J * J.conjTranspose + J.conjTranspose * J = 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (jumpMap J q X)‖ ≤
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) X‖ := by
  let H := jumpMap J q
  have hc (r : ℝ) : H (algebraMap ℝ (Matrix n n ℂ) r) =
      algebraMap ℝ (Matrix n n ℂ) r := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [← Complex.coe_smul, map_smul, jumpMap_unital J hJ hCAR q hq0 hq1]
  have hlo := jumpMap_mono J q hq0 (hX.isSelfAdjoint.neg_algebraMap_norm_le_self X)
  have hhi := jumpMap_mono J q hq0 (hX.isSelfAdjoint.le_algebraMap_norm_self X)
  change H _ ≤ _ at hlo
  rw [map_neg, hc] at hlo
  change _ ≤ H _ at hhi
  rw [hc] at hhi
  have hHerm : (H X).IsHermitian := by
    rw [jumpMap_apply J q hq0]
    exact (isHermitian_mul_mul_conjTranspose _ hX).add
      ((isHermitian_mul_mul_conjTranspose J hX).smul
        (show IsSelfAdjoint (q : ℂ) from Complex.conj_ofReal q))
  rw [l2_opNorm_toEuclideanCLM, l2_opNorm_toEuclideanCLM]
  have hb := hHerm.isSelfAdjoint.norm_le_max_of_le_of_le hlo hhi
  have hn : ‖algebraMap ℝ (Matrix n n ℂ) ‖X‖‖ ≤ ‖X‖ := by
    rcases subsingleton_or_nontrivial (Matrix n n ℂ) with h | h
    · simp [Subsingleton.elim X 0]
    · simp [norm_algebraMap']
  simpa only [norm_neg, max_self] using hb.trans (max_le (by simpa using hn) hn)

private theorem column_inner (B C : Matrix n n ℂ) (u : n → ℂ) :
    star (B *ᵥ u) ⬝ᵥ (C *ᵥ u) = star u ⬝ᵥ ((B.conjTranspose * C) *ᵥ u) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

private theorem two_column_outer (a b : n → ℂ) :
    let A : Matrix n (Fin 2) ℂ := ![a,b]ᵀ
    A * A.conjTranspose = vecMulVec a (star a) + vecMulVec b (star b) := by
  ext i j
  simp [mul_apply, Fin.sum_univ_two, vecMulVec_apply, Matrix.transpose]

private theorem two_column_gram (a b : n → ℂ) :
    let A : Matrix n (Fin 2) ℂ := ![a,b]ᵀ
    A.conjTranspose * A =
      !![star a ⬝ᵥ a, star a ⬝ᵥ b; star b ⬝ᵥ a, star b ⬝ᵥ b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, dotProduct, Matrix.transpose]

private theorem two_column_defect_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n (Fin 2) ℂ) (hA : (1 - A.conjTranspose * A).PosSemidef) :
    ‖A * A.conjTranspose‖ ≤ 1 - (det (1 - A.conjTranspose * A)).re := by
  let G := A.conjTranspose * A
  have hG : G.PosSemidef := posSemidef_conjTranspose_mul_self A
  have hG1 : G ≤ 1 := hA
  have hn : ‖G‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg G hG.nonneg).mpr hG1
  have he (i : Fin 2) : 0 ≤ hG.1.eigenvalues i ∧ hG.1.eigenvalues i ≤ 1 := by
    refine ⟨hG.eigenvalues_nonneg i, ?_⟩
    exact (Real.le_norm_self _).trans
      ((spectrum.norm_le_norm_of_mem (hG.1.eigenvalues_mem_spectrum_real i)).trans hn)
  obtain ⟨i, hi⟩ := hG.1.spectrum_real_eq_range_eigenvalues ▸
    CStarAlgebra.norm_mem_spectrum_of_nonneg G hG.nonneg
  have hd : (det (1 - G)).re =
      (1 - hG.1.eigenvalues 0) * (1 - hG.1.eigenvalues 1) := by
    have hc := congrArg (fun p : Polynomial ℂ => p.eval 1) hG.1.charpoly_eq
    simpa [eval_charpoly, Fin.prod_univ_two] using congrArg Complex.re hc
  have hnG : ‖A * A.conjTranspose‖ = ‖G‖ := by
    calc
      _ = ‖A.conjTranspose‖ * ‖A.conjTranspose‖ := by
        simpa only [conjTranspose_conjTranspose] using
          l2_opNorm_conjTranspose_mul_self A.conjTranspose
      _ = ‖G‖ := by rw [l2_opNorm_conjTranspose]; exact (l2_opNorm_conjTranspose_mul_self A).symm
  rw [hnG]
  change ‖G‖ ≤ 1 - (det (1 - G)).re
  rw [hd]
  fin_cases i <;> norm_num at hi <;>
    nlinarith [he 0, he 1, mul_nonneg (he 0).1 (sub_nonneg.mpr (he 1).2),
      mul_nonneg (he 1).1 (sub_nonneg.mpr (he 0).2)]

/-- Rank-one attenuation for every finite nilpotent CAR representation. The norm
is the operator norm on the Euclidean complex space. -/
theorem nilpotent_jump_rank_one_attenuation
    (J : Matrix n n ℂ) (hJ : J * J = 0)
    (hCAR : J * J.conjTranspose + J.conjTranspose * J = 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) :
    let u := WithLp.ofLp ψ
    let p := (star u ⬝ᵥ ((J * J.conjTranspose) *ᵥ u)).re
    let c := star u ⬝ᵥ (J *ᵥ u)
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (jumpMap J q (vecMulVec u (star u)))‖ ≤
      1 - q * (1-q) * (p - Complex.normSq c) := by
  let u := WithLp.ofLp ψ
  let F := J * J.conjTranspose
  let R := jumpFilter J q
  let p := (star u ⬝ᵥ (F *ᵥ u)).re
  let c := star u ⬝ᵥ (J *ᵥ u)
  let a := R *ᵥ u
  let b := (Real.sqrt q : ℂ) • (J *ᵥ u)
  let A : Matrix n (Fin 2) ℂ := ![a,b]ᵀ
  have hu : star u ⬝ᵥ u = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hp : star u ⬝ᵥ (F *ᵥ u) = (p : ℂ) := by
    have hh := (posSemidef_self_mul_conjTranspose J).dotProduct_mulVec_nonneg u
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hh).2.symm
  obtain ⟨_,_,_,_,hcomp⟩ := car_projection J hJ hCAR
  obtain ⟨hR,hRR,hRJ⟩ := filter_algebra J hJ hCAR q hq1
  have haa : star a ⬝ᵥ a = 1 - (q : ℂ) * p := by
    dsimp [a]
    rw [column_inner, hR, hRR, sub_mulVec, smul_mulVec, dotProduct_sub,
      one_mulVec, dotProduct_smul, hu, hp, smul_eq_mul]
  have hvv : star (J *ᵥ u) ⬝ᵥ (J *ᵥ u) = 1 - (p : ℂ) := by
    rw [column_inner, hcomp, sub_mulVec, one_mulVec, dotProduct_sub, hu, hp]
  have hab : star a ⬝ᵥ b =
      (Real.sqrt q : ℂ) * (Real.sqrt (1-q) : ℂ) * c := by
    dsimp [a,b]
    rw [dotProduct_smul, column_inner, hR, hRJ, smul_mulVec, dotProduct_smul]
    change (Real.sqrt q : ℂ) * ((Real.sqrt (1-q) : ℂ) * c) = _
    ring
  have hba : star b ⬝ᵥ a = star (star a ⬝ᵥ b) := star_dotProduct b a
  have hbb : star b ⬝ᵥ b = (q : ℂ) * (1 - (p : ℂ)) := by
    dsimp [b]
    rw [star_smul, smul_dotProduct, dotProduct_smul]
    change (Real.sqrt q : ℂ) * ((Real.sqrt q : ℂ) *
      (star (J *ᵥ u) ⬝ᵥ (J *ᵥ u))) = _
    rw [hvv]
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]
  have hAA : A * A.conjTranspose = jumpMap J q (vecMulVec u (star u)) := by
    rw [two_column_outer, jumpMap_apply J q hq0]
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec,
      mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
    dsimp only [a,b,R]
    rw [star_smul, smul_vecMulVec, vecMulVec_smul]
    rw [show star (Real.sqrt q : ℂ) = (Real.sqrt q : ℂ) from Complex.conj_ofReal _]
    rw [_root_.smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]
  have hG : (1 - A.conjTranspose * A).PosSemidef := by
    have hAAle : A * A.conjTranspose ≤ 1 := by
      rw [hAA, ← jumpMap_unital J hJ hCAR q hq0 hq1]
      exact jumpMap_mono J q hq0 (pure_projection_le_one ψ hψ)
    have hnAA := (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (posSemidef_self_mul_conjTranspose A).nonneg).mpr hAAle
    have hnG : ‖A.conjTranspose * A‖ ≤ 1 := by
      have he := l2_opNorm_conjTranspose_mul_self A.conjTranspose
      simp only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] at he
      rw [l2_opNorm_conjTranspose_mul_self]
      rwa [he] at hnAA
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (posSemidef_conjTranspose_mul_self A).nonneg).mp hnG
  have hd : (det (1 - A.conjTranspose * A)).re =
      q * ((1-q) * (p - Complex.normSq c) + q * p^2) := by
    rw [two_column_gram, haa, hab, hba, hab, hbb]
    simp only [det_fin_two, Matrix.sub_apply, one_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, of_apply, star_mul]
    simp only [show star (Real.sqrt q : ℂ) = (Real.sqrt q : ℂ) from Complex.conj_ofReal _,
      show star (Real.sqrt (1-q) : ℂ) = (Real.sqrt (1-q) : ℂ) from Complex.conj_ofReal _]
    norm_num only [Fin.reduceFinMk, ite_true, ite_false, zero_sub, neg_mul, mul_neg, neg_neg]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring_nf
    rw [Real.sq_sqrt hq0, Real.sq_sqrt (sub_nonneg.mpr hq1)]
    norm_num <;> ring
  have hbound := two_column_defect_bound A hG
  rw [hd, hAA] at hbound
  dsimp only
  rw [l2_opNorm_toEuclideanCLM]
  change ‖jumpMap J q (vecMulVec u (star u))‖ ≤ _
  nlinarith [sq_nonneg (q*p)]

#print axioms nilpotent_jump_rank_one_attenuation

end D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
