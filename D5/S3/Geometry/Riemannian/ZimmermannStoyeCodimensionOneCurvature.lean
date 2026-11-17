/- GID: D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature
   generality: G
   mirror-B: D5/B/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sharp codimension-one Euclidean Stiefel curvature bounds and endpoints. -/
/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22071; Proved)
Direct frozen dependencies: D5/S3/Combinatorics/Graph/KyFanGap/NearExtremal.real_frobenius_sq;
  declaration statement_id sha256:6edf90a6107b2eea3e83f169860a150343d3536ac637265e8955847645c2b361.
  D5/S3/Quantum/GNSMatrix.frobenius_norm_sq_eq_trace;
  declaration statement_id sha256:470140292aee89705512206af514f5a42fdc3948e5c9195d302613a47b859917.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23644
All helper theorems have proof_shape: bind-only and are consumed by result.
The geometric interpretation uses equation (26) and the source's base-point isometry.
The real Gram extension specializes the QICLean proof retained in
D5/S3/Quantum/Algebra/GramUnitaryExtension.lean and Library/Quantum/qiclean2026gramunitary.md.
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Authors: Sirui Lu.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Ring.Identities
import D5.S3.Combinatorics.Graph.KyFanGap.NearExtremal
import D5.S3.Quantum.GNSMatrix
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.Frobenius InnerProductSpace
namespace D5.S3.Geometry.Riemannian.ZimmermannStoyeCodimensionOneCurvature
/-- St(n,p) = {U in R^(n x p) | U^T U = I_p}. -/
def stiefel (n p : ℕ) : Set (Matrix (Fin n) (Fin p) ℝ) :=
  {U | Uᵀ * U = 1}
/-- At [I_p;0], tangent vectors have blocks A in Skew(p), B in R^(q x p). The three remaining equations say that [A₁;B₁], [A₂;B₂] form a Euclidean ONB. -/
def orthonormalTangentBlocks {p q : ℕ}
    (A₁ A₂ : Matrix (Fin p) (Fin p) ℝ)
    (B₁ B₂ : Matrix (Fin q) (Fin p) ℝ) : Prop :=
  A₁ᵀ = -A₁ ∧ A₂ᵀ = -A₂ ∧
    ‖A₁‖ ^ 2 + ‖B₁‖ ^ 2 = 1 ∧
    ‖A₂‖ ^ 2 + ‖B₂‖ ^ 2 = 1 ∧
    Matrix.trace (A₁ᵀ * A₂) + Matrix.trace (B₁ᵀ * B₂) = 0
/-- The source's displayed K_e^St, equation (26), on Euclidean ONB blocks. This definition binds curvature to that display; [A₁,A₂] means A₁*A₂-A₂*A₁. -/
noncomputable def euclideanSectionalCurvature {p q : ℕ}
    (A₁ A₂ : Matrix (Fin p) (Fin p) ℝ)
    (B₁ B₂ : Matrix (Fin q) (Fin p) ℝ) : ℝ :=
  ‖B₁ * A₂ - B₂ * A₁‖ ^ 2 +
    (1 / 2 : ℝ) * ‖B₁ * B₂ᵀ - B₂ * B₁ᵀ‖ ^ 2 -
    (1 / 2 : ℝ) * ‖B₁ᵀ * B₂ - B₂ᵀ * B₁‖ ^ 2 +
    (1 / 4 : ℝ) * ‖(A₁ * A₂ - A₂ * A₁) - (B₂ᵀ * B₁ - B₁ᵀ * B₂)‖ ^ 2
/-- Conjecture 1: for every n >= 4, p=n-1, all Euclidean orthonormal tangent pairs have curvature in [-1/2,1/2], and both endpoints are attained for that n. Here q=1 is n-p, and the source's base-point isometry supplies every U. -/
def claim : Prop :=
  ∀ (n : ℕ), 4 ≤ n →
    (∀ (A₁ A₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
        (B₁ B₂ : Matrix (Fin 1) (Fin (n - 1)) ℝ),
      orthonormalTangentBlocks A₁ A₂ B₁ B₂ →
        (- (1 / 2 : ℝ) ≤ euclideanSectionalCurvature A₁ A₂ B₁ B₂ ∧
          euclideanSectionalCurvature A₁ A₂ B₁ B₂ ≤ (1 / 2 : ℝ))) ∧
    (∃ (A₁ A₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
        (B₁ B₂ : Matrix (Fin 1) (Fin (n - 1)) ℝ),
      orthonormalTangentBlocks A₁ A₂ B₁ B₂ ∧
        euclideanSectionalCurvature A₁ A₂ B₁ B₂ = - (1 / 2 : ℝ)) ∧
    (∃ (A₁ A₂ : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
        (B₁ B₂ : Matrix (Fin 1) (Fin (n - 1)) ℝ),
      orthonormalTangentBlocks A₁ A₂ B₁ B₂ ∧
        euclideanSectionalCurvature A₁ A₂ B₁ B₂ = (1 / 2 : ℝ))
private theorem skew_entry {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (i j : Fin p) : A j i = -A i j := by
  exact congrFun (congrFun hA i) j
private theorem skew_diagonal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (i : Fin p) : A i i = 0 := by
  exact CharZero.eq_neg_self_iff.mp (congrFun (congrFun hA i) i)
private theorem skew_cut_budget {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (S : Finset (Fin p)) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, A i j ^ 2) ≤ ‖A‖ ^ 2 / 2 := by
  classical
  have hnorm : ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
    exact D5.S3.Combinatorics.Graph.KyFanGap.real_frobenius_sq A
  have hswap : (∑ i ∈ Sᶜ, ∑ j ∈ S, A i j ^ 2) =
      ∑ i ∈ S, ∑ j ∈ Sᶜ, A i j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [skew_entry A hA j i, neg_sq]
  have hparts : (∑ i ∈ S, ∑ j ∈ Sᶜ, A i j ^ 2) +
      (∑ i ∈ Sᶜ, ∑ j ∈ S, A i j ^ 2) ≤ ∑ i, ∑ j, A i j ^ 2 := by
    have hrow₁ : ∀ i ∈ S, (∑ j ∈ Sᶜ, A i j ^ 2) ≤ ∑ j, A i j ^ 2 := by
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    have hrow₂ : ∀ i ∈ Sᶜ, (∑ j ∈ S, A i j ^ 2) ≤ ∑ j, A i j ^ 2 := by
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    calc
      _ ≤ (∑ i ∈ S, ∑ j, A i j ^ 2) + (∑ i ∈ Sᶜ, ∑ j, A i j ^ 2) :=
        add_le_add (Finset.sum_le_sum hrow₁) (Finset.sum_le_sum hrow₂)
      _ = _ := by rw [Finset.sum_add_sum_compl]
  rw [hnorm]
  rw [hswap] at hparts
  linarith
private theorem skew_row_budget {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (i : Fin p) :
    (∑ j, A i j ^ 2) ≤ ‖A‖ ^ 2 / 2 := by
  classical
  have h := skew_cut_budget A hA {i}
  simp only [Finset.sum_singleton] at h
  have he := Finset.sum_compl_add_sum ({i} : Finset (Fin p)) (fun j => A i j ^ 2)
  simp only [Finset.sum_singleton, skew_diagonal A hA i, zero_pow (by decide : 2 ≠ 0), add_zero] at he
  rwa [he] at h
private theorem skew_tail_budget {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (i j : Fin p) (hij : i ≠ j) :
    (∑ k ∈ ({i,j} : Finset (Fin p))ᶜ, (A i k ^ 2+A j k ^ 2)) ≤ ‖A‖ ^ 2 / 2 := by
  classical
  have h := skew_cut_budget A hA {i,j}
  simpa only [Finset.sum_pair hij, ← Finset.sum_add_distrib] using h
private theorem coupling_tail_identity {p : ℕ} (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (hC : Cᵀ = -C) (i j : Fin p) :
    (∑ k, (C i k*A j k+A i k*C j k)) =
      ∑ k ∈ ({i,j} : Finset (Fin p))ᶜ, (C i k*A j k+A i k*C j k) := by
  classical
  have hz : (∑ k ∈ ({i,j} : Finset (Fin p)), (C i k*A j k+A i k*C j k))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [skew_diagonal A hA,skew_diagonal C hC]
  have he := Finset.sum_compl_add_sum ({i,j} : Finset (Fin p))
    (fun k => C i k*A j k+A i k*C j k)
  rw [hz,add_zero] at he
  exact he.symm
private theorem coupled_row_estimate {p : ℕ} (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (hC : Cᵀ = -C) (i j : Fin p) (hij : i ≠ j) :
    |∑ k, (C i k*A j k+A i k*C j k)| ≤ ‖A‖*‖C‖/2 := by
  classical
  rw [coupling_tail_identity A C hA hC i j]
  let T : Finset (Fin p) := ({i,j} : Finset (Fin p))ᶜ
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (T ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun x => if x.2=0 then A j x.1 else A i x.1)
    (fun x => if x.2=0 then C i x.1 else C j x.1)
  simp only [Finset.sum_product, Fin.sum_univ_two] at hcs
  simp only [ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false] at hcs
  have ha := skew_tail_budget A hA i j hij
  have hc := skew_tail_budget C hC i j hij
  have ha' : (∑ k ∈ T, (A j k^2+A i k^2)) ≤ ‖A‖^2/2 := by
    simpa only [T,add_comm] using ha
  have hprod : (∑ k ∈ T, (A j k^2+A i k^2)) * (∑ k ∈ T, (C i k^2+C j k^2)) ≤
      (‖A‖^2/2)*(‖C‖^2/2) := by
    exact mul_le_mul ha' hc
      (Finset.sum_nonneg (fun k hk => add_nonneg (sq_nonneg _) (sq_nonneg _))) (by positivity)
  have hsquare : (∑ k ∈ T, (C i k*A j k+A i k*C j k))^2 ≤ (‖A‖*‖C‖/2)^2 := by
    have hcs' : (∑ k ∈ T, (C i k*A j k+A i k*C j k))^2 ≤
        (∑ k ∈ T, (A j k^2+A i k^2)) * (∑ k ∈ T, (C i k^2+C j k^2)) := by
      simpa only [mul_comm (A j _) (C i _)] using hcs
    nlinarith
  simpa only [T, abs_of_nonneg (show (0:ℝ) ≤ ‖A‖*‖C‖/2 by positivity)] using sq_le_sq.mp hsquare
private noncomputable def upperEnvelope (a c r s : ℝ) : ℝ :=
  a^2*c^2/4 + (r^2*c^2+s^2*a^2)/2 + a*c*r*s/2-r^2*s^2/2
private theorem upper_deficit_identity (a c r s : ℝ) :
    (a^2+r^2)*(c^2+s^2)/2-upperEnvelope a c r s =
      (r*s-a*c/4)^2+3*a^2*c^2/16 := by
  unfold upperEnvelope; ring
private theorem normalization_cauchy_identity (a c r s : ℝ) :
    (a^2+r^2)*(c^2+s^2)-(a*c+r*s)^2 = (a*s-c*r)^2 := by
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm (s^2) (c^2), mul_comm r c] using
    (sq_add_sq_mul_sq_add_sq (x₁ := a) (x₂ := r) (y₁ := s) (y₂ := c))
private theorem scalar_upper_bound (a c r s k : ℝ)
    (ha : a^2+r^2=1) (hc : c^2+s^2=1)
    (hk : k ≤ upperEnvelope a c r s) : k ≤ 1/2 := by
  have h := upper_deficit_identity a c r s
  rw [ha,hc] at h
  have hprod : 0 ≤ a^2*c^2 := mul_nonneg (sq_nonneg a) (sq_nonneg c)
  nlinarith [sq_nonneg (r*s-a*c/4)]
private theorem normalization_cauchy_bound (a c r s : ℝ)
    (ha : a^2+r^2=1) (hc : c^2+s^2=1) : a*c+r*s ≤ 1 := by
  have h := normalization_cauchy_identity a c r s
  rw [ha,hc] at h
  nlinarith [sq_nonneg (a*s-c*r)]
private theorem scalar_lower_bound (a c r s k : ℝ)
    (ha : a^2+r^2=1) (hc : c^2+s^2=1)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hk : -(a*c*r*s+r^2*s^2)/2 ≤ k) : -(1/2) ≤ k := by
  have ht := normalization_cauchy_bound a c r s ha hc
  have hq : 0 ≤ r*s := mul_nonneg hr hs
  have hrs : r*s ≤ 1 := by
    have := sq_nonneg (r-s)
    nlinarith [sq_nonneg a, sq_nonneg c]
  have hqt : (r*s)*(a*c+r*s) ≤ r*s := by
    exact mul_le_of_le_one_right hq ht
  nlinarith
private theorem norm_sq_add_single {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (i j : Fin p) (t : ℝ) :
    ‖M+Matrix.single i j t‖^2 = ‖M‖^2+2*t*M i j+t^2 := by
  have hn (N : Matrix (Fin p) (Fin p) ℝ) : ‖N‖^2 = ∑ u, ∑ v, N u v^2 := by
    exact D5.S3.Combinatorics.Graph.KyFanGap.real_frobenius_sq N
  rw [hn,hn]
  simp only [Matrix.add_apply,Matrix.single_apply]
  simp_rw [add_sq]
  simp [ite_and,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,mul_ite,ite_mul]
  <;> ring
private theorem normalized_curvature_expansion {p : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (hC : Cᵀ = -C)
    (i j : Fin p) (hij : i ≠ j) (r s : ℝ) :
    euclideanSectionalCurvature A C (Matrix.single (0 : Fin 1) i r) (Matrix.single (0 : Fin 1) j s) =
      ‖A*C-C*A‖^2/4+r^2*(∑ k, C i k^2)+s^2*(∑ k, A j k^2)-
        r*s*(∑ k, (C i k*A j k+A i k*C j k))-r^2*s^2/2 := by
  classical
  let Q := A*C-C*A
  have hQ : Qᵀ = -Q := by
    dsimp [Q]
    simp [Matrix.transpose_sub,Matrix.transpose_mul,hA,hC,neg_sub]
  have hentry : Q i j = -(∑ k, A i k*C j k)+(∑ k, C i k*A j k) := by
    dsimp [Q]
    simp only [Matrix.sub_apply,Matrix.mul_apply]
    simp_rw [skew_entry C hC j,skew_entry A hA j,mul_neg,Finset.sum_neg_distrib]
    ring
  have hrow (u : Fin 1) (k : Fin p) :
      (Matrix.single (0 : Fin 1) i r*C-Matrix.single (0 : Fin 1) j s*A) u k = r*C i k-s*A j k := by
    have hu : u=0 := Subsingleton.elim _ _
    subst u
    simp
  have hrowNorm : ‖Matrix.single (0 : Fin 1) i r*C-Matrix.single (0 : Fin 1) j s*A‖^2 =
      r^2*(∑ k, C i k^2)+s^2*(∑ k, A j k^2)-2*r*s*(∑ k, C i k*A j k) := by
    change ‖WithLp.toLp 2 (fun u => WithLp.toLp 2
      ((Matrix.single (0 : Fin 1) i r*C-Matrix.single (0 : Fin 1) j s*A) u))‖^2 = _
    simp only [PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs,hrow]
    rw [Fin.sum_univ_one]
    have hid (x y : ℝ) : (r*x-s*y)^2 = r^2*x^2+s^2*y^2-2*r*s*(x*y) := by ring
    change (∑ k, (r*C i k-s*A j k)^2) = _
    calc
      _ = ∑ k, (r^2*C i k^2+s^2*A j k^2-2*r*s*(C i k*A j k)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hid (C i k) (A j k)
      _ = _ := by
        rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
        simp only [← Finset.mul_sum]
  have hbottom : Matrix.single (0 : Fin 1) i r*(Matrix.single (0 : Fin 1) j s)ᵀ-
      Matrix.single (0 : Fin 1) j s*(Matrix.single (0 : Fin 1) i r)ᵀ = 0 := by
    simp [Matrix.single_mul_single_of_ne,hij,hij.symm]
  have hw : (Matrix.single (0 : Fin 1) i r)ᵀ*Matrix.single (0 : Fin 1) j s-
      (Matrix.single (0 : Fin 1) j s)ᵀ*Matrix.single (0 : Fin 1) i r =
      Matrix.single i j (r*s)-Matrix.single j i (r*s) := by simp [mul_comm]
  have hwNorm : ‖Matrix.single i j (r*s)-Matrix.single j i (r*s)‖^2 = 2*(r*s)^2 := by
    have hn (N : Matrix (Fin p) (Fin p) ℝ) : ‖N‖^2 = ∑ u, ∑ v, N u v^2 := by
      exact D5.S3.Combinatorics.Graph.KyFanGap.real_frobenius_sq N
    rw [hn]
    simp [Matrix.sub_apply,Matrix.single_apply,ite_and,sub_sq,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_ite,ite_mul,hij,hij.symm]
    <;> ring
  have hsum : ‖Q-(Matrix.single j i (r*s)-Matrix.single i j (r*s))‖^2 =
      ‖Q‖^2+4*(r*s)*Q i j+2*(r*s)^2 := by
    have he : Q-(Matrix.single j i (r*s)-Matrix.single i j (r*s)) =
        (Q+Matrix.single i j (r*s))+Matrix.single j i (-(r*s)) := by
      rw [← Matrix.single_neg]
      abel
    have hs0 : Matrix.single i j (r*s) j i=0 := by
      exact Matrix.single_apply_of_ne i j (r*s) j i (fun h => hij h.1)
    have hsk : Q j i= -Q i j := skew_entry Q hQ i j
    rw [he,norm_sq_add_single,norm_sq_add_single]
    change ‖Q‖^2+2*(r*s)*Q i j+(r*s)^2+
      2*(-(r*s))*(Q j i+Matrix.single i j (r*s) j i)+(-(r*s))^2 = _
    rw [hs0,hsk]
    ring
  have hlast : ‖Q-((Matrix.single (0 : Fin 1) j s)ᵀ*Matrix.single (0 : Fin 1) i r-
      (Matrix.single (0 : Fin 1) i r)ᵀ*Matrix.single (0 : Fin 1) j s)‖^2 =
      ‖Q‖^2+4*(r*s)*Q i j+2*(r*s)^2 := by simpa [mul_comm] using hsum
  unfold euclideanSectionalCurvature
  rw [hrowNorm,hbottom,hw,hwNorm]
  change _+_ -_ +(1/4:ℝ)*‖Q-(_)‖^2 = _
  rw [hlast,hentry]
  simp only [Finset.sum_add_distrib, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero, add_zero]
  dsimp [Q]
  ring
private theorem normalized_lower_bound {p : ℕ} (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (hC : Cᵀ = -C) (i j : Fin p) (hij : i ≠ j)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : ‖A‖^2+r^2=1) (hc : ‖C‖^2+s^2=1) :
    -(1/2:ℝ) ≤ euclideanSectionalCurvature A C (Matrix.single (0 : Fin 1) i r) (Matrix.single (0 : Fin 1) j s) := by
  apply scalar_lower_bound ‖A‖ ‖C‖ r s _ ha hc hr hs
  rw [normalized_curvature_expansion A C hA hC i j hij]
  have he := (abs_le.mp (coupled_row_estimate A C hA hC i j hij)).2
  have hmul := mul_le_mul_of_nonneg_left he (mul_nonneg hr hs)
  have hrC : 0 ≤ r^2*(∑ k, C i k^2) := by positivity
  have hsA : 0 ≤ s^2*(∑ k, A j k^2) := by positivity
  nlinarith [sq_nonneg ‖A*C-C*A‖]
private theorem normalized_upper_bound_of_skew_commutator {p : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ)
    (hA : Aᵀ = -A) (hC : Cᵀ = -C) (i j : Fin p) (hij : i ≠ j)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : ‖A‖^2+r^2=1) (hc : ‖C‖^2+s^2=1)
    (hcomm : ‖A*C-C*A‖^2 ≤ ‖A‖^2*‖C‖^2) :
    euclideanSectionalCurvature A C (Matrix.single (0 : Fin 1) i r) (Matrix.single (0 : Fin 1) j s) ≤ (1/2:ℝ) := by
  apply scalar_upper_bound ‖A‖ ‖C‖ r s _ ha hc
  rw [normalized_curvature_expansion A C hA hC i j hij]
  have hrC := mul_le_mul_of_nonneg_left (skew_row_budget C hC i) (sq_nonneg r)
  have hsA := mul_le_mul_of_nonneg_left (skew_row_budget A hA j) (sq_nonneg s)
  have he := (abs_le.mp (coupled_row_estimate A C hA hC i j hij)).1
  have hmul := mul_le_mul_of_nonneg_left he (mul_nonneg hr hs)
  unfold upperEnvelope
  nlinarith
private theorem frobenius_unitary_left_sq {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (U : Matrix.unitaryGroup m 𝕜) (M : Matrix m n 𝕜) :
    ‖(U : Matrix m m 𝕜)*M‖^2=‖M‖^2 := by
  classical
  let T := Matrix.toEuclideanLin (U : Matrix m m 𝕜)
  have hi (v w : EuclideanSpace 𝕜 m) : inner 𝕜 (T v) (T w)=inner 𝕜 v w := by
    rw [← LinearMap.adjoint_inner_right T v (T w)]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change inner 𝕜 v (((U : Matrix m m 𝕜)ᴴ).toEuclideanLin.comp
      (U : Matrix m m 𝕜).toEuclideanLin w)=_
    rw [← Matrix.toLpLin_mul_same]
    have hU : (U : Matrix m m 𝕜)ᴴ*(U : Matrix m m 𝕜)=1 :=
      Unitary.star_mul_self_of_mem U.property
    rw [hU]
    simp only [Matrix.toLpLin_one,LinearMap.id_apply]
  let L : EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 m :=
    LinearMap.isometryOfInner T hi
  have hn (N : Matrix m n 𝕜) : ‖N‖^2 = ∑ j, ‖WithLp.toLp 2 (N.col j)‖^2 := by
    change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (N i))‖^2 = _
    simp only [PiLp.norm_sq_eq_of_L2]
    rw [Finset.sum_comm]
    rfl
  rw [hn,hn]
  apply Finset.sum_congr rfl
  intro j _
  have he := L.norm_map (WithLp.toLp 2 (M.col j))
  change ‖Matrix.toEuclideanLin (U : Matrix m m 𝕜) (WithLp.toLp 2 (M.col j))‖ = _ at he
  have he2 := congrArg (fun x : ℝ => x^2) he
  change ‖WithLp.toLp 2 (((U : Matrix m m 𝕜)*M).col j)‖^2 = _
  rw [Matrix.col_mul_eq_mulVec_col]
  simpa only [Matrix.toLpLin_apply,WithLp.ofLp_toLp] using he2
private theorem frobenius_unitary_right_sq {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n 𝕜) (M : Matrix m n 𝕜) :
    ‖M*(U : Matrix n n 𝕜)‖^2=‖M‖^2 := by
  rw [← Matrix.frobenius_norm_conjTranspose, Matrix.conjTranspose_mul,
    ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star]
  rw [frobenius_unitary_left_sq,Matrix.frobenius_norm_conjTranspose]
private theorem opposite_transport_pair_bound {n : Type*} [Fintype n] [DecidableEq n]
    (l : n → ℝ) (W : n → n → ℝ)
    (hnonneg : ∀ i k, 0 ≤ W i k)
    (hrow : ∀ i, ∑ k, W i k = 1)
    (hcol : ∀ k, ∑ i, W i k = 1)
    (hsupport : ∀ i k, l i+l k ≠ 0 → W i k=0)
    (i j : n) (hij : i ≠ j) : (l i+l j)^2 ≤ ∑ k, l k^2 := by
  classical
  have hpair : l i^2+l j^2 ≤ ∑ k, l k^2 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (s := ({i,j} : Finset n)) (t := Finset.univ) (f := fun k => l k^2)
      (Finset.subset_univ _) (fun k _ _ => sq_nonneg (l k))
    simpa [Finset.sum_pair hij] using h
  by_cases hsign : l i*l j ≤ 0
  · nlinarith
  have hpos : 0 < l i*l j := lt_of_not_ge hsign
  have hni : l i+l i ≠ 0 := by
    intro h
    have hz : l i=0 := add_self_eq_zero.mp h
    rw [hz,zero_mul] at hpos
    exact (lt_irrefl _) hpos
  have hnj : l j+l j ≠ 0 := by
    intro h
    have hz : l j=0 := add_self_eq_zero.mp h
    rw [hz,mul_zero] at hpos
    exact (lt_irrefl _) hpos
  have hsum : l i+l j ≠ 0 := by
    intro h
    have : l j = -l i := (neg_eq_of_add_eq_zero_right h).symm
    rw [this] at hpos
    nlinarith [sq_nonneg (l i)]
  have hzeroii := hsupport i i hni
  have hzeroij := hsupport i j hsum
  have hzeroji := hsupport j i (by simpa [add_comm] using hsum)
  have hzerojj := hsupport j j hnj
  have henergy (u : n) : ∑ k, l k^2*W u k = l u^2 := by
    calc
      _ = ∑ k, l u^2*W u k := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : l u+l k=0
        · have : l k= -l u := (neg_eq_of_add_eq_zero_right h).symm
          rw [this]
          ring
        · rw [hsupport u k h]
          ring
      _ = _ := by rw [← Finset.mul_sum,hrow]; ring
  have hw (k : n) : W i k+W j k ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (s := ({i,j} : Finset n)) (t := Finset.univ) (f := fun u => W u k)
      (Finset.subset_univ _) (fun u _ _ => hnonneg u k)
    simpa [Finset.sum_pair hij,hcol] using h
  have hpoint (k : n) :
      (if k=i then l i^2 else 0)+(if k=j then l j^2 else 0)+
        l k^2*(W i k+W j k) ≤ l k^2 := by
    by_cases hi : k=i
    · subst k
      simp [hij,hzeroii,hzeroji]
    by_cases hj : k=j
    · subst k
      simp [hij.symm,hzeroij,hzerojj]
    simp only [if_neg hi,if_neg hj,zero_add]
    exact (mul_le_mul_of_nonneg_left (hw k) (sq_nonneg _)).trans_eq (mul_one _)
  have htotal := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpoint k)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    mul_add,henergy] at htotal
  nlinarith [sq_nonneg (l i-l j)]
private theorem unitary_anticommuter_pair_bound {p : ℕ} (l : Fin p → ℝ)
    (S : Matrix.unitaryGroup (Fin p) ℂ)
    (hS : Matrix.diagonal (fun k => (l k : ℂ))*(S : Matrix (Fin p) (Fin p) ℂ) =
      -(S : Matrix (Fin p) (Fin p) ℂ)*Matrix.diagonal (fun k => (l k : ℂ)))
    (i j : Fin p) (hij : i ≠ j) : (l i+l j)^2 ≤ ∑ k, l k^2 := by
  let W := fun u k => ‖S u k‖^2
  apply opposite_transport_pair_bound l W (fun _ _ => sq_nonneg _) _ _ _ i j hij
  · intro u
    have h := congrArg (fun M : Matrix (Fin p) (Fin p) ℂ => (M u u).re)
      (Unitary.mul_star_self_of_mem S.property)
    simpa [W, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      RCLike.star_def,Complex.mul_conj',Complex.ofReal_sum,← Complex.ofReal_pow] using h
  · intro k
    have h := congrArg (fun M : Matrix (Fin p) (Fin p) ℂ => (M k k).re)
      (Unitary.star_mul_self_of_mem S.property)
    simpa [W, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      RCLike.star_def,Complex.conj_mul',Complex.ofReal_sum,← Complex.ofReal_pow] using h
  · intro u k hne
    have he := congrArg (fun M : Matrix (Fin p) (Fin p) ℂ => M u k) hS
    simp only [Matrix.diagonal_mul, Matrix.neg_mul, Matrix.neg_apply,Matrix.mul_diagonal] at he
    have hz : ((l u : ℂ)+(l k : ℂ))*S u k = 0 := by linear_combination he
    have hcomplex : (l u : ℂ)+(l k : ℂ) ≠ 0 := by exact_mod_cast hne
    have : S u k=0 := (mul_eq_zero.mp hz).resolve_left hcomplex
    simp [W,this]
private theorem hermitian_transpose_skew_bound {p : ℕ}
    (H C : Matrix (Fin p) (Fin p) ℂ)
    (hH : H.IsHermitian) (hHt : Hᵀ = -H) (hC : Cᵀ = -C) :
    ‖H*C+C*Hᵀ‖^2 ≤ ‖H‖^2*‖C‖^2 := by
  classical
  let U := hH.eigenvectorUnitary
  let V : Matrix (Fin p) (Fin p) ℂ := (star U : Matrix (Fin p) (Fin p) ℂ)
  let l := hH.eigenvalues
  let D : Matrix (Fin p) (Fin p) ℂ := Matrix.diagonal (fun i => (l i : ℂ))
  have hspec : H=(U : Matrix (Fin p) (Fin p) ℂ)*D*V := by
    simpa only [U,V,D,l,Unitary.conjStarAlgAut_apply,Function.comp_def,Unitary.coe_star,RCLike.ofReal_eq_complex_ofReal] using hH.spectral_theorem
  have hHU : H*(U : Matrix (Fin p) (Fin p) ℂ)=(U : Matrix (Fin p) (Fin p) ℂ)*D := by
    rw [hspec]
    simp only [V,Matrix.mul_assoc,Unitary.coe_star_mul_self,Matrix.mul_one]
  have hVH : V*H=D*V := by
    rw [hspec]
    simp only [← Matrix.mul_assoc,V,Unitary.coe_star_mul_self,Matrix.one_mul]
  let S : Matrix.unitaryGroup (Fin p) ℂ := (Matrix.UnitaryGroup.transpose U)*U
  have hS : D*(S : Matrix (Fin p) (Fin p) ℂ)=
      -(S : Matrix (Fin p) (Fin p) ℂ)*D := by
    have ht := congrArg Matrix.transpose hHU
    simp only [Matrix.transpose_mul,show Dᵀ=D from Matrix.diagonal_transpose _,hHt] at ht
    change D*((U : Matrix (Fin p) (Fin p) ℂ)ᵀ*U)=
      -((U : Matrix (Fin p) (Fin p) ℂ)ᵀ*U)*D
    calc
      _ = (D*(U : Matrix (Fin p) (Fin p) ℂ)ᵀ)*U := (Matrix.mul_assoc _ _ _).symm
      _ = ((U : Matrix (Fin p) (Fin p) ℂ)ᵀ*(-H))*U := by rw [ht]
      _ = -((U : Matrix (Fin p) (Fin p) ℂ)ᵀ*(H*U)) := by simp [Matrix.mul_assoc]
      _ = _ := by rw [hHU]; simp [Matrix.mul_assoc]
  have hpair := unitary_anticommuter_pair_bound l S hS
  let C' := V*C*Vᵀ
  have hC't : C'ᵀ = -C' := by
    dsimp [C']
    simp [Matrix.transpose_mul,Matrix.transpose_transpose,hC,Matrix.mul_assoc]
  have hdiag (i : Fin p) : C' i i=0 := by
    exact CharZero.eq_neg_self_iff.mp (congrFun (congrFun hC't i) i)
  have hcongNorm (M : Matrix (Fin p) (Fin p) ℂ) : ‖V*M*Vᵀ‖^2=‖M‖^2 := by
    change ‖(star U : Matrix (Fin p) (Fin p) ℂ)*M*
      (Matrix.UnitaryGroup.transpose (star U) : Matrix (Fin p) (Fin p) ℂ)‖^2 = _
    rw [frobenius_unitary_right_sq (Matrix.UnitaryGroup.transpose (star U))]
    simpa only [Unitary.coe_star] using frobenius_unitary_left_sq (star U) M
  have htransform : V*(H*C+C*Hᵀ)*Vᵀ=D*C'+C'*D := by
    have ht := congrArg Matrix.transpose hVH
    simp only [Matrix.transpose_mul,show Dᵀ=D from Matrix.diagonal_transpose _] at ht
    dsimp [C']
    rw [Matrix.mul_add,Matrix.add_mul]
    simp only [← Matrix.mul_assoc,hVH]
    simp only [Matrix.mul_assoc,ht]
  have hHnorm : ‖H‖^2 = ∑ i, l i^2 := by
    rw [hspec]
    change ‖(U : Matrix (Fin p) (Fin p) ℂ)*D*(star U : Matrix (Fin p) (Fin p) ℂ)‖^2 = _
    calc
      _ = ‖(U : Matrix (Fin p) (Fin p) ℂ)*D‖^2 := by
        simpa only [Unitary.coe_star] using
          frobenius_unitary_right_sq (star U) ((U : Matrix (Fin p) (Fin p) ℂ)*D)
      _ = ‖D‖^2 := frobenius_unitary_left_sq U D
      _ = _ := by
        simp only [D,Matrix.frobenius_norm_diagonal,PiLp.norm_sq_eq_of_L2,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hn (M : Matrix (Fin p) (Fin p) ℂ) : ‖M‖^2=∑ i, ∑ j, ‖M i j‖^2 := by
    apply Complex.ofReal_injective
    calc
      ((‖M‖^2 : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) :=
        D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace M
      _ = ((∑ i, ∑ j, ‖M i j‖^2 : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sum, Complex.ofReal_pow, Matrix.trace, Matrix.diag_apply,
          Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']
        rw [Finset.sum_comm]
  have hbound : ‖D*C'+C'*D‖^2 ≤ (∑ i, l i^2)*‖C'‖^2 := by
    rw [hn,hn]
    calc
      _ = ∑ i, ∑ j, (l i+l j)^2*‖C' i j‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [Matrix.add_apply,D,Matrix.diagonal_mul,Matrix.mul_diagonal]
        rw [mul_comm (C' i j),← add_mul,← Complex.ofReal_add,norm_mul,mul_pow]
        simp only [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      _ ≤ ∑ i, ∑ j, (∑ k, l k^2)*‖C' i j‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i=j
        · subst j
          simp [hdiag]
        · exact mul_le_mul_of_nonneg_right (hpair i j hij) (sq_nonneg _)
      _ = _ := by simp_rw [← Finset.mul_sum]
  rw [← hHnorm] at hbound
  have hCn : ‖C'‖^2=‖C‖^2 := hcongNorm C
  rw [hCn] at hbound
  have hEn : ‖D*C'+C'*D‖^2 = ‖H*C+C*Hᵀ‖^2 := by
    rw [← htransform,hcongNorm]
  rw [hEn] at hbound
  exact hbound
private theorem real_skew_commutator_bound {p : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (hA : Aᵀ = -A) (hC : Cᵀ = -C) :
    ‖A*C-C*A‖^2 ≤ ‖A‖^2*‖C‖^2 := by
  let F : Matrix (Fin p) (Fin p) ℝ →+* Matrix (Fin p) (Fin p) ℂ :=
    Complex.ofRealHom.mapMatrix
  have hnorm (M : Matrix (Fin p) (Fin p) ℝ) : ‖F M‖=‖M‖ := by
    apply Matrix.frobenius_norm_map_eq
    intro x
    exact Complex.norm_real x
  have hAt : (F A)ᵀ= -(F A) := by
    change F Aᵀ= -(F A)
    simpa only [map_neg] using congrArg F hA
  have hCt : (F C)ᵀ= -(F C) := by
    change F Cᵀ= -(F C)
    simpa only [map_neg] using congrArg F hC
  have hAstar : (F A)ᴴ= -(F A) := by
    have he : (F A)ᴴ=(F A)ᵀ := by ext i j; simp [F]
    rw [he,hAt]
  let H : Matrix (Fin p) (Fin p) ℂ := Complex.I • F A
  have hH : H.IsHermitian := by
    change Hᴴ=H
    simp [H,Matrix.conjTranspose_smul,hAstar]
  have hHt : Hᵀ= -H := by simp [H,Matrix.transpose_smul,hAt]
  have heq : H*F C+F C*Hᵀ=Complex.I • F (A*C-C*A) := by
    rw [hHt]
    simp only [H,map_sub,map_mul,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.mul_neg,smul_sub]
    module
  have hb := hermitian_transpose_skew_bound H (F C) hH hHt hCt
  rw [heq] at hb
  simpa only [H,norm_smul,Complex.norm_I,one_mul,hnorm] using hb
private theorem real_gram_extension
    {m n : Type*} [Fintype m] [DecidableEq m] [Finite n]
    (B A : Matrix m n ℝ)
    (hGram : Bᴴ * B = Aᴴ * A) :
    ∃ U : Matrix.unitaryGroup m ℝ, B = (U : Matrix m m ℝ) * A := by
  classical
  let : Fintype n := Fintype.ofFinite n
  let : InnerProductSpace ℝ (EuclideanSpace ℝ m) :=
    PiLp.innerProductSpace (fun _ : m => ℝ)
  let : FiniteDimensional ℝ (EuclideanSpace ℝ m) :=
    (EuclideanSpace.basisFun m ℝ).toBasis.finiteDimensional_of_finite
  let fB : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ m :=
    Matrix.toEuclideanLin B
  let fA : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ m :=
    Matrix.toEuclideanLin A
  have hinner : ∀ v w : EuclideanSpace ℝ n,
      ⟪fB v, fB w⟫_ℝ = ⟪fA v, fA w⟫_ℝ := by
    intro v w
    rw [← LinearMap.adjoint_inner_right fB v (fB w),
        ← LinearMap.adjoint_inner_right fA v (fA w)]
    congr 1
    change fB.adjoint (fB w) = fA.adjoint (fA w)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
    change (Bᴴ.toEuclideanLin.comp B.toEuclideanLin) w =
      (Aᴴ.toEuclideanLin.comp A.toEuclideanLin) w
    rw [← toLpLin_mul_same, ← toLpLin_mul_same, hGram]
  have hker : LinearMap.ker fA ≤ LinearMap.ker fB := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h0 := hinner v v
    simp only [hv, inner_zero_left] at h0
    exact inner_self_eq_zero.mp h0
  let L_lm : LinearMap.range fA →ₗ[ℝ] EuclideanSpace ℝ m :=
    ((LinearMap.ker fA).liftQ fB hker).comp
      fA.quotKerEquivRange.symm.toLinearMap
  have hL_apply : ∀ v, L_lm ⟨fA v, LinearMap.mem_range_self fA v⟩ = fB v := by
    intro v
    change ((LinearMap.ker fA).liftQ fB hker)
        (fA.quotKerEquivRange.symm ⟨fA v, LinearMap.mem_range_self fA v⟩) =
      fB v
    rw [fA.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  have hL_inner : ∀ x y : LinearMap.range fA,
      ⟪L_lm x, L_lm y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    rw [hL_apply, hL_apply, hinner, Submodule.coe_inner]
  let L_iso : LinearMap.range fA →ₗᵢ[ℝ] EuclideanSpace ℝ m :=
    LinearMap.isometryOfInner L_lm hL_inner
  let U := L_iso.extend
  have hU_eq : ∀ v, U (fA v) = fB v := by
    intro v
    have : U (fA v) = L_iso ⟨fA v, LinearMap.mem_range_self fA v⟩ :=
      LinearIsometry.extend_apply L_iso ⟨fA v, LinearMap.mem_range_self fA v⟩
    rw [this]
    simpa [L_iso] using hL_apply v
  let U_mat : Matrix m m ℝ :=
    Matrix.toEuclideanLin.symm U.toLinearMap
  have h_U_lin : Matrix.toEuclideanLin U_mat = U.toLinearMap :=
    LinearEquiv.apply_symm_apply Matrix.toEuclideanLin U.toLinearMap
  have hU_unitary : U_matᴴ * U_mat = 1 := by
    apply Matrix.toEuclideanLin.injective
    ext1 v
    have hadj : U.toLinearMap.adjoint (U.toLinearMap v) = v :=
      ext_inner_right ℝ fun y => by
        rw [LinearMap.adjoint_inner_left]
        exact LinearIsometry.inner_map_map U v y
    rw [toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, h_U_lin, hadj]
    simp only [toLpLin_one, LinearMap.id_apply]
  have hU_mat_eq : U_mat * A = B := by
    apply Matrix.toEuclideanLin.injective
    ext1 v
    rw [toLpLin_mul_same, LinearMap.comp_apply, h_U_lin]
    exact hU_eq v
  refine ⟨⟨U_mat, Matrix.mem_unitaryGroup_iff'.2 hU_unitary⟩, ?_⟩
  exact hU_mat_eq.symm
private theorem row_gram_diagonalization {p : ℕ} (R : Matrix (Fin 2) (Fin p) ℝ) :
    ∃ P : Matrix.unitaryGroup (Fin 2) ℝ,
      (∑ k, ((P : Matrix (Fin 2) (Fin 2) ℝ)*R) 0 k *
        ((P : Matrix (Fin 2) (Fin 2) ℝ)*R) 1 k) = 0 := by
  let H := R*Rᴴ
  have hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self R
  let U := hH.eigenvectorUnitary
  refine ⟨star U, ?_⟩
  have hd := hH.conjStarAlgAut_star_eigenvectorUnitary
  change Unitary.conjStarAlgAut ℝ _ (star U) H = _ at hd
  rw [Unitary.conjStarAlgAut_star_apply] at hd
  have hg : ((star U : Matrix (Fin 2) (Fin 2) ℝ)*R)*
      (((star U : Matrix (Fin 2) (Fin 2) ℝ)*R)ᴴ) =
      Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    calc
      _ = (star U : Matrix (Fin 2) (Fin 2) ℝ)*H*U := by
        dsimp [H]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Unitary.coe_star,
          star_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      _ = _ := hd
  have hz := congrFun (congrFun hg 0) 1
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
    Unitary.coe_star, Matrix.diagonal_apply_ne _ (by decide : (0:Fin 2) ≠ 1)] using hz
private theorem two_row_orthogonal_normal_form {p : ℕ}
    (R : Matrix (Fin 2) (Fin p) ℝ) (i j : Fin p) (hij : i ≠ j) :
    ∃ (P : Matrix.unitaryGroup (Fin 2) ℝ) (Q : Matrix.unitaryGroup (Fin p) ℝ)
        (r s : ℝ),
      0 ≤ r ∧ 0 ≤ s ∧ (P : Matrix (Fin 2) (Fin 2) ℝ)*R*(Q : Matrix (Fin p) (Fin p) ℝ) =
        Matrix.single (0:Fin 2) i r + Matrix.single (1:Fin 2) j s := by
  classical
  obtain ⟨P,hP⟩ := row_gram_diagonalization R
  let R' : Matrix (Fin 2) (Fin p) ℝ := (P : Matrix (Fin 2) (Fin 2) ℝ)*R
  change (∑ k, R' 0 k*R' 1 k)=0 at hP
  let r := ‖WithLp.toLp 2 (R' 0)‖
  let s := ‖WithLp.toLp 2 (R' 1)‖
  let S : Matrix (Fin 2) (Fin p) ℝ := Matrix.single (0:Fin 2) i r + Matrix.single (1:Fin 2) j s
  have hnorm (u : Fin 2) : (R'*R'ᴴ) u u = ‖WithLp.toLp 2 (R' u)‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      Real.norm_eq_abs,sq_abs]
    simp only [pow_two]
  have hRdiag : R'*R'ᴴ = Matrix.diagonal ![r^2,s^2] := by
    ext u v
    fin_cases u <;> fin_cases v
    · simpa [r] using hnorm 0
    · change (∑ k, R' 0 k*R' 1 k)=0
      exact hP
    · change (∑ k, R' 1 k*R' 0 k)=0
      simpa only [mul_comm] using hP
    · simpa [s] using hnorm 1
  have hSdiag : S*Sᴴ = Matrix.diagonal ![r^2,s^2] := by
    ext u v
    fin_cases u <;> fin_cases v <;>
      simp [S,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.single_apply,
        Matrix.diagonal_apply,ite_and,Finset.sum_add_distrib,add_mul,mul_add,
        mul_ite,ite_mul,hij,hij.symm,pow_two]
  have hGram : (Sᵀ)ᴴ*Sᵀ = (R'ᵀ)ᴴ*R'ᵀ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose]
      using hSdiag.trans hRdiag.symm
  obtain ⟨U,hU⟩ := real_gram_extension Sᵀ R'ᵀ hGram
  refine ⟨P,star U,r,s,norm_nonneg _,norm_nonneg _,?_⟩
  have ht := congrArg Matrix.transpose hU
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose] at ht
  change R'*(star U : Matrix (Fin p) (Fin p) ℝ)=S
  simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact ht.symm
private theorem alternating_product_transform {p q : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (b d : Matrix (Fin q) (Fin p) ℝ)
    (x y z w : ℝ) :
    (x • b+y • d)*(z • A+w • C)-(z • b+w • d)*(x • A+y • C) =
      (x*w-y*z) • (b*C-d*A) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  module
private theorem alternating_outer_transform {p q : ℕ}
    (b d : Matrix (Fin q) (Fin p) ℝ) (x y z w : ℝ) :
    (x • b+y • d)*(z • b+w • d)ᵀ-(z • b+w • d)*(x • b+y • d)ᵀ =
      (x*w-y*z) • (b*dᵀ-d*bᵀ) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  module
private theorem alternating_inner_transform {p q : ℕ}
    (b d : Matrix (Fin q) (Fin p) ℝ) (x y z w : ℝ) :
    (x • b+y • d)ᵀ*(z • b+w • d)-(z • b+w • d)ᵀ*(x • b+y • d) =
      (x*w-y*z) • (bᵀ*d-dᵀ*b) := by
  simpa only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_transpose] using
    alternating_outer_transform bᵀ dᵀ x y z w
private theorem commutator_transform {p : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (x y z w : ℝ) :
    (x • A+y • C)*(z • A+w • C)-(z • A+w • C)*(x • A+y • C) =
      (x*w-y*z) • (A*C-C*A) := by
  exact alternating_product_transform A C A C x y z w
private theorem plane_change_curvature {p q : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (b d : Matrix (Fin q) (Fin p) ℝ)
    (x y z w : ℝ) :
    euclideanSectionalCurvature (x • A+y • C) (z • A+w • C)
      (x • b+y • d) (z • b+w • d) =
      (x*w-y*z)^2 * euclideanSectionalCurvature A C b d := by
  unfold euclideanSectionalCurvature
  rw [alternating_product_transform, alternating_outer_transform,
    alternating_inner_transform, commutator_transform]
  rw [show ((z • b+w • d)ᵀ*(x • b+y • d)-(x • b+y • d)ᵀ*(z • b+w • d)) =
      -(x*w-y*z) • (bᵀ*d-dᵀ*b) by
    rw [← neg_sub,alternating_inner_transform]; module]
  rw [show (x*w-y*z) • (A*C-C*A)-(-(x*w-y*z) • (bᵀ*d-dᵀ*b)) =
      (x*w-y*z) • ((A*C-C*A)-(dᵀ*b-bᵀ*d)) by module]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring
private theorem frobenius_linear_combination_sq {m n : ℕ}
    (A C : Matrix (Fin m) (Fin n) ℝ) (x y : ℝ) :
    ‖x • A+y • C‖^2=x^2*‖A‖^2+y^2*‖C‖^2+
      2*x*y*Matrix.trace (Aᵀ*C) := by
  have hn (M : Matrix (Fin m) (Fin n) ℝ) : ‖M‖^2=∑ i, ∑ k, M i k^2 := by
    exact D5.S3.Combinatorics.Graph.KyFanGap.real_frobenius_sq M
  have ht : Matrix.trace (Aᵀ*C)=∑ i, ∑ k, A i k*C i k := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [hn,hn,hn,ht]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  have hp (a c : ℝ) : (x*a+y*c)^2=x^2*a^2+y^2*c^2+2*x*y*(a*c) := by ring
  simp_rw [hp,Finset.sum_add_distrib,← Finset.mul_sum]
private theorem trace_linear_combination {m n : ℕ}
    (A C : Matrix (Fin m) (Fin n) ℝ) (x y z w : ℝ) :
    Matrix.trace ((x • A+y • C)ᵀ*(z • A+w • C)) =
      x*z*‖A‖^2+y*w*‖C‖^2+(x*w+y*z)*Matrix.trace (Aᵀ*C) := by
  have hn (M : Matrix (Fin m) (Fin n) ℝ) : ‖M‖^2=∑ i, ∑ k, M i k^2 := by
    exact D5.S3.Combinatorics.Graph.KyFanGap.real_frobenius_sq M
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [hn,hn]
  have hp (a c : ℝ) : (x*a+y*c)*(z*a+w*c)=x*z*a^2+y*w*c^2+(x*w+y*z)*(a*c) := by ring
  simp_rw [hp,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i k => A k i^2),
    Finset.sum_comm (f := fun i k => C k i^2)]
private theorem plane_change_orthonormal {p q : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (b d : Matrix (Fin q) (Fin p) ℝ)
    (h : orthonormalTangentBlocks A C b d) (x y z w : ℝ)
    (hxy : x^2+y^2=1) (hzw : z^2+w^2=1) (hcross : x*z+y*w=0) :
    orthonormalTangentBlocks (x • A+y • C) (z • A+w • C)
      (x • b+y • d) (z • b+w • d) := by
  obtain ⟨hA,hC,hnA,hnC,horth⟩ := h
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [Matrix.transpose_add,Matrix.transpose_smul,hA,hC,smul_neg,neg_add,add_comm]
  · simp [Matrix.transpose_add,Matrix.transpose_smul,hA,hC,smul_neg,neg_add,add_comm]
  · rw [frobenius_linear_combination_sq,frobenius_linear_combination_sq]
    linear_combination x^2*hnA+y^2*hnC+2*x*y*horth+hxy
  · rw [frobenius_linear_combination_sq,frobenius_linear_combination_sq]
    linear_combination z^2*hnA+w^2*hnC+2*z*w*horth+hzw
  · rw [trace_linear_combination,trace_linear_combination]
    linear_combination x*z*hnA+y*w*hnC+(x*w+y*z)*horth+hcross
private theorem ambient_change_curvature {p q : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (b d : Matrix (Fin q) (Fin p) ℝ)
    (Q : Matrix.unitaryGroup (Fin p) ℝ) :
    euclideanSectionalCurvature ((star Q : Matrix (Fin p) (Fin p) ℝ)*A*(Q : Matrix (Fin p) (Fin p) ℝ))
      ((star Q : Matrix (Fin p) (Fin p) ℝ)*C*(Q : Matrix (Fin p) (Fin p) ℝ)) (b*(Q : Matrix (Fin p) (Fin p) ℝ)) (d*(Q : Matrix (Fin p) (Fin p) ℝ)) =
      euclideanSectionalCurvature A C b d := by
  have hQt : (Q : Matrix (Fin p) (Fin p) ℝ)ᵀ=(star Q : Matrix (Fin p) (Fin p) ℝ) := rfl
  have hQQ : (Q : Matrix (Fin p) (Fin p) ℝ)*star (Q : Matrix (Fin p) (Fin p) ℝ)=1 :=
    Unitary.mul_star_self_of_mem Q.property
  have hcancel {t : ℕ} (M : Matrix (Fin p) (Fin t) ℝ) :
      (Q : Matrix (Fin p) (Fin p) ℝ)*((star Q : Matrix (Fin p) (Fin p) ℝ)*M)=M := by
    rw [← Matrix.mul_assoc,hQQ,Matrix.one_mul]
  have hleft (M : Matrix (Fin p) (Fin p) ℝ) :
      ‖star (Q : Matrix (Fin p) (Fin p) ℝ)*M‖^2=‖M‖^2 := by
    simpa only [Unitary.coe_star] using frobenius_unitary_left_sq (star Q) M
  have h1 : b*(Q : Matrix (Fin p) (Fin p) ℝ)*((star Q : Matrix (Fin p) (Fin p) ℝ)*C*(Q : Matrix (Fin p) (Fin p) ℝ))-
      d*(Q : Matrix (Fin p) (Fin p) ℝ)*((star Q : Matrix (Fin p) (Fin p) ℝ)*A*(Q : Matrix (Fin p) (Fin p) ℝ))=(b*C-d*A)*(Q : Matrix (Fin p) (Fin p) ℝ) := by
    simp [Matrix.sub_mul,Matrix.mul_assoc,hcancel]
  have h2 : b*(Q : Matrix (Fin p) (Fin p) ℝ)*(d*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ-d*(Q : Matrix (Fin p) (Fin p) ℝ)*(b*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ=b*dᵀ-d*bᵀ := by
    simp [Matrix.transpose_mul,hQt,Matrix.mul_assoc,hcancel,Unitary.coe_mul_star_self]
  have h3 : (b*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ*(d*(Q : Matrix (Fin p) (Fin p) ℝ))-(d*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ*(b*(Q : Matrix (Fin p) (Fin p) ℝ))=
      (star Q : Matrix (Fin p) (Fin p) ℝ)*(bᵀ*d-dᵀ*b)*(Q : Matrix (Fin p) (Fin p) ℝ) := by
    simp [Matrix.transpose_mul,hQt,Matrix.mul_assoc,Matrix.mul_sub,Matrix.sub_mul]
  have h4 : ((star Q : Matrix (Fin p) (Fin p) ℝ)*A*(Q : Matrix (Fin p) (Fin p) ℝ))*
      ((star Q : Matrix (Fin p) (Fin p) ℝ)*C*(Q : Matrix (Fin p) (Fin p) ℝ))-
      ((star Q : Matrix (Fin p) (Fin p) ℝ)*C*(Q : Matrix (Fin p) (Fin p) ℝ))*
      ((star Q : Matrix (Fin p) (Fin p) ℝ)*A*(Q : Matrix (Fin p) (Fin p) ℝ))-
      ((d*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ*(b*(Q : Matrix (Fin p) (Fin p) ℝ))-(b*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ*(d*(Q : Matrix (Fin p) (Fin p) ℝ))) =
      (star Q : Matrix (Fin p) (Fin p) ℝ)*
        ((A*C-C*A)-(dᵀ*b-bᵀ*d))*(Q : Matrix (Fin p) (Fin p) ℝ) := by
    simp [Matrix.transpose_mul,hQt,Matrix.mul_assoc,hcancel,Unitary.coe_mul_star_self,
      Matrix.mul_sub,Matrix.sub_mul]
  unfold euclideanSectionalCurvature
  rw [h1,h2,h3,h4,frobenius_unitary_right_sq,frobenius_unitary_right_sq,
    hleft,frobenius_unitary_right_sq,hleft]
private theorem ambient_change_orthonormal {p q : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (b d : Matrix (Fin q) (Fin p) ℝ)
    (h : orthonormalTangentBlocks A C b d)
    (Q : Matrix.unitaryGroup (Fin p) ℝ) :
    orthonormalTangentBlocks ((star Q : Matrix (Fin p) (Fin p) ℝ)*A*(Q : Matrix (Fin p) (Fin p) ℝ))
      ((star Q : Matrix (Fin p) (Fin p) ℝ)*C*(Q : Matrix (Fin p) (Fin p) ℝ)) (b*(Q : Matrix (Fin p) (Fin p) ℝ)) (d*(Q : Matrix (Fin p) (Fin p) ℝ)) := by
  obtain ⟨hA,hC,hnA,hnC,horth⟩ := h
  have hQt : (Q : Matrix (Fin p) (Fin p) ℝ)ᵀ=(star Q : Matrix (Fin p) (Fin p) ℝ) := rfl
  have hQQ : (Q : Matrix (Fin p) (Fin p) ℝ)*star (Q : Matrix (Fin p) (Fin p) ℝ)=1 :=
    Unitary.mul_star_self_of_mem Q.property
  have hcancel {t : ℕ} (M : Matrix (Fin p) (Fin t) ℝ) :
      (Q : Matrix (Fin p) (Fin p) ℝ)*((star Q : Matrix (Fin p) (Fin p) ℝ)*M)=M := by
    rw [← Matrix.mul_assoc,hQQ,Matrix.one_mul]
  have hleft (M : Matrix (Fin p) (Fin p) ℝ) :
      ‖star (Q : Matrix (Fin p) (Fin p) ℝ)*M‖^2=‖M‖^2 := by
    simpa only [Unitary.coe_star] using frobenius_unitary_left_sq (star Q) M
  have hVt : (star Q : Matrix (Fin p) (Fin p) ℝ)ᵀ=(Q : Matrix (Fin p) (Fin p) ℝ) := by
    exact Eq.symm (ext fun i => congrFun rfl)
  have hconjTrace (M : Matrix (Fin p) (Fin p) ℝ) :
      Matrix.trace ((star Q : Matrix (Fin p) (Fin p) ℝ)*M*(Q : Matrix (Fin p) (Fin p) ℝ))=Matrix.trace M := by
    rw [Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc,hcancel,Unitary.coe_mul_star_self]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [Matrix.transpose_mul,hQt,hVt,hA,Matrix.mul_assoc]
  · simp [Matrix.transpose_mul,hQt,hVt,hC,Matrix.mul_assoc]
  · rw [frobenius_unitary_right_sq,hleft,frobenius_unitary_right_sq]
    exact hnA
  · rw [frobenius_unitary_right_sq,hleft,frobenius_unitary_right_sq]
    exact hnC
  · have he : (((star Q : Matrix (Fin p) (Fin p) ℝ)*A*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ*
        ((star Q : Matrix (Fin p) (Fin p) ℝ)*C*(Q : Matrix (Fin p) (Fin p) ℝ))) =
        (star Q : Matrix (Fin p) (Fin p) ℝ)*(Aᵀ*C)*(Q : Matrix (Fin p) (Fin p) ℝ) := by
      simp [Matrix.transpose_mul,hQt,hVt,Matrix.mul_assoc,hcancel,Unitary.coe_mul_star_self]
    have hb : (b*(Q : Matrix (Fin p) (Fin p) ℝ))ᵀ*(d*(Q : Matrix (Fin p) (Fin p) ℝ))=(star Q : Matrix (Fin p) (Fin p) ℝ)*(bᵀ*d)*(Q : Matrix (Fin p) (Fin p) ℝ) := by
      simp [Matrix.transpose_mul,hQt,Matrix.mul_assoc]
    rw [he,hb,hconjTrace,hconjTrace]
    exact horth
private theorem single_norm_sq {m n : ℕ} (i : Fin m) (j : Fin n) (a : ℝ) :
    ‖Matrix.single i j a‖ ^ 2 = a^2 := by
  change ‖WithLp.toLp 2 (fun u => WithLp.toLp 2 (Matrix.single i j a u))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Matrix.single, ite_and]
private theorem disjoint_single_sub_norm_sq {m n : ℕ}
    (i k : Fin m) (j l : Fin n) (hik : i ≠ k) (a b : ℝ) :
    ‖Matrix.single i j a - Matrix.single k l b‖^2 = a^2+b^2 := by
  change ‖WithLp.toLp 2 (fun u => WithLp.toLp 2 ((Matrix.single i j a - Matrix.single k l b) u))‖ ^ 2 = _
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Matrix.sub_apply,
    Matrix.single_apply]
  simp [ite_and, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_ite, ite_mul, hik, hik.symm]
private theorem lower_endpoint_pair {p : ℕ} (i j : Fin p) (hij : i ≠ j) :
    orthonormalTangentBlocks (0 : Matrix (Fin p) (Fin p) ℝ) 0
      (Matrix.single (0 : Fin 1) i 1) (Matrix.single (0 : Fin 1) j 1) ∧
    euclideanSectionalCurvature (0 : Matrix (Fin p) (Fin p) ℝ) 0
      (Matrix.single (0 : Fin 1) i 1) (Matrix.single (0 : Fin 1) j 1) = -(1/2:ℝ) := by
  constructor
  · simp [orthonormalTangentBlocks, single_norm_sq, Matrix.transpose_single,
      Matrix.single_mul_single_same, Matrix.trace_single_eq_of_ne, hij]
  · unfold euclideanSectionalCurvature
    simp [Matrix.transpose_single, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne, hij, hij.symm,
      disjoint_single_sub_norm_sq i j j i hij,
      disjoint_single_sub_norm_sq j i i j hij.symm]
    <;> norm_num
private theorem upper_endpoint_pair {p : ℕ} (i j : Fin p) (hij : i ≠ j)
    (r : ℝ) (hr : 2*r^2=1) :
    orthonormalTangentBlocks (0 : Matrix (Fin p) (Fin p) ℝ)
      (Matrix.single i j r-Matrix.single j i r)
      (Matrix.single (0 : Fin 1) i 1) 0 ∧
    euclideanSectionalCurvature (0 : Matrix (Fin p) (Fin p) ℝ)
      (Matrix.single i j r-Matrix.single j i r)
      (Matrix.single (0 : Fin 1) i 1) 0 = (1/2:ℝ) := by
  have hc : (Matrix.single i j r-Matrix.single j i r)ᵀ =
      -(Matrix.single i j r-Matrix.single j i r) := by
    simp [Matrix.transpose_sub, neg_sub]
  have hn := disjoint_single_sub_norm_sq i j j i hij r r
  have hprod : (Matrix.single (0 : Fin 1) i (1:ℝ)) *
      (Matrix.single i j r-Matrix.single j i r) = Matrix.single (0 : Fin 1) j r := by
    simp [Matrix.mul_sub, Matrix.single_mul_single_of_ne, hij]
  constructor
  · simp [orthonormalTangentBlocks, hc, hn, single_norm_sq]
    linarith
  · simp [euclideanSectionalCurvature, hprod, single_norm_sq]
    linarith
private theorem all_dimensions_endpoints (n : ℕ) (hn : 4 ≤ n) :
    (∃ (A C : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)
        (b d : Matrix (Fin 1) (Fin (n-1)) ℝ),
      orthonormalTangentBlocks A C b d ∧ euclideanSectionalCurvature A C b d = -(1/2:ℝ)) ∧
    (∃ (A C : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)
        (b d : Matrix (Fin 1) (Fin (n-1)) ℝ),
      orthonormalTangentBlocks A C b d ∧ euclideanSectionalCurvature A C b d = (1/2:ℝ)) := by
  have hp : 2 ≤ n-1 := by omega
  let i : Fin (n-1) := ⟨0,by omega⟩
  let j : Fin (n-1) := ⟨1,by omega⟩
  have hij : i ≠ j := by exact not_eq_of_beq_eq_false rfl
  constructor
  · exact ⟨0,0,Matrix.single (0 : Fin 1) i 1,Matrix.single (0 : Fin 1) j 1,lower_endpoint_pair i j hij⟩
  · have hr : 2*(Real.sqrt (1/2))^2=1 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    exact ⟨0,_,_,0,upper_endpoint_pair i j hij (Real.sqrt (1/2)) hr⟩
private theorem codimension_one_normalization {p : ℕ}
    (A C : Matrix (Fin p) (Fin p) ℝ) (b d : Matrix (Fin 1) (Fin p) ℝ)
    (h : orthonormalTangentBlocks A C b d) (i j : Fin p) (hij : i ≠ j) :
    ∃ (A' C' : Matrix (Fin p) (Fin p) ℝ) (r s : ℝ),
      0 ≤ r ∧ 0 ≤ s ∧
      orthonormalTangentBlocks A' C' (Matrix.single (0 : Fin 1) i r) (Matrix.single (0 : Fin 1) j s) ∧
      euclideanSectionalCurvature A' C' (Matrix.single (0 : Fin 1) i r) (Matrix.single (0 : Fin 1) j s) =
        euclideanSectionalCurvature A C b d := by
  classical
  let R : Matrix (Fin 2) (Fin p) ℝ := ![b 0,d 0]
  obtain ⟨P,Q,r,s,hr,hs,hNF⟩ := two_row_orthogonal_normal_form R i j hij
  let x := P 0 0
  let y := P 0 1
  let z := P 1 0
  let w := P 1 1
  have hPP := Unitary.mul_star_self_of_mem P.property
  have hxy : x^2+y^2=1 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hPP
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,pow_two,x,y] using he
  have hzw : z^2+w^2=1 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hPP
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,pow_two,z,w] using he
  have hcross : x*z+y*w=0 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hPP
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,x,y,z,w] using he
  have hdet : (x*w-y*z)^2=1 := by
    have he := (Matrix.det_of_mem_unitary P.property).1
    simpa [Matrix.det_fin_two,star_trivial,pow_two,x,y,z,w] using he
  have hb : (x • b+y • d)*(Q : Matrix (Fin p) (Fin p) ℝ)=Matrix.single (0 : Fin 1) i r := by
    ext u k
    have hu : u=0 := Subsingleton.elim _ _
    subst u
    have he := congrArg (fun M : Matrix (Fin 2) (Fin p) ℝ => M 0 k) hNF
    simpa [Matrix.mul_apply,Fin.sum_univ_two,R,x,y,z,w,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,Matrix.single_apply] using he
  have hd : (z • b+w • d)*(Q : Matrix (Fin p) (Fin p) ℝ)=Matrix.single (0 : Fin 1) j s := by
    ext u k
    have hu : u=0 := Subsingleton.elim _ _
    subst u
    have he := congrArg (fun M : Matrix (Fin 2) (Fin p) ℝ => M 1 k) hNF
    simpa [Matrix.mul_apply,Fin.sum_univ_two,R,x,y,z,w,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,Matrix.single_apply] using he
  let A' := (star Q : Matrix (Fin p) (Fin p) ℝ)*(x • A+y • C)*(Q : Matrix (Fin p) (Fin p) ℝ)
  let C' := (star Q : Matrix (Fin p) (Fin p) ℝ)*(z • A+w • C)*(Q : Matrix (Fin p) (Fin p) ℝ)
  have hrot := plane_change_orthonormal A C b d h x y z w hxy hzw hcross
  have hamb := ambient_change_orthonormal _ _ _ _ hrot Q
  rw [hb,hd] at hamb
  refine ⟨A',C',r,s,hr,hs,hamb,?_⟩
  have he := ambient_change_curvature (x • A+y • C) (z • A+w • C)
    (x • b+y • d) (z • b+w • d) Q
  rw [hb,hd,plane_change_curvature,hdet,one_mul] at he
  exact he
theorem result : claim := by
  intro n hn
  obtain ⟨hlo,hhi⟩ := all_dimensions_endpoints n hn
  refine ⟨?_,hlo,hhi⟩
  intro A C b d h
  let i : Fin (n-1) := ⟨0,by omega⟩
  let j : Fin (n-1) := ⟨1,by omega⟩
  have hij : i ≠ j := by exact not_eq_of_beq_eq_false rfl
  obtain ⟨A',C',r,s,hr,hs,hON,hK⟩ := codimension_one_normalization A C b d h i j hij
  have hsingle (k : Fin (n-1)) (t : ℝ) : ‖Matrix.single (0 : Fin 1) k t‖^2=t^2 := by
    exact single_norm_sq (0 : Fin 1) k t
  obtain ⟨hA',hC',hnA',hnC',_⟩ := hON
  rw [hsingle] at hnA' hnC'
  have hblo := normalized_lower_bound A' C' hA' hC' i j hij r s hr hs hnA' hnC'
  have hbhi := normalized_upper_bound_of_skew_commutator A' C' hA' hC' i j hij r s hr hs hnA' hnC'
    (real_skew_commutator_bound A' C' hA' hC')
  rw [hK] at hblo hbhi
  exact ⟨hblo,hbhi⟩
end D5.S3.Geometry.Riemannian.ZimmermannStoyeCodimensionOneCurvature
