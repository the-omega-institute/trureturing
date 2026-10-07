/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity
   mirror-E: none(waiver:kernel-checked-exact-maximum)
   anchors: []
   utility: none
   digest: Every qutrit APPT purity maximum is the larger of the two attaining families. -/

/-
proof_shape: result: content
escape_witness: The sharp gap certificates for total dimensions 9 through 30,
  the K1-only uniform ray estimate and explicit APPT attaining matrices settle
  the exact supremum for every qutrit-qudit dimension.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose
  statement_id: sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN3PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN4PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN5PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN6PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN9PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN10PurityBound

set_option autoImplicit false
set_option maxHeartbeats 8000000
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritQuditMaximumPurity
open QutritPerturbationAttainment QutritSpectralReduction

def claim : Prop := ∀ n : ℕ, 3 ≤ n →
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = p} =
      max ((3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2) (3/(8*(n : ℝ)))) ∧
    ∃ rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      rho = diagonal (fun ij => ((if n ≤ 8 then
        (if ij.1 = 0 ∧ ij.2.val = 0 then 3 else 1) / (3*(n : ℝ)+2)
        else (if ij.1 = 0 then 2 else 1) / (4*(n : ℝ)) : ℝ) : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re =
        max ((3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2) (3/(8*(n : ℝ)))

theorem result : claim := by
  have density_bound (n : ℕ) (hn : 3 ≤ n)
      (rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
      (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
      (rho*rho).trace.re ≤ max ((3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2) (3/(8*(n : ℝ))) := by
    obtain ⟨k,rfl⟩ : ∃ k, n=3+k := ⟨n-3,by omega⟩
    by_cases hk : k ≤ 7
    · interval_cases k
      · convert QutritN3PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN4PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN5PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN6PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN7PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN8PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN9PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
      · convert QutritN10PurityBound.purity_bound rho hrho htrace happt using 1 <;> norm_num
    · obtain ⟨l,ho,hl,ht,h1,h2,hpur⟩ := spectral_reduction k rho hrho htrace happt
      rw [hpur]
      exact le_trans (UniformSpectralBound.uniform_spectral_bound k (by omega) l ho hl ht h1)
        (le_max_right _ _)
  have pure_attains (n : ℕ) (hn : 0<n) :
      ∃ rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
        rho = diagonal (fun ij => (((if ij.1 = 0 ∧ ij.2.val = 0 then 3 else 1) /
          (3*(n : ℝ)+2) : ℝ) : ℂ)) ∧
        (rho.PosSemidef ∧ rho.trace=1) ∧ APPT rho ∧
        (rho*rho).trace.re=(3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 := by
    let v : Fin 3 × Fin n → ℂ := Pi.single (0,⟨0,hn⟩) 1
    have hv : ∑ ij, star (v ij)*v ij=1 := by simp [v,Pi.single_apply]
    obtain ⟨ha,hp,ht,hpur⟩ := pure_attainment n v hv
    refine ⟨rhoPure n v,?_,⟨hp,ht⟩,ha,?_⟩
    · have hindex (ij : Fin 3 × Fin n) : ij = (0,⟨0,hn⟩) ↔ ij.1 = 0 ∧ ij.2.val = 0 := by
        constructor
        · intro h
          subst ij
          exact ⟨rfl,rfl⟩
        · rintro ⟨hi,hj⟩
          exact Prod.ext hi (Fin.ext hj)
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : i = (0,⟨0,hn⟩)
        · simp [rhoPure, v, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
            Pi.single_apply, ← hindex, hi]
          push_cast
          ring
        · simp [rhoPure, v, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
            Pi.single_apply, ← hindex, hi]
      · by_cases hi : i = (0,⟨0,hn⟩)
        · have hj : j ≠ (0,⟨0,hn⟩) := by intro h; apply hij; exact hi.trans h.symm
          simp [rhoPure, v, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
            Pi.single_apply, hij, hi, hj, eq_comm]
        · simp [rhoPure, v, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
            Pi.single_apply, hij, hi]
    · simpa only [Complex.ofReal_re] using congrArg Complex.re hpur
  have projection_trace_rank {I : Type} [Fintype I] [DecidableEq I]
      (P : Matrix I I ℂ) (hP : P*P=P) : P.trace=(P.rank : ℂ) := by
    have hlin : IsIdempotentElem P.mulVecLin := by
      rw [← Matrix.toLin'_apply']
      change Matrix.toLin' P ∘ₗ Matrix.toLin' P=Matrix.toLin' P
      rw [← Matrix.toLin'_mul, hP]
    have ht := (LinearMap.IsIdempotentElem.isProj_range _ hlin).trace
    have htrace : LinearMap.trace ℂ (I → ℂ) P.mulVecLin=P.trace := by
      rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I),
        LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rw [htrace] at ht
    exact ht
  have projector_attains (n : ℕ) (hn : 0<n) :
      ∃ rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
        rho = diagonal (fun ij => (((if ij.1 = 0 then 2 else 1) /
          (4*(n : ℝ)) : ℝ) : ℂ)) ∧
        (rho.PosSemidef ∧ rho.trace=1) ∧ APPT rho ∧
        (rho*rho).trace.re=3/(8*(n : ℝ)) := by
    let P : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
      diagonal (fun ij => if ij.1=0 then 1 else 0)
    have hH : P.IsHermitian := by
      ext i j
      by_cases hi : i.1=0 <;> by_cases hij : i=j <;>
        simp [P,diagonal,Matrix.conjTranspose_apply,hi,hij,eq_comm]
    have hP : P*P=P := by
      dsimp only [P]
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : i.1=0 <;> simp [hi]
    have htrace : P.trace=(n : ℂ) := by
      dsimp only [P]
      rw [trace_diagonal,Fintype.sum_prod_type]
      simp only [Fin.sum_univ_succ]
      simp
    have hr : P.rank=n := by
      have h := projection_trace_rank P hP
      rw [htrace] at h
      exact_mod_cast h.symm
    obtain ⟨ha,hp,ht,hpur⟩ := projector_attainment n hn P hH hP hr
    refine ⟨rhoProjector n P,?_,⟨hp,ht⟩,ha,?_⟩
    · ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : i.1 = 0
        · simp [rhoProjector, P, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.one_apply, hi]
          push_cast
          ring
        · simp [rhoProjector, P, Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.add_apply, Matrix.one_apply, hi]
      · simp [rhoProjector, P, Matrix.diagonal_apply, Matrix.smul_apply,
          Matrix.add_apply, Matrix.one_apply, hij]
    · simpa only [Complex.ofReal_re] using congrArg Complex.re hpur
  intro n hn
  have ha : ∃ rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      rho = diagonal (fun ij => ((if n ≤ 8 then
        (if ij.1 = 0 ∧ ij.2.val = 0 then 3 else 1) / (3*(n : ℝ)+2)
        else (if ij.1 = 0 then 2 else 1) / (4*(n : ℝ)) : ℝ) : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace=1) ∧ APPT rho ∧ (rho*rho).trace.re=
        max ((3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2) (3/(8*(n : ℝ))) := by
    by_cases h8 : n ≤ 8
    · have hcmp : 3/(8*(n : ℝ)) ≤ (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 := by
        interval_cases n <;> norm_num
      simpa only [if_pos h8, max_eq_left hcmp] using pure_attains n (by omega)
    · have hnR : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n from by omega)
      have hp1 : (0 : ℝ)<(3*(n : ℝ)+2)^2 := by positivity
      have hp2 : (0 : ℝ)<8*(n : ℝ) := by positivity
      have hcmp : (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 ≤ 3/(8*(n : ℝ)) := by
        apply (div_le_div_iff₀ hp1 hp2).mpr
        nlinarith [sq_nonneg ((n : ℝ)-9)]
      simpa only [if_neg h8, max_eq_right hcmp] using projector_attains n (by omega)
  obtain ⟨rho,hrho,hd,happt,hpur⟩ := ha
  have hattain : ∃ rho : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      (rho.PosSemidef ∧ rho.trace=1) ∧ APPT rho ∧ (rho*rho).trace.re=
        max ((3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2) (3/(8*(n : ℝ))) :=
    ⟨rho,hd,happt,hpur⟩
  refine ⟨?_,rho,hrho,hd,happt,hpur⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · exact ⟨_,hattain⟩
  · intro p ⟨rho,hd,hp,he⟩
    rw [← he]
    exact density_bound n hn rho hd.1 hd.2 hp
  · intro w hw
    exact ⟨_,hattain,hw⟩

#print axioms result
end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritQuditMaximumPurity
