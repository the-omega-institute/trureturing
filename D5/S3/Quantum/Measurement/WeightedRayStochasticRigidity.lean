/- GID: D5/S3/Quantum/Measurement/WeightedRayStochasticRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/WeightedRayStochasticRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stochastic unitary transport permutes pure rays and conserves grouped weights. -/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Information.ActualQubitChordObstruction
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-! Exact stochastic rigidity of the original weighted qubit rays. -/

noncomputable section
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity

private theorem projection_psd {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef := by
  simpa only [hP.eq, hPP] using Matrix.posSemidef_conjTranspose_mul_self P

private theorem pure_projection_eq {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hPt : trace P = 1) (hQt : trace Q = 1)
    (h : trace (P * (1 - Q)) = 0) : P = Q := by
  have hPQ : trace (P * Q) = 1 := by
    rw [mul_sub, mul_one, trace_sub, hPt] at h
    linear_combination -h
  have hQP : trace (Q * P) = 1 := (trace_mul_comm Q P).trans hPQ
  apply sub_eq_zero.mp
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rw [(hP.sub hQ).eq, sub_mul, mul_sub, mul_sub, trace_sub,
    trace_sub, trace_sub, hPP, hQQ, hPt, hQt, hPQ, hQP]
  ring

private theorem conjugate_projection {d : ℕ} (U : unitaryGroup (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (ht : trace P = 1) :
    (star (U : Matrix (Fin d) (Fin d) ℂ) * P * (U : Matrix (Fin d) (Fin d) ℂ)).IsHermitian ∧
    (star (U : Matrix (Fin d) (Fin d) ℂ) * P * (U : Matrix (Fin d) (Fin d) ℂ)) *
      (star (U : Matrix (Fin d) (Fin d) ℂ) * P * (U : Matrix (Fin d) (Fin d) ℂ)) =
      star (U : Matrix (Fin d) (Fin d) ℂ) * P * (U : Matrix (Fin d) (Fin d) ℂ) ∧
    trace (star (U : Matrix (Fin d) (Fin d) ℂ) * P * (U : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul _ hP, ?_, ?_⟩
  · calc
      _ = star (U : Matrix (Fin d) (Fin d) ℂ) * P *
          ((U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ)) * P * (U : Matrix (Fin d) (Fin d) ℂ) := by noncomm_ring
      _ = _ := by rw [Unitary.coe_mul_star_self]; simp only [mul_one, mul_assoc, hPP]
  · rw [trace_mul_cycle, Unitary.coe_mul_star_self, one_mul, ht]

/-- A single unitary and a single column-stochastic matrix transporting a finite
weighted family of normalized pure projections induce one permutation of the
distinct rays. The total weight of each repeated-ray group is conserved. -/
private theorem weighted_ray_transport {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {d : ℕ}
    (g : ι → κ) (hg : Function.Surjective g)
    (P : κ → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).IsHermitian) (hPP : ∀ k, P k * P k = P k)
    (ht : ∀ k, trace (P k) = 1) (hPinj : Function.Injective P)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (U : unitaryGroup (Fin d) ℂ) (T : Matrix ι ι ℝ)
    (hT : T ∈ colStochastic ℝ ι)
    (hE : ∀ i, star (U : Matrix (Fin d) (Fin d) ℂ) * (w i • P (g i)) * (U : Matrix (Fin d) (Fin d) ℂ) =
      ∑ j, T i j • (w j • P (g j))) :
    ∃ π : Equiv.Perm κ,
      (∀ k, star (U : Matrix (Fin d) (Fin d) ℂ) * P k * (U : Matrix (Fin d) (Fin d) ℂ) = P (π k)) ∧
      (∀ i j, T i j ≠ 0 → g j = π (g i)) ∧
      (∀ k, (∑ i with g i = k, w i) = ∑ j with g j = π k, w j) := by
  classical
  let Q (k : κ) := star (U : Matrix (Fin d) (Fin d) ℂ) * P k * (U : Matrix (Fin d) (Fin d) ℂ)
  have hQ (k : κ) := conjugate_projection U (P k) (hP k) (hPP k) (ht k)
  have hm (i : ι) : w i = ∑ j, T i j * w j := by
    have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (trace A).re) (hE i)
    simpa only [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_sum, map_sum, hQ (g i) |>.2.2, ht, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.one_re, mul_one] using he
  have hs (i j : ι) (hij : T i j ≠ 0) : P (g j) = Q (g i) := by
    have hzero : ∑ j, (T i j * w j) * (trace (P (g j) * (1 - Q (g i)))).re = 0 := by
      have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ =>
        (trace (A * (1 - Q (g i)))).re) (hE i)
      have hqq : Q (g i) * (1 - Q (g i)) = 0 := by
        rw [mul_sub, mul_one, hQ (g i) |>.2.1, sub_self]
      have hel : star (U : Matrix (Fin d) (Fin d) ℂ) * (w i • P (g i)) * (U : Matrix (Fin d) (Fin d) ℂ) =
          w i • Q (g i) := by simp [Q]
      rw [hel, smul_mul, hqq, smul_zero, trace_zero, Complex.zero_re] at he
      simpa only [sum_mul, trace_sum, map_sum, smul_mul, trace_smul,
        smul_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using he.symm
    have hn (j : ι) : 0 ≤ (trace (P (g j) * (1 - Q (g i)))).re :=
      RHLinalg.trace_mul_nonneg_of_posSemidef
        (projection_psd _ (hP _) (hPP _))
        (D5.S3.Quantum.Measurement.AntidistinguishabilityGram.hermitian_projection_complement_psd
          _ (hQ _).1 (hQ _).2.1)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (mul_nonneg (hT.1 _ _) (hw j).le) (hn j))).mp hzero j (mem_univ j)
    have hzre : (trace (P (g j) * (1 - Q (g i)))).re = 0 :=
      (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hij (hw j).ne')
    have hzcomplex : trace (P (g j) * (1 - Q (g i))) = 0 := by
      have he : star (trace (P (g j) * (1 - Q (g i)))) =
          trace (P (g j) * (1 - Q (g i))) := by
        rw [← trace_conjTranspose, conjTranspose_mul, (hP _).eq,
          (Matrix.isHermitian_one.sub (hQ _).1).eq, trace_mul_comm]
      have hi := congrArg Complex.im he
      simp only [Complex.star_def, Complex.conj_im] at hi
      exact Complex.ext hzre (by simp only [Complex.zero_im]; linarith)
    exact pure_projection_eq _ _ (hP _) (hQ _).1 (hPP _) (hQ _).2.1 (ht _) (hQ _).2.2 hzcomplex
  have hex (k : κ) : ∃ l, Q k = P l := by
    obtain ⟨i, rfl⟩ := hg k
    have hj : ∃ j, T i j ≠ 0 := by
      by_contra h
      push_neg at h
      have hz : w i = 0 := by simpa [h] using hm i
      exact (hw i).ne' hz
    obtain ⟨j, hj⟩ := hj
    exact ⟨g j, (hs i j hj).symm⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro k l hkl
    have he : Q k = Q l := (hf k).trans ((congrArg P hkl).trans (hf l).symm)
    apply hPinj
    have he' := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) * A * star (U : Matrix (Fin d) (Fin d) ℂ)) he
    simpa only [Q, ← mul_assoc, Unitary.coe_mul_star_self, one_mul,
      mul_assoc, Unitary.coe_mul_star_self, mul_one] using he'
  let π : Equiv.Perm κ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hsupport (i j : ι) (hij : T i j ≠ 0) : g j = π (g i) :=
    hPinj ((hs i j hij).trans (hf (g i)))
  refine ⟨π, hf, hsupport, ?_⟩
  intro k
  calc
    (∑ i with g i = k, w i) = ∑ i with g i = k, ∑ j, T i j * w j := by
      apply sum_congr rfl; intro i _; exact hm i
    _ = ∑ j, (∑ i with g i = k, T i j) * w j := by
      rw [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_mul]
    _ = ∑ j with g j = π k, w j := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      by_cases hj : g j = π k
      · rw [if_pos hj]
        have he : (∑ i with g i = k, T i j) = ∑ i, T i j := by
          symm
          apply sum_subset (filter_subset _ _) 
          intro i _ hi
          have hgi : g i ≠ k := by simpa only [mem_filter, mem_univ, true_and] using hi
          by_contra hn
          exact hgi (π.injective ((hsupport i j hn).symm.trans hj))
        rw [he, sum_col_of_mem_colStochastic hT, one_mul]
      · rw [if_neg hj]
        have he : (∑ i with g i = k, T i j) = 0 := by
          apply sum_eq_zero
          intro i hi
          have hi' : g i = k := (mem_filter.mp hi).2
          by_contra hn
          exact hj ((hsupport i j hn).trans (congrArg π hi'))
        rw [he, zero_mul]

open D5.S3.Quantum.Measurement.FourQubitParentConstruction
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

/-- The positive gain of the original five-effect encoding. -/
def gain : ℝ := (1 + 2 * Real.sqrt 3 + Real.sqrt 11)⁻¹

/-- The four distinct Bloch directions, in the order A, B, C, D. -/
def direction : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![WithLp.toLp 2 ![-1 / Real.sqrt 3, -1 / Real.sqrt 3, -1 / Real.sqrt 3],
    WithLp.toLp 2 ![3 / Real.sqrt 11, 1 / Real.sqrt 11, 1 / Real.sqrt 11],
    WithLp.toLp 2 ![0, 0, 1],
    WithLp.toLp 2 ![1 / Real.sqrt 11, 3 / Real.sqrt 11, 1 / Real.sqrt 11]]

/-- The original order is (0,2,3,5,25); the first and last outcomes share A. -/
def group : Fin 5 → Fin 4 := ![0, 1, 2, 3, 0]

def weight : Fin 5 → ℝ :=
  ![3 * gain * Real.sqrt 3, gain * Real.sqrt 11, 2 * gain,
    gain * Real.sqrt 11, gain * Real.sqrt 3]

def ray (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := blochMatrix 1 (direction k)

/-- The literal source effects, using X, Y, Z with Y's upper-right entry -i. -/
def effect : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(3 * gain / 2) • scalarB (Real.sqrt 3) (WithLp.toLp 2 ![-1, -1, -1]),
    (gain / 2) • scalarB (Real.sqrt 11) (WithLp.toLp 2 ![3, 1, 1]),
    gain • scalarB 1 (WithLp.toLp 2 ![0, 0, 1]),
    (gain / 2) • scalarB (Real.sqrt 11) (WithLp.toLp 2 ![1, 3, 1]),
    (gain / 2) • scalarB (Real.sqrt 3) (WithLp.toLp 2 ![-1, -1, -1])]

/-- Real Born probabilities in the fixed original order. -/
def probability (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Fin 5 → ℝ :=
  fun s => (trace (ρ * effect s)).re

/-- One matrix acts on every qubit density matrix. -/
def Autonomous (U : unitaryGroup (Fin 2) ℂ) (T : Matrix (Fin 5) (Fin 5) ℝ) : Prop :=
  T ∈ colStochastic ℝ (Fin 5) ∧
    ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef → trace ρ = 1 →
      T.mulVec (probability ρ) = probability (U * ρ * star (U : Matrix _ _ ℂ))

/-- All kernels, including t=0 and t=1/3. -/
def kernel (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1-t, 0, 0, 0, 3*t;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     t, 0, 0, 0, 1-3*t]

private theorem gain_pos : 0 < gain := by unfold gain; positivity

private theorem ray_facts (k : Fin 4) :
    (ray k).IsHermitian ∧ ray k * ray k = ray k ∧ trace (ray k) = 1 := by
  have hn : ‖direction k‖ = 1 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
    have h3n : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have h11n : Real.sqrt 11 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hs : ‖direction k‖ ^ 2 = 1 := by
      rw [norm_sq_coords]
      fin_cases k <;> simp [direction] <;> field_simp <;> nlinarith
    nlinarith [norm_nonneg (direction k)]
  refine ⟨?_, D5.S3.Quantum.Information.ActualQubitChordObstruction.pure _ hn,
    blochMatrix_trace 1 _⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ray, blochMatrix, Matrix.conjTranspose_apply]

private theorem ray_injective : Function.Injective ray := by
  intro k l h
  have hd : direction k = direction l := by
    simpa [ray, bloch_blochMatrix] using congrArg bloch h
  have h0 := congrArg (fun r : EuclideanSpace ℝ (Fin 3) => r 0) hd
  have h1 := congrArg (fun r : EuclideanSpace ℝ (Fin 3) => r 1) hd
  have h2 := congrArg (fun r : EuclideanSpace ℝ (Fin 3) => r 2) hd
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h11p : 0 < Real.sqrt 11 := Real.sqrt_pos.mpr (by norm_num)
  have hp : 0 < 1 / Real.sqrt 11 := by positivity
  have hp3 : 0 < 1 / Real.sqrt 3 := by positivity
  fin_cases k <;> fin_cases l <;> norm_num [direction] at h0 h1 h2 ⊢ <;>
    nlinarith

private theorem effect_factor (s : Fin 5) : effect s = weight s • ray (group s) := by
  have h3n : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h11n : Real.sqrt 11 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [effect, weight, ray, group, direction, blochMatrix, scalarB, B_formula,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

private theorem effect_hermitian (s : Fin 5) : (effect s).IsHermitian := by
  rw [effect_factor]
  exact (ray_facts _).1.smul (isSelfAdjoint_iff.mpr (star_trivial _))

private theorem density_trace_ext {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → trace ρ = 1 →
      (trace (ρ * A)).re = (trace (ρ * B)).re) : A = B := by
  let L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ := {
    toFun := fun X => (trace (X * (A-B))).re
    map_add' := by intro X Y; simp [add_mul, trace_add]
    map_smul' := by intro c X; simp [smul_mul, trace_smul] }
  have hspan := (D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.all_density_tomographically_complete d).2
  have hle : D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d ≤ L.ker := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro ρ hρ
    change (trace (ρ * (A-B))).re = 0
    simpa only [mul_sub, trace_sub, Complex.sub_re, sub_eq_zero] using h ρ hρ.1 hρ.2
  have hz : (trace ((A-B) * (A-B))).re = 0 := hle (hA.sub hB)
  have hp := Matrix.posSemidef_conjTranspose_mul_self (A-B)
  have hi : (trace ((A-B)ᴴ * (A-B))).im = 0 :=
    (Complex.nonneg_iff.mp hp.trace_nonneg).2
  have he : trace ((A-B)ᴴ * (A-B)) = 0 := by
    apply Complex.ext
    · simpa only [(hA.sub hB).eq] using hz
    · exact hi
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp he)

private theorem operator_transport (U : unitaryGroup (Fin 2) ℂ)
    (T : Matrix (Fin 5) (Fin 5) ℝ) (h : Autonomous U T) (s : Fin 5) :
    star (U : Matrix (Fin 2) (Fin 2) ℂ) * effect s * (U : Matrix (Fin 2) (Fin 2) ℂ) = ∑ j, T s j • effect j := by
  apply density_trace_ext _ _
    (Matrix.isHermitian_conjTranspose_mul_mul _ (effect_hermitian s))
    ((isSelfAdjoint_sum Finset.univ (fun j _ =>
      ((effect_hermitian j).smul (isSelfAdjoint_iff.mpr (star_trivial _))).isSelfAdjoint)).isHermitian)
  intro ρ hρ ht
  have he := congrFun (h.2 ρ hρ ht) s
  change (∑ j, T s j * (trace (ρ * effect j)).re) =
    (trace (((U : Matrix (Fin 2) (Fin 2) ℂ) * ρ * star (U : Matrix (Fin 2) (Fin 2) ℂ)) * effect s)).re at he
  calc
    _ = (trace (((U : Matrix (Fin 2) (Fin 2) ℂ) * ρ * star (U : Matrix (Fin 2) (Fin 2) ℂ)) * effect s)).re := by
      congr 1
      simpa only [mul_assoc] using trace_mul_comm (ρ * star (U : Matrix _ _ ℂ) * effect s) (U : Matrix _ _ ℂ)
    _ = _ := by simpa [mul_sum, mul_smul, trace_sum, trace_smul] using he.symm

private theorem group_weight (k : Fin 4) :
    (∑ i with group i = k, weight i) =
      gain * (![4 * Real.sqrt 3, Real.sqrt 11, 2, Real.sqrt 11] : Fin 4 → ℝ) k := by
  fin_cases k <;> norm_num [group, weight, Fin.sum_univ_succ] <;> ring

private theorem scalar_of_fixed_rays (U : unitaryGroup (Fin 2) ℂ)
    (hA : star (U : Matrix (Fin 2) (Fin 2) ℂ) * ray 0 * (U : Matrix (Fin 2) (Fin 2) ℂ) = ray 0)
    (hC : star (U : Matrix (Fin 2) (Fin 2) ℂ) * ray 2 * (U : Matrix (Fin 2) (Fin 2) ℂ) = ray 2) :
    ∃ γ : ℝ, (U : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp ((γ : ℂ) * Complex.I) • 1 := by
  have comm (k : Fin 4) (hk : star (U : Matrix (Fin 2) (Fin 2) ℂ) * ray k * (U : Matrix (Fin 2) (Fin 2) ℂ) = ray k) :
      ray k * (U : Matrix (Fin 2) (Fin 2) ℂ) = (U : Matrix (Fin 2) (Fin 2) ℂ) * ray k := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (U : Matrix _ _ ℂ) * M) hk
    simpa only [← mul_assoc, Unitary.coe_mul_star_self, one_mul] using he
  have h01 : (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    have he := congrFun₂ (comm 2 hC) 0 1
    simpa [ray, direction, blochMatrix, Matrix.mul_apply, Fin.sum_univ_two] using he
  have h10 : (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    have he := congrFun₂ (comm 2 hC) 1 0
    simpa [ray, direction, blochMatrix, Matrix.mul_apply, Fin.sum_univ_two] using he.symm
  have ha : ray 0 0 1 ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    norm_num [ray, direction, blochMatrix] at he
    positivity
  have hdiag : (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = U 0 0 := by
    apply mul_left_cancel₀ ha
    have he := congrFun₂ (comm 0 hA) 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h01, mul_comm] using he
  have hscalar : (U : Matrix (Fin 2) (Fin 2) ℂ) = (U 0 0) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, hdiag]
  have hu := congrFun₂ (Unitary.coe_star_mul_self U) 0 0
  rw [hscalar] at hu
  have hn : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
    have he := congrArg norm hu
    simp only [star_smul, star_one, smul_mul, mul_smul, one_mul,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, norm_mul,
      norm_star, norm_one] at he
    nlinarith [norm_nonneg ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)]
  obtain ⟨γ, hγ⟩ := (Complex.norm_eq_one_iff _).mp hn
  exact ⟨γ, hscalar.trans (by rw [hγ])⟩

private theorem autonomous_constraints (U : unitaryGroup (Fin 2) ℂ)
    (T : Matrix (Fin 5) (Fin 5) ℝ) (h : Autonomous U T) :
    (∃ γ : ℝ, (U : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp ((γ : ℂ) * Complex.I) • 1) ∧
    (∀ i j, group j ≠ group i → T i j = 0) ∧
    (∀ i, weight i = ∑ j, T i j * weight j) := by
  have hw (i : Fin 5) : 0 < weight i := by
    fin_cases i <;> simp only [weight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;>
      positivity [gain_pos]
  have hg : Function.Surjective group := by
    intro k
    fin_cases k
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hE (i : Fin 5) :
      star (U : Matrix (Fin 2) (Fin 2) ℂ) * (weight i • ray (group i)) * (U : Matrix (Fin 2) (Fin 2) ℂ) =
        ∑ j, T i j • (weight j • ray (group j)) := by
    simpa only [← effect_factor] using operator_transport U T h i
  obtain ⟨π, hπ, hs, hW⟩ := weighted_ray_transport group hg ray
    (fun k => (ray_facts k).1) (fun k => (ray_facts k).2.1)
    (fun k => (ray_facts k).2.2) ray_injective weight hw U T h.1 hE
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h11p : 0 < Real.sqrt 11 := Real.sqrt_pos.mpr (by norm_num)
  have hord : 2 < Real.sqrt 11 ∧ Real.sqrt 11 < 4 * Real.sqrt 3 := by
    constructor <;> nlinarith
  have hweight (k : Fin 4) :
      (![4 * Real.sqrt 3, Real.sqrt 11, 2, Real.sqrt 11] : Fin 4 → ℝ) k =
      (![4 * Real.sqrt 3, Real.sqrt 11, 2, Real.sqrt 11] : Fin 4 → ℝ) (π k) := by
    have he := hW k
    rw [group_weight, group_weight] at he
    exact mul_left_cancel₀ gain_pos.ne' he
  have hp0 : π 0 = 0 := by
    have he := hweight 0
    generalize hq : π 0 = q at he ⊢
    fin_cases q <;> norm_num at he ⊢ <;> nlinarith [hord.1, hord.2]
  have hp2 : π 2 = 2 := by
    have he := hweight 2
    generalize hq : π 2 = q at he ⊢
    fin_cases q <;> norm_num at he ⊢ <;> nlinarith [hord.1, hord.2]
  have hphase := scalar_of_fixed_rays U (by simpa [hp0] using hπ 0)
    (by simpa [hp2] using hπ 2)
  obtain ⟨γ, hγ⟩ := hphase
  have hfix (k : Fin 4) : star (U : Matrix (Fin 2) (Fin 2) ℂ) * ray k * (U : Matrix (Fin 2) (Fin 2) ℂ) = ray k := by
    have hc : ray k * (U : Matrix (Fin 2) (Fin 2) ℂ) = (U : Matrix (Fin 2) (Fin 2) ℂ) * ray k := by rw [hγ]; simp [mul_smul, smul_mul]
    rw [mul_assoc, hc, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hpall (k : Fin 4) : π k = k := ray_injective ((hπ k).symm.trans (hfix k))
  refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
  · intro i j hne
    by_contra hn
    exact hne (by simpa [hpall] using hs i j hn)
  · intro i
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (trace M).re) (hE i)
    rw [← smul_mul, ← mul_smul, hfix, trace_smul, (ray_facts _).2.2] at he
    simpa [trace_sum, trace_smul, (ray_facts _).2.2, smul_smul] using he

private theorem kernel_of_constraints (T : Matrix (Fin 5) (Fin 5) ℝ)
    (hT : T ∈ colStochastic ℝ (Fin 5))
    (hs : ∀ i j, group j ≠ group i → T i j = 0)
    (hm : ∀ i, weight i = ∑ j, T i j * weight j) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/3 ∧ T = kernel t := by
  have hz (i j : Fin 5) (hij : group j ≠ group i) : T i j = 0 := hs i j hij
  have c0 := sum_col_of_mem_colStochastic hT 0
  have c1 := sum_col_of_mem_colStochastic hT 1
  have c2 := sum_col_of_mem_colStochastic hT 2
  have c3 := sum_col_of_mem_colStochastic hT 3
  have c4 := sum_col_of_mem_colStochastic hT 4
  have r0 := hm 0
  have h01 := hz 0 1 (by decide)
  have h02 := hz 0 2 (by decide)
  have h03 := hz 0 3 (by decide)
  have h10 := hz 1 0 (by decide)
  have h12 := hz 1 2 (by decide)
  have h13 := hz 1 3 (by decide)
  have h14 := hz 1 4 (by decide)
  have h20 := hz 2 0 (by decide)
  have h21 := hz 2 1 (by decide)
  have h23 := hz 2 3 (by decide)
  have h24 := hz 2 4 (by decide)
  have h30 := hz 3 0 (by decide)
  have h31 := hz 3 1 (by decide)
  have h32 := hz 3 2 (by decide)
  have h34 := hz 3 4 (by decide)
  have h41 := hz 4 1 (by decide)
  have h42 := hz 4 2 (by decide)
  have h43 := hz 4 3 (by decide)
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero,
    h10, h20, h30, h01, h21, h31, h41, h02, h12, h32, h42,
    h03, h13, h23, h43, h14, h24, h34, add_zero, zero_add] at c0 c1 c2 c3 c4
  have h00 : T 0 0 = 1 - T 4 0 := by linarith
  have h44 : T 4 4 = 1 - T 0 4 := by linarith
  have h04 : T 0 4 = 3 * T 4 0 := by
    simp [weight, Fin.sum_univ_succ, h01, h02, h03, h00] at r0
    have hne : gain * Real.sqrt 3 ≠ 0 := mul_ne_zero gain_pos.ne'
      (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    have he : (T 0 4 - 3 * T 4 0) * (gain * Real.sqrt 3) = 0 := by nlinarith [r0]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hne)
  refine ⟨T 4 0, hT.1 4 0, ?_, ?_⟩
  · have hp := hT.1 4 4
    rw [h44, h04] at hp
    linarith
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kernel, h00, h04, h44, h01, h02, h03, h10, h12, h13, h14,
        h20, h21, h23, h24, h30, h31, h32, h34, h41, h42, h43, c1, c2, c3]

private theorem autonomous_of_kernel (U : unitaryGroup (Fin 2) ℂ)
    (hphase : ∃ γ : ℝ, (U : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp ((γ : ℂ) * Complex.I) • 1)
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1/3) : Autonomous U (kernel t) := by
  constructor
  · apply mem_colStochastic_iff_sum.mpr
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [kernel] <;> linarith
    · intro j
      fin_cases j <;> norm_num [kernel, Fin.sum_univ_succ] <;> ring
  · intro ρ _ _
    obtain ⟨γ, hγ⟩ := hphase
    have hc : (U : Matrix (Fin 2) (Fin 2) ℂ) * ρ = ρ * (U : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hγ]; simp [smul_mul, mul_smul]
    have hρ : (U : Matrix (Fin 2) (Fin 2) ℂ) * ρ * star (U : Matrix (Fin 2) (Fin 2) ℂ) = ρ := by
      rw [hc, mul_assoc, Unitary.coe_mul_star_self, mul_one]
    rw [hρ]
    have hr : probability ρ 0 = 3 * probability ρ 4 := by
      simp [probability, effect, mul_smul, trace_smul]
      ring
    ext i
    fin_cases i <;>
      simp [kernel, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      nlinarith [hr]

/-- For the original five effects in the order (0,2,3,5,25), one nonnegative
column-stochastic matrix transports Born probabilities for every qubit density
matrix precisely when the unitary is a scalar phase and the matrix is the
specified one-parameter kernel, with the complete closed parameter interval. -/
theorem original_five_effect_classification
    (U : unitaryGroup (Fin 2) ℂ) (T : Matrix (Fin 5) (Fin 5) ℝ) :
    Autonomous U T ↔
      (∃ γ : ℝ, (U : Matrix (Fin 2) (Fin 2) ℂ) = Complex.exp ((γ : ℂ) * Complex.I) • 1) ∧
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/3 ∧ T = kernel t := by
  constructor
  · intro h
    obtain ⟨hphase, hs, hm⟩ := autonomous_constraints U T h
    exact ⟨hphase, kernel_of_constraints T h.1 hs hm⟩
  · rintro ⟨hphase, t, ht, ht', rfl⟩
    exact autonomous_of_kernel U hphase t ht ht'

end D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity
