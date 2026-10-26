/- GID: D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim; result=D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result; claim=D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim
   digest: Entangled Werner states need not be detected by any pair of complex testers. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments

namespace D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness

noncomputable section

/-- A complex tester has trace-norm to Euclidean operator norm exactly one. -/
def IsTester {d n : ℕ}
    (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ x, ‖e x‖ ≤ traceNorm x) ∧ ∃ x, x ≠ 0 ∧ ‖e x‖ = traceNorm x

/-- The coefficient matrix of the tensor product of two complex linear maps. -/
def testerImage {d₁ d₂ n₁ n₂ : ℕ}
    (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    Matrix (Fin n₁) (Fin n₂) ℂ :=
  fun p q => ∑ i, ∑ j, ∑ k, ∑ l,
    ρ (i, j) (k, l) * e₁ (Matrix.single i k 1) p * e₂ (Matrix.single j l 1) q

/-- The projective tensor norm, as an infimum over all finite decompositions. -/
def projNorm {n₁ n₂ : ℕ} (m : Matrix (Fin n₁) (Fin n₂) ℂ) : ℝ :=
  sInf {r | ∃ (k : ℕ) (a : Fin k → EuclideanSpace ℂ (Fin n₁))
    (b : Fin k → EuclideanSpace ℂ (Fin n₂)),
    m = ∑ t, Matrix.of (fun p q => a t p * b t q) ∧ r = ∑ t, ‖a t‖ * ‖b t‖}

/-- Separable density matrices form the convex hull of all product density matrices. -/
def Separable {d₁ d₂ : ℕ}
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) : Prop :=
  ρ ∈ convexHull ℝ {σ | ∃ (ρ₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ρ₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
    ρ₁.PosSemidef ∧ ρ₁.trace = 1 ∧ ρ₂.PosSemidef ∧ ρ₂.trace = 1 ∧
    σ = Matrix.kroneckerMap (· * ·) ρ₁ ρ₂}

/-- Werner's symmetric and antisymmetric mixture, with the flip on the two factors. -/
def werner (d : ℕ) (μ : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (μ / ((d : ℝ) * (d + 1))) •
      (1 + Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))) +
    ((1 - μ) / ((d : ℝ) * (d - 1))) •
      (1 - Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)))

/-- The bipartite completeness question for complex testers without index permutations. -/
def claim : Prop :=
  ∀ (d₁ d₂ : ℕ) (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ),
    ρ.PosSemidef → ρ.trace = 1 → ¬ Separable ρ →
    ∃ (n₁ n₂ : ℕ)
      (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
      (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂)),
      IsTester e₁ ∧ IsTester e₂ ∧ 1 < projNorm (testerImage e₁ e₂ ρ)

set_option maxHeartbeats 2000000 in
private theorem witness_pos : (werner 3 (1 / 3)).PosSemidef := by
  let f := Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 3) (Fin 3))
  have h : werner 3 (1 / 3) =
      (1 / 72 : ℝ) • ((1 + f)ᴴ * (1 + f)) +
      (1 / 18 : ℝ) • ((1 - f)ᴴ * (1 - f)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [werner, f, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_succ, Matrix.conjTranspose_apply, replicaSwap_apply,
        Matrix.one_apply, Prod.mk.injEq]
  rw [h]
  exact ((Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num : (0 : ℝ) ≤ 1 / 72)).add
    ((Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num : (0 : ℝ) ≤ 1 / 18))

private theorem witness_trace : (werner 3 (1 / 3)).trace = 1 := by
  norm_num [werner, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Matrix.one_apply, replicaSwap_apply]

private theorem flip_product_trace {d : ℕ} (a b : Matrix (Fin d) (Fin d) ℂ) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
      Matrix.kroneckerMap (· * ·) a b).trace = (a * b).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, replicaSwap_apply, Prod.swap_prod_mk, Prod.mk.injEq,
    Matrix.kroneckerMap_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i j : Fin d => a j i * b i j)

private def flipReadout (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℝ] ℝ where
  toFun ρ := (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) * ρ).trace.re
  map_add' a b := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c a := by simp [Matrix.mul_smul, Matrix.trace_smul]

private theorem separable_flip_nonneg {d : ℕ}
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (h : Separable ρ) :
    0 ≤ flipReadout d ρ := by
  apply convexHull_min (t := (flipReadout d) ⁻¹' Set.Ici 0) ?_
    ((convex_Ici (0 : ℝ)).linear_preimage (flipReadout d)) h
  rintro σ ⟨a, b, ha, _, hb, _, rfl⟩
  change 0 ≤ (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d)) *
    Matrix.kroneckerMap (· * ·) a b).trace.re
  rw [flip_product_trace]
  exact RHLinalg.trace_mul_nonneg_of_posSemidef ha hb

private theorem witness_entangled : ¬ Separable (werner 3 (1 / 3)) := by
  intro h
  have hn := separable_flip_nonneg _ h
  norm_num [flipReadout, werner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply,
    replicaSwap_apply, Prod.mk.injEq] at hn

private abbrev EnsembleIndex := Fin 3 ⊕ (Fin 3 → Fin 4)

private def weight : EnsembleIndex → ℝ :=
  Sum.elim (fun _ => 1 / 12) (fun _ => 3 / 256)

private def projector : EnsembleIndex → Matrix (Fin 3) (Fin 3) ℂ :=
  Sum.elim (fun a => Matrix.single a a 1)
    (fun z => (1 / 3 : ℝ) • Matrix.vecMulVec (fun i => phase (z i))
      (star (fun i => phase (z i))))

private def average : Matrix (Fin 3) (Fin 3) ℂ := (1 / 3 : ℝ) • 1

private def centered (t : EnsembleIndex) : Matrix (Fin 3) (Fin 3) ℂ :=
  projector t - average

private theorem weight_nonneg (t : EnsembleIndex) : 0 ≤ weight t := by
  cases t <;> norm_num [weight]

private theorem weight_sum : ∑ t, weight t = 1 := by
  norm_num [weight, Fintype.sum_sum_type]

private theorem projector_density (t : EnsembleIndex) :
    (projector t).PosSemidef ∧ (projector t).trace = 1 := by
  classical
  cases t with
  | inl a =>
    constructor
    · have heq : projector (Sum.inl a) =
          Matrix.vecMulVec (Pi.single a 1) (star (Pi.single a 1)) := by
        ext i j
        by_cases hi : i = a <;> by_cases hj : j = a <;>
          simp [projector, Matrix.single_apply, Matrix.vecMulVec_apply,
            Pi.single_apply, hi, hj, eq_comm] <;> aesop
      rw [heq]
      exact Matrix.posSemidef_vecMulVec_self_star _
    · simp [projector, Matrix.trace_single_eq_same]
  | inr z =>
    constructor
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)
    · have hu (s : Fin 4) : phase s * (starRingEnd ℂ) (phase s) = 1 := by
        fin_cases s <;> norm_num [phase]
      simp [projector, Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
        Pi.star_apply, hu, Fin.sum_univ_succ]

private theorem ensemble_second_entry (i j k l : Fin 3) :
    (∑ t, (weight t : ℂ) * projector t i k * projector t j l) =
      (1 / 12 : ℂ) * ((if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) := by
  classical
  rw [Fintype.sum_sum_type]
  have hp : (∑ z : Fin 3 → Fin 4,
      (weight (Sum.inr z) : ℂ) * projector (Sum.inr z) i k * projector (Sum.inr z) j l) =
      (1 / 768 : ℂ) * ∑ z : Fin 3 → Fin 4,
        star (phase (z k)) * phase (z i) * star (phase (z l)) * phase (z j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp only [weight, projector, Sum.elim_inr, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  rw [hp]
  have hm := moment_four k i l j
  simp only [starRingEnd_apply] at hm
  rw [hm]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [weight, projector, Fin.sum_univ_succ, Matrix.single_apply]

private theorem ensemble_first : ∑ t, weight t • projector t = average := by
  classical
  have he (i k : Fin 3) : (∑ t, (weight t : ℂ) * projector t i k) = average i k := by
    calc
      _ = ∑ t, ∑ j : Fin 3,
          (weight t : ℂ) * projector t i k * projector t j j := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.mul_sum]
        have ht := (projector_density t).2
        change ∑ j, projector t j j = 1 at ht
        rw [ht, mul_one]
      _ = ∑ j : Fin 3, ∑ t,
          (weight t : ℂ) * projector t i k * projector t j j := Finset.sum_comm
      _ = average i k := by
        simp_rw [ensemble_second_entry]
        fin_cases i <;> fin_cases k <;>
          norm_num [average, Fin.sum_univ_succ, Matrix.one_apply]
  ext i k
  simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] using he i k

set_option maxRecDepth 4096 in
private theorem witness_decomposition :
    werner 3 (1 / 3) = Matrix.kroneckerMap (· * ·) average average -
      ∑ t, weight t • Matrix.kroneckerMap (· * ·) (centered t) (centered t) := by
  classical
  have hfirst (i k : Fin 3) :
      (∑ t, (weight t : ℂ) * projector t i k) = average i k := by
    have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℂ => m i k) ensemble_first
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] using h
  have hmass : ∑ t, (weight t : ℂ) = 1 := by exact_mod_cast weight_sum
  ext ⟨i, j⟩ ⟨k, l⟩
  change werner 3 (1 / 3) (i, j) (k, l) = average i k * average j l -
    ∑ t, (weight t : ℂ) * ((projector t i k - average i k) *
      (projector t j l - average j l))
  have he (t : EnsembleIndex) :
      (weight t : ℂ) * ((projector t i k - average i k) *
        (projector t j l - average j l)) =
      (weight t : ℂ) * projector t i k * projector t j l -
      (weight t : ℂ) * projector t i k * average j l -
      (weight t : ℂ) * projector t j l * average i k +
      (weight t : ℂ) * average i k * average j l := by
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hfirst, hmass, one_mul, ensemble_second_entry]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [werner, average, replicaSwap_apply, Matrix.one_apply, Prod.mk.injEq]

private theorem tester_second_moment {n : ℕ}
    (e : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (h : ∀ x, ‖e x‖ ≤ traceNorm x) :
    ‖e average‖ ^ 2 + ∑ t, weight t * ‖e (centered t)‖ ^ 2 ≤ 1 := by
  classical
  have hm : ∑ t, weight t • e (projector t) = e average := by
    rw [← ensemble_first]
    simp only [map_sum, LinearMap.map_smul_of_tower]
  have hx : (∑ t, weight t * inner ℝ (e (projector t)) (e average)) =
      ‖e average‖ ^ 2 := by
    rw [← hm]
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, real_inner_smul_left]
  have hv : ‖e average‖ ^ 2 + ∑ t, weight t * ‖e (centered t)‖ ^ 2 =
      ∑ t, weight t * ‖e (projector t)‖ ^ 2 := by
    have hp (t : EnsembleIndex) :
        weight t * ‖e (centered t)‖ ^ 2 =
          weight t * ‖e (projector t)‖ ^ 2 -
          2 * (weight t * inner ℝ (e (projector t)) (e average)) +
          weight t * ‖e average‖ ^ 2 := by
      rw [centered, map_sub, norm_sub_sq_real]
      ring
    simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hx, weight_sum]
    ring
  rw [hv]
  calc
    _ ≤ ∑ t, weight t * 1 := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg t)
      have ht : traceNorm (projector t) = 1 := by
        have ht := traceNorm_of_posSemidef (projector_density t).1
        rw [(projector_density t).2] at ht
        exact Complex.ofReal_eq_one.mp ht
      have hc := h (projector t)
      rw [ht] at hc
      nlinarith [norm_nonneg (e (projector t))]
    _ = 1 := by simpa using weight_sum

set_option maxHeartbeats 2000000 in
private theorem tester_image_decomposition {d₁ d₂ n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]
    (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (a : ι → Matrix (Fin d₁) (Fin d₁) ℂ) (b : ι → Matrix (Fin d₂) (Fin d₂) ℂ) :
    testerImage e₁ e₂ (∑ t, Matrix.kroneckerMap (· * ·) (a t) (b t)) =
      ∑ t, Matrix.of (fun p q => e₁ (a t) p * e₂ (b t) q) := by
  classical
  have hex {d n : ℕ}
      (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (x : Matrix (Fin d) (Fin d) ℂ) (p : Fin n) :
      e x p = ∑ i, ∑ k, x i k * e (Matrix.single i k 1) p := by
    have hs (i k : Fin d) : Matrix.single i k (x i k) =
        x i k • Matrix.single i k (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    have he : e x = ∑ i, ∑ k, x i k • e (Matrix.single i k 1) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single x]
      simp only [map_sum, hs, map_smul]
    have he' := congrArg (fun u : EuclideanSpace ℂ (Fin n) => u p) he
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] using he'
  ext p q
  simp only [testerImage, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.of_apply]
  conv_rhs =>
    arg 2
    ext t
    rw [hex e₁ (a t) p, hex e₂ (b t) q]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₂)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₁)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₂)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₁)))
    (t := (Finset.univ : Finset ι))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d₂)))
    (t := (Finset.univ : Finset (Fin d₁)))]
  simp only [mul_comm, mul_left_comm, mul_assoc]

private theorem projective_decomposition_bound {n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → EuclideanSpace ℂ (Fin n₁)) (b : ι → EuclideanSpace ℂ (Fin n₂))
    (ha : ∑ t, ‖a t‖ ^ 2 ≤ 1) (hb : ∑ t, ‖b t‖ ^ 2 ≤ 1) :
    projNorm (∑ t, Matrix.of (fun p q => a t p * b t q)) ≤ 1 := by
  classical
  have hc : (∑ t, ‖a t‖ * ‖b t‖) ≤ 1 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun t => ‖a t‖) (fun t => ‖b t‖)
    have hp : (∑ t, ‖a t‖ ^ 2) * (∑ t, ‖b t‖ ^ 2) ≤ (1 : ℝ) := by
      nlinarith [Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) => sq_nonneg ‖a t‖),
        Finset.sum_nonneg (fun t (_ : t ∈ Finset.univ) => sq_nonneg ‖b t‖)]
    have hn : 0 ≤ ∑ t, ‖a t‖ * ‖b t‖ :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  apply le_trans (b := ∑ t, ‖a t‖ * ‖b t‖) ?_ hc
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨k, u, v, _, rfl⟩
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · refine ⟨Fintype.card ι, fun t => a ((Fintype.equivFin ι).symm t),
      fun t => b ((Fintype.equivFin ι).symm t), ?_, ?_⟩
    · exact (Equiv.sum_comp (Fintype.equivFin ι).symm
        (fun t => Matrix.of (fun p q => a t p * b t q))).symm
    · exact (Equiv.sum_comp (Fintype.equivFin ι).symm
        (fun t => ‖a t‖ * ‖b t‖)).symm

private theorem witness_bound {n₁ n₂ : ℕ}
    (e₁ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (h₁ : ∀ x, ‖e₁ x‖ ≤ traceNorm x) (h₂ : ∀ x, ‖e₂ x‖ ≤ traceNorm x) :
    projNorm (testerImage e₁ e₂ (werner 3 (1 / 3))) ≤ 1 := by
  classical
  let a : Unit ⊕ EnsembleIndex → Matrix (Fin 3) (Fin 3) ℂ :=
    Sum.elim (fun _ => average) (fun t => Real.sqrt (weight t) • centered t)
  let b : Unit ⊕ EnsembleIndex → Matrix (Fin 3) (Fin 3) ℂ :=
    Sum.elim (fun _ => average) (fun t => (-Real.sqrt (weight t)) • centered t)
  have hρ : werner 3 (1 / 3) = ∑ t, Matrix.kroneckerMap (· * ·) (a t) (b t) := by
    rw [witness_decomposition]
    conv_rhs => rw [Fintype.sum_sum_type]
    simp only [a, b, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ext p q
    simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul, Complex.ofReal_neg]
    have hs : (Real.sqrt (weight t) : ℂ) ^ 2 = (weight t : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (weight_nonneg t)]
    linear_combination (centered t p.1 q.1 * centered t p.2 q.2) * hs
  have hscale {n : ℕ} (r : ℝ) (v : EuclideanSpace ℂ (Fin n)) :
      ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have ha : ∑ t, ‖e₁ (a t)‖ ^ 2 ≤ 1 := by
    simpa only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_unique, LinearMap.map_smul_of_tower, hscale,
      Real.sq_sqrt (weight_nonneg _)] using tester_second_moment e₁ h₁
  have hb : ∑ t, ‖e₂ (b t)‖ ^ 2 ≤ 1 := by
    simpa only [b, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_unique, LinearMap.map_smul_of_tower, hscale, neg_sq,
      Real.sq_sqrt (weight_nonneg _)] using tester_second_moment e₂ h₂
  rw [hρ, tester_image_decomposition]
  exact projective_decomposition_bound (fun t => e₁ (a t)) (fun t => e₂ (b t)) ha hb

/-- The qutrit Werner state at parameter one third refutes tester completeness. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨n₁, n₂, e₁, e₂, h₁, h₂, hdet⟩ :=
    h 3 3 (werner 3 (1 / 3)) witness_pos witness_trace witness_entangled
  exact (not_lt_of_ge (witness_bound e₁ e₂ h₁.1 h₂.1)) hdet

end

end D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
