/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Taylor
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The four-factor Taylor expansion used in the uniform near-scalar comparator. -/

open scoped BigOperators

noncomputable section

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarTaylor

/-- Multiply in increasing index order. -/
def orderedProd {A : Type*} [Monoid A] {r : ℕ} (f : Fin r → A) : A :=
  (List.ofFn f).prod

private theorem orderedProd_succ {A : Type*} [Monoid A] {r : ℕ}
    (f : Fin (r + 1) → A) :
    orderedProd f = f 0 * orderedProd (fun i => f i.succ) := by
  simp only [orderedProd, List.ofFn_succ, List.prod_cons]

def gapWeight (g : Fin 4 → ℝ) (k : Fin 4 → ℕ) : ℝ :=
  ∏ i, g i ^ k i / (Nat.factorial (k i) : ℝ)

theorem gapWeight_nonneg {g : Fin 4 → ℝ} (hg : ∀ i, 0 ≤ g i) (k : Fin 4 → ℕ) :
    0 ≤ gapWeight g k := by
  exact Finset.prod_nonneg fun i _ =>
    div_nonneg (pow_nonneg (hg i) _) (Nat.cast_nonneg _)

/-- The total factorial weight in degree `m` depends only on the sum of the gaps. -/
theorem sum_gapWeight (g : Fin 4 → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple 4 m, gapWeight g k =
      (∑ i, g i) ^ m / (Nat.factorial m : ℝ) := by
  classical
  have hindex : Finset.piAntidiag (Finset.univ : Finset (Fin 4)) m =
      Finset.Nat.antidiagonalTuple 4 m := by
    ext k
    simp [Finset.Nat.mem_antidiagonalTuple]
  have hm : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  apply (eq_div_iff hm).2
  rw [Finset.sum_mul, Finset.sum_pow_eq_sum_piAntidiag, hindex]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hdegree := Finset.Nat.mem_antidiagonalTuple.mp hk
  have hfact :
      (∏ i, (Nat.factorial (k i) : ℝ)) *
        (Nat.multinomial Finset.univ k : ℝ) = (Nat.factorial m : ℝ) := by
    have hnat := (Nat.multinomial_spec Finset.univ k).trans
      (congrArg Nat.factorial hdegree)
    simpa only [Nat.cast_mul, Nat.cast_prod] using
      congrArg (fun a : ℕ => (a : ℝ)) hnat
  have hdenom : (∏ i, (Nat.factorial (k i) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [gapWeight, Finset.prod_div_distrib, ← hfact, ← mul_assoc, div_mul_cancel₀ _ hdenom]
  exact mul_comm _ _

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Degree `m` of the real trace of the ordered exponential product. -/
def traceCoeff (g : Fin 4 → ℝ) (H B : Matrix n n ℂ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple 4 m,
    gapWeight g k * (Matrix.trace (orderedProd fun i => H ^ k i * B)).re

/-- Subtract the common sorted word at degree `m` before estimating the remainder. -/
theorem traceCoeff_sub_sorted (g : Fin 4 → ℝ) (H B : Matrix n n ℂ) (m : ℕ) :
    traceCoeff g H B m -
        ((∑ i, g i) ^ m / (Nat.factorial m : ℝ)) * (Matrix.trace (H ^ m * B ^ 4)).re =
      ∑ k ∈ Finset.Nat.antidiagonalTuple 4 m, gapWeight g k *
        ((Matrix.trace (orderedProd fun i => H ^ k i * B)).re -
          (Matrix.trace (H ^ m * B ^ 4)).re) := by
  rw [traceCoeff, ← sum_gapWeight g m, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (mul_sub _ _ _).symm

private theorem orderedProd_smul {A : Type*} [Semiring A] [Algebra ℝ A] {r : ℕ}
    (a : Fin r → ℝ) (x : Fin r → A) :
    orderedProd (fun i => a i • x i) = (∏ i, a i) • orderedProd x := by
  induction r with
  | zero => simp [orderedProd]
  | succ r ih =>
      rw [orderedProd_succ, orderedProd_succ, Fin.prod_univ_succ, ih, smul_mul_smul_comm]

private theorem hasSum_orderedProd {A : Type*} [NormedRing A] [CompleteSpace A]
    {r : ℕ} (f : Fin r → ℕ → A) (x : Fin r → A)
    (habs : ∀ i, Summable fun d => ‖f i d‖) (hsum : ∀ i, HasSum (f i) (x i)) :
    (Summable fun k : Fin r → ℕ => ‖orderedProd (fun i => f i (k i))‖) ∧
      HasSum (fun k : Fin r → ℕ => orderedProd (fun i => f i (k i))) (orderedProd x) := by
  induction r with
  | zero =>
      constructor
      · simpa [orderedProd] using
          (hasSum_unique (fun _ : Fin 0 → ℕ => ‖(1 : A)‖)).summable
      · simpa [orderedProd] using hasSum_unique (fun _ : Fin 0 → ℕ => (1 : A))
  | succ r ih =>
      let e := Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)
      let tailTerm (k : Fin r → ℕ) : A := orderedProd fun i => f i.succ (k i)
      obtain ⟨hTailAbs, hTailSum⟩ :=
        ih (fun i => f i.succ) (fun i => x i.succ)
          (fun i => habs i.succ) (fun i => hsum i.succ)
      change Summable (fun k => ‖tailTerm k‖) at hTailAbs
      change HasSum tailTerm (orderedProd fun i => x i.succ) at hTailSum
      have hAbs := (habs 0).mul_norm hTailAbs
      have hSum := (hsum 0).mul hTailSum hAbs.of_norm
      constructor
      · apply e.summable_iff.mp
        simpa only [Function.comp_def, e, Fin.consEquiv_apply, orderedProd_succ,
          Fin.cons_zero, Fin.cons_succ, tailTerm] using hAbs
      · apply e.hasSum_iff.mp
        simpa only [Function.comp_def, e, Fin.consEquiv_apply, orderedProd_succ,
          Fin.cons_zero, Fin.cons_succ, tailTerm] using hSum

section Trace

open scoped Matrix.Norms.Frobenius

omit [DecidableEq n] in
private theorem hasSum_traceRe {ι : Type*} {f : ι → Matrix n n ℂ} {M : Matrix n n ℂ}
    (h : HasSum f M) :
    HasSum (fun i => (Matrix.trace (f i)).re) (Matrix.trace M).re := by
  let tr := (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap
  exact (h.mapL tr).mapL Complex.reCLM

end Trace

section Exponential

open NormedSpace
open scoped Matrix.Norms.L2Operator

private theorem exp_mul_series (g : ℝ) (H B : Matrix n n ℂ) :
    (Summable fun d : ℕ => ‖(g ^ d / (Nat.factorial d : ℝ)) • (H ^ d * B)‖) ∧
      HasSum (fun d : ℕ => (g ^ d / (Nat.factorial d : ℝ)) • (H ^ d * B))
        (exp (g • H) * B) := by
  let : NormedAlgebra ℝ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℝ ℂ (Matrix n n ℂ)
  have hterm (d : ℕ) :
      ((Nat.factorial d : ℝ)⁻¹ • (g • H) ^ d) * B =
        (g ^ d / (Nat.factorial d : ℝ)) • (H ^ d * B) := by
    rw [smul_pow, smul_smul, smul_mul_assoc, div_eq_mul_inv, mul_comm (g ^ d)]
  have habs := norm_expSeries_summable' (𝕂 := ℝ) (g • H)
  refine ⟨?_, ?_⟩
  · refine (habs.mul_right ‖B‖).of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_)
    rw [← hterm]
    exact norm_mul_le _ _
  · simpa only [hterm] using (exp_series_hasSum_exp' (𝕂 := ℝ) (g • H)).mul_right B

/-- The four-factor Cauchy product grouped by total degree, followed by real trace. -/
theorem hasSum_traceCoeff (g : Fin 4 → ℝ) (H B : Matrix n n ℂ) :
    HasSum (traceCoeff g H B)
      (Matrix.trace (orderedProd fun i => exp (g i • H) * B)).re := by
  classical
  let f (i : Fin 4) (d : ℕ) : Matrix n n ℂ :=
    (g i ^ d / (Nat.factorial d : ℝ)) • (H ^ d * B)
  let term (k : Fin 4 → ℕ) : Matrix n n ℂ := orderedProd fun i => f i (k i)
  have hProduct : HasSum term (orderedProd fun i => exp (g i • H) * B) :=
    (hasSum_orderedProd f _ (fun i => (exp_mul_series (g i) H B).1)
      (fun i => (exp_mul_series (g i) H B).2)).2
  have hTrace := hasSum_traceRe hProduct
  let e := Finset.Nat.sigmaAntidiagonalTupleEquivTuple 4
  have hSigma :
      HasSum (fun x : Σ m, Finset.Nat.antidiagonalTuple 4 m =>
        (Matrix.trace (term x.2.val)).re)
        (Matrix.trace (orderedProd fun i => exp (g i • H) * B)).re :=
    e.hasSum_iff.mpr hTrace
  refine hSigma.sigma fun m => ?_
  have hterm (k : Fin 4 → ℕ) :
      (Matrix.trace (term k)).re =
        gapWeight g k * (Matrix.trace (orderedProd fun i => H ^ k i * B)).re := by
    unfold term f
    rw [orderedProd_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, gapWeight]
  unfold traceCoeff
  rw [← Finset.sum_coe_sort]
  simpa only [hterm] using
    (hasSum_fintype fun k : Finset.Nat.antidiagonalTuple 4 m =>
      (Matrix.trace (term k.val)).re)

end Exponential

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarTaylor
