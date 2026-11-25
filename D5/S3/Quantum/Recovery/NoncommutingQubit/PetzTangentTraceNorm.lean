/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full trace-norm bound for the faithful physical qubit Petz tangent. -/

import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary

/-! Weighted Cauchy–Schwarz with one trace-dual unitary. -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Recovery.PetzTangentTraceNorm

open D5.S3.Quantum.Recovery.PetzTangentPhysical (faithful_weighted_tangent)
open D5.S3.Quantum.Recovery.PetzTangentReciprocalGram (parityMultiplier)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open D5.S3.Divergence.LogDerivTrace (logDeriv)

variable {E : Type} [Fintype E] [DecidableEq E]

open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U traceNorm_nonneg)

private lemma traceNorm_sq_le_arithmetic_weight {n : Type} [Fintype n] [DecidableEq n]
    (Y : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) (lam : n → ℝ)
    (hpos : ∀ i, 0 < lam i) (hmass : ∑ i, lam i = 1) :
    traceNorm Y ^ 2 ≤ ∑ i, ∑ j, Complex.normSq ((U.valᴴ * Y * U.val) i j) / ((lam i+lam j)/2) := by
  obtain ⟨W, hW⟩ := (traceNorm_eq_max_re_tr_U Y).1
  let Q := star U * W * U
  let A := U.valᴴ * Y * U.val
  have hQ : Q.val = U.valᴴ * W.val * U.val := rfl
  have htrace : traceNorm Y = (Q.val * A).trace.re := by
    rw [← hW, hQ]
    have hU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
    have hmul : (U.valᴴ * W.val * U.val) * A = U.valᴴ * (W.val * Y) * U.val := by
      dsimp [A]
      calc
        _ = U.valᴴ * W.val * (U.val * U.valᴴ) * Y * U.val := by noncomm_ring
        _ = _ := by simp [hU, Matrix.mul_assoc]
    rw [hmul]
    conv_rhs => rw [Matrix.trace_mul_comm]
    rw [← Matrix.mul_assoc, hU, one_mul]
  let w := fun i j : n => (lam i+lam j)/2
  let r := fun k : n × n => ‖Q.val k.2 k.1 * A k.1 k.2‖
  let a := fun k : n × n => w k.1 k.2 * ‖Q.val k.2 k.1‖^2
  let b := fun k : n × n => ‖A k.1 k.2‖^2 / w k.1 k.2
  have hw (i j : n) : 0 < w i j := by
    exact div_pos (add_pos (hpos i) (hpos j)) (by norm_num)
  have hbound : traceNorm Y ≤ ∑ k, r k := by
    rw [htrace, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Complex.re_le_norm _
  have hm : ∑ k, a k = 1 := by
    have hrow := Matrix.unitary_row_sum_norm_sq Q.val (Unitary.coe_mul_star_self Q)
    have hcol := Matrix.unitary_col_sum_norm_sq Q.val (Unitary.coe_star_mul_self Q)
    rw [Fintype.sum_prod_type]
    simp only [a, w, Prod.fst, Prod.snd, add_div, add_mul]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show (∑ i, ∑ j, lam j / 2 * ‖Q.val j i‖ ^ 2) =
        ∑ j, ∑ i, lam j / 2 * ‖Q.val j i‖ ^ 2 from Finset.sum_comm]
    norm_num [← Finset.mul_sum, hrow, hcol, ← Finset.sum_div, hmass]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (r := r) (f := a) (g := b) Finset.univ
    (fun k _ => mul_nonneg (hw _ _).le (sq_nonneg _))
    (fun k _ => div_nonneg (sq_nonneg _) (hw _ _).le)
    (fun k _ => by
      dsimp [r, a, b]
      rw [norm_mul, mul_pow]
      field_simp [(hw k.1 k.2).ne']
      exact le_rfl)
  rw [hm, one_mul] at hcs
  have hsq := (pow_le_pow_left₀ (traceNorm_nonneg Y) hbound 2).trans hcs
  simpa only [Fintype.sum_prod_type, b, A, w, Complex.normSq_eq_norm_sq] using hsq

/-- The faithful tangent bound in the full trace norm. -/
theorem faithful_traceNorm_tangent [Nonempty E]
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (hZ : Z.PosDef)
    (htrace : Z.trace.re = 1) :
    let P := partialTraceRight Z
    let M := partialTraceRight H
    let p := (partialTraceRight_posDef Z hZ).isHermitian.eigenvalues
    traceNorm (H - partialTracePetz Z M) ^ 2 ≤ parityMultiplier (2*Real.sqrt (p 0*p 1)) *
      ((Hᴴ * logDeriv Z H).trace.re - (Mᴴ * logDeriv P M).trace.re) := by
  have hT : (partialTraceRight Z).trace.re = 1 := by
    rwa [D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight]
  have hl : ∑ i, hZ.isHermitian.eigenvalues i = 1 := by
    have h := congrArg Complex.re hZ.isHermitian.trace_eq_sum_eigenvalues
    simp only [Complex.re_sum, Complex.ofReal_re] at h
    exact h.symm.trans htrace
  exact (traceNorm_sq_le_arithmetic_weight _ hZ.isHermitian.eigenvectorUnitary _
    hZ.eigenvalues_pos hl).trans (faithful_weighted_tangent Z H hZ hT)

#print axioms faithful_traceNorm_tangent

end D5.S3.Quantum.Recovery.PetzTangentTraceNorm
