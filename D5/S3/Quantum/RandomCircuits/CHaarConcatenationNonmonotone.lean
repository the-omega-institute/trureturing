/- GID: D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone
   generality: I
   mirror-B: D5/B/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone
   mirror-E: none(waiver:kernel-checked-content)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.claim; result=D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.result; claim=D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.claim
   digest: The literal second cHaar moment has larger squared norm at power five than four. -/

/-
admission_basis: open-problem-resolution (#15553; Refuted).
escape_witness: none.
proof_shape: cHaarChannel: bind-only; consumers: momentOp, cHaarSingle, twoCopyIntegrand, momentOp2HaarEntries.
proof_shape: momentOp: bind-only; consumers: claim, momentOp2HaarEntries, momentOp2Formula, moment22Reindex, instanceN4, instanceN5, result.
proof_shape: hsNormSq: bind-only; consumers: claim, result.
proof_shape: claim: bind-only; consumers: result.
proof_shape: swapHermitian: bind-only; consumers: twirlSwapTrace.
proof_shape: swapSquare: bind-only; consumers: twirlFormula.
proof_shape: traceSwap: bind-only; consumers: twirlFormula.
proof_shape: twirlTrace: bind-only; consumers: twirlFormula.
proof_shape: twirlSwapTrace: bind-only; consumers: twirlFormula.
proof_shape: twirlFormula: bind-only; consumers: haarAverageEntry.
proof_shape: haarAverageEntry: bind-only; consumers: momentOp2Formula.
proof_shape: cHaarSingle: bind-only; consumers: twoCopyIntegrand.
proof_shape: jointIndex: bind-only; consumers: twoCopyIntegrand, momentOp2HaarEntries, jointId, jointSwap, jointSwapRev, momentOp2Formula.
proof_shape: twoCopyIntegrand: bind-only; consumers: momentOp2HaarEntries.
proof_shape: momentOp2HaarEntries: bind-only; consumers: momentOp2Formula.
proof_shape: jointId: bind-only; consumers: momentOp2Formula.
proof_shape: jointSwap: bind-only; consumers: jointSwapRev, momentOp2Formula.
proof_shape: jointSwapRev: bind-only; consumers: momentOp2Formula.
proof_shape: momentOp2Formula: bind-only; consumers: moment22Reindex.
proof_shape: w: bind-only; consumers: Q, R, uDotW, wDotU, wDotW, moment22Reindex, pMulQ, pMulR, qMulP, qMulQ, qMulR, rMulP, rMulQ, rMulR, normNormal.
proof_shape: P: bind-only; consumers: A, pMulP, pMulQ, pMulR, qMulP, rMulP, aMulNormal, aPow, normNormal, instanceN4, instanceN5.
proof_shape: Q: bind-only; consumers: A, pMulQ, qMulP, qMulQ, qMulR, rMulQ, aMulNormal, aPow, normNormal, instanceN4, instanceN5.
proof_shape: R: bind-only; consumers: A, pMulR, qMulR, rMulP, rMulQ, rMulR, aMulNormal, aPow, normNormal, instanceN4, instanceN5.
proof_shape: A: bind-only; consumers: moment22Reindex, aMulNormal, aPow, instanceN4, instanceN5.
proof_shape: uDotU: bind-only; consumers: pMulP, qMulP.
proof_shape: uDotW: bind-only; consumers: wDotU, pMulQ, pMulR, qMulQ, qMulR.
proof_shape: wDotU: bind-only; consumers: rMulP.
proof_shape: wDotW: bind-only; consumers: rMulQ, rMulR.
proof_shape: moment22Reindex: bind-only; consumers: instanceN4, instanceN5.
proof_shape: pMulP: bind-only; consumers: aMulNormal.
proof_shape: pMulQ: bind-only; consumers: aMulNormal.
proof_shape: pMulR: bind-only; consumers: aMulNormal.
proof_shape: qMulP: bind-only; consumers: aMulNormal.
proof_shape: qMulQ: bind-only; consumers: aMulNormal.
proof_shape: qMulR: bind-only; consumers: aMulNormal.
proof_shape: rMulP: bind-only; consumers: aMulNormal.
proof_shape: rMulQ: bind-only; consumers: aMulNormal.
proof_shape: rMulR: bind-only; consumers: aMulNormal.
proof_shape: aMulNormal: bind-only; consumers: aPow.
proof_shape: aPow: content; consumers: instanceN4, instanceN5.
proof_shape: hsNormSqCorrespondence: bind-only; consumer: normReindex, normNormal, result.
proof_shape: normReindex: bind-only; consumers: instanceN4, instanceN5.
proof_shape: normNormal: bind-only; consumers: instanceN4, instanceN5.
proof_shape: instanceN4: bind-only; consumers: result.
proof_shape: instanceN5: bind-only; consumers: result.
proof_shape: result: bind-only; consumers: none (designated refutation result).
The aPow induction is a consumed invariant, not an escape witness for the finite refutation.
Direct frozen dependencies (declaration statement_id, not module pins):
F1: D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
  sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
F2: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant.replicaSwap_apply
  sha256:e3427bb6efbbe3e9b723be03b86574ca66e788ed2d360508fdb706fa7b764080
F3: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.haarAverage
  sha256:643023e91c290d010b39ef66865832300da6bc0e9e247a1d942263cdbaef62ba
F4: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.haarAverage_hermitian
  sha256:e2c73307f067b03207d0f3f7d1d834657288c35f0eccfdf141f5cf0d50ef2c08
F5: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.haarAverage_identity_fixed
  sha256:b7e1bc0bee2a33d3da5732a7d8d3c96dadf292c003f4698a39bc9f6d6ae544f7
F6: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.haarAverage_image_span
  sha256:9c148163365a59f540f3e854581a5066b8373b36936af617f39db9e095a337af
F7: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.haarAverage_swap_fixed
  sha256:4140ddf84490bd3b1b543ceeadf3f3208a4d8d9335600bc17a932777dae22758
F8: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.hermitian_fixed_pairing
  sha256:9ea713521ccc6215fc514afd9c2c5507a4e5dcc7b677cf819086214ea0a54163
F9: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.literalMoment
  sha256:6d3808f646b3a2dccfb6f436f49901190286d1e2981e01de7c972ab57d7d214d
F10: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.literalMoment_integrable
  sha256:6aeca34ab3850c51aee19232cf3d90e3fed0e26d6714c829c20c1904fdb6f3c6
F11: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.unitaryBorelSpace
  sha256:757f890bf0f7c651f03551550d08fb6b7b44524790dd9502bb910d11d5d7843a
F12: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.unitaryCompactSpace
  sha256:2cec9c00a5ea65c8a268bcfb410af53b86bea819b3619fe6453185aea736e95d
F13: D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.unitaryMeasurableSpace
  sha256:abb9c185cb4644ae2b034b61c7aa2a837e9832ef73855984512122acadf02844
F14: RHLinalg.frobSq
  sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
F15: D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace
  sha256:470140292aee89705512206af514f5a42fdc3948e5c9195d302613a47b859917
Direct frozen dependencies: cHaarChannel: F1.
Direct frozen dependencies: momentOp: F13, F11, F12, F1.
Direct frozen dependencies: hsNormSq: none.
Direct frozen dependencies: claim: F13, F11, F12, F1.
Direct frozen dependencies: swapHermitian: none.
Direct frozen dependencies: swapSquare: none.
Direct frozen dependencies: traceSwap: none.
Direct frozen dependencies: twirlTrace: F3, F8, F4, F5.
Direct frozen dependencies: twirlSwapTrace: F3, F8, F4, F7.
Direct frozen dependencies: twirlFormula: F3, F6, F8, F4, F5, F7.
Direct frozen dependencies: haarAverageEntry: F3, F6, F8, F4, F5, F7.
Direct frozen dependencies: cHaarSingle: F1.
Direct frozen dependencies: jointIndex: none.
Direct frozen dependencies: twoCopyIntegrand: F1, F9.
Direct frozen dependencies: momentOp2HaarEntries: F13, F11, F12, F1, F3, F9, F10.
Direct frozen dependencies: jointId: none.
Direct frozen dependencies: jointSwap: none.
Direct frozen dependencies: jointSwapRev: none.
Direct frozen dependencies: momentOp2Formula: F13, F11, F12, F1, F3, F9, F10, F6, F8, F4, F5, F7.
Direct frozen dependencies: w: none.
Direct frozen dependencies: P: none.
Direct frozen dependencies: Q: none.
Direct frozen dependencies: R: none.
Direct frozen dependencies: A: none.
Direct frozen dependencies: uDotU: none.
Direct frozen dependencies: uDotW: none.
Direct frozen dependencies: wDotU: none.
Direct frozen dependencies: wDotW: none.
Direct frozen dependencies: moment22Reindex: F13, F11, F12, F1, F3, F9, F10, F6, F8, F4, F5, F7, F2.
Direct frozen dependencies: pMulP: none.
Direct frozen dependencies: pMulQ: none.
Direct frozen dependencies: pMulR: none.
Direct frozen dependencies: qMulP: none.
Direct frozen dependencies: qMulQ: none.
Direct frozen dependencies: qMulR: none.
Direct frozen dependencies: rMulP: none.
Direct frozen dependencies: rMulQ: none.
Direct frozen dependencies: rMulR: none.
Direct frozen dependencies: aMulNormal: none.
Direct frozen dependencies: aPow: none.
Direct frozen dependencies: hsNormSqCorrespondence: F14, F15.
Direct frozen dependencies: normReindex: F14, F15.
Direct frozen dependencies: normNormal: F14, F15.
Direct frozen dependencies: instanceN4: F14, F15, F13, F11, F12, F1, F3, F9, F10, F6, F8, F4, F5, F7, F2.
Direct frozen dependencies: instanceN5: F14, F15, F13, F11, F12, F1, F3, F9, F10, F6, F8, F4, F5, F7, F2.
Direct frozen dependencies: result: F14, F15, F13, F11, F12, F1, F3, F9, F10, F6, F8, F4, F5, F7, F2.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Every other newly authored public theorem would be an escape-audit target;
the seven owner publications expose existing frozen proofs.
The channel uses partialTraceRight, whose defining sum is exactly the source's
partial trace over the environment. Its ancilla is Matrix.single 0 0 1.
The two-copy average is expressed through haarAverage acting on Matrix.vec;
Matrix.of with Function.curry and Prod.swap performs the inverse vectorization.
No separate twirl, swap matrix, identity vector or coordinate equivalence is defined.
The claim uses hsNormSq, the double sum of Complex.normSq. The frozen
`GNSMatrix.frobenius_norm_sq_eq_trace` identity supplies the trace form; taking
real parts and using Mathlib's Frobenius norm and `Complex.normSq_eq_norm_sq`
gives exactly the double sum.
-/

import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Quantum.GNSMatrix

open Matrix MeasureTheory TopologicalSpace
open scoped Kronecker
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
noncomputable section

namespace D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone

def cHaarChannel (d e : ℕ) [NeZero e]
    (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
    (U * Matrix.kroneckerMap (· * ·) X
      (Matrix.single 0 0 1 : Matrix (Fin e) (Fin e) ℂ) * star U)

def momentOp (d e t : ℕ) [NeZero e] :
    Matrix ((Fin t → Fin d) × (Fin t → Fin d))
      ((Fin t → Fin d) × (Fin t → Fin d)) ℂ :=
  fun r c => ∫ U : Matrix.unitaryGroup (Fin d × Fin e) ℂ,
    ∏ s : Fin t,
      cHaarChannel d e U.val (Matrix.single (c.1 s) (c.2 s) 1) (r.1 s) (r.2 s)
        ∂(Measure.haarMeasure ⊤)

def hsNormSq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ :=
  ∑ r, ∑ c, Complex.normSq (M r c)

def claim : Prop := ∀ (d e t : ℕ) [NeZero e],
  1 ≤ d → 1 ≤ t → ∀ k k' : ℕ, 1 ≤ k → k ≤ k' →
    hsNormSq ((momentOp d e t)^k') ≤ hsNormSq ((momentOp d e t)^k)


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem swapHermitian : ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))).IsHermitian := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [Matrix.conjTranspose_apply, Prod.swap_prod_mk, Prod.mk.injEq]
  simp [and_comm, eq_comm]

theorem swapSquare : (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) = 1 := by
  have h : Equiv.prodComm n n * Equiv.prodComm n n = (1 : Equiv.Perm (n×n)) := by
    ext x <;> rfl
  simp [← Matrix.permMatrix_mul, h]

theorem traceSwap : Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))) = (Fintype.card n : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp [Prod.ext_iff, eq_comm]

private theorem twirlTrace (Y : Matrix (n×n) (n×n) ℂ) :
    Matrix.trace (Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = Matrix.trace Y := by
  have h := hermitian_fixed_pairing (haarAverage n) haarAverage_hermitian
    (Matrix.vec (1 : Matrix (n×n) (n×n) ℂ)) (Matrix.vec Y) haarAverage_identity_fixed
  have hv : Matrix.vec (Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = (haarAverage n).mulVec (Matrix.vec Y) := by rfl
  rw [← hv, Matrix.star_vec_dotProduct_vec, Matrix.star_vec_dotProduct_vec] at h
  simpa using h

private theorem twirlSwapTrace (Y : Matrix (n×n) (n×n) ℂ) :
    Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) := by
  have h := hermitian_fixed_pairing (haarAverage n) haarAverage_hermitian
    (Matrix.vec ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)))) (Matrix.vec Y) haarAverage_swap_fixed
  have hv : Matrix.vec (Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap))) = (haarAverage n).mulVec (Matrix.vec Y) := by rfl
  rw [← hv, Matrix.star_vec_dotProduct_vec, Matrix.star_vec_dotProduct_vec,
      swapHermitian.eq] at h
  exact h

private theorem twirlFormula (Y : Matrix (n×n) (n×n) ℂ) (hN : 2 ≤ Fintype.card n) :
    Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap)) =
      ((Matrix.trace Y - Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2 - 1)) • (1 : Matrix (n×n) (n×n) ℂ) +
      ((Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) - Matrix.trace Y / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2 - 1)) • (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) := by
  letI : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,b,hab⟩ := exists_pair_ne n
  obtain ⟨x,y,hxy⟩ := haarAverage_image_span (Matrix.vec Y) a b hab
  have hv : Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap)) = x • (1 : Matrix (n×n) (n×n) ℂ) + y • (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) := by
    ext r c
    change ((haarAverage n).mulVec (Matrix.vec Y)) (c,r) = _
    exact congrFun hxy (c,r)
  have h0 := twirlTrace Y
  have h1 := twirlSwapTrace Y
  rw [hv, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, traceSwap] at h0
  rw [hv, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      swapSquare, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      traceSwap, Matrix.trace_one] at h1
  simp only [Fintype.card_prod, Nat.cast_mul, smul_eq_mul] at h0 h1
  have hn : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast (show Fintype.card n ≠ 0 by omega)
  have hden : (Fintype.card n : ℂ)^2 - 1 ≠ 0 := by
    have hi : (2 : ℤ) ≤ Fintype.card n := by exact_mod_cast hN
    have hz : (Fintype.card n : ℤ)^2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast hz
  have hx : x = (Matrix.trace Y - Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) / (Fintype.card n : ℂ)) /
      ((Fintype.card n : ℂ)^2 - 1) := by
    rw [← h0, ← h1]
    field_simp [hn, hden]
    <;> ring
  have hy : y = (Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) - Matrix.trace Y / (Fintype.card n : ℂ)) /
      ((Fintype.card n : ℂ)^2 - 1) := by
    rw [← h0, ← h1]
    field_simp [hn, hden]
    <;> ring
  rw [hv, hx, hy]

private theorem haarAverageEntry {n : Type*} [Fintype n] [DecidableEq n]
    (r c : ((n×n)×(n×n))) (hN : 2 ≤ Fintype.card n) :
    haarAverage n r c =
      (((if c.2=c.1 then 1 else 0 : ℂ) - (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) c.1 c.2 / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2-1)) * (if r.2=r.1 then 1 else 0) +
      (((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) c.1 c.2 - (if c.2=c.1 then 1 else 0 : ℂ) / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2-1)) * (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) r.2 r.1 := by
  have h := congrFun (congrFun (twirlFormula (Matrix.single c.2 c.1 (1:ℂ)) hN) r.2) r.1
  have he : Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec (Matrix.single c.2 c.1 (1:ℂ)))) ∘ Prod.swap)) r.2 r.1 = haarAverage n r c := by
    simp [Matrix.of_apply, Function.curry, Function.comp_apply, Prod.swap, Matrix.vec_single]
  rw [he] at h
  have ht : Matrix.trace (Matrix.single c.2 c.1 (1:ℂ)) = (if c.2=c.1 then 1 else 0 : ℂ) := by
    by_cases hc : c.2=c.1 <;> simp [hc]
  simpa [ht, Matrix.trace_mul_single, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] using h

private theorem cHaarSingle (d e : ℕ) [NeZero e]
    (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (a b i j : Fin d) :
    cHaarChannel d e U (Matrix.single a b 1) i j =
      ∑ k : Fin e, U (i,k) (a,0) * star (U (j,k) (b,0)) := by
  simp [cHaarChannel, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.single,
    Fintype.sum_prod_type, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    mul_ite, ite_mul, ite_and]

private def jointIndex (d e : ℕ) (r : (Fin 2 → Fin d) × (Fin 2 → Fin d)) (k l : Fin e) :
    (((Fin d × Fin e) × (Fin d × Fin e)) × ((Fin d × Fin e) × (Fin d × Fin e))) :=
  (((r.2 0,k),(r.2 1,l)),((r.1 0,k),(r.1 1,l)))

private theorem twoCopyIntegrand (d e : ℕ) [NeZero e]
    (r c : (Fin 2 → Fin d) × (Fin 2 → Fin d))
    (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) :
    (∏ s : Fin 2, cHaarChannel d e U (Matrix.single (c.1 s) (c.2 s) 1) (r.1 s) (r.2 s)) =
      ∑ k : Fin e, ∑ l : Fin e, literalMoment U (jointIndex d e r k l) (jointIndex d e c 0 0) := by
  rw [Fin.prod_univ_two]
  simp only [cHaarSingle]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  apply Finset.sum_congr rfl; intro l hl
  simp only [literalMoment, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply,
    jointIndex]
  ring

private theorem momentOp2HaarEntries (d e : ℕ) [NeZero e]
    (r c : (Fin 2 → Fin d) × (Fin 2 → Fin d)) :
    momentOp d e 2 r c = ∑ k : Fin e, ∑ l : Fin e,
      haarAverage (Fin d × Fin e) (jointIndex d e r k l) (jointIndex d e c 0 0) := by
  simp only [momentOp, twoCopyIntegrand]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl; intro k hk
    rw [integral_finsetSum]
    · rfl
    · intro l hl; exact literalMoment_integrable _ _
  · intro k hk
    exact integrable_finsetSum _ (fun l hl => literalMoment_integrable _ _)

private theorem jointId (d e : ℕ) (r : (Fin 2 → Fin d) × (Fin 2 → Fin d)) (k l : Fin e) :
    (if (jointIndex d e r k l).2 = (jointIndex d e r k l).1 then 1 else 0 : ℂ) =
      (if r.1 0 = r.2 0 ∧ r.1 1 = r.2 1 then 1 else 0 : ℂ) := by
  simp [jointIndex, Prod.ext_iff]

private theorem jointSwap (d e : ℕ) (r : (Fin 2 → Fin d) × (Fin 2 → Fin d)) (k l : Fin e) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d × Fin e) (Fin d × Fin e))) (jointIndex d e r k l).2 (jointIndex d e r k l).1 =
      (if r.1 0 = r.2 1 ∧ r.1 1 = r.2 0 then 1 else 0 : ℂ) * (if k=l then 1 else 0 : ℂ) := by
  simp only [jointIndex, Prod.swap_prod_mk, Prod.mk.injEq]
  by_cases h : k=l
  · subst l; simp [and_comm]
  · simp [h, Ne.symm h]

private theorem jointSwapRev (d e : ℕ) (r : (Fin 2 → Fin d) × (Fin 2 → Fin d)) (k l : Fin e) :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d × Fin e) (Fin d × Fin e))) (jointIndex d e r k l).1 (jointIndex d e r k l).2 =
      (if r.1 0 = r.2 1 ∧ r.1 1 = r.2 0 then 1 else 0 : ℂ) * (if k=l then 1 else 0 : ℂ) := by
  simpa only [jointIndex, Prod.swap, eq_comm, and_comm] using
    jointSwap d e r.swap k l

private theorem momentOp2Formula (d e : ℕ) [NeZero e] (hd : 2 ≤ d)
    (r c : (Fin 2 → Fin d) × (Fin 2 → Fin d)) :
    momentOp d e 2 r c =
      ((e:ℂ)^2 * ((if c.1 0 = c.2 0 ∧ c.1 1 = c.2 1 then 1 else 0 : ℂ) - (if c.1 0 = c.2 1 ∧ c.1 1 = c.2 0 then 1 else 0 : ℂ) / (d*e:ℂ)) /
        ((d*e:ℂ)^2 - 1)) * (if r.1 0 = r.2 0 ∧ r.1 1 = r.2 1 then 1 else 0 : ℂ) +
      ((e:ℂ) * ((if c.1 0 = c.2 1 ∧ c.1 1 = c.2 0 then 1 else 0 : ℂ) - (if c.1 0 = c.2 0 ∧ c.1 1 = c.2 1 then 1 else 0 : ℂ) / (d*e:ℂ)) /
        ((d*e:ℂ)^2 - 1)) * (if r.1 0 = r.2 1 ∧ r.1 1 = r.2 0 then 1 else 0 : ℂ) := by
  have hN : 2 ≤ Fintype.card (Fin d × Fin e) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have he : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (NeZero.ne e)
    nlinarith
  rw [momentOp2HaarEntries]
  simp only [haarAverageEntry _ _ hN]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simp only [jointId, jointSwap, jointSwapRev]
  simp only [ite_true, mul_one]
  simp only [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> ring

private def w : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℂ :=
  fun r => 2 * (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2))) r.1 r.2 -
    Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) r

private def P : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := (1/4 : ℂ) • Matrix.vecMulVec (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))

private def Q : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := (1/4 : ℂ) • Matrix.vecMulVec w (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))

private def R : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := (1/12 : ℂ) • Matrix.vecMulVec w w

private def A : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := P + (1/15 : ℂ) • Q + (2/5 : ℂ) • R

private theorem uDotU : (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ⬝ᵥ (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = (4:ℂ) := by
  norm_num [dotProduct, Matrix.vec, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem uDotW : (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ⬝ᵥ w = (0:ℂ) := by
  norm_num [dotProduct, Matrix.vec, Matrix.one_apply, w, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Prod.swap_prod_mk, Prod.mk.injEq, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem wDotU : w ⬝ᵥ (Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = (0:ℂ) := by
  rw [dotProduct_comm, uDotW]

private theorem wDotW : w ⬝ᵥ w = (12:ℂ) := by
  norm_num [dotProduct, Matrix.vec, Matrix.one_apply, w, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Prod.swap_prod_mk, Prod.mk.injEq, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem moment22Reindex : Matrix.reindex ((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2))) ((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2))) (momentOp 2 2 2) = A := by
  ext r c
  change momentOp 2 2 2 (((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2))).symm r) (((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2))).symm c) = A r c
  rw [momentOp2Formula 2 2 (by norm_num)]
  change
    ((2:ℂ)^2 * ((if c.1.1=c.2.1 ∧ c.1.2=c.2.2 then 1 else 0) -
      (if c.1.1=c.2.2 ∧ c.1.2=c.2.1 then 1 else 0) / (2*2:ℂ)) /
      ((2*2:ℂ)^2-1)) * (if r.1.1=r.2.1 ∧ r.1.2=r.2.2 then 1 else 0) +
    ((2:ℂ) * ((if c.1.1=c.2.2 ∧ c.1.2=c.2.1 then 1 else 0) -
      (if c.1.1=c.2.1 ∧ c.1.2=c.2.2 then 1 else 0) / (2*2:ℂ)) /
      ((2*2:ℂ)^2-1)) * (if r.1.1=r.2.2 ∧ r.1.2=r.2.1 then 1 else 0) = A r c
  have hid (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) :
      Matrix.vec (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) x =
        (if x.1.1 = x.2.1 ∧ x.1.2 = x.2.2 then 1 else 0 : ℂ) := by
    simp only [Matrix.vec, Matrix.one_apply, Prod.mk.injEq]
    simp only [Prod.ext_iff, eq_comm]
  have hswap (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) :
      (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin 2) (Fin 2))) x.1 x.2 =
        (if x.1.1 = x.2.2 ∧ x.1.2 = x.2.1 then 1 else 0 : ℂ) := by
    simp only [Commutant.replicaSwap_apply, Prod.ext_iff, Prod.swap]
    simp only [and_comm]
  simp only [A, P, Q, R, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, w, hid, hswap]
  split_ifs <;> norm_num <;> ring

private theorem pMulP : P * P = P := by
  simp [P, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, uDotU,
    Matrix.vecMulVec_smul, smul_smul]

private theorem pMulQ : P * Q = 0 := by
  simp [P,Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, uDotW]

private theorem pMulR : P * R = 0 := by
  simp [P,R, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, uDotW]

private theorem qMulP : Q * P = Q := by
  simp [P,Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, uDotU,
    Matrix.vecMulVec_smul, smul_smul]

private theorem qMulQ : Q * Q = 0 := by
  simp [Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, uDotW]

private theorem qMulR : Q * R = 0 := by
  simp [Q,R, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, uDotW]

private theorem rMulP : R * P = 0 := by
  simp [P,R, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, wDotU]

private theorem rMulQ : R * Q = Q := by
  simp [Q,R, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, wDotW,
    Matrix.vecMulVec_smul, smul_smul]

private theorem rMulR : R * R = R := by
  simp [R, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, wDotW,
    Matrix.vecMulVec_smul, smul_smul]

private theorem aMulNormal (b z : ℂ) :
    A * (P + b • Q + z • R) = P + (1/15 + (2/5)*b : ℂ) • Q + ((2/5)*z : ℂ) • R := by
  simp only [A, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    pMulP, pMulQ, pMulR, qMulP, qMulQ, qMulR,
    rMulP, rMulQ, rMulR, smul_zero, add_zero, zero_add, smul_smul]
  module

private theorem aPow (k : ℕ) (hk : 1 ≤ k) :
    A^k = P + ((1/9 : ℂ)*(1-(2/5 : ℂ)^k)) • Q + ((2/5 : ℂ)^k) • R := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k=0
    · subst k; norm_num [A]
    · rw [pow_succ', ih (by omega), aMulNormal, pow_succ]
      congr 2 <;> ring

private theorem hsNormSqCorrespondence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    RHLinalg.frobSq M = ∑ r, ∑ c, Complex.normSq (M r c) := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace M)
  rw [Complex.ofReal_re] at h
  unfold RHLinalg.frobSq
  change (Mᴴ * M).trace.re = _
  rw [← h, Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  positivity

private theorem normReindex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (f : ι ≃ κ) (M : Matrix ι ι ℂ) :
    RHLinalg.frobSq (Matrix.reindex f f M) = RHLinalg.frobSq M := by
  rw [hsNormSqCorrespondence, hsNormSqCorrespondence]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  apply Fintype.sum_equiv f.symm
  intro r
  exact f.symm.sum_comp (fun c => Complex.normSq (M (f.symm r) c))

private theorem normNormal (b z : ℂ) (hb : b.im=0) (hz : z.im=0) :
    RHLinalg.frobSq (P + b • Q + z • R) = 1 + 3*b.re^2 + z.re^2 := by
  rw [hsNormSqCorrespondence]
  norm_num [P,Q,R,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,Matrix.vec,Matrix.one_apply,w,
    Pi.smul_apply,Pi.sub_apply,Prod.swap_prod_mk,Prod.mk.injEq,Fintype.sum_prod_type,Fin.sum_univ_two,
    Complex.normSq_apply,Complex.add_re,Complex.mul_re,Complex.mul_im,hb,hz]
  ring

private theorem instanceN4 : RHLinalg.frobSq ((momentOp 2 2 2)^4) = (1213852/1171875 : ℝ) := by
  rw [← normReindex ((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2)))]
  change RHLinalg.frobSq ((Matrix.reindexRingEquiv ℂ ((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2)))) ((momentOp 2 2 2)^4)) = _
  rw [map_pow, Matrix.coe_reindexRingEquiv, moment22Reindex, aPow 4 (by norm_num)]
  rw [normNormal _ _ (by norm_num) (by norm_num)]
  norm_num

private theorem instanceN5 : RHLinalg.frobSq ((momentOp 2 2 2)^5) = (30362908/29296875 : ℝ) := by
  rw [← normReindex ((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2)))]
  change RHLinalg.frobSq ((Matrix.reindexRingEquiv ℂ ((finTwoArrowEquiv (Fin 2)).prodCongr (finTwoArrowEquiv (Fin 2)))) ((momentOp 2 2 2)^5)) = _
  rw [map_pow, Matrix.coe_reindexRingEquiv, moment22Reindex, aPow 5 (by norm_num)]
  rw [normNormal _ _ (by norm_num) (by norm_num)]
  norm_num

theorem result : ¬ claim := by
  intro h
  have hi := h 2 2 2 (by norm_num) (by norm_num) 4 5 (by norm_num) (by norm_num)
  unfold hsNormSq at hi
  rw [← hsNormSqCorrespondence, ← hsNormSqCorrespondence] at hi
  rw [instanceN4, instanceN5] at hi
  norm_num at hi


end D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
