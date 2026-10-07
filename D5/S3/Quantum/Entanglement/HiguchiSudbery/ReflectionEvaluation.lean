/- GID: D5/S3/Quantum/Entanglement/HiguchiSudbery/ReflectionEvaluation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HiguchiSudbery/ReflectionEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result; instance=D5/S3/Quantum/Entanglement/HiguchiSudbery/PrimeHierarchyCertificate.prime_certificate_identity
   digest: ReflectionEvaluation for the sharp four-qubit marginal entropy bound. -/

/- admission_basis: escape-witness
The generic weighted square law proves nonnegativity for all sparse polynomials. -/

import D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
import D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly

noncomputable section
namespace D5.S3.Quantum.Entanglement.HiguchiSudbery
open private ref_swapIndex ref_vars ref_vars_swap ref_eval_swap ref_eval_swap_vars from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private squaredAmplitudeTotal from D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.style.longLine false

open private literalMinor totalMinorE3 det_map_star_3 normPair_star from D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly
open private
  ref_normPoly
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private
  ref_sortFuel ref_sortFuel_perm
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private
  ref_eval ref_evalTerm ref_swap
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private lemma ref_eval_normPoly /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) :
    ref_eval (ref_vars z) ref_normPoly = dotProduct z (star z) := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, ref_vars, ref_normPoly, dotProduct, Fin.sum_univ_succ]
  ring!
open private ref_m0 ref_m1 ref_m2 ref_m3 ref_m4 ref_m5 ref_m6 ref_m7 ref_m8 ref_m9 ref_m10 ref_m11 ref_m12 ref_m13 ref_m14 ref_m15 ref_m16 ref_m17 ref_m18 ref_m19 ref_m20 ref_m21 ref_m22 ref_m23 ref_m24 ref_m25 ref_m26 ref_m27 ref_m28 ref_m29 ref_m30 ref_m31 ref_m32 ref_m33 ref_m34 ref_m35 ref_m36 ref_m37 ref_m38 ref_m39 ref_m40 ref_m41 ref_m42 ref_m43 ref_m44 ref_m45 ref_m46 ref_m47 from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
private lemma ref_eval_m0 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m0 = literalMinor z 0 0 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m0]
  ring!
private lemma ref_eval_m1 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m1 = literalMinor z 0 0 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m1]
  ring!
private lemma ref_eval_m2 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m2 = literalMinor z 0 0 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m2]
  ring!
private lemma ref_eval_m3 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m3 = literalMinor z 0 0 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m3]
  ring!
private lemma ref_eval_m4 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m4 = literalMinor z 0 1 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m4]
  ring!
private lemma ref_eval_m5 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m5 = literalMinor z 0 1 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m5]
  ring!
private lemma ref_eval_m6 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m6 = literalMinor z 0 1 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m6]
  ring!
private lemma ref_eval_m7 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m7 = literalMinor z 0 1 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m7]
  ring!
private lemma ref_eval_m8 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m8 = literalMinor z 0 2 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m8]
  ring!
private lemma ref_eval_m9 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m9 = literalMinor z 0 2 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m9]
  ring!
private lemma ref_eval_m10 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m10 = literalMinor z 0 2 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m10]
  ring!
private lemma ref_eval_m11 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m11 = literalMinor z 0 2 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m11]
  ring!
private lemma ref_eval_m12 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m12 = literalMinor z 0 3 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m12]
  ring!
private lemma ref_eval_m13 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m13 = literalMinor z 0 3 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m13]
  ring!
private lemma ref_eval_m14 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m14 = literalMinor z 0 3 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m14]
  ring!
private lemma ref_eval_m15 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m15 = literalMinor z 0 3 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m15]
  ring!
private lemma ref_eval_m16 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m16 = literalMinor z 1 0 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m16]
  ring!
private lemma ref_eval_m17 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m17 = literalMinor z 1 0 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m17]
  ring!
private lemma ref_eval_m18 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m18 = literalMinor z 1 0 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m18]
  ring!
private lemma ref_eval_m19 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m19 = literalMinor z 1 0 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m19]
  ring!
private lemma ref_eval_m20 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m20 = literalMinor z 1 1 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m20]
  ring!
private lemma ref_eval_m21 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m21 = literalMinor z 1 1 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m21]
  ring!
private lemma ref_eval_m22 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m22 = literalMinor z 1 1 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m22]
  ring!
private lemma ref_eval_m23 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m23 = literalMinor z 1 1 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m23]
  ring!
private lemma ref_eval_m24 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m24 = literalMinor z 1 2 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m24]
  ring!
private lemma ref_eval_m25 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m25 = literalMinor z 1 2 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m25]
  ring!
private lemma ref_eval_m26 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m26 = literalMinor z 1 2 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m26]
  ring!
private lemma ref_eval_m27 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m27 = literalMinor z 1 2 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m27]
  ring!
private lemma ref_eval_m28 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m28 = literalMinor z 1 3 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m28]
  ring!
private lemma ref_eval_m29 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m29 = literalMinor z 1 3 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m29]
  ring!
private lemma ref_eval_m30 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m30 = literalMinor z 1 3 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m30]
  ring!
private lemma ref_eval_m31 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m31 = literalMinor z 1 3 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m31]
  ring!
private lemma ref_eval_m32 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m32 = literalMinor z 2 0 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m32]
  ring!
private lemma ref_eval_m33 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m33 = literalMinor z 2 0 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m33]
  ring!
private lemma ref_eval_m34 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m34 = literalMinor z 2 0 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m34]
  ring!
private lemma ref_eval_m35 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m35 = literalMinor z 2 0 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m35]
  ring!
private lemma ref_eval_m36 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m36 = literalMinor z 2 1 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m36]
  ring!
private lemma ref_eval_m37 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m37 = literalMinor z 2 1 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m37]
  ring!
private lemma ref_eval_m38 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m38 = literalMinor z 2 1 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m38]
  ring!
private lemma ref_eval_m39 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m39 = literalMinor z 2 1 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m39]
  ring!
private lemma ref_eval_m40 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m40 = literalMinor z 2 2 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m40]
  ring!
private lemma ref_eval_m41 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m41 = literalMinor z 2 2 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m41]
  ring!
private lemma ref_eval_m42 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m42 = literalMinor z 2 2 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m42]
  ring!
private lemma ref_eval_m43 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m43 = literalMinor z 2 2 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m43]
  ring!
private lemma ref_eval_m44 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m44 = literalMinor z 2 3 0 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m44]
  ring!
private lemma ref_eval_m45 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m45 = literalMinor z 2 3 1 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m45]
  ring!
private lemma ref_eval_m46 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m46 = literalMinor z 2 3 2 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m46]
  ring!
private lemma ref_eval_m47 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_lhs -/ (z : Fin 16 → ℂ) : ref_eval (ref_vars z) ref_m47 = literalMinor z 2 3 3 := by
  norm_num (config := {decide := true}) [ref_eval, ref_evalTerm, literalMinor, cutFlatten, cutIndex, Fin.rev, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ref_vars, ref_m47]
  ring!
open private
  normPair_star
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly
open private
  ref_lhs ref_q0 ref_q1 ref_q10 ref_q100 ref_q101 ref_q102
  ref_q103 ref_q104 ref_q105 ref_q106 ref_q107 ref_q108 ref_q109
  ref_q11 ref_q110 ref_q111 ref_q112 ref_q113 ref_q114 ref_q115
  ref_q116 ref_q117 ref_q118 ref_q119 ref_q12 ref_q120 ref_q121
  ref_q122 ref_q123 ref_q124 ref_q125 ref_q126 ref_q127 ref_q128
  ref_q129 ref_q13 ref_q130 ref_q131 ref_q132 ref_q133 ref_q134
  ref_q135 ref_q136 ref_q137 ref_q138 ref_q139 ref_q14 ref_q140
  ref_q141 ref_q142 ref_q143 ref_q144 ref_q145 ref_q146 ref_q147
  ref_q148 ref_q149 ref_q15 ref_q150 ref_q151 ref_q152 ref_q153
  ref_q154 ref_q155 ref_q156 ref_q157 ref_q158 ref_q159 ref_q16
  ref_q160 ref_q161 ref_q162 ref_q163 ref_q164 ref_q165 ref_q166
  ref_q167 ref_q168 ref_q169 ref_q17 ref_q170 ref_q171 ref_q172
  ref_q173 ref_q174 ref_q175 ref_q176 ref_q177 ref_q178 ref_q179
  ref_q18 ref_q180 ref_q181 ref_q182 ref_q183 ref_q184 ref_q185
  ref_q186 ref_q187 ref_q188 ref_q189 ref_q19 ref_q190 ref_q191
  ref_q192 ref_q193 ref_q194 ref_q195 ref_q196 ref_q197 ref_q198
  ref_q199 ref_q2 ref_q20 ref_q200 ref_q201 ref_q202 ref_q203
  ref_q204 ref_q205 ref_q206 ref_q207 ref_q208 ref_q209 ref_q21
  ref_q210 ref_q211 ref_q212 ref_q213 ref_q214 ref_q215 ref_q216
  ref_q217 ref_q218 ref_q219 ref_q22 ref_q220 ref_q221 ref_q222
  ref_q223 ref_q224 ref_q225 ref_q226 ref_q227 ref_q228 ref_q229
  ref_q23 ref_q230 ref_q231 ref_q232 ref_q233 ref_q234 ref_q235
  ref_q236 ref_q237 ref_q238 ref_q239 ref_q24 ref_q240 ref_q241
  ref_q242 ref_q243 ref_q244 ref_q245 ref_q246 ref_q247 ref_q248
  ref_q249 ref_q25 ref_q250 ref_q251 ref_q252 ref_q253 ref_q254
  ref_q255 ref_q256 ref_q257 ref_q258 ref_q259 ref_q26 ref_q260
  ref_q261 ref_q262 ref_q263 ref_q264 ref_q265 ref_q266 ref_q267
  ref_q268 ref_q269 ref_q27 ref_q270 ref_q271 ref_q28 ref_q29
  ref_q3 ref_q30 ref_q31 ref_q32 ref_q33 ref_q34 ref_q35
  ref_q36 ref_q37 ref_q38 ref_q39 ref_q4 ref_q40 ref_q41
  ref_q42 ref_q43 ref_q44 ref_q45 ref_q46 ref_q47 ref_q48
  ref_q49 ref_q5 ref_q50 ref_q51 ref_q52 ref_q53 ref_q54
  ref_q55 ref_q56 ref_q57 ref_q58 ref_q59 ref_q6 ref_q60
  ref_q61 ref_q62 ref_q63 ref_q64 ref_q65 ref_q66 ref_q67
  ref_q68 ref_q69 ref_q7 ref_q70 ref_q71 ref_q72 ref_q73
  ref_q74 ref_q75 ref_q76 ref_q77 ref_q78 ref_q79 ref_q8
  ref_q80 ref_q81 ref_q82 ref_q83 ref_q84 ref_q85 ref_q86
  ref_q87 ref_q88 ref_q89 ref_q9 ref_q90 ref_q91 ref_q92
  ref_q93 ref_q94 ref_q95 ref_q96 ref_q97 ref_q98 ref_q99
  ref_rawBlock0 ref_rawBlock1 ref_rawBlock10 ref_rawBlock11 ref_rawBlock12 ref_rawBlock13 ref_rawBlock14
  ref_rawBlock15 ref_rawBlock16 ref_rawBlock2 ref_rawBlock3 ref_rawBlock4 ref_rawBlock5 ref_rawBlock6
  ref_rawBlock7 ref_rawBlock8 ref_rawBlock9 ref_rhs
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open private
  ref_eval ref_eval_add ref_eval_mul ref_eval_scale ref_mul ref_scale ref_swap
  from D5.S3.Quantum.Entanglement.HiguchiSudbery.SparseReflection
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private lemma ref_eval_square_nonneg /- proof_shape: content; escape_witness: SparseReflection.ref_eval_mul; consumer: ReflectionEvaluation.ref_block_nonneg0 -/ (z : Fin 16 → ℂ) (w : ℤ) (p : (List (List ℕ × ℤ))) (hw : 0 ≤ w) :
    0 ≤ (ref_eval (ref_vars z) (ref_scale w (ref_mul p (ref_swap p)))).re := by
  rw [ref_eval_scale, ref_eval_mul, ref_eval_swap_vars, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (by exact_mod_cast hw) (Complex.normSq_nonneg _)
private lemma ref_eval_lhs /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.e3_bound_of_certificate -/ (z : Fin 16 → ℂ) :
    ref_eval (ref_vars z) ref_lhs = ((62720 * squaredAmplitudeTotal 15 z ^ 3 - 451584 * totalMinorE3 z : ℝ) : ℂ) := by
  simp only [ref_lhs, ref_eval_add, ref_eval_scale, ref_eval_mul, ref_eval_swap_vars, ref_eval_normPoly, ref_eval_m0, ref_eval_m1, ref_eval_m2, ref_eval_m3, ref_eval_m4, ref_eval_m5, ref_eval_m6, ref_eval_m7, ref_eval_m8, ref_eval_m9, ref_eval_m10, ref_eval_m11, ref_eval_m12, ref_eval_m13, ref_eval_m14, ref_eval_m15, ref_eval_m16, ref_eval_m17, ref_eval_m18, ref_eval_m19, ref_eval_m20, ref_eval_m21, ref_eval_m22, ref_eval_m23, ref_eval_m24, ref_eval_m25, ref_eval_m26, ref_eval_m27, ref_eval_m28, ref_eval_m29, ref_eval_m30, ref_eval_m31, ref_eval_m32, ref_eval_m33, ref_eval_m34, ref_eval_m35, ref_eval_m36, ref_eval_m37, ref_eval_m38, ref_eval_m39, ref_eval_m40, ref_eval_m41, ref_eval_m42, ref_eval_m43, ref_eval_m44, ref_eval_m45, ref_eval_m46, ref_eval_m47]
  rw [normPair_star]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  simp only [Complex.star_def, Complex.mul_conj]
  norm_num [totalMinorE3, Fin.sum_univ_succ, Complex.ofReal_add]
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  ring
private lemma ref_block_nonneg0 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock0).re := by
  simp only [ref_rawBlock0, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q0 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q1 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q2 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q3 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q4 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q5 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q6 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q7 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q8 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q9 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q10 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q11 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q12 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q13 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q14 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q15 (by norm_num))))))
private lemma ref_block_nonneg1 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock1).re := by
  simp only [ref_rawBlock1, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q16 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q17 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q18 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q19 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q20 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q21 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q22 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q23 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q24 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q25 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q26 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q27 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q28 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q29 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q30 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q31 (by norm_num))))))
private lemma ref_block_nonneg2 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock2).re := by
  simp only [ref_rawBlock2, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q32 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q33 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q34 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q35 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q36 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q37 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q38 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q39 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q40 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q41 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q42 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q43 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q44 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q45 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q46 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q47 (by norm_num))))))
private lemma ref_block_nonneg3 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock3).re := by
  simp only [ref_rawBlock3, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q48 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q49 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q50 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q51 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q52 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q53 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q54 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q55 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q56 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q57 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q58 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q59 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q60 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q61 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q62 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q63 (by norm_num))))))
private lemma ref_block_nonneg4 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock4).re := by
  simp only [ref_rawBlock4, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q64 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q65 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q66 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q67 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q68 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q69 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q70 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q71 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q72 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q73 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q74 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q75 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q76 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q77 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q78 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q79 (by norm_num))))))
private lemma ref_block_nonneg5 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock5).re := by
  simp only [ref_rawBlock5, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q80 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q81 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q82 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q83 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q84 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q85 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q86 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q87 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q88 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q89 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q90 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q91 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q92 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q93 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q94 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q95 (by norm_num))))))
private lemma ref_block_nonneg6 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock6).re := by
  simp only [ref_rawBlock6, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q96 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q97 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q98 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q99 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q100 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q101 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q102 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q103 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q104 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q105 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q106 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q107 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q108 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q109 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q110 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q111 (by norm_num))))))
private lemma ref_block_nonneg7 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock7).re := by
  simp only [ref_rawBlock7, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q112 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q113 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q114 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q115 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q116 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q117 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q118 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q119 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q120 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q121 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q122 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q123 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q124 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q125 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q126 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q127 (by norm_num))))))
private lemma ref_block_nonneg8 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock8).re := by
  simp only [ref_rawBlock8, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q128 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q129 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q130 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q131 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q132 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q133 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q134 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q135 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q136 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q137 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q138 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q139 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q140 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q141 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q142 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q143 (by norm_num))))))
private lemma ref_block_nonneg9 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock9).re := by
  simp only [ref_rawBlock9, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q144 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q145 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q146 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q147 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q148 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q149 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q150 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q151 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q152 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q153 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q154 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q155 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q156 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q157 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q158 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q159 (by norm_num))))))
private lemma ref_block_nonneg10 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock10).re := by
  simp only [ref_rawBlock10, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q160 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q161 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q162 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q163 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q164 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q165 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q166 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q167 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q168 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q169 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q170 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q171 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q172 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q173 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q174 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q175 (by norm_num))))))
private lemma ref_block_nonneg11 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock11).re := by
  simp only [ref_rawBlock11, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q176 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q177 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q178 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q179 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q180 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q181 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q182 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q183 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q184 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q185 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q186 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q187 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q188 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q189 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q190 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q191 (by norm_num))))))
private lemma ref_block_nonneg12 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock12).re := by
  simp only [ref_rawBlock12, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q192 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q193 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q194 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q195 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q196 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q197 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q198 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q199 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q200 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q201 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q202 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q203 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q204 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q205 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q206 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q207 (by norm_num))))))
private lemma ref_block_nonneg13 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock13).re := by
  simp only [ref_rawBlock13, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q208 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q209 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q210 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q211 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q212 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q213 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q214 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q215 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q216 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q217 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q218 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q219 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q220 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q221 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q222 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q223 (by norm_num))))))
private lemma ref_block_nonneg14 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock14).re := by
  simp only [ref_rawBlock14, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q224 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q225 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q226 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q227 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q228 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q229 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q230 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q231 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q232 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q233 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q234 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q235 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q236 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q237 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q238 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q239 (by norm_num))))))
private lemma ref_block_nonneg15 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock15).re := by
  simp only [ref_rawBlock15, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q240 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q241 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q242 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q243 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q244 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q245 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q246 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q247 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 3 ref_q248 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q249 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 1 ref_q250 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q251 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 1 ref_q252 (by norm_num)) (ref_eval_square_nonneg z 124 ref_q253 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 3 ref_q254 (by norm_num)) (ref_eval_square_nonneg z 372 ref_q255 (by norm_num))))))
private lemma ref_block_nonneg16 /- proof_shape: bind-only; consumer: ReflectionEvaluation.ref_eval_rhs_nonneg -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rawBlock16).re := by
  simp only [ref_rawBlock16, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 6272 ref_q256 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q257 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 6272 ref_q258 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q259 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 6272 ref_q260 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q261 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 6272 ref_q262 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q263 (by norm_num))))) (add_nonneg (add_nonneg (add_nonneg (ref_eval_square_nonneg z 6272 ref_q264 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q265 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 6272 ref_q266 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q267 (by norm_num)))) (add_nonneg (add_nonneg (ref_eval_square_nonneg z 6272 ref_q268 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q269 (by norm_num))) (add_nonneg (ref_eval_square_nonneg z 6272 ref_q270 (by norm_num)) (ref_eval_square_nonneg z 6272 ref_q271 (by norm_num))))))
private lemma ref_eval_rhs_nonneg /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.e3_bound_of_certificate -/ (z : Fin 16 → ℂ) : 0 ≤ (ref_eval (ref_vars z) ref_rhs).re := by
  simp only [ref_rhs, ref_eval_add, Complex.add_re]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (ref_block_nonneg0 z) (ref_block_nonneg1 z)) (add_nonneg (ref_block_nonneg2 z) (ref_block_nonneg3 z))) (add_nonneg (add_nonneg (ref_block_nonneg4 z) (ref_block_nonneg5 z)) (add_nonneg (ref_block_nonneg6 z) (ref_block_nonneg7 z)))) (add_nonneg (add_nonneg (add_nonneg (ref_block_nonneg8 z) (ref_block_nonneg9 z)) (add_nonneg (ref_block_nonneg10 z) (ref_block_nonneg11 z))) (add_nonneg (add_nonneg (ref_block_nonneg12 z) (ref_block_nonneg13 z)) (add_nonneg (ref_block_nonneg14 z) (add_nonneg (ref_block_nonneg15 z) (ref_block_nonneg16 z))))))

end D5.S3.Quantum.Entanglement.HiguchiSudbery
