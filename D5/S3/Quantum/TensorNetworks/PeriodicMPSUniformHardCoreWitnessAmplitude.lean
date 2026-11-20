/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCounts]
   utility: none
   digest: The rank-one trace product around a cycle realizes the independent-set indicator with two explicit bond-two cores. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCounts

/-! The cyclic independent-set indicator is the literal trace tensor of the witness cores. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreWitnessAmplitude

open PeriodicMPSParentIntersection (Word wordMatrix wordMatrix_snoc)
open PeriodicMPSUniformDeterminantPencil (witnessCore)
open PeriodicMPSUniformHardCoreCounts (Independent occupied_independent_iff)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped BigOperators Matrix

noncomputable section

/-- Along the ordered path, the neighboring dot products multiply the outer
product of the first left vector and the last right vector. -/
private theorem wordMatrix_rankOne (u v : Fin 2 → Fin 2 → ℂ) (n : ℕ)
    (w : Word (n + 1)) :
    wordMatrix (fun a => Matrix.vecMulVec (u a) (v a)) w =
      (∏ i : Fin n, v (w i.castSucc) ⬝ᵥ u (w i.succ)) •
        Matrix.vecMulVec (u (w 0)) (v (w (Fin.last n))) := by
  induction n with
  | zero =>
    conv_lhs => rw [← Fin.snoc_init_self w, wordMatrix_snoc]
    have hlast : Fin.last 0 = 0 := rfl
    simp [wordMatrix, hlast]
  | succ n ih =>
    conv_lhs => rw [← Fin.snoc_init_self w, wordMatrix_snoc, ih]
    rw [Matrix.smul_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, smul_smul,
      Fin.prod_univ_castSucc]
    rfl

/-- Taking the trace inserts the last-to-first dot product in the ordered word. -/
theorem traceWord_rankOne (u v : Fin 2 → Fin 2 → ℂ) (n : ℕ) (w : Word (n + 1)) :
    traceWord 2 2 (n + 1) (fun a => Matrix.vecMulVec (u a) (v a)) w =
      ∏ i : Fin (n + 1), v (w i) ⬝ᵥ u (w (finRotate (n + 1) i)) := by
  change (wordMatrix (fun a => Matrix.vecMulVec (u a) (v a)) w).trace = _
  rw [wordMatrix_rankOne, Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul,
    Fin.prod_univ_castSucc, finRotate_last, dotProduct_comm (u (w 0))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hi : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [hi]

private def witnessLeft : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![1, -1]]

private def witnessRight : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![1, 1]]

private theorem witnessCore_eq_vecMulVec (a : Fin 2) :
    witnessCore a = Matrix.vecMulVec (witnessLeft a) (witnessRight a) := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [witnessCore, witnessLeft, witnessRight, Matrix.vecMulVec_apply]

private theorem witness_dotProduct (a b : Fin 2) :
    witnessRight a ⬝ᵥ witnessLeft b = if a = 1 ∧ b = 1 then 0 else 1 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [witnessLeft, witnessRight, dotProduct, Fin.sum_univ_two]

/-- Every forward cyclic edge contributes one, except an occupied pair contributes zero. -/
theorem traceWord_witnessCore_eq_prod {n : ℕ} (hn : 0 < n) (w : Word n) :
    traceWord 2 2 n witnessCore w =
      ∏ i : Fin n, if w i = 1 ∧ w (finRotate n i) = 1 then 0 else 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [funext witnessCore_eq_vecMulVec, traceWord_rankOne]
  simp only [witness_dotProduct]

/-- At every length at least seven, the witness amplitude is exactly the
indicator that the occupied sites form an independent set of the cycle graph. -/
theorem traceWord_witnessCore_eq_indicator {n : ℕ} (hn : 7 ≤ n) (w : Word n) :
    traceWord 2 2 n witnessCore w =
      if Independent (Finset.univ.filter fun i => w i = 1) then 1 else 0 := by
  classical
  rw [traceWord_witnessCore_eq_prod (by omega)]
  by_cases h : Independent (Finset.univ.filter fun i => w i = 1)
  · rw [ite_eq_left h]
    have hNoAdjacent := (occupied_independent_iff hn w).mp h
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_right (fun hi => hNoAdjacent i hi.1 hi.2)
  · rw [ite_eq_right h]
    have hAdjacent : ¬ ∀ i, w i = 1 → w (finRotate n i) ≠ 1 :=
      fun hNoAdjacent => h ((occupied_independent_iff hn w).mpr hNoAdjacent)
    push Not at hAdjacent
    obtain ⟨i, hi, hj⟩ := hAdjacent
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_left ⟨hi, hj⟩)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreWitnessAmplitude
