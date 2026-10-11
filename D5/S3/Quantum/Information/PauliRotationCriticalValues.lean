/- GID: D5/S3/Quantum/Information/PauliRotationCriticalValues
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/PauliRotationCriticalValues
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/PauliRotationCriticalValues.claim; result=D5/S3/Quantum/Information/PauliRotationCriticalValues.result; claim=D5/S3/Quantum/Information/PauliRotationCriticalValues.claim
   digest: Two-qubit Pauli rotation circuits and their critical-value Hausdorff dimension. -/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

namespace D5.S3.Quantum.Information.PauliRotationCriticalValues

open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli wordOp)

abbrev BasisState := Fin 2 → Fin 2
abbrev Mat := Matrix BasisState BasisState ℂ
abbrev Param := Fin 15 → ℝ
abbrev NonIdentityPauli :=
  {p : Fin 2 → Pauli // p ≠ (fun _ => Pauli.I)}

noncomputable def rotation (p : NonIdentityPauli) (a : ℝ) : Mat :=
  Real.cos (a / 2) • (1 : Mat) -
    Real.sin (a / 2) • (Complex.I • wordOp p.val)

noncomputable def circuit (P : Fin 15 → NonIdentityPauli)
    (α : Param) : Mat :=
  (List.ofFn (fun j : Fin 15 => rotation (P j) (α j))).prod

noncomputable def derivativeRank (P : Fin 15 → NonIdentityPauli)
    (α : Param) : ℕ :=
  Module.finrank ℝ
    (LinearMap.range ((fderiv ℝ (circuit P) α).toLinearMap))

def critical (P : Fin 15 → NonIdentityPauli) : Set Param :=
  {α | derivativeRank P α < 15}

def claim : Prop :=
  ∀ P : Fin 15 → NonIdentityPauli,
    (∀ᵐ α ∂(volume : Measure Param), derivativeRank P α = 15) →
      dimH (circuit P '' critical P) ≤ (13 : ℝ≥0∞)

open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (pauliMatrix tensorOp tensor_mul)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)

private theorem pauli_square (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
  obtain ⟨_, _, _, hx, hz⟩ := qubit_weyl_star
  cases p
  · exact mul_one _
  · exact (pow_two _).symm.trans hx
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, mul_apply]
  · exact (pow_two _).symm.trans hz

private theorem pauli_star (p : Pauli) : star (pauliMatrix p) = pauliMatrix p := by
  obtain ⟨_, hx, hz, _, _⟩ := qubit_weyl_star
  cases p
  · exact star_one _
  · exact hx
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, qubitX, qubitZ, star_apply]
  · exact hz

private theorem tensor_identity : tensorOp (fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext x y
  simp only [tensorOp, of_apply, one_apply]
  by_cases h : x = y
  · subst y; simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem word_square (p : Fin 2 → Pauli) : wordOp p * wordOp p = (1 : Mat) := by
  unfold wordOp
  rw [tensor_mul]
  simp_rw [pauli_square]
  exact tensor_identity

private theorem word_star (p : Fin 2 → Pauli) : star (wordOp p) = wordOp p := by
  ext x y
  simp only [wordOp, tensorOp, star_apply, of_apply, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (pauli_star (p i)) (x i)) (y i)

private theorem pauli_trace_mul (p q : Pauli) :
    trace (pauliMatrix p * pauliMatrix q) = if p = q then (2 : ℂ) else 0 := by
  cases p <;> cases q <;>
    simp [pauliMatrix, qubitX, qubitZ, trace, Fin.sum_univ_two] <;> norm_num

private theorem word_trace_mul (p q : Fin 2 → Pauli) :
    trace (wordOp p * wordOp q) = if p = q then (4 : ℂ) else 0 := by
  unfold wordOp
  rw [tensor_mul]
  change (∑ x : BasisState, ∏ i, (pauliMatrix (p i) * pauliMatrix (q i)) (x i) (x i)) = _
  rw [← Fintype.prod_sum (fun i k => (pauliMatrix (p i) * pauliMatrix (q i)) k k)]
  change (∏ i, trace (pauliMatrix (p i) * pauliMatrix (q i))) = _
  simp_rw [pauli_trace_mul]
  by_cases h : p = q
  · subst q; norm_num
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private def labels : Fin 15 → Fin 2 → Pauli :=
  ![![.I,.X], ![.I,.Y], ![.I,.Z], ![.X,.I], ![.X,.X], ![.X,.Y], ![.X,.Z],
    ![.Y,.I], ![.Y,.X], ![.Y,.Y], ![.Y,.Z], ![.Z,.I], ![.Z,.X], ![.Z,.Y], ![.Z,.Z]]

private theorem labels_injective : Function.Injective labels := by decide

private noncomputable def E : Param →L[ℝ] Mat :=
  ∑ i : Fin 15, (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).smulRight (wordOp (labels i))

private noncomputable def rho : Mat →L[ℝ] Param :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M i => (trace (wordOp (labels i) * M)).re / 4
    map_add' := by
      intro A B; funext i
      simp [mul_add, trace_add, add_div]
    map_smul' := by
      intro c A; funext i
      simp [trace_smul, smul_eq_mul, Complex.mul_re, mul_div_assoc] }

private theorem rho_E (x : Param) : rho (E x) = x := by
  ext i
  change (trace (wordOp (labels i) * ∑ j, x j • wordOp (labels j))).re / 4 = x i
  simp only [Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul]
  simp_rw [word_trace_mul, labels_injective.eq_iff]
  simp

private theorem E_injective : Function.Injective E :=
  Function.LeftInverse.injective rho_E

private theorem sum_states {A : Type*} [AddCommMonoid A] (f : BasisState → A) :
    ∑ x, f x = f ![0,0] + f ![0,1] + f ![1,0] + f ![1,1] := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, finTwoArrowEquiv, add_assoc]

-- The finite reconstruction expands sixteen matrix entries in the fifteen Pauli coordinates.
set_option maxHeartbeats 2000000 in
private theorem pauli_expansion (M : Mat) :
    (∑ i, (trace (wordOp (labels i) * M) / 4) • wordOp (labels i)) +
      (trace M / 4) • (1 : Mat) = M := by
  ext x y
  obtain ⟨⟨a,b⟩, rfl⟩ := (finTwoArrowEquiv (Fin 2)).symm.surjective x
  obtain ⟨⟨c,d⟩, rfl⟩ := (finTwoArrowEquiv (Fin 2)).symm.surjective y
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [finTwoArrowEquiv, labels, wordOp, tensorOp, pauliMatrix, qubitX, qubitZ, trace, diag,
      Matrix.mul_apply, Matrix.one_apply, sum_states, Fin.prod_univ_two, smul_eq_mul,
      Fin.sum_univ_succ] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private theorem E_rho (M : Mat) (hs : star M = M) (ht : trace M = 0) : E (rho M) = M := by
  have hr (i : Fin 15) : ((trace (wordOp (labels i) * M)).re : ℂ) =
      trace (wordOp (labels i) * M) := by
    apply Complex.conj_eq_iff_re.mp
    change star (trace (wordOp (labels i) * M)) = _
    rw [← trace_conjTranspose, conjTranspose_mul]
    change trace (star M * star (wordOp (labels i))) = _
    rw [hs, word_star, trace_mul_comm]
  apply Eq.trans ?_ (by simpa [ht] using pauli_expansion M)
  change (∑ i, rho M i • wordOp (labels i)) = _
  apply Finset.sum_congr rfl
  intro i _
  change ((trace (wordOp (labels i) * M)).re / 4) • _ = _
  ext x y
  change (((trace (wordOp (labels i) * M)).re / 4 : ℝ) : ℂ) * _ = _
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, hr]
  rfl

end D5.S3.Quantum.Information.PauliRotationCriticalValues
