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

set_option maxHeartbeats 2000000 in
-- The finite reconstruction expands sixteen matrix entries in the fifteen Pauli coordinates.
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

private theorem rotation_complex (p : NonIdentityPauli) (a : ℝ) :
    rotation p a = (Real.cos (a / 2) : ℂ) • (1 : Mat) -
      ((Real.sin (a / 2) : ℂ) * Complex.I) • wordOp p.val := by
  ext x y
  simp [rotation, smul_eq_mul, Complex.real_smul, mul_assoc]

private theorem rotation_unitary (p : NonIdentityPauli) (a : ℝ) :
    rotation p a ∈ unitary Mat := by
  have hc : (Real.cos (a / 2) : ℂ) ^ 2 + (Real.sin (a / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq (a / 2)] :
      Real.cos (a / 2) ^ 2 + Real.sin (a / 2) ^ 2 = 1)
  rw [Unitary.mem_iff, rotation_complex]
  simp only [star_sub, star_smul, star_one, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, word_star]
  constructor <;>
    simp only [mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      word_square, smul_smul] <;>
    calc _ = ((Real.cos (a / 2) : ℂ) ^ 2 + (Real.sin (a / 2) : ℂ) ^ 2) • (1 : Mat) := by
          match_scalars
          all_goals ring_nf
          all_goals simp only [Complex.I_sq]
          all_goals ring
         _ = 1 := by rw [hc, one_smul]

private noncomputable def listCircuit (P : Fin 15 → NonIdentityPauli)
    (l : List (Fin 15)) (α : Param) : Mat :=
  (l.map (fun j => rotation (P j) (α j))).prod

private theorem list_unitary (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15)) (α : Param) :
    listCircuit P l α ∈ unitary Mat := by
  apply (unitary Mat).list_prod_mem
  intro M hM
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hM
  exact rotation_unitary (P j) (α j)

private noncomputable def prefixOp (P : Fin 15 → NonIdentityPauli) (α : Param) (n : ℕ) : Mat :=
  listCircuit P ((List.finRange 15).take n) α

private theorem prefix_unitary (P : Fin 15 → NonIdentityPauli) (α : Param) (n : ℕ) :
    prefixOp P α n ∈ unitary Mat := by
  exact list_unitary P ((List.finRange 15).take n) α

private theorem circuit_eq_list (P : Fin 15 → NonIdentityPauli) :
    circuit P = listCircuit P (List.finRange 15) := by
  funext α
  unfold circuit listCircuit
  rw [List.ofFn_eq_map]

private theorem circuit_unitary (P : Fin 15 → NonIdentityPauli) (α : Param) :
    circuit P α ∈ unitary Mat := by
  rw [circuit_eq_list]
  exact list_unitary P (List.finRange 15) α

private noncomputable def gateD (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    Param →L[ℝ] Mat :=
  (ContinuousLinearMap.proj j : Param →L[ℝ] ℝ).smulRight
    ((-Complex.I / 2) • (wordOp (P j).val * rotation (P j) (α j)))

private theorem gate_deriv (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    HasStrictFDerivAt (fun β : Param => rotation (P j) (β j)) (gateD P α j) α := by
  let d := (1 / 2 : ℝ) • (ContinuousLinearMap.proj j : Param →L[ℝ] ℝ)
  have hd : HasStrictFDerivAt (fun β : Param => β j / 2) d α := by
    simpa [d, div_eq_mul_inv, mul_comm] using
      (ContinuousLinearMap.proj j : Param →L[ℝ] ℝ).hasStrictFDerivAt.const_mul (1 / 2)
  apply (hd.cos.smul_const (1 : Mat) |>.sub
    (hd.sin.smul_const (Complex.I • wordOp (P j).val))).congr_fderiv
  ext1 h
  simp only [gateD, d, _root_.sub_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, ContinuousLinearMap.proj_apply, rotation_complex, mul_sub, Matrix.mul_smul,
    mul_one, word_square, smul_smul]
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

private theorem list_split (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15))
    (α : Param) (i : Fin l.length) :
    listCircuit P (l.take i) α * rotation (P l[i]) (α l[i]) *
      listCircuit P (l.drop (i.val + 1)) α = listCircuit P l α := by
  have hi : i.val < (l.map (fun j => rotation (P j) (α j))).length := by simp
  have hh := List.prod_take_mul_prod_drop (l.map (fun j => rotation (P j) (α j))) (i.val + 1)
  rw [List.prod_take_succ _ _ hi] at hh
  simpa [listCircuit, List.map_take, List.map_drop] using hh

private noncomputable def listD (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15))
    (α : Param) : Param →L[ℝ] Mat :=
  ∑ i : Fin l.length, (ContinuousLinearMap.proj l[i] : Param →L[ℝ] ℝ).smulRight
    ((-Complex.I / 2) • (listCircuit P (l.take i) α * wordOp (P l[i]).val *
      star (listCircuit P (l.take i) α) * listCircuit P l α))

private theorem list_deriv (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15)) (α : Param) :
    HasStrictFDerivAt (listCircuit P l) (listD P l α) α := by
  apply (HasStrictFDerivAt.list_prod' (l := l) (fun j _ => gate_deriv P α j)).congr_fderiv
  ext1 h
  simp only [listD, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [_root_.smul_apply, op_smul_eq_mul, smul_eq_mul, gateD,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  change listCircuit P (l.take i) α *
      ((h l[i] • ((-Complex.I / 2) • (wordOp (P l[i]).val * rotation (P l[i]) (α l[i])))) *
      listCircuit P (l.drop (i.val + 1)) α) = _
  rw [← list_split P l α i]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
  rw [← mul_assoc (star (listCircuit P (l.take i) α)) (listCircuit P (l.take i) α),
    Unitary.star_mul_self_of_mem (list_unitary P (l.take i) α), one_mul]

private theorem circuit_strict (P : Fin 15 → NonIdentityPauli) (α : Param) :
    HasStrictFDerivAt (circuit P) (listD P (List.finRange 15) α) α := by
  rw [circuit_eq_list]
  exact list_deriv P (List.finRange 15) α

private noncomputable def H (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) : Mat :=
  prefixOp P α j.val * wordOp (P j).val * star (prefixOp P α j.val)

private noncomputable def J_H (P : Fin 15 → NonIdentityPauli) (α : Param) :
    Fin 15 → Fin 15 → ℝ := fun i j => rho (H P α j) i

private theorem H_star (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    star (H P α j) = H P α j := by
  simp only [H, star_mul, star_star, word_star, mul_assoc]

private theorem H_trace (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    trace (H P α j) = 0 := by
  have hI : wordOp (fun _ : Fin 2 => Pauli.I) = (1 : Mat) := tensor_identity
  have hz : trace (wordOp (P j).val) = 0 := by
    simpa only [hI, mul_one, if_neg (P j).property] using
      word_trace_mul (P j).val (fun _ => Pauli.I)
  rw [H, trace_mul_cycle, Unitary.star_mul_self_of_mem (prefix_unitary P α j.val), one_mul, hz]

private theorem E_J_mulVec (P : Fin 15 → NonIdentityPauli) (α h : Param) :
    E ((J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h) = ∑ j, h j • H P α j := by
  have hv : (J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h = ∑ j, h j • rho (H P α j) := by
    ext i
    simp [J_H, Matrix.mulVec, dotProduct, mul_comm]
  rw [hv, map_sum]
  simp only [map_smul, E_rho _ (H_star P α _) (H_trace P α _)]

private theorem circuit_fderiv (P : Fin 15 → NonIdentityPauli) (α h : Param) :
    fderiv ℝ (circuit P) α h = (-Complex.I / 2) •
      (E ((J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h) * circuit P α) := by
  rw [(circuit_strict P α).hasFDerivAt.fderiv, E_J_mulVec]
  simp only [listD, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  change (∑ j, h j • ((-Complex.I / 2) • (H P α j * circuit P α))) = _
  simp_rw [smul_comm (h _) (-Complex.I / 2), ← Matrix.smul_mul]
  rw [← Finset.sum_mul, ← Finset.smul_sum]

private theorem circuit_ker (P : Fin 15 → NonIdentityPauli) (α : Param) :
    LinearMap.ker (fderiv ℝ (circuit P) α).toLinearMap =
      LinearMap.ker (Matrix.mulVecLin (J_H P α)) := by
  ext h
  change fderiv ℝ (circuit P) α h = 0 ↔ (J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h = 0
  rw [circuit_fderiv]
  constructor
  · intro hh
    have hz := congrArg (fun M : Mat => M * star (circuit P α)) hh
    simp only [Matrix.smul_mul, mul_assoc,
      Unitary.mul_star_self_of_mem (circuit_unitary P α), mul_one, zero_mul] at hz
    have hc : (-Complex.I / 2 : ℂ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num)
    exact E_injective (by simpa using (smul_eq_zero.mp hz).resolve_left hc)
  · intro hh; simp [hh]

private theorem derivative_rank (P : Fin 15 → NonIdentityPauli) (α : Param) :
    derivativeRank P α = Matrix.rank (J_H P α) := by
  have hf := (fderiv ℝ (circuit P) α).toLinearMap.finrank_range_add_finrank_ker
  have hj := (Matrix.mulVecLin (J_H P α)).finrank_range_add_finrank_ker
  rw [circuit_ker] at hf
  exact Nat.add_right_cancel (hf.trans hj.symm)

private theorem critical_eq_det_zero (P : Fin 15 → NonIdentityPauli) :
    critical P = {α | Matrix.det (J_H P α) = 0} := by
  ext α
  change derivativeRank P α < 15 ↔ _
  rw [derivative_rank]
  constructor
  · intro hh
    by_contra hd
    have hr := Matrix.rank_of_det_ne_zero hd
    simp only [Fintype.card_fin] at hr
    omega
  · intro hd
    obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have hk : LinearMap.ker (Matrix.mulVecLin (J_H P α)) ≠ ⊥ := by
      intro he
      exact hv (by simpa only [he, Submodule.mem_bot] using
        (show v ∈ LinearMap.ker (Matrix.mulVecLin (J_H P α)) from hz))
    have hp := Submodule.one_le_finrank_iff.mpr hk
    have hr := (Matrix.mulVecLin (J_H P α)).finrank_range_add_finrank_ker
    simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hr
    change Matrix.rank (J_H P α) + _ = 15 at hr
    omega

end D5.S3.Quantum.Information.PauliRotationCriticalValues
