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
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
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
    simp only [Module.finrank_pi, Fintype.card_fin] at hr
    change Matrix.rank (J_H P α) + _ = 15 at hr
    omega

private noncomputable def prefixG (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    Param →L[ℝ] Mat :=
  ∑ k : Fin j.val,
    (ContinuousLinearMap.proj (⟨k.val, lt_trans k.isLt j.isLt⟩ : Fin 15) : Param →L[ℝ] ℝ).smulRight
      (H P α ⟨k.val, lt_trans k.isLt j.isLt⟩)

private theorem prefix_strict (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    HasStrictFDerivAt (fun β => prefixOp P β j.val)
      (((ContinuousLinearMap.mul ℝ Mat).flip (prefixOp P α j.val)).comp
        ((-Complex.I / 2) • prefixG P α j)) α := by
  apply (list_deriv P ((List.finRange 15).take j.val) α).congr_fderiv
  ext1 h
  simp only [listD, prefixG,
    _root_.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', _root_.smul_apply, Matrix.smul_mul, Finset.sum_mul,
    Finset.smul_sum]
  apply Finset.sum_equiv (finCongr (by simp)) (by simp)
  intro k _
  have hk : k.val ≤ j.val := by have := k.isLt; simp only [List.length_take] at this; omega
  simp [List.take_take, Nat.min_eq_left hk, H, prefixOp, smul_comm (h _) (-Complex.I / 2)]

private noncomputable def H_D (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    Param →L[ℝ] Mat := (-Complex.I / 2) •
  (((ContinuousLinearMap.mul ℝ Mat).flip (H P α j)).comp (prefixG P α j) -
    ((ContinuousLinearMap.mul ℝ Mat) (H P α j)).comp (prefixG P α j))

private theorem H_deriv (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    HasStrictFDerivAt (fun β => H P β j) (H_D P α j) α := by
  have hp := prefix_strict P α j
  apply ((hp.mul_const' (wordOp (P j).val)).mul' hp.star).congr_fderiv
  ext1 h
  simp only [H_D, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearEquiv.coe_coe,
    starL'_apply, op_smul_eq_mul, smul_eq_mul, Matrix.smul_mul]
  have hg : star (prefixG P α j h) = prefixG P α j h := by
    simp [prefixG, star_sum, star_smul, H_star]
  have hc : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by simp; ring
  simp only [star_smul, star_mul, hg, hc, H, Matrix.mul_smul,
    mul_assoc, smul_sub, neg_smul, mul_neg]
  module

private noncomputable def J_D (P : Fin 15 → NonIdentityPauli) (α : Param) :
    Param →L[ℝ] (Fin 15 → Fin 15 → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).comp (rho.comp (H_D P α j))

private theorem J_strict (P : Fin 15 → NonIdentityPauli) (α : Param) :
    HasStrictFDerivAt (J_H P) (J_D P α) α := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  apply hasStrictFDerivAt_pi.mpr
  intro j
  exact (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).hasStrictFDerivAt.comp α
    (rho.hasStrictFDerivAt.comp α (H_deriv P α j))

private theorem J_fderiv (P : Fin 15 → NonIdentityPauli) (α h : Param) (i j : Fin 15) :
    fderiv ℝ (J_H P) α h i j = rho ((-Complex.I / 2) •
      (prefixG P α j h * H P α j - H P α j * prefixG P α j h)) i := by
  rw [(J_strict P α).hasFDerivAt.fderiv]
  rfl

private noncomputable def conjStep (p : NonIdentityPauli) (a : ℝ) (Q : Mat) : Mat :=
  ((1 + (Real.cos a : ℂ)) / 2) • Q +
    ((1 - (Real.cos a : ℂ)) / 2) • (wordOp p.val * Q * wordOp p.val) -
      (((Real.sin a : ℂ) / 2) * Complex.I) • (wordOp p.val * Q - Q * wordOp p.val)
private theorem rotation_conjugation (p : NonIdentityPauli) (a : ℝ) (Q : Mat) :
    rotation p a * Q * star (rotation p a) = conjStep p a Q := by
  have ha : 2 * (a / 2) = a := by ring
  have hc := Real.cos_two_mul (a / 2); rw [ha] at hc
  have hs := Real.cos_two_mul_eq_one_sub (a / 2); rw [ha] at hs
  have ht := Real.sin_two_mul (a / 2); rw [ha] at ht
  have hc' : (1 + (Real.cos a : ℂ)) / 2 = (Real.cos (a / 2) : ℂ) ^ 2 := by
    exact_mod_cast (by linarith : (1 + Real.cos a) / 2 = Real.cos (a / 2) ^ 2)
  have hs' : (1 - (Real.cos a : ℂ)) / 2 = (Real.sin (a / 2) : ℂ) ^ 2 := by
    exact_mod_cast (by linarith : (1 - Real.cos a) / 2 = Real.sin (a / 2) ^ 2)
  have ht' : (Real.sin a : ℂ) / 2 =
      (Real.sin (a / 2) : ℂ) * (Real.cos (a / 2) : ℂ) := by
    exact_mod_cast (by linarith : Real.sin a / 2 = Real.sin (a / 2) * Real.cos (a / 2))
  rw [conjStep, hc', hs', ht', rotation_complex]
  simp only [star_sub, star_smul, star_one, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, word_star, mul_sub, sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, smul_sub, mul_assoc]
  match_scalars <;> ring_nf
  all_goals simp [Complex.I_sq]
private theorem conjStep_comm (p : NonIdentityPauli) (a : ℝ) (Q : Mat)
    (hq : wordOp p.val * Q = Q * wordOp p.val) : conjStep p a Q = Q := by
  have hh : wordOp p.val * Q * wordOp p.val = Q := by
    rw [hq, mul_assoc, word_square, mul_one]
  rw [conjStep, hh, hq]
  simp only [sub_self, smul_zero, sub_zero]
  module
private theorem conjStep_anticomm (p : NonIdentityPauli) (a : ℝ) (Q : Mat)
    (hq : wordOp p.val * Q = -(Q * wordOp p.val)) :
    conjStep p a Q = (Real.cos a : ℂ) • Q -
      ((Real.sin a : ℂ) * Complex.I) • (wordOp p.val * Q) := by
  have hh : wordOp p.val * Q * wordOp p.val = -Q := by
    rw [hq, neg_mul, mul_assoc, word_square, mul_one]
  have hqp : Q * wordOp p.val = -(wordOp p.val * Q) := by rw [hq, neg_neg]
  simp only [conjStep, hh, hqp, smul_neg, sub_neg_eq_add, smul_add]
  module
private theorem list_conjugation (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15))
    (α : Param) (Q : Mat) : listCircuit P l α * Q * star (listCircuit P l α) =
      l.foldr (fun k M => conjStep (P k) (α k) M) Q := by
  induction l with
  | nil => simp [listCircuit]
  | cons k l ih =>
    rw [List.foldr_cons, ← rotation_conjugation, ← ih]
    simp only [listCircuit, List.map_cons, List.prod_cons, star_mul, mul_assoc]
private theorem J_recurrence (P : Fin 15 → NonIdentityPauli) (α : Param) (i j : Fin 15) :
    J_H P α i j = rho (((List.finRange 15).take j.val).foldr
      (fun k M => conjStep (P k) (α k) M) (wordOp (P j).val)) i := by
  simp only [J_H, H, prefixOp, list_conjugation]

-- Rational row and column coordinates; the exceptional parameter index is 12.
private abbrev RatMat := Matrix (Fin 15) (Fin 15) ℚ
private def certA : RatMat := Matrix.transpose
  ![![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0], ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,-1/2,1/2,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    ![1/4,1/4,0,0,0,0,-1/2,0,-1/4,1/4,0,1/2,0,0,0],
    ![1/4,1/4,0,0,0,0,1/2,0,-1/4,1/4,0,-1/2,0,0,0],
    ![1/4,1/4,0,0,0,0,1/2,0,1/4,-1/4,0,1/2,0,0,0],
    ![0,0,0,-1/2,0,0,0,1/2,0,0,0,0,-1/4,1/4,1/2],
    ![-1/4,1/4,1/2,0,-1/4,-1/4,0,0,1/4,1/4,0,0,0,0,0],
    ![0,0,0,1/2,0,0,0,1/2,0,0,0,0,-1/4,1/4,-1/2],
    ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,1]]
private def certL : RatMat :=
  ![![0,0,0,0,0,0,0,0,1,1,0,0,0,0,0], ![-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,1,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,-1/2,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,1/2,0,0,0,0,1,0,0], ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    ![0,0,0,0,0,0,0,0,-2,0,0,1,0,0,0], ![2,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],
    ![2,0,0,0,0,0,0,0,2,0,0,0,0,0,0], ![0,0,0,-1/2,0,0,0,1,0,0,0,0,0,0,1/2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,1/2,0,0,0,1,0,0,0,0,0,0,-1/2],
    ![0,0,0,1/2,0,0,0,0,0,0,0,0,0,0,1/2]]
private def certu : Fin 15 → ℚ := ![-1/2,-1/2,1/2,0,0,-1/2,1/2,0,1/2,1/2,0,0,1,0,0]
private def certz : Fin 15 → ℚ := ![-2,0,0,0,0,0,1,0,-2,0,0,1,0,0,0]
private def certe : Fin 15 → ℚ := Pi.single 12 1
private def certr : Fin 15 → ℚ := Pi.single 6 1
private def certD : RatMat := diagonal (fun i => if i = 12 then 0 else 1)
private def certN : RatMat := 1 + vecMulVec (certu - certe) certe
private def certNi : RatMat := 1 - vecMulVec (certu - certe) certe
private def certK : RatMat := certL + vecMulVec certe certz
private def certKi : RatMat := certA * certD + vecMulVec certr certe
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The kernel reduces five finite rational matrix identities.
private theorem rational_certificate :
    certA *ᵥ certu = 0 ∧ certz ᵥ* certA = 0 ∧
    certK * certKi = 1 ∧ certN * certNi = 1 ∧ certK * certA * certN = certD := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private noncomputable def ratReal : RatMat →+* Matrix (Fin 15) (Fin 15) ℝ :=
  (Rat.castHom ℝ).mapMatrix
private noncomputable def rowScale (i : Fin 15) : ℝ :=
  if i ∈ ({0,1,4,5,8,9,12,13} : Finset (Fin 15)) then Real.sqrt 2 else 1
private noncomputable def colScale (i : Fin 15) : ℝ :=
  if i ∈ ({0,1,2,3,4,14} : Finset (Fin 15)) then Real.sqrt 2 else 1
private noncomputable def R : Matrix (Fin 15) (Fin 15) ℝ := diagonal rowScale
private noncomputable def Ri : Matrix (Fin 15) (Fin 15) ℝ := diagonal (fun i => (rowScale i)⁻¹)
private noncomputable def S : Matrix (Fin 15) (Fin 15) ℝ := diagonal colScale
private noncomputable def Si : Matrix (Fin 15) (Fin 15) ℝ := diagonal (fun i => (colScale i)⁻¹)
private theorem scaling_inverse : Ri * R = 1 ∧ Si * S = 1 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  constructor
  · rw [Ri, R, diagonal_mul_diagonal]; apply diagonal_eq_one.mpr
    ext i; simp only [rowScale]; split_ifs <;> simp [hs]
  · rw [Si, S, diagonal_mul_diagonal]; apply diagonal_eq_one.mpr
    ext i; simp only [colScale]; split_ifs <;> simp [hs]
private noncomputable def B : Matrix (Fin 15) (Fin 15) ℝ := ratReal certK * Ri
private noncomputable def U : Matrix (Fin 15) (Fin 15) ℝ := S * ratReal certN
private noncomputable def D : Matrix (Fin 15) (Fin 15) ℝ := ratReal certD
private noncomputable def v : Param := S *ᵥ (fun i => (certu i : ℝ))
private theorem coordinate_inverse :
    B * (R * ratReal certKi) = 1 ∧ U * (ratReal certNi * Si) = 1 := by
  have hR := scaling_inverse.1
  have hS := scaling_inverse.2
  have hS' : S * Si = 1 := mul_eq_one_comm.mp hS
  constructor
  · simp only [B, mul_assoc, ← mul_assoc Ri R, hR, one_mul, ← map_mul,
      rational_certificate.2.2.1, map_one]
  · simp only [U, mul_assoc, ← mul_assoc (ratReal certN) (ratReal certNi),
      ← map_mul, rational_certificate.2.2.2.1, map_one, one_mul, hS']

private def pauliProd : Pauli → Pauli → Pauli
  | .I, q => q | p, .I => p
  | .X, .X => .I | .Y, .Y => .I | .Z, .Z => .I
  | .X, .Y => .Z | .Y, .X => .Z
  | .Y, .Z => .X | .Z, .Y => .X
  | .Z, .X => .Y | .X, .Z => .Y
private noncomputable def pauliPhase : Pauli → Pauli → ℂ
  | .X, .Y | .Y, .Z | .Z, .X => Complex.I
  | .Y, .X | .Z, .Y | .X, .Z => -Complex.I
  | _, _ => 1
private theorem pauli_product (p q : Pauli) :
    pauliMatrix p * pauliMatrix q = pauliPhase p q • pauliMatrix (pauliProd p q) := by
  cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix, qubitX, qubitZ, pauliProd, pauliPhase, mul_apply, smul_eq_mul]
private theorem word_product (p q : Fin 2 → Pauli) :
    wordOp p * wordOp q = (∏ i, pauliPhase (p i) (q i)) •
      wordOp ![pauliProd (p 0) (q 0), pauliProd (p 1) (q 1)] := by
  unfold wordOp; rw [tensor_mul]
  ext x y
  simp [tensorOp, pauli_product, Fin.prod_univ_two, smul_eq_mul]; ring
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (sgn anticomm)
private theorem pauli_commutation (p q : Pauli) :
    pauliMatrix p * pauliMatrix q = (sgn p q : ℂ) • (pauliMatrix q * pauliMatrix p) := by
  cases p <;> cases q <;> simp [pauli_product, sgn, anticomm,
    pauliProd, pauliPhase, smul_smul, smul_neg, neg_smul]
private theorem word_commutation (p q : Fin 2 → Pauli) :
    wordOp p * wordOp q = (∏ i, (sgn (p i) (q i) : ℂ)) • (wordOp q * wordOp p) := by
  unfold wordOp; rw [tensor_mul, tensor_mul]
  calc tensorOp (fun i => pauliMatrix (p i) * pauliMatrix (q i)) =
      tensorOp (fun i => (sgn (p i) (q i) : ℂ) • (pauliMatrix (q i) * pauliMatrix (p i))) :=
        congrArg tensorOp (funext fun i => pauli_commutation (p i) (q i))
       _ = _ := by ext x y; simp [tensorOp, Finset.prod_mul_distrib, smul_eq_mul]
private theorem conjStep_word (p : NonIdentityPauli) (a : ℝ) (q : Fin 2 → Pauli) :
    conjStep p a (wordOp q) =
      if sgn (p.val 0) (q 0) * sgn (p.val 1) (q 1) = -1 then
        (Real.cos a : ℂ) • wordOp q - ((Real.sin a : ℂ) * Complex.I *
          (∏ i, pauliPhase (p.val i) (q i))) • wordOp ![pauliProd (p.val 0) (q 0), pauliProd (p.val 1) (q 1)]
      else wordOp q := by
  have hh := word_commutation p.val q
  simp only [Fin.prod_univ_two, ← Int.cast_mul] at hh
  have hs : sgn (p.val 0) (q 0) * sgn (p.val 1) (q 1) = 1 ∨
      sgn (p.val 0) (q 0) * sgn (p.val 1) (q 1) = -1 := by
    unfold sgn; split_ifs <;> norm_num
  split_ifs with h
  · rw [h] at hh
    simpa [word_product, smul_smul, mul_assoc] using
      conjStep_anticomm p a (wordOp q) (by simpa using hh)
  · rw [hs.resolve_right h] at hh
    exact conjStep_comm p a (wordOp q) (by simpa using hh)
private theorem conjStep_add (p : NonIdentityPauli) (a : ℝ) (M N : Mat) :
    conjStep p a (M + N) = conjStep p a M + conjStep p a N := by
  simp only [conjStep, mul_add, add_mul, smul_add]; module
private theorem conjStep_sub (p : NonIdentityPauli) (a : ℝ) (M N : Mat) :
    conjStep p a (M - N) = conjStep p a M - conjStep p a N := by
  simp only [conjStep, mul_sub, sub_mul, smul_sub]; module
private theorem conjStep_smul (p : NonIdentityPauli) (a : ℝ) (c : ℂ) (M : Mat) :
    conjStep p a (c • M) = c • conjStep p a M := by
  simp only [conjStep, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, smul_smul]; module
private def gateOrder : Fin 15 → Fin 15 := ![9,1,4,13,12,2,5,10,0,6,11,7,8,3,14]
private def witnessP : Fin 15 → NonIdentityPauli := fun j =>
  ⟨labels (gateOrder j), by fin_cases j <;> decide +kernel⟩
private noncomputable def point : Param := fun i =>
  if i ∈ ({5,6,7,10} : Finset (Fin 15)) then Real.pi / 4 else 0

set_option maxHeartbeats 2000000 in
-- Each column uses at most four sparse double-angle conjugations.
private theorem witness_columns (j : Fin 15) :
    colScale j • H witnessP point j = E (fun i => rowScale i * (certA i j : ℝ)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hc : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by simp [pow_succ, hs]
  rw [H, prefixOp, list_conjugation]
  fin_cases j <;>
    simp only [colScale, Fin.isValue, Fin.zero_eta, Finset.mem_insert, zero_ne_one, Fin.reduceEq, Finset.mem_singleton, or_self, or_false, ↓reduceIte, witnessP, ne_eq, labels,
      gateOrder, point, cons_val_zero, cons_val, List.take, List.foldr_nil, E, Fin.sum_univ_succ, cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      Finset.univ_unique, Fin.default_eq_zero, cons_val_fin_one, Finset.sum_singleton, rowScale, certA, one_div, transpose_apply, cons_val', ite_mul, one_mul, _root_.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Rat.cast_zero, mul_zero, zero_smul, one_ne_zero, or_true, cons_val_one, Rat.cast_one, mul_one, add_zero,
      zero_add, Fin.mk_one, List.finRange, List.ofFn_succ, List.ofFn_zero, List.take_succ_cons, List.foldr_cons, List.foldr, conjStep_word, sgn, anticomm, Bool.false_eq_true,
      bne_self_eq_false, Int.reduceNeg, reduceCtorEq, Fin.reduceFinMk, bne_iff_ne, not_false_eq_true, mul_neg, Nat.succ_eq_add_one, Nat.reduceAdd, Real.cos_zero,
      Complex.ofReal_one, one_smul, Real.sin_zero, Complex.ofReal_zero, zero_mul, pauliPhase, Fin.prod_univ_two, neg_zero, pauliProd, sub_zero, neg_neg, Real.cos_pi_div_four,
      Complex.ofReal_div, Complex.ofReal_ofNat, Real.sin_pi_div_four, neg_smul, sub_neg_eq_add, conjStep_add, conjStep_smul, smul_add, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat,
      Rat.cast_inv, conjStep_sub] <;> match_scalars
  all_goals
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq, Complex.inv_re, Complex.inv_im]
    all_goals ring_nf <;> simp only [hs, hc] <;> ring
private theorem J_witness : (J_H witnessP point : Matrix (Fin 15) (Fin 15) ℝ) =
    R * ratReal certA * Si := by
  have hs : ∀ j, colScale j ≠ 0 := by
    intro j; simp only [colScale]; split_ifs <;> positivity
  ext i j
  have hh := congrArg (fun M => rho M i) (witness_columns j)
  simp only [map_smul, rho_E] at hh
  change colScale j * J_H witnessP point i j = rowScale i * (certA i j : ℝ) at hh
  simp only [R, Si, diagonal_mul, mul_diagonal, ratReal, RingHom.mapMatrix_apply,
    map_apply, Rat.coe_castHom]
  change J_H witnessP point i j = rowScale i * (certA i j : ℝ) * (colScale j)⁻¹
  exact (eq_div_iff (hs j)).mpr (by simpa [mul_comm] using hh)
private theorem normalized_witness : B * Matrix.of (J_H witnessP point) * U = D := by
  rw [show Matrix.of (J_H witnessP point) = R * ratReal certA * Si from J_witness]
  calc _ = ratReal certK * (Ri * R) * ratReal certA * (Si * S) * ratReal certN := by
             simp only [B, U, mul_assoc]
       _ = D := by rw [scaling_inverse.1, scaling_inverse.2]
                   simp only [mul_one, ← map_mul, rational_certificate.2.2.2.2, D]

private theorem sqrt_inverse : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
private theorem H_witness (j : Fin 15) : H witnessP point j =
    (colScale j)⁻¹ • E (fun i => rowScale i * (certA i j : ℝ)) := by
  have hs : colScale j ≠ 0 := by simp only [colScale]; split_ifs <;> positivity
  rw [← witness_columns, smul_smul, inv_mul_cancel₀ hs, one_smul]
private theorem B_row (i : Fin 15) : B 12 i = (certz i : ℝ) / rowScale i := by
  fin_cases i <;> simp [B, Ri, mul_diagonal, ratReal, certK, certL, certe, certz, div_eq_mul_inv,
    rowScale, sqrt_inverse]
set_option maxHeartbeats 2000000 in
-- Only the four left-kernel coordinates contribute to this commutator contraction.
private theorem contracted_derivative :
    (B *ᵥ (Matrix.of (J_D witnessP point v) *ᵥ v)) 12 = -1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    calc _ = (Real.sqrt 2 ^ 2) ^ 3 := by ring
         _ = 8 := by rw [hs]; norm_num
  simp only [mulVec, dotProduct, B_row, Matrix.of_apply, Fin.sum_univ_succ]
  simp only [certz, cons_val_zero, cons_val_succ, cons_val_fin_one, Rat.cast_zero, Rat.cast_one,
    Rat.cast_neg, Rat.cast_ofNat, zero_div, zero_mul, zero_add]
  simp only [v, S, mulVec_diagonal, certu, colScale, rowScale, Finset.mem_insert, Finset.mem_singleton,
    cons_val_zero, cons_val_succ, cons_val_fin_one, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat,
    Rat.cast_zero, Rat.cast_one, Fin.reduceEq, or_false, ↓reduceIte, mul_zero, zero_add]
  simp only [J_D, H_D, H_witness, colScale, Fin.isValue, Finset.mem_insert, Finset.mem_singleton, E, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, rowScale, certA, one_div, transpose_apply, cons_val', cons_val_fin_one, ite_mul, one_mul, _root_.add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, zero_ne_one, Fin.reduceEq, or_self,
    or_false, ↓reduceIte, cons_val_zero, one_ne_zero, or_true, cons_val_one, cons_val, smul_add, map_add, map_smul, prefixG, Fin.mk_eq_zero, Fin.mk_eq_one, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.coe_pi', sqrt_inverse, Rat.cast_zero, mul_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Finset.univ_eq_empty, Finset.sum_empty, ContinuousLinearMap.comp_zero, smul_zero, Rat.cast_one, mul_one, add_zero, sub_self,
    _root_.zero_apply, zero_mul, Nat.reduceMod, Fin.val_eq_zero, Fin.zero_eta, zero_smul, zero_add, Finset.sum_const, Finset.card_singleton, one_smul, ContinuousLinearMap.comp_apply, _root_.smul_apply, _root_.sub_apply, mulVec_diagonal,
    Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', Fin.val_eq_zero_iff, Fin.val_succ, Fin.mk_one, Fin.succ_ne_zero, ContinuousLinearMap.comp_add, inv_one, Nat.add_eq_right,
    false_or, cons_val_succ', Nat.reduceAdd, Fin.reduceFinMk, Rat.cast_inv, map_zero, ne_eq, not_false_eq_true, div_self]
  simp only [mul_add, word_product, Fin.prod_univ_two, pauliProd, pauliPhase,
    labels, cons_val_zero, cons_val_one, smul_smul, mul_one, one_mul, mul_neg]
  simp only [rho, labels, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val, cons_val_one, mul_one, one_smul, sub_self, smul_zero, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, mul_zero, trace_zero, Complex.zero_re, zero_div, zero_mul, mul_neg, neg_mul, Complex.I_mul_I, neg_neg, neg_smul, smul_neg, one_mul, add_sub_add_left_eq_sub, Algebra.mul_smul_comm, mul_sub, trace_smul, trace_sub,
    trace_neg, word_trace_mul, vecCons_inj, reduceCtorEq, and_true, and_self, ↓reduceIte, smul_eq_mul, neg_zero, mul_add, trace_add, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_ofNat, add_zero, zero_add, sub_neg_eq_add, Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.neg_re, Complex.I_re, Complex.ofReal_re, Complex.one_re, Complex.ofReal_im, Complex.div_ofNat_im, Complex.neg_im,
    Complex.one_im, sub_zero, Complex.mul_im, Complex.re_ofNat, Complex.I_im, Complex.im_ofNat, zero_sub, and_false, Complex.ofReal_inv, Complex.sub_re, Complex.inv_re, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im]
  ring_nf; simp only [h6, sqrt_inverse]; nlinarith [hs]

private theorem coordinate_det : det B ≠ 0 ∧ det U ≠ 0 := by
  constructor
  · intro h; have hh := congrArg det coordinate_inverse.1; simp [det_mul, h] at hh
  · intro h; have hh := congrArg det coordinate_inverse.2; simp [det_mul, h] at hh
private theorem D_eq : D = diagonal (fun i : Fin 15 => if i = 12 then (0 : ℝ) else 1) := by
  ext i j; simp [D, certD, ratReal, diagonal]; split_ifs <;> simp
private noncomputable def normalize : (Fin 15 → Fin 15 → ℝ) →L[ℝ] (Fin 15 → Fin 15 → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => B * Matrix.of M * U
    map_add' := by intro M N; ext i j; simp [mul_apply, add_mul, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c M; change B * (c • Matrix.of M) * U = _
      rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
private noncomputable def detForm {n : Type*} [Fintype n] [DecidableEq n] :
    (n → ℝ) [⋀^n]→L[ℝ] ℝ :=
  { (detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ) with cont := continuous_id.matrix_det }
private theorem detForm_apply {n : Type*} [Fintype n] [DecidableEq n] (M : n → n → ℝ) :
    (detForm (n := n)).1 M = det (Matrix.of M) := rfl
private noncomputable def detDiff {n : Type*} [Fintype n] [DecidableEq n] (M : n → n → ℝ) :
    (n → n → ℝ) →L[ℝ] ℝ := (detForm (n := n)).1.linearDeriv M
private theorem detForm_deriv {n : Type*} [Fintype n] [DecidableEq n] (M T : n → n → ℝ) :
    detDiff M T = ∑ i, det (Matrix.of (Function.update M i (T i))) := by
  simp only [detDiff, ContinuousMultilinearMap.linearDeriv_apply, detForm_apply]
private theorem det_comp_strict {n : Type*} [Fintype n] [DecidableEq n]
    {f : Param → (n → n → ℝ)} {fD : Param →L[ℝ] (n → n → ℝ)} {a : Param}
    (hf : HasStrictFDerivAt f fD a) :
    HasStrictFDerivAt (fun x => det (Matrix.of (f x))) ((detDiff (f a)).comp fD) a := by
  simpa only [detDiff, Function.comp_def, detForm_apply] using ((detForm (n := n)).1.hasStrictFDerivAt _).comp a hf
private noncomputable def g (α : Param) : ℝ := det (Matrix.of (normalize (J_H witnessP α)))
private noncomputable def gD (α : Param) : Param →L[ℝ] ℝ :=
  (detDiff (normalize (J_H witnessP α))).comp (normalize.comp (J_D witnessP α))
private theorem g_strict (α : Param) : HasStrictFDerivAt g (gD α) α :=
  det_comp_strict (normalize.hasStrictFDerivAt.comp α (J_strict witnessP α))
private theorem g_zero_iff (α : Param) : g α = 0 ↔ det (J_H witnessP α) = 0 := by
  change det (B * Matrix.of (J_H witnessP α) * U) = 0 ↔ det (Matrix.of (J_H witnessP α)) = 0
  simp [det_mul, coordinate_det.1, coordinate_det.2]
private theorem g_point : g point = 0 := by
  change det (B * Matrix.of (J_H witnessP point) * U) = 0
  rw [normalized_witness]; exact det_eq_zero_of_row_eq_zero 12 (by intro j; simp [D_eq, diagonal])
private theorem det_derivative_D (T : Fin 15 → Fin 15 → ℝ) : detDiff D T = T 12 12 := by
  rw [detForm_deriv]
  change (∑ i, det (D.updateRow i (T i))) = T 12 12
  rw [Finset.sum_eq_single 12]
  · have hh : D.updateRow 12 (T 12) = (1 : Matrix (Fin 15) (Fin 15) ℝ).updateRow 12 (T 12) := by
      ext i j; by_cases h : i = 12 <;> simp [D_eq, updateRow_apply, diagonal, one_apply, h]
    rw [hh, ← cramer_transpose_apply, transpose_one, cramer_one]; rfl
  · intro i _ hi; exact det_eq_zero_of_row_eq_zero 12 (by intro j; simp [D_eq, updateRow_apply, Ne.symm hi, diagonal])
  · intro h; simp at h
private theorem U_pivot : U *ᵥ Pi.single 12 1 = v := by
  unfold U v; rw [← mulVec_mulVec]; congr 1; ext i
  rw [mulVec_single_one]
  change (certN i 12 : ℝ) = (certu i : ℝ)
  exact_mod_cast (show certN i 12 = certu i from
    (show ∀ k, certN k 12 = certu k by decide +kernel) i)
set_option maxRecDepth 2000 in
private theorem gD_direction : gD point v = -1 := by
  have hn : normalize (J_H witnessP point) = D := normalized_witness
  simp only [gD, hn, ContinuousLinearMap.comp_apply, det_derivative_D]
  change (B * Matrix.of (J_D witnessP point v) * U) 12 12 = -1
  have hh := congrFun (mulVec_single_one (B * Matrix.of (J_D witnessP point v) * U) 12) 12
  change ((B * Matrix.of (J_D witnessP point v) * U) *ᵥ Pi.single 12 1) 12 = (B * Matrix.of (J_D witnessP point v) * U) 12 12 at hh
  rw [← hh, ← mulVec_mulVec, ← mulVec_mulVec, U_pivot]
  exact contracted_derivative

end D5.S3.Quantum.Information.PauliRotationCriticalValues
