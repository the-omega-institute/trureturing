/- GID: D5/S3/Quantum/Information/PauliRotationCriticalValues
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/PauliRotationCriticalValues
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/PauliRotationCriticalValues.claim; result=D5/S3/Quantum/Information/PauliRotationCriticalValues.result; claim=D5/S3/Quantum/Information/PauliRotationCriticalValues.claim
   digest: Two-qubit Pauli rotation circuits and their critical-value Hausdorff dimension. -/

import D5.S3.Analytic.NullSets.AnalyticZeroSetNull
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Observer.Hankel.PositiveGramianBalancing

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

open D5.S3.Observer.Hankel.PositiveGramianBalancing (diagonal_scalings)
open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (pauliMatrix tensorOp tensor_mul)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (wordUnit word_hermitian word_expansion letterProduct letterPhase letter_mul word_one tensor_one word_trace_pair word_mul word_comm_sign)

private def labels : Fin 15 → Fin 2 → Pauli :=
  ![![.I,.X], ![.I,.Y], ![.I,.Z], ![.X,.I], ![.X,.X], ![.X,.Y], ![.X,.Z],
    ![.Y,.I], ![.Y,.X], ![.Y,.Y], ![.Y,.Z], ![.Z,.I], ![.Z,.X], ![.Z,.Y], ![.Z,.Z]]
private theorem labels_unfold : labels = ![![.I,.X], ![.I,.Y], ![.I,.Z], ![.X,.I], ![.X,.X], ![.X,.Y], ![.X,.Z], ![.Y,.I], ![.Y,.X], ![.Y,.Y], ![.Y,.Z], ![.Z,.I], ![.Z,.X], ![.Z,.Y], ![.Z,.Z]] := rfl

private theorem labels_injective : Function.Injective labels := by decide
private noncomputable def E : Param →L[ℝ] Mat :=
  ∑ i : Fin 15, (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).smulRight (wordOp (labels i))
private theorem E_unfold : E = ∑ i : Fin 15, (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).smulRight (wordOp (labels i)) := rfl

private noncomputable def rho : Mat →L[ℝ] Param :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M i => (trace (wordOp (labels i) * M)).re / 4
    map_add' := by
      intro A B; funext i
      simp -implicitDefEqProofs [mul_add, trace_add, add_div]
    map_smul' := by
      intro c A; funext i
      simp -implicitDefEqProofs [trace_smul, smul_eq_mul, Complex.mul_re, mul_div_assoc] }
private theorem rho_unfold (M : Mat) (i : Fin 15) : rho M i = (trace (wordOp (labels i) * M)).re / 4 := rfl

private theorem rho_E (x : Param) : rho (E x) = x := by
  ext i
  change (trace (wordOp (labels i) * ∑ j, x j • wordOp (labels j))).re / 4 = x i
  simp -implicitDefEqProofs only [Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul]
  simp_rw [word_trace_pair, labels_injective.eq_iff]
  norm_num
private theorem E_rho (M : Mat) (hs : star M = M) (ht : trace M = 0) : E (rho M) = M := by
  have hr (i : Fin 15) : ((trace (wordOp (labels i) * M)).re : ℂ) =
      trace (wordOp (labels i) * M) := by
    apply Complex.conj_eq_iff_re.mp
    change star (trace (wordOp (labels i) * M)) = _
    rw [← trace_conjTranspose, conjTranspose_mul]
    change trace (star M * star (wordOp (labels i))) = _
    rw [hs, (fun p : Fin 2 → Pauli => (Matrix.star_eq_conjTranspose (wordOp p)).trans (word_hermitian p)), trace_mul_comm]
  have expansion := word_expansion (n := 2) M
  let enumeration : Fin 16 ≃ (Fin 2 → Pauli) := Equiv.ofBijective
    (fun i : Fin 16 => Fin.cases (fun _ => Pauli.I) labels i)
    (by constructor <;> decide)
  rw [← Equiv.sum_comp enumeration] at expansion
  rw [Fin.sum_univ_succ] at expansion
  simp only [enumeration, Equiv.ofBijective_apply, Fin.cases_zero,
    Fin.cases_succ, word_one, one_mul, ht, mul_zero, zero_smul, zero_add] at expansion
  norm_num only [pow_two, show (2 : ℂ) * 2 = 4 by norm_num] at expansion
  apply Eq.trans ?_ expansion.symm
  change (∑ i, rho M i • wordOp (labels i)) = _
  apply Finset.sum_congr rfl
  intro i _
  change ((trace (wordOp (labels i) * M)).re / 4) • _ = _
  ext x y
  change (((trace (wordOp (labels i) * M)).re / 4 : ℝ) : ℂ) * _ = _
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, hr]
  simp only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm]
private theorem rotation_complex (p : NonIdentityPauli) (a : ℝ) :
    rotation p a = (Real.cos (a / 2) : ℂ) • (1 : Mat) -
      ((Real.sin (a / 2) : ℂ) * Complex.I) • wordOp p.val := by
  ext x y
  dsimp only [rotation]
  simp -implicitDefEqProofs [smul_eq_mul, Complex.real_smul, mul_assoc]
private theorem rotation_unitary (p : NonIdentityPauli) (a : ℝ) :
    rotation p a ∈ unitary Mat := by
  have hc : (Real.cos (a / 2) : ℂ) ^ 2 + (Real.sin (a / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq (a / 2)] :
      Real.cos (a / 2) ^ 2 + Real.sin (a / 2) ^ 2 = 1)
  rw [Unitary.mem_iff, rotation_complex]
  simp -implicitDefEqProofs only [star_sub, star_smul, star_one, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, (fun p : Fin 2 → Pauli => (Matrix.star_eq_conjTranspose (wordOp p)).trans (word_hermitian p))]
  constructor <;>
    simp -implicitDefEqProofs only [mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      (show ∀ p : Fin 2 → Pauli, wordOp p * wordOp p = (1 : Mat) from fun p => (wordUnit p).val_inv), smul_smul] <;>
    calc _ = ((Real.cos (a / 2) : ℂ) ^ 2 + (Real.sin (a / 2) : ℂ) ^ 2) • (1 : Mat) := by
          match_scalars
          all_goals ring_nf
          all_goals simp -implicitDefEqProofs only [Complex.I_sq]
          all_goals ring
         _ = 1 := by rw [hc, one_smul]
private noncomputable def listCircuit (P : Fin 15 → NonIdentityPauli)
    (l : List (Fin 15)) (α : Param) : Mat :=
  (l.map (fun j => rotation (P j) (α j))).prod
private theorem listCircuit_unfold : listCircuit = fun P l α => (l.map (fun j => rotation (P j) (α j))).prod := rfl

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
private theorem gateD_unfold : gateD = fun P α j => (ContinuousLinearMap.proj j : Param →L[ℝ] ℝ).smulRight ((-Complex.I / 2) • (wordOp (P j).val * rotation (P j) (α j))) := rfl

private theorem gate_deriv (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    HasStrictFDerivAt (fun β : Param => rotation (P j) (β j)) (gateD P α j) α := by
  let d := (1 / 2 : ℝ) • (ContinuousLinearMap.proj j : Param →L[ℝ] ℝ)
  have hd : HasStrictFDerivAt (fun β : Param => β j / 2) d α := by
    simpa -implicitDefEqProofs [d, div_eq_mul_inv, mul_comm] using
      (ContinuousLinearMap.proj j : Param →L[ℝ] ℝ).hasStrictFDerivAt.const_mul (1 / 2)
  apply (hd.cos.smul_const (1 : Mat) |>.sub
    (hd.sin.smul_const (Complex.I • wordOp (P j).val))).congr_fderiv
  ext1 h
  simp -implicitDefEqProofs only [gateD_unfold, d, _root_.sub_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, ContinuousLinearMap.proj_apply, rotation_complex, mul_sub, Matrix.mul_smul,
    mul_one, (show ∀ p : Fin 2 → Pauli, wordOp p * wordOp p = (1 : Mat) from fun p => (wordUnit p).val_inv), smul_smul]
  ext x y
  simp -implicitDefEqProofs only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring_nf
  all_goals simp -implicitDefEqProofs [Complex.I_sq]
  all_goals ring

private theorem list_split (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15))
    (α : Param) (i : Fin l.length) :
    listCircuit P (l.take i) α * rotation (P l[i]) (α l[i]) *
      listCircuit P (l.drop (i.val + 1)) α = listCircuit P l α := by
  have hi : i.val < (l.map (fun j => rotation (P j) (α j))).length := by simp -implicitDefEqProofs
  have hh := List.prod_take_mul_prod_drop (l.map (fun j => rotation (P j) (α j))) (i.val + 1)
  rw [List.prod_take_succ _ _ hi] at hh
  simpa -implicitDefEqProofs [listCircuit_unfold, List.map_take, List.map_drop] using hh

private noncomputable def listD (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15))
    (α : Param) : Param →L[ℝ] Mat :=
  ∑ i : Fin l.length, (ContinuousLinearMap.proj l[i] : Param →L[ℝ] ℝ).smulRight
    ((-Complex.I / 2) • (listCircuit P (l.take i) α * wordOp (P l[i]).val *
      star (listCircuit P (l.take i) α) * listCircuit P l α))
private theorem listD_unfold : listD = fun P l α => ∑ i : Fin l.length, (ContinuousLinearMap.proj l[i] : Param →L[ℝ] ℝ).smulRight ((-Complex.I / 2) • (listCircuit P (l.take i) α * wordOp (P l[i]).val * star (listCircuit P (l.take i) α) * listCircuit P l α)) := rfl

private theorem list_deriv (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15)) (α : Param) :
    HasStrictFDerivAt (listCircuit P l) (listD P l α) α := by
  apply (HasStrictFDerivAt.list_prod' (l := l) (fun j _ => gate_deriv P α j)).congr_fderiv
  ext1 h
  simp -implicitDefEqProofs only [listD_unfold, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp -implicitDefEqProofs only [_root_.smul_apply, op_smul_eq_mul, smul_eq_mul, gateD_unfold,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  change listCircuit P (l.take i) α *
      ((h l[i] • ((-Complex.I / 2) • (wordOp (P l[i]).val * rotation (P l[i]) (α l[i])))) *
      listCircuit P (l.drop (i.val + 1)) α) = _
  rw [← list_split P l α i]
  simp -implicitDefEqProofs only [Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
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
private theorem J_H_unfold : J_H = fun P α => fun i j => rho (H P α j) i := rfl

private theorem H_star (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    star (H P α j) = H P α j := by
  exact (show IsSelfAdjoint (wordOp (P j).val) from
    (Matrix.star_eq_conjTranspose _).trans (word_hermitian _)).conjugate _

private theorem H_trace (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    trace (H P α j) = 0 := by
  have hI : wordOp (fun _ : Fin 2 => Pauli.I) = (1 : Mat) := tensor_one
  have hz : trace (wordOp (P j).val) = 0 := by
    simpa -implicitDefEqProofs only [hI, mul_one, if_neg (P j).property] using
      word_trace_pair (P j).val (fun _ => Pauli.I)
  rw [H, trace_mul_cycle, Unitary.star_mul_self_of_mem (prefix_unitary P α j.val), one_mul, hz]

private theorem E_J_mulVec (P : Fin 15 → NonIdentityPauli) (α h : Param) :
    E ((J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h) = ∑ j, h j • H P α j := by
  have hv : (J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h = ∑ j, h j • rho (H P α j) := by
    ext i
    simp -implicitDefEqProofs [J_H_unfold, Matrix.mulVec, dotProduct, mul_comm]
  rw [hv, map_sum]
  simp -implicitDefEqProofs only [map_smul, E_rho _ (H_star P α _) (H_trace P α _)]

private theorem circuit_fderiv (P : Fin 15 → NonIdentityPauli) (α h : Param) :
    fderiv ℝ (circuit P) α h = (-Complex.I / 2) •
      (E ((J_H P α : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ h) * circuit P α) := by
  rw [(circuit_strict P α).hasFDerivAt.fderiv, E_J_mulVec]
  simp -implicitDefEqProofs only [listD_unfold, _root_.sum_apply,
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
    simp -implicitDefEqProofs only [Matrix.smul_mul, mul_assoc,
      Unitary.mul_star_self_of_mem (circuit_unitary P α), mul_one, zero_mul] at hz
    have hc : (-Complex.I / 2 : ℂ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num)
    exact Function.LeftInverse.injective rho_E (by simpa -implicitDefEqProofs using (smul_eq_zero.mp hz).resolve_left hc)
  · intro hh; simp -implicitDefEqProofs [hh]

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
    simp -implicitDefEqProofs only [Fintype.card_fin] at hr
    omega
  · intro hd
    obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have hk : LinearMap.ker (Matrix.mulVecLin (J_H P α)) ≠ ⊥ := by
      intro he
      exact hv (by simpa -implicitDefEqProofs only [he, Submodule.mem_bot] using
        (show v ∈ LinearMap.ker (Matrix.mulVecLin (J_H P α)) from hz))
    have hp := Submodule.one_le_finrank_iff.mpr hk
    have hr := (Matrix.mulVecLin (J_H P α)).finrank_range_add_finrank_ker
    simp -implicitDefEqProofs only [Module.finrank_pi, Fintype.card_fin] at hr
    change Matrix.rank (J_H P α) + _ = 15 at hr
    omega

private noncomputable def prefixG (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    Param →L[ℝ] Mat :=
  ∑ k : Fin j.val,
    (ContinuousLinearMap.proj (⟨k.val, lt_trans k.isLt j.isLt⟩ : Fin 15) : Param →L[ℝ] ℝ).smulRight
      (H P α ⟨k.val, lt_trans k.isLt j.isLt⟩)
private theorem prefixG_unfold : prefixG = fun P α j => ∑ k : Fin j.val, (ContinuousLinearMap.proj (⟨k.val, lt_trans k.isLt j.isLt⟩ : Fin 15) : Param →L[ℝ] ℝ).smulRight (H P α ⟨k.val, lt_trans k.isLt j.isLt⟩) := rfl

private theorem prefix_strict (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    HasStrictFDerivAt (fun β => prefixOp P β j.val)
      (((ContinuousLinearMap.mul ℝ Mat).flip (prefixOp P α j.val)).comp
        ((-Complex.I / 2) • prefixG P α j)) α := by
  apply (list_deriv P ((List.finRange 15).take j.val) α).congr_fderiv
  ext1 h
  simp -implicitDefEqProofs only [listD_unfold, prefixG_unfold,
    _root_.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', _root_.smul_apply, Matrix.smul_mul, Finset.sum_mul,
    Finset.smul_sum]
  apply Finset.sum_equiv (finCongr (by simp -implicitDefEqProofs)) (by simp -implicitDefEqProofs)
  intro k _
  have hk : k.val ≤ j.val := by have := k.isLt; simp -implicitDefEqProofs only [List.length_take] at this; omega
  simp -implicitDefEqProofs [List.take_take, Nat.min_eq_left hk, H, prefixOp, smul_comm (h _) (-Complex.I / 2)]

private noncomputable def H_D (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    Param →L[ℝ] Mat := (-Complex.I / 2) •
  (((ContinuousLinearMap.mul ℝ Mat).flip (H P α j)).comp (prefixG P α j) -
    ((ContinuousLinearMap.mul ℝ Mat) (H P α j)).comp (prefixG P α j))
private theorem H_D_unfold : H_D = fun P α j => (-Complex.I / 2) • (((ContinuousLinearMap.mul ℝ Mat).flip (H P α j)).comp (prefixG P α j) - ((ContinuousLinearMap.mul ℝ Mat) (H P α j)).comp (prefixG P α j)) := rfl

private theorem H_deriv (P : Fin 15 → NonIdentityPauli) (α : Param) (j : Fin 15) :
    HasStrictFDerivAt (fun β => H P β j) (H_D P α j) α := by
  have hp := prefix_strict P α j
  apply ((hp.mul_const' (wordOp (P j).val)).mul' hp.star).congr_fderiv
  ext1 h
  simp -implicitDefEqProofs only [H_D_unfold, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearEquiv.coe_coe,
    starL'_apply, op_smul_eq_mul, smul_eq_mul, Matrix.smul_mul]
  have hg : star (prefixG P α j h) = prefixG P α j h := by
    simp -implicitDefEqProofs [prefixG_unfold, star_sum, star_smul, H_star]
  have hc : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by simp -implicitDefEqProofs; ring
  simp -implicitDefEqProofs only [star_smul, star_mul, hg, hc, H, Matrix.mul_smul,
    mul_assoc, smul_sub, neg_smul, mul_neg]
  module

private noncomputable def J_D (P : Fin 15 → NonIdentityPauli) (α : Param) :
    Param →L[ℝ] (Fin 15 → Fin 15 → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).comp (rho.comp (H_D P α j))
private theorem J_D_unfold : J_D = fun P α => ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => (ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).comp (rho.comp (H_D P α j)) := rfl

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
  simp -implicitDefEqProofs only [star_sub, star_smul, star_one, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, (fun p : Fin 2 → Pauli => (Matrix.star_eq_conjTranspose (wordOp p)).trans (word_hermitian p)), mul_sub, sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, smul_sub, mul_assoc]
  match_scalars <;> ring_nf
  all_goals simp -implicitDefEqProofs [Complex.I_sq]
private theorem conjStep_comm (p : NonIdentityPauli) (a : ℝ) (Q : Mat)
    (hq : wordOp p.val * Q = Q * wordOp p.val) : conjStep p a Q = Q := by
  have hh : wordOp p.val * Q * wordOp p.val = Q := by
    rw [hq, mul_assoc, (show ∀ p : Fin 2 → Pauli, wordOp p * wordOp p = (1 : Mat) from fun p => (wordUnit p).val_inv), mul_one]
  rw [conjStep, hh, hq]
  simp -implicitDefEqProofs only [sub_self, smul_zero, sub_zero]
  module
private theorem conjStep_anticomm (p : NonIdentityPauli) (a : ℝ) (Q : Mat)
    (hq : wordOp p.val * Q = -(Q * wordOp p.val)) :
    conjStep p a Q = (Real.cos a : ℂ) • Q -
      ((Real.sin a : ℂ) * Complex.I) • (wordOp p.val * Q) := by
  have hh : wordOp p.val * Q * wordOp p.val = -Q := by
    rw [hq, neg_mul, mul_assoc, (show ∀ p : Fin 2 → Pauli, wordOp p * wordOp p = (1 : Mat) from fun p => (wordUnit p).val_inv), mul_one]
  have hqp : Q * wordOp p.val = -(wordOp p.val * Q) := by rw [hq, neg_neg]
  simp -implicitDefEqProofs only [conjStep, hh, hqp, smul_neg, sub_neg_eq_add, smul_add]
  module
private theorem list_conjugation (P : Fin 15 → NonIdentityPauli) (l : List (Fin 15))
    (α : Param) (Q : Mat) : listCircuit P l α * Q * star (listCircuit P l α) =
      l.foldr (fun k M => conjStep (P k) (α k) M) Q := by
  induction l with
  | nil => simp -implicitDefEqProofs [listCircuit_unfold]
  | cons k l ih =>
    rw [List.foldr_cons, ← rotation_conjugation, ← ih]
    simp -implicitDefEqProofs only [listCircuit_unfold, List.map_cons, List.prod_cons, star_mul, mul_assoc]
private theorem J_recurrence (P : Fin 15 → NonIdentityPauli) (α : Param) (i j : Fin 15) :
    J_H P α i j = rho (((List.finRange 15).take j.val).foldr
      (fun k M => conjStep (P k) (α k) M) (wordOp (P j).val)) i := by
  simp -implicitDefEqProofs only [J_H_unfold, H, prefixOp, list_conjugation]

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
private theorem certA_unfold : certA = Matrix.transpose ![![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0], ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,-1/2,1/2,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0], ![1/4,1/4,0,0,0,0,-1/2,0,-1/4,1/4,0,1/2,0,0,0], ![1/4,1/4,0,0,0,0,1/2,0,-1/4,1/4,0,-1/2,0,0,0], ![1/4,1/4,0,0,0,0,1/2,0,1/4,-1/4,0,1/2,0,0,0], ![0,0,0,-1/2,0,0,0,1/2,0,0,0,0,-1/4,1/4,1/2], ![-1/4,1/4,1/2,0,-1/4,-1/4,0,0,1/4,1/4,0,0,0,0,0], ![0,0,0,1/2,0,0,0,1/2,0,0,0,0,-1/4,1/4,-1/2], ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,1]] := rfl

private def certL : RatMat :=
  ![![0,0,0,0,0,0,0,0,1,1,0,0,0,0,0], ![-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,1,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,-1/2,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,1/2,0,0,0,0,1,0,0], ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    ![0,0,0,0,0,0,0,0,-2,0,0,1,0,0,0], ![2,0,0,0,0,0,0,0,0,0,0,-1,0,0,0],
    ![2,0,0,0,0,0,0,0,2,0,0,0,0,0,0], ![0,0,0,-1/2,0,0,0,1,0,0,0,0,0,0,1/2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,1/2,0,0,0,1,0,0,0,0,0,0,-1/2],
    ![0,0,0,1/2,0,0,0,0,0,0,0,0,0,0,1/2]]
private theorem certL_unfold : certL = ![![0,0,0,0,0,0,0,0,1,1,0,0,0,0,0], ![-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,1,1,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,-1/2,0,0,0,0,0,1,0], ![0,0,0,0,0,0,0,1/2,0,0,0,0,1,0,0], ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0], ![0,0,0,0,0,0,0,0,-2,0,0,1,0,0,0], ![2,0,0,0,0,0,0,0,0,0,0,-1,0,0,0], ![2,0,0,0,0,0,0,0,2,0,0,0,0,0,0], ![0,0,0,-1/2,0,0,0,1,0,0,0,0,0,0,1/2], ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,1/2,0,0,0,1,0,0,0,0,0,0,-1/2], ![0,0,0,1/2,0,0,0,0,0,0,0,0,0,0,1/2]] := rfl

private def certu : Fin 15 → ℚ := ![-1/2,-1/2,1/2,0,0,-1/2,1/2,0,1/2,1/2,0,0,1,0,0]
private theorem certu_unfold : certu = ![-1/2,-1/2,1/2,0,0,-1/2,1/2,0,1/2,1/2,0,0,1,0,0] := rfl

private def certz : Fin 15 → ℚ := ![-2,0,0,0,0,0,1,0,-2,0,0,1,0,0,0]
private theorem certz_unfold : certz = ![-2,0,0,0,0,0,1,0,-2,0,0,1,0,0,0] := rfl

private def certe : Fin 15 → ℚ := Pi.single 12 1
private theorem certe_unfold : certe = Pi.single 12 1 := rfl

private def certr : Fin 15 → ℚ := Pi.single 6 1
private def certD : RatMat := diagonal (fun i => if i = 12 then 0 else 1)
private theorem certD_unfold : certD = diagonal (fun i => if i = 12 then 0 else 1) := rfl

private def certN : RatMat := 1 + vecMulVec (certu - certe) certe
private def certNi : RatMat := 1 - vecMulVec (certu - certe) certe
private def certK : RatMat := certL + vecMulVec certe certz
private theorem certK_unfold : certK = certL + vecMulVec certe certz := rfl

private def certKi : RatMat := certA * certD + vecMulVec certr certe
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The kernel reduces three finite rational matrix identities.
private theorem rational_certificate :
    certK * certKi = 1 ∧ certN * certNi = 1 ∧ certK * certA * certN = certD := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
private noncomputable def ratReal : RatMat →+* Matrix (Fin 15) (Fin 15) ℝ :=
  (Rat.castHom ℝ).mapMatrix
private theorem ratReal_unfold : ratReal = (Rat.castHom ℝ).mapMatrix := rfl

private noncomputable def rowScale (i : Fin 15) : ℝ :=
  if i ∈ ({0,1,4,5,8,9,12,13} : Finset (Fin 15)) then Real.sqrt 2 else 1
private theorem rowScale_unfold : rowScale = fun i => if i ∈ ({0,1,4,5,8,9,12,13} : Finset (Fin 15)) then Real.sqrt 2 else 1 := rfl

private noncomputable def colScale (i : Fin 15) : ℝ :=
  if i ∈ ({0,1,2,3,4,14} : Finset (Fin 15)) then Real.sqrt 2 else 1
private theorem colScale_unfold : colScale = fun i => if i ∈ ({0,1,2,3,4,14} : Finset (Fin 15)) then Real.sqrt 2 else 1 := rfl

private noncomputable def R : Matrix (Fin 15) (Fin 15) ℝ := diagonal rowScale
private noncomputable def Ri : Matrix (Fin 15) (Fin 15) ℝ := diagonal (fun i => (rowScale i)⁻¹)
private noncomputable def S : Matrix (Fin 15) (Fin 15) ℝ := diagonal colScale
private noncomputable def Si : Matrix (Fin 15) (Fin 15) ℝ := diagonal (fun i => (colScale i)⁻¹)
private noncomputable def B : Matrix (Fin 15) (Fin 15) ℝ := ratReal certK * Ri
private theorem B_unfold : B = ratReal certK * Ri := rfl

private noncomputable def U : Matrix (Fin 15) (Fin 15) ℝ := S * ratReal certN
private theorem U_unfold : U = S * ratReal certN := rfl

private noncomputable def D : Matrix (Fin 15) (Fin 15) ℝ := ratReal certD
private theorem D_unfold : D = ratReal certD := rfl

private noncomputable def v : Param := S *ᵥ (fun i => (certu i : ℝ))
private theorem v_unfold : v = S *ᵥ (fun i => (certu i : ℝ)) := rfl

private theorem coordinate_inverse :
    B * (R * ratReal certKi) = 1 ∧ U * (ratReal certNi * Si) = 1 := by
  have hR : Ri * R = 1 := by
    have hp (i : Fin 15) : 0 < rowScale i := by
      simp -implicitDefEqProofs only [rowScale_unfold]; split_ifs <;> positivity
    rw [Ri, R]
    simpa -implicitDefEqProofs only [Real.sqrt_sq (le_of_lt (hp _))] using
      (diagonal_scalings (fun i => rowScale i ^ 2) (fun i => pow_pos (hp i) 2)).2.1
  have hS : Si * S = 1 := by
    have hp (i : Fin 15) : 0 < colScale i := by
      simp -implicitDefEqProofs only [colScale_unfold]; split_ifs <;> positivity
    rw [Si, S]
    simpa -implicitDefEqProofs only [Real.sqrt_sq (le_of_lt (hp _))] using
      (diagonal_scalings (fun i => colScale i ^ 2) (fun i => pow_pos (hp i) 2)).2.1
  have hS' : S * Si = 1 := mul_eq_one_comm.mp hS
  constructor
  · simp -implicitDefEqProofs only [B_unfold, mul_assoc, ← mul_assoc Ri R, hR, one_mul, ← map_mul,
      rational_certificate.1, map_one]
  · simp -implicitDefEqProofs only [U_unfold, mul_assoc, ← mul_assoc (ratReal certN) (ratReal certNi),
      ← map_mul, rational_certificate.2.1, map_one, one_mul, hS']
private theorem letterProduct_rec (p q : Pauli) :
    letterProduct p q = Pauli.rec q (Pauli.rec .X .I .Z .Y q)
      (Pauli.rec .Y .Z .I .X q) (Pauli.rec .Z .Y .X .I q) p := by
  cases p <;> cases q <;> rfl
private theorem letterPhase_rec (p q : Pauli) :
    letterPhase p q = Pauli.rec 1 (Pauli.rec 1 1 Complex.I (-Complex.I) q)
      (Pauli.rec 1 (-Complex.I) 1 Complex.I q)
      (Pauli.rec 1 Complex.I (-Complex.I) 1 q) p := by
  cases p <;> cases q <;> rfl
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (sgn anticomm)
private theorem conjStep_word (p : NonIdentityPauli) (a : ℝ) (q : Fin 2 → Pauli) :
    conjStep p a (wordOp q) =
      if sgn (p.val 0) (q 0) * sgn (p.val 1) (q 1) = -1 then
        (Real.cos a : ℂ) • wordOp q - ((Real.sin a : ℂ) * Complex.I *
          (∏ i, letterPhase (p.val i) (q i))) • wordOp ![letterProduct (p.val 0) (q 0), letterProduct (p.val 1) (q 1)]
      else wordOp q := by
  have hpq : (fun i : Fin 2 => letterProduct (p.val i) (q i)) =
      ![letterProduct (p.val 0) (q 0), letterProduct (p.val 1) (q 1)] := by
    ext i; fin_cases i <;> rfl
  have hh := word_comm_sign p.val q
  simp -implicitDefEqProofs only [Fin.prod_univ_two, ← Int.cast_mul] at hh
  have hs : sgn (p.val 0) (q 0) * sgn (p.val 1) (q 1) = 1 ∨
      sgn (p.val 0) (q 0) * sgn (p.val 1) (q 1) = -1 := by
    unfold sgn; split_ifs <;> norm_num
  split_ifs with h
  · rw [h] at hh
    simpa -implicitDefEqProofs [word_mul, hpq, smul_smul, mul_assoc] using
      conjStep_anticomm p a (wordOp q) (by simpa -implicitDefEqProofs using hh)
  · rw [hs.resolve_right h] at hh
    exact conjStep_comm p a (wordOp q) (by simpa -implicitDefEqProofs using hh)
private theorem conjStep_add (p : NonIdentityPauli) (a : ℝ) (M N : Mat) :
    conjStep p a (M + N) = conjStep p a M + conjStep p a N := by
  simp -implicitDefEqProofs only [conjStep, mul_add, add_mul, smul_add]; module
private theorem conjStep_sub (p : NonIdentityPauli) (a : ℝ) (M N : Mat) :
    conjStep p a (M - N) = conjStep p a M - conjStep p a N := by
  simp -implicitDefEqProofs only [conjStep, mul_sub, sub_mul, smul_sub]; module
private theorem conjStep_smul (p : NonIdentityPauli) (a : ℝ) (c : ℂ) (M : Mat) :
    conjStep p a (c • M) = c • conjStep p a M := by
  simp -implicitDefEqProofs only [conjStep, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, smul_smul]; module
private def gateOrder : Fin 15 → Fin 15 := ![9,1,4,13,12,2,5,10,0,6,11,7,8,3,14]
private theorem gateOrder_unfold : gateOrder = ![9,1,4,13,12,2,5,10,0,6,11,7,8,3,14] := rfl

private def witnessP : Fin 15 → NonIdentityPauli := fun j =>
  ⟨labels (gateOrder j), by fin_cases j <;> decide +kernel⟩
private theorem witnessP_unfold : witnessP = fun j => ⟨labels (gateOrder j), by fin_cases j <;> decide +kernel⟩ := rfl

private noncomputable def point : Param := fun i => if i ∈ ({5,6,7,10} : Finset (Fin 15)) then Real.pi / 4 else 0
private theorem point_unfold : point = fun i => if i ∈ ({5,6,7,10} : Finset (Fin 15)) then Real.pi / 4 else 0 := rfl

set_option maxHeartbeats 2000000 in
-- Each column uses at most four sparse double-angle conjugations.
private theorem witness_columns (j : Fin 15) :
    colScale j • H witnessP point j = E (fun i => rowScale i * (certA i j : ℝ)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hc : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by simp -implicitDefEqProofs [pow_succ, hs]
  rw [H, prefixOp, list_conjugation]
  fin_cases j <;>
    simp -implicitDefEqProofs only [colScale_unfold, Fin.isValue, Fin.zero_eta, Finset.mem_insert, zero_ne_one, Fin.reduceEq, Finset.mem_singleton, or_self, or_false, ↓reduceIte, witnessP_unfold, ne_eq, labels_unfold,
      gateOrder_unfold, point_unfold, cons_val_zero, cons_val, List.take, List.foldr_nil, E_unfold, Fin.sum_univ_succ, cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      Finset.univ_unique, Fin.default_eq_zero, cons_val_fin_one, Finset.sum_singleton, rowScale_unfold, certA_unfold, one_div, transpose_apply, cons_val', ite_mul, one_mul, _root_.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Rat.cast_zero, mul_zero, zero_smul, one_ne_zero, or_true, cons_val_one, Rat.cast_one, mul_one, add_zero,
      zero_add, Fin.mk_one, List.finRange, List.ofFn_succ, List.ofFn_zero, List.take_succ_cons, List.foldr_cons, List.foldr, conjStep_word, sgn, anticomm, Bool.false_eq_true,
      bne_self_eq_false, Int.reduceNeg, reduceCtorEq, Fin.reduceFinMk, bne_iff_ne, not_false_eq_true, mul_neg, Nat.succ_eq_add_one, Nat.reduceAdd, Real.cos_zero,
      Complex.ofReal_one, one_smul, Real.sin_zero, Complex.ofReal_zero, zero_mul, letterPhase_rec, Fin.prod_univ_two, neg_zero, letterProduct_rec, sub_zero, neg_neg, Real.cos_pi_div_four,
      Complex.ofReal_div, Complex.ofReal_ofNat, Real.sin_pi_div_four, neg_smul, sub_neg_eq_add, conjStep_add, conjStep_smul, smul_add, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat,
      Rat.cast_inv, conjStep_sub] <;> match_scalars
  all_goals
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq, Complex.inv_re, Complex.inv_im]
    all_goals ring_nf <;> simp -implicitDefEqProofs only [hs, hc] <;> ring
private theorem J_witness : (J_H witnessP point : Matrix (Fin 15) (Fin 15) ℝ) =
    R * ratReal certA * Si := by
  have hs : ∀ j, colScale j ≠ 0 := by
    intro j; simp -implicitDefEqProofs only [colScale_unfold]; split_ifs <;> positivity
  ext i j
  have hh := congrArg (fun M => rho M i) (witness_columns j)
  simp -implicitDefEqProofs only [map_smul, rho_E] at hh
  change colScale j * J_H witnessP point i j = rowScale i * (certA i j : ℝ) at hh
  simp -implicitDefEqProofs only [R, Si, diagonal_mul, mul_diagonal, ratReal_unfold, RingHom.mapMatrix_apply,
    map_apply, Rat.coe_castHom]
  change J_H witnessP point i j = rowScale i * (certA i j : ℝ) * (colScale j)⁻¹
  exact (eq_div_iff (hs j)).mpr (by simpa -implicitDefEqProofs [mul_comm] using hh)
private theorem normalized_witness : B * Matrix.of (J_H witnessP point) * U = D := by
  have hR : Ri * R = 1 := by
    have hp (i : Fin 15) : 0 < rowScale i := by
      simp -implicitDefEqProofs only [rowScale_unfold]; split_ifs <;> positivity
    simpa -implicitDefEqProofs only [Ri, R, Real.sqrt_sq (le_of_lt (hp _))] using
      (diagonal_scalings (fun i => rowScale i ^ 2) (fun i => pow_pos (hp i) 2)).2.1
  have hS : Si * S = 1 := by
    have hp (i : Fin 15) : 0 < colScale i := by
      simp -implicitDefEqProofs only [colScale_unfold]; split_ifs <;> positivity
    simpa -implicitDefEqProofs only [Si, S, Real.sqrt_sq (le_of_lt (hp _))] using
      (diagonal_scalings (fun i => colScale i ^ 2) (fun i => pow_pos (hp i) 2)).2.1
  rw [show Matrix.of (J_H witnessP point) = R * ratReal certA * Si from J_witness]
  calc _ = ratReal certK * (Ri * R) * ratReal certA * (Si * S) * ratReal certN := by
             simp -implicitDefEqProofs only [B_unfold, U_unfold, mul_assoc]
       _ = D := by rw [hR, hS]
                   simp -implicitDefEqProofs only [mul_one, ← map_mul, rational_certificate.2.2, D_unfold]
private theorem H_witness (j : Fin 15) : H witnessP point j =
    (colScale j)⁻¹ • E (fun i => rowScale i * (certA i j : ℝ)) := by
  have hs : colScale j ≠ 0 := by simp -implicitDefEqProofs only [colScale_unfold]; split_ifs <;> positivity
  rw [← witness_columns, smul_smul, inv_mul_cancel₀ hs, one_smul]
private theorem B_row (i : Fin 15) : B 12 i = (certz i : ℝ) / rowScale i := by
  fin_cases i <;> simp -implicitDefEqProofs [B_unfold, Ri, mul_diagonal, ratReal_unfold, certK_unfold, certL_unfold, certe_unfold, certz_unfold, div_eq_mul_inv,
    rowScale_unfold, ← Real.sqrt_div_self]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Only the four left-kernel coordinates contribute to this commutator contraction.
private theorem contracted_derivative :
    (B *ᵥ (Matrix.of (J_D witnessP point v) *ᵥ v)) 12 = -1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    calc _ = (Real.sqrt 2 ^ 2) ^ 3 := by ring
         _ = 8 := by rw [hs]; norm_num
  simp -implicitDefEqProofs only [mulVec, dotProduct, B_row, Matrix.of_apply, Fin.sum_univ_succ]
  simp -implicitDefEqProofs only [certz_unfold, cons_val_zero, cons_val_succ, cons_val_fin_one, Rat.cast_zero, Rat.cast_one,
    Rat.cast_neg, Rat.cast_ofNat, zero_div, zero_mul, zero_add]
  simp -implicitDefEqProofs only [v_unfold, S, mulVec_diagonal, certu_unfold, colScale_unfold, rowScale_unfold, Finset.mem_insert, Finset.mem_singleton,
    cons_val_zero, cons_val_succ, cons_val_fin_one, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat,
    Rat.cast_zero, Rat.cast_one, Fin.reduceEq, or_false, ↓reduceIte, mul_zero, zero_add]
  simp -implicitDefEqProofs only [J_D_unfold, H_D_unfold, H_witness, colScale_unfold, Fin.isValue, Finset.mem_insert, Finset.mem_singleton, E_unfold, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, rowScale_unfold, certA_unfold, one_div, transpose_apply, cons_val', cons_val_fin_one, ite_mul, one_mul, _root_.add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, zero_ne_one, Fin.reduceEq, or_self,
    or_false, ↓reduceIte, cons_val_zero, one_ne_zero, or_true, cons_val_one, cons_val, smul_add, map_add, map_smul, prefixG_unfold, Fin.mk_eq_zero, Fin.mk_eq_one, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.coe_pi', ← Real.sqrt_div_self, Rat.cast_zero, mul_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Finset.univ_eq_empty, Finset.sum_empty, ContinuousLinearMap.comp_zero, smul_zero, Rat.cast_one, mul_one, add_zero, sub_self,
    _root_.zero_apply, zero_mul, Nat.reduceMod, Fin.val_eq_zero, Fin.zero_eta, zero_smul, zero_add, Finset.sum_const, Finset.card_singleton, one_smul, ContinuousLinearMap.comp_apply, _root_.smul_apply, _root_.sub_apply, mulVec_diagonal,
    Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', Fin.val_eq_zero_iff, Fin.val_succ, Fin.mk_one, Fin.succ_ne_zero, ContinuousLinearMap.comp_add, inv_one, Nat.add_eq_right,
    false_or, cons_val_succ', Nat.reduceAdd, Fin.reduceFinMk, Rat.cast_inv, map_zero, ne_eq, not_false_eq_true, div_self]
  simp -implicitDefEqProofs only [mul_add, word_mul, Fin.prod_univ_two, letterProduct_rec, letterPhase_rec,
    labels_unfold, cons_val_zero, cons_val_one, smul_smul, mul_one, one_mul, mul_neg]
  simp -implicitDefEqProofs only [rho_unfold, labels_unfold, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val, cons_val_one, mul_one, one_smul, sub_self, smul_zero, mul_zero, Complex.zero_re, zero_div, zero_mul, mul_neg, neg_mul, Complex.I_mul_I, neg_neg, neg_smul, smul_neg, one_mul, Algebra.mul_smul_comm, mul_sub, trace_smul, trace_sub,
    trace_neg, word_trace_pair, funext_iff, Fin.forall_fin_two, pow_two, reduceCtorEq, and_true, and_self, ↓reduceIte, smul_eq_mul, neg_zero, mul_add, trace_add, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_ofNat, add_zero, zero_add, sub_neg_eq_add, Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.neg_re, Complex.I_re, Complex.ofReal_re, Complex.one_re, Complex.ofReal_im, Complex.div_ofNat_im, Complex.neg_im,
    Complex.one_im, sub_zero, Complex.mul_im, Complex.re_ofNat, Complex.I_im, Complex.im_ofNat, zero_sub, and_false, Complex.ofReal_inv, Complex.sub_re, Complex.inv_re, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im]
  ring_nf; simp -implicitDefEqProofs only [h6, ← Real.sqrt_div_self]; nlinarith [hs]
private theorem coordinate_det : det B ≠ 0 ∧ det U ≠ 0 := by
  constructor
  · intro h; have hh := congrArg det coordinate_inverse.1; simp -implicitDefEqProofs [det_mul, h] at hh
  · intro h; have hh := congrArg det coordinate_inverse.2; simp -implicitDefEqProofs [det_mul, h] at hh
private theorem D_eq : D = diagonal (fun i : Fin 15 => if i = 12 then (0 : ℝ) else 1) := by ext i j; simp -implicitDefEqProofs [D_unfold, certD_unfold, ratReal_unfold, diagonal]; split_ifs <;> simp -implicitDefEqProofs
private noncomputable def normalize : (Fin 15 → Fin 15 → ℝ) →L[ℝ] (Fin 15 → Fin 15 → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => B * Matrix.of M * U
    map_add' := by intro M N; ext i j; simp -implicitDefEqProofs [mul_apply, add_mul, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c M; change B * (c • Matrix.of M) * U = _
      rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
private theorem normalize_apply (T : Fin 15 → Fin 15 → ℝ) : normalize T = B * Matrix.of T * U := rfl
private noncomputable def detForm {n : Type*} [Fintype n] [DecidableEq n] :
    (n → ℝ) [⋀^n]→L[ℝ] ℝ :=
  { (detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ) with cont := continuous_id.matrix_det }
private theorem detForm_apply {n : Type*} [Fintype n] [DecidableEq n] (M : n → n → ℝ) :
    (detForm (n := n)).1 M = det (Matrix.of M) := rfl
private noncomputable def detDiff {n : Type*} [Fintype n] [DecidableEq n] (M : n → n → ℝ) :
    (n → n → ℝ) →L[ℝ] ℝ := (detForm (n := n)).1.linearDeriv M
private theorem detDiff_unfold {n : Type*} [Fintype n] [DecidableEq n] (M : n → n → ℝ) : detDiff M = (detForm (n := n)).1.linearDeriv M := rfl

private theorem detForm_deriv {n : Type*} [Fintype n] [DecidableEq n] (M T : n → n → ℝ) :
    detDiff M T = ∑ i, det (Matrix.of (Function.update M i (T i))) := by
  simp -implicitDefEqProofs only [detDiff_unfold, ContinuousMultilinearMap.linearDeriv_apply, detForm_apply]
private theorem det_comp_strict {n : Type*} [Fintype n] [DecidableEq n]
    {f : Param → (n → n → ℝ)} {fD : Param →L[ℝ] (n → n → ℝ)} {a : Param}
    (hf : HasStrictFDerivAt f fD a) :
    HasStrictFDerivAt (fun x => det (Matrix.of (f x))) ((detDiff (f a)).comp fD) a := by
  simpa -implicitDefEqProofs only [detDiff_unfold, Function.comp_def, detForm_apply] using ((detForm (n := n)).1.hasStrictFDerivAt _).comp a hf
private noncomputable def g (α : Param) : ℝ := det (Matrix.of (normalize (J_H witnessP α)))
private noncomputable def gD (α : Param) : Param →L[ℝ] ℝ :=
  (detDiff (normalize (J_H witnessP α))).comp (normalize.comp (fderiv ℝ (J_H witnessP) α))
private theorem g_strict (α : Param) : HasStrictFDerivAt g (gD α) α := by
  unfold gD
  rw [(J_strict witnessP α).hasFDerivAt.fderiv]
  exact det_comp_strict (normalize.hasStrictFDerivAt.comp α (J_strict witnessP α))
private theorem g_zero_iff (α : Param) : g α = 0 ↔ det (J_H witnessP α) = 0 := by
  change det (B * Matrix.of (J_H witnessP α) * U) = 0 ↔ det (Matrix.of (J_H witnessP α)) = 0
  simp -implicitDefEqProofs [det_mul, coordinate_det.1, coordinate_det.2]
private theorem g_point : g point = 0 := by
  change det (B * Matrix.of (J_H witnessP point) * U) = 0
  rw [normalized_witness]; exact det_eq_zero_of_row_eq_zero 12 (by intro j; simp -implicitDefEqProofs [D_eq, diagonal])
private theorem det_derivative_D (T : Fin 15 → Fin 15 → ℝ) : detDiff D T = T 12 12 := by
  rw [detForm_deriv]
  change (∑ i, det (D.updateRow i (T i))) = T 12 12
  rw [Finset.sum_eq_single 12]
  · have hh : D.updateRow 12 (T 12) = (1 : Matrix (Fin 15) (Fin 15) ℝ).updateRow 12 (T 12) := by
      ext i j; by_cases h : i = 12 <;> simp -implicitDefEqProofs [D_eq, updateRow_apply, diagonal, one_apply, h]
    rw [hh, ← cramer_transpose_apply, transpose_one, cramer_one]; rfl
  · intro i _ hi; exact det_eq_zero_of_row_eq_zero 12 (by intro j; simp -implicitDefEqProofs [D_eq, updateRow_apply, Ne.symm hi, diagonal])
  · intro h; simp -implicitDefEqProofs at h
private theorem U_pivot : U *ᵥ Pi.single 12 1 = v := by
  unfold U v; rw [← mulVec_mulVec]; congr 1; ext i
  rw [mulVec_single_one]
  change (certN i 12 : ℝ) = (certu i : ℝ)
  exact_mod_cast (show certN i 12 = certu i from
    (show ∀ k, certN k 12 = certu k by decide +kernel) i)
private theorem normalized_pivot (T : Fin 15 → Fin 15 → ℝ) :
    normalize T 12 12 = (B *ᵥ (Matrix.of T *ᵥ v)) 12 := by
  rw [normalize_apply]
  have hh := congrFun (mulVec_single_one (B * Matrix.of T * U) 12) 12
  change ((B * Matrix.of T * U) *ᵥ Pi.single 12 1) 12 = (B * Matrix.of T * U) 12 12 at hh
  rw [← hh, ← mulVec_mulVec, ← mulVec_mulVec, U_pivot]
set_option maxRecDepth 2000 in
set_option backward.isDefEq.respectTransparency true in
private theorem gD_eval (α h : Param) : gD α h = detDiff (normalize (J_H witnessP α)) (normalize (J_D witnessP α h)) := by
  unfold gD; rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply congrArg (fun M : Fin 15 → Fin 15 → ℝ =>
    detDiff (normalize (J_H witnessP α)) (normalize M))
  ext i j
  exact J_fderiv witnessP α h i j
set_option backward.isDefEq.respectTransparency true in
private theorem gD_direction : gD point v = -1 := by
  have hn : normalize (J_H witnessP point) = D := by rw [normalize_apply]; exact normalized_witness
  rw [gD_eval, hn, det_derivative_D, normalized_pivot]
  exact contracted_derivative
private noncomputable def Q : Mat →L[ℝ] (Fin 14 → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj ((12 : Fin 15).succAbove i)).comp
      ((Matrix.mulVecLin B).toContinuousLinearMap.comp
        (rho.comp ((2 * Complex.I) • (ContinuousLinearMap.mul ℝ Mat).flip (star (circuit witnessP point)))))
private theorem Q_DF (x : Param) :
    Q (fderiv ℝ (circuit witnessP) point (U *ᵥ x)) = Fin.removeNth 12 x := by
  have hn (i : Fin 14) : (12 : Fin 15).succAbove i ≠ 12 := Fin.succAbove_ne _ _
  have hc : (2 * Complex.I) * (-Complex.I / 2) = 1 := by norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq]
  change Fin.removeNth 12 (B *ᵥ rho ((2 * Complex.I) • (fderiv ℝ (circuit witnessP) point (U *ᵥ x) * star (circuit witnessP point)))) = _
  rw [circuit_fderiv, Matrix.smul_mul, mul_assoc,
    Unitary.mul_star_self_of_mem (circuit_unitary witnessP point), mul_one,
    smul_smul, hc, one_smul, rho_E, mulVec_mulVec, mulVec_mulVec]
  change Fin.removeNth 12 ((B * Matrix.of (J_H witnessP point) * U) *ᵥ x) = _; rw [normalized_witness]
  ext i; simp -implicitDefEqProofs [D_eq, mulVec_diagonal, Fin.removeNth, hn]
private theorem Q_kernel : Q (fderiv ℝ (circuit witnessP) point v) = 0 := by
  have hn (i : Fin 14) : (12 : Fin 15).succAbove i ≠ 12 := Fin.succAbove_ne _ _
  rw [← U_pivot, Q_DF]; ext i; simp -implicitDefEqProofs [Fin.removeNth, hn]

private noncomputable def criticalL : Param →L[ℝ] (Fin 14 → ℝ) :=
  Q.comp (fderiv ℝ (circuit witnessP) point)
private noncomputable def criticalT : Param → ((Fin 14 → ℝ) × ℝ) :=
  fun α => (Q (circuit witnessP α), g α)
private theorem criticalL_apply (z : Param) :
    criticalL z = Q (fderiv ℝ (circuit witnessP) point z) := rfl
private theorem criticalL_right_inverse (y : Fin 14 → ℝ) :
    criticalL (U *ᵥ Fin.insertNth 12 0 y) = y := by
  rw [criticalL_apply]
  exact (Q_DF (Fin.insertNth 12 0 y)).trans
    (@Fin.removeNth_insertNth 14 (fun _ => ℝ) 12 0 y)
private theorem criticalL_kernel : criticalL v = 0 := by
  rw [criticalL_apply]
  exact Q_kernel
private theorem prod_range_top
    (L : Param →L[ℝ] (Fin 14 → ℝ)) (s : Param →L[ℝ] ℝ)
    (hL : ∀ y : Fin 14 → ℝ, L (U *ᵥ Fin.insertNth 12 0 y) = y)
    (hLv : L v = 0) (hs : s v = -1) :
    (L.prod s).range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  rintro ⟨y, t⟩
  refine ⟨U *ᵥ Fin.insertNth 12 0 y +
      (s (U *ᵥ Fin.insertNth 12 0 y) - t) • v, ?_⟩
  change (L (U *ᵥ Fin.insertNth 12 0 y +
      (s (U *ᵥ Fin.insertNth 12 0 y) - t) • v),
    s (U *ᵥ Fin.insertNth 12 0 y +
      (s (U *ᵥ Fin.insertNth 12 0 y) - t) • v)) = (y, t)
  apply Prod.ext
  · simp only [Prod.fst]
    rw [map_add, map_smul, hL, hLv, smul_zero, add_zero]
  · simp only [Prod.snd]
    rw [map_add, map_smul, hs]
    simp -implicitDefEqProofs only [smul_eq_mul]
    ring
private theorem criticalA_range :
    (criticalL.prod (gD point)).range = ⊤ :=
  prod_range_top criticalL (gD point) criticalL_right_inverse criticalL_kernel
    gD_direction

private theorem critical_dim_lower :
    (14 : ℝ≥0∞) ≤ dimH (circuit witnessP '' critical witnessP) := by
  have hf : HasStrictFDerivAt (circuit witnessP)
      (fderiv ℝ (circuit witnessP) point) point := by
    have h := circuit_strict witnessP point
    exact h.congr_fderiv h.hasFDerivAt.fderiv.symm
  have hT : HasStrictFDerivAt criticalT (criticalL.prod (gD point)) point := by
    change HasStrictFDerivAt (fun α => (Q (circuit witnessP α), g α))
      (criticalL.prod (gD point)) point
    exact (Q.hasStrictFDerivAt.comp point hf).prodMk (g_strict point)
  have hA : (criticalL.prod (gD point)).range = ⊤ := criticalA_range
  have hr : Set.range criticalT ∈ nhds (criticalT point) := by
    rw [← hT.map_nhds_eq_of_surj hA]
    simpa -implicitDefEqProofs only [Set.image_univ] using
      (Filter.image_mem_map (m := criticalT) (Filter.univ_mem (f := nhds point)))
  have ho : {y : Fin 14 → ℝ | (y,0) ∈ Set.range criticalT} ∈
      nhds (Q (circuit witnessP point)) := by
    have hc : Continuous (fun y : Fin 14 → ℝ => (y,(0 : ℝ))) :=
      continuous_id.prodMk continuous_const
    exact hc.continuousAt.preimage_mem_nhds
      (by simpa -implicitDefEqProofs only [criticalT, g_point] using hr)
  have hs : {y : Fin 14 → ℝ | (y,0) ∈ Set.range criticalT} ⊆
      Q '' (circuit witnessP '' critical witnessP) := by
    rintro y ⟨α,hα⟩
    refine ⟨circuit witnessP α, ⟨α, ?_, rfl⟩, congrArg Prod.fst hα⟩
    rw [critical_eq_det_zero]
    exact (g_zero_iff α).mp (congrArg Prod.snd hα)
  obtain ⟨O,hO,hopen,hpoint⟩ := mem_nhds_iff.mp ho
  have hd := Real.dimH_of_mem_nhds (hopen.mem_nhds hpoint)
  simp -implicitDefEqProofs only [Module.finrank_pi, Fintype.card_fin,
    Nat.cast_ofNat] at hd
  exact hd.symm.le.trans ((dimH_mono (hO.trans hs)).trans (Q.lipschitz.dimH_image_le _))

private theorem det_comp_analytic {n : Type*} [Fintype n] [DecidableEq n]
    {f : Param → (n → n → ℝ)} {a : Param} (hf : AnalyticAt ℝ f a) :
    AnalyticAt ℝ (fun x => det (Matrix.of (f x))) a := by
  simpa -implicitDefEqProofs only [Function.comp_def, detForm_apply] using
    ((detForm (n := n)).1.analyticAt).comp hf

private theorem g_analytic : AnalyticOnNhd ℝ g Set.univ := by
  intro a _
  have hh (l : List (Fin 15)) (M : Mat) : AnalyticAt ℝ
      (fun α : Param => l.foldr (fun k N => conjStep (witnessP k) (α k) N) M) a := by
    induction l with
    | nil => exact analyticAt_const
    | cons k l ih =>
      have hc : AnalyticAt ℝ (fun α : Param => (Real.cos (α k) : ℂ)) a :=
        (Complex.ofRealCLM.analyticAt _).comp
          (Real.analyticAt_cos.comp ((ContinuousLinearMap.proj k : Param →L[ℝ] ℝ).analyticAt a))
      have hs : AnalyticAt ℝ (fun α : Param => (Real.sin (α k) : ℂ)) a :=
        (Complex.ofRealCLM.analyticAt _).comp
          (Real.analyticAt_sin.comp ((ContinuousLinearMap.proj k : Param →L[ℝ] ℝ).analyticAt a))
      simp -implicitDefEqProofs only [List.foldr_cons, conjStep]
      exact (((analyticAt_const.add hc).div analyticAt_const (by norm_num)).smul ih |>.add
        (((analyticAt_const.sub hc).div analyticAt_const (by norm_num)).smul
          ((analyticAt_const.mul ih).mul analyticAt_const))).sub
        (((hs.div analyticAt_const (by norm_num)).mul analyticAt_const).smul
          ((analyticAt_const.mul ih).sub (ih.mul analyticAt_const)))
  have hj : AnalyticAt ℝ (J_H witnessP) a := by
    apply AnalyticAt.pi; intro i
    apply AnalyticAt.pi; intro j
    simp_rw [J_recurrence]
    exact ((ContinuousLinearMap.proj i : Param →L[ℝ] ℝ).analyticAt _).comp
      ((rho.analyticAt _).comp (hh _ _))
  exact det_comp_analytic ((normalize.analyticAt _).comp hj)

private theorem full_rank_ae :
    ∀ᵐ α ∂(volume : Measure Param), derivativeRank witnessP α = 15 := by
  have hn : ∃ a, g a ≠ 0 := by
    by_contra! h
    have he : g = fun _ => 0 := funext h
    have hd : gD point = 0 := (g_strict point).hasFDerivAt.unique
      (by rw [he]; exact hasFDerivAt_const (0 : ℝ) point)
    have hv := congrArg (fun L : Param →L[ℝ] ℝ => L v) hd
    rw [gD_direction] at hv
    norm_num at hv
  obtain ⟨a,ha⟩ := hn
  filter_upwards [D5.S3.Analytic.NullSets.AnalyticZeroSetNull.ae_ne_zero_of_analytic g_analytic ha] with α hα
  rw [derivative_rank]
  simpa -implicitDefEqProofs only [Fintype.card_fin] using
    Matrix.rank_of_det_ne_zero (mt (g_zero_iff α).mpr hα)

theorem result : ¬ claim := by
  intro h
  have hu := h witnessP full_rank_ae
  have hb := critical_dim_lower.trans hu
  norm_num at hb

end D5.S3.Quantum.Information.PauliRotationCriticalValues
