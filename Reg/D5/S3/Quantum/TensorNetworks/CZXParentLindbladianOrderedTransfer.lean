import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
import Reg.Support.SingleDependentReadout

/-! Source-family observations of the actual CZX evolution and trace distance. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped ComplexConjugate

private abbrev Config (m : ℕ) := Fin (2 * m) → Fin 2
private abbrev Operator (m : ℕ) := Matrix (Config m) (Config m) ℂ

private lemma exp_neg_log_four : Real.exp (-Real.log 4) = 1 / 4 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

private lemma four_site_entry (t : ℝ) :
    evolution 4 t (initial 2) (fun _ => 1) (fun _ => 0) =
      (((1 + Real.exp (-t) ^ 2) / 32 : ℝ) : ℂ) := by
  let u : Config 2 := fun _ => 1
  let v : Config 2 := fun _ => 0
  have hne : u ≠ v := fun h => (by decide : (1 : Fin 2) ≠ 0) (congrFun h 0)
  have hdiag : czxUnitary 4 u v = 1 := by
    unfold czxUnitary cz
    rw [Matrix.diagonal_mul]
    norm_num [u, v, tensorX]
  have hw (ρ : ℝ) :
      Matrix.trace (word ρ 2 (blocks 2 v)) = 2 + 2 * ρ ^ 2 := by
    have hv : blocks 2 v = fun _ => (0, 0) := by
      funext k
      fin_cases k <;> rfl
    rw [hv]
    simp [word, letter, Fin.init, Matrix.trace, Fin.sum_univ_two]
    ring
  change evolution 4 t (initial 2) u v = _
  rw [evolved_initial_transfer 2 (by decide), Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply_ne hne, Matrix.mul_diagonal, hdiag, hw]
  push_cast
  ring

abbrev operatorSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) Operator

def operatorActual : Realization operatorSignature :=
  realize operatorSignature (fun _ m t => evolution (2 * m) t (initial m)) (fun e => nomatch e)

def operatorRejected : Realization operatorSignature :=
  realize operatorSignature
    (fun _ m t => evolution (2 * m) t (initial m) + 1) (fun e => nomatch e)

abbrev operatorArena : Arena where
  signature := operatorSignature
  Law R := ∀ (m : ℕ) (_hm : 2 ≤ m) (t : ℝ),
    R.readout () m t = ((4 : ℂ) ^ m)⁻¹ •
      (1 + czxUnitary (2 * m) * Matrix.diagonal (fun x =>
        (((2 : ℝ)⁻¹ ^ m * Matrix.trace (word (Real.exp (-t)) m (blocks m x))) : ℂ)))

private lemma operator_rejected : ¬ operatorArena.Law operatorRejected := by
  intro h
  have he := h 2 (by decide) 0
  change evolution 4 0 (initial 2) + 1 = _ at he
  rw [← evolved_initial_transfer 2 (by decide) 0] at he
  have hz : (1 : Operator 2) = 0 := add_left_cancel (he.trans (add_zero _).symm)
  exact one_ne_zero hz

private lemma operator_dependence : ObservationalDependence operatorSignature operatorActual := by
  intro i
  refine ⟨2, 0, Real.log 4, ?_⟩
  intro h
  have he := congrArg (fun M : Operator 2 => M (fun _ => 1) (fun _ => 0)) h
  change evolution 4 0 (initial 2) (fun _ => 1) (fun _ => 0) =
    evolution 4 (Real.log 4) (initial 2) (fun _ => 1) (fun _ => 0) at he
  rw [four_site_entry, four_site_entry, exp_neg_log_four] at he
  norm_num at he

def operatorFamily : Registration operatorArena (type_of% (@evolved_initial_transfer)) where
  actual := operatorActual
  bridge := Iff.rfl
  variation := ⟨@evolved_initial_transfer, operatorRejected, operator_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    operatorArena.Law operatorActual operatorRejected operator_rejected
  dependence := operator_dependence

def operatorRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@evolved_initial_transfer) (Realization operatorSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.operatorUnit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.operatorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨operatorArena⟩
  objectArena := .source ⟨operatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source operatorArena ⟨operatorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize operatorSignature
    (fun _ m t => evolution (2 * m) t (initial m)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private lemma distance_at_zero : (7 : ℝ) / 16 ≤ delta 4 0 := by
  let X := tensorX 8
  have hx : Xᴴ * X = 1 := mul_eq_one_comm.mp (tensor_x_unitary 8)
  have hu : Xᴴ ∈ Matrix.unitaryGroup (Config 4) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hx
  have hzero : evolution 8 0 (initial 4) = initial 4 := by
    ext x y
    simp [evolution]
  have hd : initial 4 - stationary 4 =
      (1 / 256 : ℂ) • (X - (1 / 8 : ℂ) • czxUnitary 8) := by
    rw [initial, stationary, ← smul_sub, add_sub_add_left_eq_sub]
    norm_num [X]
  have hcz : Matrix.trace (Xᴴ * czxUnitary 8) = Matrix.trace (cz 8) := by
    change Matrix.trace (Xᴴ * (cz 8 * X)) = _
    rw [Matrix.trace_mul_comm, mul_assoc]
    change Matrix.trace (cz 8 * (tensorX 8 * (tensorX 8)ᴴ)) = _
    rw [tensor_x_unitary, mul_one]
  have htr : (Matrix.trace (cz 8)).re ≤ 256 := by
    simp only [cz, Matrix.trace_diagonal, Complex.re_sum]
    calc
      _ ≤ ∑ _ : Config 4, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        exact (Complex.re_le_norm _).trans (by simp [norm_pow])
      _ = _ := by norm_num [Config, Fintype.card_fun]
  have hre : (Matrix.trace (Xᴴ * (evolution 8 0 (initial 4) - stationary 4))).re ≥
      (7 : ℝ) / 8 := by
    rw [hzero, hd, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, hx,
      Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, hcz, Matrix.trace_one]
    norm_num [Config, Fintype.card_fun, smul_eq_mul, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.div_re, Complex.div_im]
    linarith
  have hmax := (traceNorm_eq_max_re_tr_U
    (evolution 8 0 (initial 4) - stationary 4)).2
      (show (Matrix.trace (Xᴴ * (evolution 8 0 (initial 4) - stationary 4))).re ∈ _ from
        ⟨⟨Xᴴ, hu⟩, rfl⟩)
  unfold delta
  linarith

private lemma distance_at_log_four : delta 4 (Real.log 4) < (7 : ℝ) / 16 := by
  have h := fixed_time_delta_upper 4 (by decide) (Real.log 4) (Real.log_pos (by norm_num))
  rw [exp_neg_log_four] at h
  have hg := annealed_growth (1 / 4) (by norm_num) (by norm_num) 4 0
  have hs : Real.sqrt (1 + 3 * (1 / 4 : ℝ) ^ 2) < 5 / 4 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    norm_num
  have hb : growthFactor (1 / 4) / 2 ≤ (5 : ℝ) / 8 := by linarith [hg.2.1]
  have hp : 0 ≤ growthFactor (1 / 4) / 2 := div_nonneg hg.1.le (by norm_num)
  have hpow := pow_le_pow_left₀ hp hb 4
  linarith

abbrev distanceSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def distanceActual : Realization distanceSignature :=
  realize distanceSignature (fun _ m t => delta m t) (fun e => nomatch e)

def distanceRejected : Realization distanceSignature :=
  realize distanceSignature
    (fun _ m t => 2 * (growthFactor (Real.exp (-t)) / 2) ^ m + 1) (fun e => nomatch e)

abbrev distanceArena : Arena where
  signature := distanceSignature
  Law R := ∀ (m : ℕ) (_hm : 2 ≤ m) (t : ℝ) (_ht : 0 < t),
    R.readout () m t ≤ 2 * (growthFactor (Real.exp (-t)) / 2) ^ m

private lemma distance_rejected : ¬ distanceArena.Law distanceRejected := by
  intro h
  have he := h 2 (by decide) 1 (by norm_num)
  change 2 * (growthFactor (Real.exp (-1)) / 2) ^ 2 + 1 ≤
    2 * (growthFactor (Real.exp (-1)) / 2) ^ 2 at he
  linarith

private lemma distance_dependence : ObservationalDependence distanceSignature distanceActual := by
  intro i
  refine ⟨4, 0, Real.log 4, ?_⟩
  change delta 4 0 ≠ delta 4 (Real.log 4)
  exact ne_of_gt (distance_at_log_four.trans_le distance_at_zero)

def distanceFamily : Registration distanceArena (type_of% (@fixed_time_delta_upper)) where
  actual := distanceActual
  bridge := Iff.rfl
  variation := ⟨@fixed_time_delta_upper, distanceRejected, distance_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    distanceArena.Law distanceActual distanceRejected distance_rejected
  dependence := distance_dependence

def distanceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_time_delta_upper) (Realization distanceSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.distanceUnit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.distanceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨distanceArena⟩
  objectArena := .source ⟨distanceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source distanceArena ⟨distanceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize distanceSignature (fun _ m t => delta m t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
