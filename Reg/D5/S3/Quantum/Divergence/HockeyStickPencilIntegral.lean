import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.HockeyStickPencilIntegral

/-! Source-bound audits of the logarithm in the two pencil integral formulas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open Matrix MeasureTheory RHLinalg Set
open scoped BigOperators ComplexOrder ENNReal MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.HockeyStickPencilIntegral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

private def zeroLog : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev shiftedArena : Arena where
  signature := signature
  Law F := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ}
    {r : ℝ} (hX : (A + r • (1 : Matrix n n ℂ)).PosDef)
    (hY : (B + r • (1 : Matrix n n ℂ)).PosDef),
    let hA : A.IsHermitian := by
      simpa only [add_sub_cancel_right] using
        hX.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all r))
    let hB : B.IsHermitian := by
      simpa only [add_sub_cancel_right] using
        hY.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all r))
    let R := (CFC.sqrt (A + r • (1 : Matrix n n ℂ)))⁻¹
    let hK := isHermitian_conjTranspose_mul_mul R (hB.sub hA)
    let hP (t : ℝ) := (hA.add ((hB.sub hA).smul (IsSelfAdjoint.all t))).add
      (isHermitian_one.smul (IsSelfAdjoint.all r))
    Integrable (fun t => pencilWeight t * (negIndex (hP t) : ℝ)) ∧
      (∫ t, pencilWeight t * (negIndex (hP t) : ℝ)) =
        ∑ i, (F.readout () () (1 + hK.eigenvalues i) -
          hK.eigenvalues i / (1 + hK.eigenvalues i))

abbrev integratedArena : Arena where
  signature := signature
  Law F := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef),
    let hM (t : ℝ) := hA.isHermitian.add
      ((hB.isHermitian.sub hA.isHermitian).smul (IsSelfAdjoint.all t))
    (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart (hM t)))) =
      ∫⁻ r in Ioi (0 : ℝ),
        let R := (CFC.sqrt (A + r • (1 : Matrix n n ℂ)))⁻¹
        let hK := isHermitian_conjTranspose_mul_mul R (hB.isHermitian.sub hA.isHermitian)
        ENNReal.ofReal (∑ i, (F.readout () () (1 + hK.eigenvalues i) -
          hK.eigenvalues i / (1 + hK.eigenvalues i)))

private abbrev ScalarMatrix := Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ

private theorem two_posDef : (1 + 1 : ScalarMatrix.{u}).PosDef :=
  Matrix.PosDef.one.add Matrix.PosDef.one

private theorem one_shift_posDef {r : ℝ} (hr : 0 ≤ r) :
    ((1 : ScalarMatrix.{u}) + r • 1).PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.PosSemidef.one.smul hr)

private theorem scalar_normalized_eigenvalue_pos {r : ℝ} (hr : 0 ≤ r)
    (i : ULift.{u} Unit) :
    let R := (CFC.sqrt ((1 : ScalarMatrix.{u}) + r • 1))⁻¹
    0 < (isHermitian_conjTranspose_mul_mul R
      (two_posDef.{u}.isHermitian.sub Matrix.PosDef.one.isHermitian)).eigenvalues i := by
  let R := (CFC.sqrt ((1 : ScalarMatrix.{u}) + r • 1))⁻¹
  have hR : IsUnit R := Matrix.isUnit_nonsing_inv_iff.mpr
    (CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr (one_shift_posDef hr).isStrictlyPositive)
  have hd : ((1 + 1 : ScalarMatrix.{u}) - 1).PosDef := by
    rw [add_sub_cancel_right]
    exact Matrix.PosDef.one
  exact (hd.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hR)).eigenvalues_pos i

private theorem shifted_rejects_zeroLog : ¬ shiftedArena.{u}.Law zeroLog := by
  intro h
  let hA : (1 : ScalarMatrix.{u}).IsHermitian := Matrix.PosDef.one.isHermitian
  let hB := two_posDef.{u}.isHermitian
  have hr : (0 : ℝ) < 1 := zero_lt_one
  have hX := one_shift_posDef.{u} hr.le
  have hY : ((1 + 1 : ScalarMatrix.{u}) + (1 : ℝ) • 1).PosDef :=
    two_posDef.add (Matrix.PosDef.one.smul hr)
  have actualEq := (integral_weighted_negIndex_shifted_pencil hX hY).2
  have zeroEq := (@h (ULift.{u} Unit) _ _ 1 (1 + 1) 1 hX hY).2
  let R := (CFC.sqrt ((1 : ScalarMatrix.{u}) + (1 : ℝ) • 1))⁻¹
  let z := (isHermitian_conjTranspose_mul_mul R (hB.sub hA)).eigenvalues (ULift.up ())
  have he := zeroEq.symm.trans actualEq
  simp only [Fintype.sum_subsingleton _ (ULift.up () : ULift.{u} Unit)] at he
  change 0 - z / (1 + z) = Real.log (1 + z) - z / (1 + z) at he
  have hz : 0 < z := scalar_normalized_eigenvalue_pos hr.le (ULift.up ())
  have hx : 0 < 1 + z := add_pos zero_lt_one hz
  have hinv := inv_lt_one_of_one_lt₀ (lt_add_of_pos_right 1 hz)
  have hlog := Real.log_lt_sub_one_of_pos (inv_pos.mpr hx) hinv.ne
  rw [Real.log_inv] at hlog
  have hquot : z / (1 + z) = 1 - (1 + z)⁻¹ := by
    field_simp [hx.ne']
    ring
  have hActual : 0 < Real.log (1 + z) - z / (1 + z) := by
    rw [hquot]
    linarith only [hlog]
  have hZeroLog : 0 - z / (1 + z) ≤ 0 := sub_nonpos.mpr (div_nonneg hz.le hx.le)
  exact (not_le_of_gt hActual) (he ▸ hZeroLog)

private theorem scalar_pencil_eigenvalue (t : ℝ) (i : ULift.{u} Unit) :
    (Matrix.PosDef.one.isHermitian.add
      ((two_posDef.{u}.isHermitian.sub Matrix.PosDef.one.isHermitian).smul
        (IsSelfAdjoint.all t))).eigenvalues i = 1 + t := by
  let hM := Matrix.PosDef.one.isHermitian.add
    ((two_posDef.{u}.isHermitian.sub Matrix.PosDef.one.isHermitian).smul (IsSelfAdjoint.all t))
  have htrace := congrArg Complex.re hM.trace_eq_sum_eigenvalues
  change (Matrix.trace ((1 : ScalarMatrix.{u}) + t • ((1 + 1) - 1))).re =
    (∑ j, (hM.eigenvalues j : ℂ)).re at htrace
  rw [Fintype.sum_subsingleton _ i] at htrace
  simpa [add_sub_cancel_right, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Complex.real_smul] using htrace.symm

private theorem scalar_pencil_integral_pos :
    0 < (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart
      (Matrix.PosDef.one.isHermitian.add
        ((two_posDef.{u}.isHermitian.sub Matrix.PosDef.one.isHermitian).smul
          (IsSelfAdjoint.all t)))))) := by
  let f (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (pencilWeight t * (1 + t)⁻)
  have hf : Measurable f := by unfold f pencilWeight; fun_prop
  have hs : Ioo (-3 : ℝ) (-2) ⊆ Function.support f := by
    intro t ht
    have ht0 : t < 0 := ht.2.trans (by norm_num)
    have hw : 0 < pencilWeight t := by
      unfold pencilWeight
      exact one_div_pos.mpr
        (mul_pos (abs_pos.mpr ht0.ne) (sq_pos_of_ne_zero (by linarith)))
    have hn : 0 < (1 + t)⁻ := by
      change 0 < max (-(1 + t)) 0
      exact lt_max_of_lt_left (by linarith [ht.2])
    exact (ENNReal.ofReal_pos.mpr (mul_pos hw hn)).ne'
  have hvol : 0 < volume (Ioo (-3 : ℝ) (-2)) := by
    rw [Real.volume_Ioo]
    norm_num
  have hp := (lintegral_pos_iff_support hf).mpr (hvol.trans_le (measure_mono hs))
  convert hp using 2
  funext t
  dsimp only [f]
  rw [rtrace_hermNegPart, Fintype.sum_subsingleton _ (ULift.up () : ULift.{u} Unit),
    scalar_pencil_eigenvalue]

private theorem integrated_rejects_zeroLog : ¬ integratedArena.{u}.Law zeroLog := by
  intro h
  let hA : (1 : ScalarMatrix.{u}).PosSemidef := Matrix.PosDef.one.posSemidef
  let hB := two_posDef.{u}.posSemidef
  have he := @h (ULift.{u} Unit) _ _ 1 (1 + 1) hA hB
  have hz : (∫⁻ r in Ioi (0 : ℝ),
      let R := (CFC.sqrt ((1 : ScalarMatrix.{u}) + r • 1))⁻¹
      let hK := isHermitian_conjTranspose_mul_mul R (hB.isHermitian.sub hA.isHermitian)
      ENNReal.ofReal (∑ i, (zeroLog.readout () () (1 + hK.eigenvalues i) -
        hK.eigenvalues i / (1 + hK.eigenvalues i)))) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp only
    simp only [Fintype.sum_subsingleton _ (ULift.up () : ULift.{u} Unit),
      zeroLog, realize, zero_sub]
    apply ENNReal.ofReal_eq_zero.mpr
    have hp := scalar_normalized_eigenvalue_pos (le_of_lt hr) (ULift.up () : ULift.{u} Unit)
    exact neg_nonpos.mpr (div_nonneg hp.le (add_nonneg zero_le_one hp.le))
  change (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart
      (hA.isHermitian.add ((hB.isHermitian.sub hA.isHermitian).smul
        (IsSelfAdjoint.all t)))))) = _ at he
  exact (scalar_pencil_integral_pos.{u}).ne' (he.trans hz)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let j : ULift.{0} Unit := ULift.up ()
  let R : ScalarMatrix.{0} := (CFC.sqrt ((1 : ScalarMatrix.{0}) + (1 : ℝ) • 1))⁻¹
  let hA : (1 : ScalarMatrix.{0}).IsHermitian := Matrix.PosDef.one.isHermitian
  let hEqual := isHermitian_conjTranspose_mul_mul R (hA.sub hA)
  let hUnequal := isHermitian_conjTranspose_mul_mul R (two_posDef.{0}.isHermitian.sub hA)
  have hZero := hEqual.eigenvalues_eq_zero_iff.mpr (by simp)
  have hEqualAtJ : hEqual.eigenvalues j = 0 := congrFun hZero j
  refine ⟨(), 1 + hEqual.eigenvalues j, 1 + hUnequal.eigenvalues j, ?_⟩
  change Real.log (1 + hEqual.eigenvalues j) ≠ Real.log (1 + hUnequal.eigenvalues j)
  rw [hEqualAtJ, add_zero, Real.log_one]
  have hPos : 0 < hUnequal.eigenvalues j := scalar_normalized_eigenvalue_pos zero_le_one j
  exact (Real.log_pos (lt_add_of_pos_right 1 hPos)).ne

def shiftedFamily : Registration shiftedArena.{u}
    (type_of% @integral_weighted_negIndex_shifted_pencil.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_weighted_negIndex_shifted_pencil, zeroLog, shifted_rejects_zeroLog⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    shiftedArena.Law actual zeroLog shifted_rejects_zeroLog
  dependence := dependence

def integratedFamily : Registration integratedArena.{u}
    (type_of% @lintegral_weighted_negPart_pencil.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lintegral_weighted_negPart_pencil, zeroLog, integrated_rejects_zeroLog⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integratedArena.Law actual zeroLog integrated_rejects_zeroLog
  dependence := dependence

set_option linter.style.longLine false in
def shiftedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_weighted_negIndex_shifted_pencil.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.HockeyStickPencilIntegral.integral_weighted_negIndex_shifted_pencil.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.HockeyStickPencilIntegral.shiftedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shiftedArena⟩
  objectArena := .source ⟨shiftedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftedArena ⟨shiftedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option linter.style.longLine false in
def integratedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lintegral_weighted_negPart_pencil.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.HockeyStickPencilIntegral.lintegral_weighted_negPart_pencil.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.HockeyStickPencilIntegral.integratedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integratedArena⟩
  objectArena := .source ⟨integratedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integratedArena ⟨integratedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms shiftedAudit
#print axioms integratedAudit

end Reg.D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
