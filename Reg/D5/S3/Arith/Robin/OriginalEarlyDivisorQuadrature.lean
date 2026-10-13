import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open _root_.D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℝ × ℝ) × (ℕ → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ t => ((discretePhi t - mixedG t - boundaryHeight t * endpointSum t,
    discretePhi t - mixedG t - earlyError t),
    fun d => Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => ((0, 0), fun _ => -1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 256 ≤ t →
    (R.readout () () t).1.2 = 0 ∧
    (∀ d ∈ Finset.Icc 1 (divisorCutoff t), 0 ≤ (R.readout () () t).2 d) ∧
    |(R.readout () () t).1.1| ≤ (1 / 6 : ℝ) *
      ∑ d ∈ Finset.Icc 1 (divisorCutoff t), |(ArithmeticFunction.moebius d : ℝ)| * d *
        (R.readout () () t).2 d ∧
    |(R.readout () () t).1.1| ≤ (1 / 6 : ℝ) * t ^ (-62 / 125 : ℝ) * Real.log t

private theorem actual_bridge :
    (type_of% (@original_early_quadrature)) ↔ arena.Law actual := by
  constructor
  · intro h t ht
    obtain ⟨he, hp, hs, hd⟩ := h ht
    refine ⟨?_, hp, hs, hd⟩
    change discretePhi t - mixedG t - earlyError t = 0
    linarith
  · intro h t ht
    obtain ⟨he, hp, hs, hd⟩ := h ht
    refine ⟨?_, hp, hs, hd⟩
    change discretePhi t - mixedG t - earlyError t = 0 at he
    linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd : 1 ∈ Finset.Icc 1 (divisorCutoff (256 : ℝ)) := by
    simp only [Finset.mem_Icc, le_refl, true_and, divisorCutoff]
    apply (Nat.le_floor_iff (by positivity)).mpr
    simpa only [Nat.cast_one] using
      (Real.one_le_rpow (x := 256) (z := (151 / 500 : ℝ)) (by norm_num) (by norm_num))
  have hh := (h (t := 256) (by norm_num)).2.1 1 hd
  change (0 : ℝ) ≤ -1 at hh
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 256, 512, ?_⟩
  intro he
  have h1 := congrArg (fun v : (ℝ × ℝ) × (ℕ → ℝ) => v.2 1) he
  have h2 := congrArg (fun v : (ℝ × ℝ) × (ℕ → ℝ) => v.2 2) he
  simp only [actual, realize, Nat.cast_one, Nat.cast_ofNat] at h1 h2
  change Real.log ((256 : ℝ) / 1) * (256 : ℝ) ^ (-11 / 10 : ℝ) -
      boundaryHeight 256 / 256 =
    Real.log ((512 : ℝ) / 1) * (512 : ℝ) ^ (-11 / 10 : ℝ) -
      boundaryHeight 512 / 512 at h1
  change Real.log ((256 : ℝ) / 2) * (256 : ℝ) ^ (-11 / 10 : ℝ) -
      boundaryHeight 256 / 256 =
    Real.log ((512 : ℝ) / 2) * (512 : ℝ) ^ (-11 / 10 : ℝ) -
      boundaryHeight 512 / 512 at h2
  rw [div_one, div_one] at h1
  rw [Real.log_div (by norm_num : (256 : ℝ) ≠ 0) (by norm_num),
    Real.log_div (by norm_num : (512 : ℝ) ≠ 0) (by norm_num)] at h2
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hp := Real.rpow_lt_rpow_of_neg (x := 256) (y := 512)
    (by norm_num) (by norm_num) (show (-11 / 10 : ℝ) < 0 by norm_num)
  nlinarith

def family : Registration arena (type_of% (@original_early_quadrature)) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨@original_early_quadrature |> actual_bridge.mp, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_early_quadrature)
    (type_of% (realize signature
      (fun _ _ t => ((discretePhi t - mixedG t - boundaryHeight t * endpointSum t,
        discretePhi t - mixedG t - earlyError t),
        fun d => Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t))
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature.original_early_quadrature.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => ((discretePhi t - mixedG t - boundaryHeight t * endpointSum t,
      discretePhi t - mixedG t - earlyError t),
      fun d => Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature
