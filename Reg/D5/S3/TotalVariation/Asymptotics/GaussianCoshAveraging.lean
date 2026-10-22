import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
open _root_.D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging
open StatLean.HypothesisTesting LeanInformationAudit MeasureTheory Set Filter Topology
open Classical

noncomputable section
namespace Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging

private def witnessB (n : ℕ) : ℝ := Real.log 4 / ((n : ℝ) + 2) ^ 2
private def witnessQ (n : ℕ) : ℝ := Real.sqrt (2 * Real.log 4 * (1 - 1 / ((n : ℝ) + 2)))

private theorem witness_log_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

private theorem witness_b_pos (n : ℕ) : 0 < witnessB n := by
  unfold witnessB
  have hn : 0 < (n : ℝ) + 2 := by positivity
  exact div_pos witness_log_pos (sq_pos_of_pos hn)

private theorem witness_q_pos (n : ℕ) : 0 < witnessQ n := by
  have hn : 1 < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  apply Real.sqrt_pos.2
  apply mul_pos (mul_pos (by norm_num) witness_log_pos)
  exact sub_pos.mpr ((div_lt_one (by positivity)).2 hn)

private theorem witness_n_limit : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
  tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

private theorem witness_b_limit : Tendsto witnessB atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp witness_n_limit
  unfold witnessB
  simpa [div_eq_mul_inv, inv_pow, Function.comp_apply] using
    (tendsto_const_nhds (x := Real.log 4)).mul (hi.pow 2)

private theorem witness_q_limit :
    Tendsto witnessQ atTop (𝓝 (Real.sqrt (2 * Real.log 4))) := by
  have hi := tendsto_inv_atTop_zero.comp witness_n_limit
  have h := (tendsto_const_nhds (x := 2 * Real.log 4)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hi)
  unfold witnessQ
  simpa [one_div, Function.comp_apply] using h.sqrt

private theorem witness_offset (n : ℕ) : sourceOffset (witnessQ n) (witnessB n) = (n : ℝ) + 2 := by
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hq : 0 < 2 * Real.log 4 * (1 - 1 / ((n : ℝ) + 2)) := by
    apply mul_pos (mul_pos (by norm_num) witness_log_pos)
    exact sub_pos.mpr ((div_lt_one hn).2 (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  unfold sourceOffset witnessQ witnessB
  rw [Real.sq_sqrt hq.le]
  field_simp [witness_log_pos.ne', hn.ne']
  ring

private theorem witness_regime :
    Tendsto (fun n => sourceOffset (witnessQ n) (witnessB n)) atTop atTop := by
  simpa only [witness_offset] using witness_n_limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ q => coshCoefficient q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def analyticClauses (q b : ℕ → ℝ) : Prop :=
  ∀ n, (∀ v : ℝ, Integrable (fun u : ℝ => stdNormalPDF u *
      max (Real.exp (affineOffset (b n) (sourceOffset (q n) (b n)) v) - Real.cosh (q n * u)) 0)) ∧
    Integrable (fun v : ℝ => stdNormalPDF v *
      gaussianCoshIntegral (q n) (affineOffset (b n) (sourceOffset (q n) (b n)) v)) ∧
    Integrable (fun v : ℝ => stdNormalPDF v *
      max (affineOffset (b n) (sourceOffset (q n) (b n)) v) 0 ^ (3 / 2 : ℝ)) ∧
    0 < positiveMoment (b n) (sourceOffset (q n) (b n)) ∧
    0 < coshCoefficient (q n) ∧
    0 < coshCoefficient (q n) * positiveMoment (b n) (sourceOffset (q n) (b n))

def arena : Arena where
  signature := signature
  Law F := ∀ q b : ℕ → ℝ,
    (∀ n, 0 < q n) → (∀ n, 0 < b n) →
    Tendsto q atTop (𝓝 (Real.sqrt (2 * Real.log 4))) → Tendsto b atTop (𝓝 0) →
    (Tendsto (fun n => sourceOffset (q n) (b n)) atTop atTop ∨
      Tendsto (fun n => sourceOffset (q n) (b n)) atTop atBot) →
    analyticClauses q b ∧ Tendsto
      (fun n => averagedCosh (q n) (b n) (sourceOffset (q n) (b n)) /
        (F.readout () () (q n) * positiveMoment (b n) (sourceOffset (q n) (b n))))
      atTop (𝓝 1)

private theorem actual_law : arena.Law actual := by
  intro q b hq hb hq0 hb0 hr
  exact gaussian_cosh_source_relative q b hq hb hq0 hb0 hr

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h witnessQ witnessB witness_q_pos witness_b_pos witness_q_limit witness_b_limit
    (Or.inl witness_regime)).2
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := by
    simpa [rejected, realize] using hh
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hz)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change coshCoefficient 1 ≠ coshCoefficient 2
  have hp : 0 < 4 * Real.sqrt 2 * stdNormalPDF 0 := by
    unfold stdNormalPDF
    positivity
  unfold coshCoefficient
  norm_num
  linarith

def family : Registration arena (type_of% (@gaussian_cosh_source_relative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_cosh_source_relative) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging.unit
  realizationName := `Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => coshCoefficient q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging
