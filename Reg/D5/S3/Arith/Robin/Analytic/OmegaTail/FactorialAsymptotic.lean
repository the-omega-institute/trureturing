import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic
import Reg.Support.SingleDependentReadout

/-! The fixed-order logarithmic rate as a dependent convergence readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve (tailCount)
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic (factorial_tail_asymptotic)

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (r : ℕ), 2 ≤ r →
    (∀ᶠ x : ℝ in atTop, 0 < tailCount r x) ∧
    O.readout () ()
      (fun x : ℝ => log (tailCount r x : ℝ) / (log x / log (log x) ^ (((r : ℝ) + 1) / 2)))
      atTop (𝓝 (π * sqrt (2 * (r.factorial : ℝ) / 3)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 2 (by decide)).2

def family : Registration arena (type_of% @factorial_tail_asymptotic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@factorial_tail_asymptotic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have h : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@factorial_tail_asymptotic) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic.factorial_tail_asymptotic.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialAsymptotic
