import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.CausalKernel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology ArithmeticFunction
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.CausalKernel

/- Compiled source-owner audit attempt; four-slot registration unfinished.
The selected existing template is DependentFamily.realize, enrolled through
Reg.Support.DependentFamily. The actual readout is the literal causal r.
The exact source bridge below retains the origin, every real interval,
actual rSlope derivative, Integrable r, Integrable (deriv r), and both
4*gamma+16 budgets. There is no assumed-regularity supplier telescope.
Whole-family variation and sensitivity below use the failed origin value
of r+1. Actual observational dependence of the literal r and a lawful full
sourceSelection/current binding remain unpaid. These are required proof/
binding obligations, not asserted interface limitations or compiler errors.
Continuation is unknown. No incomplete Contract.Registration is fabricated,
and no declared_validated status is claimed. The unfinished registration is
tracked at https://github.com/the-omega-institute/trureturing/issues/25738. -/

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => r t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := Continuous (V.readout () ()) ∧ (V.readout () ()) 0 = 0 ∧
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (V.readout () ()) a b) ∧
    (∀ᵐ t : ℝ, HasDerivAt (V.readout () ()) (rSlope t) t) ∧
    Integrable (V.readout () ()) ∧ Integrable (deriv (V.readout () ())) ∧
    (∫ t : ℝ, |(V.readout () ()) t|) ≤ 4 * gamma + 16 ∧
    (∫ t : ℝ, |deriv (V.readout () ()) t|) ≤ 4 * gamma + 16

private theorem actual_law : arena.Law actual := causal_kernel

private theorem sourceBridge :
    (type_of% (@causal_kernel)) ↔ arena.Law actual := Iff.rfl

def rejected : Realization signature :=
  realize signature (fun _ _ t => r t + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.2.1
  have ha := causal_kernel.2.1
  change r 0 + 1 = 0 at he
  linarith

private theorem variation : Variation arena actual := ⟨actual_law, rejected, rejected_law⟩

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.CausalKernel
