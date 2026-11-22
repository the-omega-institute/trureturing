import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedTailFiniteWindow
import Reg.D5.S3.Weil.Mertens.WeightedTailInverse

/-! The unweighted tail at the left endpoint is the observed output. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedTailInverse (a)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail)
open _root_.D5.S3.Weil.Mertens.WeightedTailFiniteWindow (neg_sqrt_mul_tail_le)
open _root_.Reg.D5.S3.Weil.Mertens.WeightedTailInverse (signature actual rejected inverseEvidence)

namespace Reg.D5.S3.Weil.Mertens.WeightedTailFiniteWindow

def arena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ → ℝ} {x B A D : ℝ}
    (_ : exp 1 ≤ x) (_ : x ≤ B) (_ : 0 ≤ A) (_ : IntegrableOn k (Ioi x))
    (_ : ∀ t ∈ Icc x B, -A / (sqrt t * log t) ≤ weightedTail k t)
    (_ : -D / sqrt B ≤ tail k B - a B * weightedTail k B),
    -sqrt x * R.readout () () k x ≤
      A * (log x / (1 + log x) + (2 / log x) * (1 - sqrt x / sqrt B)) +
        D * sqrt x / sqrt B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := fun _ => 0) (x := exp 1) (B := exp 1) (A := 0) (D := 0)
    le_rfl le_rfl le_rfl (by simp) (by simp [weightedTail]) (by simp [tail, weightedTail])
  have hnonpos : sqrt (exp 1) ≤ 0 := by
    simpa [rejected, realize] using hbad
  exact (not_le_of_gt (sqrt_pos.2 (exp_pos 1))) hnonpos

def evidence : Registration arena (type_of% @neg_sqrt_mul_tail_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neg_sqrt_mul_tail_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := inverseEvidence.dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neg_sqrt_mul_tail_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedTailFiniteWindow.neg_sqrt_mul_tail_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedTailFiniteWindow.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedTailFiniteWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Weil.Mertens.WeightedTailFiniteWindow
