import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ThetaTailRegularity
import Reg.Support.SingleDependentReadout

/-! Source-faithful observations for actual theta-tail regularity. -/

namespace Reg.D5.S3.Weil.Mertens.ThetaTailRegularity

open Set MeasureTheory
open _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace
open _root_.D5.S3.Weil.Mertens.ThetaTailRegularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Modulus

/-- The exact distance in the original modulus, with v as parameter and u as state. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ v u => |u - v|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {u v : ℝ}, 1 ≤ u → 1 ≤ v →
    |f u - f v| ≤ 2 * R.readout () v u

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := 1) (v := 1) le_rfl le_rfl
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @theta_tail_lipschitz) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_tail_lipschitz, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
    change |(1 : ℝ) - 1| ≠ |(2 : ℝ) - 1|
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@theta_tail_lipschitz) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.ThetaTailRegularity.theta_tail_lipschitz.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ThetaTailRegularity.Modulus.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v u => |u - v|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ThetaTailRegularity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Modulus

namespace Mass

/-- Observe exactly the absolute value in the original mass integral. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U a : ℝ}, 1 ≤ U → U ≤ a → 0 < f a →
    (f a) ^ 2 ≤ 4 * ∫ u in Ioi U, R.readout () () (f u)

private theorem actual_law : arena.Law actual := @theta_tail_peak_sq_le_mass

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

/-- A zero-mass intervention is rejected precisely when the original positive
peak domain is inhabited. No positive peak is assumed as audit evidence. -/
private theorem rejected_law_iff : arena.Law rejected ↔
    ¬ ∃ a : ℝ, 1 ≤ a ∧ 0 < f a := by
  constructor
  · intro h ⟨a, ha, hp⟩
    have hh := h (U := 1) (a := a) le_rfl ha hp
    change (f a) ^ 2 ≤ 4 * ∫ u in Ioi (1 : ℝ), (0 : ℝ) at hh
    simp only [integral_zero, mul_zero] at hh
    nlinarith
  · intro hn U a hU ha hp
    exact (hn ⟨a, hU.trans ha, hp⟩).elim

private theorem rejected_requires_positive_peak {Q : Realization signature}
    (hQ : ¬ arena.Law Q) : ∃ a : ℝ, 1 ≤ a ∧ 0 < f a := by
  by_contra hn
  apply hQ
  intro U a hU ha hp
  exact (hn ⟨a, hU.trans ha, hp⟩).elim

end Mass

#print axioms Modulus.family
#print axioms Modulus.registration
#print axioms Mass.rejected_law_iff

end
end Reg.D5.S3.Weil.Mertens.ThetaTailRegularity
