import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! The ambient-vector observation entering the actual rank-six membership law. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.RankSubspace
set_option autoImplicit false
noncomputable section

abbrev rankSignature : Signature :=
  signature Unit (fun _ => E6Ambient) (fun _ => E6Ambient)

abbrev rankArena : Arena where
  signature := rankSignature
  Law R := (∀ α ∈ e6Roots, R.readout () () α ∈ H6) ∧ Module.finrank ℝ H6 = 6

private def outside : E6Ambient := WithLp.toLp 2 ![0, 0, 0, 0, 0, 1, 0, 0]

private theorem outsideNotMem : outside ∉ H6 := by
  intro h
  have hh := h.1
  change (1 : ℝ) = 0 at hh
  norm_num at hh

private theorem rejected : ¬ rankArena.Law
    (realize rankSignature (fun _ _ _ => outside) (fun e => nomatch e)) := by
  intro h
  have hh := h.1 (e6SimpleRoot 0) (e6_dynkin_simple_roots.1 0)
  exact outsideNotMem hh

def rankFamily : Registration rankArena (type_of% (@e6Roots_in_rank6_subspace)) where
  actual := realize rankSignature
    (fun _ _ α => α) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨e6Roots_in_rank6_subspace,
    realize rankSignature (fun _ _ _ => outside) (fun e => nomatch e), rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity rankArena.Law _ _ rejected
  dependence := by
    intro _
    refine ⟨(), 0, outside, ?_⟩
    change (0 : E6Ambient) ≠ outside
    intro h
    exact outsideNotMem (h ▸ H6.zero_mem)

def rankRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6Roots_in_rank6_subspace) (Realization rankSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6Roots_in_rank6_subspace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.RankSubspace.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature
    (fun _ _ α => α) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.E6TrinificationUnification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.RankSubspace
