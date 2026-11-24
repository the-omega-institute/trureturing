import D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Complete variation for the conditional arithmetic laws requires RH. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => smoothedMangoldt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 3, ?_⟩
  have hv := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  change smoothedMangoldt 0 ≠ smoothedMangoldt 3
  norm_num [smoothedMangoldt, Finset.sum_range_succ, hv]

namespace Explicit

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x),
    x / 2 - (707 / 300 * firstLiMass) * Real.sqrt x - (1 + Real.log Real.pi) -
      (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
        101 / 75 * firstLiMass) / x ≤ R.readout () () x

private theorem source_bridge :
    (type_of% @smoothedMangoldt_explicit_lower) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law_implies_rh (R : Realization signature)
    (h : ¬arena.Law R) : RiemannHypothesis := by
  by_contra hn
  apply h
  intro hRH
  exact (hn hRH).elim

private theorem rejected_law (hRH : RiemannHypothesis) : ¬arena.Law rejected := by
  intro h
  have he := h hRH (x := 1) (by norm_num)
  change (1 : ℝ) / 2 - (707 / 300 * firstLiMass) * Real.sqrt 1 -
    (1 + Real.log Real.pi) -
    (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
      101 / 75 * firstLiMass) / 1 ≤ -1 at he
  norm_num only [Real.sqrt_one, mul_one, div_one] at he
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero] at he
  linarith [firstLiMass_split, firstLiMass_lt_third]

def family (hRH : RiemannHypothesis) :
    Registration arena (type_of% @smoothedMangoldt_explicit_lower) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@smoothedMangoldt_explicit_lower, rejected, rejected_law hRH⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected (rejected_law hRH)
  dependence := dependence

def audit (hRH : RiemannHypothesis) :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@smoothedMangoldt_explicit_lower) (Realization signature) Unit Unit where
  unitName := ((`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta).str
    "smoothedMangoldt_explicit_lower").str "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta.Explicit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family hRH⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Explicit

namespace Uniform

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (hRH : RiemannHypothesis) {x : ℝ},
    x / 2 - Real.sqrt x ≤ R.readout () () x

private theorem source_bridge :
    (type_of% @smoothedMangoldt_lower) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law_implies_rh (R : Realization signature)
    (h : ¬arena.Law R) : RiemannHypothesis := by
  by_contra hn
  apply h
  intro hRH
  exact (hn hRH).elim

private theorem rejected_law (hRH : RiemannHypothesis) : ¬arena.Law rejected := by
  intro h
  have he := h hRH (x := 0)
  norm_num [rejected, realize] at he

def family (hRH : RiemannHypothesis) :
    Registration arena (type_of% @smoothedMangoldt_lower) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@smoothedMangoldt_lower, rejected, rejected_law hRH⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected (rejected_law hRH)
  dependence := dependence

def audit (hRH : RiemannHypothesis) :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@smoothedMangoldt_lower) (Realization signature) Unit Unit where
  unitName := (`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta.smoothedMangoldt_lower).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta.Uniform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family hRH⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
