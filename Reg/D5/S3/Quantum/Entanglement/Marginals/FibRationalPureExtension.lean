import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
import Reg.Support.DependentFamily

/-! Source-equivalence registration for the rational norm criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open _root_.D5.S3.Quantum.PureState.PureStateHandshake

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ b : ℚ,
    (∃ ψ : Word → ℂ, let ρ := rankOneDensity ψ
      ρ.trace = 1 ∧ edgeTrace ρ 1 2 = edgeState (1 - (b : ℝ)) b 0 ∧
      edgeTrace ρ 2 1 = edgeState (1 - (b : ℝ)) b 0 ∧
      ∀ i j, RationalEntry (ρ i j)) ↔
      ∃ a c : ℚ, Y.readout () () (a ^ 2 + c ^ 2) (b * (1 - b))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (rational_pure_extension_iff 0).mpr ⟨0, 0, by norm_num⟩
  obtain ⟨_, _, hfalse⟩ := (h 0).mp hzero
  exact hfalse

def family : Registration arena (type_of% @rational_pure_extension_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_pure_extension_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_pure_extension_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension.rational_pure_extension_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
