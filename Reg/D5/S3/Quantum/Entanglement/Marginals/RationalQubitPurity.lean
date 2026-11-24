import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity
import Reg.Support.DependentFamily

/-! Source registration for the common determinant of rational pure marginal extensions. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity

open LeanInformationAudit
open Matrix Complex
open scoped ComplexOrder
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def rejectAll : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (L R : Matrix Bool Bool ℂ),
    (∃ ψ : Bool × Bool → ℂ, (rankOneDensity ψ).trace = 1 ∧
      partialTraceRight (rankOneDensity ψ) = L ∧ partialTraceLeft (rankOneDensity ψ) = R ∧
      ∀ i j, RationalEntry (rankOneDensity ψ i j)) ↔
      L.PosSemidef ∧ R.PosSemidef ∧ L.trace = 1 ∧ R.trace = 1 ∧
        Y.readout () () L.det R.det ∧ (∀ i j, RationalEntry (L i j)) ∧
        (∀ i j, RationalEntry (R i j)) ∧
        ∃ s : ℂ, RationalEntry s ∧ (normSq s : ℂ) = L.det

private theorem rejected_law : ¬ arena.Law rejectAll := by
  intro h
  let L : Matrix Bool Bool ℂ := Matrix.diagonal fun i => if i then 0 else 1
  have hL : L.PosSemidef := Matrix.PosSemidef.diagonal fun i => by cases i <;> simp
  have htrace : L.trace = 1 := by simp [L, Matrix.trace, Matrix.diag_apply, Fintype.sum_bool]
  have hQ (i j : Bool) : RationalEntry (L i j) := by
    cases i <;> cases j
    · exact rationalComplex.one_mem
    · exact rationalComplex.zero_mem
    · exact rationalComplex.zero_mem
    · exact rationalComplex.zero_mem
  have hdet : L.det = 0 := by simp [L, Matrix.det_diagonal, Fintype.prod_bool]
  have hP := (rational_qubit_purity_iff L L).mpr
    ⟨hL, hL, htrace, htrace, rfl, hQ, hQ, 0, rationalComplex.zero_mem, by simp [hdet]⟩
  exact ((h L L).mp hP).2.2.2.2.1

def family : Registration arena (type_of% @rational_qubit_purity_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_qubit_purity_iff, rejectAll, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejectAll, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_qubit_purity_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity.rational_qubit_purity_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitPurity
