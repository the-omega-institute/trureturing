import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank
import Reg.Support.DependentFamily

/-! Source registration for the common trace needed by rational marginal extensions. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank

open LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank
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

private def acceptAll : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (L R : Matrix Bool Bool ℂ) (_ : L.PosSemidef) (_ : R.PosSemidef)
    (_ : Y.readout () () L.trace R.trace)
    (_ : ∀ i j, RationalEntry (L i j)) (_ : ∀ i j, RationalEntry (R i j)),
    ∃ S : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      S.PosSemidef ∧ partialTraceRight S = L ∧ partialTraceLeft S = R ∧
        S.rank ≤ 3 ∧ ∀ i j, RationalEntry (S i j)

private theorem rejected_law : ¬ arena.Law acceptAll := by
  intro h
  have hzero : ∀ i j, RationalEntry ((0 : Matrix Bool Bool ℂ) i j) :=
    fun _ _ => rationalComplex.zero_mem
  have hone (i j : Bool) : RationalEntry ((1 : Matrix Bool Bool ℂ) i j) := by
    simp only [Matrix.one_apply]
    split
    · exact rationalComplex.one_mem
    · exact rationalComplex.zero_mem
  obtain ⟨S, _, hL, hR, _⟩ := h 0 1 Matrix.PosSemidef.zero Matrix.PosSemidef.one
    trivial hzero hone
  have he := (congrArg Matrix.trace hL).symm.trans
    ((trace_partialTraceRight S).trans ((trace_partialTraceLeft S).symm.trans
      (congrArg Matrix.trace hR)))
  simpa using he

def family : Registration arena (type_of% @rational_endpoint_rank_le_three) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_endpoint_rank_le_three, acceptAll, rejected_law⟩
  sensitivity := ⟨fun i => ⟨acceptAll, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_endpoint_rank_le_three) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank.rational_endpoint_rank_le_three.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank
