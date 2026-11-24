import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank
import Reg.Support.DependentFamily

/-! Source registration for normalization of the right marginal. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank

open LeanInformationAudit Matrix
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank
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
  Law Y := ∀ (A B : Matrix Bool Bool ℂ), A.PosSemidef → B.PosSemidef →
    A.trace = 1 → Y.readout () () B.trace 1 → A.det = B.det →
    (∀ i j, RationalEntry (A i j)) → (∀ i j, RationalEntry (B i j)) →
    ∃ S : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      S.PosSemidef ∧ partialTraceRight S = A ∧ partialTraceLeft S = B ∧
      S.rank ≤ 2 ∧ ∀ i j, RationalEntry (S i j)

private theorem rejected_law : ¬ arena.Law acceptAll := by
  intro h
  let A : Matrix Bool Bool ℂ := Matrix.diagonal (fun i => if i then 0 else 1)
  have hA : A.PosSemidef := Matrix.PosSemidef.diagonal fun i => by cases i <;> simp
  have htA : A.trace = 1 := by simp [A, Matrix.trace]
  have hd : A.det = 0 := by simp [A]
  have hAQ (i j : Bool) : RationalEntry (A i j) := by
    cases i <;> cases j
    · exact rationalComplex.one_mem
    · exact rationalComplex.zero_mem
    · exact rationalComplex.zero_mem
    · exact rationalComplex.zero_mem
  obtain ⟨S, _, hL, hR, _⟩ :=
    h A 0 hA Matrix.PosSemidef.zero htA trivial (by simpa using hd)
      hAQ (fun _ _ => rationalComplex.zero_mem)
  have he := (congrArg Matrix.trace hL).symm.trans
    ((trace_partialTraceRight S).trans ((trace_partialTraceLeft S).symm.trans
      (congrArg Matrix.trace hR)))
  simp [htA] at he

def family : Registration arena (type_of% @rational_endpoint_rank_le_two_of_equal_det) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_endpoint_rank_le_two_of_equal_det, acceptAll, rejected_law⟩
  sensitivity := ⟨fun i => ⟨acceptAll, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_endpoint_rank_le_two_of_equal_det) (Realization signature) Unit Unit where
  unitName :=
    (`D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank ++
      `rational_endpoint_rank_le_two_of_equal_det.audit)
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitEqualSpectrumRank
