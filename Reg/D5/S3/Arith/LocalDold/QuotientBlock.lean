import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.LocalDold.QuotientBlock

/-! Faithful whole-family source reconstruction for the actual quotient/block coefficient ideal. -/

namespace Reg.D5.S3.Arith.LocalDold.QuotientBlock
open LeanInformationAudit Function
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.LocalDold.QuotientBlock
open _root_.D5.S3.Arith.LocalDold.NormalizedQuotient
noncomputable section

abbrev signature : Signature where
  Params := LinearRecurrence ℤ
  State E := Algebra E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Ideal ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ E : LinearRecurrence ℤ, 2 ≤ E.order → ∀ q : Algebra E,
    R.readout () E q = Ideal.span (Set.range (fun i : Fin (E.order-1) =>
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val)))

def actual : Realization signature :=
  realize signature (fun _ E q => Ideal.span (Set.range (fun j : Fin (E.order-1) =>
      observation E (q*(AdjoinRoot.root E.charPoly)^j.val)))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev sourceScope := type_of% (@observation_ideal)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private def probeE : LinearRecurrence ℤ := ⟨2,fun _ => 1⟩

private theorem probe_one : actual.readout () probeE (AdjoinRoot.root probeE.charPoly) = ⊤ := by
  have hv : (fun j : Fin (probeE.order-1) => observation probeE
      (AdjoinRoot.root probeE.charPoly*(AdjoinRoot.root probeE.charPoly)^j.val)) =
      fun _ => (1 : ℤ) := by
    funext j
    have hj : j.val=0 := by have h:=j.isLt; change j.val<1 at h; omega
    rw [hj,pow_zero,mul_one]
    have he := observation_eq_impulse probeE (by decide) 1
    rw [pow_one] at he
    rw [he]
    norm_num [impulse,LinearRecurrence.mkSol,probeE]
  change Ideal.span (Set.range _) = ⊤
  rw [hv]
  apply (Ideal.eq_top_iff_one _).mpr
  exact Ideal.subset_span ⟨⟨0,by decide⟩,rfl⟩

private theorem probe_zero : actual.readout () probeE 0 = ⊥ := by
  change Ideal.span (Set.range (fun j : Fin (probeE.order-1) =>
    observation probeE (0*(AdjoinRoot.root probeE.charPoly)^j.val))) = ⊥
  simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := h probeE (by decide) (AdjoinRoot.root probeE.charPoly)
  have he := observation_ideal probeE (by decide) (AdjoinRoot.root probeE.charPoly)
  change (⊥ : Ideal ℤ) = _ at hc
  rw [← he] at hc
  change (⊥ : Ideal ℤ) = actual.readout () probeE (AdjoinRoot.root probeE.charPoly) at hc
  rw [probe_one] at hc
  exact bot_ne_top hc

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@observation_ideal), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨probeE,0,AdjoinRoot.root probeE.charPoly,?_⟩
    rw [probe_zero,probe_one]
    exact bot_ne_top

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@observation_ideal) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.LocalDold.QuotientBlock.observation_ideal.__information_unit
  realizationName := `Reg.D5.S3.Arith.LocalDold.QuotientBlock.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ E q => Ideal.span (Set.range (fun j : Fin (E.order-1) =>
      observation E (q*(AdjoinRoot.root E.charPoly)^j.val)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.LocalDold.QuotientBlock
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Arith.LocalDold.QuotientBlock
