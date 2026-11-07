import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace
universe u v
noncomputable section

abbrev signature : Signature where
  Params := Σ K : Type u, Σ L : Type v, Σ _ : Field K, Σ _ : Field L, Algebra K L
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p x =>
    letI := p.2.2.1
    letI := p.2.2.2.1
    letI := p.2.2.2.2
    Algebra.trace p.1 p.2.1 x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ => letI := p.2.2.1; (0 : p.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ (K : Type u) (L : Type v) [kfield : Field K] [lfield : Field L]
    [alg : Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (_hG : IsPGroup p (L ≃ₐ[K] L)) (x : L),
    LinearIndependent K (fun σ : L ≃ₐ[K] L => σ x) ↔
      r.readout () ⟨K, L, kfield, lfield, alg⟩ x ≠ 0

private abbrev testK := ULift.{u} (ZMod 2)
private abbrev testL := ULift.{v} (ZMod 2)
private def testEquiv : testK.{u} ≃+* testL.{v} :=
  ULift.ringEquiv.trans ULift.ringEquiv.symm
private instance testAlgebra : Algebra testK.{u} testL.{v} := testEquiv.toRingHom.toAlgebra
private instance testGalois : IsGalois testK.{u} testL.{v} :=
  IsGalois.of_equiv_equiv (F := ZMod 2) (E := ZMod 2)
    (f := ULift.ringEquiv.symm) (g := ULift.ringEquiv.symm) (by ext; rfl)
private instance testAutSubsingleton : Subsingleton (testL.{v} ≃ₐ[testK.{u}] testL.{v}) := by
  constructor
  intro f g
  apply AlgEquiv.ext
  intro x
  obtain ⟨r, rfl⟩ := testEquiv.surjective x
  change f (algebraMap testK.{u} testL.{v} r) =
    g (algebraMap testK.{u} testL.{v} r)
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := Algebra.trace_surjective testK.{u} testL.{v} 1
  have htrace : Algebra.trace testK.{u} testL.{v} x ≠ 0 := by
    rw [hx]
    exact one_ne_zero
  have hind := (_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero
    testK.{u} testL.{v} 2 (IsPGroup.of_subsingleton 2 _) x).mpr htrace
  exact (h testK.{u} testL.{v} 2 (IsPGroup.of_subsingleton 2 _) x).mp hind rfl

def family : Registration arena.{u,v}
    (type_of% @_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero.{u,v},
    rejected, rejected_law⟩
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
    obtain ⟨x, hx⟩ := Algebra.trace_surjective testK.{u} testL.{v} 1
    refine ⟨⟨testK.{u}, testL.{v}, inferInstance, inferInstance, inferInstance⟩, x, 0, ?_⟩
    change Algebra.trace testK.{u} testL.{v} x ≠ Algebra.trace testK.{u} testL.{v} 0
    rw [hx, map_zero]
    exact one_ne_zero

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero.{u,v})
    (type_of% actual.{u,v}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace.linearIndependent_conjugates_iff_trace_ne_zero.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.PGroupNormalTrace
