import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanContractedAlgebra
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! # The induced contracted multiplication map as a dependent family -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra.BergmanQuestion15Refutation

namespace Reg.D5.S0.Certificates.Algebra.BergmanContractedAlgebra

universe u v w
noncomputable section

abbrev Parameters :=
  Σ F : Type v, Σ S : Type u, Σ T : Type w,
  Σ field : Field F, Σ source : SemigroupWithZero S, Σ target : SemigroupWithZero T,
    letI := field
    letI := source
    letI := target
    Σ _f : S → T, Contracted F S

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State := fun ⟨F, S, _, field, source, _, _⟩ => by
    letI := field
    letI := source
    exact Contracted F S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ ⟨F, _, T, field, _, target, _⟩ => by
    letI := field
    letI := target
    exact Contracted F T
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u,v,w} :=
  realize signature (fun _ ⟨F, S, T, field, source, target, f, a⟩ b => by
    letI := field
    letI := source
    letI := target
    exact _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map
      (F := F) f (a * b)) (fun e => nomatch e)

abbrev rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ ⟨_, _, _, field, _, target, _⟩ _ => by
    letI := field
    letI := target
    exact 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {F : Type v} {S : Type u} {T : Type w}
    [field : Field F] [source : SemigroupWithZero S] [target : SemigroupWithZero T]
    (f : S → T) (hzero : f 0 = 0) (hmul : ∀ a b, f (a * b) = f a * f b)
    (a b : Contracted F S),
      r.readout () ⟨F, S, T, field, source, target, f, a⟩ b =
        _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map (F := F) f a *
        _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map (F := F) f b

private abbrev liftMap : ULift.{u} ℕ → ULift.{w} ℕ := fun x => ⟨x.down⟩

private theorem liftMap_zero : liftMap.{u,w} 0 = 0 := rfl

private theorem liftMap_mul (a b : ULift.{u} ℕ) :
    liftMap.{u,w} (a * b) = liftMap a * liftMap b := rfl

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let F := ULift.{v} ℚ
  let S := ULift.{u} ℕ
  let T := ULift.{w} ℕ
  have H := h liftMap.{u,w} liftMap_zero liftMap_mul
    (delta F S 1) (delta F S 1)
  change (0 : Contracted F T) =
    _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map (F := F) liftMap
      (delta F S 1) *
    _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map (F := F) liftMap
      (delta F S 1) at H
  rw [_root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map_delta
      liftMap liftMap_zero,
    _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.delta_mul] at H
  change (0 : Contracted F T) = delta F T 1 at H
  have hn : (1 : T) ≠ 0 := by decide
  have hc := congrArg (fun x : Contracted F T => x ⟨1, hn⟩) H
  simp [delta, hn] at hc

abbrev mapMulAudit : Registration arena.{u,v,w}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map_mul.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map_mul.{u,v,w},
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
    let F := ULift.{v} ℚ
    let S := ULift.{u} ℕ
    let T := ULift.{w} ℕ
    let p : Parameters.{u,v,w} :=
      ⟨F, S, T, inferInstance, inferInstance, inferInstance,
        liftMap.{u,w}, delta F S 1⟩
    refine ⟨p, delta F S 1, 0, ?_⟩
    intro he
    change
      _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map (F := F) liftMap
        (delta F S 1 * delta F S 1) =
      _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map (F := F) liftMap
        (delta F S 1 * 0) at he
    rw [mul_zero, map_zero,
      _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.delta_mul,
      _root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map_delta
        liftMap liftMap_zero] at he
    change delta F T 1 = 0 at he
    have hn : (1 : T) ≠ 0 := by decide
    have hc := congrArg (fun x : Contracted F T => x ⟨1, hn⟩) he
    simp [delta, hn] at hc

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map_mul.{u,v,w})
    (type_of% actual.{u,v,w}) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanContractedAlgebra.map_mul.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanContractedAlgebra.mapMulAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨mapMulAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanContractedAlgebra
    definition := none
    coordinates := #[0, 1, 2, 6, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S0.Certificates.Algebra.BergmanContractedAlgebra
