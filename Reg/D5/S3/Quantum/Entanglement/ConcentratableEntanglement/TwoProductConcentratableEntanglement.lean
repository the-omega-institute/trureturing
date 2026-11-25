import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement
import Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments

/-! Source-bound readout of the actual finite physical family as the real order varies. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- The joint sort of the dependent readout necessarily contains both universe levels.
set_option linter.checkUnivs false

namespace Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement
open _root_.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
open _root_.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
  (ProbeSite ProbeLevel site0 firstBasis secondBasis firstBasis_unit secondBasis_unit bell_mass_ne
    bell_empty bell_left)
open LeanInformationAudit
open scoped Classical

noncomputable section
universe u v
private local instance probeSiteClassical : DecidableEq ProbeSite.{u} := Classical.decEq _

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := {I : Type u} → [Fintype I] → {D : I → Type v} →
    [∀ i, Fintype (D i)] → [∀ i, DecidableEq (D i)] →
    ℂ → ℂ → ((i : I) → D i → ℂ) → ((i : I) → D i → ℂ) → Finset I → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ K => @physicalGCE.{u,v} K) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ {_} [_] {_} [_] [_] _ _ _ _ S => -(S.card : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {K : ℝ}, 1 < K →
    let observed := @Realization.readout signature.{u,v} R () () K
    ∀ {I : Type u} [Fintype I] {D : I → Type v} [∀ i, Fintype (D i)]
      [∀ i, DecidableEq (D i)] (a b : ℂ) (x z : ∀ i, D i → ℂ),
    (∀ i, overlap (x i) (x i) = 1) →
    (∀ i, overlap (z i) (z i) = 1) →
    totalMass a b x z ≠ 0 →
    let f := @observed I inferInstance D inferInstance inferInstance a b x z
    Monotone f ∧ ∀ X Y, f (X∩Y)+f (X∪Y) ≤ f X+f Y

set_option maxHeartbeats 1000000 in
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have ht := (h (K := 2) (by norm_num) 1 1 firstBasis.{u,v} secondBasis.{u,v}
    firstBasis_unit secondBasis_unit bell_mass_ne).1
  have q := ht (Finset.empty_subset ({site0} : Finset ProbeSite.{u}))
  change -((∅ : Finset ProbeSite.{u}).card : ℝ) ≤ -(({site0} : Finset ProbeSite.{u}).card : ℝ) at q
  norm_num at q

set_option maxHeartbeats 1000000 in
private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  refine ⟨(),2,3,?_⟩
  intro h
  let eval (F : signature.{u,v}.Output () role) := @F ProbeSite.{u} inferInstance
    (fun _ => ProbeLevel.{v}) inferInstance inferInstance 1 1 firstBasis secondBasis {site0}
  have eq := congrArg eval h
  change physicalGCE 2 1 1 firstBasis.{u,v} secondBasis.{u,v} {site0} =
    physicalGCE 3 1 1 firstBasis.{u,v} secondBasis.{u,v} {site0} at eq
  have hs : ({site0} : Finset ProbeSite.{u}).powerset = {∅,{site0}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  unfold physicalGCE at eq
  rw [hs, Finset.sum_insert (by simp), Finset.sum_singleton] at eq
  repeat rw [Finset.sum_insert (by simp), Finset.sum_singleton] at eq
  rw [bell_empty (by norm_num), bell_left (by norm_num),
    bell_empty (by norm_num), bell_left (by norm_num)] at eq
  norm_num [← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast] at eq

def source_registration : Registration arena.{u,v} (type_of% @actual_two_product_gce.{u,v}) where
  actual := actual.{u,v}
  bridge := Iff.rfl
  variation := ⟨@actual_two_product_gce.{u,v},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_two_product_gce.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement.actual_two_product_gce.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ K => @physicalGCE.{u,v} K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement
