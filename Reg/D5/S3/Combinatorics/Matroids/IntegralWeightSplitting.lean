import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
import Mathlib.Combinatorics.Matroid.Map

/-! # Source-bound audits of native integral weight splitting -/

namespace Reg.D5.S3.Combinatorics.Matroids.IntegralWeightSplitting

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State E := Matroid E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := Set E → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => M.IsBase) (fun e => nomatch e)

def allBases : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

def noBases : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, loopyOn ∅, freeOn {ULift.up ()}, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  simp [actual, realize] at hh

abbrev localArena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [Finite E] (M : Matroid E) (q : E → ℤ)
    {B : Set E}, M.IsBase B →
    (∀ b ∈ B, ∀ e ∈ M.E \ B, M.IsBase (insert e (B \ {b})) → q b ≤ q e) →
    ∀ C, r.readout () E M C → weightSum q B ≤ weightSum q C

private theorem local_rejected : ¬ localArena.{u}.Law allBases := by
  intro h
  have hh := h (E := ULift.{u} Unit) (loopyOn ∅) (fun _ => -1) (B := ∅)
    (by simp) (by simp) {ULift.up ()} trivial
  norm_num [weightSum] at hh

def local_source : Registration localArena.{u}
    (type_of% (@exchange_local_is_global_minimum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exchange_local_is_global_minimum, allBases, local_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨allBases, ?_, rfl, local_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

abbrev closedWalkArena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [Finite E] (M₁ M₂ : Matroid E)
    (_hE : M₁.E = M₂.E) (w : E → ℤ) {B : Set E},
    M₁.IsBase B → M₂.IsBase B →
    (∀ C, r.readout () E M₁ C → M₂.IsBase C → weightSum w B ≤ weightSum w C) →
    ∀ (s : E) (p : (exchangeGraph M₁ M₂ B).Walk s s),
      Maths.MaxPlusPotential.walkWeight (exchangeWeight M₁ M₂ B w) p ≤ 0

private def rankOne : Matroid (ULift.{u} Bool) :=
  (freeOn (univ : Set Unit)).comap (fun _ => ())

private theorem rankOne_base (a : ULift.{u} Bool) : rankOne.IsBase {a} := by
  have him : (fun _ : ULift.{u} Bool => ()) '' univ = (univ : Set Unit) := by
    ext x
    cases x
    simp
  rw [rankOne, comap_isBase_iff, Set.image_singleton, freeOn_ground, Set.preimage_univ, him]
  refine ⟨?_, Set.injOn_singleton _ _, Set.subset_univ _⟩
  have hb : (freeOn (univ : Set Unit)).IsBase {()} := by
    rw [freeOn_isBase_iff]
    ext x
    cases x
    simp
  exact hb.isBasis_ground

private theorem closedWalk_rejected : ¬ closedWalkArena.{u}.Law noBases := by
  intro h
  let b : ULift.{u} Bool := ULift.up false
  let e : ULift.{u} Bool := ULift.up true
  let w : ULift.{u} Bool → ℤ := fun x => if x.down then 0 else 1
  have hbe : b ≠ e := by decide
  have hex : rankOne.IsBase (insert e ({b} \ {b})) := by
    simpa using rankOne_base e
  let a₁ : ExchangeArc rankOne rankOne {b} :=
    ⟨(true, b, e), by simp, by simp [rankOne, hbe.symm], hex⟩
  let a₂ : ExchangeArc rankOne rankOne {b} :=
    ⟨(false, b, e), by simp, by simp [rankOne, hbe.symm], hex⟩
  let p : (exchangeGraph rankOne rankOne {b}).Walk b b :=
    ((Maths.EdgeGraph.Walk.nil).concat a₁ rfl).concat a₂ rfl
  have hh := h rankOne rankOne rfl w (rankOne_base b) (rankOne_base b)
    (fun C hC _ => False.elim hC) b p
  change (1 : ℤ) ≤ 0 at hh
  omega

def closedWalk_source : Registration closedWalkArena.{u}
    (type_of% (@optimal_common_base_closedWalk_nonpos.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@optimal_common_base_closedWalk_nonpos, noBases, closedWalk_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨noBases, ?_, rfl, closedWalk_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

abbrev splittingArena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [Finite E] (M₁ M₂ : Matroid E)
    (_hE : M₁.E = M₂.E) (_hcommon : ∃ B, M₁.IsBase B ∧ M₂.IsBase B) (w : E → ℤ),
    ∃ (B : Set E) (c d : E → ℤ), r.readout () E M₁ B ∧ M₂.IsBase B ∧
      (∀ e, c e + d e = w e) ∧
      (∀ C, M₁.IsBase C → weightSum c B ≤ weightSum c C) ∧
      (∀ D, M₂.IsBase D → weightSum d B ≤ weightSum d D)

private theorem splitting_rejected : ¬ splittingArena.{u}.Law noBases := by
  intro h
  obtain ⟨B, c, d, hB, _⟩ := h (E := ULift.{u} Unit) (loopyOn ∅) (loopyOn ∅) rfl
    ⟨∅, by simp, by simp⟩ (fun _ => 0)
  exact hB

def splitting_source : Registration splittingArena.{u}
    (type_of% (@finite_integral_weight_splitting.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_integral_weight_splitting, noBases, splitting_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨noBases, ?_, rfl, splitting_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def local_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exchange_local_is_global_minimum.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.IntegralWeightSplitting.exchange_local_is_global_minimum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralWeightSplitting.local_source
  realizationSource := none
  generated := false
  arena := .source ⟨localArena⟩
  objectArena := .source ⟨localArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source localArena ⟨local_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def closedWalk_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@optimal_common_base_closedWalk_nonpos.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.IntegralWeightSplitting.optimal_common_base_closedWalk_nonpos.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralWeightSplitting.closedWalk_source
  realizationSource := none
  generated := false
  arena := .source ⟨closedWalkArena⟩
  objectArena := .source ⟨closedWalkArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closedWalkArena ⟨closedWalk_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "domain", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def splitting_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@finite_integral_weight_splitting.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.IntegralWeightSplitting.finite_integral_weight_splitting.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralWeightSplitting.splitting_source
  realizationSource := none
  generated := false
  arena := .source ⟨splittingArena⟩
  objectArena := .source ⟨splittingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source splittingArena ⟨splitting_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms local_source
#print axioms closedWalk_source
#print axioms splitting_source
#print axioms local_registration
#print axioms closedWalk_registration
#print axioms splitting_registration

end
end Reg.D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
