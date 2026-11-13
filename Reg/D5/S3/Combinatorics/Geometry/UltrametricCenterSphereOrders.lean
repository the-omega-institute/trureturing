import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders

/-! Source-bound observation of the entire unrestricted sphere-count classification. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open _root_.UltrametricCenterSphereOrders

abbrev Parameters := Σ _ : (ℕ → ℝ), Σ _ : (ℕ → ℕ), ℕ

abbrev signature : DependentFamily.Signature where
  Params := Parameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ n => n)
    (fun e => nomatch e)

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (c : ℕ → ℝ) (b : ℕ → ℕ) (h n : ℕ)
    (hc0 : c 0 = 0) (hc : ∀ i < h, c i < c (i + 1)) (hb : ∀ i ≤ h, 0 < b i),
    (∃ (X : Type) (m : MetricSpace X),
      letI := m
      IsUltrametricDist X ∧ Finite X ∧ Nonempty X ∧ Nat.card X = n ∧
        center X = c '' Set.Iic h ∧
        (∀ i ≤ h, ∀ x : X, Nat.card (Metric.sphere x (c i)) = b i)) ↔
      b 0 = 1 ∧ R.readout () ⟨c, b, h⟩ n ∈ orders b h

abbrev sourceScope := type_of%
  (@_root_.UltrametricCenterSphereOrders.possible_orders_unrestricted_iff)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual :=
  source_bridge.mp (@_root_.UltrametricCenterSphereOrders.possible_orders_unrestricted_iff)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let c : ℕ → ℝ := fun _ => 0
  let b : ℕ → ℕ := fun _ => 1
  have hc : ∀ i < 0, c i < c (i + 1) := by omega
  have hb : ∀ i ≤ 0, 0 < b i := by intro i hi; simp [b]
  have hn : 1 ∈ orders b 0 := by simp [orders]
  have he := (_root_.UltrametricCenterSphereOrders.possible_orders_unrestricted_iff
    c b 0 1 rfl hc hb).mpr ⟨rfl, hn⟩
  have hz := (h c b 0 1 rfl hc hb).mp he |>.2
  simpa [rejected, DependentFamily.realize, orders] using hz

theorem dependence : ∀ i : Unit, ∃ (p : signature.Params) (s t : signature.State p),
    actual.readout i p s ≠ actual.readout i p t := by
  intro i
  let p : Parameters := ⟨fun _ => 0, fun _ => 1, 0⟩
  exact ⟨p, 1, 2, by simp [actual, DependentFamily.realize]⟩

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.UltrametricCenterSphereOrders.possible_orders_unrestricted_iff)
      (DependentFamily.Realization signature) Unit Unit where
  unitName := `UltrametricCenterSphereOrders.possible_orders_unrestricted_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders
