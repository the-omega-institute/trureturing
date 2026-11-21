import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts

open Metric
open _root_.D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges (center)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the order `|X| = 2^h`. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    ∀ {X : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X] (c : ℕ → ℝ) (h : ℕ),
      c 0 = 0 → (∀ i < h, c i < c (i + 1)) → center X = c '' Set.Iic h →
      ((∀ i, 1 ≤ i → i ≤ h → ∀ x : X, Nat.card (sphere x (c i)) = 2 ^ (i - 1)) ↔
        Q.readout () () (Nat.card X) (2 ^ h))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  obtain ⟨X, hF, hM, hU, -, hC, -⟩ :=
    ((_root_.D5.S3.Combinatorics.Geometry.UltrametricCenterMinimumOrder.result {0}).2
      (Finset.mem_singleton_self 0) (by simp)).2
  have hcen : center X = (fun _ : ℕ => (0 : ℝ)) '' Set.Iic 0 := by
    rw [hC]
    ext t
    simp
  exact (hlaw (X := X) (fun _ => 0) 0 rfl (fun i hi => absurd hi (Nat.not_lt_zero i)) hcen).mp
    (fun i hi1 hi0 => absurd hi0 (by omega))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℕ)
  norm_num [actual, realize] at hh

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts.result, rejected,
      rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts.result)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts
