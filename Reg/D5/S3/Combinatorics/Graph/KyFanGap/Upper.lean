/- GID: Reg/D5/S3/Combinatorics/Graph/KyFanGap/Upper
   generality: G
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: Source-bound registrations for the universal Ky Fan upper bound. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.Upper
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for dimension truncation and the zero-one bound. -/

noncomputable section
open _root_.D5.S3.Combinatorics.Graph.KyFanGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.Upper

namespace Truncation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ}, n ≤ k → ∀ (M : Matrix (Fin n) (Fin n) ℝ),
    R.readout () () (kyFan k M) (kyFan n M)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (n := 0) le_rfl 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun y : ℝ => (0 : ℝ) = y) = (fun y : ℝ => (1 : ℝ) = y) at h
  have h10 : (1 : ℝ) = 0 := by rw [← congrFun h 0]
  exact one_ne_zero h10
def family : Registration arena (type_of% (@kyFan_eq_of_ge)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kyFan_eq_of_ge, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kyFan_eq_of_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.kyFan_eq_of_ge.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.Upper.Truncation.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Truncation

namespace ZeroOneBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    (∀ i j, A i j = 0 ∨ A i j = 1) →
      R.readout () () (kyFan k A) ((1 + Real.sqrt k) * n / 2)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (n := 0) 0 (by simp [Matrix.IsSymm]) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h (0 : ℝ)
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@kyFan_le_of_zero_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kyFan_le_of_zero_one, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kyFan_le_of_zero_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.kyFan_le_of_zero_one.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.Upper.ZeroOneBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZeroOneBound

end Reg.D5.S3.Combinatorics.Graph.KyFanGap.Upper
