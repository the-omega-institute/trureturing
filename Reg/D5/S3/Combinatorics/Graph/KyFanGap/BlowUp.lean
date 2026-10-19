import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for graph blow-ups and their asymptotic maximum. -/

noncomputable section

attribute [local instance] Classical.propDecidable
open Filter Topology
open _root_.D5.S3.Combinatorics.Graph.KyFanGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.BlowUp

namespace GraphBlowUp
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k m t : ℕ} (ht : 1 ≤ t)
    (G : SimpleGraph (Fin m)), Rz.readout () ()
      ((t : ℝ) * kyFan k (G.adjMatrix ℝ)) (xi k (m * t))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (m := 0) (t := 1) (by decide) ⊥
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@kyFan_blowUp_le_xi)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kyFan_blowUp_le_xi, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kyFan_blowUp_le_xi) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.kyFan_blowUp_le_xi.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.BlowUp.GraphBlowUp.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
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
end GraphBlowUp

namespace IsolatedVertices
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k m n : ℕ} (hmn : m ≤ n),
    Rz.readout () () (xi k m) (xi k n)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (m := 0) (n := 0) (by decide)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@xi_mono)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@xi_mono, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@xi_mono) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.xi_mono.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.BlowUp.IsolatedVertices.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
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
end IsolatedVertices

namespace MaximumBlowUp
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k m t : ℕ} (ht : 1 ≤ t),
    Rz.readout () () ((t : ℝ) * xi k m) (xi k (m * t))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (m := 0) (t := 1) (by decide)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@xi_blowUp)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@xi_blowUp, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@xi_blowUp) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.xi_blowUp.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.BlowUp.MaximumBlowUp.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
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
end MaximumBlowUp

namespace NormalizedLimit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => Filter ℕ → Filter ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k : ℕ} (hk : 1 ≤ k),
    Rz.readout () () (fun n : ℕ => xi k n / n) atTop (nhds (normalizedSupremum k))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 1) (by decide)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hh := congrFun (congrFun he atTop) (nhds (0 : ℝ))
  change (Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) =
    (Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0)) at hh
  have hb := (eq_iff_iff.mp hh).mp tendsto_const_nhds
  have heq := tendsto_nhds_unique hb (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num at heq
def family : Registration arena (type_of% (@tendsto_xi_div)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_xi_div, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tendsto_xi_div) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.tendsto_xi_div.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.BlowUp.NormalizedLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NormalizedLimit

end Reg.D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
