import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for fourth-moment compression and polynomial averages. -/

noncomputable section
open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
namespace Compression
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k n : ℕ} (hn : 0 < n) (x : Fin n → Fin k → ℝ),
    ∃ (p : Fin (nodeCount k) → ℝ) (y : Fin (nodeCount k) → Fin k → ℝ),
      (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
      (∀ a, y a ∈ Set.range x) ∧
      ∀ a : Monomial k, Rz.readout () () ((∑ r, monomial a (x r)) / n)
        (∑ b, p b * monomial a (y b))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, y, _, _, _, he⟩ := h (k := 0) (n := 1) (by decide) (fun _ => Fin.elim0)
  exact he (Sym.replicate 4 none)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h10 : (1 : ℝ) = 0 := by
    have hh := congrFun he 0
    change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at hh
    exact (eq_iff_iff.mp hh).mp rfl
  exact one_ne_zero h10
def family : Registration arena (type_of% (@exists_moment_compression)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_moment_compression, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_moment_compression) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression.exists_moment_compression.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression.Compression.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Compression

namespace Quartic
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k n R : ℕ} (x : Fin n → Fin k → ℝ)
    (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ),
    (∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) → ∀ c : Monomial k → ℝ,
    Rz.readout () () ((∑ r, quartic c (x r)) / n)
      (∑ b, p b * quartic c (y b))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (n := 0) (R := 0) Fin.elim0 Fin.elim0 Fin.elim0
    (fun _ => by simp) (fun _ => 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h10 : (1 : ℝ) = 0 := by
    have hh := congrFun he 0
    change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at hh
    exact (eq_iff_iff.mp hh).mp rfl
  exact one_ne_zero h10
def family : Registration arena (type_of% (@quartic_average_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quartic_average_eq, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quartic_average_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression.quartic_average_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression.Quartic.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Quartic

namespace Product
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law Rz := ∀ {k n R : ℕ} (x : Fin n → Fin k → ℝ)
    (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ),
    (∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) →
    ∀ {T : Type} [Fintype T] (f g : T → Monomial k → ℝ),
    Rz.readout () ()
      ((∑ r, ∑ s, ∑ t, quartic (f t) (x r) * quartic (g t) (x s)) / (n : ℝ)^2)
      (∑ a, ∑ b, p a * p b * ∑ t, quartic (f t) (y a) * quartic (g t) (y b))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (k := 0) (n := 0) (R := 0) Fin.elim0 Fin.elim0 Fin.elim0
    (fun _ => by simp) (T := Unit) (fun _ _ => 0) (fun _ _ => 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h10 : (1 : ℝ) = 0 := by
    have hh := congrFun he 0
    change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at hh
    exact (eq_iff_iff.mp hh).mp rfl
  exact one_ne_zero h10
def family : Registration arena (type_of% (@product_average_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_average_eq, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@product_average_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression.product_average_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression.Product.family
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
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Product

end Reg.D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
