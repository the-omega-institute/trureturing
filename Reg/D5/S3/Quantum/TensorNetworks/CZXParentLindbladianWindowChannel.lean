import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the cyclic window coordinates and channel identities. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance low] Classical.propDecidable
noncomputable section

namespace SiteInjective

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin n)
    (fun n => Fin n → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 4 ≤ n) (i : Fin n) (k l : Fin 4),
    R.readout () n (site i k.val) (site i l.val) ↔ k = l

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 4 (by decide) 0 0 0).mpr rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  intro he
  have hbad : (1 : Fin 2) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @site_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@site_injective, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@site_injective) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.SiteInjective.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SiteInjective

namespace SectorGaugeConst

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℂ)
    (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (e : Fin 2) (x : Fin n → Fin 2),
    R.readout () () (sectorGauge n (fun _ => e) x) (gauge n e x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @sectorGauge_const) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sectorGauge_const, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sectorGauge_const) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.SectorGaugeConst.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SectorGaugeConst

namespace SectorGaugeSquare

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℂ)
    (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (δ x : Fin n → Fin 2),
    R.readout () () (sectorGauge n δ x * sectorGauge n δ x) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @sectorGauge_mul_self) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sectorGauge_mul_self, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sectorGauge_mul_self) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.SectorGaugeSquare.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SectorGaugeSquare

namespace SuccessorInjective

/-- Observe the cyclic successor on each site, including the empty fiber. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin n)
    (fun n => Fin n)

def actual : Realization signature :=
  realize signature (fun _ _ i => site i 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ i => ⟨0, Nat.zero_lt_of_lt i.isLt⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Function.Injective (R.readout () n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : (0 : Fin 2) = 1 := h 2 (a₁ := 0) (a₂ := 1) rfl
  exact (by decide : (0 : Fin 2) ≠ 1) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change site (0 : Fin 2) 1 ≠ site (1 : Fin 2) 1
  decide

def source_registration : Registration arena (type_of% @site_succ_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@site_succ_injective, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@site_succ_injective) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.SuccessorInjective.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => site i 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SuccessorInjective

namespace GaugedWindowSector

open private middleUpdate from D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 4 ≤ n) (i : Fin n) (δ x : Fin n → Fin 2),
    R.readout () n (windowChannel n i (gaugedUnit n δ x))
      (if goodWindow i δ then
        (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
          gaugedUnit n δ (middleUpdate i x b c)
      else 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 4 (by decide) 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro he
  have hbad : (1 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @gauged_window_sector) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gauged_window_sector, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gauged_window_sector) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.GaugedWindowSector.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end GaugedWindowSector

namespace MatrixExtensionality

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
    (fun n => Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) {f g : Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)},
    (∀ δ x, f (gaugedUnit n δ x) = g (gaugedUnit n δ x)) →
    R.readout () n f g

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 0 0 (fun _ _ => rfl)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro he
  have hbad : (1 : Module.End ℂ (Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ)) = 0 :=
    Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @matrix_linearMap_ext_gauged) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matrix_linearMap_ext_gauged, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matrix_linearMap_ext_gauged) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.MatrixExtensionality.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end MatrixExtensionality

namespace WindowCommutation

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 4 ≤ n) (i j : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
    R.readout () n (windowChannel n i (windowChannel n j a))
      (windowChannel n j (windowChannel n i a))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 4 (by decide) 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro he
  have hbad : (1 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @window_channels_commute) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@window_channels_commute, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@window_channels_commute) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.WindowCommutation.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end WindowCommutation

namespace SuperoperatorAction

/-- The selected source predicate is observed on its original data operands. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℂ)
    (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (i : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x y : Fin n → Fin 2),
    R.readout () () ((windowSuperoperator n i).mulVec (fun p => a p.1 p.2) (x, y))
      (windowChannel n i a x y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena (type_of% @window_superoperator_action) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@window_superoperator_action, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@window_superoperator_action) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.SuperoperatorAction.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
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
  options := #[] }

#print axioms source_registration
#print axioms registration

end SuperoperatorAction

namespace WindowIdempotence

open private middleUpdate from D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel

/-- Observe a row of the source window superoperator. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Fin n)
    (fun p => (Fin p.1 → Fin 2) × (Fin p.1 → Fin 2))
    (fun p => ((Fin p.1 → Fin 2) × (Fin p.1 → Fin 2)) → ℂ)

def actual : Realization signature :=
  realize signature (fun _ p row => windowSuperoperator p.1 p.2 row) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ row => (2 : Matrix _ _ ℂ) row) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 4 ≤ n) (i : Fin n),
    IsIdempotentElem (show Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ from fun row => R.readout () ⟨n, i⟩ row)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 4 (by decide) 0
  change IsIdempotentElem (2 : Matrix ((Fin 4 → Fin 2) × (Fin 4 → Fin 2))
    ((Fin 4 → Fin 2) × (Fin 4 → Fin 2)) ℂ) at hbad
  norm_num [IsIdempotentElem] at hbad
  have hentry := congrArg (fun A => A (0, 0) (0, 0)) hbad
  norm_num [Matrix.ofNat_apply] at hentry

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let δ : Fin 5 → Fin 2 := fun k => if k = 4 then 1 else 0
  have hg : goodWindow (0 : Fin 5) δ := by
    intro k
    fin_cases k <;> rfl
  refine ⟨⟨5, 0⟩, (δ, 0), (0, 0), ?_⟩
  intro h
  have ha := congrArg
    (fun row : ((Fin 5 → Fin 2) × (Fin 5 → Fin 2)) → ℂ =>
      row ⬝ᵥ (fun p => gaugedUnit 5 δ 0 p.1 p.2)) h
  change (windowSuperoperator 5 0).mulVec
    (fun p => gaugedUnit 5 δ 0 p.1 p.2) (δ, 0) =
      (windowSuperoperator 5 0).mulVec
        (fun p => gaugedUnit 5 δ 0 p.1 p.2) (0, 0) at ha
  simp only [window_superoperator_action] at ha
  rw [gauged_window_sector 5 (by decide) 0 δ 0, ite_eq_left hg] at ha
  norm_num [gaugedUnit, sectorGauge, middleUpdate, site, δ, Matrix.single_apply,
    Matrix.smul_apply, Matrix.sum_apply, Fin.sum_univ_two, Fin.sum_univ_succ,
    funext_iff, Fin.forall_fin_succ, Function.update_apply] at ha

def source_registration : Registration arena (type_of% @window_idempotent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@window_idempotent, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@window_idempotent) (Realization signature) Unit Unit := {
  unitName := `CZXWindowChannel.WindowIdempotence.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p row => windowSuperoperator p.1 p.2 row) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end WindowIdempotence

set_option pp.proofs false in
#print site_injective
set_option pp.proofs false in
#print sectorGauge_const
set_option pp.proofs false in
#print sectorGauge_mul_self
set_option pp.proofs false in
#print site_succ_injective
set_option pp.proofs false in
#print gauged_window_sector
set_option pp.proofs false in
#print matrix_linearMap_ext_gauged
set_option pp.proofs false in
#print window_channels_commute
set_option pp.proofs false in
#print window_superoperator_action
set_option pp.proofs false in
#print window_idempotent

end
end Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
