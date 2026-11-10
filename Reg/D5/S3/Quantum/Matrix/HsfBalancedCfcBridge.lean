import D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Typed source-binding attempt for the two-level block supplier. The complete
actual-CFC derivative telescope is retained. Current declared-template binding
is unresolved under https://github.com/the-omega-institute/trureturing/issues/23103;
the scalar observation has no validated source-selection reconstruction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
open _root_.D5.S3.Quantum.Matrix.HsfBalancedSpectralCertificate
open _root_.D5.S3.Quantum.Matrix.RpowPencilTaylor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
noncomputable section
universe u v w

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ s => 0 ≤ s.1 ∧ s.1 ≤ s.2) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : ℝ), 0 < r →
    ∀ (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ),
    (direction A C H).PosSemidef →
    ∀ (Z : Matrix (m ⊕ n) (m ⊕ n) ℂ), Z.IsHermitian →
    let Y := (baseRoot (m := m) (n := n) r)^3
    let K := baseDirection r A C H
    let P := CFC.rpow Y (1/3 : ℝ)
    let B := jetCoeff (fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹)
    F.readout () () (kappa r/6*pairEnergy A C H,
      tr (B 3)+2*tr (Z*B 2)+tr (B 1*Z*Z)-(5/48 : ℝ)*tr ((B 1)^3))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let m := ULift.{u} Unit
  let n := ULift.{v} Unit
  have hS : (direction (0 : Matrix m m ℂ) (0 : Matrix m n ℂ) 0).PosSemidef := by
    simpa [direction] using (Matrix.PosSemidef.zero : (0 : Matrix (m ⊕ n) (m ⊕ n) ℂ).PosSemidef)
  exact h (m := m) (n := n) 1 (by norm_num) 0 0 0 hS 0
    (by simp : (0 : Matrix (m ⊕ n) (m ⊕ n) ℂ).IsHermitian)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0,0), (-1,0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.actual_twoLevel_supplier.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.actual_twoLevel_supplier.{u,v},
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.actual_twoLevel_supplier.{u,v})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => 0 ≤ s.1 ∧ s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Transported

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (r : ℝ), 0 < r → ∀ (c : ℝ), 0 < c →
    ∀ (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ),
    (direction A C H).PosSemidef →
    ∀ (q : (m ⊕ n) ≃ ι) (U : unitary (Matrix ι ι ℂ))
      (Z : Matrix ι ι ℂ), Z.IsHermitian →
    let e := spectralFrame q U
    let Y := c • e ((baseRoot (m := m) (n := n) r)^3)
    let K := c • e (baseDirection r A C H)
    let P := CFC.rpow Y (1/3 : ℝ)
    let B := jetCoeff (fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹)
    F.readout () () (kappa r/6*pairEnergy A C H,
      tr (B 3)+2*tr (Z*B 2)+tr (B 1*Z*Z)-(5/48 : ℝ)*tr ((B 1)^3))

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let m := ULift.{u} Empty
  let n := ULift.{v} Empty
  let ι := ULift.{w} Empty
  have hS : (direction (0 : Matrix m m ℂ) (0 : Matrix m n ℂ) 0).PosSemidef := by
    simpa [direction] using (Matrix.PosSemidef.zero : (0 : Matrix (m ⊕ n) (m ⊕ n) ℂ).PosSemidef)
  exact h (m := m) (n := n) (ι := ι) 1 (by norm_num) 1 (by norm_num) 0 0 0 hS
    (Equiv.equivOfIsEmpty _ _) 1 0 (by simp : (0 : Matrix ι ι ℂ).IsHermitian)

private theorem sensitivity : Sensitivity arena.{u,v,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u,v,w}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.transported_twoLevel_supplier.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.transported_twoLevel_supplier.{u,v,w},
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.transported_twoLevel_supplier.{u,v,w})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.Transported.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge.Transported.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => 0 ≤ s.1 ∧ s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transported

end
end Reg.D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
