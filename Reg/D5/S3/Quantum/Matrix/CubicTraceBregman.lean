import D5.S3.Quantum.Matrix.CubicTraceBregman
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Scalar observations retain the complete source matrix telescopes. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.CubicTraceBregman
noncomputable section
universe u

private abbrev pairSignature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Coercivity
private def actual : Realization pairSignature :=
  realize pairSignature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)
private def rejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence pairSignature actual := by
  intro i
  exact ⟨(), (0, 0), (1, 0), by norm_num [actual, realize]⟩
private abbrev arena : Arena where
  signature := pairSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) (hA : A.PosSemidef) (hT : T.PosSemidef),
    let H := A - T
    let hH : H.IsHermitian := hA.isHermitian.sub hT.isHermitian
    R.readout () () ((T * H ^ 2).trace.re + (∑ i, |hH.eigenvalues i| ^ 3),
      (A ^ 3).trace.re - 3 * (T ^ 2 * A).trace.re + 2 * (T ^ 3).trace.re)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.CubicTraceBregman.cubic_trace_bregman_ge_weighted_square_add_abs_cube.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @_root_.D5.S3.Quantum.Matrix.CubicTraceBregman.cubic_trace_bregman_ge_weighted_square_add_abs_cube.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.CubicTraceBregman.cubic_trace_bregman_ge_weighted_square_add_abs_cube.{u})
    (Realization pairSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CubicTraceBregman.Coercivity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CubicTraceBregman.Coercivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Coercivity

namespace TwoLevel
private def actual : Realization pairSignature :=
  realize pairSignature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)
private def rejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence pairSignature actual := by
  intro i
  exact ⟨(), (0, 0), (1, 0), by norm_num [actual, realize]⟩
private abbrev arena : Arena where
  signature := pairSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (a b q : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (E : Matrix Unit n ℂ) (D : Matrix n n ℂ),
    let T : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
      Matrix.fromBlocks ((a : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0
        ((b : ℂ) • (1 : Matrix n n ℂ))
    let X : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
      Matrix.fromBlocks (((a + q : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) E Eᴴ
        (((b : ℂ) • (1 : Matrix n n ℂ)) + D)
    let W : ℝ := a * q ^ 2 + b * (Dᴴ * D).trace.re +
      (a + b) * (E * Eᴴ).trace.re
    X.PosSemidef → R.readout () () (max (W + |q| ^ 3) (2 * W),
      (X ^ 3).trace.re - 3 * (T ^ 2 * X).trace.re + 2 * (T ^ 3).trace.re)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero : (Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit (ULift.{u} Unit) ℂ)
      0 (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)).PosSemidef := by
    simpa only [Matrix.fromBlocks_zero] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Unit ⊕ ULift.{u} Unit) (Unit ⊕ ULift.{u} Unit) ℂ).PosSemidef)
  exact h (n := ULift.{u} Unit) 0 0 0 le_rfl le_rfl 0 0 (by simpa using hzero)
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.CubicTraceBregman.two_level_cubic_bregman_controls_components.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @_root_.D5.S3.Quantum.Matrix.CubicTraceBregman.two_level_cubic_bregman_controls_components.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.CubicTraceBregman.two_level_cubic_bregman_controls_components.{u})
    (Realization pairSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CubicTraceBregman.TwoLevel.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CubicTraceBregman.TwoLevel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end TwoLevel

end

end Reg.D5.S3.Quantum.Matrix.CubicTraceBregman
