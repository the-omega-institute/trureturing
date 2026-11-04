import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.CanonicalOccupationSewing
open _root_.D5.S3.VertexAlgebra.CanonicalFullChargeLoop

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop

/-- The source predicate is summability of an unrestricted real family. -/
abbrev signature : Signature where
  Params := Type
  State σ := σ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ f => Summable f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ℕ, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) :=
    Eq.mp h (show Summable (fun _ : ℕ => (0 : ℝ)) from summable_zero)
  simpa only [summable_const_iff, one_ne_zero] using hs

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (D : LatticeData)
    (_ : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (_ : ‖q1‖ < 1) (_ : ‖q2‖ < 1),
    F.readout () (Charge D × (Occ D × Occ D))
      (fun z => ‖loopTerm D a u v r s q1 q2 z‖)

private theorem source_bridge :
    (type_of% (@full_charge_loop_summable)) ↔ arena.Law actual := Iff.rfl

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem zeroPositive : Matrix.PosDef (zeroLattice.G.map (Int.cast : ℤ → ℝ)) := by
  constructor
  · ext i; exact Fin.elim0 i
  · intro x hx
    apply False.elim
    apply hx
    ext i
    exact Fin.elim0 i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice zeroPositive 0 0 0 0 0 0 0 (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@full_charge_loop_summable)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp full_charge_loop_summable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_charge_loop_summable) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family


namespace Trace

abbrev signature : Signature where
  Params := Type
  State α := α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := α → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ℕ, 0, 1, ?_⟩
  intro h
  have hh : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  omega

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (D : LatticeData)
    (_ : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (_ : ‖q1‖ < 1) (_ : ‖q2‖ < 1),
    Summable (fun nm : ℕ × ℕ => ‖q1^nm.1*q2^nm.2*blockTrace D a u v r s nm.1 nm.2‖) ∧
    F.readout () ℂ
      (∑' z : Charge D × (Occ D × Occ D), loopTerm D a u v r s q1 q2 z)
      (∑' nm : ℕ × ℕ, q1^nm.1*q2^nm.2*blockTrace D a u v r s nm.1 nm.2)

private theorem source_bridge : (type_of% (@full_charge_loop_trace)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h zeroLattice zeroPositive 0 0 0 0 0 0 0 (by norm_num) (by norm_num)).2

def family : Registration arena (type_of% (@full_charge_loop_trace)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp full_charge_loop_trace, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_charge_loop_trace) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop.Trace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop.Trace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Trace
end Reg.D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop
