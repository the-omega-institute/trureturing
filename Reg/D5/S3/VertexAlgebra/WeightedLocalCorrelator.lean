import D5.S3.VertexAlgebra.WeightedLocalCorrelator
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.ULift

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.WeightedLocalCorrelator
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open _root_.D5.S3.VertexAlgebra.WeightedLocalCorrelator
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u
noncomputable section

structure Parameters where
  N : ℕ
  V : Type u
  [addGroup : AddCommGroup V]
  [module : Module ℂ V]
  A : Fin N → VertexOperator ℂ V
  orders : Fin N × Fin N → ℕ
  locality : ∀ i j : Fin N, i < j →
    (deltaEnd ^ orders (i, j)) (FieldNormalProductLocality.commutator (A i) (A j)) = 0
  l : List (Fin N)
  nodup : l.Nodup
  allLabels : ∀ i, i ∈ l

attribute [instance] Parameters.addGroup Parameters.module

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.V × Module.End ℂ p.V × List (Fin p.N)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Distribution p.N p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p input =>
    let (v, P, order) := input
    polynomialAction (weightedClearingPolynomial p.orders)
      (coefficientDistribution p.A v P order))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ p v P,
    (∀ r, p.l.Perm r → R.readout () p (v, P, p.l) = R.readout () p (v, P, r)) ∧
    (∀ i, LowerBoundIn (R.readout () p (v, P, p.l)) i
      (((HahnModule.of ℂ).symm (p.A i v)).order)) ∧
    (∀ total : ℤ, {e : Exponent p.N | totalExponent e = total ∧
      R.readout () p (v, P, p.l) e ≠ 0}.Finite)

set_option maxHeartbeats 2000000 in
-- The dependent field and module instances are reconstructed at their original universe.
theorem source_bridge : (type_of% (@common_cleared_fields.{u})) ↔
    arena.{u}.Law actual.{u} := by
  constructor
  · intro h p v P
    exact h p.A v P p.orders p.locality p.l p.nodup p.allLabels
  · intro h N V addGroup module A v P orders locality l nodup allLabels
    let p : Parameters.{u} := {
      N := N
      V := V
      A := A
      orders := orders
      locality := locality
      l := l
      nodup := nodup
      allLabels := allLabels }
    exact h p v P

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.{u}.mp (@common_cleared_fields.{u})

/-- An intervention that discards the fields and keeps the actual input and map. -/
def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ input => fun _ => input.2.1 input.1)
  (fun empty => nomatch empty)

private def oneLabel : Parameters.{u} where
  N := 1
  V := ULift.{u} ℂ
  A := fun _ => 0
  orders := fun _ => 0
  locality := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    omega
  l := [0]
  nodup := by simp
  allLabels := by intro i; fin_cases i; simp

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro law
  have lower := (law oneLabel (ULift.up (1 : ℂ)) 1).2.1 (0 : Fin 1)
  have zero := lower (fun _ => -1) (by simp [oneLabel])
  have impossible : (ULift.up (1 : ℂ) : ULift.{u} ℂ) = 0 := by
    simpa [rejected, realize] using zero
  have := congrArg ULift.down impossible
  simpa using this

private def noLabels : Parameters.{u} where
  N := 0
  V := ULift.{u} ℂ
  A := fun i => Fin.elim0 i
  orders := fun _ => 0
  locality := by intro i; exact Fin.elim0 i
  l := []
  nodup := by simp
  allLabels := by intro i; exact Fin.elim0 i

private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  refine ⟨noLabels, (ULift.up (1 : ℂ), 1, []), (ULift.up (1 : ℂ), 0, []), ?_⟩
  intro equal
  have coefficient := congrFun equal (fun i => Fin.elim0 i)
  have impossible : (ULift.up (1 : ℂ) : ULift.{u} ℂ) = 0 := by
    simpa [actual, realize, noLabels, weightedClearingPolynomial, labelledPairs,
      coefficientDistribution, word] using coefficient
  have := congrArg ULift.down impossible
  simpa using this

def familyRegistration : Registration arena.{u} (type_of% (@common_cleared_fields.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext empty
        exact nomatch empty
    · intro empty
      exact nomatch empty
  dependence := actual_dependence

/-- The source selectors are unresolved; the compiled family proofs do not supply them. -/
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_cleared_fields.{u}) (Realization signature.{u}) (Type u) Unit where
  unitName := `D5.S3.VertexAlgebra.WeightedLocalCorrelator.common_cleared_fields.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.WeightedLocalCorrelator.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.WeightedLocalCorrelator
