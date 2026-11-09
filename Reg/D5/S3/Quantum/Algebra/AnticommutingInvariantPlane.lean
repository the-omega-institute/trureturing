import D5.S3.Quantum.Algebra.AnticommutingInvariantPlane
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Complete source reconstruction for the positive-branch coordinate construction.
These declarations supply the actual readout, exact bridge and actual law.
Whole-family variation, role sensitivity, observational dependence and source
occurrence evidence remain outside this partial audit. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Reg.D5.S3.Quantum.Algebra.AnticommutingInvariantPlane

open _root_.D5.S3.Quantum.Algebra.AnticommutingInvariantPlane
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Carrier where
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  [nontrivial : Nontrivial H]
  R : Type v
  [cstar : CStarAlgebra R]

attribute [instance] Carrier.normed Carrier.inner Carrier.complete Carrier.nontrivial Carrier.cstar

structure Inputs (P : Carrier.{u,v}) where
  representation : P.R →⋆ₐ[ℂ] (P.H →L[ℂ] P.H)
  a : P.R
  b : P.R
  d : P.R
  X : ℝ
  Y : ℝ

abbrev signature : Signature where
  Params := Carrier.{u,v}
  State := Inputs
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def predicate (P : Carrier.{u,v}) (q : Inputs P) : Prop :=
  ∃ (z : ℝ) (U : P.H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2)),
    (∀ x, U (q.representation q.a x) 0 = (q.X : ℂ) * U x 0 ∧
      U (q.representation q.a x) 1 = -(q.X : ℂ) * U x 1) ∧
    (∀ x, U (q.representation q.b x) 0 = (q.Y : ℂ) * U x 1 ∧
      U (q.representation q.b x) 1 = (q.Y : ℂ) * U x 0) ∧
    (∀ x, U (q.representation q.d x) 0 = -(Complex.I * (z : ℂ)) * U x 1 ∧
      U (q.representation q.d x) 1 = (Complex.I * (z : ℂ)) * U x 0)

def actual : Realization signature.{u,v} :=
  realize signature (fun _ P q => predicate P q) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law F := ∀ (P : Carrier.{u,v}) (q : Inputs P),
    0 < q.X → 0 < q.Y →
    IsSelfAdjoint q.a → IsSelfAdjoint q.b → IsSelfAdjoint q.d →
    q.a * q.b = -(q.b * q.a) → q.a * q.d = -(q.d * q.a) →
    q.b * q.d = -(q.d * q.b) →
    q.representation q.a * q.representation q.a = (q.X ^ 2) • (1 : P.H →L[ℂ] P.H) →
    q.representation q.b * q.representation q.b = (q.Y ^ 2) • (1 : P.H →L[ℂ] P.H) →
    (StarAlgebra.adjoin ℂ ({q.a,q.b,q.d} : Set P.R)).topologicalClosure = ⊤ →
    InnerProductSpace.IsTopologicallyIrreducible (Set.range q.representation) →
    F.readout () P q

abbrev sourceScope : Prop := type_of% (@positive_branch_coordinates.{u,v})

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h P q
    exact h q.representation q.a q.b q.d q.X q.Y
  · intro h H normed inner complete nontrivial R cstar π a b d X Y
    exact h ⟨H,R⟩ ⟨π,a,b,d,X,Y⟩

theorem actual_law : arena.{u,v}.Law actual :=
  source_bridge.mp (@positive_branch_coordinates.{u,v})

end Reg.D5.S3.Quantum.Algebra.AnticommutingInvariantPlane
