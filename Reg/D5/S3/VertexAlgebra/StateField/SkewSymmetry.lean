/- Faithful source reconstruction attempt. No validated registration is claimed.
The per-module equality readout degenerates on the zero module; full-family
realization/binding remains open. Keep the exact original theorem telescope.
-/
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.StateField.SkewSymmetry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Reg.D5.S3.VertexAlgebra.StateField.SkewSymmetry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
open _root_.D5.S3.VertexAlgebra.StateField.SkewSymmetry
open scoped VertexOperator
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

def equalitySignature (W : Type u) : Signature :=
  { Params := Unit
    State := fun _ => W × W
    Role := Unit
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ _ => Prop
    Anchor := Empty
    finiteAnchor := inferInstance }

def equalityReadout (W : Type u) : Realization (equalitySignature W) where
  readout _ _ p := p.1 = p.2
  anchor e := nomatch e

def creationArena : Arena where
  signature := equalitySignature V
  Law R := ∀ (A : StateFieldVertexAlgebra V) (v : V) (j : ℕ),
    R.readout () () (((A.stateField v)[[-(j : ℤ)-1]]) A.vacuum,
      (j.factorial : ℂ)⁻¹ • (A.translation ^ j) v)

theorem creation_source_bridge :
    (type_of% (@creation_coeff V _ _)) ↔ (creationArena (V := V)).Law (equalityReadout V) :=
  Iff.rfl

def finiteSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℕ) (fun _ => Prop)

def finiteReadout : Realization finiteSignature where
  readout _ _ s := s.Finite
  anchor e := nomatch e

def finiteArena : Arena where
  signature := finiteSignature
  Law R := ∀ (T : Module.End ℂ V) (s : HahnSeries ℤ V) (k : ℤ),
    R.readout () () (Function.support (reversalTerm T s k))

theorem finite_source_bridge :
    (type_of% (@reversal_finite V _ _)) ↔ (finiteArena (V := V)).Law finiteReadout :=
  Iff.rfl

def boundedSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℤ) (fun _ => Prop)

def boundedReadout : Realization boundedSignature where
  readout _ _ s := BddBelow s
  anchor e := nomatch e

def boundedArena : Arena where
  signature := boundedSignature
  Law R := ∀ (T : Module.End ℂ V) (s : HahnSeries ℤ V),
    R.readout () () (Function.support (fun k : ℤ => ∑ᶠ j : ℕ, reversalTerm T s k j))

theorem bounded_source_bridge :
    (type_of% (@reversal_bounded V _ _)) ↔ (boundedArena (V := V)).Law boundedReadout :=
  Iff.rfl

/-- A degenerate fiber really has constant equality readout. This is an audit
obstruction for this attempted per-fiber arena, not a restriction on skew symmetry. -/
theorem degenerate_equality_readout (W : Type u) [Subsingleton W] :
    ¬ ObservationalDependence (equalitySignature W) (equalityReadout W) := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  apply hxy
  apply propext
  constructor <;> intro _ <;> exact Subsingleton.elim _ _

/-- The complete original skew theorem remains the reconstruction target,
including its support conjunct and its series equality, with no weakened fiber. -/
def skewSource : Prop := type_of% (@skew_symmetry V _ _)

theorem skew_source_bridge :
    (type_of% (@skew_symmetry V _ _)) ↔ skewSource (V := V) := Iff.rfl

end Reg.D5.S3.VertexAlgebra.StateField.SkewSymmetry
