import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceCurrentIterate
import Reg.Support.SingleDependentReadout
/-! Exact finite source-current field readout. Four-slot registration remains
unfinished under issue #20510; lawful final template/source binding and
whole-family variation, sensitivity and observational dependence are absent.
No declared_validated registration is claimed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceCurrentIterate
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockPhysicalRescaling
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeAllStateField LatticeHalfFockLeftCurrentTransport LatticeHalfFockGroundRightCurrentTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator
noncomputable section
local macro "upper" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.upper))
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  b : Carrier D
  K : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => Unit) (fun p => VertexOperator ℂ (ActualTensor p.D p.hu))
def left (p : Params) (j : ℕ) : VertexOperator ℂ (ActualTensor p.D p.hu) :=
  BinomialKernelDelta.chooseSign p.d j • targetSlice p.D p.hu
    (neutralMode p.D p.i (p.d-j) (mu p.D p.a (p.r+j) p.b)) (p.gamma+p.delta+1)
def right (p : Params) (j : ℕ) : VertexOperator ℂ (ActualTensor p.D p.hu) :=
  BinomialKernelDelta.chooseSign p.d j • targetSlice p.D p.hu
    (mu p.D p.a (p.d+p.r-j) (neutralMode p.D p.i j p.b)) (p.gamma+p.delta+1)
def actual : Realization signature := realize signature (fun _ p _ =>
  targetSlice p.D p.hu (mu p.D (neutralMode p.D p.i p.d p.a) p.r p.b)
    (p.gamma+p.delta+1)) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law R := ∀ (p : Params), upper (Y p.D p.a) p.b ≤ p.K →
    Function.HasFiniteSupport (left p) ∧ Function.HasFiniteSupport (right p) ∧
      R.readout () p () =
        (∑ j ∈ Finset.range ((p.K : ℤ)-p.r).toNat, left p j) -
          StateFieldResidueReconstruction.epsilon p.d •
            ∑ j ∈ Finset.range (vectorFrequencyBound p.D p.b+1), right p j

theorem source_bridge : (type_of% (@source_current_iterate_slice)) ↔ arena.Law actual := by
  constructor
  · intro h p bound
    exact h p.D p.hu p.i p.a p.b p.K bound p.gamma p.delta p.d p.r
  · intro h D hu i a b K bound gamma delta d r
    exact h ⟨D, hu, i, a, b, K, gamma, delta, d, r⟩ bound

theorem actual_law : arena.Law actual := source_bridge.mp (@source_current_iterate_slice)
end
end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceCurrentIterate
