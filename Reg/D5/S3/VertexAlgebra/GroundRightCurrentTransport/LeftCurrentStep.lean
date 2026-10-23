import D5.S3.VertexAlgebra.GroundRightCurrentTransport.LeftCurrentStep
import Reg.Support.SingleDependentReadout

/-! Complete source-bound readout reconstruction. Four-slot registration remains
unfinished under issue #20510: lawful template/source binding and whole-family
variation, sensitivity and actual observational dependence are missing.
No declared_validated registration is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.LeftCurrentStep
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockPhysicalRescaling
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockGroundRightCurrentTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  a : Carrier D
  gamma : ℤ
  d : ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Carrier p.D × ℤ × ℤ)
    (fun p => VertexOperator ℂ (ActualTensor p.D p.hu))
def actual : Realization signature := realize signature (fun _ p x =>
  targetSlice p.D p.hu (mu p.D (neutralMode p.D p.i p.d p.a) x.2.2 x.1)
    ((p.gamma + 1) + x.2.1)) (fun empty => nomatch empty)
def smaller (p : Params) : Prop := ∀ (b : Carrier p.D) (delta : ℤ),
  OriginalCompatible p.D p.hu p.a b p.gamma delta
def arena : Arena where
  signature := signature
  Law R := ∀ (p : Params) (b : Carrier p.D) (delta r : ℤ), smaller p →
    R.readout () p (b, delta, r) =
      nativeProduct p.D p.hu (neutralMode p.D p.i p.d p.a) b (p.gamma + 1) delta r

theorem source_bridge : (type_of% (@left_current_step)) ↔ arena.Law actual := by
  constructor
  · intro h p b delta r law
    exact sub_eq_zero.mp (compatible_defect p.D p.hu
      (neutralMode p.D p.i p.d p.a) b (p.gamma+1) delta
      (h p.D p.hu p.i p.a p.gamma p.d law b delta) r)
  · intro h D hu i a gamma d law b delta
    apply defect_compatible D hu
    intro r
    exact sub_eq_zero.mpr (h ⟨D, hu, i, a, gamma, d⟩ b delta r law)

theorem actual_law : arena.Law actual := source_bridge.mp (@left_current_step)
end
end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.LeftCurrentStep
