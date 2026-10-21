import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

def probeLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intros; rfl
  even_diagonal := by intro; exact ⟨1, rfl⟩

def probeIndex : Index probeLattice := (⟨0, by decide⟩, 0)

namespace DerivationReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Index lattice)
  (fun parameter => CorrectionPolynomial parameter.1)
  (fun parameter => CorrectionPolynomial parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => pairDerivation parameter.1 parameter.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, probeIndex⟩, 0, MvPolynomial.X (some probeIndex), ?_⟩
  simp only [actual, realize, map_zero]
  rw [show pairDerivation probeLattice probeIndex (MvPolynomial.X (some probeIndex)) =
    pairPolynomial probeLattice probeIndex probeIndex by
      simp [pairDerivation, MvPolynomial.mkDerivation_X]]
  intro equal
  have value := congrArg (MvPolynomial.eval (fun _ : Option (Index probeLattice) => (1 : ℂ))) equal
  norm_num [pairPolynomial, pairScalar, sourceWeight, halfBinomial, probeIndex, probeLattice] at value
  change (2 : ℤ) = 0 at value
  norm_num at value

end DerivationReadout

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
