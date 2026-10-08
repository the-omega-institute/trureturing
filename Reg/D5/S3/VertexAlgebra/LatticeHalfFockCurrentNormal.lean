import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
import Reg.Support.DependentFamily

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Complex
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => frequency (-j-1)) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ j : Int, readout.readout () () j = -frequency j

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have bad := law 0
  change (0 : Complex) = -frequency 0 at bad
  norm_num [frequency] at bad

def registration : Registration arena (∀ j : Int, frequency (-j-1) = -frequency j) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨frequency_opposite, rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change frequency (-0-1) ≠ frequency (-1-1)
    norm_num [frequency]

register_information_theorem
  _root_.D5.S3.VertexAlgebra.LatticeHalfFock.frequency_opposite in arena
  readout via (realize signature (fun _ _ j => frequency (-j-1))
    (fun empty => nomatch empty))
  realizes registration
  escape from source ({
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
