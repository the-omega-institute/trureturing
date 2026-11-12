import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Hankel.SunA006077Binary

/-! Direct determinant observations of the Rueppel evaluations are constant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Hankel.SunA006077Binary

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Hankel.SunA006077

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i _ n => if i then T n else S n) (fun e => nomatch e)

/-- The original two determinant functions cannot supply actual observational dependence. -/
theorem observation_obstruction : ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p,x,y,hxy⟩ := h false
  change S x ≠ S y at hxy
  rw [(rueppel_determinants x).1,(rueppel_determinants y).1] at hxy
  exact hxy rfl

end
end Reg.D5.S3.Combinatorics.Hankel.SunA006077Binary
