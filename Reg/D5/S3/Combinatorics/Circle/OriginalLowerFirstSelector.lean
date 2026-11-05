import D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
import Reg.Support.DependentFamily

/-! The source family's actual law is proved below. A full registration also
needs lawful source reconstruction and whole-family variation/sensitivity.
In particular a rejected constant readout needs a witness of the exact
m>5/e=1/F>=4/y/a0/quotient/remainder source corner. No such source is assumed
or manufactured here, and no Contract.Registration is asserted.
The missing binding and sensitivity evidence is scoped in
https://github.com/the-omega-institute/trureturing/issues/21811. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
open _root_.D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
open _root_.D5.S3.Combinatorics.Circle.OriginalLowerFullBank
open _root_.D5.S3.Combinatorics.Circle.M5FullWordConsumer
open _root_.D5.S3.Combinatorics.Circle.SourceWidth

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p => actualSource p.1 p.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (hm : 5 < m)
    (he : (sourceCoordinates h).e = 1)
    (hF : 4 ≤ (sourceCoordinates h).F)
    (hLower : (sourceCoordinates h).F ≤ (sourceCoordinates h).H / 4)
    (hy : (sourceCoordinates h).y ≤ 2 * b - 3)
    (ha0 : 2 * b + 1 ≤ (sourceCoordinates h).a0)
    (hell : ((sourceCoordinates h).N + (sourceCoordinates h).z -
      2 * (sourceCoordinates h).a0) / 2 / b ≤ (sourceCoordinates h).q - 3)
    (hr : ((sourceCoordinates h).y - 1) / 2 <
      (((sourceCoordinates h).N + (sourceCoordinates h).z -
        2 * (sourceCoordinates h).a0) / 2) % b),
    FirstStep h (R.readout () ⟨k, t⟩)

theorem actual_law : arena.Law actual := by
  intro m k t L a b p d x h hm he hF hLower hy ha0 hell hr
  exact canonical_lower_first_selector h hm he hF hLower hy ha0 hell hr

end Reg.D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
