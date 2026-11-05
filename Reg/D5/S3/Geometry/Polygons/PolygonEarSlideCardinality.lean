import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonEarSlideCardinality
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Polygons.PolygonEarSlideCardinality
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := {n : ℕ // 14 ≤ n}
  State n := Finset (ZMod n.1) × Finset (ZMod n.1) ×
    Finset (ZMod n.1) × Finset (ZMod n.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ n S => by
    letI : NeZero n.1 := ⟨by have := n.2; omega⟩
    exact Nat.card (ConditionFiber S.1 S.2.1 S.2.2.1 S.2.2.2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) [NeZero n] (hn : 14 ≤ n) (a : ZMod n)
    (P Q J R : Finset (ZMod n)), J ⊆ E_K (P ∪ Q) →
    a ∉ J → a + 1 ∈ J → a + 2 ∈ J →
    R ⊆ ((J.erase (a + 1)).erase (a + 2)).erase (a + 3) →
    O.readout () ⟨n, hn⟩ (P, Q, J, insert (a + 2) R) =
      O.readout () ⟨n, hn⟩ (P, Q, J, insert (a + 1) R) +
        if a + 3 ∈ J then
          O.readout () ⟨n, hn⟩ (P, Q, J, insert (a + 3) (insert (a + 1) R))
        else 0

theorem actual_law : arena.Law actual := by
  intro n _ hn a P Q J R hJ ha0 ha1 ha2 hR
  exact _root_.D5.S3.Geometry.Polygons.PolygonEarSlideCardinality.condition_fibre_card_at
    hn a hJ ha0 ha1 ha2 hR

abbrev source_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonEarSlideCardinality.condition_fibre_card_at)

def source : source_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonEarSlideCardinality.condition_fibre_card_at

/-!
This dependent-family candidate preserves the original telescope and
uses the actual complete-fibre cardinality as its observation. It is not a
Contract.Registration. Source selection and reconstruction binding evidence,
a rejected realization, whole-family sensitivity, and actual observational
dependence remain unproved. In particular, positivity or variation of complete
conditioned polygon fibre counts is not supplied by the local cardinality law.
-/
end Reg.D5.S3.Geometry.Polygons.PolygonEarSlideCardinality
