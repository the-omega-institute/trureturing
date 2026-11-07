import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonCyclicCrossing
import Reg.Support.DependentFamily

/-! Complete source families for actual cyclic arc and chord observations. -/

namespace Reg.D5.S3.Geometry.Polygons.PolygonCyclicCrossing
open _root_.D5.S3.Geometry.Polygons.PolygonCyclicCrossing
open _root_.D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Module
universe u

structure Parameters where
  E : Type u
  group : NormedAddCommGroup E
  space : @NormedSpace ℝ E _ group.toSeminormedAddCommGroup
  n : ℕ
  nonzero : NeZero n
attribute [instance] Parameters.group Parameters.space Parameters.nonzero

abbrev Labels (p : Parameters.{u}) := ZMod p.n × ZMod p.n × ZMod p.n × ZMod p.n

namespace Arc
abbrev source_scope := type_of% (@same_arc_sign.{u})
def source : source_scope.{u} := @same_arc_sign.{u}
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Polygon p.E p.n × Labels p × (p.E →L[ℝ] ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ q =>
    (q.2.2 (vertex q.1 q.2.1.2.2.1) - q.2.2 (vertex q.1 q.2.1.1)) *
    (q.2.2 (vertex q.1 q.2.1.2.2.2) - q.2.2 (vertex q.1 q.2.1.1))) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2) (hn : 3 ≤ p.n)
    (poly : Polygon p.E p.n) (B : BoundaryModel poly) (a b c d : ZMod p.n),
    a ≠ b → sbtw a c b → sbtw a d b → ∀ (f : p.E →L[ℝ] ℝ), f ≠ 0 →
    f (vertex poly b) = f (vertex poly a) → O.readout () p (poly,(a,b,c,d),f) > 0
theorem bridge : source_scope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p hdim hn poly B a b c d hab hc hd f hf hfab
    exact @h p.E p.group p.space p.n p.nonzero hdim hn poly B a b c d hab hc hd f hf hfab
  · intro h E group space n nonzero hdim hn poly B a b c d hab hc hd f hf hfab
    exact h ⟨E,group,space,n,nonzero⟩ hdim hn poly B a b c d hab hc hd f hf hfab
theorem actual_law : arena.{u}.Law actual.{u} := bridge.{u}.mp source.{u}
noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => nomatch e)
end Arc

namespace Side
abbrev source_scope := type_of% (@sOppSide_iff_cross.{u})
def source : source_scope.{u} := @sOppSide_iff_cross.{u}
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Polygon p.E p.n × Labels p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ q =>
    line[ℝ,vertex q.1 q.2.1,vertex q.1 q.2.2.1].SOppSide
      (vertex q.1 q.2.2.2.1) (vertex q.1 q.2.2.2.2)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2) (hn : 3 ≤ p.n)
    (poly : Polygon p.E p.n) (B : BoundaryModel poly) (a b c d : ZMod p.n),
    a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
    (O.readout () p (poly,(a,b,c,d)) ↔ Carrier.Cross s(a,b) s(c,d))
theorem bridge : source_scope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p hdim hn poly B a b c d hab hca hcb hda hdb
    exact @h p.E p.group p.space p.n p.nonzero hdim hn poly B a b c d hab hca hcb hda hdb
  · intro h E group space n nonzero hdim hn poly B a b c d hab hca hcb hda hdb
    exact h ⟨E,group,space,n,nonzero⟩ hdim hn poly B a b c d hab hca hcb hda hdb
theorem actual_law : arena.{u}.Law actual.{u} := bridge.{u}.mp source.{u}
noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)
end Side

namespace Crossing
abbrev source_scope := type_of% (@cross_iff_properCross.{u})
def source : source_scope.{u} := @cross_iff_properCross.{u}
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Polygon p.E p.n × Sym2 (ZMod p.n) × Sym2 (ZMod p.n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ q => ProperCross q.1 q.2.1 q.2.2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2) (hn : 3 ≤ p.n)
    (poly : Polygon p.E p.n) (B : BoundaryModel poly) (e f : Sym2 (ZMod p.n)),
    Carrier.Cross e f ↔ O.readout () p (poly,e,f)
theorem bridge : source_scope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p hdim hn poly B e f
    exact @h p.E p.group p.space p.n p.nonzero hdim hn poly B e f
  · intro h E group space n nonzero hdim hn poly B e f
    exact h ⟨E,group,space,n,nonzero⟩ hdim hn poly B e f
theorem actual_law : arena.{u}.Law actual.{u} := bridge.{u}.mp source.{u}
noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => True) (fun e => nomatch e)
end Crossing

/-!
The source telescopes and exact equivalence bridges retain every ambient type,
instance, polygon, size, boundary hypothesis, label, functional and chord.
These are partial source-family operands, not closed Contract.Registration values.
Full-family rejected-law, variation, sensitivity, observational dependence and
raw source-selection binding remain required; no declared_validated claim is made.
-/
end Reg.D5.S3.Geometry.Polygons.PolygonCyclicCrossing
