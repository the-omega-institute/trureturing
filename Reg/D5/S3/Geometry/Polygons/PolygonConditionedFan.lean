import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonConditionedFan
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Polygons.PolygonConditionedFan
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open _root_.D5.S3.Geometry.Polygons.PolygonConditionedFan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Triangulation

abbrev source_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonConditionedFan.fan_triangulation)

def source : source_scope := @_root_.D5.S3.Geometry.Polygons.PolygonConditionedFan.fan_triangulation

abbrev signature : Signature where
  Params := {n : ℕ // 6 ≤ n}
  State n := Finset (Sym2 (ZMod n.1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ n T => by
    letI : NeZero n.1 := ⟨by have := n.2; omega⟩
    exact IsTriangulation T) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) [NeZero n] (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hP : Independent P) (hh : h ∉ P),
    O.readout () ⟨n, hn⟩ (fan P h) ∧ P ⊆ EarCenters (fan P h) ∧
      EarCenters (fan P h) ⊆ P ∪ {h - 1, h + 1}

theorem actual_law : arena.Law actual := by
  intro n _ hn P h hP hh
  exact fan_triangulation hn P h hP hh

end Triangulation

namespace Crossings

abbrev source_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonConditionedFan.fan_two_crossings)

def source : source_scope := @_root_.D5.S3.Geometry.Polygons.PolygonConditionedFan.fan_two_crossings

abbrev signature : Signature where
  Params := {n : ℕ // 6 ≤ n}
  State n := Finset (Sym2 (ZMod n.1)) × ZMod n.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ n T => by
    letI : NeZero n.1 := ⟨by have := n.2; omega⟩
    exact ∃ e ∈ T.1, ∃ f ∈ T.1, e ≠ f ∧ IsDiagonal e ∧ IsDiagonal f ∧
      Cross e (ear T.2) ∧ Cross f (ear T.2)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) [NeZero n] (hn : 6 ≤ n) (P : Finset (ZMod n)) (h : ZMod n)
    (hsize : P.card + 4 < n),
    O.readout () ⟨n, hn⟩ (fan P h, h)

theorem actual_law : arena.Law actual := by
  intro n _ hn P h hsize
  exact fan_two_crossings hn P h hsize

end Crossings

namespace Source

abbrev source_scope := type_of% (@_root_.D5.S3.Geometry.Polygons.PolygonConditionedFan.source_conditioned_witnesses)

def source : source_scope := @_root_.D5.S3.Geometry.Polygons.PolygonConditionedFan.source_conditioned_witnesses

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
  realize signature (fun _ n T => by
    letI : NeZero n.1 := ⟨by have := n.2; omega⟩
    exact Nat.card (ConditionFiber T.1 T.2.1 T.2.2.1 T.2.2.2)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) [NeZero n] (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hdisj : Disjoint P Q)
    (hcompat : (↑(P ∪ Q) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : (P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
      (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)),
    Nonempty (ConditionFiber P Q ∅ ∅) ∧
      0 < O.readout () ⟨n, hn⟩ (P, Q, ∅, ∅) ∧
      (∃ h : ZMod n, h ∉ P ∧
        ∃ T : ConditionFiber P Q ∅ ∅, T.val = fan P h) ∧
      ∀ H : Finset (ZMod n), H ⊆ E_K (P ∪ Q) →
        (H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)) →
        ∀ h ∈ H, ∃ T : ConditionFiber P Q H ∅, T.val = fan P h ∧
          ∃ e ∈ T.val, ∃ f ∈ T.val, e ≠ f ∧ IsDiagonal e ∧ IsDiagonal f ∧
            Cross e (ear h) ∧ Cross f (ear h)

theorem actual_law : arena.Law actual := by
  intro n _ hn P Q hd hc hcases
  exact source_conditioned_witnesses hn P Q hd hc hcases

end Source

/-!
Each candidate retains its exact source telescope and an actual readout through
the enrolled DependentFamily.realize template. A full Contract.Registration
requires source selection and reconstruction binding, a statement-to-law bridge,
a rejected realization, whole-family variation and sensitivity, and actual
observational dependence. Those obligations are not asserted by these candidates.
The continuation can be unknown only after the other required evidence is supplied.
-/

end Reg.D5.S3.Geometry.Polygons.PolygonConditionedFan
