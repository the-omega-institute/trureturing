/- GID: D5/S3/Geometry/Gluing/PolygonMarkedEndpointChains
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/PolygonMarkedEndpointChains
   mirror-E: none(waiver:polygon-marked-endpoint-chain-reflection)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.Circle]
   utility: none
   digest: Circular polygon point chains restrict exactly to marked cyclic endpoint chains. -/

/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors

Selected source reuse from mccorvie/classification-of-surfaces,
revision e3c7230fe78d7b056a415d9ecae6f77887046b32,
ClassificationOfSurfaces/PolygonalQuotient.lean (Apache-2.0).
The cell, side, instruction and generated-relation definitions below keep the
original namespace and contract. Unconsumed convenience declarations are omitted.
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace LeanEval.Topology.ClassificationOfSurfaces
structure PolygonCell (_n : ℕ) where
  /-- The `val` declaration. -/
  val : ℂ
  property : val ∈ Metric.closedBall (0 : ℂ) 1

namespace PolygonCell

instance (n : ℕ) : CoeOut (PolygonCell n) ℂ :=
  ⟨val⟩

@[ext]
private theorem ext {n : ℕ} {x y : PolygonCell n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

noncomputable instance (n : ℕ) : TopologicalSpace (PolygonCell n) :=
  TopologicalSpace.induced val inferInstance

/-- The unit circle included in a polygonal cell. -/
def ofCircle (n : ℕ) : C(Circle, PolygonCell n) where
  toFun z := ⟨z, by
    rw [Metric.mem_closedBall]
    exact z.property.le⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

/-- The angle swept out by side `i` at parameter `t`. -/
noncomputable def sideAngle {n : ℕ} (i : Fin n) (t : unitInterval) : ℝ :=
  2 * Real.pi * ((i.val : ℝ) + t) / n

private theorem continuous_sideAngle {n : ℕ} (i : Fin n) : Continuous (sideAngle i) := by
  unfold sideAngle
  fun_prop

/-- Side `i` of an `n`-sided cell, parameterized in boundary order. -/
noncomputable def side {n : ℕ} (i : Fin n) : C(unitInterval, PolygonCell n) where
  toFun t := ofCircle n (Circle.exp (sideAngle i t))
  continuous_toFun :=
    (ofCircle n).continuous.comp (Circle.exp.continuous.comp (continuous_sideAngle i))

/-- Consecutive sides meet at their common cyclic endpoint. -/
private theorem side_one_eq_rotate_zero {n : ℕ} (i : Fin n) :
    side i 1 = side (finRotate n i) 0 := by
  apply PolygonCell.ext
  change (Circle.exp (sideAngle i 1) : ℂ) =
    (Circle.exp (sideAngle (finRotate n i) 0) : ℂ)
  apply congr_arg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt i.pos)
  by_cases hi : i = Fin.last n
  · subst i
    refine ⟨1, ?_⟩
    rw [finRotate_last]
    simp [sideAngle]
    field_simp
  · refine ⟨0, ?_⟩
    simp only [sideAngle, Nat.succ_eq_add_one, finRotate_apply, Int.cast_zero, zero_mul,
      add_zero]
    rw [Fin.val_add_one_of_lt (Fin.val_lt_last hi)]
    push_cast
    rw [add_zero]


end PolygonCell

namespace PolygonGluing

universe u

/-- The disjoint union of a family of polygonal cells. -/
abbrev PreRealization (Face : Type u) (sideCount : Face → ℕ) : Type u :=
  Σ f, PolygonCell (sideCount f)

/-- A labelled side in a family of polygonal cells. -/
structure Side (Face : Type u) (sideCount : Face → ℕ) where
  /-- The `face` declaration. -/
  face : Face
  /-- The `index` declaration. -/
  index : Fin (sideCount face)

namespace Side

/-- A point on a labelled side, included in the disjoint union. -/
noncomputable def point {Face : Type u} {sideCount : Face → ℕ}
    (s : Side Face sideCount) (t : unitInterval) : PreRealization Face sideCount :=
  ⟨s.face, PolygonCell.side s.index t⟩

end Side

/-- The two affine self-homeomorphisms of the unit interval used to glue polygon sides. -/
inductive ParameterDirection where
  | same
  | opposite
deriving DecidableEq, Repr

namespace ParameterDirection
def homeomorph : ParameterDirection → (unitInterval ≃ₜ unitInterval)
  | same => Homeomorph.refl unitInterval
  | opposite => unitInterval.symmHomeomorph

end ParameterDirection

/-- Instructions for identifying two polygon sides with an affine parameter map. -/
structure Identification (Face : Type u) (sideCount : Face → ℕ) where
  /-- The `source` declaration. -/
  source : Side Face sideCount
  /-- The `target` declaration. -/
  target : Side Face sideCount
  /-- The `direction` declaration. -/
  direction : ParameterDirection

namespace Identification

/-- The affine parameter homeomorphism of a side identification. -/
def parameter {Face : Type u} {sideCount : Face → ℕ}
    (identification : Identification Face sideCount) : unitInterval ≃ₜ unitInterval :=
  identification.direction.homeomorph

end Identification

/-- The elementary point identifications prescribed by a collection of side gluings. -/
inductive Generator {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    PreRealization Face sideCount → PreRealization Face sideCount → Prop
  | glue (identification : Identification Face sideCount)
      (h : identification ∈ identifications) (t : unitInterval) :
      Generator identifications (identification.source.point t)
        (identification.target.point (identification.parameter t))

/-- The equivalence relation generated by the prescribed side identifications. -/
def setoid {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    Setoid (PreRealization Face sideCount) :=
  Relation.EqvGen.setoid (Generator identifications)

end PolygonGluing
end LeanEval.Topology.ClassificationOfSurfaces

set_option autoImplicit false
noncomputable section
open scoped Topology
open LeanEval.Topology.ClassificationOfSurfaces
namespace D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains

private theorem side_angle_equation {n : ℕ} (i j : Fin n) (t : unitInterval)
    (h : PolygonCell.side i t = PolygonCell.side j 0) :
    ∃ m : ℤ, (i.val : ℝ) + t = j.val + (m : ℝ) * n := by
  have hv := congrArg PolygonCell.val h
  change (Circle.exp (PolygonCell.sideAngle i t) : ℂ) =
    (Circle.exp (PolygonCell.sideAngle j 0) : ℂ) at hv
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Subtype.ext hv)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt i.pos)
  refine ⟨m, ?_⟩
  apply mul_left_cancel₀ (ne_of_gt Real.two_pi_pos)
  calc
    2 * Real.pi * ((i.val : ℝ) + t) = PolygonCell.sideAngle i t * n := by
      simp [PolygonCell.sideAngle, hn]
    _ = (PolygonCell.sideAngle j 0 + (m : ℝ) * (2 * Real.pi)) * n := by rw [hm]
    _ = 2 * Real.pi * ((j.val : ℝ) + (m : ℝ) * n) := by
      dsimp [PolygonCell.sideAngle]
      field_simp
      ring

private theorem side_parameter_endpoint {n : ℕ} (i j : Fin n) (t : unitInterval)
    (h : PolygonCell.side i t = PolygonCell.side j 0) : t = 0 ∨ t = 1 := by
  obtain ⟨m, hm⟩ := side_angle_equation i j t h
  let z : ℤ := (j.val : ℤ) + m * n - i.val
  have hz : (t : ℝ) = (z : ℝ) := by
    dsimp [z]
    push_cast
    linarith
  have h0 := t.property.1
  have h1 := t.property.2
  rw [hz] at h0 h1
  have h0' : (0 : ℤ) ≤ z := by exact_mod_cast h0
  have h1' : z ≤ (1 : ℤ) := by exact_mod_cast h1
  have he : z = 0 ∨ z = 1 := by omega
  rcases he with he | he
  · left; apply Subtype.ext; simpa [he] using hz
  · right; apply Subtype.ext; simpa [he] using hz

private theorem side_zero_injective {n : ℕ} :
    Function.Injective (fun i : Fin n => PolygonCell.side i 0) := by
  intro i j h
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have range (k : Fin n) : PolygonCell.sideAngle k 0 ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    simp only [PolygonCell.sideAngle, show ((0 : unitInterval) : ℝ) = 0 from rfl, add_zero]
    refine ⟨div_nonneg (mul_nonneg Real.two_pi_pos.le (Nat.cast_nonneg _)) hn.le, ?_⟩
    apply (div_lt_iff₀ hn).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast k.isLt) Real.two_pi_pos
  have hv := congrArg PolygonCell.val h
  change (Circle.exp (PolygonCell.sideAngle i 0) : ℂ) =
    (Circle.exp (PolygonCell.sideAngle j 0) : ℂ) at hv
  have he := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
    (by simp) (range i) (range j) (Subtype.ext hv)
  have hs := congrArg (fun z : ℝ => z * n) he
  have hc : 2 * Real.pi * (i.val : ℝ) = 2 * Real.pi * (j.val : ℝ) := by
    simpa [PolygonCell.sideAngle, ne_of_gt hn] using hs
  apply Fin.ext
  exact_mod_cast (mul_left_cancel₀ (ne_of_gt Real.two_pi_pos) hc)

universe u
variable {Face : Type u} {count : Face → ℕ}

def vertex (s : PolygonGluing.Side Face count) :
    PolygonGluing.PreRealization Face count := s.point 0

def endSide (s : PolygonGluing.Side Face count) (b : Bool) :
    PolygonGluing.Side Face count :=
  if b then ⟨s.face, finRotate (count s.face) s.index⟩ else s

def endParam (b : Bool) : unitInterval := if b then 1 else 0

private theorem vertex_endSide (s : PolygonGluing.Side Face count) (b : Bool) :
    vertex (endSide s b) = s.point (endParam b) := by
  cases b
  · rfl
  · exact congrArg
      (fun z : PolygonCell (count s.face) =>
        (⟨s.face,z⟩ : PolygonGluing.PreRealization Face count))
      (PolygonCell.side_one_eq_rotate_zero s.index).symm

private theorem vertex_injective :
    Function.Injective (vertex (Face := Face) (count := count)) := by
  rintro ⟨f,i⟩ ⟨g,j⟩ h
  have hf : f = g := congrArg Sigma.fst h
  subst g
  have hv := congrArg (fun x : PolygonGluing.PreRealization Face count => x.2.val) h
  have hi := side_zero_injective (PolygonCell.ext hv)
  cases hi
  rfl

private theorem point_parameter_endpoint (s w : PolygonGluing.Side Face count)
    (t : unitInterval) (h : s.point t = vertex w) : t = 0 ∨ t = 1 := by
  rcases s with ⟨f,i⟩
  rcases w with ⟨g,j⟩
  have hf : f = g := congrArg Sigma.fst h
  subst g
  have hv := congrArg (fun x : PolygonGluing.PreRealization Face count => x.2.val) h
  exact side_parameter_endpoint i j t (PolygonCell.ext hv)

def endDirection (d : PolygonGluing.ParameterDirection) (b : Bool) : Bool :=
  match d with
  | .same => b
  | .opposite => !b

private theorem parameter_end (a : PolygonGluing.Identification Face count) (b : Bool) :
    a.parameter (endParam b) = endParam (endDirection a.direction b) := by
  cases h : a.direction <;> cases b <;>
    simp [PolygonGluing.Identification.parameter, PolygonGluing.ParameterDirection.homeomorph,
      h, endParam, endDirection]

/-- Endpoint instructions retain the actual side occurrences and their cyclic successors. -/
inductive EndpointStep (I : Set (PolygonGluing.Identification Face count)) :
    PolygonGluing.Side Face count → PolygonGluing.Side Face count → Prop
  | glue (a : PolygonGluing.Identification Face count) (ha : a ∈ I) (b : Bool) :
      EndpointStep I (endSide a.source b)
        (endSide a.target (endDirection a.direction b))

private theorem generator_endpoints (I : Set (PolygonGluing.Identification Face count))
    {x y : PolygonGluing.PreRealization Face count} (h : PolygonGluing.Generator I x y)
    (hmark : (∃ s, x = vertex s) ∨ (∃ s, y = vertex s)) :
    ∃ s t, x = vertex s ∧ y = vertex t ∧ EndpointStep I s t := by
  cases h with
  | glue a ha r =>
    have hr : r = 0 ∨ r = 1 := by
      rcases hmark with ⟨s,hs⟩ | ⟨s,hs⟩
      · exact point_parameter_endpoint a.source s r hs
      · have hh := point_parameter_endpoint a.target s (a.parameter r) hs
        cases hd : a.direction with
        | same => simpa [PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph, hd] using hh
        | opposite =>
          simp only [PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph, hd] at hh
          change unitInterval.symm r = 0 ∨ unitInterval.symm r = 1 at hh
          rcases hh with hh | hh
          · right
            have h' := congrArg unitInterval.symm hh
            simpa using h'
          · left
            have h' := congrArg unitInterval.symm hh
            simpa using h'
    rcases hr with rfl | rfl
    · refine ⟨endSide a.source false, endSide a.target (endDirection a.direction false),
        (vertex_endSide a.source false).symm, ?_, EndpointStep.glue a ha false⟩
      rw [vertex_endSide, ← parameter_end]
      rfl
    · refine ⟨endSide a.source true, endSide a.target (endDirection a.direction true),
        (vertex_endSide a.source true).symm, ?_, EndpointStep.glue a ha true⟩
      rw [vertex_endSide, ← parameter_end]
      rfl

private theorem marked_saturated (I : Set (PolygonGluing.Identification Face count))
    {x y : PolygonGluing.PreRealization Face count} (h : PolygonGluing.setoid I x y) :
    (∃ s, x = vertex s) ↔ (∃ s, y = vertex s) := by
  induction h with
  | rel x y h =>
    constructor
    · intro hx
      obtain ⟨_,t,_,ht,_⟩ := generator_endpoints I h (Or.inl hx)
      exact ⟨t,ht⟩
    · intro hy
      obtain ⟨s,_,hs,_,_⟩ := generator_endpoints I h (Or.inr hy)
      exact ⟨s,hs⟩
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Complete polygon point chains between marked vertices are exactly endpoint chains.
This uses the circular cells, all side parameters and the full generated point relation. -/
theorem polygon_marked_endpoint_chains
    (I : Set (PolygonGluing.Identification Face count)) :
    (∀ x y : PolygonGluing.PreRealization Face count, PolygonGluing.setoid I x y →
      ((∃ s : PolygonGluing.Side Face count, x = s.point 0) ↔
        (∃ s : PolygonGluing.Side Face count, y = s.point 0))) ∧
    (∀ s t : PolygonGluing.Side Face count,
      PolygonGluing.setoid I (s.point 0) (t.point 0) ↔
        Relation.EqvGen (EndpointStep I) s t) := by
  refine ⟨fun _ _ h => marked_saturated I h, ?_⟩
  intro s t
  constructor
  · intro h
    have lift : ∀ {x y : PolygonGluing.PreRealization Face count},
        PolygonGluing.setoid I x y → ∀ (s t : PolygonGluing.Side Face count),
        x = vertex s → y = vertex t → Relation.EqvGen (EndpointStep I) s t := by
      intro x y h
      induction h with
      | rel x y h =>
        intro s t hs ht
        obtain ⟨s',t',hs',ht',hh⟩ := generator_endpoints I h (Or.inl ⟨s,hs⟩)
        have hss : s = s' := vertex_injective (hs.symm.trans hs')
        have htt : t = t' := vertex_injective (ht.symm.trans ht')
        subst s'; subst t'
        exact Relation.EqvGen.rel _ _ hh
      | refl x =>
        intro s t hs ht
        have hst : s = t := vertex_injective (hs.symm.trans ht)
        subst t
        exact Relation.EqvGen.refl _
      | symm x y _ ih => exact fun s t hs ht => (ih t s ht hs).symm
      | trans x y z hxy _ ih₁ ih₂ =>
        intro s t hs ht
        obtain ⟨w,hw⟩ := (marked_saturated I hxy).mp ⟨s,hs⟩
        exact (ih₁ s w hs hw).trans _ _ _ (ih₂ w t hw ht)
    exact lift h s t rfl rfl
  · intro h
    induction h with
    | rel s t h =>
      cases h with
      | glue a ha b =>
        change PolygonGluing.setoid I (vertex (endSide a.source b))
          (vertex (endSide a.target (endDirection a.direction b)))
        rw [vertex_endSide, vertex_endSide, ← parameter_end]
        exact Relation.EqvGen.rel _ _ (PolygonGluing.Generator.glue a ha (endParam b))
    | refl s => exact Relation.EqvGen.refl _
    | symm s t _ ih => exact ih.symm
    | trans s t r _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

end D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains
