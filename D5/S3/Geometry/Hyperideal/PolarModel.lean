/- GID: D5/S3/Geometry/Hyperideal/PolarModel
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/PolarModel
   mirror-E: none(waiver:local-lorentz-geometry)
   anchors: []
   utility: none
   digest: Literal Lorentz polar-edge data and the compatible tangent inner-product structure. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Adjugate
import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Module
namespace D5.S3.Geometry.Hyperideal.PolarNormalSector

abbrev Space := ℝ × EuclideanSpace ℝ (Fin 3)

local instance : AddCommGroup Space :=
  (inferInstance : NormedAddCommGroup Space).toAddCommGroup
local instance : Module ℝ Space :=
  (inferInstance : NormedSpace ℝ Space).toModule
local instance : TopologicalSpace Space :=
  (inferInstance : PseudoMetricSpace Space).toUniformSpace.toTopologicalSpace

/-- The ambient form has signature minus, plus, plus, plus. -/
def lorentz : Space →ₗ[ℝ] Space →ₗ[ℝ] ℝ where
  toFun p := {
    toFun := fun u => -p.1 * u.1 + inner ℝ p.2 u.2
    map_add' := by intros; simp [inner_add_right]; ring
    map_smul' := by intros; simp [inner_smul_right]; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro u
    change -(p + q).1 * u.1 + inner ℝ (p + q).2 u.2 = _
    simp [inner_add_left]
    ring
  map_smul' := by
    intro r p
    apply LinearMap.ext
    intro u
    change -(r • p).1 * u.1 + inner ℝ (r • p).2 u.2 = _
    simp [inner_smul_left]
    ring

/-- An algebraic tangent carrier, with no inherited ambient norm. -/
def Tangent (p : Space) := ↥(lorentz p).ker

instance (p : Space) : AddCommGroup (Tangent p) :=
  inferInstanceAs (AddCommGroup ↥(lorentz p).ker)
instance (p : Space) : Module ℝ (Tangent p) :=
  inferInstanceAs (Module ℝ ↥(lorentz p).ker)

/-- The positive Lorentz restriction builds its own compatible norm. -/
def tangentCore (p : Space) (hp : lorentz p p = -1) :
    InnerProductSpace.Core ℝ (Tangent p) := by
  have htime : 0 < p.1 ^ 2 := by
    have hsp := (real_inner_self_nonneg (x := p.2))
    change -p.1 * p.1 + inner ℝ p.2 p.2 = -1 at hp
    nlinarith
  have estimate (u : Tangent p) :
      inner ℝ u.val.2 u.val.2 ≤ p.1 ^ 2 * lorentz u.val u.val := by
    have hu := u.property
    change -p.1 * u.val.1 + inner ℝ p.2 u.val.2 = 0 at hu
    have hcs := real_inner_mul_inner_self_le p.2 u.val.2
    change -p.1 * p.1 + inner ℝ p.2 p.2 = -1 at hp
    change inner ℝ u.val.2 u.val.2 ≤
      p.1 ^ 2 * (-u.val.1 * u.val.1 + inner ℝ u.val.2 u.val.2)
    have heq : inner ℝ p.2 u.val.2 = p.1 * u.val.1 := by linarith
    have hpEq : inner ℝ p.2 p.2 = p.1 ^ 2 - 1 := by nlinarith
    rw [heq, hpEq] at hcs
    nlinarith only [hcs]
  refine {
    inner := fun u v => lorentz u.val v.val
    conj_inner_symm := ?_
    re_inner_nonneg := ?_
    add_left := ?_
    smul_left := ?_
    definite := ?_ }
  · intro u v
    change -v.val.1 * u.val.1 + inner ℝ v.val.2 u.val.2 =
      -u.val.1 * v.val.1 + inner ℝ u.val.2 v.val.2
    rw [real_inner_comm]; ring
  · intro u
    change 0 ≤ lorentz u.val u.val
    exact nonneg_of_mul_nonneg_right
      (((real_inner_self_nonneg (x := u.val.2))).trans (estimate u)) htime
  · intro u v w
    exact LinearMap.map_add₂ lorentz u.val v.val w.val
  · intro u v r
    exact LinearMap.map_smul₂ lorentz r u.val v.val
  · intro u hu
    have hsp : inner ℝ u.val.2 u.val.2 = 0 := by
      have he := estimate u
      rw [hu, mul_zero] at he
      exact le_antisymm he (real_inner_self_nonneg)
    have hz : u.val.2 = 0 := (inner_self_eq_zero.mp hsp)
    have ht : u.val.1 = 0 := by
      have he := u.property
      change -p.1 * u.val.1 + inner ℝ p.2 u.val.2 = 0 at he
      rw [hz, inner_zero_right, add_zero] at he
      have hn : p.1 ≠ 0 := by intro hh; simp [hh] at htime
      exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr hn)
    apply Subtype.ext
    exact Prod.ext ht hz

/-- A basis and its Lorentz-dual basis are algebraic data, without a cell certificate. -/
structure GramFrame where
  lengths : Fin 4 → Fin 4 → ℝ
  vertices : Basis (Fin 4) ℝ Space
  dual : Basis (Fin 4) ℝ Space
  gram : ∀ i j, lorentz (vertices i) (vertices j) =
    if i = j then 1 else -lengths i j
  duality : ∀ i j, lorentz (vertices i) (dual j) = if i = j then 1 else 0
  box : ∀ i j, i ≠ j → 1 < lengths i j ∧ lengths i j ≤ 2

/-- The common time reflection is chosen before imposing the future sheet. -/
def timeOrientation (F : GramFrame) : Space ≃ₗ[ℝ] Space :=
  if 0 ≤ (∑ i, F.vertices i).1 then LinearEquiv.refl ℝ Space
  else {
    toFun := fun p => (-p.1, p.2)
    invFun := fun p => (-p.1, p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp
    map_add' := by
      intro p q
      apply Prod.ext
      · change -(p.1+q.1) = -p.1 + -q.1
        ring
      · rfl
    map_smul' := by intros; simp }

def vertex (F : GramFrame) (i : Fin 4) : Space := timeOrientation F (F.vertices i)
def dualVertex (F : GramFrame) (i : Fin 4) : Space := timeOrientation F (F.dual i)

/-- The polar block is the literal intersection of eight Lorentz halfspaces. -/
def polarSet (F : GramFrame) : Set Space :=
  {p | lorentz p p = -1 ∧ 0 < p.1 ∧
    (∀ i, 0 ≤ lorentz p (dualVertex F i)) ∧
    (∀ i, lorentz p (vertex F i) ≤ 0)}

def edgePoint (F : GramFrame) (e : Equiv.Perm (Fin 4)) (s : ℝ) : Space :=
  (Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))))⁻¹ •
    (Real.cosh (Real.arcosh (F.lengths (e 0) (e 1)) - s) • vertex F (e 0) +
      Real.cosh s • vertex F (e 1))

def edgeVelocity (F : GramFrame) (e : Equiv.Perm (Fin 4)) (s : ℝ) : Space :=
  (Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))))⁻¹ •
    (-Real.sinh (Real.arcosh (F.lengths (e 0) (e 1)) - s) • vertex F (e 0) +
      Real.sinh s • vertex F (e 1))

/-- The zero direction has the constant geodesic. -/
def normalGeodesic (p u : Space) (t : ℝ) : Space :=
  if u = 0 then p else
    Real.cosh (t * Real.sqrt (lorentz u u)) • p +
      (Real.sinh (t * Real.sqrt (lorentz u u)) / Real.sqrt (lorentz u u)) • u

/-- Eventual forward containment is quantified over every small positive time. -/
def forwardNormalSet (F : GramFrame) (e : Equiv.Perm (Fin 4)) (s : ℝ) : Set Space :=
  {u | lorentz (edgePoint F e s) u = 0 ∧
    lorentz (edgeVelocity F e s) u = 0 ∧
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, normalGeodesic (edgePoint F e s) u t ∈ polarSet F}

/-- The normal plane is orthogonal to the literal point and velocity. -/
def normalSpace (F : GramFrame) (e : Equiv.Perm (Fin 4)) (s : ℝ) : Submodule ℝ Space :=
  (lorentz (edgePoint F e s)).ker ⊓ (lorentz (edgeVelocity F e s)).ker

def outwardNormal (F : GramFrame) (i : Fin 4) : Space :=
  -(Real.sqrt (lorentz (dualVertex F i) (dualVertex F i)))⁻¹ • dualVertex F i

def normalCosine (F : GramFrame) (e : Equiv.Perm (Fin 4)) : ℝ :=
  lorentz (outwardNormal F (e 2)) (outwardNormal F (e 3))

def inwardRay (F : GramFrame) (e : Equiv.Perm (Fin 4)) (side : Bool) : Space :=
  let c := normalCosine F e
  let a := if side then e 3 else e 2
  let b := if side then e 2 else e 3
  (Real.sqrt (1 - c ^ 2))⁻¹ •
    (-outwardNormal F b + c • outwardNormal F a)

/-- The angle uses the norm built from the Lorentz restriction. -/
def tangentAngle (p : Space) (hp : lorentz p p = -1) (u v : Tangent p) : ℝ :=
  letI : InnerProductSpace.Core ℝ (Tangent p) := tangentCore p hp
  letI : NormedAddCommGroup (Tangent p) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ (Tangent p) := InnerProductSpace.ofCore (tangentCore p hp).toCore
  InnerProductGeometry.angle u v

/-- The Gram matrix uses the actual Lorentz frame in the chosen edge order. -/
def gramMatrix (F : GramFrame) (e : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => lorentz (vertex F (e i)) (vertex F (e j))

/-- Rows contain time and the three spatial coordinates of the actual frame. -/
def frameMatrix (F : GramFrame) (e : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i => ![(vertex F (e i)).1,(vertex F (e i)).2 0,
    (vertex F (e i)).2 1,(vertex F (e i)).2 2]

end D5.S3.Geometry.Hyperideal.PolarNormalSector
