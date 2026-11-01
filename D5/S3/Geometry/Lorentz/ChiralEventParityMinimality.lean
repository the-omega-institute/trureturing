/- GID: D5/S3/Geometry/Lorentz/ChiralEventParityMinimality
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/ChiralEventParityMinimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two continuous invariant parity-odd variables vanish on a chiral event. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import D5.S3.Topology.BorsukUlam.PlanarOddMapZero

/-! The preregistered two-variable lower bound for chiral four-particle events. -/

set_option autoImplicit false

open scoped EuclideanSpace

noncomputable section

namespace D5.S3.Geometry.Lorentz.ChiralEventParityMinimality

abbrev fourVector := Fin 4 → ℝ
abbrev event := Fin 4 → fourVector

def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

def rotation : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 0, -1, 0; 0, -1, 0, 0; 0, 0, 0, -1]

def minkowski (x y : fourVector) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

def forwardCone : Set fourVector := {x |
  0 ≤ x 0 ∧ x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 ≤ x 0 ^ 2}

def properOrthochronous : Set (Matrix (Fin 4) (Fin 4) ℝ) := {lam |
  lam.transpose * eta * lam = eta ∧ Matrix.det lam = 1 ∧ 0 < lam 0 0}

def parityVector (x : fourVector) : fourVector := ![x 0, -x 1, -x 2, -x 3]

def parity (x : event) : event := ![parityVector (x 0), parityVector (x 1),
  parityVector (x 2), parityVector (x 3)]

def act (lam : Matrix (Fin 4) (Fin 4) ℝ) (sigma tau : Equiv.Perm (Fin 2))
    (x : event) : event :=
  ![Matrix.mulVec lam (x (Fin.castAdd 2 (sigma 0))),
    Matrix.mulVec lam (x (Fin.castAdd 2 (sigma 1))),
    Matrix.mulVec lam (x (Fin.natAdd 2 (tau 0))),
    Matrix.mulVec lam (x (Fin.natAdd 2 (tau 1)))]

def chiral (x : event) : Prop :=
  ¬ ∃ lam ∈ properOrthochronous, ∃ sigma tau,
      act lam sigma tau x = parity x

def allEvents : Set event := {x | ∀ i, x i ∈ forwardCone}

def collisionEvents : Set event := {x |
  x ∈ allEvents ∧ minkowski (x 0) (x 0) * minkowski (x 1) (x 1) <
    minkowski (x 0) (x 1) ^ 2}

def admissible (om : Set event) (f : event → ℝ) : Prop :=
  ContinuousOn f om ∧
    (∀ x ∈ om, ∀ lam ∈ properOrthochronous, ∀ sigma tau,
      f (act lam sigma tau x) = f x) ∧
    (∀ x ∈ om, f (parity x) = -f x)

def claim : Prop :=
  ∀ om ∈ ({allEvents, collisionEvents} : Set (Set event)), ∀ f₁ f₂,
    admissible om f₁ → admissible om f₂ →
      ∃ x ∈ om, chiral x ∧ f₁ x = 0 ∧ f₂ x = 0

def family (v : EuclideanSpace ℝ (Fin 3)) : event :=
  let s := v 0
  let t := v 1
  let d := v 2
  let aa := Real.sqrt (4 + t)
  let bb := Real.sqrt (4 - t)
  ![![30, 0, 0, 1], ![20, 0, 0, -1],
    ![10 + s, aa, 0, d], ![10 - s, 0, bb, -d]]

private theorem family_mem_all
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere) :
    family v ∈ allEvents := by
  have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  have hsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    simpa [hvnorm, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq v).symm
  have hs : -1 ≤ v 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have hsn : v 0 ≤ 1 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have ht : -1 ≤ v 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  have htn : v 1 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  have h4t : 0 ≤ 4 + v 1 := by linarith
  have h4tn : 0 ≤ 4 - v 1 := by linarith
  have hsa : (Real.sqrt (4 + v 1)) ^ 2 = 4 + v 1 := Real.sq_sqrt h4t
  have hsb : (Real.sqrt (4 - v 1)) ^ 2 = 4 - v 1 := Real.sq_sqrt h4tn
  intro i
  fin_cases i
  · change 0 ≤ (30 : ℝ) ∧ 0 ^ 2 + 0 ^ 2 + 1 ^ 2 ≤ 30 ^ 2
    norm_num
  · change 0 ≤ (20 : ℝ) ∧ 0 ^ 2 + 0 ^ 2 + (-1 : ℝ) ^ 2 ≤ 20 ^ 2
    norm_num
  · constructor
    · change 0 ≤ 10 + v 0
      linarith
    · change (Real.sqrt (4 + v 1)) ^ 2 + 0 ^ 2 + v 2 ^ 2 ≤ (10 + v 0) ^ 2
      rw [hsa]
      nlinarith
  · constructor
    · change 0 ≤ 10 - v 0
      linarith
    · change 0 ^ 2 + (Real.sqrt (4 - v 1)) ^ 2 + (-v 2) ^ 2 ≤ (10 - v 0) ^ 2
      rw [hsb]
      nlinarith

private theorem family_mem_collision
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere) :
    family v ∈ collisionEvents := by
  constructor
  · exact family_mem_all v hv
  · norm_num [family, minkowski]

private theorem family_continuous :
    ContinuousOn family
      D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere := by
  sorry

private theorem family_chiral
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere) :
    chiral (family v) := by
  sorry

private theorem family_neg
    (v : EuclideanSpace ℝ (Fin 3)) :
    family (-v) =
      act rotation 1 (Equiv.swap 0 1)
        (parity (family v)) := by
  funext i
  fin_cases i <;>
    funext j <;>
      fin_cases j <;>
        simp [family, act, parity, parityVector, rotation, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three] <;> ring_nf

private theorem family_admissible_zero
    (om : Set event) (hom : collisionEvents ⊆ om) (f₁ f₂ : event → ℝ)
    (hf₁ : admissible om f₁) (hf₂ : admissible om f₂) :
    ContinuousOn (fun v => (f₁ (family v) : ℂ) + (f₂ (family v) : ℂ) * Complex.I)
      D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere := by
  sorry

private theorem family_admissible_odd
    (om : Set event) (hom : collisionEvents ⊆ om) (f : event → ℝ)
    (hf : admissible om f) :
    ∀ v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere,
      ((f (family (-v)) : ℂ)) = -((f (family v) : ℂ)) := by
  sorry

private theorem route_claim
    (hcollision : ∀ v,
      v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere →
        family v ∈ collisionEvents)
    (hall : ∀ v,
      v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere →
        family v ∈ allEvents)
    (hcont : ContinuousOn family
      D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere)
    (hchir : ∀ v,
      v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere → chiral (family v))
    (hneg : ∀ v, family (-v) =
      act rotation 1 (Equiv.swap 0 1)
        (parity (family v)))
    (hcomplex : ∀ om, collisionEvents ⊆ om → ∀ f₁ f₂,
      admissible om f₁ → admissible om f₂ →
      ContinuousOn (fun v => (f₁ (family v) : ℂ) + (f₂ (family v) : ℂ) * Complex.I)
        D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere)
    (hodd : ∀ om, collisionEvents ⊆ om → ∀ f,
      admissible om f → ∀ v ∈ D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unitSphere,
        ((f (family (-v)) : ℂ)) = -((f (family v) : ℂ))) :
    claim := by
  sorry

theorem result : claim := by
  apply route_claim family_mem_collision family_mem_all family_continuous family_chiral
    family_neg
  · intro om hom f₁ f₂ hf₁ hf₂
    exact family_admissible_zero om hom f₁ f₂ hf₁ hf₂
  · intro om hom f hf v hv
    exact family_admissible_odd om hom f hf v hv

end D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
