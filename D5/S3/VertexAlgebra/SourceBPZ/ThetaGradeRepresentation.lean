/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaGradeRepresentation
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Character]
   utility: none
   digest: The order-two lattice reflection acts on every finite grade as a genuine representation, exposing theta-intertwiners as representation invariants. -/

import D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeIntertwiner
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeRepresentation

open D5.S3.VertexAlgebra.SourceBPZ
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open ThetaReflectionAction
open ThetaGradeTraceSplit
open ThetaGradeIntertwiner
open Representation

@[simp] theorem gradeTheta_sq (D : LatticeData) (n : ℤ) (x : grade D n) :
    gradeTheta D n (gradeTheta D n x) = x := by
  apply Subtype.ext
  simpa [gradeTheta_val, theta] using theta_involutive D x.1

def gradeThetaRepresentation (D : LatticeData) (n : ℤ) :
    Representation ℂ (Multiplicative ReflectionGroup) (grade D n) where
  toFun g :=
    if Multiplicative.toAdd g = 0 then LinearMap.id else gradeTheta D n
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    have hsum : (1 + 1 : ReflectionGroup) = 0 := by decide
    fin_cases g <;> fin_cases h <;>
      apply LinearMap.ext <;> intro x <;>
        simp [hsum, Module.End.mul_eq_comp, gradeTheta_sq]

private theorem gradeThetaRepresentation_one (D : LatticeData) (n : ℤ) :
    gradeThetaRepresentation D n (Multiplicative.ofAdd (1 : ReflectionGroup)) =
      gradeTheta D n := by
  apply LinearMap.ext
  intro x
  change (if (1 : ReflectionGroup) = 0 then LinearMap.id else gradeTheta D n) x = _
  rw [if_neg (by decide)]

private theorem gradeThetaRepresentation_inv_one (D : LatticeData) (n : ℤ) :
    gradeThetaRepresentation D n ((Multiplicative.ofAdd (1 : ReflectionGroup))⁻¹) =
      gradeTheta D n := by
  apply LinearMap.ext
  intro x
  change (if (-(1 : ReflectionGroup)) = 0 then LinearMap.id else gradeTheta D n) x = _
  rw [if_neg (by decide)]

def thetaHomRepresentation (D : LatticeData) (m n : ℤ) :
    Representation ℂ (Multiplicative ReflectionGroup)
      (grade D m →ₗ[ℂ] grade D n) :=
  Representation.linHom (gradeThetaRepresentation D m) (gradeThetaRepresentation D n)

theorem thetaIntertwiner_eq_invariants (D : LatticeData) (m n : ℤ) :
    thetaIntertwiner D m n = Representation.invariants (thetaHomRepresentation D m n) := by
  ext F
  constructor
  · intro hF
    rw [Representation.mem_invariants]
    have hconj :
        ((gradeTheta D n).comp F).comp (gradeTheta D m) = F := by
      calc
        ((gradeTheta D n).comp F).comp (gradeTheta D m) =
            (F.comp (gradeTheta D m)).comp (gradeTheta D m) := by
              rw [hF]
        _ = F := by
          apply LinearMap.ext
          intro x
          simp [LinearMap.comp_apply, gradeTheta_sq]
    intro g
    fin_cases g
    · simp [thetaHomRepresentation, gradeThetaRepresentation]
    · simpa [thetaHomRepresentation, Representation.linHom,
        gradeThetaRepresentation, LinearMap.comp_apply, LinearMap.comp_assoc] using hconj
  · intro hF
    have hconj := (Representation.mem_invariants (thetaHomRepresentation D m n) F).mp hF
      (Multiplicative.ofAdd (1 : ReflectionGroup))
    have hconj' :
        ((gradeTheta D n).comp F).comp (gradeTheta D m) = F := by
      change
        ((Representation.linHom (gradeThetaRepresentation D m)
          (gradeThetaRepresentation D n))
            (Multiplicative.ofAdd (1 : ReflectionGroup))) F = F at hconj
      rw [Representation.linHom_apply] at hconj
      rw [gradeThetaRepresentation_one D n,
        gradeThetaRepresentation_inv_one D m] at hconj
      simpa [LinearMap.comp_assoc] using hconj
    change (gradeTheta D n).comp F = F.comp (gradeTheta D m)
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun q : grade D m →ₗ[ℂ] grade D n => q (gradeTheta D m x)) hconj'
    simpa [LinearMap.comp_apply, gradeTheta_sq] using hx

theorem thetaHom_character_average_finrank (D : LatticeData) (m n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (Nat.card (Multiplicative ReflectionGroup) : ℂ)⁻¹ *
        ∑ g : Multiplicative ReflectionGroup,
          (thetaHomRepresentation D m n).character g =
      (Module.finrank ℂ (thetaIntertwiner D m n) : ℂ) := by
  letI : FiniteDimensional ℂ (grade D m) := grade_finiteDimensional D hD m
  letI : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  letI : Invertible (Nat.card (Multiplicative ReflectionGroup) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [Representation.card_inv_mul_sum_char_eq_finrank]
  rw [thetaIntertwiner_eq_invariants D m n]

end D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeRepresentation
