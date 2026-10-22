/- GID: D5/S3/VertexAlgebra/TwistedGround/BinaryOrbit
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BinaryOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary Weyl actions construct a nonzero projector and a complete character orbit. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.NoncommProd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.BinaryOrbit

open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

noncomputable section

variable {number : ℕ}

theorem half_add_self (half : Half number) : half + half = 0 := by
  ext index
  exact CharTwo.add_self_eq_zero (half index)

theorem half_neg (half : Half number) : -half = half := by
  ext index
  exact CharTwo.neg_eq (half index)

theorem dot_zero_right (half : Half number) : dot half 0 = 0 := by
  simp [dot]

theorem dot_add_left (first second other : Half number) :
    dot (first + second) other = dot first other + dot second other := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right (other first second : Half number) :
    dot other (first + second) = dot other first + dot other second := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem character_sum (charge : Half number) :
    (∑ half : Half number, complexSign (dot half charge)) =
      if charge = 0 then (2 : ℂ) ^ number else 0 := by
  classical
  by_cases zero : charge = 0
  · subst charge
    simp [dot, sign_zero, Half, F₂]
  · rw [if_neg zero]
    obtain ⟨index, different⟩ : ∃ index, charge index ≠ 0 := by
      by_contra absent
      push Not at absent
      exact zero (funext absent)
    have coordinate : charge index = 1 :=
      ((by decide : ∀ value : F₂, value = 0 ∨ value = 1) (charge index)).resolve_left different
    let coordinateHalf : Half number := Pi.single index 1
    have pairing : dot coordinateHalf charge = 1 := by
      dsimp only [coordinateHalf]
      simp [dot, Pi.single_apply, coordinate]
    have reindex := Fintype.sum_equiv (Equiv.addRight coordinateHalf)
      (fun half : Half number => complexSign (dot (half + coordinateHalf) charge))
      (fun half : Half number => complexSign (dot half charge)) (fun _ => rfl)
    simp only [dot_add_left, pairing, complexSign_add, sign_one, mul_neg_one,
      Finset.sum_neg_distrib] at reindex
    have twice : (2 : ℂ) * (∑ half : Half number, complexSign (dot half charge)) = 0 := by
      linear_combination -reindex
    exact (mul_eq_zero.mp twice).resolve_left (by norm_num)

universe groundUniverse

variable {V : Type groundUniverse} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

structure Actions (number : ℕ) (V : Type groundUniverse) [AddCommGroup V] [Module ℂ V] where
  left : Half number → Module.End ℂ V
  right : Half number → Module.End ℂ V
  left_zero : left 0 = 1
  right_zero : right 0 = 1
  left_add : ∀ first second, left (first + second) = left first * left second
  right_add : ∀ first second, right (first + second) = right first * right second
  cross : ∀ leftHalf rightHalf, right rightHalf * left leftHalf =
    complexSign (dot rightHalf leftHalf) • (left leftHalf * right rightHalf)

variable (actions : Actions number V)

def characterProjector (character : Half number) : Module.End ℂ V :=
  ((2 : ℂ) ^ number)⁻¹ •
    ∑ half : Half number, complexSign (dot half character) • actions.right half

def plusProjector : Module.End ℂ V := characterProjector actions 0

theorem right_plus (half : Half number) :
    actions.right half * plusProjector actions = plusProjector actions := by
  classical
  unfold plusProjector characterProjector
  simp only [dot_zero_right, sign_zero, one_smul]
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [← actions.right_add]
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft half)
    (fun other => actions.right (half + other)) actions.right (fun _ => rfl)

theorem plus_trace (dimension : Module.finrank ℂ V = 2 ^ number)
    (vanishing : ∀ half : Half number, half ≠ 0 → LinearMap.trace ℂ V (actions.right half) = 0) :
    LinearMap.trace ℂ V (plusProjector actions) = 1 := by
  classical
  unfold plusProjector characterProjector
  simp only [dot_zero_right, sign_zero, one_smul,
    map_smul, smul_eq_mul, map_sum]
  rw [Finset.sum_eq_single (0 : Half number)]
  · rw [actions.right_zero, LinearMap.trace_one, dimension, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero number (by norm_num : (2 : ℂ) ≠ 0))
  · intro half _ different
    exact vanishing half different
  · simp

theorem plus_nonzero (dimension : Module.finrank ℂ V = 2 ^ number)
    (vanishing : ∀ half : Half number, half ≠ 0 → LinearMap.trace ℂ V (actions.right half) = 0) :
    plusProjector actions ≠ 0 := by
  intro zero
  have contradiction := plus_trace actions dimension vanishing
  rw [zero, map_zero] at contradiction
  exact zero_ne_one contradiction

theorem image_vector_exists (dimension : Module.finrank ℂ V = 2 ^ number)
    (vanishing : ∀ half : Half number, half ≠ 0 → LinearMap.trace ℂ V (actions.right half) = 0) :
    ∃ state : V, plusProjector actions state ≠ 0 := by
  by_contra absent
  push Not at absent
  apply plus_nonzero actions dimension vanishing
  ext state
  exact absent state

variable (state : V)

def orbit (half : Half number) : V := actions.left half (plusProjector actions state)

theorem orbit_character (half character : Half number) :
    actions.right character (orbit actions state half) =
      complexSign (dot character half) • orbit actions state half := by
  change (actions.right character * actions.left half) (plusProjector actions state) = _
  rw [actions.cross, LinearMap.smul_apply, Module.End.mul_apply]
  have fixed := congrArg (fun operator : Module.End ℂ V => operator state)
    (right_plus actions character)
  change actions.right character (plusProjector actions state) = plusProjector actions state at fixed
  rw [fixed]
  rfl

theorem character_projector_orbit (character half : Half number) :
    characterProjector actions character (orbit actions state half) =
      if character = half then orbit actions state half else 0 := by
  classical
  unfold characterProjector
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, orbit_character, smul_smul,
    ← complexSign_add, ← dot_add_right]
  rw [← Finset.sum_smul, character_sum]
  by_cases same : character = half
  · subst half
    simp [half_add_self, inv_mul_cancel₀ (pow_ne_zero number (by norm_num) :
      (2 : ℂ) ^ number ≠ 0), smul_smul]
  · have nonzero : character + half ≠ 0 := by
      intro zero
      apply same
      have := eq_neg_of_add_eq_zero_left zero
      simpa only [half_neg] using this
    simp [nonzero, same]

theorem orbit_nonzero (image_nonzero : plusProjector actions state ≠ 0) (half : Half number) :
    orbit actions state half ≠ 0 := by
  intro zero
  have undo := congrArg (actions.left half) zero
  rw [map_zero] at undo
  change (actions.left half * actions.left half) (plusProjector actions state) = 0 at undo
  rw [← actions.left_add, half_add_self, actions.left_zero] at undo
  exact image_nonzero undo

theorem orbit_independent (image_nonzero : plusProjector actions state ≠ 0) :
    LinearIndependent ℂ (orbit actions state) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients vanishes half
  have isolated := congrArg (characterProjector actions half) vanishes
  simp only [map_sum, map_smul, character_projector_orbit, map_zero] at isolated
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at isolated
  exact (smul_eq_zero.mp isolated).resolve_right (orbit_nonzero actions state image_nonzero half)

def orbitBasis (dimension : Module.finrank ℂ V = 2 ^ number)
    (image_nonzero : plusProjector actions state ≠ 0) : Module.Basis (Half number) ℂ V :=
  basisOfLinearIndependentOfCardEqFinrank (orbit_independent actions state image_nonzero)
    (by simp [Half, F₂, dimension])

theorem orbit_basis_apply (dimension : Module.finrank ℂ V = 2 ^ number)
    (image_nonzero : plusProjector actions state ≠ 0) (half : Half number) :
    orbitBasis actions state dimension image_nonzero half = orbit actions state half := by
  simp [orbitBasis]

theorem orbit_spans (dimension : Module.finrank ℂ V = 2 ^ number)
    (image_nonzero : plusProjector actions state ≠ 0) :
    Submodule.span ℂ (Set.range (orbit actions state)) = ⊤ := by
  have families : (fun half => orbitBasis actions state dimension image_nonzero half) =
      orbit actions state := funext (orbit_basis_apply actions state dimension image_nonzero)
  rw [← families]
  exact (orbitBasis actions state dimension image_nonzero).span_eq

end

end D5.S3.VertexAlgebra.TwistedGround.BinaryOrbit
