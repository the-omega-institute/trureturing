/- GID: D5/S3/Observer/Bridges/CharacterPreservation
   generality: G
   mirror-B: D5/B/S3/Observer/Bridges/CharacterPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An equivariant linear bridge preserves both reflection characters. -/

import D5.S3.Observer.Bridges.FixedPointSemiconjugacy
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

/-!
# Reflection character preservation

A real-linear bridge intertwining two reflections sends fixed vectors to fixed
vectors and negated vectors to negated vectors. Since the two real characters
are distinct, an image vector carrying both characters must vanish.

Library-search audit:
* Repository searches for character preservation, semiconjugacy, fixed points,
  and eigenspace transport found the fixed-point component
  `FixedPointSemiconjugacy.fixed_point_maps`, which is applied below, but no
  result containing both characters and the two zero-intersection clauses.
* Pinned Mathlib supplies `Function.Semiconj`, linear-map negation, and real
  scalar cancellation, but no end-to-end theorem with this statement.
* A GitHub Lean code search combining `Function.Semiconj` with eigenspaces
  returned no matching declaration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Bridges.CharacterPreservation

open D5.S3.Observer.Bridges.FixedPointSemiconjugacy

/-- A real-linear equivariant bridge preserves the even and odd reflection
characters. Its image from either character sector has zero intersection with
the opposite response sector. -/
theorem character_preservation
    {C Z : Type*} [AddCommGroup C] [Module Real C]
    [AddCommGroup Z] [Module Real Z]
    (configReflection : C →ₗ[Real] C)
    (responseReflection : Z →ₗ[Real] Z)
    (bridge : C →ₗ[Real] Z)
    (equivariant : Function.Semiconj bridge configReflection responseReflection) :
    (forall x : C, configReflection x = x ->
      responseReflection (bridge x) = bridge x) /\
    (forall x : C, configReflection x = -x ->
      responseReflection (bridge x) = -(bridge x)) /\
    (forall x : C, configReflection x = x ->
      responseReflection (bridge x) = -(bridge x) -> bridge x = 0) /\
    (forall x : C, configReflection x = -x ->
      responseReflection (bridge x) = bridge x -> bridge x = 0) := by
  have even_maps : forall x : C, configReflection x = x ->
      responseReflection (bridge x) = bridge x := by
    intro x hEven
    exact fixed_point_maps equivariant hEven
  have odd_maps : forall x : C, configReflection x = -x ->
      responseReflection (bridge x) = -(bridge x) := by
    intro x hOdd
    rw [← equivariant x, hOdd, map_neg]
  refine ⟨even_maps, odd_maps, ?_, ?_⟩
  · intro x hEven hOddResponse
    have hEvenResponse := even_maps x hEven
    have hSelfNeg : bridge x = -(bridge x) := hEvenResponse.symm.trans hOddResponse
    have hDouble : (2 : Real) • bridge x = 0 := by
      calc
        (2 : Real) • bridge x = bridge x + bridge x := two_smul Real (bridge x)
        _ = bridge x + -(bridge x) := congrArg (bridge x + ·) hSelfNeg
        _ = 0 := add_neg_cancel (bridge x)
    exact (smul_eq_zero.mp hDouble).resolve_left (by norm_num)
  · intro x hOdd hEvenResponse
    have hOddResponse := odd_maps x hOdd
    have hSelfNeg : bridge x = -(bridge x) := hEvenResponse.symm.trans hOddResponse
    have hDouble : (2 : Real) • bridge x = 0 := by
      calc
        (2 : Real) • bridge x = bridge x + bridge x := two_smul Real (bridge x)
        _ = bridge x + -(bridge x) := congrArg (bridge x + ·) hSelfNeg
        _ = 0 := add_neg_cancel (bridge x)
    exact (smul_eq_zero.mp hDouble).resolve_left (by norm_num)

#print axioms character_preservation

end D5.S3.Observer.Bridges.CharacterPreservation
