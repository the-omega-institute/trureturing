/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedPairingExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedPairingExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared quasiprimary adjoints yield shared adjoints for every actual fixed Leech mode. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldFixedQuasiprimary
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldNegativeTwistedIrreducible
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! Shared adjoint covariance extends along the actual quasiprimary derivative span. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedPairingExtension

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier fixedTranslation)
open LatticePositiveEnergy (grade)
open OriginalOrbifoldFixedQuasiprimary
  (fixedL quasiprimaryDerivatives span_quasiprimary_derivatives)
open OriginalOrbifoldNegativeTwistedIrreducible (NegativeTwisted)
open OriginalOrbifoldSectorModules (fixedParityY)
open scoped VertexOperator

open private twisted_source_derivative from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion

local notation "V" => FixedCarrier leechData
local notation "X" => NegativeTwisted
local notation "T" => fixedTranslation leechData
local notation "hu" => And.left (And.right leech_spec)
local notation "M" => fun (a : V) (n : ℤ) => (fixedParityY leechData hu (-1) a)[[n]]

set_option maxHeartbeats 600000 in
/-- A family of bilinear forms with common adjoints on homogeneous quasiprimary modes
admits one common adjoint action on all fixed modes of the actual negative twisted module. -/
theorem exists_shared_adjoint_of_quasiprimary {ι : Type*} (B : ι → LinearMap.BilinForm ℂ X)
    (hqp : ∀ (d : ℕ) (a : V), a.val ∈ grade leechData d → fixedL 1 a = 0 →
      ∀ n : ℤ, ∃ O : Module.End ℂ X, ∀ J x y, B J (M a n x) y = B J x (O y)) :
    ∃ O : V → ℤ → Module.End ℂ X, ∀ a n J x y, B J (M a n x) y = B J x (O a n y) := by
  have extend (W : Type) [AddCommGroup W] [Module ℂ W]
      (F : ι → LinearMap.BilinForm ℂ W) (mode : ℤ → V →ₗ[ℂ] Module.End ℂ W)
      (hT : ∀ a n x, mode n (T a) x = -(n : ℂ) • mode (n - 1) a x)
      (hprim : ∀ (d : ℕ) (a : V), a.val ∈ grade leechData d → fixedL 1 a = 0 →
        ∀ n : ℤ, ∃ O : Module.End ℂ W, ∀ J x y, F J (mode n a x) y = F J x (O y)) :
      ∃ O : V → ℤ → Module.End ℂ W, ∀ a n J x y, F J (mode n a x) y = F J x (O a n y) := by
    let P (a : V) : Prop :=
      ∀ n : ℤ, ∃ O : Module.End ℂ W, ∀ J x y, F J (mode n a x) y = F J x (O y)
    let S : Submodule ℂ V :=
      { carrier := {a | P a}
        zero_mem' := by
          change P 0
          intro n
          refine ⟨0, ?_⟩
          intro J x y
          simp
        add_mem' := by
          intro a b ha hb
          change P a at ha
          change P b at hb
          change P (a + b)
          intro n
          obtain ⟨Oa, hOa⟩ := ha n
          obtain ⟨Ob, hOb⟩ := hb n
          refine ⟨Oa + Ob, ?_⟩
          intro J x y
          simp only [map_add, LinearMap.add_apply, hOa, hOb]
        smul_mem' := by
          intro c a ha
          change P a at ha
          change P (c • a)
          intro n
          obtain ⟨O, hO⟩ := ha n
          refine ⟨c • O, ?_⟩
          intro J x y
          simp only [map_smul, LinearMap.smul_apply, hO] }
    have translate (a : V) (ha : P a) : P (T a) := by
      intro n
      obtain ⟨O, hO⟩ := ha (n - 1)
      refine ⟨-(n : ℂ) • O, ?_⟩
      intro J x y
      rw [hT a n x]
      simp only [map_smul, LinearMap.smul_apply, hO]
    have translate_pow (b : V) (hb : P b) (j : ℕ) : P ((T ^ j) b) := by
      induction j with
      | zero => simpa only [pow_zero, Module.End.one_apply] using hb
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact translate _ ih
    have span_le : Submodule.span ℂ (⋃ n : ℤ, quasiprimaryDerivatives n) ≤ S := by
      apply Submodule.span_le.mpr
      intro a ha
      obtain ⟨_, hs⟩ := Set.mem_iUnion.mp ha
      obtain ⟨d, j, b, _, hb, hL, rfl⟩ := hs
      exact translate_pow b (hprim d b hb hL) j
    rw [span_quasiprimary_derivatives] at span_le
    have hall (a : V) : P a := span_le (Submodule.mem_top (R := ℂ) (x := a))
    change ∀ (a : V) (n : ℤ), ∃ O : Module.End ℂ W,
      ∀ J x y, F J (mode n a x) y = F J x (O y) at hall
    choose O hO using hall
    exact ⟨O, hO⟩
  let mode (n : ℤ) : V →ₗ[ℂ] Module.End ℂ X :=
    (LinearMap.proj n).comp (VertexOperator.ncoeff.comp (fixedParityY leechData hu (-1)))
  exact extend X B mode (twisted_source_derivative leechData hu (-1)) hqp

#print axioms exists_shared_adjoint_of_quasiprimary

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedPairingExtension
