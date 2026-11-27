/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original Leech extension vertex algebra and its central-charge-24 stress action. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVertexAlgebra
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldMMV
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMatter
import Batteries.Tactic.OpenPrivate

/-! The literal Leech state-field vertex algebra uses the native stress coefficients
on the fixed and negative twisted sectors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private stress stress_fixed_mode stress_twisted_mode from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation

/-- The fixed Leech states and original negative twisted states, with their literal field. -/
def leechVertexAlgebra : StateFieldVertexAlgebra Orbifold :=
  OriginalOrbifoldVertexAlgebra.actualVertexAlgebra (hu := leechUnit) leechPosDef leech_spec.1
    (OriginalOrbifoldJacobi.defect_mmv (hu := leechUnit) leechPosDef leech_spec.1)

@[simp] theorem stateField_eq :
    leechVertexAlgebra.stateField = OriginalOrbifoldField.Y leechData leechUnit leechPosDef := rfl

/-- The already constructed theta-fixed conformal state in the fixed summand. -/
abbrev conformalVector : Orbifold := ActualLeechOrbifoldMatter.omega

/-- The Virasoro action with charge 24, from the modes of the conformal vector. -/
abbrev virasoroMatter : VirasoroBRST.MatterDatum Orbifold :=
  ActualLeechOrbifoldMatter.matter

theorem central_charge : virasoroMatter.centralCharge = 24 := rfl

theorem virasoro_mode_eq (n : ℤ) :
    virasoroMatter.mode n = (leechVertexAlgebra.stateField conformalVector)[[n+1]] := rfl

/-- The conformal vector's zero field mode is the actual translation on both sectors. -/
theorem virasoro_minus_one : virasoroMatter.mode (-1) = leechVertexAlgebra.translation := by
  rw [virasoro_mode_eq, show (-1 : ℤ) + 1 = 0 by norm_num, stateField_eq]
  apply LinearMap.ext
  intro x
  change ((OriginalOrbifoldField.Y leechData leechUnit leechPosDef
    (stress leechData, 0))[[0]]) x = OriginalOrbifoldTranslation.T leechData leechUnit x
  rw [OriginalOrbifoldField.Y_fixed_ncoeff_apply, OriginalOrbifoldTranslation.T_apply,
    stress_fixed_mode leechData leechUnit, stress_twisted_mode leechData leechUnit]

theorem stress_from_vacuum :
    virasoroMatter.mode (-2) leechVertexAlgebra.vacuum = conformalVector := by
  rw [virasoro_mode_eq, show (-2 : ℤ) + 1 = -1 by norm_num]
  exact leechVertexAlgebra.creation conformalVector

theorem virasoro_vacuum (n : ℤ) (hn : -1 ≤ n) :
    virasoroMatter.mode n leechVertexAlgebra.vacuum = 0 := by
  rw [virasoro_mode_eq]
  exact leechVertexAlgebra.creativity conformalVector (n+1) (by omega)

theorem stress_has_weight_two :
    virasoroMatter.mode 0 conformalVector = (2 : ℂ) • conformalVector := by
  have h := LinearMap.congr_fun (virasoroMatter.virasoro 0 (-2)) leechVertexAlgebra.vacuum
  have h0 := virasoro_vacuum 0 (by norm_num)
  norm_num [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    stress_from_vacuum, h0, map_zero] at h
  exact h

private theorem choose_one_finsum (f : ℕ → Orbifold) :
    (∑ᶠ j : ℕ, integerBinomial 1 j • f j) = f 0 + f 1 := by
  have finite : (∑ᶠ j : ℕ, integerBinomial 1 j • f j) =
      ∑ j ∈ Finset.range 2, integerBinomial 1 j • f j := by
    apply finsum_eq_sum_of_support_subset
    intro j member
    by_contra outside
    have vanish : (1 : ℕ).choose j = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    have choose : Ring.choose (1 : ℤ) j = 0 := by
      change Ring.choose ((1 : ℕ) : ℤ) j = 0
      rw [Ring.choose_natCast, vanish]
      rfl
    exact member (by simp [integerBinomial, choose])
  rw [finite]
  simp [Finset.sum_range_succ, integerBinomial]

/-- The original stress zero mode acts on arbitrary states and fields by conformal weight. -/
theorem energy_covariance (a : Orbifold) (q : ℤ) :
    virasoroMatter.mode 0 * (leechVertexAlgebra.stateField a)[[q]] -
        (leechVertexAlgebra.stateField a)[[q]] * virasoroMatter.mode 0 =
      (leechVertexAlgebra.stateField (virasoroMatter.mode 0 a))[[q]] -
        ((q : ℂ) + 1) • (leechVertexAlgebra.stateField a)[[q]] := by
  apply LinearMap.ext
  intro c
  let Y := leechVertexAlgebra.stateField
  let μ := fun (a : Orbifold) (n : ℤ) (b : Orbifold) => ((Y a)[[n]]) b
  let ω := conformalVector
  have h := (leechVertexAlgebra.borcherds ω a c 1 q 0).2.2.2
  change (∑ᶠ j : ℕ, integerBinomial 1 j • μ (μ ω (0+j) a) (1+q-j) c) =
    (∑ᶠ j : ℕ, ((-1 : ℂ)^j * integerBinomial 0 j) •
      (μ ω (1+0-j) (μ a (q+j) c) - epsilon 0 • μ a (q+0-j) (μ ω (1+j) c))) at h
  have rhs : (∑ᶠ j : ℕ, ((-1 : ℂ)^j * integerBinomial 0 j) •
      (μ ω (1+0-j) (μ a (q+j) c) - epsilon 0 • μ a (q+0-j) (μ ω (1+j) c))) =
      μ ω 1 (μ a q c) - μ a q (μ ω 1 c) := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, epsilon]
    · intro j hj
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  rw [choose_one_finsum, rhs] at h
  simp only [Nat.cast_zero, Nat.cast_one, add_zero, sub_zero, zero_add] at h
  rw [show (1 : ℤ) + q - 1 = q by omega, add_comm (1 : ℤ) q] at h
  have mode_zero : (Y ω)[[0]] = leechVertexAlgebra.translation := by
    simpa only [virasoro_mode_eq, show (-1 : ℤ) + 1 = 0 by norm_num] using virasoro_minus_one
  have mode_one : virasoroMatter.mode 0 = (Y ω)[[1]] := by
    simpa only [zero_add] using virasoro_mode_eq 0
  have derivative : (Y (leechVertexAlgebra.translation a))[[q+1]] =
      -((q+1 : ℤ) : ℂ) • (Y a)[[q]] := by
    dsimp only [Y, leechVertexAlgebra, OriginalOrbifoldVertexAlgebra.actualVertexAlgebra]
    simpa only [add_sub_cancel_right] using
      OriginalOrbifoldTranslation.Y_translation leechData leechUnit leechPosDef
        leech_spec.1 (q+1) a
  dsimp only [μ] at h
  rw [mode_zero, derivative, ← mode_one, LinearMap.smul_apply, Int.cast_add, Int.cast_one,
    neg_smul] at h
  change virasoroMatter.mode 0 (((Y a)[[q]]) c) - ((Y a)[[q]]) (virasoroMatter.mode 0 c) =
    ((Y (virasoroMatter.mode 0 a))[[q]]) c - ((q : ℂ) + 1) • ((Y a)[[q]]) c
  rw [h.symm]
  exact (add_comm _ _).trans (sub_eq_add_neg _ _).symm

/-- An integer mode shifts the stress weight by the source weight minus its index and one. -/
theorem mode_weight (a b : Orbifold) (q : ℤ) (α β : ℂ)
    (ha : virasoroMatter.mode 0 a = α • a) (hb : virasoroMatter.mode 0 b = β • b) :
    virasoroMatter.mode 0 (((leechVertexAlgebra.stateField a)[[q]]) b) =
      (α + β - (q : ℂ) - 1) • (((leechVertexAlgebra.stateField a)[[q]]) b) := by
  have h := LinearMap.congr_fun (energy_covariance a q) b
  simp only [LinearMap.sub_apply, Module.End.mul_apply, ha, hb,
    map_smul, Pi.smul_apply, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  module

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra
