/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldModularCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldModularCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genus-one modular covariance of the actual Leech holonomy traces. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldMoonshineCharacter

/-! The four actual torus traces of the Leech lattice involution transform under
right multiplication of the spatial and temporal holonomies. The doubly
twisted entry uses the negative of the oscillator-parity insertion. -/

set_option autoImplicit false

noncomputable section

open Matrix ModularForm UpperHalfPlane
open scoped Matrix MatrixGroups ModularForm

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldModularCovariance

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit leechPosDef)
open ActualLeechOrbifoldTraceSeries (character ordinaryCharacter ordinary_trace_series)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeThetaCharacter (positiveFullThetaCharacter)
open LatticeHalfFockCharacter (actualInsertedCharacter)
open LatticeHalfFockParityT (actualParityInsertedCharacter)
open Lattice.ActualLeechTheta (latticeTheta_leech_eq_E4_cube_sub_discriminant)
open LeechTwiningTraceModularity
  (actual_theta_eq_B actual_twisted_eq_U actual_parity_eq_P B_S U_S P_S B_T U_T P_T)

local notation "Δ" => ModularForm.discriminant
local notation "S" => ModularGroup.S
local notation "T" => ModularGroup.T
local notation "thetaTrace" => positiveFullThetaCharacter leechData (actualInverse leechData)
  (actualInverse_left leechData leechUnit) (actualInverse_right leechData leechUnit) leechPosDef
local notation "twistedTrace" => actualInsertedCharacter leechData leechUnit LinearMap.id
local notation "parityTrace" => actualParityInsertedCharacter leechData leechUnit LinearMap.id

/-- The spatial and temporal holonomies of the lattice involution. -/
abbrev Holonomy := ZMod 2 × ZMod 2

/-- Entrywise reduction of the integral modular group modulo two. -/
def reduceModTwo : SL(2, ℤ) →* SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

/-- Right multiplication of the holonomies, regarded as a row vector. -/
def holonomyRight (p : Holonomy) (a : SL(2, ZMod 2)) : Holonomy :=
  let row := ![p.1, p.2] ᵥ* (a : Matrix (Fin 2) (Fin 2) (ZMod 2))
  (row 0, row 1)

@[simp] theorem holonomyRight_one (p : Holonomy) : holonomyRight p 1 = p := by
  simp [holonomyRight]

theorem holonomyRight_mul (p : Holonomy) (a b : SL(2, ZMod 2)) :
    holonomyRight p (a * b) = holonomyRight (holonomyRight p a) b := by
  have row_eta (v : Fin 2 → ZMod 2) : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> rfl
  simp only [holonomyRight, row_eta, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul]

@[simp] theorem holonomyRight_S (p : Holonomy) :
    holonomyRight p (reduceModTwo S) = (p.2, p.1) := by
  have hneg : (-1 : ZMod 2) = 1 := ZMod.neg_eq_self_mod_two 1
  simp [holonomyRight, reduceModTwo, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hneg]

@[simp] theorem holonomyRight_T (p : Holonomy) :
    holonomyRight p (reduceModTwo T) = (p.1, p.1 + p.2) := by
  simp [holonomyRight, reduceModTwo, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The actual holonomy traces, with the physical twisted-sector insertion. -/
def holonomyTrace (p : Holonomy) (τ : ℍ) : ℂ :=
  if p.1 = 0 then
    if p.2 = 0 then ordinaryCharacter τ else thetaTrace τ
  else
    if p.2 = 0 then twistedTrace τ else -parityTrace τ

@[simp] theorem holonomyTrace_zero_zero (τ : ℍ) :
    holonomyTrace (0, 0) τ = ordinaryCharacter τ := by simp [holonomyTrace]

@[simp] theorem holonomyTrace_zero_one (τ : ℍ) :
    holonomyTrace (0, 1) τ = thetaTrace τ := by simp [holonomyTrace]

@[simp] theorem holonomyTrace_one_zero (τ : ℍ) :
    holonomyTrace (1, 0) τ = twistedTrace τ := by simp [holonomyTrace]

@[simp] theorem holonomyTrace_one_one (τ : ℍ) :
    holonomyTrace (1, 1) τ = -parityTrace τ := by simp [holonomyTrace]

private theorem ordinary_eq_E4_cube_div_discriminant (τ : ℍ) :
    ordinaryCharacter τ = E₄ τ ^ (3 : ℕ) / Δ τ - 720 := by
  rw [(ordinary_trace_series τ).2, latticeTheta_leech_eq_E4_cube_sub_discriminant]
  change (E₄ τ ^ (3 : ℕ) - 720 * Δ τ) / Δ τ = _
  rw [sub_div, mul_div_cancel_right₀ _ (discriminant_ne_zero τ)]

/-- The actual untwisted identity trace is invariant under the full modular group. -/
theorem ordinaryCharacter_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ordinaryCharacter (γ • τ) = ordinaryCharacter τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  change E₄ (γ • τ) = _ at hE
  change Δ (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ at hΔ
  rw [ordinary_eq_E4_cube_div_discriminant, ordinary_eq_E4_cube_div_discriminant, hE, hΔ]
  simp only [zpow_ofNat, mul_pow, ← pow_mul]
  rw [show (4 * 3 : ℕ) = 12 by rfl, mul_div_mul_left _ _
    (pow_ne_zero 12 (denom_ne_zero (γ : GL (Fin 2) ℝ) τ))]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a

theorem holonomyTrace_S (p : Holonomy) (τ : ℍ) :
    holonomyTrace p (S • τ) = holonomyTrace (p.2, p.1) τ := by
  obtain ⟨g, h⟩ := p
  rcases zmod_two_cases g with rfl | rfl <;> rcases zmod_two_cases h with rfl | rfl <;>
    simp only [holonomyTrace_zero_zero, holonomyTrace_zero_one, holonomyTrace_one_zero,
      holonomyTrace_one_one, ordinaryCharacter_smul, actual_theta_eq_B, actual_twisted_eq_U,
      actual_parity_eq_P, B_S, U_S, P_S]

theorem holonomyTrace_T (p : Holonomy) (τ : ℍ) :
    holonomyTrace p (T • τ) = holonomyTrace (p.1, p.1 + p.2) τ := by
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  obtain ⟨g, h⟩ := p
  rcases zmod_two_cases g with rfl | rfl <;> rcases zmod_two_cases h with rfl | rfl <;>
    simp only [zero_add, add_zero, hone, holonomyTrace_zero_zero, holonomyTrace_zero_one,
      holonomyTrace_one_zero, holonomyTrace_one_one, ordinaryCharacter_smul, actual_theta_eq_B,
      actual_twisted_eq_U, actual_parity_eq_P, B_T, U_T, P_T, neg_neg]

/-- Simultaneous covariance of the actual trace array, via the right action of
`SL(2, ZMod 2)` on the holonomies. -/
theorem holonomyTrace_smul (γ : SL(2, ℤ)) (p : Holonomy) (τ : ℍ) :
    holonomyTrace p (γ • τ) = holonomyTrace (holonomyRight p (reduceModTwo γ)) τ := by
  have hγ : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  revert p τ
  induction hγ using Subgroup.closure_induction with
  | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · simpa only [holonomyRight_S] using holonomyTrace_S
      · simpa only [holonomyRight_T] using holonomyTrace_T
  | one => simp
  | mul a b _ _ ha hb =>
      intro p τ
      rw [mul_smul, ha, hb, map_mul, holonomyRight_mul]
  | inv a _ ha =>
      intro p τ
      have h := ha (holonomyRight p (reduceModTwo a⁻¹)) (a⁻¹ • τ)
      rw [smul_inv_smul, ← holonomyRight_mul, ← map_mul, inv_mul_cancel, map_one,
        holonomyRight_one] at h
      exact h.symm

/-- Integral matrices with the same reduction produce identical transformed trace arrays. -/
theorem holonomyTrace_smul_eq_of_reduceModTwo_eq {γ δ : SL(2, ℤ)}
    (h : reduceModTwo γ = reduceModTwo δ) (p : Holonomy) (τ : ℍ) :
    holonomyTrace p (γ • τ) = holonomyTrace p (δ • τ) := by
  rw [holonomyTrace_smul γ, holonomyTrace_smul δ, h]

/-- The actual oscillator-parity insertion is nonzero everywhere on the upper half-plane. -/
theorem parityTrace_ne_zero (τ : ℍ) : parityTrace τ ≠ 0 := by
  rw [actual_parity_eq_P, LeechTwiningTraceModularity.P, neg_ne_zero]
  exact mul_ne_zero (by norm_num) (div_ne_zero (discriminant_ne_zero τ)
    (discriminant_ne_zero (LeechTwiningTraceModularity.halfShift τ)))

/-- The `(1, 0)` to `(1, 1)` covariance equation for `T` fixes the parity
coefficient even at a single point of the upper half-plane. -/
theorem twisted_T_coefficient_iff (τ : ℍ) (c : ℂ) :
    twistedTrace (T • τ : ℍ) = c * parityTrace τ ↔ c = -1 := by
  rw [actual_twisted_eq_U, U_T, ← actual_parity_eq_P, ← neg_one_mul]
  constructor
  · intro h
    exact (mul_right_cancel₀ (parityTrace_ne_zero τ) h).symm
  · rintro rfl
    rfl

/-- The orbifold average of the actual holonomy traces is the assembled character. -/
theorem holonomyTrace_average (τ : ℍ) :
    (∑ p : Holonomy, holonomyTrace p τ) / 2 = character τ := by
  have h : (Finset.univ : Finset Holonomy) = {(0, 0), (0, 1), (1, 0), (1, 1)} := by
    decide
  rw [h]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, zero_ne_one, one_ne_zero, false_and, and_false, or_false, not_false_eq_true,
    holonomyTrace_zero_zero, holonomyTrace_zero_one, holonomyTrace_one_zero,
    holonomyTrace_one_one]
  rw [ActualLeechOrbifoldMoonshineCharacter.character_eq_j_sub_744]
  simpa only [sub_eq_add_neg, add_assoc] using
    ActualLeechOrbifoldMoonshineCharacter.four_traces_eq_j_sub_744 τ

end D5.S3.VertexAlgebra.ActualLeechOrbifoldModularCovariance
