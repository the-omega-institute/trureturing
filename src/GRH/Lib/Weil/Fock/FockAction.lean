import GRH.Lib.General.Measure.HaarModulus
import GRH.Lib.Weil.Construction.OrthogonalSum
import GRH.Lib.Weil.Fock.FockVacuum
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair).

This file: Cocycle identity for U(p,q): oscillator representation splits, by a complex Gaussian
determinant. -/

open Complex ComplexOrder Matrix U

attribute [local simp] fromBlocks_add fromBlocks_smul mul_assoc realHeis realVac realMultiplier

variable {ι : Type*} [Fintype ι]

/-- For a bijection e: ι₁ ⊔ ι₂ → ι compatible with signs, the isomorphism ℂ^ι₁ × ℂ^ι₂ ≅ ℂ^ι
under which β of ε is the product of those of ε₁, ε₂. -/
noncomputable def realCoordSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {ε ε₁ ε₂} {e :
  ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) : (realHeis ε).OrthogonalSum (realHeis ε₁) (realHeis ε₂)
  realVac := by use { (.funCongrLeft ℂ ℂ e ≪≫ₗ
  .sumArrowLequivProdArrow ..).symm.toContinuousLinearEquiv with toFun x := (x.1 ⊕ᵥ x.2) ∘
  e.symm } <;> simp_all [← exp_add, ← e.sum_comp, funext_iff, dotProduct, signMatrix] <;> grind

@[simp] lemma unitary_smul_eq_mulVec {ε} (g : USign ε) (x : ι → ℂ) : g • x = g.1.1 *ᵥ x := rfl

/-- The linear action of U(ε) on ℂ^ι, preserving β and the measure, with multiplier Δ(g) =
conj(det d), d the negative–negative block of g, and trivial cocycle for the Gaussian. -/
noncomputable def realAction ε : (realHeis ε).MultiplierAction (realMeasure ι) realVac (USign ε) :=
  ⟨by simp [↓form_mulVec_mulVec], (⟨by fun_prop, by simp [map_mulVec_haar ·.1.det_ne_zero]⟩),
  realMultiplier, by fun_prop [realMultiplier], by simp, by simp [↓principalMinor_coe_inv],
  fun g h ↦ by
  set k := g * h; let T x := posProj ε + (1 - posProj ε) * x; let J := h.1.1.fromBlocks 0 0 k.1.1
  have := (integral_gauss (A :=
    ofReal 2⁻¹ • (Jᴴ * J + fromBlocks 1 (1 + signMatrix ε) (1 - signMatrix ε) 1)) ?P 0).symm
  rw [(realCoordSum (e := .refl _) (ε ⊕ᵥ ε).comp_id).integral_eq_integral_prod,
    ← mul_eq_one_iff_inv_eq₀ (IsAccretive.det_ne_zero
    ?P), MeasureTheory.integral_prod _ (.of_integral_ne_zero (by aesop))] at *
  convert! this using 6
  rw [show _ • _ = ((T h).fromBlocks (1 - posProj ε) 0 (T ↑k⁻¹ * k.1.1))ᴴ * (posProj ε).fromBlocks
    (posProj ε - 1) 1 1 * fromBlocks 1 1 (-T h) (-T h + T ↑g⁻¹ * k.1.1) by
    linear_combination (norm := (
      simp +zetaDelta [mul_sub, mul_add, add_mul, signMatrix_eq_posProj_sub, sub_mul,
        ← mul_assoc (posProj _) (posProj _)]; split_ands <;> module))
      congr(ofReal 2⁻¹ • fromBlocks $(h.2) 0 0 (-$(k.2)))]
  all_goals simp [J, T, ↓det_mul, -conjTranspose_add, ← principalMinor_coe_inv, field, realCoordSum,
    ← principalMinor_sign_eq_det, IsAccretive, conj_mul', ← exp_add, fromBlocks_mulVec,
    star_mulVec_dotProduct, Function.star_sumElim]
  ring
  convert (PosDef.conjTranspose_mul_self J ?_).add_posSemidef (.submatrix .one (id ⊕ᵥ id)) <;>
    simp [J, ← ext_iff, mulVec_injective_iff_isUnit]; grind⟩
