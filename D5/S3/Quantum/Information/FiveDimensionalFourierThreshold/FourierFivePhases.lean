/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFivePhases
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFivePhases
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero fifth-root phases bound sums of two and three distinct terms. -/

import Mathlib.Tactic
import D5.S3.Quantum.ShorCountingMarginal
import D5.S3.Constants.PentagonCosines
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Exact pentagon estimates for the phases in small Fourier Gram matrices. -/

open scoped BigOperators
open QuantumPhaseEstimationGeneral
open D5.S3.Constants.PentagonCosines

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

abbrev pentagonPhase := ZMod.stdAddChar (N := 5)

private theorem pentagonPhase_norm (a : ZMod 5) : ‖pentagonPhase a‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

private theorem pentagonPhase_re (a : ZMod 5) :
    (pentagonPhase a).re = Real.cos (2 * Real.pi * (a.val : ℝ) / 5) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

private theorem pentagon_cos_le (a : ZMod 5) (ha : a ≠ 0) :
    Real.cos (2 * Real.pi * (a.val : ℝ) / 5) ≤ (Real.sqrt 5 - 1) / 4 := by
  obtain ⟨h₁, h₂, _, _⟩ := pentagon_golden_cosines
  have cos₂ : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [Real.inv_goldenRatio, Real.goldenConj] at h₂
    linarith only [h₂]
  have cos₄ : Real.cos (2 * Real.pi * 2 / 5) = -(1 + Real.sqrt 5) / 4 := by
    rw [show 2 * Real.pi * 2 / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub]
    rw [Real.goldenRatio] at h₁
    linarith only [h₁]
  have cos₆ : Real.cos (2 * Real.pi * 3 / 5) = Real.cos (2 * Real.pi * 2 / 5) := by
    rw [show 2 * Real.pi * 3 / 5 = 2 * Real.pi - 2 * Real.pi * 2 / 5 by ring,
      Real.cos_two_pi_sub]
  have cos₈ : Real.cos (2 * Real.pi * 4 / 5) = Real.cos (2 * Real.pi / 5) := by
    rw [show 2 * Real.pi * 4 / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring, Real.cos_two_pi_sub]
  have hc : -(1 + Real.sqrt 5) / 4 ≤ (Real.sqrt 5 - 1) / 4 := by
    linarith only [Real.sqrt_nonneg (5 : ℝ)]
  have hlt := ZMod.val_lt a
  have hpos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha (ZMod.val_injective 5 (by simpa using h)))
  interval_cases h : a.val
  · norm_num only [Nat.cast_one, mul_one, cos₂, le_refl]
  · exact_mod_cast (cos₄.le.trans hc)
  · exact_mod_cast (cos₆.le.trans (cos₄.le.trans hc))
  · exact_mod_cast (cos₈.le.trans cos₂.le)

/-- The cross-term from a pair of distinct pentagon phases is at most the golden ratio. -/
theorem pentagonPhase_pair_norm (a b : ZMod 5) (hab : a ≠ b) :
    ‖pentagonPhase a + pentagonPhase b‖ ≤ Real.goldenRatio := by
  have hb : b = a + (b - a) := by abel
  have hfact : pentagonPhase a + pentagonPhase b =
      pentagonPhase a * (1 + pentagonPhase (b - a)) := by
    rw [mul_add, mul_one, ← AddChar.map_add_eq_mul, ← hb]
  rw [hfact, norm_mul, pentagonPhase_norm, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) Real.goldenRatio_pos.le).1
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_eq_norm_sq (pentagonPhase _),
    pentagonPhase_norm, Complex.normSq_one, one_mul, Complex.conj_re,
    pentagonPhase_re, Real.goldenRatio_sq, Real.goldenRatio]
  have h := pentagon_cos_le (b - a) (sub_ne_zero.mpr hab.symm)
  linarith only [h]

private theorem sum_pentagonPhase : ∑ a : ZMod 5, pentagonPhase a = 0 := by
  apply AddChar.sum_eq_zero_of_ne_one
  intro h
  have hvalue : pentagonPhase 1 = pentagonPhase 0 := by rw [h]; simp
  exact (by decide : (1 : ZMod 5) ≠ 0) (ZMod.injective_stdAddChar hvalue)

/-- A two- or three-term Fourier Gram sum reduces to two distinct pentagon phases. -/
theorem pentagonPhase_small_sum (s : Finset (Fin 5)) (m : ZMod 5) (hm : m ≠ 0)
    (hs : s.card = 2 ∨ s.card = 3) :
    ‖∑ j ∈ s, pentagonPhase (m * ZMod.finEquiv 5 j)‖ ≤ Real.goldenRatio := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let e : Fin 5 ≃ ZMod 5 := (ZMod.finEquiv 5).toEquiv.trans (Equiv.mulLeft₀ m hm)
  change ‖∑ j ∈ s, pentagonPhase (e j)‖ ≤ Real.goldenRatio
  have htwo (t : Finset (Fin 5)) (ht : t.card = 2) :
      ‖∑ j ∈ t, pentagonPhase (e j)‖ ≤ Real.goldenRatio := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht
    rw [Finset.sum_pair hab]
    exact pentagonPhase_pair_norm _ _ (e.injective.ne hab)
  rcases hs with h | h
  · exact htwo s h
  have hc : sᶜ.card = 2 := by rw [Finset.card_compl, Fintype.card_fin, h]
  have htotal := Finset.sum_compl_add_sum s (fun j => pentagonPhase (e j))
  rw [e.sum_comp, sum_pentagonPhase] at htotal
  have hrepl : (∑ j ∈ s, pentagonPhase (e j)) = -(∑ j ∈ sᶜ, pentagonPhase (e j)) :=
    eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using htotal)
  rw [hrepl, norm_neg]
  exact htwo sᶜ hc

private theorem finEquiv_eq_natCast (j : Fin 5) : ZMod.finEquiv 5 j = (j.val : ZMod 5) := by
  apply ZMod.val_injective 5
  rw [ZMod.val_natCast_of_lt j.isLt]
  rfl

/-- The repo Fourier kernel equals the standard additive character at the index product. -/
theorem kernel_five_eq_pentagonPhase (j k : Fin 5) :
    kernel 5 j k = pentagonPhase (ZMod.finEquiv 5 j * ZMod.finEquiv 5 k) := by
  rw [finEquiv_eq_natCast, finEquiv_eq_natCast, ← Nat.cast_mul, ← Int.cast_natCast,
    ZMod.stdAddChar_coe, kernel, phase]
  congr 1
  push_cast
  ring

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
