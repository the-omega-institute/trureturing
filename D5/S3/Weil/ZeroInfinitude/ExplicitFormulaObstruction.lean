/- GID: D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction
   mirror-E: none(waiver:kernel-verified-zero-infinitude-obstruction-only)
   anchors: []
   digest: The frozen explicit formula and cosine packet force every zero carrier to be infinite. -/

import D5.S3.Weil.ZeroInfinitude.CosinePacket
import D5.S3.Weil.ZeroInfinitude.ArchimedeanDivergence
import D5.S3.Weil.ZetaExplicit.Main
import D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite

/-!
# Explicit-formula obstruction to a finite zero carrier

This closes the zero-infinitude argument of Addendum Thirty. If a zero
configuration satisfying the frozen unconditional explicit formula had a
finite carrier, its zero side would tend to zero along the cosine-modulated
packet. The same explicit formula identifies that side with a right-hand side
whose Archimedean term diverges, while its pole terms vanish and its prime term
stays bounded, giving a contradiction.

For the canonical zeta configuration this proves that the set of nontrivial
zeros is infinite. It is not Hardy's theorem about zeros on the critical line,
and it is not a proof of the Riemann hypothesis. The `ZeroData` result is only
the frozen M1-a bridge applied to zero infinitude.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set Topology
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open scoped Topology

namespace D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction

/-- On the real axis, the modulated packet transform is the translated real packet. -/
theorem paperFT_cosineModulation_packet (T r : ℝ) :
    Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ) r =
      (ArchimedeanDivergence.packet
        (fun t : ℝ => (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) t).re)
        T r : ℂ) := by
  rw [CosinePacket.paperFT_cosineModulation]
  apply Complex.ext
  · simp [ArchimedeanDivergence.packet]
  · have hplus :
        (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) ((r : ℂ) + (T : ℂ))).im = 0 := by
      simpa only [Complex.ofReal_add] using
        (CosinePacket.packetTransform_real_nonneg (r + T)).1
    have hminus :
        (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) ((r : ℂ) - (T : ℂ))).im = 0 := by
      simpa only [Complex.ofReal_sub] using
        (CosinePacket.packetTransform_real_nonneg (r - T)).1
    rw [Complex.div_im, Complex.add_im, hplus, hminus]
    simp

/-- Closed-strip decay gives a quadratic majorant for the packet's real transform. -/
theorem packetTransform_re_decay :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : ℝ,
        |(Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) x).re| ≤
          K / (1 + x ^ 2) := by
  obtain ⟨K, hK, hdecay⟩ :=
    fourierLaplace_decay_closedStrip CosinePacket.packetSquare 0 le_rfl
  refine ⟨K, hK, fun x => ?_⟩
  calc
    |(Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) x).re| ≤
        ‖Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) x‖ :=
      Complex.abs_re_le_norm _
    _ = ‖D5.S3.Weil.FourierLaplace.fourierLaplace CosinePacket.packetSquare (x : ℂ)‖ := by
      rw [paperFT_eq_fourierLaplace]
    _ ≤ K / (1 + x ^ 2) := by
      simpa using hdecay (x : ℂ) (by simp)

/-- The real part of the explicit formula's Gamma term diverges for the packet. -/
private theorem gamma_term_re_tendsto_atTop :
    Tendsto
      (fun T : ℝ =>
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ,
            Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ) r *
              (Zeta23.EF.gammaBracket r : ℂ)).re)
      atTop atTop := by
  obtain ⟨δ, hδ, hlocal⟩ := CosinePacket.packetTransform_ge_half_near_zero
  obtain ⟨K, hK, hdecay⟩ := packetTransform_re_decay
  have harch := ArchimedeanDivergence.archimedean_divergence_complex_of_decay
    CosinePacket.packetTransform_integrable.re
    (fun r => (CosinePacket.packetTransform_real_nonneg r).2)
    hδ hlocal hK hdecay
  convert harch using 1
  funext T
  exact congrArg Complex.re
    (ArchimedeanDivergence.gamma_term_packet
      (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
      (paperFT_cosineModulation_packet T))

/-- The full literature right-hand side diverges along the modulated packet. -/
private theorem literatureRHS_re_tendsto_atTop :
    Tendsto
      (fun T : ℝ =>
        (Zeta23.EF.literatureRHS
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)).re)
      atTop atTop := by
  have hpolePos : Tendsto
      (fun T : ℝ =>
        (Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (Complex.I / 2)).re)
      atTop (nhds 0) := by
    exact Tendsto.comp (Complex.continuous_re.tendsto (0 : ℂ))
      CosinePacket.paperFT_cosineModulation_pole_pos_tendsto_zero
  have hpoleNeg : Tendsto
      (fun T : ℝ =>
        (Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (-Complex.I / 2)).re)
      atTop (nhds 0) := by
    exact Tendsto.comp (Complex.continuous_re.tendsto (0 : ℂ))
      CosinePacket.paperFT_cosineModulation_pole_neg_tendsto_zero
  obtain ⟨B, hB⟩ := CosinePacket.primeTerm_cosineModulation_bounded
  let P : ℝ → ℂ := fun T =>
    ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt n /
        Real.sqrt n : ℝ) : ℂ) *
      (CosinePacket.cosineModulation CosinePacket.packetSquare T (Real.log n) +
        CosinePacket.cosineModulation CosinePacket.packetSquare T (-Real.log n)))
  have hBnonneg : 0 ≤ B :=
    (norm_nonneg (P 0)).trans (by simpa [P] using hB 0)
  refine tendsto_atTop.2 fun a => ?_
  have hgamma := tendsto_atTop.1 gamma_term_re_tendsto_atTop (a + B + 2)
  have hpos := hpolePos.eventually (Ici_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  have hneg := hpoleNeg.eventually (Ici_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  filter_upwards [hgamma, hpos, hneg] with T hgammaT hposT hnegT
  have hprimeNorm : ‖P T‖ ≤ B := by
    simpa [P] using hB T
  have hprimeRe : (P T).re ≤ B :=
    (le_abs_self (P T).re).trans
      ((Complex.abs_re_le_norm (P T)).trans hprimeNorm)
  rw [Zeta23.EF.literatureRHS]
  simp only [Complex.add_re, Complex.sub_re]
  change a ≤
    (Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
      (Complex.I / 2)).re +
    (Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
      (-Complex.I / 2)).re -
    (P T).re +
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ r : ℝ,
        Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ) r *
          (Zeta23.EF.gammaBracket r : ℂ)).re
  linarith

/-- Every zero configuration satisfying the frozen explicit formula has infinite carrier. -/
theorem carrier_infinite_of_EF_lit
    (Z : Zeta23.ZeroConfig) (hEF : Zeta23.EF.EF_lit Z) :
    Z.carrier.Infinite := by
  intro hfinite
  have hzeroComplex := CosinePacket.finiteCarrier_zeroSide_tendsto_zero Z hfinite
  have hzeroReal : Tendsto
      (fun T : ℝ =>
        (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) *
          Zeta23.paperFT (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
            (Zeta23.gammaOf ρ)).re)
      atTop (nhds 0) := by
    exact Tendsto.comp (Complex.continuous_re.tendsto (0 : ℂ)) hzeroComplex
  have hrhsZero : Tendsto
      (fun T : ℝ =>
        (Zeta23.EF.literatureRHS
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)).re)
      atTop (nhds 0) := by
    convert hzeroReal using 1
    funext T
    have hk : ContDiff ℝ 2
        (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ) :=
      (CosinePacket.cosineModulation CosinePacket.packetSquare T).contDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top)
    exact congrArg Complex.re
      (hEF
        (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
        hk
        (CosinePacket.cosineModulation CosinePacket.packetSquare T).hasCompactSupport).2.symm
  exact not_tendsto_atTop_of_tendsto_nhds
    hrhsZero literatureRHS_re_tendsto_atTop

/-- The canonical zero configuration has exactly the nontrivial-zero carrier. -/
theorem zetaZeroConfig_carrier_identification :
    Zeta23.zetaZeroConfig.carrier = {ρ : ℂ | IsNontrivialZero ρ} :=
  Zeta23.zetaZeroConfig_carrier

/-- The set of nontrivial zeros of the Riemann zeta function is infinite. -/
theorem isNontrivialZero_infinite :
    {ρ : ℂ | IsNontrivialZero ρ}.Infinite := by
  have hcarrier : Zeta23.zetaZeroConfig.carrier.Infinite :=
    carrier_infinite_of_EF_lit Zeta23.zetaZeroConfig
      Zeta23.WeilEF.EF_lit_zetaZeroConfig
  rw [zetaZeroConfig_carrier_identification] at hcarrier
  exact hcarrier

/-- The frozen M1-a bridge turns zero infinitude into an inhabitant of `ZeroData`. -/
theorem nonempty_zeroData : Nonempty ZeroData :=
  D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite.mpr
    isNontrivialZero_infinite

-- The target hypothesis and theorem domain are inhabited in the pinned toolchain.
example : ∃ Z : Zeta23.ZeroConfig, Zeta23.EF.EF_lit Z :=
  ⟨Zeta23.zetaZeroConfig, Zeta23.WeilEF.EF_lit_zetaZeroConfig⟩

example : Nonempty Zeta23.ZeroConfig := ⟨Zeta23.zetaZeroConfig⟩

example : Nonempty ℂ := ⟨0⟩

#print axioms paperFT_cosineModulation_packet
#print axioms packetTransform_re_decay
#print axioms carrier_infinite_of_EF_lit
#print axioms zetaZeroConfig_carrier_identification
#print axioms isNontrivialZero_infinite
#print axioms nonempty_zeroData

end D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction
