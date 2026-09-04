/- GID: D5/S3/Weil/ZeroInfinitude/WindowZero
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroInfinitude/WindowZero
   mirror-E: none(waiver:kernel-verified-zero-window-existence-only)
   anchors: []
   digest: A fixed-width window at every sufficiently large height contains a zeta zero. -/

import D5.S3.Weil.ZeroInfinitude.CosinePacket
import D5.S3.Weil.ZeroInfinitude.ArchimedeanDivergence
import D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction
import D5.S3.Weil.ZetaExplicit.Main
import D5.S3.Weil.ZetaRvm.LocalCount
import D5.S3.Weil.ZetaExplicit.ZeroSummability

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace D5.S3.Weil.ZeroInfinitude.WindowZero

open D5.S3.Weil.ZeroInfinitude
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

def H (z : ℂ) : ℂ :=
  Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) z

theorem H_closed_strip_decay :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖H z‖ ≤ K / (1 + z.re ^ 2) := by
  obtain ⟨K, hK, hdecay⟩ :=
    fourierLaplace_decay_closedStrip CosinePacket.packetSquare (1 / 2) (by norm_num)
  refine ⟨K, hK, fun z hz => ?_⟩
  rw [H, paperFT_eq_fourierLaplace]
  exact hdecay z hz

theorem zero_summand_norm_le
    {K : ℝ}
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖H z‖ ≤ K / (1 + z.re ^ 2))
    (T : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (Zeta23.gammaOf ρ)‖ ≤
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) * (K / 2) *
        (1 / (1 + ((ρ : ℂ).im + T) ^ 2) +
          1 / (1 + ((ρ : ℂ).im - T) ^ 2)) := by
  have hstrip := Zeta23.WeilEF.abs_gammaOf_im_le
    (Zeta23.zetaZeroConfig.strip ρ ρ.2)
  have hp : ‖H (Zeta23.gammaOf ρ + T)‖ ≤
      K / (1 + ((ρ : ℂ).im + T) ^ 2) := by
    have him : |(Zeta23.gammaOf (ρ : ℂ) + (T : ℂ)).im| ≤ 1 / 2 := by
      simpa using hstrip
    simpa [Zeta23.WeilEF.gammaOf_re] using
      hdecay (Zeta23.gammaOf ρ + T) him
  have hm : ‖H (Zeta23.gammaOf ρ - T)‖ ≤
      K / (1 + ((ρ : ℂ).im - T) ^ 2) := by
    have him : |(Zeta23.gammaOf (ρ : ℂ) - (T : ℂ)).im| ≤ 1 / 2 := by
      simpa using hstrip
    simpa [Zeta23.WeilEF.gammaOf_re] using
      hdecay (Zeta23.gammaOf ρ - T) him
  have hmod :
      ‖Zeta23.paperFT
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (Zeta23.gammaOf ρ)‖ ≤
        (K / (1 + ((ρ : ℂ).im + T) ^ 2) +
          K / (1 + ((ρ : ℂ).im - T) ^ 2)) / 2 := by
    rw [CosinePacket.paperFT_cosineModulation, norm_div]
    simp only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hp hm)) (by norm_num)
  rw [norm_mul, Complex.norm_natCast]
  have hmult : (0 : ℝ) ≤ Zeta23.zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  calc
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
        ‖Zeta23.paperFT
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (Zeta23.gammaOf ρ)‖ ≤
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
        ((K / (1 + ((ρ : ℂ).im + T) ^ 2) +
          K / (1 + ((ρ : ℂ).im - T) ^ 2)) / 2) :=
      mul_le_mul_of_nonneg_left hmod hmult
    _ = _ := by ring

/-- Quantitative form of the archimedean growth needed to beat a fixed
window tail. -/
theorem gamma_term_re_lower_log :
    ∃ c M T₁ : ℝ, 0 < c ∧ ∀ T : ℝ, T₁ ≤ T →
      c * Real.log (T + 3) - M ≤
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ,
            Zeta23.paperFT
                (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ) r *
              (Zeta23.EF.gammaBracket r : ℂ)).re := by
  obtain ⟨δ, hδ, hlocal⟩ := CosinePacket.packetTransform_ge_half_near_zero
  obtain ⟨K, hK, hdecay⟩ :=
    ExplicitFormulaObstruction.packetTransform_re_decay
  obtain ⟨C, hstirling⟩ := Zeta23.StirlingVert.mu_stirling
  have hC : 0 ≤ C := by
    have h := hstirling 1 (by norm_num)
    have := (abs_nonneg
      (Zeta23.mu 1 - (1 / (2 * Real.pi)) *
        Real.log (|1| / (2 * Real.pi)))).trans h
    norm_num at this ⊢
    exact this
  let T₁ : ℝ := max δ (max 300 (max (2 * |δ|) (2 * (C + 1))))
  refine ⟨δ / (8 * Real.pi), ∫ r : ℝ, (H r).re, T₁, by positivity, fun T hT => ?_⟩
  have hTδ : δ ≤ T := le_trans (le_max_left _ _) hT
  have hT300 : (300 : ℝ) ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hTabs : 2 * |δ| ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hT))
  have hTC : 2 * (C + 1) ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hT))
  let S : ℝ := T - δ
  have hS_half : T / 2 ≤ S := by
    dsimp [S]
    have hδabs := le_abs_self δ
    linarith
  have hS1 : 1 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hSabs : |S| = S := abs_of_pos hSpos
  have hTsq : 256 * (T + 3) ≤ T ^ 2 := by
    have hT0 : 0 ≤ T := by linarith
    have h300mul : 300 * T ≤ T * T :=
      mul_le_mul_of_nonneg_right hT300 hT0
    nlinarith
  have hsqrt_sq : Real.sqrt (T + 3) ^ 2 = T + 3 :=
    Real.sq_sqrt (by linarith)
  have hsqrt_le : Real.sqrt (T + 3) ≤ T / 16 := by
    have hsqrt0 := Real.sqrt_nonneg (T + 3)
    nlinarith
  have hgeom : 2 * Real.pi * Real.sqrt (T + 3) ≤ S := by
    have hπ := Real.pi_le_four
    have hsqrt0 := Real.sqrt_nonneg (T + 3)
    have : 2 * Real.pi * Real.sqrt (T + 3) ≤
        8 * Real.sqrt (T + 3) := by nlinarith
    calc
      2 * Real.pi * Real.sqrt (T + 3) ≤ 8 * Real.sqrt (T + 3) := this
      _ ≤ T / 2 := by linarith
      _ ≤ S := hS_half
  have hlogcomp : Real.log (T + 3) / 2 ≤
      Real.log (S / (2 * Real.pi)) := by
    have hsqrt_pos : 0 < Real.sqrt (T + 3) := Real.sqrt_pos.2 (by linarith)
    have hdiv : Real.sqrt (T + 3) ≤ S / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      simpa [mul_comm] using hgeom
    have hlog := Real.log_le_log hsqrt_pos hdiv
    rw [Real.log_sqrt (by linarith : 0 ≤ T + 3)] at hlog
    exact hlog
  have hCerr : C / S ^ 2 ≤ 1 := by
    have hCS : C ≤ S := by linarith
    have hCSsq : C ≤ S ^ 2 := by nlinarith
    exact (div_le_one (sq_pos_of_pos hSpos)).2 hCSsq
  have hst := hstirling S (by simpa [hSabs] using hS1)
  rw [hSabs] at hst
  have hmu : (1 / (4 * Real.pi)) * Real.log (T + 3) - 1 ≤ Zeta23.mu S := by
    have hlo := (abs_le.mp hst).1
    have hmain : (1 / (4 * Real.pi)) * Real.log (T + 3) ≤
        (1 / (2 * Real.pi)) * Real.log (S / (2 * Real.pi)) := by
      have hfac : 0 ≤ 1 / (2 * Real.pi) := by positivity
      calc
        (1 / (4 * Real.pi)) * Real.log (T + 3) =
            (1 / (2 * Real.pi)) * (Real.log (T + 3) / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogcomp hfac
    linarith
  have harch := ArchimedeanDivergence.archimedean_lower_bound
    CosinePacket.packetTransform_integrable.re
    (fun r => (CosinePacket.packetTransform_real_nonneg r).2)
    hδ hlocal hK hdecay hTδ
  have hweighted := ArchimedeanDivergence.packet_weighted_integrable_of_decay
    CosinePacket.packetTransform_integrable.re hK hdecay T
  have hcomplex : Integrable (fun r : ℝ =>
      (ArchimedeanDivergence.packet
          (fun t : ℝ =>
            (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) t).re)
          T r : ℂ) *
        (Zeta23.mu r : ℂ)) := by
    convert hweighted.ofReal using 1
    funext r
    norm_num
  have hreal :
      (∫ r : ℝ,
        (ArchimedeanDivergence.packet
            (fun t : ℝ =>
              (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) t).re)
            T r : ℂ) *
          (Zeta23.mu r : ℂ)).re =
        ∫ r : ℝ,
          ArchimedeanDivergence.packet
              (fun t : ℝ =>
                (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) t).re)
              T r * Zeta23.mu r := by
    calc
      _ = ∫ r : ℝ, Complex.re
          ((ArchimedeanDivergence.packet
              (fun t : ℝ =>
                (Zeta23.paperFT (CosinePacket.packetSquare : ℝ → ℂ) t).re)
              T r : ℂ) *
            (Zeta23.mu r : ℂ)) := (integral_re hcomplex).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with r
        norm_num
  rw [ArchimedeanDivergence.gamma_term_packet
    (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
    (ExplicitFormulaObstruction.paperFT_cosineModulation_packet T), hreal]
  dsimp [S] at hmu
  have hmu1 : (1 / (4 * Real.pi)) * Real.log (T + 3) ≤
      Zeta23.mu (T - δ) + 1 := by linarith
  have hscale := mul_le_mul_of_nonneg_left hmu1 (show 0 ≤ δ / 2 by positivity)
  calc
    δ / (8 * Real.pi) * Real.log (T + 3) - ∫ r : ℝ, (H r).re =
        δ / 2 * ((1 / (4 * Real.pi)) * Real.log (T + 3)) -
          ∫ r : ℝ, (H r).re := by ring
    _ ≤
        δ / 2 * (Zeta23.mu (T - δ) + 1) - ∫ r : ℝ, (H r).re := by
      exact sub_le_sub_right hscale (∫ r : ℝ, (H r).re)
    _ ≤ _ := by simpa [H] using harch

/-- Quantitative lower bound for the entire literature RHS. -/
theorem literatureRHS_re_lower_log :
    ∃ c M T₁ : ℝ, 0 < c ∧ ∀ T : ℝ, T₁ ≤ T →
      c * Real.log (T + 3) - M ≤
        (Zeta23.EF.literatureRHS
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)).re := by
  let primeTerm : ℝ → ℂ := fun T =>
    ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt n /
        Real.sqrt n : ℝ) : ℂ) *
      (CosinePacket.cosineModulation CosinePacket.packetSquare T (Real.log n) +
        CosinePacket.cosineModulation CosinePacket.packetSquare T (-Real.log n)))
  obtain ⟨c, Mγ, Tγ, hc, hgamma⟩ := gamma_term_re_lower_log
  have hpolePos : Tendsto
      (fun T : ℝ =>
        (Zeta23.paperFT
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (Complex.I / 2)).re)
      atTop (nhds 0) := by
    exact Tendsto.comp (Complex.continuous_re.tendsto (0 : ℂ))
      CosinePacket.paperFT_cosineModulation_pole_pos_tendsto_zero
  have hpoleNeg : Tendsto
      (fun T : ℝ =>
        (Zeta23.paperFT
          (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
          (-Complex.I / 2)).re)
      atTop (nhds 0) := by
    exact Tendsto.comp (Complex.continuous_re.tendsto (0 : ℂ))
      CosinePacket.paperFT_cosineModulation_pole_neg_tendsto_zero
  have hposEv := hpolePos.eventually
    (Ici_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  have hnegEv := hpoleNeg.eventually
    (Ici_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  obtain ⟨Tpos, hTpos⟩ := eventually_atTop.1 hposEv
  obtain ⟨Tneg, hTneg⟩ := eventually_atTop.1 hnegEv
  obtain ⟨B, hB⟩ := CosinePacket.primeTerm_cosineModulation_bounded
  refine ⟨c, Mγ + B + 2, max Tγ (max Tpos Tneg), hc, fun T hT => ?_⟩
  have hTγ : Tγ ≤ T := (le_max_left _ _).trans hT
  have hTp : Tpos ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTn : Tneg ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hprimeNorm : ‖primeTerm T‖ ≤ B := by simpa [primeTerm] using hB T
  have hprimeRe : (primeTerm T).re ≤ B :=
    (le_abs_self (primeTerm T).re).trans
      ((Complex.abs_re_le_norm (primeTerm T)).trans hprimeNorm)
  have hγ := hgamma T hTγ
  have hp := hTpos T hTp
  have hn := hTneg T hTn
  rw [Zeta23.EF.literatureRHS]
  simp only [Complex.add_re, Complex.sub_re]
  change c * Real.log (T + 3) - (Mγ + B + 2) ≤
    (Zeta23.paperFT
      (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
      (Complex.I / 2)).re +
    (Zeta23.paperFT
      (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ)
      (-Complex.I / 2)).re -
    (primeTerm T).re +
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ r : ℝ,
        Zeta23.paperFT
            (CosinePacket.cosineModulation CosinePacket.packetSquare T : ℝ → ℂ) r *
          (Zeta23.EF.gammaBracket r : ℂ)).re
  linarith

open Zeta23 WeilEF

/-- The unweighted inverse-square integer kernel is summable. -/
theorem summable_shift_kernel :
    Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num)) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  have hnonneg : 0 ≤ 1 / (1 + (n : ℝ) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    Real.rpow_neg (abs_nonneg (n : ℝ)), show (2 : ℝ) = (2 : ℕ) by norm_num,
    Real.rpow_natCast, sq_abs, one_div]
  exact inv_anti₀ (by positivity) (by linarith)

/-- A finite-set form of the fact that the inverse-square kernel has arbitrarily
small tails.  This is the radius-selection input needed by the window argument. -/
theorem exists_radius_kernel_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ s : Finset ℤ,
      (∀ n ∈ s, R ≤ |(n : ℝ)|) →
      ∑ n ∈ s, 1 / (1 + (n : ℝ) ^ 2) < ε := by
  classical
  obtain ⟨F, hF⟩ :=
    (summable_iff_vanishing_norm.mp summable_shift_kernel) ε hε
  let R : ℝ := 1 + ∑ n ∈ F, |(n : ℝ)|
  refine ⟨R, ?_, fun s hs => ?_⟩
  · dsimp [R]
    have : 0 ≤ ∑ n ∈ F, |(n : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hdisj : Disjoint s F := by
    rw [Finset.disjoint_left]
    intro n hns hnF
    have hle : |(n : ℝ)| ≤ ∑ k ∈ F, |(k : ℝ)| := by
      exact Finset.single_le_sum
        (s := F) (f := fun k : ℤ => |(k : ℝ)|)
        (fun k _ => abs_nonneg (k : ℝ)) hnF
    have := hs n hns
    dsimp [R] at this
    linarith
  have htail := hF s hdisj
  have hnonneg : 0 ≤ ∑ n ∈ s, 1 / (1 + (n : ℝ) ^ 2) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using htail

/-- Finite shifted inverse-square bound after grouping ordinates into unit
windows.  It isolates the exact logarithmic coefficient controlled by choosing
the gap radius. -/
theorem shifted_inv_sq_finite_le
    {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : Zeta23.Tail.LocalCount γ m A₀) (s : Finset ι) :
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
      4 * A₀ *
        (Real.log (|T| + 3) *
            ∑ n ∈ s.image (fun ρ => WeilEF.key (γ ρ - T)),
              1 / (1 + (n : ℝ) ^ 2) + WeilEF.totalWeight) := by
  classical
  let κ : ι → ℤ := fun ρ => WeilEF.key (γ ρ - T)
  have hA₀ : 0 ≤ A₀ := (zero_le_one.trans hN.one_le)
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
    (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
        4 * A₀ * Real.log (|T + n| + 3) / (1 + (n : ℝ) ^ 2) := by
    intro n hn
    have hwin := hN.window (T + n) (s.filter fun ρ => κ ρ = n) (by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      dsimp [κ] at hρ
      have hlt := WeilEF.key_lt (γ ρ - T)
      have hle := WeilEF.le_key_add_one (γ ρ - T)
      have hρcast : ((WeilEF.key (γ ρ - T) : ℤ) : ℝ) = (n : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hρ.2
      rw [hρcast] at hlt hle
      constructor <;> linarith)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
          (4 / (1 + (n : ℝ) ^ 2)) * (m ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      dsimp [κ] at hρ
      have hlt := WeilEF.key_lt (γ ρ - T)
      have hle := WeilEF.le_key_add_one (γ ρ - T)
      have hρcast : ((WeilEF.key (γ ρ - T) : ℤ) : ℝ) = (n : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hρ.2
      rw [hρcast] at hlt hle
      have hden := WeilEF.one_add_sq_ge hlt hle
      have hm : (0 : ℝ) ≤ m ρ := Nat.cast_nonneg _
      have hinv : 1 / (1 + (γ ρ - T) ^ 2) ≤
          4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc
        (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) =
            (m ρ : ℝ) * (1 / (1 + (γ ρ - T) ^ 2)) := by ring
        _ ≤ (m ρ : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hinv hm
        _ = _ := by ring
    calc
      ∑ ρ ∈ s with κ ρ = n, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
          ∑ ρ ∈ s with κ ρ = n,
            (4 / (1 + (n : ℝ) ^ 2)) * (m ρ : ℝ) :=
        Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) *
          ∑ ρ ∈ s with κ ρ = n, (m ρ : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) *
          (A₀ * Real.log (|T + n| + 3)) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = _ := by ring
  calc
    ∑ n ∈ s.image κ,
        ∑ ρ ∈ s with κ ρ = n, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
        ∑ n ∈ s.image κ,
          4 * A₀ * Real.log (|T + n| + 3) / (1 + (n : ℝ) ^ 2) :=
      Finset.sum_le_sum hfiber
    _ ≤ ∑ n ∈ s.image κ,
        4 * A₀ *
          ((Real.log (|T| + 3) + Real.log (|(n : ℝ)| + 3)) /
            (1 + (n : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hprod : |T + (n : ℝ)| + 3 ≤ (|T| + 3) * (|(n : ℝ)| + 3) := by
        have hadd := abs_add_le T (n : ℝ)
        nlinarith [abs_nonneg T, abs_nonneg (n : ℝ)]
      have hlog : Real.log (|T + (n : ℝ)| + 3) ≤
          Real.log (|T| + 3) + Real.log (|(n : ℝ)| + 3) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        exact Real.log_le_log (by positivity) hprod
      have hfac : 0 ≤ 4 * A₀ / (1 + (n : ℝ) ^ 2) := by positivity
      calc
        4 * A₀ * Real.log (|T + (n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) =
            (4 * A₀ / (1 + (n : ℝ) ^ 2)) *
              Real.log (|T + (n : ℝ)| + 3) := by ring
        _ ≤ (4 * A₀ / (1 + (n : ℝ) ^ 2)) *
              (Real.log (|T| + 3) + Real.log (|(n : ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hlog hfac
        _ = _ := by ring
    _ = 4 * A₀ *
        (Real.log (|T| + 3) *
            ∑ n ∈ s.image κ, 1 / (1 + (n : ℝ) ^ 2) +
          ∑ n ∈ s.image κ,
            Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
      have hconst :
          (∑ n ∈ s.image κ, Real.log (|T| + 3) / (1 + (n : ℝ) ^ 2)) =
            Real.log (|T| + 3) *
              ∑ n ∈ s.image κ, 1 / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      have hweight :
          (∑ n ∈ s.image κ,
              (4 * A₀) * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2))) =
            (4 * A₀) * ∑ n ∈ s.image κ,
              Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        exact (Finset.mul_sum (s.image κ)
          (fun n : ℤ => Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2))
          (4 * A₀)).symm
      simp_rw [add_div, mul_add, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, hconst]
      rw [hweight]
    _ ≤ 4 * A₀ *
        (Real.log (|T| + 3) *
            ∑ n ∈ s.image κ, 1 / (1 + (n : ℝ) ^ 2) + WeilEF.totalWeight) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hA₀)
      gcongr
      exact WeilEF.summable_weight.sum_le_tsum _ fun n _ =>
        div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)

/-- Uniform finite-subfamily tail estimate.  The coefficient of
`log (|T|+3)` can be made arbitrarily small by fixing one absolute radius. -/
theorem exists_radius_shifted_inv_sq_finite
    {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ ε : ℝ}
    (hN : Zeta23.Tail.LocalCount γ m A₀) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ (T : ℝ) (s : Finset ι),
      (∀ ρ ∈ s, R ≤ |γ ρ - T|) →
      ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
        4 * A₀ * (ε * Real.log (|T| + 3) + WeilEF.totalWeight) := by
  classical
  obtain ⟨R₀, hR₀, htail⟩ := exists_radius_kernel_tail hε
  refine ⟨R₀ + 1, by linarith, fun T s hgap => ?_⟩
  let κ : ι → ℤ := fun ρ => WeilEF.key (γ ρ - T)
  have hkeyfar : ∀ n ∈ s.image κ, R₀ ≤ |(n : ℝ)| := by
    intro n hn
    obtain ⟨ρ, hρs, hρκ⟩ := Finset.mem_image.mp hn
    have hρcast : ((WeilEF.key (γ ρ - T) : ℤ) : ℝ) = (n : ℝ) :=
      congrArg (fun z : ℤ => (z : ℝ)) hρκ
    have hlt := WeilEF.key_lt (γ ρ - T)
    have hle := WeilEF.le_key_add_one (γ ρ - T)
    rw [hρcast] at hlt hle
    have hgapρ := hgap ρ hρs
    rcases le_abs'.mp hgapρ with hneg | hpos
    · have hn : (n : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hn]
      linarith
    · have hn : 0 ≤ (n : ℝ) := by linarith
      rw [abs_of_nonneg hn]
      linarith
  have hkern :
      ∑ n ∈ s.image κ, 1 / (1 + (n : ℝ) ^ 2) < ε :=
    htail (s.image κ) hkeyfar
  have hlog : 0 ≤ Real.log (|T| + 3) :=
    Real.log_nonneg (by linarith [abs_nonneg T])
  have hA₀ : 0 ≤ A₀ := zero_le_one.trans hN.one_le
  calc
    ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
        4 * A₀ *
          (Real.log (|T| + 3) *
              ∑ n ∈ s.image κ, 1 / (1 + (n : ℝ) ^ 2) + WeilEF.totalWeight) :=
      shifted_inv_sq_finite_le hN s
    _ ≤ 4 * A₀ *
        (Real.log (|T| + 3) * ε + WeilEF.totalWeight) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hA₀)
      gcongr
    _ = _ := by ring

/-- The finite-subfamily estimate passes to the full nonnegative series. -/
theorem exists_radius_shifted_inv_sq_tsum
    {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ ε : ℝ}
    (hN : Zeta23.Tail.LocalCount γ m A₀) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ T : ℝ,
      (∀ ρ : ι, R ≤ |γ ρ - T|) →
      Summable (fun ρ : ι => (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2)) ∧
      ∑' ρ : ι, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
        4 * A₀ * (ε * Real.log (|T| + 3) + WeilEF.totalWeight) := by
  obtain ⟨R, hR, hfin⟩ := exists_radius_shifted_inv_sq_finite hN hε
  refine ⟨R, hR, fun T hgap => ?_⟩
  have hfinite : ∀ s : Finset ι,
      ∑ ρ ∈ s, (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) ≤
        4 * A₀ * (ε * Real.log (|T| + 3) + WeilEF.totalWeight) :=
    fun s => hfin T s (fun ρ hρ => hgap ρ)
  have hnonneg : 0 ≤ fun ρ : ι =>
      (m ρ : ℝ) / (1 + (γ ρ - T) ^ 2) :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hs := summable_of_sum_le hnonneg hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- Conjugation preserves the canonical zeta carrier. -/
theorem zetaZeroConfig_conj_mem {ρ : ℂ}
    (hρ : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    conj ρ ∈ Zeta23.zetaZeroConfig.carrier := by
  rw [Zeta23.zetaZeroConfig_carrier] at hρ ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [_root_.riemannZeta_conj, hρ.1, map_zero]
  · simpa using hρ.2.1
  · simpa using hρ.2.2

/-- Absence of a zeta zero near `T` also gives absence near `-T`, by
complex conjugation. -/
theorem no_zero_near_neg_of_no_zero_near
    {R T : ℝ}
    (hgap : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, R ≤ |ρ.im - T|) :
    ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, R ≤ |ρ.im + T| := by
  intro ρ hρ
  have hc := hgap (conj ρ) (zetaZeroConfig_conj_mem hρ)
  simpa [abs_sub_comm, add_comm] using hc

theorem exists_zero_near_every_large_height :
    ∃ R T₀ : ℝ, 0 < R ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ ρ ∈ Zeta23.zetaZeroConfig.carrier, |ρ.im - T| ≤ R := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount
    Zeta23.zetaZeroConfig hA₀ hloc
  obtain ⟨K, hK, hdecay⟩ := H_closed_strip_decay
  have hK1 : 1 ≤ K := by
    have h := hdecay 0 (by norm_num)
    rw [H, CosinePacket.packetTransform_zero] at h
    norm_num at h
    simpa using h
  obtain ⟨c, M, TR, hc, hRHS⟩ := literatureRHS_re_lower_log
  let ε : ℝ := c / (8 * K * A₀)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨R, hR2, htail⟩ :=
    exists_radius_shifted_inv_sq_tsum hLC hε
  let Ctail : ℝ := 4 * K * A₀ * WeilEF.totalWeight
  let D : ℝ := |M| + |Ctail| + 1
  let T₀ : ℝ := max TR (Real.exp (2 * D / c))
  refine ⟨R, T₀, by linarith, fun T hT => ?_⟩
  have hTR : TR ≤ T := (le_max_left _ _).trans hT
  have hTexp : Real.exp (2 * D / c) ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hTexp
  have hloglarge : 2 * D / c ≤ Real.log (T + 3) := by
    rw [← Real.log_exp (2 * D / c)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hDpos : 0 < D := by
    dsimp [D]
    linarith [abs_nonneg M, abs_nonneg Ctail]
  have hdom : M + Ctail < c / 2 * Real.log (T + 3) := by
    have hc0 : 0 < c / 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hloglarge hc0.le
    have hMD : M + Ctail < D := by
      dsimp [D]
      have hM := le_abs_self M
      have hC := le_abs_self Ctail
      linarith
    have heq : c / 2 * (2 * D / c) = D := by field_simp
    rw [heq] at hscaled
    linarith
  by_contra hnone
  push Not at hnone
  have hgap : ∀ ρ : Zeta23.zetaZeroConfig.carrier,
      R ≤ |(ρ : ℂ).im - T| := fun ρ => (hnone ρ ρ.2).le
  have hgapNeg : ∀ ρ : Zeta23.zetaZeroConfig.carrier,
      R ≤ |(ρ : ℂ).im + T| := fun ρ =>
    no_zero_near_neg_of_no_zero_near
      (fun z hz => hgap ⟨z, hz⟩) ρ ρ.2
  have hminus := htail T hgap
  have hplus := htail (-T) (fun ρ => by simpa using hgapNeg ρ)
  let fminus : Zeta23.zetaZeroConfig.carrier → ℝ := fun ρ =>
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) /
      (1 + ((ρ : ℂ).im - T) ^ 2)
  let fplus : Zeta23.zetaZeroConfig.carrier → ℝ := fun ρ =>
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) /
      (1 + ((ρ : ℂ).im + T) ^ 2)
  have hfminus : Summable fminus := by simpa [fminus] using hminus.1
  have hfplus : Summable fplus := by simpa [fplus] using hplus.1
  have hfminusBound : ∑' ρ, fminus ρ ≤
      4 * A₀ * (ε * Real.log (T + 3) + WeilEF.totalWeight) := by
    simpa [fminus, abs_of_pos hTpos] using hminus.2
  have hfplusBound : ∑' ρ, fplus ρ ≤
      4 * A₀ * (ε * Real.log (T + 3) + WeilEF.totalWeight) := by
    simpa [fplus, abs_of_pos hTpos] using hplus.2
  let k := CosinePacket.cosineModulation CosinePacket.packetSquare T
  obtain ⟨hzeroSummable, hEF⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig (k : ℝ → ℂ)
      (k.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)) k.hasCompactSupport
  let upper : Zeta23.zetaZeroConfig.carrier → ℝ := fun ρ =>
    (K / 2) * (fplus ρ + fminus ρ)
  have hupperSummable : Summable upper := by
    exact (hfplus.add hfminus).mul_left (K / 2)
  have hpoint : ∀ ρ : Zeta23.zetaZeroConfig.carrier,
      ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (k : ℝ → ℂ) (Zeta23.gammaOf ρ)‖ ≤ upper ρ := by
    intro ρ
    have h := zero_summand_norm_le hdecay T ρ
    calc
      ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ) *
          Zeta23.paperFT (k : ℝ → ℂ) (Zeta23.gammaOf ρ)‖ ≤
        (Zeta23.zetaZeroConfig.mult ρ : ℝ) * (K / 2) *
          (1 / (1 + ((ρ : ℂ).im + T) ^ 2) +
            1 / (1 + ((ρ : ℂ).im - T) ^ 2)) := by simpa [k] using h
      _ = upper ρ := by dsimp [upper, fplus, fminus]; ring
  have hzeroNorm :
      ‖∑' ρ : Zeta23.zetaZeroConfig.carrier,
          (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
            Zeta23.paperFT (k : ℝ → ℂ) (Zeta23.gammaOf ρ)‖ ≤
        (K / 2) *
          (8 * A₀ * (ε * Real.log (T + 3) + WeilEF.totalWeight)) := by
    calc
      _ ≤ ∑' ρ : Zeta23.zetaZeroConfig.carrier,
          ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ) *
            Zeta23.paperFT (k : ℝ → ℂ) (Zeta23.gammaOf ρ)‖ :=
        norm_tsum_le_tsum_norm hzeroSummable.norm
      _ ≤ ∑' ρ, upper ρ :=
        hzeroSummable.norm.tsum_le_tsum hpoint hupperSummable
      _ = (K / 2) * ((∑' ρ, fplus ρ) + ∑' ρ, fminus ρ) := by
        rw [show upper = fun ρ => (K / 2) * (fplus ρ + fminus ρ) from rfl,
          (hfplus.add hfminus).tsum_mul_left, hfplus.tsum_add hfminus]
      _ ≤ (K / 2) *
          (8 * A₀ * (ε * Real.log (T + 3) + WeilEF.totalWeight)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  have hzeroFinal :
      ‖∑' ρ : Zeta23.zetaZeroConfig.carrier,
          (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
            Zeta23.paperFT (k : ℝ → ℂ) (Zeta23.gammaOf ρ)‖ ≤
        c / 2 * Real.log (T + 3) + Ctail := by
    calc
      _ ≤ (K / 2) *
          (8 * A₀ * (ε * Real.log (T + 3) + WeilEF.totalWeight)) := hzeroNorm
      _ = _ := by
        dsimp [ε, Ctail]
        field_simp
        ring
  have hlower : c * Real.log (T + 3) - M ≤
      (Zeta23.EF.literatureRHS (k : ℝ → ℂ)).re := by
    simpa [k] using hRHS T hTR
  have hreNorm :
      (Zeta23.EF.literatureRHS (k : ℝ → ℂ)).re ≤
        ‖Zeta23.EF.literatureRHS (k : ℝ → ℂ)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hreNormZero := hreNorm
  rw [← hEF] at hreNormZero
  rw [← hEF] at hlower
  linarith

#print axioms summable_shift_kernel
#print axioms exists_radius_kernel_tail
#print axioms shifted_inv_sq_finite_le
#print axioms exists_radius_shifted_inv_sq_finite
#print axioms exists_radius_shifted_inv_sq_tsum
#print axioms zetaZeroConfig_conj_mem
#print axioms no_zero_near_neg_of_no_zero_near
#print axioms H_closed_strip_decay
#print axioms zero_summand_norm_le
#print axioms gamma_term_re_lower_log
#print axioms literatureRHS_re_lower_log
#print axioms exists_zero_near_every_large_height

end D5.S3.Weil.ZeroInfinitude.WindowZero
