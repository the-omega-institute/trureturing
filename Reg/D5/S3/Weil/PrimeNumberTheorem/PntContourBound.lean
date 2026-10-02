import D5.S3.Weil.PrimeNumberTheorem.PntContourBound
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.PntContourBound

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
local notation "𝓜" => mellin

noncomputable section
theorem Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  have hSym {𝕂 : Type} [RCLike 𝕂] (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
      MellinConvolution f g x = MellinConvolution g f x := by
    have hMul (h : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
        ∫ y in Ioi 0, h (y * a) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_mul_right_Ioi (fun y ↦ h y / y) 0 ha
      simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at hh
      rw [← integral_smul] at hh
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro _ _
      simp only [RCLike.real_smul_eq_coe_mul]
      rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
      exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
    have hInv (h : ℝ → 𝕂) :
        ∫ y in Ioi 0, h (1 / y) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_rpow_Ioi (fun y ↦ h y / y) (p := -1) (by simp)
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro y hy
      have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
      simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
        RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
      ring_nf
      simp [field]
    unfold MellinConvolution
    calc
      _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
      _ = _ := ?_
    · rw [← hMul (fun y ↦ f y * g (x / y)) xpos]
      simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
    · convert (hInv fun y ↦ f (y * x) * g (1 / y)).symm using 3
      rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
  have hDiv (h : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
      ∫ y in Ioi 0, h (a / y) / y = ∫ y in Ioi 0, h y / y := by
    simpa only [MellinConvolution, one_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] using
      (hSym (𝕂 := ℝ) (fun _ : ℝ ↦ (1 : ℝ)) h ha)
  have hPow (h : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
      ∫ y in Ioi 0, |p| * h (y ^ p) / y = ∫ y in Ioi 0, h y / y := by
    rw [← integral_comp_rpow_Ioi (fun y ↦ h y / y) hp,
      setIntegral_congr_fun (by simp)]
    intro y hy
    have ypos : 0 < y := mem_Ioi.mp hy
    simp only [rpow_sub_one ypos.ne', smul_eq_mul]
    field_simp
  have hMass : ∫ y in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ y in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ y in Ioi 0, ν y / y := ?_
      _ = 1 := mass_one
    · have hh := hDiv (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
      convert! hh.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have hh := hPow (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
      rw [← hh, abs_of_pos <| one_div_pos.mpr εpos]
      field_simp
  unfold Smooth1 MellinConvolution DeltaSpike
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := hMass
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one hMass) (by simp) ?_
    · refine integrable_of_integral_eq_one hMass |>.bdd_mul ?_
        (ae_of_all _ <| by aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
          indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul]
      intro y hy
      by_cases h : y ≤ 1
      · aesop
      field_simp
      simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
      simp only [mem_Ioi] at hy
      apply div_nonneg
      · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · positivity

theorem Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  unfold Smooth1 MellinConvolution DeltaSpike
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y hy
    have ypos : 0 < y := mem_Ioi.mp hy
    have hν : 0 ≤ ν ((x / y) ^ (1 / ε)) :=
      νnonneg _ (rpow_pos_of_pos (div_pos xpos ypos) _)
    by_cases h : y ≤ 1
    · simpa [ypos, h] using (div_nonneg (div_nonneg hν εpos.le) ypos.le)
    · simp [ypos, h]

theorem Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

theorem joint_zeta_rectangle : ∃ σ₂ σ₁ : ℝ,
    σ₂ ∈ Ioo 0 1 ∧ σ₁ ∈ Ioo σ₂ 1 ∧ LogDerivZetaIsHoloSmall σ₂ ∧
    HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2 ×ℂ Icc (-4) 4) \ {1}) := by
  obtain ⟨a, ha, hzero⟩ := ZetaNoZerosInBox 4
  let σ₂ : ℝ := max a (1 / 2)
  have hσ₂pos : 0 < σ₂ := by dsimp [σ₂]; bound
  have hσ₂lt : σ₂ < 1 := by dsimp [σ₂]; exact max_lt ha (by norm_num)
  let σ₁ : ℝ := (σ₂ + 1) / 2
  have horder : σ₂ < σ₁ := by dsimp [σ₁]; linarith
  have hσ₁lt : σ₁ < 1 := by dsimp [σ₁]; linarith
  have hb : HolomorphicOn (fun s => ζ' s / ζ s)
      ((Icc σ₂ 2 ×ℂ Icc (-4) 4) \ {1}) := by
    apply LogDerivZetaHoloOn (by simp)
    intro s hs
    have hmem := mem_reProdIm.mp hs.1
    have hz := hzero s.im (abs_le.mpr hmem.2) s.re
      (le_trans (le_max_left a (1 / 2)) hmem.1.1)
    simpa only [Complex.re_add_im] using hz
  refine ⟨σ₂, σ₁, ⟨hσ₂pos, hσ₂lt⟩, ⟨horder, hσ₁lt⟩, ?_, ?_⟩
  · change HolomorphicOn (fun s => ζ' s / ζ s)
      ((uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1})
    rw [uIcc_of_le (by linarith), uIcc_of_le (by norm_num)]
    apply hb.mono
    intro s hs
    have hh := mem_reProdIm.mp hs.1
    refine ⟨mem_reProdIm.mpr ⟨hh.1, ?_⟩, hs.2⟩
    constructor <;> linarith [hh.2.1, hh.2.2]
  · apply hb.mono
    intro s hs
    have hh := mem_reProdIm.mp hs.1
    refine ⟨mem_reProdIm.mpr ⟨⟨?_, hh.1.2⟩, hh.2⟩, hs.2⟩
    exact le_trans horder.le hh.1.1

theorem smoothed_integrand_holo {ν : ℝ → ℝ}
    (hd : ContDiff ℝ 1 ν) (hn : ∀ x > 0, 0 ≤ ν x)
    (hs : ν.support ⊆ Icc (1 / 2) 2) (hm : ∫ x in Ioi 0, ν x / x = 1)
    {σ₂ : ℝ} (hσ₂ : σ₂ ∈ Ioo 0 1) (hholo : LogDerivZetaIsHoloSmall σ₂) :
    HolomorphicOn (SmoothedChebyshevIntegrand ν (1 / 2) 4)
      ((Icc σ₂ 2 ×ℂ Icc (-3) 3) \ {1}) := by
  have holo2 := hholo
  change HolomorphicOn (fun s => ζ' s / ζ s)
    ((uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1}) at holo2
  rw [uIcc_of_le (by linarith [hσ₂.2]), uIcc_of_le (by norm_num)] at holo2
  apply DifferentiableOn.mul
  · apply DifferentiableOn.mul
    · rw [(by ext; ring : (fun s => -ζ' s / ζ s) = (fun s => -(ζ' s / ζ s)))]
      exact DifferentiableOn.neg holo2
    · intro s hmem
      apply DifferentiableAt.differentiableWithinAt
      apply Smooth1MellinDifferentiable hd hs (by constructor <;> norm_num) hn hm
      linarith [mem_reProdIm.mp hmem.1 |>.1.1, hσ₂.1]
  · intro s hmem
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_cpow (by fun_prop)
    left
    norm_num

namespace ContourBound

abbrev signature : Signature where
  Params := Σ _ : (ℝ → ℝ), Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p C₅ => ‖I₁ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.1‖ + ‖I₂ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ +
        ‖I₃ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ + ‖I₄ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.2 p.2.1‖ +
        C₅ * p.2.2.1 ^ p.2.1 / p.2.2.2.1 + ‖I₆ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.2 p.2.1‖ +
        ‖I₇ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ + ‖I₈ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ +
        ‖I₉ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.1‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    {σ₂ : ℝ} (holoSmall : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1),
    ∃ C₅ > 0, ∀ (X ε T σ₁ : ℝ), 3 < X → 0 < ε → ε < 1 → 3 < T →
      0 < σ₁ → σ₁ < 1 → σ₂ < σ₁ →
      HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2 ×ℂ Icc (-T) T) \ {1}) →
      HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
        (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) →
      ‖SmoothedChebyshev SmoothingF ε X -
          𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X‖ ≤
        r.readout () ⟨SmoothingF, σ₂, X, ε, T, σ₁⟩ C₅

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, hd, hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨σ₂, σ₁, hσ₂, hσ₁, hholo, hlarge⟩ := joint_zeta_rectangle
  obtain ⟨C₅, _hC₅, hh⟩ := h hs hd hn hm hholo hσ₂
  have hi := smoothed_integrand_holo hd hn hs hm hσ₂ hholo
  have hb := hh 4 (1 / 2) 4 σ₁ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith [hσ₂.1, hσ₁.1]) hσ₁.2 hσ₁.1 hlarge hi
  change ‖SmoothedChebyshev ν (1 / 2) 4 -
    mellin (fun x => (_root_.Smooth1 ν (1 / 2) x : ℂ)) 1 * 4‖ ≤ (-1 : ℝ) at hb
  exact (not_le_of_gt (by linarith [norm_nonneg (SmoothedChebyshev ν (1 / 2) 4 - mellin (fun x => (_root_.Smooth1 ν (1 / 2) x : ℂ)) 1 * 4)])) hb

def registration : Registration arena
    (∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    {σ₂ : ℝ} (holoSmall : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1),
    ∃ C₅ > 0, ∀ (X ε T σ₁ : ℝ), 3 < X → 0 < ε → ε < 1 → 3 < T →
      0 < σ₁ → σ₁ < 1 → σ₂ < σ₁ →
      HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2 ×ℂ Icc (-T) T) \ {1}) →
      HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
        (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) →
      ‖SmoothedChebyshev SmoothingF ε X -
          𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X‖ ≤
        ‖I₁ SmoothingF ε X T‖ + ‖I₂ SmoothingF ε T X σ₁‖ +
        ‖I₃ SmoothingF ε T X σ₁‖ + ‖I₄ SmoothingF ε X σ₁ σ₂‖ +
        C₅ * X ^ σ₂ / ε + ‖I₆ SmoothingF ε X σ₁ σ₂‖ +
        ‖I₇ SmoothingF ε T X σ₁‖ + ‖I₈ SmoothingF ε T X σ₁‖ +
        ‖I₉ SmoothingF ε X T‖) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.SmoothedChebyshevContourBound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(fun _ => 0), (1 : ℝ), (1 : ℝ), (1 : ℝ), (4 : ℝ), (1 : ℝ)⟩,
      (0 : ℝ), (1 : ℝ), ?_⟩
    change (‖I₁ (fun _ => 0) (1 : ℝ) (1 : ℝ) (4 : ℝ)‖ + ‖I₂ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        ‖I₃ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ + ‖I₄ (fun _ => 0) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        (0 : ℝ) * (1 : ℝ) ^ (1 : ℝ) / (1 : ℝ) + ‖I₆ (fun _ => 0) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        ‖I₇ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ + ‖I₈ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        ‖I₉ (fun _ => 0) (1 : ℝ) (1 : ℝ) (4 : ℝ)‖) ≠ (‖I₁ (fun _ => 0) (1 : ℝ) (1 : ℝ) (4 : ℝ)‖ + ‖I₂ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        ‖I₃ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ + ‖I₄ (fun _ => 0) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        (1 : ℝ) * (1 : ℝ) ^ (1 : ℝ) / (1 : ℝ) + ‖I₆ (fun _ => 0) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        ‖I₇ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ + ‖I₈ (fun _ => 0) (1 : ℝ) (4 : ℝ) (1 : ℝ) (1 : ℝ)‖ +
        ‖I₉ (fun _ => 0) (1 : ℝ) (1 : ℝ) (4 : ℝ)‖)
    simp only [zero_mul, one_mul, Real.one_rpow, div_one]
    intro h
    linarith

register_information_theorem _root_.SmoothedChebyshevContourBound in arena
  readout via (realize signature (fun _ p C₅ => ‖I₁ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.1‖ + ‖I₂ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ +
        ‖I₃ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ + ‖I₄ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.2 p.2.1‖ +
        C₅ * p.2.2.1 ^ p.2.1 / p.2.2.2.1 + ‖I₆ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.2 p.2.1‖ +
        ‖I₇ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ + ‖I₈ p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2‖ +
        ‖I₉ p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.1‖) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.PntContourBound
    coordinates := #[0, 5, 9, 10, 11, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"] }] })
  escape continues (open)

end ContourBound
end
end Reg.D5.S3.Weil.PrimeNumberTheorem.PntContourBound
