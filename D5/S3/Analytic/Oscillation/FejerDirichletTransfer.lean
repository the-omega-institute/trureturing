/- GID: D5/S3/Analytic/Oscillation/FejerDirichletTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/FejerDirichletTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fejer localization and simultaneous phase alignment force logarithmic oscillation. -/

import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
import D5.S3.Arith.DiophantineApproximation.SimultaneousPhaseAlignment

/-! Logarithmic oscillation from paired Laplace poles with logarithmic counting growth. -/

namespace D5.S3.Analytic.Oscillation.FejerDirichletTransfer

open D5.S3.Analytic.Fourier.AngularFejerKernel
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Laplace.PairedPoleRegularity
open D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
open D5.S3.Arith.DiophantineApproximation.SimultaneousPhaseAlignment
open Set Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

def OmegaPMLog (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧ 1 < y ∧ f y ≤ -c * Real.log y) ∧
    (∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧ 1 < y ∧ c * Real.log y ≤ f y)

private lemma phi_nonneg (b t : ℝ) : 0 ≤ phi b t := le_max_left _ _

private lemma cut_card_le (S : Spectrum) (M : ℝ) : (S.cut M).card ≤ S.N M := by
  classical
  rw [Spectrum.N, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun j _ => S.mult_pos j)

private lemma window_card_le (S : Spectrum) (b U : ℝ) :
    ((S.cut (U + b)).filter (fun j => |S.gamma j - U| < b)).card ≤ windowMass S b U := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, windowMass]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact S.mult_pos j
  · exact le_rfl

private lemma align_finset {ι : Type*} (s : Finset ι) (lambda : ι → ℝ)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ y : ℝ, L ≤ y ∧ y ≤ L * (8 : ℝ) ^ s.card ∧
      Real.log y ≤ Real.log L + (s.card : ℝ) * Real.log 8 ∧
      ∀ j ∈ s, Real.cos (Real.pi / 4) ≤ Real.cos (lambda j * y) := by
  classical
  let e := s.equivFin
  obtain ⟨y, hly, hyl, hc⟩ := simultaneous_cos_alignment
    (fun n => lambda (e.symm n)) hL
  refine ⟨y, hly, hyl, ?_, ?_⟩
  · have hy : 0 < y := by linarith
    have hL0 : L ≠ 0 := by linarith
    have hpow : (8 : ℝ) ^ s.card ≠ 0 := by positivity
    calc
      Real.log y ≤ Real.log (L * (8 : ℝ) ^ s.card) := Real.log_le_log hy hyl
      _ = Real.log L + (s.card : ℝ) * Real.log 8 := by
        rw [Real.log_mul hL0 hpow, Real.log_pow]
  · intro j hj
    simpa only [Equiv.symm_apply_apply] using hc (e ⟨j, hj⟩)

private lemma negative_spectral (S : Spectrum) {M y : ℝ} (hM : 0 < M)
    (ha : ∀ j ∈ S.cut M,
      Real.cos (Real.pi / 4) ≤ Real.cos (S.gamma j * y)) :
    Real.cos (Real.pi / 4) * Wminus S M ≤
      ∑ j ∈ S.cut (2 * M), (S.mult j : ℝ) * phi M (S.gamma j) *
        Real.cos (S.gamma j * y) := by
  classical
  have hsub : S.cut M ⊆ S.cut (2 * M) := by
    intro j hj
    have hj' : S.gamma j ≤ M := by simpa [Spectrum.cut] using hj
    simpa [Spectrum.cut] using (show S.gamma j ≤ 2 * M by linarith)
  have heq := Finset.sum_subset hsub (f := fun j =>
    (S.mult j : ℝ) * phi M (S.gamma j) * Real.cos (S.gamma j * y))
    (fun j _ hj => by
      have hj' : ¬ S.gamma j ≤ M := by simpa [Spectrum.cut] using hj
      rw [phi_eq_zero hM (by rw [abs_of_pos (S.gamma_pos j)]; linarith), mul_zero, zero_mul])
  rw [← heq, Wminus, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ = ((S.mult j : ℝ) * phi M (S.gamma j)) * Real.cos (Real.pi / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ha j hj)
      (mul_nonneg (Nat.cast_nonneg _) (phi_nonneg _ _))

private lemma positive_spectral (S : Spectrum) {b U y : ℝ}
    (hb : 0 < b) (hU : 2 * b < U) (hgap : ∀ j, b < S.gamma j)
    (ha : ∀ j ∈ (S.cut (U + b)).filter (fun j => |S.gamma j - U| < b),
      Real.cos (Real.pi / 4) ≤ Real.cos (S.gamma j * y)) :
    Real.cos (Real.pi / 4) / 2 * Wplus S b U ≤
      -(∑ j ∈ S.cut (2 * (U + b)), (S.mult j : ℝ) * psi b U (S.gamma j) *
        Real.cos (S.gamma j * y)) := by
  classical
  have hU0 : 0 < U := by linarith
  have hpsi (j : S.index) : psi b U (S.gamma j) = -phi b (S.gamma j - U) / 2 := by
    have hcentral : phi b (S.gamma j) = 0 :=
      phi_eq_zero hb (by rw [abs_of_pos (S.gamma_pos j)]; exact (hgap j).le)
    have hfar : phi b (S.gamma j + U) = 0 :=
      phi_eq_zero hb (by rw [abs_of_pos (by linarith [S.gamma_pos j])]; linarith [hgap j])
    rw [psi, hcentral, hfar]
    ring
  have hsub : S.cut (U + b) ⊆ S.cut (2 * (U + b)) := by
    intro j hj
    have hj' : S.gamma j ≤ U + b := by simpa [Spectrum.cut] using hj
    simpa [Spectrum.cut] using (show S.gamma j ≤ 2 * (U + b) by linarith)
  have heq := Finset.sum_subset hsub (f := fun j =>
    (S.mult j : ℝ) * phi b (S.gamma j - U) * Real.cos (S.gamma j * y))
    (fun j _ hj => by
      have hj' : ¬ S.gamma j ≤ U + b := by simpa [Spectrum.cut] using hj
      rw [phi_eq_zero hb (by exact (show b ≤ S.gamma j - U by linarith).trans (le_abs_self _)),
        mul_zero, zero_mul])
  have hmain : -(∑ j ∈ S.cut (2 * (U + b)), (S.mult j : ℝ) * psi b U (S.gamma j) *
      Real.cos (S.gamma j * y)) =
      (1 / 2 : ℝ) * ∑ j ∈ S.cut (U + b),
        (S.mult j : ℝ) * phi b (S.gamma j - U) * Real.cos (S.gamma j * y) := by
    simp_rw [hpsi]
    rw [heq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hmain, Wplus, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjwin : |S.gamma j - U| < b
  · have hc := mul_le_mul_of_nonneg_left
      (ha j (Finset.mem_filter.mpr ⟨hj, hjwin⟩))
      (mul_nonneg (Nat.cast_nonneg (S.mult j)) (phi_nonneg b (S.gamma j - U)))
    nlinarith
  · rw [phi_eq_zero hb (le_of_not_gt hjwin)]
    simp

private lemma count_upper (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ M : ℝ in atTop,
      (S.N M : ℝ) ≤ B * (M * Real.log M) := by
  let B : ℝ := 1 / (2 * Real.pi) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hN.eventually (gt_mem_nhds (by change 1 / (2 * Real.pi) < 1 / (2 * Real.pi) + 1; linarith)),
    eventually_gt_atTop (1 : ℝ)] with M hM hM1
  exact (div_le_iff₀ (mul_pos (by linarith) (Real.log_pos hM1))).mp hM.le

private lemma lower_mass_eventually (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ M : ℝ in atTop,
      a * (M * Real.log M) ≤ Wminus S M := by
  let a : ℝ := 1 / (8 * Real.pi)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, ha, ?_⟩
  filter_upwards [(lower_triangular_mass S hN).eventually
    (lt_mem_nhds (by
      change 1 / (8 * Real.pi) < 1 / (4 * Real.pi)
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith [Real.pi_pos])),
    eventually_gt_atTop (1 : ℝ)] with M hM hM1
  exact (le_div_iff₀ (mul_pos (by linarith) (Real.log_pos hM1))).mp hM.le

private lemma mass_tendsto (S : Spectrum) (hN : CountAsymptotic S) :
    Tendsto (Wminus S) atTop atTop := by
  obtain ⟨a, ha, hmass⟩ := lower_mass_eventually S hN
  have hml : Tendsto (fun M : ℝ => M * Real.log M) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  exact tendsto_atTop_mono' atTop hmass (hml.const_mul_atTop ha)

private lemma ell_le_log {y : ℝ} (hy : 1 ≤ y) :
    ell y ≤ Real.log y + Real.log (Real.exp 1 + 1) := by
  unfold ell
  rw [← Real.log_mul (by linarith : y ≠ 0) (by positivity : Real.exp 1 + 1 ≠ 0)]
  apply Real.log_le_log (by positivity)
  nlinarith [Real.exp_pos 1]

private lemma negative_growth (S : Spectrum) (hN : CountAsymptotic S) (p : ℕ) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ᶠ M : ℝ in atTop,
      ∀ (d : ℕ) (y : ℝ), (d : ℝ) ≤ (S.N M : ℝ) → 1 ≤ y →
      Real.log y ≤ (p + 3 : ℕ) * Real.log M + (d : ℝ) * Real.log 8 →
      ell y ≤ C1 * Wminus S M := by
  obtain ⟨B, hB, hcount⟩ := count_upper S hN
  obtain ⟨a, ha, hmass⟩ := lower_mass_eventually S hN
  let E : ℝ := Real.log (Real.exp 1 + 1)
  have hE : 0 < E := Real.log_pos (by linarith [Real.exp_pos 1])
  let F : ℝ := (p + 3 : ℕ) + B * Real.log 8 + E
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F / a, div_pos hF ha, ?_⟩
  filter_upwards [hcount, hmass,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with M hc hm hl hM
  intro d y hd hy hlog
  have hml : 1 ≤ M * Real.log M := one_le_mul_of_one_le_of_one_le hM hl
  have hlogM : Real.log M ≤ M * Real.log M := le_mul_of_one_le_left (by linarith) hM
  have hd' : (d : ℝ) * Real.log 8 ≤ B * (M * Real.log M) * Real.log 8 :=
    mul_le_mul_of_nonneg_right (hd.trans hc) (by positivity)
  have hmain : ell y ≤ F * (M * Real.log M) := by
    have h1 := mul_le_mul_of_nonneg_left hlogM (Nat.cast_nonneg (p + 3) : (0 : ℝ) ≤ _)
    have h2 := mul_le_mul_of_nonneg_left hml hE.le
    have he := ell_le_log hy
    dsimp only [F, E] at *
    nlinarith
  calc
    ell y ≤ F * (M * Real.log M) := hmain
    _ = (F / a) * (a * (M * Real.log M)) := by field_simp
    _ ≤ (F / a) * Wminus S M := mul_le_mul_of_nonneg_left hm (div_pos hF ha).le

private lemma count_square_upper (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ M : ℝ in atTop, (S.N (2 * M) : ℝ) ≤ B * M ^ 2 := by
  obtain ⟨C, hC, hc⟩ := count_upper S hN
  refine ⟨4 * C, by positivity, ?_⟩
  have h2 : Tendsto (fun M : ℝ => 2 * M) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [h2.eventually hc, eventually_ge_atTop (1 : ℝ)] with M hc hM
  have hl := Real.log_le_self (show 0 ≤ 2 * M by linarith)
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ C * (2 * M) by positivity)
  nlinarith

private lemma error_eventually (S : Spectrum) (hN : CountAsymptotic S)
    (p : ℕ) (hp : 1 ≤ p) (A b0 : ℝ) (hA : 0 ≤ A) (hb0 : 0 < b0) :
    ∀ᶠ M : ℝ in atTop, ∀ b y : ℝ, b0 ≤ b → b ≤ M → M ^ (p + 3) ≤ y →
      A * ((1 + b) * M ^ p / y + (S.N (2 * M) : ℝ) / (b * y)) ≤ 1 := by
  obtain ⟨B, hB, hcount⟩ := count_square_upper S hN
  have hz : Tendsto (fun M : ℝ => A * (2 + B / b0) / M ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))).const_mul
        (A * (2 + B / b0))
  filter_upwards [hcount, hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)] with M hc hsmall hM
  intro b y hb hbM hy
  have hM0 : 0 < M := by linarith
  have hb' : 0 < b := hb0.trans_le hb
  have hpM : 0 < M ^ p := pow_pos hM0 _
  have hy0 : 0 < y := (pow_pos hM0 _).trans_le hy
  have hpow : M ^ (p + 3) = M ^ p * M ^ 3 := pow_add _ _ _
  have hreg : (1 + b) * M ^ p / y ≤ 2 / M ^ 2 := by
    apply (div_le_div_iff₀ hy0 (sq_pos_of_pos hM0)).mpr
    have h1 : 1 + b ≤ 2 * M := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hpM.le (sq_nonneg M))
    rw [hpow] at hy
    nlinarith [hy]
  have hMpow : M ^ 4 ≤ M ^ (p + 3) := pow_le_pow_right₀ hM (by omega)
  have htail : (S.N (2 * M) : ℝ) / (b * y) ≤ (B / b0) / M ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos hb' hy0) (sq_pos_of_pos hM0)).mpr
    have hby : b0 * M ^ 4 ≤ b * y := by
      exact mul_le_mul hb (hMpow.trans hy) (by positivity) hb'.le
    have hbB : 0 ≤ B / b0 := (div_pos hB hb0).le
    have hh := mul_le_mul_of_nonneg_left hby hbB
    have heq : B / b0 * (b0 * M ^ 4) = B * M ^ 4 := by field_simp
    rw [heq] at hh
    have hn := mul_le_mul_of_nonneg_right hc (sq_nonneg M)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (add_le_add hreg htail) hA
  calc
    _ ≤ A * (2 / M ^ 2 + (B / b0) / M ^ 2) := hh
    _ = A * (2 + B / b0) / M ^ 2 := by ring
    _ ≤ 1 := hsmall.le

private lemma positive_growth (p : ℕ) (b cb : ℝ) (hb : 0 < b) (hcb : 0 < cb) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (U W : ℝ) (d : ℕ) (y : ℝ), U ∈ Icc T (2 * T) →
      cb * Real.log T ≤ W → (d : ℝ) ≤ 12 * W → 1 ≤ y →
      Real.log y ≤ (p + 3 : ℕ) * Real.log (U + b) + (d : ℝ) * Real.log 8 →
      ell y ≤ C2 * W := by
  let E : ℝ := Real.log (Real.exp 1 + 1)
  let F : ℝ := (p + 3 : ℕ) * (Real.log (2 + b) + 1) + E
  have hE : 0 < E := Real.log_pos (by linarith [Real.exp_pos 1])
  have hlogb : 0 < Real.log (2 + b) := Real.log_pos (by linarith)
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F / cb + 12 * Real.log 8, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hlogT
  intro U W d y hU hW hd hy hlog
  have hTb : U + b ≤ (2 + b) * T := by
    have hh := mul_le_mul_of_nonneg_left hT hb.le
    nlinarith [hU.2]
  have hM : 0 < U + b := by linarith [hU.1]
  have hlM : Real.log (U + b) ≤ Real.log (2 + b) + Real.log T := by
    rw [← Real.log_mul (by linarith : 2 + b ≠ 0) (by linarith : T ≠ 0)]
    exact Real.log_le_log hM hTb
  have hdim := mul_le_mul_of_nonneg_right hd (show 0 ≤ Real.log 8 by positivity)
  have hreg := mul_le_mul_of_nonneg_left hlM (Nat.cast_nonneg (p + 3) : (0 : ℝ) ≤ _)
  have hconst := mul_le_mul_of_nonneg_left hlogT
    (show 0 ≤ (p + 3 : ℕ) * Real.log (2 + b) + E by positivity)
  have hmain : ell y ≤ F * Real.log T + 12 * Real.log 8 * W := by
    have he := ell_le_log hy
    dsimp only [F, E] at *
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hW (div_pos hF hcb).le
  have heq : F / cb * (cb * Real.log T) = F * Real.log T := by field_simp
  rw [heq] at hscale
  calc
    ell y ≤ F * Real.log T + 12 * Real.log 8 * W := hmain
    _ ≤ (F / cb) * W + 12 * Real.log 8 * W := add_le_add hscale le_rfl
    _ = _ := by ring

private lemma log_le_ell {u : ℝ} (hu : 0 < u) : Real.log u ≤ ell u := by
  exact Real.log_le_log hu (by linarith [Real.exp_pos (1 : ℝ)])

private lemma envelope_of_eventual (S : Spectrum) {f : ℝ → ℝ} {k : ℕ}
    (D : PairedLaplaceData S f k) {e κ : ℝ} (he : |e| = 1) (hκ : 0 ≤ κ)
    {Y : ℝ} (hY : ∀ y : ℝ, Y ≤ y → 1 < y → e * f y < κ * Real.log y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → e * f u ≤ κ * ell u + C := by
  obtain ⟨B, hB, hbound⟩ := D.local_bound (max Y 2) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro u hu
  by_cases hsmall : u ≤ max Y 2
  · have hef : e * f u ≤ B := by
      calc
        e * f u ≤ |e * f u| := le_abs_self _
        _ = |f u| := by rw [abs_mul, he, one_mul]
        _ ≤ B := hbound u ⟨hu, hsmall⟩
    linarith [mul_nonneg hκ (log_ell_nonneg hu)]
  · have hlarge : max Y 2 < u := lt_of_not_ge hsmall
    have hh := hY u ((le_max_left _ _).trans hlarge.le)
      (by have := le_max_right Y 2; linarith)
    have hu0 : 0 < u := by have := le_max_right Y (2 : ℝ); linarith
    have hl := mul_le_mul_of_nonneg_left (log_le_ell hu0) hκ
    linarith

private lemma excursions_of_no_envelope (S : Spectrum) {f : ℝ → ℝ} {k : ℕ}
    (D : PairedLaplaceData S f k) {e κ : ℝ} (he : |e| = 1) (hκ : 0 < κ)
    (hno : ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → e * f u ≤ κ * ell u + C) :
    ∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧ 1 < y ∧ κ * Real.log y ≤ e * f y := by
  intro Y
  by_contra h
  push Not at h
  exact hno (envelope_of_eventual S D he hκ.le h)

private lemma average_bound {f g : ℝ → ℝ} {e κ C C₀ y : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (henv : ∀ u : ℝ, 0 ≤ u → e * f u ≤ κ * ell u + C)
    (hg : Integrable g) (hgn : ∀ v, 0 ≤ g v) (hgm : (∫ v, g v) = 1)
    (hfi : IntegrableOn (fun u => f u * g (y - u)) (Ici 0))
    (hli : IntegrableOn (fun u => g (y - u) * ell u) (Ici 0))
    (hl : (∫ u in Ici 0, g (y - u) * ell u) ≤ ell y + C₀) :
    e * (∫ u in Ici 0, f u * g (y - u)) ≤ κ * (ell y + C₀) + C := by
  have hgy := hg.comp_sub_left y
  have hmass : (∫ u in Ici 0, g (y - u)) ≤ 1 := by
    calc
      _ ≤ ∫ u, g (y - u) :=
        setIntegral_le_integral hgy (ae_of_all _ fun u => hgn _)
      _ = 1 := by rw [integral_sub_left_eq_self g volume y, hgm]
  calc
    e * (∫ u in Ici 0, f u * g (y - u)) =
        ∫ u in Ici 0, e * (f u * g (y - u)) := (integral_const_mul _ _).symm
    _ ≤ ∫ u in Ici 0, κ * (g (y - u) * ell u) + C * g (y - u) := by
      apply integral_mono_ae (hfi.const_mul e) ((hli.const_mul κ).add (hgy.integrableOn.const_mul C))
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      have := mul_le_mul_of_nonneg_right (henv u hu) (hgn (y - u))
      dsimp only [Pi.add_apply]
      convert this using 1 <;> ring
    _ = κ * (∫ u in Ici 0, g (y - u) * ell u) +
        C * (∫ u in Ici 0, g (y - u)) := by
      rw [integral_add (hli.const_mul κ) (hgy.integrableOn.const_mul C),
        integral_const_mul, integral_const_mul]
    _ ≤ κ * (ell y + C₀) + C := by
      have h1 := mul_le_mul_of_nonneg_left hl hκ
      have h2 := mul_le_mul_of_nonneg_left hmass hC
      linarith

private lemma cosine_quarter_pos : 0 < Real.cos (Real.pi / 4) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private lemma negative_excursions (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Y : ℝ, ∃ y : ℝ,
      Y ≤ y ∧ 1 < y ∧ f y ≤ -κ * Real.log y := by
  classical
  let p := max k 1
  let q := Real.cos (Real.pi / 4)
  have hq : 0 < q := cosine_quarter_pos
  obtain ⟨C1, hC1, hgrowth⟩ := negative_growth S hN p
  obtain ⟨C₀, hC₀, havg⟩ := fejer_log_average
  let κ := q / (4 * C1)
  have hκ : 0 < κ := div_pos hq (by positivity)
  have hκC1 : κ * C1 = q / 4 := by dsimp [κ]; field_simp
  refine ⟨κ, hκ, ?_⟩
  have hno : ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, 0 ≤ u → (-1 : ℝ) * f u ≤ κ * ell u + C := by
    rintro ⟨C, hC, henv⟩
    have hbound : HasLogEnvelope f := ⟨-1, κ, C, by norm_num, hκ.le, hC, henv⟩
    obtain ⟨A, hA, hboundary⟩ := quantitative_boundary_formula S hN D
    have herr := error_eventually S hN p (le_max_right _ _) A 1 hA.le zero_lt_one
    have hlarge : ∀ᶠ M : ℝ in atTop,
        κ * C₀ + C + 2 < (q / 2) * Wminus S M :=
      ((mass_tendsto S hN).const_mul_atTop (by positivity : 0 < q / 2)).eventually
        (eventually_gt_atTop _)
    obtain ⟨M, hg, he, hw, hM⟩ :=
      (hgrowth.and (herr.and (hlarge.and (eventually_ge_atTop (4 : ℝ))))).exists
    have hM0 : 0 < M := by linarith
    have hM1 : 1 ≤ M := by linarith
    have hL : 1 ≤ M ^ (p + 3) := one_le_pow₀ hM1
    obtain ⟨y, hLy, _, hlog, halign⟩ := align_finset (S.cut M) S.gamma hL
    have hy : 1 ≤ y := hL.trans hLy
    have hlog' : Real.log y ≤ (p + 3 : ℕ) * Real.log M +
        ((S.cut M).card : ℝ) * Real.log 8 := by
      simpa only [Real.log_pow] using hlog
    have hell := hg (S.cut M).card y (by exact_mod_cast cut_card_le S M) hy hlog'
    obtain ⟨hfi, hform⟩ := hboundary (K M) (phi M) M M y hM0 hM1 hy
      (Or.inl ⟨rfl, rfl, le_rfl⟩) hbound
    have he1 := he M y (by linarith) le_rfl hLy
    have hform1 : |(∫ u in Ici 0, f u * K M (y - u)) +
        ∑ j ∈ S.cut (2 * M), (S.mult j : ℝ) * phi M (S.gamma j) *
          Real.cos (S.gamma j * y)| ≤ 1 := hform.trans he1
    have hspec := negative_spectral S hM0 halign
    obtain ⟨hli, hl⟩ := havg M y hM1 hy
    obtain ⟨hgn, hgi, hgm, _, _⟩ := fejer_law hM0
    have ha := average_bound hκ.le hC henv hgi hgn hgm hfi hli hl
    have ha' : (-1 : ℝ) * (∫ u in Ici 0, f u * K M (y - u)) ≤
        κ * (C1 * Wminus S M + C₀) + C :=
      ha.trans (by nlinarith [mul_le_mul_of_nonneg_left hell hκ.le])
    have habs := (abs_le.mp hform1).2
    rw [mul_add, ← mul_assoc, hκC1] at ha'
    dsimp only [q] at hw ha'
    nlinarith
  intro Y
  obtain ⟨y, hY, hy, hh⟩ := excursions_of_no_envelope S D (e := -1) (by norm_num) hκ hno Y
  exact ⟨y, hY, hy, by nlinarith⟩

private lemma positive_excursions (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Y : ℝ, ∃ y : ℝ,
      Y ≤ y ∧ 1 < y ∧ κ * Real.log y ≤ f y := by
  classical
  let p := max k 1
  let q := Real.cos (Real.pi / 4)
  have hq : 0 < q := cosine_quarter_pos
  obtain ⟨b, hb, hgap⟩ := positive_gap S
  obtain ⟨cb, hcb, hband⟩ := select_upper_band S hN hb
  obtain ⟨C2, hC2, hgrowth⟩ := positive_growth p b cb hb hcb
  obtain ⟨C₀, hC₀, havg⟩ := notched_log_average hb
  let κ := q / (8 * C2)
  have hκ : 0 < κ := div_pos hq (by positivity)
  have hκC2 : κ * C2 = q / 8 := by dsimp [κ]; field_simp
  refine ⟨κ, hκ, ?_⟩
  have hno : ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, 0 ≤ u → (1 : ℝ) * f u ≤ κ * ell u + C := by
    rintro ⟨C, hC, henv⟩
    have hbound : HasLogEnvelope f := ⟨1, κ, C, by norm_num, hκ.le, hC, henv⟩
    obtain ⟨A, hA, hboundary⟩ := quantitative_boundary_formula S hN D
    have herr := error_eventually S hN p (le_max_right _ _) A b hA.le hb
    obtain ⟨R, hR⟩ := eventually_atTop.mp herr
    have hlarge : ∀ᶠ T : ℝ in atTop,
        κ * C₀ + C + 2 < (q / 4) * (cb * Real.log T) :=
      ((Real.tendsto_log_atTop.const_mul_atTop hcb).const_mul_atTop
        (by positivity : 0 < q / 4)).eventually (eventually_gt_atTop _)
    obtain ⟨T, hbandT, hg, hw, hT⟩ :=
      (hband.and (hgrowth.and (hlarge.and
        (eventually_ge_atTop (max R (max 4 (2 * b + 1))))))).exists
    obtain ⟨U, hU, hn, hmass⟩ := hbandT
    have hT4 : 4 ≤ T := (le_trans (le_max_left _ _) (le_max_right R _)).trans hT
    have hTb : 2 * b + 1 ≤ T :=
      (le_trans (le_max_right _ _) (le_max_right R _)).trans hT
    have hUT : 2 * b < U := by linarith [hU.1]
    have hM : 4 ≤ U + b := by linarith [hU.1]
    have hM1 : 1 ≤ U + b := by linarith
    have hL : 1 ≤ (U + b) ^ (p + 3) := one_le_pow₀ hM1
    let s := (S.cut (U + b)).filter (fun j => |S.gamma j - U| < b)
    obtain ⟨y, hLy, _, hlog, halign⟩ := align_finset s S.gamma hL
    have hy : 1 ≤ y := hL.trans hLy
    have hd : (s.card : ℝ) ≤ 12 * Wplus S b U :=
      (show (s.card : ℝ) ≤ (windowMass S b U : ℝ) from
        by exact_mod_cast window_card_le S b U).trans hn
    have hlog' : Real.log y ≤ (p + 3 : ℕ) * Real.log (U + b) +
        (s.card : ℝ) * Real.log 8 := by
      simpa only [Real.log_pow] using hlog
    have hell := hg U (Wplus S b U) s.card y hU hmass hd hy hlog'
    obtain ⟨hfi, hform⟩ := hboundary (H b U) (psi b U) b (U + b) y hb hM1 hy
      (Or.inr ⟨U, hUT, rfl, rfl, le_rfl⟩) hbound
    have hRM : R ≤ U + b := by have := (le_max_left R _).trans hT; linarith [hU.1]
    have he1 := hR (U + b) hRM b y le_rfl (by linarith [hU.1]) hLy
    have hform1 : |(∫ u in Ici 0, f u * H b U (y - u)) +
        ∑ j ∈ S.cut (2 * (U + b)), (S.mult j : ℝ) * psi b U (S.gamma j) *
          Real.cos (S.gamma j * y)| ≤ 1 := hform.trans he1
    have hspec := positive_spectral S hb hUT hgap halign
    obtain ⟨hli, hl⟩ := havg U y hUT hy
    obtain ⟨hgn, hgi, hgm, _, _⟩ := notched_fejer_law hb hUT
    have ha := average_bound hκ.le hC henv hgi (fun v => (hgn v).1) hgm hfi hli hl
    have ha' : (∫ u in Ici 0, f u * H b U (y - u)) ≤
        κ * (C2 * Wplus S b U + C₀) + C := by
      have hh := mul_le_mul_of_nonneg_left hell hκ.le
      simp only [one_mul] at ha
      nlinarith
    have hw' : κ * C₀ + C + 2 < q / 4 * Wplus S b U :=
      hw.trans_le (mul_le_mul_of_nonneg_left hmass (by positivity))
    have habs := (abs_le.mp hform1).1
    dsimp only [q] at hκC2 hw'
    nlinarith
  intro Y
  obtain ⟨y, hY, hy, hh⟩ := excursions_of_no_envelope S D (e := 1) (by norm_num) hκ hno Y
  exact ⟨y, hY, hy, by simpa using hh⟩

theorem quantitative_fejer_dirichlet_transfer (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) : OmegaPMLog f := by
  obtain ⟨cm, hcm, hm⟩ := negative_excursions S hN D
  obtain ⟨cp, hcp, hp⟩ := positive_excursions S hN D
  refine ⟨min cm cp, lt_min hcm hcp, ?_, ?_⟩
  · intro Y
    obtain ⟨y, hY, hy, hf⟩ := hm Y
    refine ⟨y, hY, hy, hf.trans ?_⟩
    have := mul_le_mul_of_nonneg_right (min_le_left cm cp) (Real.log_pos hy).le
    linarith
  · intro Y
    obtain ⟨y, hY, hy, hf⟩ := hp Y
    exact ⟨y, hY, hy, (mul_le_mul_of_nonneg_right (min_le_right cm cp)
      (Real.log_pos hy).le).trans hf⟩

end
end D5.S3.Analytic.Oscillation.FejerDirichletTransfer
