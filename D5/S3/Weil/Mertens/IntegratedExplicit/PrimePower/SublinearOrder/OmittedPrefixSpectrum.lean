/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedPrefixSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedPrefixSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A damped signed-prefix low-bin estimate for actual zero occurrences. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.DampedPrefixSampling
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.OmittedSpectrumCutoff

/-! Sum the signed prefix before bounding the low spectral bins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open Finset Set MeasureTheory
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (on_line)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open scoped ArithmeticFunction.Moebius

private theorem occurrence_count_and_square_bins {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : ℕ) (T : Finset ℕ) (c : ℕ → ℂ),
      (∀ i ∈ T, frequencyBin (occurrenceFrequency i) ∈ lowBins H) →
      (∀ i ∈ T, ‖c i‖ ≤ 1) →
      (T.card : ℝ) ≤ D * ((H : ℝ)+1)^(1+η) ∧
      ∃ b : ℤ → ℝ, (Summable fun k => b k^2) ∧
        (∀ k, binMass T occurrenceFrequency c k ≤ b k) ∧
        Real.sqrt (∑' k : ℤ, b k^2) ≤ D * ((H : ℝ)+1)^(1/2+η) := by
  classical
  obtain ⟨A, hA, hcount⟩ := occurrence_bin_card_majorant
  let L := A * (Real.log 3 + η⁻¹)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨2*L, by positivity, ?_⟩
  intro H T c hT hc
  let x := (H : ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) H]
  have hx₀ := zero_lt_one.trans_le hx
  let B := lowBins H
  let F := L*x^η
  let freq (i : ℕ) : ℤ := frequencyBin (occurrenceFrequency i)
  have hcount' (k : ℤ) (hk : k ∈ B) :
      ((T.filter fun i => freq i = k).card : ℝ) ≤ F := by
    have hK : |(k : ℝ)| ≤ H := by
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
      exact abs_le.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩
    have hlog : Real.log (|(k : ℝ)|+3) ≤ Real.log 3 + Real.log x := by
      rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx₀.ne']
      apply Real.log_le_log (by positivity)
      dsimp [x]
      linarith [Nat.cast_nonneg (α := ℝ) H]
    refine (hcount T k).trans (mul_le_mul_of_nonneg_left hlog hA.le) |>.trans ?_
    have h3 := mul_le_mul_of_nonneg_left (Real.one_le_rpow hx hη.le)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
    have hpow := Real.log_le_rpow_div hx₀.le hη
    dsimp only [F, L]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [add_mul, mul_comm η⁻¹, ← div_eq_mul_inv]
    exact add_le_add (by simpa using h3) hpow
  have hcard : (B.card : ℝ) ≤ 2*x := by
    have h : B.card ≤ 2*H+1 := by
      dsimp [B, lowBins]
      rw [Int.card_Icc]
      omega
    have h' : (B.card : ℝ) ≤ (2*H+1 : ℕ) := by exact_mod_cast h
    push_cast at h'
    dsimp [x]
    linarith
  have hTcard : (T.card : ℝ) ≤ 2*x*F := by
    calc
      _ = ∑ i ∈ T, (1 : ℝ) := by simp
      _ = ∑ k ∈ B, ∑ i ∈ T with freq i = k, (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (g := freq) hT _).symm
      _ ≤ ∑ _ ∈ B, F := Finset.sum_le_sum fun k hk => by
        simpa using hcount' k hk
      _ = (B.card : ℝ)*F := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  refine ⟨hTcard.trans_eq ?_, ?_⟩
  · dsimp only [F]
    rw [Real.rpow_add hx₀, Real.rpow_one]
    ring
  let b (k : ℤ) := if k ∈ B then F else 0
  have hz (k : ℤ) (hk : k ∉ B) : b k^2 = 0 := by simp [b, hk]
  refine ⟨b, summable_of_ne_finset_zero (s := B) hz, ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ B
    · simp only [b, ite_eq_left hk, binMass]
      refine (Finset.sum_le_sum fun i hi => hc i ((Finset.mem_filter.mp hi).1)).trans ?_
      simpa using hcount' k hk
    · have hempty : T.filter (fun i => freq i = k) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi he
        exact hk (he ▸ hT i hi)
      change (∑ i ∈ T.filter (fun i => freq i = k), ‖c i‖) ≤ b k
      simp [hempty, b, hk]
  · have hsum : (∑' k : ℤ, b k^2) = (B.card : ℝ)*F^2 := by
      rw [tsum_eq_sum (s := B) hz]
      rw [show (∑ k ∈ B, b k^2) = ∑ _ ∈ B, F^2 by
        exact Finset.sum_congr rfl fun k hk => by simp [b, hk]]
      simp [nsmul_eq_mul]
    rw [hsum, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ F)]
    have htwo : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ Real.sqrt (2*x)*F :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard) (by positivity)
      _ ≤ 2*Real.sqrt x*F := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg _)) (by positivity)
      _ = _ := by
        dsimp only [F]
        rw [Real.rpow_add hx₀, Real.sqrt_eq_rpow]
        ring

private theorem norm_filtered_degree_prefix {p m : ℕ} {v : ℕ → ℝ} {t A : ℝ}
    {a : ℕ → ℂ} (hv : AntitoneOn v (Set.Icc p m)) (hA : 0 ≤ A)
    (ha : ∀ k ≤ m + 1, ‖∑ n ∈ Finset.range k, a n‖ ≤ A) :
    ‖∑ n ∈ Finset.Icc p m, if t ≤ v n then a n else 0‖ ≤ 2*A := by
  rw [← Finset.sum_filter]
  let U := (Finset.Icc p m).filter (fun n => t ≤ v n)
  change ‖∑ n ∈ U, a n‖ ≤ _
  by_cases hU : U.Nonempty
  · let k := U.max' hU
    have hk : k ∈ U := U.max'_mem hU
    have hkm := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    have hpk := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have hkv := (Finset.mem_filter.mp hk).2
    have he : U = Finset.Icc p k := by
      ext n
      constructor
      · intro hn
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1, U.le_max' _ hn⟩
      · intro hn
        obtain ⟨hpn, hnk⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpn, hnk.trans hkm⟩,
          hkv.trans (hv ⟨hpn, hnk.trans hkm⟩ ⟨hpk, hkm⟩ hnk)⟩
    rw [he, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega : p ≤ k+1)]
    exact (norm_sub_le _ _).trans
      ((add_le_add (ha (k+1) (by omega)) (ha p (by omega))).trans_eq (by ring))
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simpa [he] using (show 0 ≤ 2*A by positivity)

private theorem rootCoeff_partial_fractions (hRH : RiemannHypothesis) {n : ℕ}
    (hn : 1 ≤ n) (i : ℕ) :
    rootCoeff n i = -(actualZero i)⁻¹ - ((n : ℂ)-actualZero i)⁻¹ := by
  have hρ : actualZero i ≠ 0 := norm_pos_iff.mp (occurrence_norm_pos hRH i)
  have hd : (n : ℂ)-actualZero i ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re, on_line hRH i] at hre
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold rootCoeff
  push_cast
  field_simp [hρ, hd]
  <;> ring

/-- Low frequencies can be summed after taking the signed degree prefix, with one
square-root loss in the number of frequency bins. -/
theorem signed_low_occurrence_sum_of_damped_prefix (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q p m H : ℕ), 3 ≤ q → 0 < p → p ≤ m → m ≤ q → q ≤ 2*p →
      ∀ u ≥ (0 : ℝ), ∀ (a : ℕ → ℂ) (A : ℝ), 0 ≤ A →
        (∀ n, ‖a n‖ ≤ 1) →
        (∀ k ≤ m + 1, ‖∑ n ∈ Finset.range k, a n‖ ≤ A) →
        ∀ T : Finset ℕ,
          ‖∑ n ∈ Finset.Icc p m, a n *
            ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
              normalizedMode q u n i‖ ≤
            C * (A*((H : ℝ)+1)^(1/2+η) + ((H : ℝ)+1)^(1+η)) := by
  obtain ⟨G, hG, hsample⟩ := exists_damped_reciprocal_sum_le_square_mass
  obtain ⟨D, hD, hcount⟩ := occurrence_count_and_square_bins hη
  refine ⟨2*G*D+3*D, by positivity, ?_⟩
  intro q p m H hq hp hpm hmq hhalf u hu a A hA han ha T
  let S := Finset.Icc p m
  let U := T.filter (fun i => frequencyBin (occurrenceFrequency i) ∈ lowBins H)
  let γ := occurrenceFrequency
  let w := 2*u/(q : ℝ)
  let v (n : ℕ) : ℝ := u/(n : ℝ)-w
  let c (i : ℕ) : ℂ := Complex.exp (Complex.I*(γ i : ℂ)*(w : ℂ))
  let weight (n i : ℕ) : ℂ := (Real.exp (v n/2) : ℂ) *
    Complex.exp (Complex.I*(γ i : ℂ)*((u/(n : ℝ) : ℝ) : ℂ))
  let L (n i : ℕ) : ℂ := -(c i * (Complex.exp (actualZero i * (v n : ℂ)) / actualZero i))
  let R (n i : ℕ) : ℂ := -(weight n i / ((n : ℂ)-actualZero i))
  let x := (H : ℝ)+1
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq₃ : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hpn (n : ℕ) (hn : n ∈ S) : (q : ℝ)/2 ≤ n := by
    have hqₙ : q ≤ 2*n := hhalf.trans (Nat.mul_le_mul_left _ (Finset.mem_Icc.mp hn).1)
    have h := (show (q : ℝ) ≤ 2*(n : ℝ) by exact_mod_cast hqₙ)
    linarith
  have hv (n : ℕ) (hn : n ∈ S) : v n ≤ 0 := by
    have h := div_le_div_of_nonneg_left hu (show (0 : ℝ) < (q : ℝ)/2 by positivity) (hpn n hn)
    have he : u / ((q : ℝ)/2) = w := by dsimp [w]; ring
    rw [he] at h
    exact sub_nonpos.mpr h
  have hva : AntitoneOn v (Set.Icc p m) := by
    intro n hn k hk hnk
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast hp.trans_le hn.1
    exact sub_le_sub_right (div_le_div_of_nonneg_left hu hn₀ (by exact_mod_cast hnk)) _
  have hc (i : ℕ) : ‖c i‖ = 1 := by
    simp [c, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hρ (i : ℕ) : actualZero i = 1/2 + Complex.I*(γ i : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, on_line hRH i]
    · simp [γ, occurrenceFrequency, Complex.add_im, Complex.mul_im]
  have hweight (n i : ℕ) : weight n i = c i * Complex.exp (actualZero i * (v n : ℂ)) := by
    dsimp only [weight, c]
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, hρ i]
    congr 1
    dsimp [v]
    push_cast
    ring
  have hsplit (n : ℕ) (hn : n ∈ S) (i : ℕ) : normalizedMode q u n i = L n i + R n i := by
    unfold normalizedMode
    rw [show -(2*u/(q : ℝ)-u/(n : ℝ))/2 = v n/2 by dsimp [v,w]; ring,
      rootCoeff_partial_fractions hRH (show 1 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega)]
    dsimp only [L, R]
    rw [← mul_div_assoc, ← hweight]
    dsimp only [weight]
    simp only [div_eq_mul_inv]
    ring
  obtain ⟨hcountU, b, hb, hbin, hsq⟩ :=
    hcount H U c (fun i hi => (Finset.mem_filter.mp hi).2) (fun i hi => (hc i).le)
  have hlead :
      ‖∑ n ∈ S, a n * ∑ i ∈ U, L n i‖ ≤ (2*G*D)*A*x^(1/2+η) := by
    have hpre (t : ℝ) (ht : t ≤ 0) :=
      norm_filtered_degree_prefix (t := t) hva hA ha
    have hs := hsample S U v γ a c (2*A) b (by positivity) hv hpre hb hbin
    have he :
        (∑ n ∈ S, a n * ∑ i ∈ U, L n i) =
          -(∑ i ∈ U, c i * ∑ n ∈ S, a n *
            (Complex.exp (actualZero i * (v n : ℂ)) / actualZero i)) := by
      simp only [Finset.mul_sum, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp only [L, mul_neg, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [he, norm_neg]
    simp_rw [hρ]
    refine hs.trans ?_
    exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_eq (by ring)
  have hrem (n : ℕ) (hn : n ∈ S) (i : ℕ) : ‖R n i‖ ≤ 3/(q : ℝ) := by
    have hreal : (q : ℝ)/3 ≤ ‖(n : ℂ)-actualZero i‖ := by
      have h := (le_abs_self (((n : ℂ)-actualZero i).re)).trans (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.natCast_re, on_line hRH i] at h
      linarith [hpn n hn]
    have hweight₁ : ‖weight n i‖ ≤ 1 := by
      dsimp only [weight]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
        Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub, Real.exp_zero, mul_one]
      exact Real.exp_le_one_iff.mpr (by linarith [hv n hn])
    dsimp only [R]
    rw [norm_neg, norm_div]
    refine (div_le_div_of_nonneg_right hweight₁ (norm_nonneg _)).trans ?_
    rw [show 3/(q : ℝ) = 1/((q : ℝ)/3) by ring]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) hreal
  have hcardS : (S.card : ℝ) ≤ q := by
    exact_mod_cast (show S.card ≤ q by dsimp [S]; rw [Nat.card_Icc]; omega)
  have htail : ‖∑ n ∈ S, a n * ∑ i ∈ U, R n i‖ ≤ (3*D)*x^(1+η) := by
    calc
      _ ≤ ∑ n ∈ S, (U.card : ℝ)*(3/(q : ℝ)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        refine (mul_le_of_le_one_left (norm_nonneg _) (han n)).trans ?_
        exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => hrem n hn i).trans_eq
          (by simp [nsmul_eq_mul]))
      _ = (S.card : ℝ)*((U.card : ℝ)*(3/(q : ℝ))) := by simp [nsmul_eq_mul]
      _ ≤ (q : ℝ)*((U.card : ℝ)*(3/(q : ℝ))) := mul_le_mul_of_nonneg_right hcardS (by positivity)
      _ = 3*(U.card : ℝ) := by field_simp [hq₀.ne']
      _ ≤ _ := (mul_le_mul_of_nonneg_left hcountU (by norm_num)).trans_eq (by ring)
  change ‖∑ n ∈ S, a n * ∑ i ∈ U, normalizedMode q u n i‖ ≤ _
  have he :
      (∑ n ∈ S, a n * ∑ i ∈ U, normalizedMode q u n i) =
        (∑ n ∈ S, a n * ∑ i ∈ U, L n i) + ∑ n ∈ S, a n * ∑ i ∈ U, R n i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [hsplit n hn, Finset.sum_add_distrib, mul_add]
  rw [he]
  refine (norm_add_le _ _).trans ((add_le_add hlead htail).trans ?_)
  have h₁ : (2*G*D)*A*x^(1/2+η) ≤ (2*G*D+3*D)*(A*x^(1/2+η)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ 3*D)) (by positivity)
  have h₂ : (3*D)*x^(1+η) ≤ (2*G*D+3*D)*x^(1+η) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity : 0 ≤ 2*G*D)) (by positivity)
  rw [mul_add]
  exact add_le_add h₁ h₂

/-- The damped prefix bound controls low bins, while square masses control their complement. -/
theorem signed_omitted_root_density_of_damped_prefix (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m H : ℕ, 2 ≤ m → 0 < H →
      ∀ u : ℝ, (m : ℝ)+1 ≤ u → ∀ A : ℝ,
      (∀ k ≤ m+1, |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ A) →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        Real.exp (-(orderRate m)*u) *
          (C * (A * ((H : ℝ)+1)^(1/2+η) + ((H : ℝ)+1)^(1+η) +
            ((m : ℝ)+1)*(H : ℝ)^(η-1/2))) := by
  obtain ⟨F, hF, hhead⟩ := signed_low_occurrence_sum_of_damped_prefix hRH hη
  obtain ⟨G, hG, htail⟩ := masked_occurrence_tail_at hRH hη hηhalf
  refine ⟨max F G, hF.trans_le (le_max_left _ _), ?_⟩
  intro m H hm hH u hu A ha
  let q := m+1
  let p := (q+1)/2
  let a (n : ℕ) : ℂ := -((μ n : ℝ) : ℂ)
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hqu : (q : ℝ) ≤ u := by simpa only [hq'] using hu
  have hu₀ := (Nat.cast_nonneg q : (0 : ℝ) ≤ q).trans hqu
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hp : 0 < p := by dsimp [p, q]; omega
  have hpm : p ≤ m := by dsimp [p, q]; omega
  have hhalf : q ≤ 2*p := by dsimp [p]; omega
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha 0 (Nat.zero_le _))
  have ha' (k : ℕ) (hk : k ≤ m+1) : ‖∑ n ∈ Finset.range k, a n‖ ≤ A := by
    simpa only [a, Finset.sum_neg_distrib, ← Complex.ofReal_sum, norm_neg, Complex.norm_real,
      Real.norm_eq_abs] using ha k hk
  have han (n : ℕ) : ‖a n‖ ≤ 1 := by
    simp only [a, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  let P := A*((H : ℝ)+1)^(1/2+η) + ((H : ℝ)+1)^(1+η)
  let Q := (q : ℝ)*(H : ℝ)^(η-1/2)
  have hl : ∀ T : Finset ℕ, ‖∑ n ∈ Finset.Icc p m, a n *
      ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
        normalizedMode q u n i‖ ≤ F*P :=
    hhead q p m H hq hp hpm (Nat.le_add_right _ _) hhalf u hu₀ a A hA han ha'
  have hb := signed_omitted_root_density_of_finite_bounds (H := H) (Q := G*Q)
    hRH hm hu₀ hl (fun T => (htail q H hq hH u hqu T).trans_eq (mul_assoc _ _ _))
  rw [← hq']
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  calc
    _ ≤ max F G * P + max F G * Q :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left F G) hP)
        (mul_le_mul_of_nonneg_right (le_max_right F G) hQ)
    _ = _ := by dsimp only [P, Q]; ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
