/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedSpectrumCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedSpectrumCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed degree cancellation and masked sampling in the same zero-occurrence sum. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.OmittedSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.BinSquareTail

/-! Finite Abel summation over the omitted degrees of the actual root expansion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Finset Real Complex ArithmeticFunction
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open scoped ArithmeticFunction.Moebius

private theorem finite_complex_abel_bound {a w : ℕ → ℂ} {p m : ℕ} (hpm : p ≤ m)
    {H : ℝ} (ha : ∀ k ≤ m+1, ‖∑ n ∈ Finset.range k, a n‖ ≤ H) :
    ‖∑ n ∈ Finset.Icc p m, a n * w n‖ ≤
      H * (‖w m‖ + ‖w p‖ + ∑ n ∈ Finset.Ico p m, ‖w (n+1) - w n‖) := by
  let A (k : ℕ) := ∑ n ∈ Finset.range k, a n
  have he : (∑ n ∈ Finset.Icc p m, a n*w n) =
      w m*A (m+1) - w p*A p - ∑ n ∈ Finset.Ico p m, (w (n+1)-w n)*A (n+1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa only [A, smul_eq_mul, Nat.add_sub_cancel, mul_comm] using
      Finset.sum_Ico_by_parts w a (show p < m+1 by omega)
  rw [he]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) (norm_sum_le _ _)).trans ?_)
  rw [norm_mul, norm_mul, mul_add, mul_add, Finset.mul_sum]
  refine add_le_add (add_le_add ?_ ?_) (Finset.sum_le_sum fun n hn => ?_)
  · exact (mul_le_mul_of_nonneg_left (ha _ le_rfl) (norm_nonneg _)).trans_eq (mul_comm _ _)
  · exact (mul_le_mul_of_nonneg_left (ha _ (by omega)) (norm_nonneg _)).trans_eq (mul_comm _ _)
  · rw [norm_mul]
    have hn' := (Finset.mem_Ico.mp hn).2
    exact (mul_le_mul_of_nonneg_left (ha _ (by omega)) (norm_nonneg _)).trans_eq (mul_comm _ _)

private theorem sum_Ico_adjacent_sub (f : ℕ → ℝ) {p m : ℕ} (hpm : p ≤ m) :
    (∑ n ∈ Finset.Ico p m, (f n - f (n+1))) = f p - f m := by
  have h := congrArg Neg.neg (Finset.sum_Ico_sub f hpm)
  simpa only [← Finset.sum_neg_distrib, neg_sub] using h

def normalizedMode (q : ℕ) (u : ℝ) (n i : ℕ) : ℂ :=
  (Real.exp (-(2*u/(q : ℝ)-u/(n : ℝ))/2) : ℂ) *
    (rootCoeff n i * Complex.exp (Complex.I * (occurrenceFrequency i : ℂ) * ((u/(n : ℝ) : ℝ) : ℂ)))

private theorem unit_phase_diff (γ v w : ℝ) :
    ‖Complex.exp (Complex.I * (γ : ℂ) * (v : ℂ)) -
      Complex.exp (Complex.I * (γ : ℂ) * (w : ℂ))‖ ≤ |γ| *|v-w| := by
  let f (x : ℝ) := Complex.exp (Complex.I * (γ : ℂ) * (x : ℂ))
  have hnorm : ‖f w‖ = 1 := by simp [f, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have he : f v - f w = (f (v-w)-1)*f w := by
    unfold f
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  change ‖f v-f w‖ ≤ _
  rw [he, norm_mul, hnorm, mul_one]
  have hf : f (v-w) = Complex.exp (Complex.I * ((γ*(v-w) : ℝ) : ℂ)) := by
    simp only [f, Complex.ofReal_mul, mul_assoc]
  rw [hf]
  simpa only [Real.norm_eq_abs, abs_mul] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := γ*(v-w))

private theorem normalized_mode_variation_core (hRH : RiemannHypothesis)
    {q p m : ℕ} (hp : 0 < p) (hpm : p ≤ m) (hmq : m ≤ q) (hhalf : q ≤ 2*p)
    {u : ℝ} (hu : 0 ≤ u) (i : ℕ) :
    ‖normalizedMode q u m i‖ + ‖normalizedMode q u p i‖ +
        ∑ n ∈ Finset.Ico p m, ‖normalizedMode q u (n+1) i - normalizedMode q u n i‖ ≤
      (10 + 4*|occurrenceFrequency i| * min 1 (u/(q : ℝ))) * (‖actualZero i‖)⁻¹ := by
  let r := (‖actualZero i‖)⁻¹
  let γ := occurrenceFrequency i
  let v (n : ℕ) := u/(n : ℝ)
  let E (n : ℕ) := Real.exp (-(2*u/(q : ℝ)-v n)/2)
  let P (n : ℕ) := Complex.exp (Complex.I * (γ : ℂ) * (v n : ℂ))
  let c (n : ℕ) := rootCoeff n i
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hp.trans_le (hpm.trans hmq)
  have hhalf' : (q : ℝ)/2 ≤ p := by
    have h : (q : ℝ) ≤ 2*(p : ℝ) := by exact_mod_cast hhalf
    linarith
  have hvanti (n k : ℕ) (hn : p ≤ n) (hnk : n ≤ k) : v k ≤ v n := by
    have hn₀ : (0 : ℝ) < n := hp₀.trans_le (by exact_mod_cast hn)
    exact div_le_div_of_nonneg_left hu hn₀ (by exact_mod_cast hnk)
  have hvbound (n : ℕ) (hn : p ≤ n) : v n ≤ 2*u/(q : ℝ) := by
    have hn' : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h := div_le_div_of_nonneg_left hu (show (0 : ℝ) < (q : ℝ)/2 by positivity)
      (hhalf'.trans hn')
    exact h.trans_eq (by ring)
  have hE (n : ℕ) : 0 ≤ E n := Real.exp_nonneg _
  have hE₁ (n : ℕ) (hn : p ≤ n) : E n ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith only [hvbound n hn]
  have hEanti (n k : ℕ) (hn : p ≤ n) (hnk : n ≤ k) : E k ≤ E n := by
    apply Real.exp_le_exp.mpr
    linarith only [hvanti n k hn hnk]
  have hP (n : ℕ) : ‖P n‖ = 1 := by simp [P, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hc (n : ℕ) (hn : p ≤ n) : ‖c n‖ ≤ 2*r :=
    occurrence_coeff_le hRH (by exact_mod_cast (show 1 ≤ n by omega)) i
  have hnorm (n : ℕ) (hn : p ≤ n) : ‖normalizedMode q u n i‖ ≤ 2*r := by
    change ‖(E n : ℂ)*(c n*P n)‖ ≤ _
    rw [norm_mul, norm_mul, hP, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hE n)]
    exact mul_le_of_le_one_left (by positivity) (hE₁ n hn) |>.trans (hc n hn)
  have hstep (n : ℕ) (hn : n ∈ Finset.Ico p m) :
      ‖normalizedMode q u (n+1) i-normalizedMode q u n i‖ ≤
        2*r*(E n-E (n+1)) + (4/(q : ℝ))*r + 2*r*|γ| * (E (n+1)*(v n-v (n+1))) := by
    have hpn := (Finset.mem_Ico.mp hn).1
    have hpn' := hpn.trans (Nat.le_succ n)
    have he : normalizedMode q u (n+1) i-normalizedMode q u n i =
        ((E (n+1) : ℂ)-(E n : ℂ))*c n*P n +
        (E (n+1) : ℂ)*(c (n+1)-c n)*P n +
        (E (n+1) : ℂ)*c (n+1)*(P (n+1)-P n) := by
      change (E (n+1) : ℂ)*(c (n+1)*P (n+1))-(E n : ℂ)*(c n*P n) = _
      ring
    have hv := hvanti n (n+1) hpn (Nat.le_succ _)
    have hphase : ‖P (n+1) - P n‖ ≤ |γ| *(v n-v (n+1)) := by
      have h := unit_phase_diff γ (v (n+1)) (v n)
      rwa [abs_of_nonpos (sub_nonpos.mpr hv), neg_sub] at h
    have hcstep : ‖c (n+1)-c n‖ ≤ (4/(q : ℝ))*r := by
      have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn₂ : (q : ℝ)/2 ≤ n := hhalf'.trans (by exact_mod_cast hpn)
      simpa only [c, r, Nat.cast_add, Nat.cast_one, occurrenceIncrement] using
        occurrenceIncrement_le hRH hn₁ hq₀ hn₂ i
    rw [he]
    refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
    simp only [norm_mul, hP, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hE (n+1))]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hEanti n (n+1) hpn (Nat.le_succ _))), neg_sub]
    have hfirst := mul_le_mul_of_nonneg_left (hc n hpn)
      (sub_nonneg.mpr (hEanti n (n+1) hpn (Nat.le_succ _)))
    have hsecond := (mul_le_of_le_one_left (norm_nonneg (c (n+1)-c n)) (hE₁ (n+1) hpn')).trans hcstep
    have hthird :
        E (n+1) * ‖c (n+1)‖ * ‖P (n+1)-P n‖ ≤ 2*r*|γ| * (E (n+1)*(v n-v (n+1))) := by
      calc
        _ ≤ E (n+1) * (2*r) * (|γ| *(v n-v (n+1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hc (n+1) hpn') (hE _))
            hphase (norm_nonneg _) (by positivity)
        _ = _ := by ring
    nlinarith only [hfirst, hsecond, hthird]
  have hcard : ((Finset.Ico p m).card : ℝ) ≤ q := by
    exact_mod_cast (show (Finset.Ico p m).card ≤ q by rw [Nat.card_Ico]; omega)
  have hcard' : ((Finset.Ico p m).card : ℝ)*((4/(q : ℝ))*r) ≤ 4*r := by
    refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_
    field_simp
  let V := ∑ n ∈ Finset.Ico p m, E (n+1)*(v n-v (n+1))
  have hVsmall : V ≤ 2*u/(q : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico p m, (v n-v (n+1)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := (Finset.mem_Ico.mp hn).1
        exact mul_le_of_le_one_left
          (sub_nonneg.mpr (hvanti n (n+1) hn' (Nat.le_succ _)))
          (hE₁ (n+1) (hn'.trans (Nat.le_succ _)))
      _ = v p-v m := sum_Ico_adjacent_sub _ hpm
      _ ≤ _ := by
        have hvm : 0 ≤ v m := by dsimp [v]; positivity
        linarith only [hvbound p le_rfl, hvm]
  have hVlarge : V ≤ 2*(E p-E m) := by
    rw [← sum_Ico_adjacent_sub E hpm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have he : E n = E (n+1) * Real.exp ((v n-v (n+1))/2) := by
      dsimp only [E]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp ((v n-v (n+1))/2)) (hE (n+1))
    nlinarith only [h]
  have hEs : E p-E m ≤ 1 := by linarith only [hE₁ p le_rfl, hE m]
  have hV : V ≤ 2 * min 1 (u/(q : ℝ)) := by
    by_cases h : 1 ≤ u/(q : ℝ)
    · rw [min_eq_left h]
      linarith only [hVlarge, hEs]
    · rw [min_eq_right (le_of_not_ge h)]
      exact hVsmall.trans_eq (by ring)
  calc
    _ ≤ 2*r + 2*r + ∑ n ∈ Finset.Ico p m,
        (2*r*(E n-E (n+1)) + (4/(q : ℝ))*r + 2*r*|γ| * (E (n+1)*(v n-v (n+1)))) :=
      add_le_add (add_le_add (hnorm m hpm) (hnorm p le_rfl)) (Finset.sum_le_sum hstep)
    _ = 2*r + 2*r + (2*r*(E p-E m) +
        ((Finset.Ico p m).card : ℝ)*((4/(q : ℝ))*r) + 2*r*|γ| * V) := by
      dsimp only [V]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
        sum_Ico_adjacent_sub _ hpm]
      ring
    _ ≤ 2*r + 2*r + ((2*r*1 + 4*r) + 2*r*|γ| * (2 * min 1 (u/(q : ℝ)))) := by
      apply add_le_add le_rfl
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hEs (by positivity)) hcard')
        (mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 2*r*|γ|))
    _ = _ := by change _ = (10 + 4*|γ| * min 1 (u/(q : ℝ)))*r; ring

private theorem normalized_mode_variation (hRH : RiemannHypothesis)
    {q p m : ℕ} (hp : 0 < p) (hpm : p ≤ m) (hmq : m ≤ q) (hhalf : q ≤ 2*p)
    {u : ℝ} (hu : 0 ≤ u) (i : ℕ) :
    ‖normalizedMode q u m i‖ + ‖normalizedMode q u p i‖ +
        ∑ n ∈ Finset.Ico p m, ‖normalizedMode q u (n+1) i - normalizedMode q u n i‖ ≤
      (10 + 4*|occurrenceFrequency i| *(u/(q : ℝ))) * (‖actualZero i‖)⁻¹ := by
  refine (normalized_mode_variation_core hRH hp hpm hmq hhalf hu i).trans ?_
  exact mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))) (by positivity)

def lowBins (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) H

theorem mem_lowBins {H : ℕ} {k : ℤ} : k ∈ lowBins H ↔ k.natAbs ≤ H := by
  rw [lowBins, Finset.mem_Icc, ← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]

theorem masked_occurrence_tail_at (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q H : ℕ), 3 ≤ q → 0 < H →
      ∀ u : ℝ, (q : ℝ) ≤ u → ∀ T : Finset ℕ,
      (∑ n ∈ Finset.Icc ((q+1)/2) q,
        Real.exp (-(2*u/(q : ℝ)-u/(n : ℝ))/2) *
          ‖finiteModes (T.filter (fun i => frequencyBin (occurrenceFrequency i) ∉ lowBins H))
            occurrenceFrequency (rootCoeff n) (u/(n : ℝ))‖) ≤
        C * (q : ℝ) * (H : ℝ)^(η-1/2) := by
  obtain ⟨D, hD, hmass⟩ := occurrence_bin_power_majorant_at hRH hη
  obtain ⟨G, hG, hinter⟩ := exists_local_mode_integral_le_square_mass
  let d := 1 - Real.exp (-1/2)
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  let R := 2 / (1-2*η)
  have hR : 0 < R := div_pos (by norm_num) (by linarith)
  refine ⟨8*G*D*Real.sqrt R/d, by positivity, fun q H hq hH u hu T => ?_⟩
  let b (k : ℤ) := D*(|(k : ℝ)|+1)^(η-1)
  let bTail (k : ℤ) := if k ∈ lowBins H then 0 else b k
  have hb : Summable (fun k : ℤ => b k ^ 2) := by
    have hs : Summable (fun n : ℕ => (n : ℝ)^(2*(η-1))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have ht := ((summable_nat_add_iff 1).2 hs).mul_left (D^2)
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;> apply ht.congr <;> intro n <;>
      simp only [b, Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), Nat.cast_add, Nat.cast_one,
        mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)+1)] <;>
      congr 2 <;> ring
  have hsum : Summable (fun k : ℤ => bTail k ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_) hb
    change bTail k ^ 2 ≤ b k ^ 2
    by_cases hk : k ∈ lowBins H
    · simp only [bTail, if_pos hk, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact sq_nonneg _
    · simp only [bTail, if_neg hk, le_refl]
  have hshape (k : ℤ) : bTail k ^ 2 =
      D^2*(if k.natAbs ≤ H then 0 else (|(k : ℝ)|+1)^(2*(η-1))) := by
    by_cases hk : k ∈ lowBins H
    · simp [bTail, hk, mem_lowBins.mp hk]
    · have hk' : ¬ k.natAbs ≤ H := fun hs => hk (mem_lowBins.mpr hs)
      simp only [bTail, hk, hk', if_false, b, mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      congr 1
      ring
  have hsq : (∑' k : ℤ, bTail k ^ 2) ≤ D^2*(R*(H : ℝ)^(2*η-1)) := by
    simp_rw [hshape, tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    refine (signed_bin_tail_rpow H hH (by linarith : 2*(η-1) < -1)).trans_eq ?_
    rw [show 2*(η-1)+1 = 2*η-1 by ring]
    dsimp [R]
    rw [show -(2*η-1) = 1-2*η by ring]
    ring
  have hroot : Real.sqrt (∑' k : ℤ, bTail k ^ 2) ≤ D*Real.sqrt R*(H : ℝ)^(η-1/2) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, hsq.trans_eq ?_⟩
    have hs : ((H : ℝ)^(η-1/2))^2 = (H : ℝ)^(2*η-1) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg H)]
      congr 1
      push_cast
      ring
    simp only [mul_pow, Real.sq_sqrt hR.le, hs]
    ring
  let K := G * Real.sqrt (∑' k : ℤ, bTail k^2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsample := occurrence_weighted_finite hRH hK (hinter bTail hsum) hq hu
    (T.filter (fun i => frequencyBin (occurrenceFrequency i) ∉ lowBins H))
    (fun k => occurrence_compl_bin_majorant (lowBins H) T (hmass T) k)
  refine hsample.trans ?_
  have hK' := mul_le_mul_of_nonneg_left hroot hG.le
  calc
    _ ≤ (8*(G*(D*Real.sqrt R*(H : ℝ)^(η-1/2)))/d)*(q : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK' (by norm_num)) hd.le) (Nat.cast_nonneg _)
    _ = _ := by ring

private theorem masked_occurrence_tail (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q H : ℕ), 3 ≤ q → 0 < H →
      ∀ u : ℝ, (q : ℝ) ≤ u → ∀ T : Finset ℕ,
      (∑ n ∈ Finset.Icc ((q+1)/2) q,
        Real.exp (-(2*u/(q : ℝ)-u/(n : ℝ))/2) *
          ‖finiteModes (T.filter (fun i => frequencyBin (occurrenceFrequency i) ∉ lowBins H))
            occurrenceFrequency (rootCoeff n) (u/(n : ℝ))‖) ≤
        C * (q : ℝ) * (H : ℝ)^(-1/4 : ℝ) := by
  simpa only [show (1/4 : ℝ)-1/2 = -1/4 by norm_num] using
    masked_occurrence_tail_at hRH (η := 1/4) (by norm_num) (by norm_num)

private theorem low_occurrence_sum (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q p m H : ℕ), 0 < p → p ≤ m → m ≤ q → q ≤ 2*p →
      ∀ u : ℝ, 0 ≤ u → ∀ (a : ℕ → ℂ) (A : ℝ),
      (∀ k ≤ m+1, ‖∑ n ∈ Finset.range k, a n‖ ≤ A) → ∀ T : Finset ℕ,
      ‖∑ n ∈ Finset.Icc p m,
        a n * ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
          normalizedMode q u n i‖ ≤
        C * A * ((H : ℝ)+1)^(1/4 : ℝ) * (1+((H : ℝ)+1)*(u/(q : ℝ))) := by
  obtain ⟨D, hD, hmass⟩ := occurrence_bin_power_majorant hRH
  refine ⟨80*D, by positivity, fun q p m H hp hpm hmq hhalf u hu a A ha T => ?_⟩
  let b (i : ℕ) := frequencyBin (occurrenceFrequency i)
  let U := T.filter (fun i => b i ∈ lowBins H)
  let r (i : ℕ) := (‖actualZero i‖)⁻¹
  let V := Finset.Icc p m
  let h := (H : ℝ)+1
  let s := u/(q : ℝ)
  have hs : 0 ≤ s := div_nonneg hu (Nat.cast_nonneg _)
  have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0 (Nat.zero_le _))
  have hγ (i : ℕ) (hi : i ∈ U) : |occurrenceFrequency i| ≤ h := by
    have hk := (Finset.mem_Icc.mp ((Finset.mem_filter.mp hi).2 : b i ∈ lowBins H))
    have hk₁ : -((H : ℝ)) ≤ (b i : ℝ) := by exact_mod_cast hk.1
    have hk₂ : (b i : ℝ) ≤ (H : ℝ) := by exact_mod_cast hk.2
    have hv := mem_frequencyBin (occurrenceFrequency i)
    exact abs_le.mpr ⟨by dsimp [h]; linarith [hv.1], by dsimp [h]; linarith [hv.2]⟩
  have hhead : (∑ i ∈ U, r i) ≤ 8*D*h^(1/4 : ℝ) := by
    calc
      _ = ∑ k ∈ lowBins H, ∑ i ∈ U with b i = k, r i :=
        (Finset.sum_fiberwise_of_maps_to (s := U) (t := lowBins H)
          (g := b) (fun i hi => (Finset.mem_filter.mp hi).2) r).symm
      _ ≤ ∑ k ∈ lowBins H, D*(|(k : ℝ)|+1)^(-3/4 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hmass U k)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left (by simpa only [h, lowBins, Nat.cast_add, Nat.cast_one]
          using signed_bin_head_inv_three_quarters H) hD.le).trans_eq (by ring)
  have hterm (i : ℕ) (hi : i ∈ U) : ‖∑ n ∈ V, a n * normalizedMode q u n i‖ ≤
      (A*(10*(1+h*s)))*r i := by
    have hvar := normalized_mode_variation hRH hp hpm hmq hhalf hu i
    refine (finite_complex_abel_bound hpm ha).trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA
    exact hvar.trans (mul_le_mul_of_nonneg_right (by
      change 10+4*|occurrenceFrequency i| *s ≤ 10*(1+h*s)
      nlinarith only [mul_le_mul_of_nonneg_right (hγ i hi) hs,
        mul_nonneg (show 0 ≤ h by dsimp [h]; positivity) hs]) (by positivity))
  change ‖∑ n ∈ V, a n * ∑ i ∈ U, normalizedMode q u n i‖ ≤ _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ U, (A*(10*(1+h*s)))*r i :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ (A*(10*(1+h*s)))*(8*D*h^(1/4 : ℝ)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left hhead
      have hh : 0 ≤ h := by dsimp [h]; positivity
      positivity
    _ = _ := by ring

private theorem uniform_low_occurrence_sum (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q p m H : ℕ), 0 < p → p ≤ m → m ≤ q → q ≤ 2*p →
      ∀ u : ℝ, 0 ≤ u → ∀ (a : ℕ → ℂ) (A : ℝ),
      (∀ k ≤ m+1, ‖∑ n ∈ Finset.range k, a n‖ ≤ A) → ∀ T : Finset ℕ,
      ‖∑ n ∈ Finset.Icc p m,
        a n * ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
          normalizedMode q u n i‖ ≤ C * A * ((H : ℝ)+1)^(1+η) := by
  obtain ⟨D, hD, hmass⟩ := occurrence_bin_power_majorant_at hRH hη
  refine ⟨36*D, by positivity, fun q p m H hp hpm hmq hhalf u hu a A ha T => ?_⟩
  let b (i : ℕ) := frequencyBin (occurrenceFrequency i)
  let U := T.filter (fun i => b i ∈ lowBins H)
  let r (i : ℕ) := (‖actualZero i‖)⁻¹
  let w (i : ℕ) := (10+4*|occurrenceFrequency i|) * r i
  let V := Finset.Icc p m
  let h := (H : ℝ)+1
  have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0 (Nat.zero_le _))
  have hγ (i : ℕ) : |occurrenceFrequency i| ≤ |(b i : ℝ)|+1 := by
    have hv := mem_frequencyBin (occurrenceFrequency i)
    change (b i : ℝ) < occurrenceFrequency i ∧ occurrenceFrequency i ≤ (b i : ℝ)+1 at hv
    exact abs_le.mpr ⟨by linarith only [hv.1, neg_abs_le (b i : ℝ)],
      by linarith only [hv.2, le_abs_self (b i : ℝ)]⟩
  have hbin (k : ℤ) (hk : k ∈ lowBins H) :
      ∑ i ∈ U with b i = k, w i ≤ (18*D)*h^η := by
    let x := |(k : ℝ)|+1
    have hx : 1 ≤ x := by dsimp [x]; linarith [abs_nonneg (k : ℝ)]
    have hx' : 0 < x := zero_lt_one.trans_le hx
    have hreal : |(k : ℝ)| ≤ H := by
      rw [abs_le]
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
      exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩
    have hxh : x ≤ h := by dsimp [x, h]; linarith
    calc
      _ ≤ ∑ i ∈ U with b i = k, 18*x*r i := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_right _ (by dsimp [r]; positivity)
        have hi' := hγ i
        rw [(Finset.mem_filter.mp hi).2] at hi'
        dsimp [x]
        linarith only [hi', hx]
      _ = (18*x) * ∑ i ∈ U with b i = k, r i := by rw [Finset.mul_sum]
      _ ≤ (18*x)*(D*x^(η-1)) :=
        mul_le_mul_of_nonneg_left (hmass U k) (by positivity)
      _ = 18*D*x^η := by
        rw [show x^η = x^(η-1)*x by
          calc
            _ = x^((η-1)+1) := by congr 1 <;> ring
            _ = _ := by rw [Real.rpow_add hx', Real.rpow_one]]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx'.le hxh hη.le) (by positivity)
  have hcard : ((lowBins H).card : ℝ) ≤ 2*h := by
    have hlim : (lowBins H).card ≤ 2*H+1 := by
      dsimp [lowBins]
      rw [Int.card_Icc]
      omega
    have hreal : ((lowBins H).card : ℝ) ≤ (2*H+1 : ℕ) := by exact_mod_cast hlim
    push_cast at hreal
    dsimp [h]
    linarith
  have hhead : (∑ i ∈ U, w i) ≤ 36*D*h^(1+η) := by
    calc
      _ = ∑ k ∈ lowBins H, ∑ i ∈ U with b i = k, w i :=
        (Finset.sum_fiberwise_of_maps_to (s := U) (t := lowBins H)
          (g := b) (fun i hi => (Finset.mem_filter.mp hi).2) w).symm
      _ ≤ ∑ _ ∈ lowBins H, (18*D)*h^η := Finset.sum_le_sum hbin
      _ ≤ (2*h)*((18*D)*h^η) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by
        rw [Real.rpow_add (by dsimp [h]; positivity), Real.rpow_one]
        ring
  have hterm (i : ℕ) : ‖∑ n ∈ V, a n * normalizedMode q u n i‖ ≤ A*w i := by
    refine (finite_complex_abel_bound hpm ha).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA
    refine (normalized_mode_variation_core hRH hp hpm hmq hhalf hu i).trans ?_
    change _ ≤ (10+4*|occurrenceFrequency i|) * r i
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact add_le_add (le_refl (10 : ℝ))
      (mul_le_of_le_one_right (by positivity) (min_le_left 1 (u / (q : ℝ))))
  change ‖∑ n ∈ V, a n * ∑ i ∈ U, normalizedMode q u n i‖ ≤ _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ U, A*w i := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ ≤ A*(36*D*h^(1+η)) := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hhead hA
    _ = _ := by ring

theorem signed_omitted_root_density_of_finite_bounds (hRH : RiemannHypothesis)
    {m H : ℕ} (hm : 2 ≤ m) {u P Q : ℝ} (hu : 0 ≤ u)
    (hlow : let S := Finset.Icc ((m+2)/2) m
      ∀ T : Finset ℕ, ‖∑ n ∈ S, -((μ n : ℝ) : ℂ) *
        ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
          normalizedMode (m+1) u n i‖ ≤ P)
    (hhigh : ∀ T : Finset ℕ,
      (∑ n ∈ Finset.Icc ((m+2)/2) (m+1),
        Real.exp (-(2*u/((m+1 : ℕ) : ℝ)-u/(n : ℝ))/2) *
        ‖finiteModes (T.filter (fun i => frequencyBin (occurrenceFrequency i) ∉ lowBins H))
          occurrenceFrequency (rootCoeff n) (u/(n : ℝ))‖) ≤ Q) :
    |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
      -(μ n : ℝ) * rootDensity n u| ≤ Real.exp (-(orderRate m)*u) * (P+Q) := by
  let q := m+1
  let p := (q+1)/2
  let S := Finset.Icc p m
  let a (n : ℕ) : ℂ := -((μ n : ℝ) : ℂ)
  let W := Real.exp (-(orderRate m)*u)
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hfinite (T : Finset ℕ) :
      ‖∑ n ∈ S, a n * ∑ i ∈ T, normalizedMode q u n i‖ ≤ P+Q := by
    let low (i : ℕ) : Prop := frequencyBin (occurrenceFrequency i) ∈ lowBins H
    let T₀ := T.filter low
    let T₁ := T.filter (fun i => ¬ low i)
    have hsplit (n : ℕ) : (∑ i ∈ T, normalizedMode q u n i) =
        (∑ i ∈ T₀, normalizedMode q u n i) + ∑ i ∈ T₁, normalizedMode q u n i :=
      (Finset.sum_filter_add_sum_filter_not _ low _).symm
    have hl : ‖∑ n ∈ S, a n * ∑ i ∈ T₀, normalizedMode q u n i‖ ≤ P := hlow T
    have hh : ‖∑ n ∈ S, a n * ∑ i ∈ T₁, normalizedMode q u n i‖ ≤ Q := by
      have hs : S ⊆ Finset.Icc ((q+1)/2) q := Finset.Icc_subset_Icc_right (by dsimp [q]; omega)
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans
        ((Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
          (hhigh T)))
      intro n hn
      have hnrm : ‖a n‖ ≤ 1 := by
        simp only [a, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast (abs_moebius_le_one (n := n))
      simp only [normalizedMode, ← Finset.mul_sum, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_of_le_one_left (by positivity) hnrm
    simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
    exact (norm_add_le _ _).trans (add_le_add hl hh)
  have hsum (n : ℕ) (hn : n ∈ S) : Summable (normalizedMode q u n) := by
    have hn₁ : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega)
    exact (rootMode_phase_summable hRH hn₁ u).mul_left _
  have hlim (n : ℕ) (hn : n ∈ S) :=
    (hsum n hn).hasSum.tendsto_sum_nat.const_mul (a n)
  have htotal : ‖∑ n ∈ S, a n * ∑' i : ℕ, normalizedMode q u n i‖ ≤ P+Q :=
    le_of_tendsto' (tendsto_finsetSum S hlim).norm (fun k => hfinite (Finset.range k))
  have hfilter : (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n) = S := by
    ext n
    simp only [S, p, q, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hterm (n : ℕ) (hn : n ∈ S) :
      -(μ n : ℝ)*rootDensity (n : ℝ) u =
        W * (a n * ∑' i : ℕ, normalizedMode q u n i).re := by
    have hn₀ : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega)
    have hfactor (i : ℕ) : rootMode n u i = (W : ℂ)*normalizedMode q u n i := by
      have hexp : Real.exp (((2*(n : ℝ))⁻¹-1/2)*u) =
          W*Real.exp (-(2*u/(q : ℝ)-u/(n : ℝ))/2) := by
        dsimp only [W, orderRate]
        rw [hq', ← Real.exp_add]
        congr 1
        ring
      rw [rootMode_eq_phase hRH hn₀, normalizedMode, hexp, Complex.ofReal_mul, mul_assoc]
    unfold rootDensity
    simp_rw [hfactor, tsum_mul_left]
    simp only [a, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
    ring
  rw [hfilter, Finset.sum_congr rfl hterm, ← Finset.mul_sum, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact (by simpa only [Complex.re_sum] using
    (Complex.abs_re_le_norm (∑ n ∈ S, a n * ∑' i : ℕ, normalizedMode q u n i)).trans htotal)

/-- A frequency cutoff separates signed degree cancellation from the high-frequency tail. -/
theorem signed_omitted_root_density_of_varying_cutoff (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ m H : ℕ, 2 ≤ m → 0 < H →
      ∀ u : ℝ, (m : ℝ)+1 ≤ u → ∀ A : ℝ,
      (∀ k ≤ m+1, |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ A) →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        Real.exp (-(orderRate m)*u) *
          (C * (A * ((H : ℝ)+1)^(1/4 : ℝ) * (1+((H : ℝ)+1)*(u/((m : ℝ)+1))) +
            ((m : ℝ)+1)*(H : ℝ)^(-1/4 : ℝ))) := by
  obtain ⟨F, hF, hhead⟩ := low_occurrence_sum hRH
  obtain ⟨G, hG, htail⟩ := masked_occurrence_tail hRH
  refine ⟨max F G, hF.trans_le (le_max_left _ _), fun m H hm hH u hu A ha => ?_⟩
  let q := m+1
  let p := (q+1)/2
  let a (n : ℕ) : ℂ := -((μ n : ℝ) : ℂ)
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hqu : (q : ℝ) ≤ u := by simpa only [hq'] using hu
  have hu₀ := (Nat.cast_nonneg q : (0 : ℝ) ≤ q).trans hqu
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hpm : p ≤ m := by dsimp [p, q]; omega
  have hhalf : q ≤ 2*p := by dsimp [p]; omega
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha 0 (Nat.zero_le _))
  have ha' (k : ℕ) (hk : k ≤ m+1) : ‖∑ n ∈ Finset.range k, a n‖ ≤ A := by
    simpa only [a, Finset.sum_neg_distrib, ← Complex.ofReal_sum, norm_neg, Complex.norm_real,
      Real.norm_eq_abs] using ha k hk
  let P := A*((H : ℝ)+1)^(1/4 : ℝ)*(1+((H : ℝ)+1)*(u/(q : ℝ)))
  let Q := (q : ℝ)*(H : ℝ)^(-1/4 : ℝ)
  have hl : ∀ T : Finset ℕ, ‖∑ n ∈ Finset.Icc p m, a n *
      ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
        normalizedMode q u n i‖ ≤ F*P := by
    intro T
    exact (hhead q p m H (by omega) hpm (Nat.le_add_right _ _) hhalf u hu₀ a A ha' T).trans_eq
      (by dsimp only [P]; ring)
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

/-- The decaying envelope controls the variation of each low-frequency mode uniformly
in the sample range. The high-frequency part uses the square-summable inverse-root masses. -/
theorem signed_omitted_root_density_of_uniform_cutoff (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m H : ℕ, 2 ≤ m → 0 < H →
      ∀ u : ℝ, (m : ℝ)+1 ≤ u → ∀ A : ℝ,
      (∀ k ≤ m+1, |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ A) →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        Real.exp (-(orderRate m)*u) *
          (C * (A * ((H : ℝ)+1)^(1+η) + ((m : ℝ)+1)*(H : ℝ)^(η-1/2))) := by
  obtain ⟨F, hF, hhead⟩ := uniform_low_occurrence_sum hRH hη
  obtain ⟨G, hG, htail⟩ := masked_occurrence_tail_at hRH hη hηhalf
  refine ⟨max F G, hF.trans_le (le_max_left _ _), fun m H hm hH u hu A ha => ?_⟩
  let q := m+1
  let p := (q+1)/2
  let a (n : ℕ) : ℂ := -((μ n : ℝ) : ℂ)
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hqu : (q : ℝ) ≤ u := by simpa only [hq'] using hu
  have hu₀ := (Nat.cast_nonneg q : (0 : ℝ) ≤ q).trans hqu
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hpm : p ≤ m := by dsimp [p, q]; omega
  have hhalf : q ≤ 2*p := by dsimp [p]; omega
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha 0 (Nat.zero_le _))
  have ha' (k : ℕ) (hk : k ≤ m+1) : ‖∑ n ∈ Finset.range k, a n‖ ≤ A := by
    simpa only [a, Finset.sum_neg_distrib, ← Complex.ofReal_sum, norm_neg, Complex.norm_real,
      Real.norm_eq_abs] using ha k hk
  let P := A*((H : ℝ)+1)^(1+η : ℝ)
  let Q := (q : ℝ)*(H : ℝ)^(η-1/2 : ℝ)
  have hl : ∀ T : Finset ℕ, ‖∑ n ∈ Finset.Icc p m, a n *
      ∑ i ∈ T with frequencyBin (occurrenceFrequency i) ∈ lowBins H,
        normalizedMode q u n i‖ ≤ F*P := by
    intro T
    exact (hhead q p m H (by omega) hpm (Nat.le_add_right _ _) hhalf u hu₀ a A ha' T).trans_eq
      (by dsimp only [P]; ring)
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
