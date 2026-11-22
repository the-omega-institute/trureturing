/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/LateWindowSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/LateWindowSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: High-frequency occurrence sampling with exact degree spacing. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.BinSquareTail
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.OmittedSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Finset Real MeasureTheory
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

private def derivativeBinProfile (q : ℕ) (η : ℝ) (k : ℤ) : ℝ :=
  min (q : ℝ) (|(k : ℝ)| + 1) * (|(k : ℝ)| + 1) ^ (η - 1)

-- Splitting at the degree scale keeps the derivative's square mass sublinear after taking a root.
private theorem derivative_bin_square_budget {η : ℝ} (hη : 0 < η) (hη' : η < 1/2)
    {q : ℕ} (hq : 0 < q) :
    Summable (fun k : ℤ => derivativeBinProfile q η k ^ 2) ∧
    (∑' k : ℤ, derivativeBinProfile q η k ^ 2) ≤
      (3 * 2 ^ (2*η) + 2 / (1 - 2*η)) * (q : ℝ) ^ (1 + 2*η) := by
  let b (k : ℤ) := |(k : ℝ)| + 1
  let s := 2*(η - 1)
  let f (k : ℤ) := derivativeBinProfile q η k ^ 2
  let L : Finset ℤ := Icc (-(q : ℤ)) q
  have hb (k : ℤ) : 0 < b k := by dsimp [b]; positivity
  have hs : s < -1 := by dsimp [s]; linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hsummable : Summable (fun k : ℤ => b k ^ s) := by
    have h : Summable (fun n : ℕ => (n : ℝ)^s) := Real.summable_nat_rpow.mpr hs
    have h' := (summable_nat_add_iff 1).mpr h
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;>
      simpa only [b, Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), Nat.cast_add, Nat.cast_one] using h'
  have hrewrite (k : ℤ) : f k = (min (q : ℝ) (b k))^2 * b k^s := by
    dsimp only [f, derivativeBinProfile, s, b]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), Nat.cast_ofNat, mul_comm (η - 1)]
  have hdom (k : ℤ) : f k ≤ (q : ℝ)^2 * b k^s := by
    rw [hrewrite]
    gcongr
    exact min_le_left _ _
  have hf : Summable f := Summable.of_nonneg_of_le (fun k => sq_nonneg _) hdom
    (hsummable.mul_left ((q : ℝ)^2))
  refine ⟨hf, ?_⟩
  have hm (k : ℤ) : k ∈ L ↔ k.natAbs ≤ q := by
    dsimp only [L]
    rw [mem_Icc, ← abs_le, ← Int.natCast_natAbs]
    exact Int.ofNat_le
  have hi (k : ℤ) (hk : k ∈ L) : b k ≤ 2*(q : ℝ) := by
    have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    dsimp [b]
    rw [habs]
    have h₁ : (k.natAbs : ℝ) ≤ q := by exact_mod_cast (hm k).mp hk
    have h₂ : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hL (k : ℤ) (hk : k ∈ L) : f k ≤ ((2 : ℝ)*(q : ℝ))^(2*η) := by
    rw [hrewrite]
    calc
      _ ≤ (b k)^2 * b k^s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀
          (le_min (Nat.cast_nonneg _) (hb _).le) (min_le_right _ _) _) (rpow_nonneg (hb _).le _)
      _ = (b k)^(2*η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (hb _)]
        congr 1
        push_cast
        dsimp [s]
        ring
      _ ≤ _ := Real.rpow_le_rpow (hb _).le (hi k hk) (by positivity)
  let g (k : ℤ) := if k ∈ L then ((2 : ℝ)*(q : ℝ))^(2*η) else 0
  let t (k : ℤ) := if k.natAbs ≤ q then 0 else b k^s
  have hg : Summable g := summable_of_ne_finset_zero (s := L) (fun k hk => ite_eq_right hk)
  have ht : Summable t :=
    Summable.of_nonneg_of_le (fun k => by dsimp [t]; split <;> positivity)
      (fun k => by dsimp [t]; split
                   · exact rpow_nonneg (hb k).le _
                   · exact le_rfl) hsummable
  have hG : (∑' k, g k) ≤ 3 * 2^(2*η) * (q : ℝ)^(1+2*η) := by
    rw [tsum_eq_sum (s := L) (fun k hk => ite_eq_right hk)]
    simp only [sum_ite_mem, inter_self, sum_const, nsmul_eq_mul]
    have hcard : (L.card : ℝ) ≤ 3 * q := by
      have hc : L.card ≤ 3*q := by
        dsimp [L]
        rw [Int.card_Icc]
        omega
      exact_mod_cast hc
    rw [Real.mul_rpow (by norm_num) hqr.le, Real.rpow_add hqr, Real.rpow_one]
    nlinarith only [mul_le_mul_of_nonneg_right hcard (show 0 ≤ (2 : ℝ)^(2*η)*(q:ℝ)^(2*η) by positivity)]
  have hT : (q : ℝ)^2 * (∑' k, t k) ≤ (2 / (1-2*η)) * (q : ℝ)^(1+2*η) := by
    have h := signed_bin_tail_rpow q hq hs
    change (∑' k, t k) ≤ _ at h
    refine (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq ?_
    rw [show s+1 = 2*η-1 by dsimp [s]; ring, show -(2*η-1) = 1-2*η by ring]
    have hr : (q : ℝ)^2 * (q : ℝ)^(2*η-1) = (q : ℝ)^(1+2*η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hqr]
      congr 1
      push_cast
      ring
    calc
      _ = (2 / (1-2*η)) * ((q : ℝ)^2 * (q : ℝ)^(2*η-1)) := by ring
      _ = _ := by rw [hr]
  have hsum := hf.tsum_le_tsum (fun k => show f k ≤ g k + (q : ℝ)^2 * t k by
    by_cases hk : k ∈ L
    · simpa only [g, t, ite_eq_left hk, ite_eq_left ((hm k).mp hk), mul_zero, add_zero] using hL k hk
    · have hkn := mt (hm k).mpr hk
      simpa only [g, t, ite_eq_right hk, ite_eq_right hkn, zero_add] using hdom k)
    (hg.add (ht.mul_left ((q : ℝ)^2)))
  rw [Summable.tsum_add hg (ht.mul_left ((q : ℝ)^2)), tsum_mul_left] at hsum
  exact hsum.trans ((add_le_add hG hT).trans_eq (by ring))

private theorem derivative_bin_mass_le {T : Finset ℕ} {a : ℕ → ℂ} {γ : ℕ → ℝ}
    {weight : ℕ → ℝ} {C D η : ℝ} {q : ℕ}
    (hC : 0 ≤ C) (hq : 0 < q) (hweight : ∀ i, 0 ≤ weight i)
    (hmass : ∀ k, ∑ i ∈ T with frequencyBin (γ i) = k, weight i ≤
      D * (|(k : ℝ)| + 1) ^ (η-1))
    (ha : ∀ i, ‖a i‖ ≤ C * weight i)
    (hphase : ∀ i, ‖phaseDerivCoeff γ a i‖ ≤ (C*q) * weight i) :
    ∀ k, binMass T γ (phaseDerivCoeff γ a) k ≤ (C*D) * derivativeBinProfile q η k := by
  intro k
  let b := |(k : ℝ)| + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hpoint (i : ℕ) (hi : i ∈ T.filter (fun i => frequencyBin (γ i) = k)) :
      ‖phaseDerivCoeff γ a i‖ ≤ (C * min (q : ℝ) b) * weight i := by
    have hbin := mem_frequencyBin (γ i)
    rw [(Finset.mem_filter.mp hi).2] at hbin
    have hfreq : |γ i| ≤ b := by
      have hlow := hbin.1
      have hhigh := hbin.2
      have hklo := neg_le_abs (k : ℝ)
      have hkhi := le_abs_self (k : ℝ)
      apply abs_le.mpr
      dsimp [b]
      constructor <;> linarith
    have hl : ‖phaseDerivCoeff γ a i‖ ≤ (C*b) * weight i := by
      simp only [phaseDerivCoeff, norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
        Real.norm_eq_abs]
      exact (mul_le_mul (ha i) hfreq (abs_nonneg _) (mul_nonneg hC (hweight i))).trans_eq (by ring)
    by_cases h : (q : ℝ) ≤ b
    · rw [min_eq_left h]
      exact hphase i
    · rw [min_eq_right (le_of_not_ge h)]
      exact hl
  unfold binMass
  calc
    _ ≤ ∑ i ∈ T with frequencyBin (γ i) = k, (C * min (q : ℝ) b) * weight i :=
      Finset.sum_le_sum hpoint
    _ ≤ (C * min (q : ℝ) b) * (D * b^(η-1)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hmass k) (mul_nonneg hC (le_min hqr.le hb.le))
    _ = _ := by dsimp only [derivativeBinProfile, b]; ring

private theorem slab_sum_of_local_integrals
    {T S : Finset ℕ} {γ v : ℕ → ℝ} {a : ℕ → ℕ → ℂ}
    {p q : ℕ} {δ c K J : ℝ} (hS : S ⊆ Finset.Icc p q)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hq : 0 < q)
    (hwindow : ∀ n ∈ S, v n ∈ Set.Icc (c-1/2) (c+1/2))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |v i-v j|)
    (hlocal : ∀ (b : ℕ → ℂ) (scale : ℝ), 0 < scale →
      (∀ i, ‖b i‖ ≤ scale * (‖actualZero i‖)⁻¹) →
      (∀ i, ‖phaseDerivCoeff γ b i‖ ≤ (scale*q) * (‖actualZero i‖)⁻¹) →
      (∫ z in Set.Icc (c-1) (c+1), ‖finiteModes T γ b z‖) ≤ K*scale ∧
      (∫ z in Set.Icc (c-1) (c+1), ‖finiteModes T γ (phaseDerivCoeff γ b) z‖) ≤ J*scale)
    (hfirst : ∀ i, ‖a p i‖ ≤ 2 * (‖actualZero i‖)⁻¹)
    (hfirst' : ∀ i, ‖phaseDerivCoeff γ (a p) i‖ ≤ (2*(q : ℝ)) * (‖actualZero i‖)⁻¹)
    (hincr : ∀ r ∈ Finset.Ico p q, ∀ i,
      ‖a (r+1) i - a r i‖ ≤ (4/(q : ℝ)) * (‖actualZero i‖)⁻¹)
    (hincr' : ∀ r ∈ Finset.Ico p q, ∀ i,
      ‖phaseDerivCoeff γ (fun j => a (r+1) j - a r j) i‖ ≤
        ((4/(q : ℝ))*(q : ℝ)) * (‖actualZero i‖)⁻¹) :
    (∑ n ∈ S, ‖finiteModes T γ (a n) (v n)‖) ≤ 6*K / δ + 6*J := by
  let f (n : ℕ) := finiteModes T γ (a n)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hbase : ∑ n ∈ S, ‖f p (v n)‖ ≤ (K*2)/δ + J*2 := by
    obtain ⟨hU, hV⟩ := hlocal (a p) 2 (by norm_num) hfirst hfirst'
    exact separated_mode_samples_le hδ hδ₁ hwindow hsep hU hV
  have hdiff : ∀ r ∈ Finset.Ico p q,
      ∑ n ∈ S, ‖f (r+1) (v n) - f r (v n)‖ ≤ (K*(4/q))/δ + J*(4/q) := by
    intro r hr
    obtain ⟨hU, hV⟩ := hlocal (fun i => a (r+1) i - a r i) (4/q) (by positivity)
      (hincr r hr) (hincr' r hr)
    calc
      _ = ∑ n ∈ S, ‖finiteModes T γ (fun i => a (r+1) i - a r i) (v n)‖ := by
        apply Finset.sum_congr rfl
        intro n _
        congr 1
        unfold f finiteModes
        rw [← Finset.sum_sub_distrib]
        simp only [sub_mul]
      _ ≤ _ := separated_mode_samples_le hδ hδ₁ hwindow hsep hU hV
  have hc : ((Finset.Ico p q).card : ℝ) ≤ q := by
    exact_mod_cast (show (Finset.Ico p q).card ≤ q by rw [Nat.card_Ico]; omega)
  refine (varying_sample_sum_le (fun n hn => hS hn) hbase hdiff).trans ?_
  calc
    _ ≤ (K*2)/δ + J*2 + (q : ℝ) * ((K*(4/q))/δ + J*(4/q)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = _ := by field_simp; ring

/-- The high-frequency contribution retains the actual separation of the degree samples. -/
theorem masked_occurrence_tail_of_exact_spacing (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q H : ℕ), 3 ≤ q → 0 < H →
      ∀ u : ℝ, (q : ℝ) ≤ u → ∀ T : Finset ℕ,
      (∑ n ∈ Finset.Icc ((q+1)/2) q,
        Real.exp (-(2*u/(q : ℝ)-u/(n : ℝ))/2) *
          ‖finiteModes (T.filter (fun i => H < (frequencyBin (occurrenceFrequency i)).natAbs))
            occurrenceFrequency (rootCoeff n) (u/(n : ℝ))‖) ≤
        C * ((1 + (q : ℝ)^2 / u) * (H : ℝ)^(η-1/2) + (q : ℝ)^(1/2+η)) := by
  obtain ⟨D, hD, hmass⟩ := occurrence_bin_power_majorant_at hRH hη
  obtain ⟨G, hG, hinter⟩ := exists_local_mode_integral_le_square_mass
  let d := 1 - Real.exp (-1/2)
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  let R := 2 / (1-2*η)
  let W : ℝ := 3 * 2^(2*η) + R
  have hR : 0 < R := div_pos (by norm_num) (by linarith)
  have hW : 0 < W := by dsimp only [W]; positivity
  let P := 6 * G * D * max (Real.sqrt R) (Real.sqrt W) / d
  refine ⟨P, by dsimp [P]; positivity, fun q H hq hH u hu T => ?_⟩
  let p := (q+1)/2
  let δ := min 1 (u/(q : ℝ)^2)
  let L : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  let F := T.filter (fun i => (frequencyBin (occurrenceFrequency i)).natAbs > H)
  let b (k : ℤ) := D*(|(k : ℝ)|+1)^(η-1)
  let bTail (k : ℤ) := if k ∈ L then 0 else b k
  let K := G*D*Real.sqrt R*(H : ℝ)^(η-1/2)
  let J := G*D*Real.sqrt W*(q : ℝ)^(1/2+η)
  have hp : 0 < p := by dsimp [p]; omega
  have hpq : p ≤ q := by dsimp [p]; omega
  have hpHalf : (q : ℝ)/2 ≤ p := by
    have hnat : q ≤ 2*p := by dsimp [p]; omega
    have hreal : (q : ℝ) ≤ 2*(p : ℝ) := by exact_mod_cast hnat
    linarith
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.trans_le hpq
  have hu0 := hq0.trans_le hu
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hL (k : ℤ) : k ∈ L ↔ k.natAbs ≤ H := by
    dsimp only [L]
    rw [Finset.mem_Icc, ← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
  have hF : F = T.filter (fun i => frequencyBin (occurrenceFrequency i) ∉ L) := by
    ext i
    simp [F, hL, not_le]
  have hfb (k : ℤ) : ∑ i ∈ F with frequencyBin (occurrenceFrequency i) = k,
      (‖actualZero i‖)⁻¹ ≤ bTail k := by
    rw [hF]
    exact occurrence_compl_bin_majorant L T (hmass T) k
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
    by_cases hk : k ∈ L
    · simpa [bTail, hk] using sq_nonneg (b k)
    · simp [bTail, hk]
  have hshape (k : ℤ) : bTail k ^ 2 =
      D^2*(if k.natAbs ≤ H then 0 else (|(k : ℝ)|+1)^(2*(η-1))) := by
    by_cases hk : k ∈ L
    · simp [bTail, hk, (hL k).mp hk]
    · have hk' : ¬ k.natAbs ≤ H := mt (hL k).mpr hk
      simp only [bTail, ite_eq_right hk, ite_eq_right hk', b, mul_pow]
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
  have hvalue : Real.sqrt (∑' k : ℤ, bTail k ^ 2) ≤ D*Real.sqrt R*(H : ℝ)^(η-1/2) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, hsq.trans_eq ?_⟩
    have hs : ((H : ℝ)^(η-1/2))^2 = (H : ℝ)^(2*η-1) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg H)]
      congr 1
      push_cast
      ring
    simp only [mul_pow, Real.sq_sqrt hR.le, hs]
    ring
  obtain ⟨hderivSum, hderivSq⟩ := derivative_bin_square_budget hη hηhalf (by omega : 0 < q)
  have hderiv : Real.sqrt (∑' k : ℤ, derivativeBinProfile q η k ^ 2) ≤
      Real.sqrt W*(q : ℝ)^(1/2+η) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, hderivSq.trans_eq ?_⟩
    have hs : ((q : ℝ)^(1/2+η))^2 = (q : ℝ)^(1+2*η) := by
      rw [← Real.rpow_mul_natCast hq0.le]
      congr 1
      push_cast
      ring
    simp only [mul_pow, Real.sq_sqrt hW.le, hs]
    rfl
  have hslab (S : Finset ℕ) (c : ℝ) (hS : S ⊆ Finset.Icc p q)
      (hwindow : ∀ n ∈ S, u/(n : ℝ) ∈ Set.Icc (c-1/2) (c+1/2)) :
      (∑ n ∈ S, ‖finiteModes F occurrenceFrequency (rootCoeff n) (u/(n : ℝ))‖) ≤
        6*K/δ + 6*J := by
    have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |u/(i : ℝ)-u/(j : ℝ)| := by
      intro i hi j hj hij
      have hi' := Finset.mem_Icc.mp (hS hi)
      have hj' := Finset.mem_Icc.mp (hS hj)
      exact (min_le_right _ _).trans (root_coord_exact_separation hu0.le
        (hp.trans_le hi'.1) (hp.trans_le hj'.1) hi'.2 hj'.2 hij)
    refine slab_sum_of_local_integrals hS hδ (min_le_left _ _) hK hJ (by omega)
      hwindow hsep ?_ (occurrence_coeff_le hRH hp₁) ?_ ?_ ?_
    · intro coeff scale hs hcoeff hphase
      have hv := hinter bTail hsum F occurrenceFrequency coeff scale hs
        (occurrence_bin_majorant hs.le hfb hcoeff) c
      have hdv := hinter (derivativeBinProfile q η) hderivSum F occurrenceFrequency
        (phaseDerivCoeff occurrenceFrequency coeff) (scale*D) (mul_pos hs hD)
        (derivative_bin_mass_le hs.le (by omega) (fun _ => by positivity)
          (hmass F) hcoeff hphase) c
      constructor
      · refine hv.trans ?_
        dsimp only [K]
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvalue hG.le) hs.le
        exact h.trans_eq (by ring)
      · refine hdv.trans ?_
        dsimp only [J]
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hderiv hG.le) (mul_nonneg hs.le hD.le)
        exact h.trans_eq (by ring)
    · intro i
      exact (occurrence_coeff_phase_le (by positivity : (0 : ℝ) ≤ p) i).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · intro n hn i
      have hn' : (p : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      simpa only [Nat.cast_add, Nat.cast_one, occurrenceIncrement] using
        occurrenceIncrement_le hRH (hp₁.trans hn') hq0 (hpHalf.trans hn') i
    · intro n hn i
      have hn' : (p : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      simp only [Nat.cast_add, Nat.cast_one]
      change ‖phaseDerivCoeff occurrenceFrequency (occurrenceIncrement n) i‖ ≤ _
      refine (occurrenceIncrement_phase_le hRH (hp₁.trans hn') i).trans ?_
      rw [div_mul_cancel₀ _ hq0.ne']
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
  have hweighted := occurrence_weighted_finite_of_slab_bound hq hu0.le
    (show 0 ≤ 6*K/δ+6*J by positivity) F hslab
  have hδinv : δ⁻¹ ≤ 1 + (q : ℝ)^2 / u := by
    dsimp only [δ]
    by_cases hx : u/(q : ℝ)^2 ≤ 1
    · rw [min_eq_right hx, inv_div]
      linarith
    · rw [min_eq_left (le_of_not_ge hx), inv_one]
      exact le_add_of_nonneg_right (by positivity)
  have hRmax : Real.sqrt R ≤ max (Real.sqrt R) (Real.sqrt W) := le_max_left _ _
  have hWmax : Real.sqrt W ≤ max (Real.sqrt R) (Real.sqrt W) := le_max_right _ _
  refine hweighted.trans ?_
  rw [div_eq_mul_inv (6*K) δ]
  apply (div_le_iff₀ hd).mpr
  have hr : 6 * K * δ⁻¹ ≤
      (6 * G * D * max (Real.sqrt R) (Real.sqrt W)) *
        ((1 + (q : ℝ)^2/u) * (H : ℝ)^(η-1/2)) := by
    dsimp only [K]
    calc
      _ ≤ 6 * (G*D*Real.sqrt R*(H : ℝ)^(η-1/2)) * (1+(q : ℝ)^2/u) :=
        mul_le_mul_of_nonneg_left hδinv (by positivity)
      _ = (6*G*D*Real.sqrt R)*((1+(q : ℝ)^2/u)*(H : ℝ)^(η-1/2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRmax (by positivity)) (by positivity)
  have hj : 6 * J ≤
      (6 * G * D * max (Real.sqrt R) (Real.sqrt W)) * (q : ℝ)^(1/2+η) := by
    dsimp only [J]
    rw [show 6 * (G*D*Real.sqrt W*(q : ℝ)^(1/2+η)) =
      (6*G*D*Real.sqrt W)*(q : ℝ)^(1/2+η) by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWmax (by positivity))
      (by positivity)
  exact (add_le_add hr hj).trans_eq (by dsimp [P]; field_simp)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
