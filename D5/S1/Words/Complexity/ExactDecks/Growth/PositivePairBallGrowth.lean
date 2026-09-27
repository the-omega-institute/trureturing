/- GID: D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual positive-word cutoff balls have weighted Lyndon polynomial growth. -/

import D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.Growth.PositivePairBallGrowth

open scoped BigOperators
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Digits.ActualLyndonDirections
open D5.S1.Words.Complexity.PositivePairs.Digits.CentralDigitWords
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
open private scatteredCount_singleton_eq_count count_flatMap_replicate_of_nodup
  length_flatMap_replicate_le letterActualLyndonEquiv letterOrder letterBoxWord
  scaleDenominator fittingScale from
  D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall

variable {A : Type*}

/-- For every fixed positive cutoff degree and every finite linearly ordered
alphabet with at least two letters, the actual positive-word cutoff-Magnus ball
has the full weighted-Lyndon polynomial lower bound at every sufficiently large
radius.  The natural constant `C` represents the positive rational lower
constant `1 / C`. -/
theorem actual_positiveWordBall_weightedLyndon_lower_bound
    [Fintype A] [LinearOrder A] (hq : 2 ≤ Fintype.card A)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ C N : ℕ, 0 < C ∧
      ∀ n, N ≤ n →
        n ^ weightedLyndonExponent (A := A) r ≤
          C * (positiveWordBall (A := A) r n).card := by
  classical
  have mem_positiveWordBall_iff (degree radius : ℕ)
      (x : CutoffCoefficients A degree) :
      x ∈ positiveWordBall (A := A) degree radius ↔
        ∃ w : List A, w.length ≤ radius ∧ cutoffMagnus degree w = x := by
    simp [positiveWordBall]
  have letterOrder_nodup : (letterOrder (A := A)).Nodup := by
    simp [letterOrder]
  have mem_letterOrder (a : A) : a ∈ letterOrder (A := A) := by
    simp [letterOrder]
  have letterBoxWord_scatteredCount (t : ℕ)
      (digits : A → Fin (t + 1)) (a : A) :
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          [a] (letterBoxWord (A := A) t digits) = digits a := by
    rw [scatteredCount_singleton_eq_count]
    exact count_flatMap_replicate_of_nodup
      (letterOrder (A := A)) letterOrder_nodup
      (fun b ↦ (digits b : ℕ)) a (mem_letterOrder a)
  have letterBoxWord_length (t : ℕ) (digits : A → Fin (t + 1)) :
      (letterBoxWord (A := A) t digits).length ≤ Fintype.card A * t := by
    have h := length_flatMap_replicate_le
      (letterOrder (A := A)) (fun a ↦ (digits a : ℕ)) t
      (fun a _ ↦ Nat.le_of_lt_succ (digits a).2)
    simpa [letterBoxWord, letterOrder] using h
  have letterBox_cutoff_injective (t : ℕ) :
      Function.Injective (fun digits : A → Fin (t + 1) ↦
        cutoffMagnus 1 (letterBoxWord (A := A) t digits)) := by
    intro left right h
    funext a
    have hcoeff := congrFun h
      (⟨FreeMonoid.ofList [a], by simp [FreeMonoid.length]⟩ : CutoffWord A 1)
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom,
      magnusPolynomial_coeff_scatteredCount] at hcoeff
    have hcount :
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            [a] (letterBoxWord (A := A) t left) =
          D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            [a] (letterBoxWord (A := A) t right) := by
      have hq :
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              [a] (letterBoxWord (A := A) t left) : ℚ) =
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              [a] (letterBoxWord (A := A) t right) : ℚ) := by
        simpa using hcoeff
      exact_mod_cast hq
    rw [letterBoxWord_scatteredCount, letterBoxWord_scatteredCount] at hcount
    exact Fin.ext hcount
  have positiveWordBall_one_card_lower (t : ℕ) :
      (t + 1) ^ Fintype.card A ≤
        (positiveWordBall (A := A) 1 (Fintype.card A * t)).card := by
    let embed : (A → Fin (t + 1)) →
        ↑(positiveWordBall (A := A) 1 (Fintype.card A * t)) :=
      fun digits ↦ ⟨cutoffMagnus 1 (letterBoxWord (A := A) t digits),
        (mem_positiveWordBall_iff 1 (Fintype.card A * t) _).2
          ⟨letterBoxWord (A := A) t digits,
            letterBoxWord_length t digits, rfl⟩⟩
    have hinjective : Function.Injective embed := by
      intro left right heq
      apply letterBox_cutoff_injective t
      exact congrArg Subtype.val heq
    have hcard := Fintype.card_le_of_injective embed hinjective
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using hcard
  have actualLyndonCount_one :
      actualLyndonCount (A := A) 1 = Fintype.card A := by
    unfold actualLyndonCount
    exact (Fintype.card_congr letterActualLyndonEquiv).symm
  have weightedLyndonExponent_one :
      weightedLyndonExponent (A := A) 1 = Fintype.card A := by
    unfold weightedLyndonExponent
    rw [show 1 + 1 = 1 + 1 by rfl, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simpa using actualLyndonCount_one
  have weightedLyndonExponent_step (r : ℕ) (hr : 1 ≤ r) :
      weightedLyndonExponent (A := A) r =
        weightedLyndonExponent (A := A) (r - 1) +
          r * actualLyndonCount (A := A) r := by
    unfold weightedLyndonExponent
    have hrange : r - 1 + 1 = r := by omega
    rw [hrange, Finset.sum_range_succ]
  have positiveWordBall_mono (r left right : ℕ) (h : left ≤ right) :
      (positiveWordBall (A := A) r left).card ≤
        (positiveWordBall (A := A) r right).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨word, hlength, hcutoff⟩ :=
      (mem_positiveWordBall_iff r left x).mp hx
    exact (mem_positiveWordBall_iff r right x).2
      ⟨word, hlength.trans h, hcutoff⟩
  have self_lt_mul_div_add_one (n d : ℕ) (hd : 0 < d) :
      n < d * (n / d + 1) := by
    have hmod : n % d < d := Nat.mod_lt n hd
    nth_rewrite 1 [← Nat.div_add_mod n d]
    rw [Nat.mul_add]
    omega
  have positiveWordBall_one_polynomial :
      ∀ n,
        n ^ weightedLyndonExponent (A := A) 1 ≤
          (Fintype.card A) ^ weightedLyndonExponent (A := A) 1 *
            (positiveWordBall (A := A) 1 n).card := by
    intro n
    let q := Fintype.card A
    let t := n / q
    have hqpos : 0 < q := by omega
    have hn : n ≤ q * (t + 1) :=
      (self_lt_mul_div_add_one n q hqpos).le
    have hqt : q * t ≤ n := Nat.mul_div_le n q
    have hbox := positiveWordBall_one_card_lower t
    have hmono := positiveWordBall_mono 1 (q * t) n hqt
    rw [weightedLyndonExponent_one]
    calc
      n ^ q ≤ (q * (t + 1)) ^ q := Nat.pow_le_pow_left hn q
      _ = q ^ q * (t + 1) ^ q := by rw [Nat.mul_pow]
      _ ≤ q ^ q * (positiveWordBall (A := A) 1 (q * t)).card :=
        Nat.mul_le_mul_left _ hbox
      _ ≤ q ^ q * (positiveWordBall (A := A) 1 n).card :=
        Nat.mul_le_mul_left _ hmono
  have scaleDenominator_pos (r : ℕ) :
      0 < scaleDenominator (A := A) r := by
    simp [scaleDenominator]
  have scaleDenominator_ge_baseLength (r : ℕ) :
      baseLength (A := A) r ≤ scaleDenominator (A := A) r := by
    exact Nat.le_max_left _ _
  have fittingScale_length_le (r m : ℕ) :
      baseLength (A := A) r * (2 ^ fittingScale (A := A) r m - 1) ≤ m := by
    let d := scaleDenominator (A := A) r
    let t := fittingScale (A := A) r m
    have hd : 0 < d := scaleDenominator_pos r
    have hpow : 2 ^ t ≤ m / d + 1 := by
      dsimp only [t, fittingScale, d]
      exact Nat.pow_log_le_self 2 (Nat.add_one_ne_zero _)
    have hsub : 2 ^ t - 1 ≤ m / d := by
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_comm] using hpow
    calc
      baseLength (A := A) r * (2 ^ t - 1) ≤ d * (2 ^ t - 1) :=
        Nat.mul_le_mul_right _ (scaleDenominator_ge_baseLength r)
      _ ≤ d * (m / d) := Nat.mul_le_mul_left d hsub
      _ ≤ m := Nat.mul_div_le m d
  have fittingScale_quantitative (r m : ℕ) :
      m < 2 * scaleDenominator (A := A) r *
        2 ^ fittingScale (A := A) r m := by
    let d := scaleDenominator (A := A) r
    let t := fittingScale (A := A) r m
    have hd : 0 < d := scaleDenominator_pos r
    have hm : m < d * (m / d + 1) := self_lt_mul_div_add_one m d hd
    have hx : m / d + 1 < 2 ^ (Nat.log 2 (m / d + 1)).succ :=
      Nat.lt_pow_succ_log_self (by omega) _
    have hmul : d * (m / d + 1) <
        d * 2 ^ (Nat.log 2 (m / d + 1)).succ :=
      (Nat.mul_lt_mul_left hd).2 hx
    calc
      m < d * (m / d + 1) := hm
      _ < d * 2 ^ (Nat.log 2 (m / d + 1)).succ := hmul
      _ = 2 * d * 2 ^ t := by
        dsimp only [t, fittingScale, d]
        rw [pow_succ]
        ac_rfl
  have half_bounds (n : ℕ) (hn : 2 ≤ n) :
      let m := n / 2
      1 ≤ m ∧ n ≤ 3 * m ∧ 2 * m ≤ n := by
    let m := n / 2
    have hdecomp := Nat.div_add_mod n 2
    have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
    dsimp only [m]
    omega
  have digitCard_eq_scalePower (r t : ℕ) :
      digitBase r ^ (t * actualLyndonCount (A := A) r) =
        (2 ^ t) ^ (r * actualLyndonCount (A := A) r) := by
    unfold digitBase
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    congr 1
    ac_rfl
  have combine_polynomial_bounds
      (n m scale q r c previousBall ball three k : ℕ)
      (hnm : n ≤ three * m) (hns : n ≤ k * scale)
      (hprevious : m ^ q ≤ c * previousBall)
      (hstep : previousBall * scale ^ r ≤ ball) :
      n ^ (q + r) ≤ (three ^ q * k ^ r * c) * ball := by
    calc
      n ^ (q + r) = n ^ q * n ^ r := Nat.pow_add _ _ _
      _ ≤ (three * m) ^ q * (k * scale) ^ r :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hnm q)
          (Nat.pow_le_pow_left hns r)
      _ = (three ^ q * k ^ r) * (m ^ q * scale ^ r) := by
        simp only [Nat.mul_pow]
        ac_rfl
      _ ≤ (three ^ q * k ^ r) * ((c * previousBall) * scale ^ r) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hprevious)
      _ = (three ^ q * k ^ r) * (c * (previousBall * scale ^ r)) := by
        ac_rfl
      _ ≤ (three ^ q * k ^ r) * (c * ball) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hstep)
      _ = (three ^ q * k ^ r * c) * ball := by ac_rfl
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hrone : r = 1
      · subst r
        refine ⟨(Fintype.card A) ^
            weightedLyndonExponent (A := A) 1, 0, ?_, ?_⟩
        · positivity
        · intro n _
          exact positiveWordBall_one_polynomial n
      · have hr2 : 2 ≤ r := by omega
        have hrprev : 1 ≤ r - 1 := by omega
        obtain ⟨C, N, hC, hprevious⟩ :=
          ih (r - 1) (by omega) hrprev
        let Q := weightedLyndonExponent (A := A) (r - 1)
        let R := r * actualLyndonCount (A := A) r
        let d := scaleDenominator (A := A) r
        let K := 6 * d
        let Cnew := 3 ^ Q * K ^ R * C
        let Nnew := max 2 (2 * N)
        refine ⟨Cnew, Nnew, ?_, ?_⟩
        · have hd : 0 < d := scaleDenominator_pos r
          dsimp only [Cnew, K]
          positivity
        · intro n hn
          let m := n / 2
          let t := fittingScale (A := A) r m
          have hn2 : 2 ≤ n :=
            (Nat.le_max_left 2 (2 * N)).trans hn
          have hhalves := half_bounds n hn2
          have hmN : N ≤ m := by
            have h2N : 2 * N ≤ n :=
              (Nat.le_max_right 2 (2 * N)).trans hn
            have hdecomp := Nat.div_add_mod n 2
            have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
            dsimp only [m]
            omega
          have hIH : m ^ Q ≤
              C * (positiveWordBall (A := A) (r - 1) m).card := by
            exact hprevious m hmN
          have hdigit : baseLength (A := A) r * (2 ^ t - 1) ≤ m := by
            exact fittingScale_length_le r m
          have hfit :
              m + baseLength (A := A) r * (2 ^ t - 1) ≤ n := by
            have htwom : 2 * m ≤ n := hhalves.2.2
            omega
          have hcardStep := positiveWordBall_card_step r m t n hr2 hfit
          rw [digitCard_eq_scalePower] at hcardStep
          have hscale : m < 2 * d * 2 ^ t := by
            exact fittingScale_quantitative r m
          have hnK : n ≤ K * 2 ^ t := by
            have hthree : n ≤ 3 * m := hhalves.2.1
            have hmul : 3 * m < 3 * (2 * d * 2 ^ t) :=
              (Nat.mul_lt_mul_left (by omega : 0 < 3)).2 hscale
            have hle := hthree.trans hmul.le
            calc
              n ≤ 3 * (2 * d * 2 ^ t) := hle
              _ = K * 2 ^ t := by
                dsimp only [K]
                ring
          rw [weightedLyndonExponent_step r (by omega)]
          exact combine_polynomial_bounds n m (2 ^ t) Q R C
            (positiveWordBall (A := A) (r - 1) m).card
            (positiveWordBall (A := A) r n).card 3 K
            hhalves.2.1 hnK hIH hcardStep

end D5.S1.Words.Complexity.ExactDecks.Growth.PositivePairBallGrowth
