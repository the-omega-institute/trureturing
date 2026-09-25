/- GID: D5/S3/Estimation/SequentialDecisionRisk/UniformPosteriorOdds
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/UniformPosteriorOdds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal finite variance bounds for actual posterior log odds. -/

import Mathlib
import D5.S3.Analytic.RealRootedCoefficientNewton
import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open Finset
open scoped BigOperators
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds

/-- Elementary symmetric coefficients of positive odds. -/
def elem {α : Type*} (w : α → ℝ) (s : Finset α) (k : ℕ) : ℝ :=
  ∑ a ∈ s.powersetCard k, ∏ i ∈ a, w i

/-- Mean of independent Bernoulli variables parameterized by their odds. -/
def mean {α : Type*} (w : α → ℝ) (s : Finset α) : ℝ :=
  ∑ i ∈ s, w i / (1 + w i)

/-- Variance of the independent Bernoulli sum parameterized by its odds. -/
def variance {α : Type*} (w : α → ℝ) (s : Finset α) : ℝ :=
  ∑ i ∈ s, w i / (1 + w i)^2

/-- Universal finite log-odds approximation for both actual compensated observation laws.
The constants can be chosen as four, independently of all model and observation parameters. -/
theorem result : ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
    ∀ (M q s : ℕ) (r : ℝ), 1 ≤ q → q < M → 0 < r → r < 1 →
      compensation M q r < 1 → ∀ (e : Experiment) (o : Obs M s e) (t : ℝ), 0 < t →
      let B0 : ℝ := ((M-q : ℕ) : ℝ) / (q : ℝ)
      let p := fun i : Fin M => t*weight q r e o i/(B0+t*weight q r e o i)
      (∑ i, p i) = (q : ℝ) → V0 ≤ ∑ i, p i*(1-p i) →
      ∀ i : Fin M, 0 < inclusion q r e o i ∧ inclusion q r e o i < 1 ∧
        |Real.log (inclusion q r e o i/(1-inclusion q r e o i)) -
          (score q r e o i-Real.log B0+Real.log t)| ≤ C/(∑ i, p i*(1-p i)) := by
  classical
  have adjacent {α : Type} [DecidableEq α] (w : α → ℝ) (s : Finset α) (k : ℕ)
      (hw : ∀ i ∈ s, 0 < w i) (hk : k + 1 ≤ s.card)
      (hm0 : (k : ℝ) ≤ mean w s) (hm1 : mean w s ≤ k + 1)
      (hv : 2 ≤ variance w s) :
      |Real.log (elem w s k / elem w s (k+1))| ≤ 2 / variance w s := by
    classical
    have e0 (w : α → ℝ) (s : Finset α) : elem w s 0 = 1 := by simp [elem]
    have enonneg (w : α → ℝ) (s : Finset α) (k : ℕ)
        (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ elem w s k := by
      apply sum_nonneg
      intro a ha
      exact prod_nonneg (fun i hi => hw i ((mem_powersetCard.mp ha).1 hi))
    have epos (w : α → ℝ) (s : Finset α) (k : ℕ)
        (hw : ∀ i ∈ s, 0 < w i) (hk : k ≤ s.card) : 0 < elem w s k := by
      apply sum_pos
      · intro a ha
        exact prod_pos (fun i hi => hw i ((mem_powersetCard.mp ha).1 hi))
      · exact powersetCard_nonempty.mpr hk
    have eins (w : α → ℝ) (s : Finset α) (i : α) (hi : i ∉ s) (k : ℕ) :
        elem w (insert i s) (k+1) = elem w s (k+1) + w i * elem w s k := by
      unfold elem
      rw [powersetCard_succ_insert hi, sum_union]
      · rw [mul_sum]
        congr 1
        rw [sum_image]
        · apply sum_congr rfl
          intro a ha
          rw [prod_insert (fun h => hi ((mem_powersetCard.mp ha).1 h))]
        · intro a ha b hb hab
          have hia : i ∉ a := fun h => hi ((mem_powersetCard.mp ha).1 h)
          have hib : i ∉ b := fun h => hi ((mem_powersetCard.mp hb).1 h)
          simpa [hia, hib] using congrArg (fun a : Finset α => a.erase i) hab
      · apply disjoint_left.mpr
        intro a ha hb
        obtain ⟨b, hb, rfl⟩ := mem_image.mp hb
        exact hi ((mem_powersetCard.mp ha).1 (mem_insert_self _ _))
    have emoment (w : α → ℝ) (s : Finset α) (k : ℕ) :
        (∑ i ∈ s, w i * elem w (s.erase i) k) = (k+1 : ℝ) * elem w s (k+1) := by
      induction s using Finset.induction_on generalizing k with
      | empty => simp [elem, powersetCard_eq_empty.mpr (show (∅ : Finset α).card < k+1 by simp)]
      | @insert a s ha ih =>
        rw [sum_insert ha, erase_insert ha]
        have he (i : α) (hi : i ∈ s) : (insert a s).erase i = insert a (s.erase i) :=
          erase_insert_of_ne (Ne.symm (ne_of_mem_of_not_mem hi ha))
        cases k with
        | zero =>
          simp only [e0, mul_one, Nat.cast_zero, zero_add, one_mul]
          rw [eins w s a ha 0, e0]
          simpa [e0, mul_one, add_comm] using congrArg (fun x : ℝ => w a + x) (ih 0)
        | succ k =>
          have hs : (∑ i ∈ s, w i * elem w ((insert a s).erase i) (k+1)) =
              (∑ i ∈ s, w i * elem w (s.erase i) (k+1)) +
                w a * (∑ i ∈ s, w i * elem w (s.erase i) k) := by
            rw [mul_sum, ← sum_add_distrib]
            apply sum_congr rfl
            intro i hi
            rw [he i hi, eins w (s.erase i) a (fun h => ha (mem_of_mem_erase h)) k]
            ring
          rw [hs, ih (k+1), ih k, eins w s a ha (k+1)]
          push_cast
          ring
    have newton (w : α → ℝ) (s : Finset α) (k : ℕ) :
        elem w s k * elem w s (k+2) ≤ (elem w s (k+1))^2 := by
      let m := s.val.map w
      have he (j : ℕ) : m.esymm j = elem w s j := Finset.esymm_map_val w s j
      rw [← he, ← he, ← he]
      by_cases hn : k+2 ≤ m.card
      · have h := D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm m k
        have hc : (k : ℝ)+2 ≤ m.card := by exact_mod_cast hn
        have hp : 0 < ((k : ℝ)+2)*((m.card : ℝ)-k) := mul_pos (by positivity) (by linarith)
        have hd : ((k : ℝ)+1)*((m.card : ℝ)-k-1) ≤ ((k : ℝ)+2)*((m.card : ℝ)-k) := by nlinarith
        exact (mul_le_mul_iff_right₀ hp).mp (h.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg _)))
      · have hz : m.esymm (k+2) = 0 := by simp [Multiset.esymm, show m.card < k+2 by omega]
        rw [hz, mul_zero]
        exact sq_nonneg _
    -- A tie of adjacent masses traps the mean between their indices.
    have tie_mean (w : α → ℝ) (s : Finset α) (k : ℕ)
        (hw : ∀ i ∈ s, 0 < w i) (hk : k+1 ≤ s.card)
        (ht : elem w s k = elem w s (k+1)) :
        (k : ℝ) ≤ mean w s ∧ mean w s ≤ k+1 := by
      have hA : 0 < elem w s k := epos w s k hw (by omega)
      have hpoint (i : α) (hi : i ∈ s) :
          w i / (1+w i) * elem w s k ≤ w i * elem w (s.erase i) k := by
        have hwi := hw i hi
        have hden : 0 < 1+w i := by linarith
        have hb : 0 ≤ elem w (s.erase i) k :=
          enonneg w _ _ (fun j hj => (hw j (mem_of_mem_erase hj)).le)
        have he := eins w (s.erase i) i (notMem_erase _ _) k
        rw [insert_erase hi] at he
        have hc : elem w (s.erase i) (k+1) ≤ elem w (s.erase i) k := by
          cases k with
          | zero =>
            rw [e0]
            simp only [e0] at ht he
            linarith
          | succ k =>
            have he' := eins w (s.erase i) i (notMem_erase _ _) k
            rw [insert_erase hi] at he'
            have hn := newton w (s.erase i) k
            have ha : 0 ≤ elem w (s.erase i) k :=
              enonneg w _ _ (fun j hj => (hw j (mem_of_mem_erase hj)).le)
            have hc0 : 0 ≤ elem w (s.erase i) (k+2) :=
              enonneg w _ _ (fun j hj => (hw j (mem_of_mem_erase hj)).le)
            have ht' : elem w (s.erase i) (k+1) + w i*elem w (s.erase i) k =
                elem w (s.erase i) (k+2) + w i*elem w (s.erase i) (k+1) := by
              simpa [he', he] using ht
            by_contra h
            have hbc : elem w (s.erase i) (k+1) < elem w (s.erase i) (k+2) := lt_of_not_ge h
            have hab : elem w (s.erase i) (k+1) < elem w (s.erase i) k := by nlinarith
            nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)]
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        rw [ht, he]
        nlinarith
      have upper : mean w s ≤ k+1 := by
        apply (mul_le_mul_iff_left₀ hA).mp
        rw [mean, sum_mul]
        conv_rhs => rw [ht]
        rw [← emoment w s k]
        exact sum_le_sum hpoint
      constructor
      · cases k with
        | zero =>
          simpa only [Nat.cast_zero, mean] using
            (sum_nonneg (fun i hi => div_nonneg (hw i hi).le
              (show 0 ≤ 1+w i by linarith [hw i hi])))
        | succ k =>
          have hlow (i : α) (hi : i ∈ s) :
              w i * elem w (s.erase i) k ≤ w i/(1+w i)*elem w s (k+1) := by
            have hwi := hw i hi
            have hden : 0 < 1+w i := by linarith
            have he := eins w (s.erase i) i (notMem_erase _ _) k
            have he' := eins w (s.erase i) i (notMem_erase _ _) (k+1)
            rw [insert_erase hi] at he he'
            have hn := newton w (s.erase i) k
            have ha := enonneg w (s.erase i) k (fun j hj => (hw j (mem_of_mem_erase hj)).le)
            have hb := enonneg w (s.erase i) (k+1) (fun j hj => (hw j (mem_of_mem_erase hj)).le)
            have hc := enonneg w (s.erase i) (k+2) (fun j hj => (hw j (mem_of_mem_erase hj)).le)
            have hab : elem w (s.erase i) k ≤ elem w (s.erase i) (k+1) := by
              by_contra h
              have hab' := lt_of_not_ge h
              have hbc : elem w (s.erase i) (k+1) < elem w (s.erase i) (k+2) := by nlinarith [ht]
              nlinarith [mul_pos (sub_pos.mpr hab') (sub_pos.mpr hbc)]
            rw [div_mul_eq_mul_div, le_div_iff₀ hden, he]
            nlinarith
          apply (mul_le_mul_iff_left₀ hA).mp
          rw [mean, sum_mul, Nat.cast_add, Nat.cast_one, ← emoment w s k]
          exact sum_le_sum hlow
      · exact upper
    have escale (a : ℝ) (j : ℕ) : elem (fun i => a*w i) s j = a^j * elem w s j := by
      unfold elem
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hb).2]
    -- This explicit common tilt equalizes the two adjacent coefficients.
    let a := elem w s k / elem w s (k+1)
    have hp := epos w s k hw (by omega)
    have hp' := epos w s (k+1) hw hk
    have ha : 0 < a := div_pos hp hp'
    have ht : elem (fun i => a*w i) s k = elem (fun i => a*w i) s (k+1) := by
      rw [escale, escale, pow_succ]
      dsimp [a]
      field_simp
    obtain ⟨ht0,ht1⟩ := tie_mean (fun i => a*w i) s k (fun i hi => mul_pos ha (hw i hi)) hk ht
    have hV : 0 < variance w s := by linarith
    have hmu : mean (fun i => a*w i) s - mean w s ≤ 1 := by linarith
    have hmu' : mean w s - mean (fun i => a*w i) s ≤ 1 := by linarith
    -- Mean displacement is at most one; variance then controls the tilt logarithm.
    by_cases ha1 : 1 ≤ a
    · have hshift : (a-1)*variance w s ≤ a*(mean (fun i => a*w i) s - mean w s) := by
        simp only [variance, mean]
        rw [← sum_sub_distrib]
        simp only [mul_sum]
        apply sum_le_sum
        intro i hi
        have hx := hw i hi
        have hd : 0 < 1+w i := by positivity
        have hd' : 0 < 1+a*w i := by positivity
        have he : (a-1)*(w i/(1+w i)^2) ≤ a*(a*w i/(1+a*w i)-w i/(1+w i)) := by
          field_simp
          nlinarith [mul_nonneg (sq_nonneg (a-1)) hx.le]
        exact he
      have hprod : (a-1)*variance w s ≤ a := by nlinarith [mul_le_mul_of_nonneg_left hmu ha.le]
      have ha2 : a ≤ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hv)]
      rw [abs_of_nonneg (Real.log_nonneg ha1)]
      apply (le_div_iff₀ hV).mpr
      have hl := Real.log_le_sub_one_of_pos ha
      nlinarith [mul_le_mul_of_nonneg_right hl hV.le]
    · have ha1' : a ≤ 1 := (lt_of_not_ge ha1).le
      have hshift : (1-a)*variance w s ≤ mean w s-mean (fun i => a*w i) s := by
        simp only [variance, mean]
        rw [← sum_sub_distrib]
        simp only [mul_sum]
        apply sum_le_sum
        intro i hi
        have hx := hw i hi
        have hd : 0 < 1+w i := by positivity
        have hd' : 0 < 1+a*w i := by positivity
        have he : (1-a)*(w i/(1+w i)^2) ≤ w i/(1+w i)-a*w i/(1+a*w i) := by
          field_simp
          nlinarith [mul_nonneg (sq_nonneg (1-a)) (sq_nonneg (w i))]
        exact he
      have hprod : (1-a)*variance w s ≤ 1 := hshift.trans hmu'
      have ha2 : 1/2 ≤ a := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1') (sub_nonneg.mpr hv)]
      have hi2 : a⁻¹ ≤ 2 := by
        rw [inv_eq_one_div, div_le_iff₀ ha]
        linarith
      have hiprod : (a⁻¹-1)*variance w s ≤ a⁻¹ := by
        apply (mul_le_mul_iff_right₀ ha).mp
        have he : a*((a⁻¹-1)*variance w s) = (1-a)*variance w s := by field_simp
        rw [he, mul_inv_cancel₀ ha.ne']
        exact hprod
      have hl : -Real.log a ≤ a⁻¹-1 := by
        simpa using Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
      rw [abs_of_nonpos (Real.log_nonpos ha.le ha1')]
      apply (le_div_iff₀ hV).mpr
      nlinarith [mul_le_mul_of_nonneg_right hl hV.le]
  refine ⟨4, by norm_num, 4, by norm_num, ?_⟩
  intro M q s r hq hqm hr hr1 ha1 e o t ht
  dsimp only
  let B0 : ℝ := ((M-q : ℕ) : ℝ) / (q : ℝ)
  let p := fun i : Fin M => t*weight q r e o i/(B0+t*weight q r e o i)
  change (∑ i, p i) = (q : ℝ) → 4 ≤ ∑ i, p i*(1-p i) → _
  intro hmean hvar
  have ha : 0 ≤ compensation M q r := by unfold compensation; positivity
  obtain ⟨hZ, hw, hpost, _⟩ :=
    (finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hb : 0 < B0 := div_pos (by exact_mod_cast (show 0 < M-q by omega)) hqpos
  let c := t/B0
  let w := fun i : Fin M => c*weight q r e o i
  have hc : 0 < c := div_pos ht hb
  have hwpos (i : Fin M) : 0 < w i := mul_pos hc (hw i).1
  have hp (i : Fin M) : p i = w i/(1+w i) := by
    dsimp [p, w, c]
    field_simp
  have hdw (i : Fin M) : 0 < 1+w i := by linarith [hwpos i]
  have hp0 (i : Fin M) : 0 < p i := by rw [hp]; exact div_pos (hwpos i) (hdw i)
  have hp1 (i : Fin M) : p i < 1 := by
    rw [hp, div_lt_one (hdw i)]
    linarith
  have hpv (i : Fin M) : p i*(1-p i) = w i/(1+w i)^2 := by
    rw [hp]
    field_simp [(hdw i).ne']
    ring
  have hsum (f : Finset (Fin M) → ℝ) :
      (∑ S : Support M q, f S.val) = ∑ S ∈ univ.powersetCard q, f S :=
    (sum_subtype _ (fun S => by simp) f).symm
  have hscale (S : Support M q) : (∏ i ∈ S.val, w i) = c^q * ∏ i ∈ S.val, weight q r e o i := by
    simp only [w, prod_mul_distrib, prod_const, S.property]
  have hZscale : elem w univ q = c^q * partition (q := q) r e o := by
    rw [elem, ← hsum (fun S => ∏ j ∈ S, w j)]
    simp only [hscale, ← mul_sum, partition]
  have hZpos : 0 < elem w univ q := by rw [hZscale]; positivity
  have hpostw (S : Support M q) : posterior r e o S = (∏ i ∈ S.val, w i)/elem w univ q := by
    rw [hpost, hscale, hZscale]
    field_simp
  have epos (u : Finset (Fin M)) (k : ℕ) (hk : k ≤ u.card) : 0 < elem w u k := by
    apply sum_pos
    · intro a ha
      exact prod_pos (fun i _ => hwpos i)
    · exact powersetCard_nonempty.mpr hk
  intro i
  let u := (univ : Finset (Fin M)).erase i
  let A := elem w u (q-1)
  let D := elem w u q
  have hcard : u.card = M-1 := by simp [u]
  have hA : 0 < A := epos u (q-1) (by rw [hcard]; omega)
  have hD : 0 < D := epos u q (by rw [hcard]; omega)
  have hmarked : (∑ S : Support M q, if i ∈ S.val then ∏ j ∈ S.val, w j else 0) = w i*A := by
    rw [hsum (fun S => if i ∈ S then ∏ j ∈ S, w j else 0), ← sum_filter]
    dsimp only [A, elem]
    rw [mul_sum]
    symm
    apply sum_bij (fun U _ => insert i U)
    · intro U hU
      obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hU
      have hiU : i ∉ U := fun h => (mem_erase.mp (hsub h)).1 rfl
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      exact ⟨by rw [card_insert_of_notMem hiU,hcard]; omega, mem_insert_self _ _⟩
    · intro U hU V hV heq
      have hiU : i ∉ U := fun h => (mem_erase.mp ((mem_powersetCard.mp hU).1 h)).1 rfl
      have hiV : i ∉ V := fun h => (mem_erase.mp ((mem_powersetCard.mp hV).1 h)).1 rfl
      simpa [hiU, hiV] using congrArg (fun T : Finset (Fin M) => T.erase i) heq
    · intro S hS
      obtain ⟨hS,hiS⟩ := mem_filter.mp hS
      refine ⟨S.erase i, mem_powersetCard.mpr ⟨?_, ?_⟩, insert_erase hiS⟩
      · intro j hj
        simpa [u] using (mem_erase.mp hj).1
      · rw [card_erase_of_mem hiS, (mem_powersetCard.mp hS).2]
    · intro U hU
      have hiU : i ∉ U := fun h => (mem_erase.mp ((mem_powersetCard.mp hU).1 h)).1 rfl
      rw [prod_insert hiU]
  have hunmarked : (∑ S : Support M q, if i ∉ S.val then ∏ j ∈ S.val, w j else 0) = D := by
    rw [hsum (fun S => if i ∉ S then ∏ j ∈ S, w j else 0), ← sum_filter]
    dsimp only [D, elem]
    congr 1
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hcard, hiS⟩
      exact ⟨by intro j hj; simpa [u] using ne_of_mem_of_not_mem hj hiS, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨hcard, fun h => (mem_erase.mp (hsub h)).1 rfl⟩
  have hsplit : elem w univ q = D + w i*A := by
    rw [← hunmarked, ← hmarked, ← sum_add_distrib, elem, ← hsum (fun S => ∏ j ∈ S, w j)]
    apply sum_congr rfl
    intro S _
    by_cases hiS : i ∈ S.val <;> simp [hiS]
  have hinc : inclusion q r e o i = w i*A/(D+w i*A) := by
    rw [inclusion]
    simp_rw [hpostw]
    have hi : (∑ S : Support M q, if i ∈ S.val then (∏ j ∈ S.val, w j)/elem w univ q else 0) =
        (∑ S : Support M q, if i ∈ S.val then ∏ j ∈ S.val, w j else 0)/elem w univ q := by
      rw [sum_div]
      apply sum_congr rfl
      intro S _
      split_ifs <;> simp
    rw [hi, hmarked, hsplit]
  have hwi := hwpos i
  have hden : 0 < D+w i*A := by positivity
  have hinc0 : 0 < inclusion q r e o i := by rw [hinc]; positivity
  have hinc1 : inclusion q r e o i < 1 := by
    rw [hinc, div_lt_one hden]
    linarith
  refine ⟨hinc0, hinc1, ?_⟩
  have hm : mean w u = (q : ℝ)-p i := by
    dsimp only [mean, u]
    simp_rw [← hp]
    rw [sum_erase_eq_sub (mem_univ i), hmean]
  have hv : variance w u = (∑ j, p j*(1-p j))-p i*(1-p i) := by
    dsimp only [variance, u]
    simp_rw [← hpv]
    rw [sum_erase_eq_sub (mem_univ i)]
  have hquarter : p i*(1-p i) ≤ 1/4 := by nlinarith [sq_nonneg (p i-1/2)]
  have hv2 : 2 ≤ variance w u := by rw [hv]; linarith
  have hqmcast : ((q-1 : ℕ) : ℝ) = (q : ℝ)-1 := by rw [Nat.cast_sub hq]; norm_num
  have hlocal : |Real.log (A/D)| ≤ 2/variance w u := by
    have hh := adjacent (α := Fin M) w u (q-1) (fun j _ => hwpos j) (by rw [hcard]; omega)
      (by rw [hqmcast, hm]; linarith [hp1 i])
      (by rw [hqmcast, hm]; linarith [hp0 i]) hv2
    simpa only [show q-1+1=q by omega] using hh
  have hlogw : Real.log (w i) = score q r e o i-Real.log B0+Real.log t := by
    rw [show w i = (t/B0)*weight q r e o i from rfl, Real.log_mul hc.ne' (hw i).1.ne',
      Real.log_div ht.ne' hb.ne', (hw i).2, Real.log_exp]
    ring
  have hodds : inclusion q r e o i/(1-inclusion q r e o i) = w i*(A/D) := by
    rw [hinc]
    field_simp [hD.ne', hden.ne']
    ring
  have herr : Real.log (inclusion q r e o i/(1-inclusion q r e o i)) -
      (score q r e o i-Real.log B0+Real.log t) = Real.log (A/D) := by
    rw [hodds, Real.log_mul (hwpos i).ne' (div_pos hA hD).ne', hlogw]
    ring
  change |Real.log (inclusion q r e o i/(1-inclusion q r e o i)) -
      (score q r e o i-Real.log B0+Real.log t)| ≤ 4/(∑ j, p j*(1-p j))
  rw [herr]
  apply hlocal.trans
  have hV : 0 < ∑ j, p j*(1-p j) := by linarith
  rw [div_le_div_iff₀ (by linarith : 0 < variance w u) hV]
  rw [hv]
  linarith

end D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds
