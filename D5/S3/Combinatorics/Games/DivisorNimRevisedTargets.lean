/- GID: D5/S3/Combinatorics/Games/DivisorNimRevisedTargets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimRevisedTargets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Revised depth-sensitive ceilings for the actual Divisor Nim game. -/

import D5.S3.Combinatorics.Games.DivisorNimFixedBoard

/-! Revised depth-sensitive bound for the actual Divisor Nim recurrence.
The proof uses the previously verified independent reference bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Games.DivisorNimGrundy
open D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic

def revisedCeiling (H k : ℕ) : ℕ := 2 * H - H / 2 ^ k + 1

def RevisedBoundStatement : Prop :=
  ∀ (P : Position) (H k : ℕ), Positive P → HasDepth P k →
    H ∈ P → (∀ h ∈ P, H ≤ h) → grundy P ≤ revisedCeiling H k

private theorem ceiling_mono (k : ℕ) : Monotone (fun H => revisedCeiling H k) := by
  apply monotone_nat_of_le_succ
  intro H
  have hdiv : (H + 1) / 2 ^ k ≤ H / 2 ^ k + 1 := by
    rw [Nat.succ_div]
    split_ifs <;> omega
  have hq := Nat.div_le_self H (2 ^ k)
  have hq' := Nat.div_le_self (H + 1) (2 ^ k)
  unfold revisedCeiling
  omega

private theorem ceiling_depth_mono (H : ℕ) : Monotone (revisedCeiling H) := by
  intro j k hjk
  have hd := Nat.div_le_div_left (a := H) (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hjk)
    (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ j)
  have hq := Nat.div_le_self H (2 ^ j)
  have hq' := Nat.div_le_self H (2 ^ k)
  unfold revisedCeiling
  omega

private theorem ceiling_step {H k : ℕ} (hd : 2 ^ (k + 1) ∣ H) :
    revisedCeiling H (k + 1) = revisedCeiling H k + H / 2 ^ (k + 1) := by
  obtain ⟨q, rfl⟩ := hd
  have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hp' : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide)
  have h1 : (2 ^ (k + 1) * q) / 2 ^ k = 2 * q := by
    rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ hp]
  have h2 : (2 ^ (k + 1) * q) / 2 ^ (k + 1) = q := Nat.mul_div_cancel_left _ hp'
  have hq : q ≤ 2 ^ (k + 1) * q := Nat.le_mul_of_pos_left q hp'
  unfold revisedCeiling
  rw [h1, h2]
  omega

/-- Save one exceptional removal when it is illegal or already in the low budget. -/
private theorem dyadic_step_saved {P : Position} (hp : Positive P) {k e B a : ℕ}
    (hk : HasDepth P k) (he : e ∈ P) (hek : valuation e = k) (A : Finset ℕ)
    (hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < k →
      grundy (successor P h d) ≤ B)
    (hhigh : ∀ d, legal P e d → k ≤ valuation d → d ∈ A)
    (hsave : legal P e a → grundy (successor P e a) ≤ B) :
    grundy P ≤ B + (A.erase a).card + 1 := by
  classical
  apply refined_step hp hk he hek (A.erase a) hlow
  intro d hd hv
  by_cases hda : d = a
  · subst d; exact Or.inl (hsave hd)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hda, hhigh d hd hv⟩)

/-- The old independent distinguished-heap recurrence has a strict margin one
    depth below a dyadic reference. No revised-bound hypothesis is used. -/
private theorem dyadic_penultimate {P : Position} (hp : Positive P) (k : ℕ)
    (hk : HasDepth P k) (hm : 2 ^ (k + 1) ∈ P) :
    grundy P ≤ 2 * 2 ^ (k + 1) - 1 := by
  have hb := reference_bound hp hk (by simpa using hm) (by omega : 0 < k + 1)
    (by decide : 0 < 1) (by decide : 1 % 2 = 1) (by omega : k ≤ k + 1)
  have hr : recurrenceBound (k + 1) 1 k ≤ 2 * 2 ^ (k + 1) - 1 := by
    by_cases hlarge : 16 ≤ k + 1
    · have ht := large_bound (k + 1) 1 hlarge (by decide) (by omega)
      change recurrenceBound (k + 1) 1 (k + 1) ≤ _ at ht
      rw [recurrenceBound] at ht
      simp only [exceptionalCount, ite_true] at ht
      have hm := Nat.le_max_left (recurrenceBound (k + 1) 1 k)
        ((Finset.range (k + 1)).sup (changedBound (k + 1) 1))
      omega
    · have hsmall : k ≤ 14 := by omega
      interval_cases k <;> decide
  exact hb.trans hr

/-- The refined bound holds for every distinguished heap, without a
    numerical-minimum hypothesis. -/
theorem revised_bound_reference {P : Position} (hp : Positive P) {H k : ℕ}
    (hk : HasDepth P k) (hH : H ∈ P) : grundy P ≤ revisedCeiling H k := by
  classical
  have main : ∀ k, ∀ P : Position, Positive P → HasDepth P k →
      ∀ H ∈ P, grundy P ≤ revisedCeiling H k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P hp hk H hH
      cases k with
      | zero =>
        have hb := coarse_bound hp hk hH le_rfl
        rw [coarseBound_zero] at hb
        simp only [revisedCeiling, pow_zero, Nat.div_one]
        omega
      | succ k =>
        let D := 2 ^ (k + 1)
        let q := H / D
        let B := revisedCeiling H k
        have hD : 0 < D := Nat.pow_pos (by decide)
        have hD2 : 2 ≤ D := by
          dsimp [D]; rw [pow_succ]; have := Nat.pow_pos (by decide : 0 < 2) (n := k); omega
        have hdiv : D ∣ H := (Nat.pow_dvd_pow 2 (hk.1 H hH)).trans pow_padicValNat_dvd
        have hHpos : 0 < H := hp H hH
        have hHq : D * q = H := Nat.mul_div_cancel' hdiv
        have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hHpos hdiv) hD
        have hstep : revisedCeiling H (k + 1) = B + q := ceiling_step hdiv
        have hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < k + 1 →
            grundy (successor P h d) ≤ B := by
          intro h hh d hd hj
          have hQ := (lower_move hp hk hh hd rfl hj).1
          obtain ⟨m, hm, hmH⟩ := lower_reference hp hk hh hH le_rfl hd hj
          exact (ih (valuation d) hj _ (successor_positive hp hh hd) hQ m hm).trans
            ((ceiling_mono (valuation d) hmH).trans (ceiling_depth_mono H (by omega)))
        by_cases hq1 : q = 1
        · have hHD : H = D := by rw [hq1, mul_one] at hHq; omega
          have hn : P ≠ 0 := by intro he; simpa [he] using hH
          have hmin : ∀ x ∈ P, H ≤ x := by
            intro x hx
            rw [hHD]
            exact Nat.le_of_dvd (hp x hx)
              ((Nat.pow_dvd_pow 2 (hk.1 x hx)).trans pow_padicValNat_dvd)
          have hb := result P hp hn H hH hmin
          have hquot : H / 2 ^ (k + 1) = 1 := hq1
          unfold revisedCeiling
          rw [hquot]
          omega
        by_cases hq2 : q = 2
        · have hpow : H = 2 ^ (k + 1 + 1) := by
            rw [hq2] at hHq
            simpa [D, pow_succ] using hHq.symm
          have hb := dyadic_penultimate hp (k + 1) hk (by rwa [← hpow])
          rw [← hpow] at hb
          have hquot : H / 2 ^ (k + 1) = 2 := hq2
          unfold revisedCeiling
          rw [hquot]
          omega
        have hq3 : 3 ≤ q := by omega
        obtain ⟨e, he, hek⟩ := hk.2
        let A := (Finset.Icc 1 q).image (fun i => D * i)
        let a := H - D
        have haeq : a = D * (q - 1) := by dsimp [a]; rw [← hHq, Nat.mul_sub_left_distrib]; simp
        have ha : a ∈ A := Finset.mem_image.mpr
          ⟨q - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, haeq.symm⟩
        have hcard : A.card ≤ q := by
          simpa [A, Nat.card_Icc] using
            (Finset.card_image_le (s := Finset.Icc 1 q) (f := fun i => D * i))
        have hcard' : (A.erase a).card + 1 ≤ q := by
          have ht := Finset.card_erase_add_one ha
          omega
        have hhigh : ∀ d, legal P e d → k + 1 ≤ valuation d → d ∈ A := by
          intro d hd hv
          have hdvd : D ∣ d := (Nat.pow_dvd_pow 2 hv).trans pow_padicValNat_dvd
          refine Finset.mem_image.mpr ⟨d / D, Finset.mem_Icc.mpr ⟨?_, ?_⟩,
            Nat.mul_div_cancel' hdvd⟩
          · exact Nat.div_pos (Nat.le_of_dvd hd.1 hdvd) hD
          · exact Nat.div_le_div_right (removal_le_reference hp hH le_rfl hd)
        have hsave : legal P e a → grundy (successor P e a) ≤ B := by
          intro hd
          have hH3 : 3 * D ≤ H := by nlinarith
          by_cases heH : e = H
          · subst e
            have hrem : H - a = D := by dsimp [a]; omega
            have hmem : D ∈ successor P H a := by
              rw [← hrem]; exact changed_reference (by dsimp [a]; omega)
            have hQp := successor_positive hp hH hd
            have hn : successor P H a ≠ 0 := by intro hz; simpa [hz] using hmem
            have hmin : ∀ x ∈ successor P H a, D ≤ x := by
              intro x hx
              simp only [successor, Multiset.mem_add] at hx
              rcases hx with hx | hx
              · exact Nat.le_of_dvd (hp x (Multiset.mem_of_mem_erase hx))
                  ((Nat.pow_dvd_pow 2 (hk.1 x (Multiset.mem_of_mem_erase hx))).trans
                    pow_padicValNat_dvd)
              · split_ifs at hx with hz
                · simp at hx
                · have hx' : x = H - a := by simpa using hx
                  omega
            have hb := result _ hQp hn D hmem hmin
            have hqold : H / 2 ^ k = 2 * q := by
              rw [← hHq]
              dsimp [D]
              rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
            have h2q : 2 * q ≤ H := by nlinarith
            have hbudget : 2 * D ≤ B := by dsimp [B, revisedCeiling]; rw [hqold]; omega
            exact hb.trans hbudget
          · have hdH : a ∣ H := hd.2.2 H ((Multiset.mem_erase_of_ne (Ne.symm heH)).mpr hH)
            have had : a ∣ D := by
              have ht := Nat.dvd_sub hdH (dvd_refl a)
              have hrem : H - a = D := by dsimp [a]; omega
              rwa [hrem] at ht
            have hale := Nat.le_of_dvd hD had
            dsimp [a] at hale
            omega
        have hb := dyadic_step_saved hp hk he hek A hlow hhigh hsave
        rw [hstep]
        omega
  exact main k P hp hk H hH

/-- The requested minimum-sensitive proposition, with all original hypotheses. -/
theorem revised_bound_statement : RevisedBoundStatement := by
  intro P H k hp hk hH _hmin
  exact revised_bound_reference hp hk hH

/-- The dyadic quotient is positive, so the refined ceiling is at most twice H. -/
theorem revised_bound_chain {P : Position} (hp : Positive P) {H k : ℕ}
    (hk : HasDepth P k) (hH : H ∈ P) :
    grundy P ≤ revisedCeiling H k ∧ revisedCeiling H k ≤ 2 * H := by
  refine ⟨revised_bound_reference hp hk hH, ?_⟩
  have hdiv : 2 ^ k ∣ H := (Nat.pow_dvd_pow 2 (hk.1 H hH)).trans pow_padicValNat_dvd
  have hquot := Nat.div_pos (Nat.le_of_dvd (hp H hH) hdiv) (Nat.pow_pos (by decide : 0 < 2))
  have hle := Nat.div_le_self H (2 ^ k)
  unfold revisedCeiling
  omega

def mixedPosition (r s : ℕ) : Position :=
  Multiset.replicate r 2 + Multiset.replicate s 4

def mixedFormula (r n : ℕ) : ℕ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then 2
  else 3 * ((r + n / 2) % 2)

def MixedFormulaStatement : Prop :=
  ∀ r s n : ℕ, 0 < r → 0 < s →
    fixedSequence (mixedPosition r s) n = mixedFormula r n

end D5.S3.Combinatorics.Games.DivisorNimGrundy
