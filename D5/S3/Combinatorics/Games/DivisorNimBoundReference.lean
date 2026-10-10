/- GID: D5/S3/Combinatorics/Games/DivisorNimBoundReference
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBoundReference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds obtained by following a distinguished heap through moves. -/

import D5.S3.Combinatorics.Games.DivisorNimGrundy
import D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic
import D5.S3.Combinatorics.Games.DivisorNimBoundOutcome
import Mathlib.Data.Finset.NatDivisors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

theorem removal_le_reference {P : Position} (hP : Positive P) {h d m H : ℕ}
    (hm : m ∈ P) (hmH : m ≤ H) (hd : legal P h d) : d ≤ H := by
  by_cases he : m = h
  · subst m
    exact hd.2.1.trans hmH
  · have hme : m ∈ P.erase h := (Multiset.mem_erase_of_ne he).2 hm
    exact (Nat.le_of_dvd (hP m hm) (hd.2.2 m hme)).trans hmH

theorem reference_survives {P : Position} {h d m : ℕ} (hm : m ∈ P) (hne : m ≠ h) :
    m ∈ successor P h d := by
  apply Multiset.mem_add.mpr
  exact Or.inl ((Multiset.mem_erase_of_ne hne).2 hm)

theorem changed_reference {P : Position} {h d : ℕ} (hd : d < h) :
    h - d ∈ successor P h d := by
  apply Multiset.mem_add.mpr
  refine Or.inr ?_
  have hn : h - d ≠ 0 := by omega
  simp [hn]


theorem lower_reference {P : Position} (_hp : Positive P) {h d m H k : ℕ}
    (hk : HasDepth P k) (hh : h ∈ P) (hm : m ∈ P) (hmH : m ≤ H)
    (hd : legal P h d) (hlt : valuation d < k) :
    ∃ n ∈ successor P h d, n ≤ H := by
  by_cases he : m = h
  · subst m
    have hsub := valuation_sub_of_lt hd.1 hd.2.1
      (hlt.trans_le (hk.1 h hh))
    exact ⟨h - d, changed_reference (by omega), (Nat.sub_le _ _).trans hmH⟩
  · exact ⟨m, reference_survives hm he, hmH⟩

/-- A single minimum-depth heap accounts for every nonzero high-depth follower. -/
theorem dyadic_step {P : Position} (hp : Positive P) {k e B : ℕ}
    (hk : HasDepth P k) (he : e ∈ P) (hek : valuation e = k) (A : Finset ℕ)
    (hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < k →
      grundy (successor P h d) ≤ B)
    (hhigh : ∀ d, legal P e d → k ≤ valuation d → d ∈ A) :
    grundy P ≤ B + A.card + 1 := by
  classical
  by_cases hg : grundy P = 0
  · rw [hg]; omega
  · have hb := grundy_counting P (A.image (successor P e)) B (by
      intro Q hQ
      rcases moves_spec hQ with ⟨h, hh, d, hd, rfl⟩
      by_cases hlt : valuation d < k
      · exact Or.inl (hlow h hh d hd hlt)
      · by_cases hzero : grundy (successor P h d) = 0
        · exact Or.inl (by rw [hzero]; exact Nat.zero_le B)
        · obtain ⟨hc, hvh⟩ := high_nonzero_unique hp hk hh hd (by omega) hg hzero
          have heh : h = e := unique_min hc hh he hvh hek
          subst h
          exact Or.inr (Finset.mem_image.mpr ⟨d, hhigh d hd (by omega), rfl⟩))
    exact hb.trans (Nat.add_le_add_right
      (Nat.add_le_add_left (Finset.card_image_le) B) 1)

open D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic
open scoped Pointwise

open scoped BigOperators

theorem coarseBound_zero (H : ℕ) : coarseBound 0 H = H + 1 := by
  simp [coarseBound]

theorem coarseBound_succ (k H : ℕ) :
    coarseBound (k + 1) H = coarseBound k H + H / 2 ^ (k + 1) + 1 := by
  unfold coarseBound
  rw [Finset.sum_range_succ]
  omega

theorem coarseBound_mono (H : ℕ) : Monotone (fun k => coarseBound k H) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [coarseBound_succ]
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem coarseBound_balance (k H : ℕ) (hd : 2 ^ k ∣ H) :
    coarseBound k H + H / 2 ^ k = 2 * H + k + 1 := by
  induction k with
  | zero => simp only [coarseBound_zero, pow_zero, Nat.div_one]; omega
  | succ k ih =>
    have hkd : 2 ^ k ∣ H := (Nat.pow_dvd_pow 2 (by omega : k ≤ k + 1)).trans hd
    have hi := ih hkd
    have hdiv : H / 2 ^ k = 2 * (H / 2 ^ (k + 1)) := by
      rcases hd with ⟨q, rfl⟩
      have h1 : (2 ^ (k + 1) * q) / 2 ^ k = 2 * q := by
        rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
      have h2 : (2 ^ (k + 1) * q) / 2 ^ (k + 1) = q :=
        Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))
      rw [h1, h2]
    rw [coarseBound_succ]
    omega

theorem coarseBound_le_reference {v u k : ℕ} (_hu : 0 < u) (hk : k ≤ v)
    (huv : v + 1 ≤ u) : coarseBound k (2 ^ v * u) ≤ 2 * (2 ^ v * u) := by
  have hd : 2 ^ k ∣ 2 ^ v * u :=
    dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hk) u
  have hb := coarseBound_balance k (2 ^ v * u) hd
  have hpow : 2 ^ v = 2 ^ k * 2 ^ (v - k) := by rw [← pow_add]; congr 1; omega
  have hquot : (2 ^ v * u) / 2 ^ k = 2 ^ (v - k) * u := by
    rw [hpow, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
  have hule : u ≤ (2 ^ v * u) / 2 ^ k := by
    rw [hquot]
    exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  omega

theorem changed_coarseBound {v u j : ℕ} (hu : 0 < u) (hj : j < v) :
    coarseBound j (2 ^ v * u - 2 ^ j) = changedBound v u j := by
  let m := 2 ^ v * u
  have hp : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hle : 2 ^ (j + 1) ≤ m :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j + 1 ≤ v)).trans
      (Nat.le_mul_of_pos_right _ hu)
  have hle' : 2 ^ j ≤ m := by rw [pow_succ] at hle; omega
  have hd : 2 ^ j ∣ m := dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega)) u
  have hd' : 2 ^ j ∣ m - 2 ^ j := Nat.dvd_sub hd (dvd_refl _)
  have hb := coarseBound_balance j (m - 2 ^ j) hd'
  have hq := Nat.div_eq_sub_div hp hle'
  have hsmall : m / 2 ^ j ≤ m := Nat.div_le_self _ _
  dsimp [changedBound]
  change coarseBound j (m - 2 ^ j) = 2 * m - m / 2 ^ j - 2 ^ (j + 1) + j + 2
  rw [pow_succ] at hle ⊢
  omega

/-- The bound is uniform in the number of heaps and requires only a surviving reference ceiling. -/
theorem coarse_bound {P : Position} (hp : Positive P) {k m H : ℕ}
    (hk : HasDepth P k) (hm : m ∈ P) (hmH : m ≤ H) :
    grundy P ≤ coarseBound k H := by
  classical
  have main : ∀ k, ∀ P : Position, Positive P → HasDepth P k →
      ∀ m ∈ P, m ≤ H → grundy P ≤ coarseBound k H := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P hp hk m hm hmH
      rcases hk.2 with ⟨e, he, hek⟩
      cases k with
      | zero =>
        by_cases hc : 1 < countAt P 0
        · have hsmall := depth_zero_multiple hp hk hc
          rw [coarseBound_zero]
          omega
        have hb := dyadic_step hp hk he hek (Finset.Icc 1 H)
          (B := 0) (by intro h hh d hd hlt; omega) (by
            intro d hd hv
            exact Finset.mem_Icc.mpr ⟨hd.1, removal_le_reference hp hm hmH hd⟩)
        simpa [coarseBound_zero, Nat.card_Icc] using hb
      | succ k =>
        let A := (Finset.Icc 1 (H / 2 ^ (k + 1))).image (fun i => 2 ^ (k + 1) * i)
        have hcard : A.card ≤ H / 2 ^ (k + 1) := by
          simpa [A, Nat.card_Icc] using (Finset.card_image_le
            (s := Finset.Icc 1 (H / 2 ^ (k + 1))) (f := fun i => 2 ^ (k + 1) * i))
        have hb := dyadic_step hp hk he hek A (B := coarseBound k H) (by
          intro h hh d hd hlt
          have hj := (lower_move hp hk hh hd rfl hlt).1
          rcases lower_reference hp hk hh hm hmH hd hlt with ⟨n, hn, hnH⟩
          exact (ih (valuation d) hlt _ (successor_positive hp hh hd) hj n hn hnH).trans
            (coarseBound_mono H (by omega : valuation d ≤ k))) (by
          intro d hd hv
          have hpow : 2 ^ (k + 1) ∣ d :=
            (Nat.pow_dvd_pow 2 hv).trans pow_padicValNat_dvd
          have hpos : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide)
          have hlo : 1 ≤ d / 2 ^ (k + 1) :=
            Nat.div_pos (Nat.le_of_dvd hd.1 hpow) hpos
          have hhi : d / 2 ^ (k + 1) ≤ H / 2 ^ (k + 1) :=
            Nat.div_le_div_right (removal_le_reference hp hm hmH hd)
          exact Finset.mem_image.mpr ⟨d / 2 ^ (k + 1), Finset.mem_Icc.mpr ⟨hlo, hhi⟩,
            Nat.mul_div_cancel' hpow⟩)
        rw [coarseBound_succ]
        exact hb.trans (Nat.add_le_add_right (Nat.add_le_add_left hcard _) 1)
  exact main k P hp hk m hm hmH

def highDivisors (m k : ℕ) : Finset ℕ := m.divisors.filter (fun d => 2 ^ k ∣ d)

theorem highDivisors_card_le_quotient (m k : ℕ) (hm : 0 < m) (hk : 2 ^ k ∣ m) :
    (highDivisors m k).card ≤ (m / 2 ^ k).divisors.card := by
  classical
  let s := highDivisors m k
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hquot : m / 2 ^ k ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hm hk) hpos)
  apply Finset.card_le_card_of_injOn (fun d => d / 2 ^ k)
  · intro d hd
    have h := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_div h.2 (Nat.dvd_of_mem_divisors h.1), hquot⟩
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    calc
      a = 2 ^ k * (a / 2 ^ k) := (Nat.mul_div_cancel' ha').symm
      _ = 2 ^ k * (b / 2 ^ k) := congrArg (2 ^ k * ·) he
      _ = b := Nat.mul_div_cancel' hb'

theorem divisor_card_le (w u : ℕ) :
    (2 ^ w * u).divisors.card ≤ (w + 1) * oddDivisorCount u := by
  rw [Nat.divisors_mul]
  exact (Finset.card_mul_le).trans (by
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
    rfl)

theorem highDivisors_card_le {v u k : ℕ} (hu : 0 < u) (hk : k ≤ v) :
    (highDivisors (2 ^ v * u) k).card ≤ (v - k + 1) * oddDivisorCount u := by
  have hpow : 2 ^ v = 2 ^ k * 2 ^ (v - k) := by rw [← pow_add]; congr 1; omega
  have hquo : (2 ^ v * u) / 2 ^ k = 2 ^ (v - k) * u := by
    rw [hpow, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
  have hdvd : 2 ^ k ∣ 2 ^ v * u := ⟨2 ^ (v - k) * u, by rw [hpow, mul_assoc]⟩
  have hm : 0 < 2 ^ v * u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  exact (highDivisors_card_le_quotient _ _ hm hdvd).trans (hquo ▸ divisor_card_le (v - k) u)

theorem reference_valuation {v u : ℕ} (hu : 0 < u) (hodd : u % 2 = 1) :
    valuation (2 ^ v * u) = v := by
  have hn : ¬ 2 ∣ u := by intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega
  change padicValNat 2 (2 ^ v * u) = v
  rw [padicValNat.mul (Nat.ne_of_gt (Nat.pow_pos (by decide))) (Nat.ne_of_gt hu),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hn, Nat.add_zero]

/-- Lower-depth followers distinguish preservation and replacement of the reference heap. -/
theorem reference_lower {P : Position} (hp : Positive P) {v u k B : ℕ}
    (hk : HasDepth P k) (hm : 2 ^ v * u ∈ P) (hu : 0 < u)
    (_hodd : u % 2 = 1) (hkv : k ≤ v)
    (hprev : ∀ Q : Position, Positive Q → ∀ j < k, HasDepth Q j →
      2 ^ v * u ∈ Q → grundy Q ≤ B)
    (hchanged : ∀ j < k, changedBound v u j ≤ B) :
    ∀ h ∈ P, ∀ d, legal P h d → valuation d < k →
      grundy (successor P h d) ≤ B := by
  intro h hh d hd hj
  have hQp := successor_positive hp hh hd
  have hQdepth := (lower_move hp hk hh hd rfl hj).1
  by_cases he : 2 ^ v * u = h
  · subst h
    have hsub := valuation_sub_of_lt hd.1 hd.2.1 (hj.trans_le (hk.1 _ hm))
    have hpow : 2 ^ valuation d ≤ d := Nat.le_of_dvd hd.1 pow_padicValNat_dvd
    have hsmall : 2 ^ v * u - d ≤ 2 ^ v * u - 2 ^ valuation d := Nat.sub_le_sub_left hpow _
    have hb := coarse_bound hQp hQdepth (changed_reference (by omega : d < 2 ^ v * u)) hsmall
    rw [changed_coarseBound hu (hj.trans_le hkv)] at hb
    exact hb.trans (hchanged _ hj)
  · exact hprev _ hQp _ hj hQdepth (reference_survives hm he)

/-- The distinguished heap may survive or be replaced by a smaller positive heap. -/
theorem reference_step {P : Position} (hp : Positive P) {v u k B : ℕ}
    (hk : HasDepth P k) (hm : 2 ^ v * u ∈ P) (hu : 0 < u)
    (hodd : u % 2 = 1) (hkv : k ≤ v)
    (hprev : ∀ Q : Position, Positive Q → ∀ j < k, HasDepth Q j →
      2 ^ v * u ∈ Q → grundy Q ≤ B)
    (hchanged : ∀ j < k, changedBound v u j ≤ B) :
    grundy P ≤ B + exceptionalCount v u k + 1 := by
  classical
  have hmval := reference_valuation (v := v) hu hodd
  have hlow := reference_lower hp hk hm hu hodd hkv hprev hchanged
  by_cases heq : k = v
  · subst k
    let A := (Finset.Icc 1 u).image (fun i => 2 ^ v * i)
    have hcard : A.card ≤ u := by
      simpa [A, Nat.card_Icc] using (Finset.card_image_le
        (s := Finset.Icc 1 u) (f := fun i => 2 ^ v * i))
    have hb := dyadic_step hp hk hm hmval A hlow (by
      intro d hd hv
      have hpow : 2 ^ v ∣ d := (Nat.pow_dvd_pow 2 hv).trans pow_padicValNat_dvd
      have hpos : 0 < 2 ^ v := Nat.pow_pos (by decide)
      have hlo : 1 ≤ d / 2 ^ v := Nat.div_pos (Nat.le_of_dvd hd.1 hpow) hpos
      have hhi : d / 2 ^ v ≤ u := by
        have ht := Nat.div_le_div_right (c := 2 ^ v) hd.2.1
        simpa [Nat.mul_div_cancel_left u hpos] using ht
      exact Finset.mem_image.mpr ⟨d / 2 ^ v, Finset.mem_Icc.mpr ⟨hlo, hhi⟩,
        Nat.mul_div_cancel' hpow⟩)
    simpa [exceptionalCount] using
      hb.trans (Nat.add_le_add_right (Nat.add_le_add_left hcard B) 1)
  · rcases hk.2 with ⟨e, he, hek⟩
    have hne : 2 ^ v * u ≠ e := by intro hh; rw [hh] at hmval; omega
    have hb := dyadic_step hp hk he hek (highDivisors (2 ^ v * u) k) hlow (by
      intro d hd hv
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨hd.2.2 _ ((Multiset.mem_erase_of_ne hne).mpr hm),
          Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos (by decide)) hu)⟩
      · exact (Nat.pow_dvd_pow 2 hv).trans pow_padicValNat_dvd)
    have hc := highDivisors_card_le hu hkv
    simp only [exceptionalCount, if_neg heq]
    exact hb.trans (Nat.add_le_add_right (Nat.add_le_add_left hc B) 1)

theorem reference_bound {P : Position} (hp : Positive P) {v u k : ℕ}
    (hk : HasDepth P k) (hm : 2 ^ v * u ∈ P) (hv : 0 < v)
    (hu : 0 < u) (hodd : u % 2 = 1) (hkv : k ≤ v) :
    grundy P ≤ recurrenceBound v u k := by
  classical
  have main : ∀ k, k ≤ v → ∀ P : Position, Positive P → HasDepth P k →
      2 ^ v * u ∈ P → grundy P ≤ recurrenceBound v u k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkv P hp hk hm
      cases k with
      | zero =>
        rcases hk.2 with ⟨e, he, hek⟩
        have hmval := reference_valuation (v := v) hu hodd
        have hne : 2 ^ v * u ≠ e := by intro he'; rw [he'] at hmval; omega
        have hb := dyadic_step hp hk he hek (2 ^ v * u).divisors (B := 0)
          (by intro h hh d hd hlt; omega) (by
            intro d hd hvd
            exact Nat.mem_divisors.mpr ⟨hd.2.2 _ ((Multiset.mem_erase_of_ne hne).mpr hm),
              Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos (by decide)) hu)⟩)
        have hc := divisor_card_le v u
        simp only [recurrenceBound]
        omega
      | succ k =>
        let B := max (recurrenceBound v u k) ((Finset.range (k + 1)).sup (changedBound v u))
        have hb := reference_step hp hk hm hu hodd hkv (B := B) (by
          intro Q hQp j hj hQj hmQ
          have hbj := ih j hj (by omega : j ≤ v) Q hQp hQj hmQ
          exact hbj.trans ((recurrenceBound_mono v u (by omega : j ≤ k)).trans
            (Nat.le_max_left _ _))) (by
          intro j hj
          exact (Finset.le_sup (Finset.mem_range.mpr hj)).trans (Nat.le_max_right _ _))
        exact hb
  exact main k hkv P hp hk hm

end D5.S3.Combinatorics.Games.DivisorNimGrundy
