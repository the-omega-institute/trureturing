/- GID: D5/S3/Combinatorics/Games/DivisorNimBoundOutcome
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBoundOutcome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dyadic depth and the zero positions of Divisor Nim. -/

import D5.S3.Combinatorics.Games.DivisorNimGrundy
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Multiset.AddSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

abbrev valuation (h : ℕ) : ℕ := padicValNat 2 h

def HasDepth (P : Position) (k : ℕ) : Prop :=
  (∀ h ∈ P, k ≤ valuation h) ∧ ∃ h ∈ P, valuation h = k

def countAt (P : Position) (k : ℕ) : ℕ :=
  P.countP (fun h => valuation h = k)

theorem successor_positive {P : Position} (hp : Positive P) {h d : ℕ}
    (_hh : h ∈ P) (_hd : legal P h d) : Positive (successor P h d) := by
  intro x hx
  simp only [successor, Multiset.mem_add] at hx
  rcases hx with hx | hx
  · exact hp x (Multiset.mem_of_mem_erase hx)
  · split_ifs at hx with hz
    · simp at hx
    · have he : x = h - d := by simpa using hx
      omega

theorem exists_depth {P : Position} (hn : P ≠ 0) : ∃ k, HasDepth P k := by
  classical
  have hs : (P.toFinset.image valuation).Nonempty := by
    rcases Multiset.exists_mem_of_ne_zero hn with ⟨h, hh⟩
    exact ⟨valuation h, Finset.mem_image.mpr ⟨h, Multiset.mem_toFinset.mpr hh, rfl⟩⟩
  refine ⟨(P.toFinset.image valuation).min' hs, ?_, ?_⟩
  · intro h hh
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨h, Multiset.mem_toFinset.mpr hh, rfl⟩)
  · rcases Finset.mem_image.mp (Finset.min'_mem _ hs) with ⟨h, hh, he⟩
    exact ⟨h, Multiset.mem_toFinset.mp hh, he⟩

theorem countAt_pos {P : Position} {k : ℕ} (hk : HasDepth P k) : 0 < countAt P k :=
  Multiset.countP_pos.mpr hk.2

theorem valuation_le_of_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) :
    valuation a ≤ valuation b := by
  exact (padicValNat_dvd_iff_le (p := 2) (by omega : b ≠ 0)).mp
    (pow_padicValNat_dvd.trans hab)

theorem valuation_sub_of_lt {h d : ℕ} (hd : 0 < d) (hle : d ≤ h)
    (hlt : valuation d < valuation h) :
    0 < h - d ∧ valuation (h - d) = valuation d := by
  have hne : h ≠ d := by intro he; simp [he] at hlt
  have hpos : 0 < h - d := by omega
  have hdvd : 2 ^ valuation d ∣ h - d := Nat.dvd_sub
    ((Nat.pow_dvd_pow 2 (by omega : valuation d ≤ valuation h)).trans pow_padicValNat_dvd)
    pow_padicValNat_dvd
  have hlo : valuation d ≤ valuation (h - d) :=
    (padicValNat_dvd_iff_le (p := 2) (by omega)).mp hdvd
  have hnot : ¬ 2 ^ (valuation d + 1) ∣ h - d := by
    intro hs
    have hh : 2 ^ (valuation d + 1) ∣ h :=
      (Nat.pow_dvd_pow 2 (by change valuation d + 1 ≤ valuation h; omega)).trans pow_padicValNat_dvd
    exact pow_succ_padicValNat_not_dvd (p := 2) (by omega : d ≠ 0)
      ((Nat.dvd_sub_iff_right hle hh).mp hs)
  have hhi : ¬ valuation d + 1 ≤ valuation (h - d) := by
    simpa only [← padicValNat_dvd_iff_le (p := 2) (by omega : h - d ≠ 0)] using hnot
  exact ⟨hpos, by omega⟩

theorem lower_move {P : Position} (_hp : Positive P) {h d j k : ℕ}
    (hk : HasDepth P k) (hh : h ∈ P) (hd : legal P h d)
    (hj : valuation d = j) (hjk : j < k) :
    HasDepth (successor P h d) j ∧ countAt (successor P h d) j = 1 := by
  have hsub := valuation_sub_of_lt hd.1 hd.2.1
    (by have := hk.1 h hh; omega)
  have hzero : (P.erase h).countP (fun x => valuation x = j) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro x hx he
    have := hk.1 x (Multiset.mem_of_mem_erase hx)
    omega
  have heq : successor P h d = P.erase h + {h - d} := by
    simp [successor, Nat.ne_of_gt hsub.1]
  constructor
  · rw [heq]
    constructor
    · intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · have := hk.1 x (Multiset.mem_of_mem_erase hx)
        omega
      · have he : x = h - d := by simpa using hx
        rw [he]
        omega
    · exact ⟨h - d, by simp, by omega⟩
  · rw [countAt, heq, Multiset.countP_add, hzero]
    rw [show ({h - d} : Multiset ℕ) = (h - d) ::ₘ 0 from rfl,
      Multiset.countP_cons, Multiset.countP_zero, if_pos (by omega)]

theorem valuation_sub_same {h d k : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hle : d ≤ h) (hhk : valuation h = k) (hdk : valuation d = k)
    (hn : h - d ≠ 0) : k < valuation (h - d) := by
  have hbase : 0 < 2 ^ k := by positivity
  have hhdiv : 2 ^ k ∣ h := by rw [← hhk]; exact pow_padicValNat_dvd
  have hddiv : 2 ^ k ∣ d := by rw [← hdk]; exact pow_padicValNat_dvd
  rcases hhdiv with ⟨a, ha⟩
  rcases hddiv with ⟨b, hb⟩
  have hna : ¬ 2 ∣ a := by
    intro hab
    have ht : 2 ^ (k + 1) ∣ h := by
      rw [ha, pow_succ]
      exact Nat.mul_dvd_mul_left _ hab
    rw [← hhk] at ht
    exact pow_succ_padicValNat_not_dvd (p := 2) (by omega) ht
  have hnb : ¬ 2 ∣ b := by
    intro hab
    have ht : 2 ^ (k + 1) ∣ d := by
      rw [hb, pow_succ]
      exact Nat.mul_dvd_mul_left _ hab
    rw [← hdk] at ht
    exact pow_succ_padicValNat_not_dvd (p := 2) (by omega) ht
  have hab : b ≤ a := by nlinarith
  have hmoda : a % 2 = 1 := by
    have : a % 2 ≠ 0 := fun he => hna (Nat.dvd_of_mod_eq_zero he)
    omega
  have hmodb : b % 2 = 1 := by
    have : b % 2 ≠ 0 := fun he => hnb (Nat.dvd_of_mod_eq_zero he)
    omega
  have hdab : 2 ∣ a - b := Nat.dvd_of_mod_eq_zero (by omega)
  have ht : 2 ^ (k + 1) ∣ h - d := by
    rw [ha, hb, ← Nat.mul_sub_left_distrib, pow_succ]
    exact Nat.mul_dvd_mul_left _ hdab
  have hv := (padicValNat_dvd_iff_le (p := 2) hn).mp ht
  change k + 1 ≤ valuation (h - d) at hv
  omega

theorem countAt_erase {P : Position} {h k : ℕ} (hh : h ∈ P) :
    countAt P k = countAt (P.erase h) k + if valuation h = k then 1 else 0 := by
  calc
    countAt P k = countAt (h ::ₘ P.erase h) k :=
      congrArg (fun S => countAt S k) (Multiset.cons_erase hh).symm
    _ = _ := Multiset.countP_cons (fun x => valuation x = k) h (P.erase h)

theorem countAt_successor {P : Position} {h d k : ℕ} :
    countAt (successor P h d) k = countAt (P.erase h) k +
      if h - d ≠ 0 ∧ valuation (h - d) = k then 1 else 0 := by
  unfold successor countAt
  by_cases hn : h - d = 0
  · simp only [hn, if_true, Multiset.add_zero]
    simp
  · rw [if_neg hn, Multiset.countP_add,
      show ({h - d} : Multiset ℕ) = (h - d) ::ₘ 0 from rfl,
      Multiset.countP_cons, Multiset.countP_zero]
    simp only [Nat.zero_add, ne_eq, hn, not_false_eq_true, true_and]

theorem successor_mem_remainder {P : Position} {h d : ℕ} (hn : h - d ≠ 0) :
    h - d ∈ successor P h d := by simp [successor, hn]

theorem successor_mem_erase {P : Position} {h d x : ℕ} (hx : x ∈ P.erase h) :
    x ∈ successor P h d := by
  unfold successor
  exact Multiset.mem_add.mpr (Or.inl hx)

theorem depth_of_surviving_min {P : Position} (hp : Positive P) {h d k : ℕ}
    (hk : HasDepth P k) (hh : h ∈ P) (hd : legal P h d)
    (hval : k ≤ valuation d) (hr : 0 < countAt (P.erase h) k) :
    valuation d = k ∧ HasDepth (successor P h d) k := by
  rcases Multiset.countP_pos.mp hr with ⟨z, hz, hzk⟩
  have hv : valuation d ≤ k := by
    have := valuation_le_of_dvd (hp z (Multiset.mem_of_mem_erase hz)) (hd.2.2 z hz)
    omega
  have hvk : valuation d = k := by omega
  refine ⟨hvk, ?_, z, successor_mem_erase hz, hzk⟩
  intro x hx
  simp only [successor, Multiset.mem_add] at hx
  rcases hx with hx | hx
  · exact hk.1 x (Multiset.mem_of_mem_erase hx)
  · split_ifs at hx with hn
    · simp at hx
    · have he : x = h - d := by simpa using hx
      rw [he]
      apply (padicValNat_dvd_iff_le (p := 2) hn).mp
      apply Nat.dvd_sub
      · exact (Nat.pow_dvd_pow 2 (hk.1 h hh)).trans pow_padicValNat_dvd
      · rw [← hvk]; exact pow_padicValNat_dvd

theorem high_move_count {P : Position} (hp : Positive P) {h d k : ℕ}
    (hk : HasDepth P k) (hh : h ∈ P) (hd : legal P h d)
    (hval : k ≤ valuation d) (hr : 0 < countAt (P.erase h) k) :
    HasDepth (successor P h d) k ∧
      (countAt (successor P h d) k + countAt P k) % 2 = 1 := by
  obtain ⟨hvk, hdepth⟩ := depth_of_surviving_min hp hk hh hd hval hr
  refine ⟨hdepth, ?_⟩
  have hcount := countAt_erase (k := k) hh
  have hsucc := countAt_successor (P := P) (h := h) (d := d) (k := k)
  by_cases hhk : valuation h = k
  · have hzero : ¬ (h - d ≠ 0 ∧ valuation (h - d) = k) := by
      rintro ⟨hn, he⟩
      have := valuation_sub_same (hp h hh) hd.1 hd.2.1 hhk hvk hn
      omega
    rw [if_pos hhk] at hcount
    rw [if_neg hzero] at hsucc
    omega
  · have hlt : valuation d < valuation h := by have := hk.1 h hh; omega
    have hsub := valuation_sub_of_lt hd.1 hd.2.1 hlt
    rw [if_neg hhk] at hcount
    rw [if_pos (by constructor <;> omega)] at hsucc
    omega

theorem unique_min {P : Position} {h z k : ℕ} (hc : countAt P k = 1)
    (hh : h ∈ P) (hz : z ∈ P) (hhk : valuation h = k) (hzk : valuation z = k) : h = z := by
  by_contra hne
  have he : z ∈ P.erase h := (Multiset.mem_erase_of_ne (Ne.symm hne)).mpr hz
  have hp : 0 < countAt (P.erase h) k := Multiset.countP_pos.mpr ⟨z, he, hzk⟩
  have hc' := countAt_erase (k := k) hh
  rw [if_pos hhk] at hc'
  omega

theorem successor_is_move {P : Position} {h d : ℕ} (hh : h ∈ P)
    (hd : legal P h d) : successor P h d ∈ moves P := by
  classical
  simp only [moves, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  exact ⟨h, Multiset.mem_toFinset.mpr hh, d,
    ⟨Finset.mem_Icc.mpr ⟨hd.1, hd.2.1⟩, hd⟩, rfl⟩

theorem moves_spec {P Q : Position} (hq : Q ∈ moves P) :
    ∃ h ∈ P, ∃ d, legal P h d ∧ successor P h d = Q := by
  classical
  simp only [moves, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hq
  rcases hq with ⟨h, hh, d, hd, hsucc⟩
  exact ⟨h, Multiset.mem_toFinset.mp hh, d, hd.2, hsucc⟩

theorem power_legal {P : Position} (hp : Positive P) {k h : ℕ}
    (hk : HasDepth P k) (hh : h ∈ P) : legal P h (2 ^ k) := by
  refine ⟨by positivity, ?_, ?_⟩
  · apply Nat.le_of_dvd (hp h hh)
    exact (Nat.pow_dvd_pow 2 (hk.1 h hh)).trans pow_padicValNat_dvd
  · intro x hx
    exact (Nat.pow_dvd_pow 2 (hk.1 x (Multiset.mem_of_mem_erase hx))).trans
      pow_padicValNat_dvd

theorem grundy_empty : grundy 0 = 0 := by
  rw [grundy_zero_iff]
  simp [moves]

theorem even_count_moves_odd {P : Position} (hp : Positive P) {k : ℕ}
    (hk : HasDepth P k) (he : Even (countAt P k)) {Q : Position} (hq : Q ∈ moves P) :
    ∃ j, HasDepth Q j ∧ (countAt Q j) % 2 = 1 := by
  rcases moves_spec hq with ⟨h, hh, d, hd, rfl⟩
  by_cases hlt : valuation d < k
  · obtain ⟨hdp, hc⟩ := lower_move hp hk hh hd rfl hlt
    exact ⟨valuation d, hdp, by rw [hc]⟩
  · have hpos := countAt_pos hk
    have hmod := Nat.even_iff.mp he
    have hcount := countAt_erase (k := k) hh
    have hrem : 0 < countAt (P.erase h) k := by
      split_ifs at hcount <;> omega
    obtain ⟨hdepth, hpar⟩ := high_move_count hp hk hh hd (by omega) hrem
    exact ⟨k, hdepth, by omega⟩

theorem odd_count_has_even_move {P : Position} (hp : Positive P) {k : ℕ}
    (hk : HasDepth P k) (ho : (countAt P k) % 2 = 1) :
    ∃ Q ∈ moves P, Q = 0 ∨ ∃ j, HasDepth Q j ∧ Even (countAt Q j) := by
  rcases hk.2 with ⟨h, hh, hhk⟩
  by_cases hc : countAt P k = 1
  · by_cases hzero : P.erase h = 0
    · have hP : P = {h} := by
        have := Multiset.cons_erase hh
        simpa [hzero] using this.symm
      have hd : legal P h h := by
        refine ⟨hp h hh, le_rfl, ?_⟩
        simp [dividesAll, hzero]
      refine ⟨successor P h h, successor_is_move hh hd, Or.inl ?_⟩
      simp [successor, hzero]
    · rcases Multiset.exists_mem_of_ne_zero hzero with ⟨z, hz⟩
      have hzP := Multiset.mem_of_mem_erase hz
      have hc0 : countAt (P.erase h) k = 0 := by
        have ht := countAt_erase (k := k) hh
        rw [if_pos hhk] at ht
        omega
      have hzk : valuation z ≠ k := by
        intro he
        have : 0 < countAt (P.erase h) k := Multiset.countP_pos.mpr ⟨z, hz, he⟩
        omega
      have hne : h ≠ z := by intro he; rw [← he] at hzk; exact hzk hhk
      have hhrem : h ∈ P.erase z := (Multiset.mem_erase_of_ne hne).mpr hh
      have hrem : 0 < countAt (P.erase z) k :=
        Multiset.countP_pos.mpr ⟨h, hhrem, hhk⟩
      have hd := power_legal hp hk hzP
      have hv : valuation (2 ^ k) = k := padicValNat.prime_pow k
      obtain ⟨hdepth, hpar⟩ := high_move_count hp hk hzP hd (by rw [hv]) hrem
      refine ⟨successor P z (2 ^ k), successor_is_move hzP hd, Or.inr ?_⟩
      exact ⟨k, hdepth, Nat.even_iff.mpr (by omega)⟩
  · have hcount := countAt_erase (k := k) hh
    rw [if_pos hhk] at hcount
    have hrem : 0 < countAt (P.erase h) k := by omega
    have hd := power_legal hp hk hh
    have hv : valuation (2 ^ k) = k := padicValNat.prime_pow k
    obtain ⟨hdepth, hpar⟩ := high_move_count hp hk hh hd (by rw [hv]) hrem
    refine ⟨successor P h (2 ^ k), successor_is_move hh hd, Or.inr ?_⟩
    exact ⟨k, hdepth, Nat.even_iff.mpr (by omega)⟩

theorem zero_iff_even_count {P : Position} (hp : Positive P) {k : ℕ}
    (hk : HasDepth P k) : grundy P = 0 ↔ Even (countAt P k) := by
  have hmain : ∀ n, ∀ P : Position, P.sum = n → Positive P →
      ∀ k, HasDepth P k → (grundy P = 0 ↔ Even (countAt P k)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hsum hp k hk
      constructor
      · intro hg
        by_contra he
        have ho : countAt P k % 2 = 1 := by
          have : countAt P k % 2 ≠ 0 := fun hn => he (Nat.even_iff.mpr hn)
          omega
        rcases odd_count_has_even_move hp hk ho with ⟨Q, hq, heQ⟩
        have hgQ : grundy Q = 0 := by
          rcases heQ with rfl | ⟨j, hj, heQ⟩
          · exact grundy_empty
          · have hsmall : Q.sum < n := by rw [← hsum]; exact move_sum_lt hq
            have hpos : Positive Q := by
              rcases moves_spec hq with ⟨h, hh, d, hd, rfl⟩
              exact successor_positive hp hh hd
            exact (ih Q.sum hsmall Q rfl hpos j hj).mpr heQ
        exact (grundy_zero_iff P).mp hg Q hq hgQ
      · intro he
        rw [grundy_zero_iff]
        intro Q hq
        rcases even_count_moves_odd hp hk he hq with ⟨j, hj, hodd⟩
        have hsmall : Q.sum < n := by rw [← hsum]; exact move_sum_lt hq
        have hpos : Positive Q := by
          rcases moves_spec hq with ⟨h, hh, d, hd, rfl⟩
          exact successor_positive hp hh hd
        intro hgQ
        have hc := (ih Q.sum hsmall Q rfl hpos j hj).mp hgQ
        have := Nat.even_iff.mp hc
        omega
  exact hmain P.sum P rfl hp k hk

theorem high_nonzero_unique {P : Position} (hp : Positive P) {h d k : ℕ}
    (hk : HasDepth P k) (hh : h ∈ P) (hd : legal P h d)
    (hval : k ≤ valuation d) (hgP : grundy P ≠ 0)
    (hgQ : grundy (successor P h d) ≠ 0) :
    countAt P k = 1 ∧ valuation h = k := by
  have hodd : countAt P k % 2 = 1 := by
    have hne : countAt P k % 2 ≠ 0 := by
      intro he
      exact hgP ((zero_iff_even_count hp hk).mpr (Nat.even_iff.mpr he))
    omega
  have hrem : countAt (P.erase h) k = 0 := by
    by_contra hn
    have hpos : 0 < countAt (P.erase h) k := by omega
    obtain ⟨hdepth, hpar⟩ := high_move_count hp hk hh hd hval hpos
    have hzero : Even (countAt (successor P h d) k) := Nat.even_iff.mpr (by omega)
    exact hgQ ((zero_iff_even_count (successor_positive hp hh hd) hdepth).mpr hzero)
  have hcount := countAt_erase (k := k) hh
  have hpos := countAt_pos hk
  split_ifs at hcount with hhk
  · exact ⟨by omega, hhk⟩
  · omega

theorem valuation_eq_of_dvd_not {n k : ℕ} (hn : n ≠ 0)
    (hd : 2 ^ k ∣ n) (hnd : ¬ 2 ^ (k + 1) ∣ n) : valuation n = k := by
  have hlo := (padicValNat_dvd_iff_le (p := 2) hn).mp hd
  have hhi : ¬ k + 1 ≤ valuation n := by
    simpa only [← padicValNat_dvd_iff_le (p := 2) hn] using hnd
  change k ≤ valuation n at hlo
  omega

theorem valuation_decomposition {m : ℕ} (hm : 0 < m) :
    ∃ u, 0 < u ∧ Odd u ∧ m = 2 ^ valuation m * u := by
  rcases (pow_padicValNat_dvd (p := 2) (n := m)) with ⟨u, hu⟩
  have hpos : 0 < u := by
    have hp : 0 < 2 ^ valuation m := by positivity
    nlinarith
  have hnot : ¬ 2 ∣ u := by
    intro hd
    have ht : 2 ^ (valuation m + 1) ∣ m := by
      conv_rhs => rw [hu]
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hd
    exact pow_succ_padicValNat_not_dvd (p := 2) (by omega : m ≠ 0) ht
  refine ⟨u, hpos, Nat.odd_iff.mpr ?_, hu⟩
  have : u % 2 ≠ 0 := fun he => hnot (Nat.dvd_of_mod_eq_zero he)
  omega

theorem depth_zero_multiple {P : Position} (hp : Positive P)
    (hk : HasDepth P 0) (hc : 1 < countAt P 0) : grundy P ≤ 1 := by
  by_cases hg : grundy P = 0
  · omega
  · apply grundy_le_of_followers
    intro Q hq
    rcases moves_spec hq with ⟨h, hh, d, hd, rfl⟩
    by_cases hgQ : grundy (successor P h d) = 0
    · omega
    · have ht := high_nonzero_unique hp hk hh hd (Nat.zero_le _) hg hgQ
      omega

end D5.S3.Combinatorics.Games.DivisorNimGrundy
