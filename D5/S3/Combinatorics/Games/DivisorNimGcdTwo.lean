/- GID: D5/S3/Combinatorics/Games/DivisorNimGcdTwo
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimGcdTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic zero residues and complete positive-value phases for fixed gcd two. -/

import D5.S3.Combinatorics.Games.DivisorNimFixedBoard
import Mathlib.Tactic.Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

private theorem residue_of_depth {n k : ℕ} (hn : 0 < n) :
    (k ≤ valuation n ↔ 2 ^ k ∣ n) ∧
    (valuation n = k ↔ n % (2 ^ (k + 1)) = 2 ^ k) := by
  have hp : 0 < 2 ^ k := by positivity
  have hp' : 0 < 2 ^ (k + 1) := by positivity
  have he : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ _ _
  have hdiv : 2 ^ k ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ _)
  have hle : k ≤ valuation n ↔ 2 ^ k ∣ n :=
    (padicValNat_dvd_iff_le (p := 2) (by omega)).symm
  refine ⟨hle, ?_⟩
  constructor
  · intro hv
    have hd := hle.mp (by omega)
    have hnd : ¬ 2 ^ (k + 1) ∣ n := by
      simpa [← hv] using pow_succ_padicValNat_not_dvd (p := 2) (by omega : n ≠ 0)
    have hdr : 2 ^ k ∣ n % (2 ^ (k + 1)) := Nat.dvd_mod_iff hdiv |>.mpr hd
    obtain ⟨a, ha⟩ := hdr
    have hb := Nat.mod_lt n hp'
    have hc : n % (2 ^ (k + 1)) ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    rw [ha, he] at hb
    have ha0 : a ≠ 0 := by
      intro hz
      exact hc (by simpa [hz] using ha)
    have ha1 : 1 ≤ a := by omega
    have : a = 1 := by nlinarith
    simpa [this] using ha
  · intro hm
    have hd : 2 ^ k ∣ n := (Nat.dvd_mod_iff hdiv).mp (by rw [hm])
    have hnd : ¬ 2 ^ (k + 1) ∣ n := by
      intro h
      have := Nat.mod_eq_zero_of_dvd h
      omega
    exact valuation_eq_of_dvd_not (by omega) hd hnd

/-- At any minimum depth, losing varying heaps form exactly one residue class. -/
theorem fixed_zero_residue {A : Position} (hp : Positive A) {k : ℕ}
    (hk : HasDepth A k) {n : ℕ} (hn : 0 < n) :
    grundy (n ::ₘ A) = 0 ↔
      n % (2 ^ (k + 1)) = if Even (countAt A k) then 0 else 2 ^ k := by
  classical
  have hpos : Positive (n ::ₘ A) := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hn
    · exact hp x hx
  have hres := residue_of_depth (k := k) hn
  by_cases hl : valuation n < k
  · have hdep : HasDepth (n ::ₘ A) (valuation n) := by
      refine ⟨?_, n, by simp, rfl⟩
      intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · omega
      · have := hk.1 x hx; omega
    have hc : countAt (n ::ₘ A) (valuation n) = 1 := by
      have hz : countAt A (valuation n) = 0 := Multiset.countP_eq_zero.mpr (by
        intro x hx hv
        have := hk.1 x hx
        omega)
      simp [countAt, Multiset.countP_cons, show
        A.countP (fun h => valuation h = valuation n) = 0 from hz]
    rw [zero_iff_even_count hpos hdep, hc]
    simp only [show ¬ Even (1 : ℕ) by decide, false_iff]
    split_ifs with heven
    · intro hm
      have hbig : k + 1 ≤ valuation n :=
        (padicValNat_dvd_iff_le (p := 2) (by omega)).mp (Nat.dvd_of_mod_eq_zero hm)
      omega
    · intro hm
      have := hres.2.mpr hm
      omega
  · have hdep : HasDepth (n ::ₘ A) k := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · omega
        · exact hk.1 x hx
      · obtain ⟨x, hx, hv⟩ := hk.2
        exact ⟨x, by simp [hx], hv⟩
    have hc : countAt (n ::ₘ A) k = countAt A k + if valuation n = k then 1 else 0 :=
      Multiset.countP_cons _ _ _
    have hz : valuation n ≠ k ↔ n % (2 ^ (k + 1)) = 0 := by
      constructor
      · intro hne
        apply Nat.mod_eq_zero_of_dvd
        exact (padicValNat_dvd_iff_le (p := 2) (by omega)).mpr
          (show k + 1 ≤ valuation n by omega)
      · intro hm hv
        have hnot := pow_succ_padicValNat_not_dvd (p := 2) (by omega : n ≠ 0)
        change ¬ 2 ^ (valuation n + 1) ∣ n at hnot
        rw [hv] at hnot
        exact hnot (Nat.dvd_of_mod_eq_zero hm)
    rw [zero_iff_even_count hpos hdep, hc]
    by_cases hv : valuation n = k
    · rw [if_pos hv]
      have hm := hres.2.mp hv
      split_ifs with heven
      · have hc := Nat.even_iff.mp heven
        have hpow : 0 < 2 ^ k := by positivity
        simp only [Nat.even_iff]
        omega
      · have hc : countAt A k % 2 ≠ 0 := fun h => heven (Nat.even_iff.mpr h)
        simp only [Nat.even_iff]
        omega
    · rw [if_neg hv, Nat.add_zero]
      have hm := hz.mp hv
      split_ifs with heven
      · exact iff_of_true heven hm
      · have hpow : 0 < 2 ^ k := by positivity
        exact iff_of_false heven (by omega)

/-- Every full eventual SG period also preserves the exact zero residue. -/
theorem zero_residue_period_dvd {A : Position} (hp : Positive A) {k T : ℕ}
    (hk : HasDepth A k) (hT : HasTailPeriod A T) : 2 ^ (k + 1) ∣ T := by
  classical
  obtain ⟨N, hN⟩ := hT
  let p := 2 ^ (k + 1)
  let r := if Even (countAt A k) then 0 else 2 ^ k
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hrp : r < p := by
    dsimp [r, p]
    split_ifs <;> simp [pow_succ]
  let n := p * (N + 1) + r
  have hn : N ≤ n := by dsimp [n]; nlinarith
  have hn0 : 0 < n := by dsimp [n]; nlinarith
  have hnr : n % p = r := by simp [n, Nat.add_mod, Nat.mod_eq_of_lt hrp]
  have hz : grundy (n ::ₘ A) = 0 := (fixed_zero_residue hp hk hn0).mpr hnr
  have hz' : grundy ((n + T) ::ₘ A) = 0 := (hN n hn).trans hz
  have hmod := (fixed_zero_residue hp hk (show 0 < n + T by omega)).mp hz'
  have he : Nat.ModEq p n (n + T) := hnr.trans hmod.symm
  have hd := he.dvd'
  simpa only [Nat.add_sub_cancel_left] using hd

private theorem depth_one_of_gcd_two {A : Position} (hp : Positive A) (hg : A.gcd = 2) :
    HasDepth A 1 := by
  have ha : A ≠ 0 := by intro h; simp [h] at hg
  obtain ⟨k, hk⟩ := exists_depth ha
  obtain ⟨x, hx, hvx⟩ := hk.2
  have hlo : 1 ≤ k := by
    have hd : 2 ∣ x := hg ▸ Multiset.gcd_dvd hx
    have hv := (padicValNat_dvd_iff_le (p := 2) (n := 1)
      (by have := hp x hx; omega)).mp hd
    simpa [← hvx] using hv
  have hdiv : 2 ^ k ∣ A.gcd := Multiset.dvd_gcd.mpr (by
    intro y hy
    exact (Nat.pow_dvd_pow 2 (hk.1 y hy)).trans pow_padicValNat_dvd)
  have hhi : k ≤ 1 := by
    have hv := valuation_le_of_dvd (by decide : 0 < 2) (hg ▸ hdiv)
    simpa using hv
  have : k = 1 := by omega
  simpa [this] using hk

/-- The zero convention is included: n=0 contributes no extra heap. -/
theorem gcd_two_zero_pattern {A : Position} (hp : Positive A) (hg : A.gcd = 2)
    (n : ℕ) : fixedSequence A n = 0 ↔ n % 4 = sixZeroPhase A := by
  have hk := depth_one_of_gcd_two hp hg
  by_cases hn : n = 0
  · subst n
    change grundy A = 0 ↔ 0 % 4 = sixZeroPhase A
    rw [zero_iff_even_count hp hk]
    unfold sixZeroPhase
    split_ifs <;> simp_all
  · have he := fixed_zero_residue hp hk (show 0 < n by omega)
    simpa [fixedSequence, adjoinHeap, hn, sixZeroPhase] using he

private theorem successor_nonempty {A : Position} (hc : 2 ≤ A.card)
    {h d : ℕ} (hh : h ∈ A) : successor A h d ≠ 0 := by
  have he := Multiset.card_erase_add_one hh
  have hn : A.erase h ≠ 0 := by intro hz; simp [hz] at he; omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hn
  intro hz
  have hm := successor_mem_erase (d := d) hx
  simp [hz] at hm

/-- At odd varying heaps all fixed moves have losing followers, and subtracting
one from any fixed heap supplies an actual such move. -/
theorem gcd_two_odd_fixed_values {A : Position} (hp : Positive A) (hg : A.gcd = 2)
    {n : ℕ} (hn : n % 2 = 1) : fixedMoveValues A n = {0} := by
  classical
  have hk := depth_one_of_gcd_two hp hg
  have hn0 : n ≠ 0 := by omega
  have hvn : valuation n = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega)
  have hz : ∀ h ∈ A, ∀ d, legal A h d → d ∣ n →
      fixedSequence (successor A h d) n = 0 := by
    intro h hh d hd hdn
    have hvd : valuation d = 0 := padicValNat.eq_zero_of_not_dvd (by
      intro he; have := Nat.mod_eq_zero_of_dvd (he.trans hdn); omega)
    obtain ⟨hdep, hcount⟩ := lower_move hp hk hh hd hvd (by omega)
    have hpos : Positive (n ::ₘ successor A h d) := by
      intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · omega
      · exact successor_positive hp hh hd x hx
    have hdep' : HasDepth (n ::ₘ successor A h d) 0 :=
      ⟨fun _ _ => Nat.zero_le _, n, by simp, hvn⟩
    have hcount' : countAt (n ::ₘ successor A h d) 0 = 2 := by
      change (n ::ₘ successor A h d).countP (fun x => valuation x = 0) = 2
      rw [Multiset.countP_cons, if_pos hvn]
      change countAt (successor A h d) 0 + 1 = 2
      omega
    simp only [fixedSequence, adjoinHeap, if_neg hn0]
    exact (zero_iff_even_count hpos hdep').mpr (by rw [hcount']; decide)
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · have ha : A ≠ 0 := by intro he; simp [he] at hg
    obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero ha
    have hd : legal A h 1 := ⟨by omega, hp h hh, fun _ _ => one_dvd _⟩
    refine Finset.mem_image.mpr ⟨(h, 1), Finset.mem_filter.mpr
      ⟨mem_fixedMoveData.mpr ⟨hh, hd⟩, one_dvd _⟩, hz h hh 1 hd (one_dvd _)⟩
  · intro v hv
    obtain ⟨⟨h, d⟩, hhd, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hdata', hdn⟩ := Finset.mem_filter.mp hhd
    obtain ⟨hh, hd⟩ := mem_fixedMoveData.mp hdata'
    exact hz h hh d hd hdn

/-- The literal gcd-two recurrence, including the boundary n=2. -/
theorem gcd_two_recurrence {A : Position} (hp : Positive A) (hg : A.gcd = 2)
    {n : ℕ} (hn : 2 ≤ n) : fixedSequence A n =
      mex ({fixedSequence A (n - 1), fixedSequence A (n - 2)} ∪ fixedMoveValues A n) := by
  classical
  have ha : A ≠ 0 := by intro he; simp [he] at hg
  have hr := fixed_board_recurrence hp ha (show A.gcd ≤ n by omega)
  change grundy (adjoinHeap A n) = _
  rw [grundy_eq, hr, hg, show (2 : ℕ).divisors = {1, 2} by decide]
  simp

/-- Exact odd recurrence and its full positive value range. -/
theorem gcd_two_odd_recurrence {A : Position} (hp : Positive A) (hg : A.gcd = 2)
    {n : ℕ} (hn : 3 ≤ n) (ho : n % 2 = 1) :
    fixedSequence A n = mex {0, fixedSequence A (n - 1), fixedSequence A (n - 2)} ∧
      1 ≤ fixedSequence A n ∧ fixedSequence A n ≤ 3 := by
  classical
  have he := gcd_two_recurrence hp hg (show 2 ≤ n by omega)
  rw [gcd_two_odd_fixed_values hp hg ho] at he
  have hs : ({fixedSequence A (n - 1), fixedSequence A (n - 2)} ∪ {0} : Finset ℕ) =
      {0, fixedSequence A (n - 1), fixedSequence A (n - 2)} := by
    ext v
    simp [or_comm, or_left_comm, or_assoc]
  rw [hs] at he
  refine ⟨he, ?_, ?_⟩
  · have hz := (mex_spec {0, fixedSequence A (n - 1), fixedSequence A (n - 2)}).1
    rw [he]
    by_contra hn
    have hm : mex {0, fixedSequence A (n - 1), fixedSequence A (n - 2)} = 0 := by omega
    exact hz (by rw [hm]; simp)
  · rw [he]
    exact (mex_le_card _).trans (by
      have h₁ := Finset.card_insert_le 0 {fixedSequence A (n - 1), fixedSequence A (n - 2)}
      have h₂ := Finset.card_insert_le (fixedSequence A (n - 1)) {fixedSequence A (n - 2)}
      simp only [Finset.card_singleton] at h₂
      omega)

/-- The H=2 case uses a nonempty actual successor, rather than the empty board. -/
theorem gcd_two_four_dvd_spacing {A : Position} (hp : Positive A)
    (hc : 2 ≤ A.card) (hg : A.gcd = 2) : 4 ∣ comparisonSpacing A := by
  classical
  have ha : A ≠ 0 := by intro he; simp [he] at hg
  obtain ⟨hH, _⟩ := fixed_minimum_spec ha
  have hall : ∀ x ∈ A, 2 ∣ x := by
    intro x hx
    rw [← hg]
    exact Multiset.gcd_dvd hx
  have hsig := comparison_spacing_signal hp ha
  by_cases he : fixedMinimum A = 2
  · have htwo : 2 ∈ A := he ▸ hH
    have hd : legal A 2 2 := ⟨by decide, le_rfl,
      fun x hx => hall x (Multiset.mem_of_mem_erase hx)⟩
    let B := successor A 2 2
    have hB : B ∈ moves A := successor_is_move htwo hd
    have hnB : B ≠ 0 := successor_nonempty hc htwo
    have hpB : Positive B := successor_positive hp htwo hd
    obtain ⟨k, hk⟩ := exists_depth hnB
    have hk1 : 1 ≤ k := by
      obtain ⟨x, hx, hv⟩ := hk.2
      have hxA : x ∈ A := by
        have hx' : x ∈ A.erase 2 := by simpa [B, successor] using hx
        exact Multiset.mem_of_mem_erase hx'
      have hv' := valuation_le_of_dvd (hp x hxA) (hall x hxA)
      have hv2 : valuation 2 = 1 := by norm_num
      omega
    have hpdiv := zero_residue_period_dvd hpB hk (fixed_board_least_period hpB hnB).2.1
    have hfour : 4 ∣ 2 ^ (k + 1) := by
      exact Nat.pow_dvd_pow 2 (show 2 ≤ k + 1 by omega)
    exact hfour.trans (hpdiv.trans (hsig.2.2.1 B hB hnB))
  · have hH2 := hall _ hH
    have hHpos := hp _ hH
    have hHge : 4 ≤ fixedMinimum A := by omega
    exact (Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by decide, hHge⟩)).trans hsig.2.1

private theorem fixed_sets_equal {A : Position} (hc : 2 ≤ A.card)
    {n : ℕ} (hn : 0 < n) : fixedMoveValues A n = fixedValues A n := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨⟨h, d⟩, hhd, hv⟩ := Finset.mem_image.mp hv
    obtain ⟨hdata, hdn⟩ := Finset.mem_filter.mp hhd
    obtain ⟨hh, hd⟩ := mem_fixedMoveData.mp hdata
    simp only [fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    refine ⟨h, Multiset.mem_toFinset.mpr hh, d,
      ⟨Finset.mem_Icc.mpr ⟨hd.1, hd.2.1⟩, hd, hdn, successor_nonempty hc hh⟩, ?_⟩
    simpa [fixedSequence, adjoinHeap, Nat.ne_of_gt hn] using hv
  · intro hv
    simp only [fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨h, hh, d, ⟨_, hd, hdn, _⟩, hv⟩ := hv
    refine Finset.mem_image.mpr ⟨(h, d), Finset.mem_filter.mpr
      ⟨mem_fixedMoveData.mpr ⟨Multiset.mem_toFinset.mp hh, hd⟩, hdn⟩, ?_⟩
    simpa [fixedSequence, adjoinHeap, Nat.ne_of_gt hn] using hv

private theorem fixed_move_values_tail {A : Position} (hp : Positive A)
    (hc : 2 ≤ A.card) : ∃ N, ∀ n, N ≤ n →
      fixedMoveValues A (n + comparisonSpacing A) = fixedMoveValues A n := by
  have ha : A ≠ 0 := by intro h; simp [h] at hc
  obtain ⟨N, hN⟩ := (comparison_spacing_signal hp ha).2.2.2
  refine ⟨N + 1, ?_⟩
  intro n hn
  rw [fixed_sets_equal hc (by omega), fixed_sets_equal hc (by omega)]
  exact hN n (by omega)

private theorem mex_zero_pair (x : ℕ) : mex {0, x} = if x = 1 then 2 else 1 := by
  classical
  by_cases hx : x = 1
  · rw [if_pos hx, hx]
    apply IsLeast.unique (s := {n : ℕ | n ∉ _})
      (show IsLeast {n : ℕ | n ∉ _} (mex _) from
        ⟨(mex_spec _).1, fun m hm => by
          by_contra hn
          exact hm ((mex_spec _).2 m (by omega))⟩)
    constructor
    · simp
    · intro m hnot
      by_contra hle
      apply hnot
      have hm : m < _ := Nat.lt_of_not_ge hle
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> simp
  · rw [if_neg hx]
    apply IsLeast.unique (s := {n : ℕ | n ∉ _})
      (show IsLeast {n : ℕ | n ∉ _} (mex _) from
        ⟨(mex_spec _).1, fun m hm => by
          by_contra hn
          exact hm ((mex_spec _).2 m (by omega))⟩)
    constructor
    · simp [hx, Ne.symm hx]
    · intro m hnot
      by_contra hle
      apply hnot
      have hm : m < _ := Nat.lt_of_not_ge hle
      have : m = 0 := by omega
      simp [this]

private theorem phase_transition (x : ℕ) (S : Finset ℕ) :
    let a := mex {0, x}
    let b := mex ({0, a} ∪ S)
    mex {0, a, b} =
      if x = 1 then (if 1 ∈ S then 1 else 3) else (if 2 ∈ S then 2 else 3) := by
  classical
  dsimp only
  rw [mex_zero_pair]
  by_cases hx : x = 1
  · simp only [if_pos hx]
    by_cases h1 : 1 ∈ S
    · rw [if_pos h1]
      have hb : mex ({0, 2} ∪ S) ≠ 1 := by
        intro he
        exact (mex_spec _).1 (by rw [he]; simp [h1])
      apply IsLeast.unique (s := {n : ℕ | n ∉ _})
        (show IsLeast {n : ℕ | n ∉ _} (mex _) from
          ⟨(mex_spec _).1, fun m hm => by
            by_contra hn
            exact hm ((mex_spec _).2 m (by omega))⟩)
      constructor
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by decide, by decide, Ne.symm hb⟩
      · intro m hnot
        by_contra hle
        apply hnot
        have hm : m < _ := Nat.lt_of_not_ge hle
        have : m = 0 := by omega
        simp [this]
    · rw [if_neg h1]
      have hb : mex ({0, 2} ∪ S) = 1 := by
        apply IsLeast.unique (s := {n : ℕ | n ∉ _})
          (show IsLeast {n : ℕ | n ∉ _} (mex _) from
            ⟨(mex_spec _).1, fun m hm => by
              by_contra hn
              exact hm ((mex_spec _).2 m (by omega))⟩)
        constructor
        · simp [h1]
        · intro m hnot
          by_contra hle
          apply hnot
          have hm : m < _ := Nat.lt_of_not_ge hle
          have : m = 0 := by omega
          simp [this]
      rw [hb]
      apply IsLeast.unique (s := {n : ℕ | n ∉ _})
        (show IsLeast {n : ℕ | n ∉ _} (mex _) from
          ⟨(mex_spec _).1, fun m hm => by
            by_contra hn
            exact hm ((mex_spec _).2 m (by omega))⟩)
      constructor
      · simp
      · intro m hnot
        by_contra hle
        apply hnot
        have hm : m < _ := Nat.lt_of_not_ge hle
        interval_cases m <;> simp
  · simp only [if_neg hx]
    by_cases h2 : 2 ∈ S
    · rw [if_pos h2]
      have hb : mex ({0, 1} ∪ S) ≠ 2 := by
        intro he
        exact (mex_spec _).1 (by rw [he]; simp [h2])
      apply IsLeast.unique (s := {n : ℕ | n ∉ _})
        (show IsLeast {n : ℕ | n ∉ _} (mex _) from
          ⟨(mex_spec _).1, fun m hm => by
            by_contra hn
            exact hm ((mex_spec _).2 m (by omega))⟩)
      constructor
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by decide, by decide, Ne.symm hb⟩
      · intro m hnot
        by_contra hle
        apply hnot
        have hm : m < _ := Nat.lt_of_not_ge hle
        interval_cases m <;> simp
    · rw [if_neg h2]
      have hb : mex ({0, 1} ∪ S) = 2 := by
        apply IsLeast.unique (s := {n : ℕ | n ∉ _})
          (show IsLeast {n : ℕ | n ∉ _} (mex _) from
            ⟨(mex_spec _).1, fun m hm => by
              by_contra hn
              exact hm ((mex_spec _).2 m (by omega))⟩)
        constructor
        · simp [h2]
        · intro m hnot
          by_contra hle
          apply hnot
          have hm : m < _ := Nat.lt_of_not_ge hle
          interval_cases m <;> simp
      rw [hb]
      apply IsLeast.unique (s := {n : ℕ | n ∉ _})
        (show IsLeast {n : ℕ | n ∉ _} (mex _) from
          ⟨(mex_spec _).1, fun m hm => by
            by_contra hn
            exact hm ((mex_spec _).2 m (by omega))⟩)
      constructor
      · simp
      · intro m hnot
        by_contra hle
        apply hnot
        have hm : m < _ := Nat.lt_of_not_ge hle
        interval_cases m <;> simp

/-- Every gcd-two fixed board with at least two occurrences has its actual
comparison spacing as a full SG period. The least-period multiplier is one. -/
theorem gcd_two_spacing {A : Position} (hp : Positive A) (hc : 2 ≤ A.card)
    (hg : A.gcd = 2) :
    (∃ N, ∀ n, N ≤ n →
      fixedSequence A (n + comparisonSpacing A) = fixedSequence A n) ∧
    leastTailPeriod A ∣ comparisonSpacing A ∧
    leastTailPeriod A / Nat.gcd (leastTailPeriod A) (comparisonSpacing A) = 1 := by
  classical
  have ha : A ≠ 0 := by intro he; simp [he] at hg
  have hfour := gcd_two_four_dvd_spacing hp hc hg
  obtain ⟨N, hN⟩ := fixed_move_values_tail hp hc
  let W := comparisonSpacing A
  obtain ⟨w, hw⟩ := hfour
  have hr : sixZeroPhase A = 0 ∨ sixZeroPhase A = 2 := by
    unfold sixZeroPhase
    split_ifs <;> simp
  let z := 4 * (N + 3) + sixZeroPhase A
  have hz : 3 ≤ z ∧ N ≤ z ∧ z % 4 = sixZeroPhase A ∧ z % 2 = 0 := by
    rcases hr with hr | hr <;> dsimp [z] <;> rw [hr] <;> omega
  let f := fixedSequence A
  let a := fun t => f (z + 4 * t + 1)
  let b := fun t => f (z + 4 * t + 2)
  let c := fun t => f (z + 4 * t + 3)
  let S := fun t => fixedMoveValues A (z + 4 * t + 2)
  have hzero : ∀ t, fixedSequence A (z + 4 * t) = 0 := by
    intro t
    exact (gcd_two_zero_pattern hp hg _).mpr (by omega)
  have hA : ∀ t, a (t + 1) = mex {0, c t} := by
    intro t
    have he := (gcd_two_odd_recurrence hp hg
      (show 3 ≤ z + 4 * (t + 1) + 1 by omega) (by omega)).1
    have h₁ : z + 4 * (t + 1) + 1 - 1 = z + 4 * (t + 1) := by omega
    have h₂ : z + 4 * (t + 1) + 1 - 2 = z + 4 * t + 3 := by omega
    rw [h₁, h₂, hzero (t + 1)] at he
    simpa [a, c, f] using he
  have hB : ∀ t, b t = mex ({0, a t} ∪ S t) := by
    intro t
    have he := gcd_two_recurrence hp hg (show 2 ≤ z + 4 * t + 2 by omega)
    have h₁ : z + 4 * t + 2 - 1 = z + 4 * t + 1 := by omega
    have h₂ : z + 4 * t + 2 - 2 = z + 4 * t := by omega
    rw [h₁, h₂, hzero t] at he
    simpa [b, a, S, f, Finset.pair_comm] using he
  have hC : ∀ t, c t = mex {0, a t, b t} := by
    intro t
    have he := (gcd_two_odd_recurrence hp hg
      (show 3 ≤ z + 4 * t + 3 by omega) (by omega)).1
    have h₁ : z + 4 * t + 3 - 1 = z + 4 * t + 2 := by omega
    have h₂ : z + 4 * t + 3 - 2 = z + 4 * t + 1 := by omega
    rw [h₁, h₂] at he
    have hs : ({0, f (z + 4 * t + 2), f (z + 4 * t + 1)} : Finset ℕ) =
        {0, a t, b t} := by
      ext v
      simp [a, b, or_comm, or_left_comm, or_assoc]
    simpa only [c, f, hs] using he
  have hstep : ∀ t, a (t + 1) = if c t = 1 then 2 else 1 := by
    intro t
    rw [hA, mex_zero_pair]
  have htransition : ∀ t, c (t + 1) =
      if c t = 1 then (if 1 ∈ S (t + 1) then 1 else 3)
      else (if 2 ∈ S (t + 1) then 2 else 3) := by
    intro t
    rw [hC, hB, hA]
    exact phase_transition (c t) (S (t + 1))
  have hnoReturn : ∀ t, c t ≠ 1 → c (t + 1) ≠ 1 := by
    intro t ht
    rw [htransition, if_neg ht]
    split_ifs <;> decide
  have hstable : ∃ t₀ v, (v = 1 ∨ v = 2) ∧ ∀ t, t₀ ≤ t → a t = v := by
    by_cases hstay : ∀ t, c t = 1
    · refine ⟨1, 2, Or.inr rfl, ?_⟩
      intro t ht
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      rw [hstep, if_pos (hstay u)]
    · push Not at hstay
      obtain ⟨t₀, ht₀⟩ := hstay
      have haway : ∀ u, c (t₀ + u) ≠ 1 := by
        intro u
        induction u with
        | zero => simpa using ht₀
        | succ u ih => simpa [Nat.add_assoc] using hnoReturn (t₀ + u) ih
      refine ⟨t₀ + 1, 1, Or.inl rfl, ?_⟩
      intro t ht
      have he : t = (t₀ + (t - (t₀ + 1))) + 1 := by omega
      rw [he, hstep, if_neg (haway _)]
  obtain ⟨t₀, v, _, haConst⟩ := hstable
  have hS : ∀ t, S (t + w) = S t := by
    intro t
    have he : z + 4 * (t + w) + 2 = (z + 4 * t + 2) + comparisonSpacing A := by omega
    dsimp [S]
    rw [he]
    exact hN _ (by omega)
  have hphase : ∀ t, t₀ ≤ t →
      a (t + w) = a t ∧ b (t + w) = b t ∧ c (t + w) = c t := by
    intro t ht
    have heA := (haConst (t + w) (by omega)).trans (haConst t ht).symm
    have heB : b (t + w) = b t := by rw [hB, hB, heA, hS]
    have heC : c (t + w) = c t := by rw [hC, hC, heA, heB]
    exact ⟨heA, heB, heC⟩
  have hperiod : HasTailPeriod A W := by
    refine ⟨z + 4 * t₀, ?_⟩
    intro n hn
    let t := (n - z) / 4
    have hdiv := Nat.mod_add_div (n - z) 4
    have hmod := Nat.mod_lt (n - z) (by decide : 0 < 4)
    have ht : t₀ ≤ t := by dsimp [t]; omega
    have heq : n = z + 4 * t + (n - z) % 4 := by omega
    have heqW : n + W = z + 4 * (t + w) + (n - z) % 4 := by omega
    have hphase' := hphase t ht
    have hvalues : f (n + W) = f n := by
      calc
        f (n + W) = f (z + 4 * (t + w) + (n - z) % 4) := congrArg f heqW
        _ = f (z + 4 * t + (n - z) % 4) := by
          interval_cases hres : (n - z) % 4
          · simpa only [Nat.add_zero] using (hzero (t + w)).trans (hzero t).symm
          · exact hphase'.1
          · exact hphase'.2.1
          · exact hphase'.2.2
        _ = f n := congrArg f heq.symm
    have hn0 : n ≠ 0 := by omega
    have hnW0 : n + W ≠ 0 := by omega
    simpa [f, fixedSequence, adjoinHeap, hn0, hnW0] using hvalues
  have hleast := fixed_board_least_period hp ha
  have hdiv := hleast.2.2 W hperiod
  refine ⟨tail_period_iff_fixed_sequence.mp hperiod, hdiv, ?_⟩
  rw [Nat.gcd_eq_left hdiv, Nat.div_self hleast.1]

end D5.S3.Combinatorics.Games.DivisorNimGrundy
