/- GID: D5/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: A target-biased binary reversal order attains the Kasel displacement upper bound. -/

import D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.KaselDisplacementLadderUpper

open D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs

/-- Reverse the low bits of the XOR with a target, so the target has rank zero. -/
private def rank : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, t, x => ((x ^^^ t).testBit 0).toNat * 2 ^ n + rank n (t / 2) (x / 2)

private lemma rank_lt (n t x : ℕ) : rank n t x < 2 ^ n := by
  induction n generalizing t x with
  | zero => simp [rank]
  | succ n ih =>
      have hr := ih (t / 2) (x / 2)
      have hd := Nat.mod_lt (x ^^^ t) (by omega : 0 < 2)
      simp only [rank, Nat.toNat_testBit, Nat.pow_zero, Nat.div_one, pow_succ]
      rcases (by omega : (x ^^^ t) % 2 = 0 ∨ (x ^^^ t) % 2 = 1) with h | h
      all_goals rw [h]; omega

private lemma rank_target (n t : ℕ) : rank n t t = 0 := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [rank, ih]

private lemma rank_injective {n t x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : rank n t x = rank n t y) : x = y := by
  induction n generalizing t x y with
  | zero => simp only [pow_zero] at hx hy; omega
  | succ n ih =>
      have hxq : x / 2 < 2 ^ n := by rw [pow_succ] at hx; omega
      have hyq : y / 2 < 2 ^ n := by rw [pow_succ] at hy; omega
      have hxr := rank_lt n (t / 2) (x / 2)
      have hyr := rank_lt n (t / 2) (y / 2)
      have hxm := Nat.mod_lt x (by omega : 0 < 2)
      have hym := Nat.mod_lt y (by omega : 0 < 2)
      have htm := Nat.mod_lt t (by omega : 0 < 2)
      simp only [rank, Nat.toNat_testBit, Nat.pow_zero, Nat.div_one, Nat.xor_mod_two_eq,
        Nat.add_mod, Nat.mod_mod] at h
      have hp : x % 2 = y % 2 := by
        rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx | hx <;>
          rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy | hy <;>
          rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with ht | ht
        all_goals simp only [hx, hy, ht] at h; norm_num at h; omega
      have hq : rank n (t / 2) (x / 2) = rank n (t / 2) (y / 2) := by
        rw [hp] at h; omega
      have he := ih hxq hyq hq
      omega

/-- At the first differing low bit, an AP's middle term is an extreme. -/
private lemma rank_no_ap {n t a b c : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hap : a + c = 2 * b) :
    ¬ (rank n t a < rank n t b ∧ rank n t b < rank n t c) := by
  induction n generalizing t a b c with
  | zero => simp [rank]
  | succ n ih =>
      intro hord
      have haq : a / 2 < 2 ^ n := by rw [pow_succ] at ha; omega
      have hbq : b / 2 < 2 ^ n := by rw [pow_succ] at hb; omega
      have hcq : c / 2 < 2 ^ n := by rw [pow_succ] at hc; omega
      have har := rank_lt n (t / 2) (a / 2)
      have hbr := rank_lt n (t / 2) (b / 2)
      have hcr := rank_lt n (t / 2) (c / 2)
      have ham := Nat.mod_lt a (by omega : 0 < 2)
      have hbm := Nat.mod_lt b (by omega : 0 < 2)
      have hcm := Nat.mod_lt c (by omega : 0 < 2)
      have htm := Nat.mod_lt t (by omega : 0 < 2)
      have hac : a % 2 = c % 2 := by omega
      simp only [rank, Nat.toNat_testBit, Nat.pow_zero, Nat.div_one, Nat.xor_mod_two_eq,
        Nat.add_mod, Nat.mod_mod] at hord
      by_cases hab : a % 2 = b % 2
      · have hq : a / 2 + c / 2 = 2 * (b / 2) := by omega
        apply ih (t := t / 2) haq hbq hcq hq
        rw [← hab, ← hac] at hord
        omega
      · rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha <;>
          rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb | hb <;>
          rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with ht | ht
        all_goals rw [← hac, ha, hb, ht] at hord
        all_goals norm_num at hord; omega

private def stage (m v : ℕ) : ℕ := if v = 3 ∨ v = 4 then 1 else m

private def position (n v : ℕ) : ℕ :=
  if v % 2 = 0 then rank n 4 v else 2 ^ n + rank n 3 v

private lemma position_injective {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : position n x = position n y) : x = y := by
  have hx4 := rank_lt n 4 x
  have hy4 := rank_lt n 4 y
  have hx3 := rank_lt n 3 x
  have hy3 := rank_lt n 3 y
  by_cases hxe : x % 2 = 0 <;> by_cases hye : y % 2 = 0
  · simp only [position, if_pos hxe, if_pos hye] at h
    exact rank_injective hx hy h
  · simp only [position, if_pos hxe, if_neg hye] at h
    omega
  · simp only [position, if_neg hxe, if_pos hye] at h
    omega
  · simp only [position, if_neg hxe, if_neg hye] at h
    exact rank_injective (t := 3) hx hy (by omega)

private lemma position_no_ap {n a b c : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hc : c < 2 ^ n) (hap : a + c = 2 * b) :
    ¬ (position n a < position n b ∧ position n b < position n c) := by
  have ham := Nat.mod_lt a (by omega : 0 < 2)
  have hcm := Nat.mod_lt c (by omega : 0 < 2)
  have hac : a % 2 = c % 2 := by omega
  by_cases hae : a % 2 = 0 <;> by_cases hbe : b % 2 = 0
  · simpa only [position, if_pos hae, if_pos hbe, if_pos (hac ▸ hae)] using
      (rank_no_ap (t := 4) ha hb hc hap)
  · have hce : c % 2 = 0 := hac ▸ hae
    simp only [position, if_pos hae, if_neg hbe, if_pos hce]
    have := rank_lt n 4 c
    omega
  · have hce : c % 2 ≠ 0 := hac ▸ hae
    simp only [position, if_neg hae, if_pos hbe, if_neg hce]
    have := rank_lt n 4 b
    omega
  · have hce : c % 2 ≠ 0 := hac ▸ hae
    simpa only [position, if_neg hae, if_neg hbe, if_neg hce, Nat.add_lt_add_iff_left]
      using (rank_no_ap (t := 3) ha hb hc hap)

private lemma position_four_le (n v : ℕ) : position n 4 ≤ position n v := by
  have h : position n 4 = 0 := by simp [position, rank_target]
  rw [h]
  exact Nat.zero_le _

private lemma position_three_le {n v : ℕ} (hv : v % 2 ≠ 0) :
    position n 3 ≤ position n v := by simp [position, hv, rank_target]

private lemma sa_data {m v : ℕ} (hv : v ∈ SA m) :
    1 ≤ v ∧ v ≤ 4 ^ m ∧ 2 ≤ block v ∧ Even (block v) := by
  simpa only [SA, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hv

private lemma sa_small {m v : ℕ} (hv : v ∈ SA m) : v = 3 ∨ v = 4 ∨ 9 ≤ v := by
  obtain ⟨hv1, _, hb, he⟩ := sa_data hv
  by_cases h : v ≤ 8
  · have hblock : block v ≤ 3 :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (by norm_num; omega)
    have htwo : block v = 2 := by have := Nat.even_iff.mp he; omega
    have hlo := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (x := v)
    have hhi := Nat.le_pow_clog (by decide : 1 < 2) v
    rw [← block] at hlo hhi
    have hv2 : 1 < v := by
      by_contra hn
      have : v = 1 := by omega
      subst v
      norm_num [block] at hb
    specialize hlo hv2
    rw [htwo] at hlo hhi
    norm_num at hlo hhi
    omega
  · omega

private lemma sa_bit_bound {m v : ℕ} (hv : v ∈ SA m) : v < 2 ^ (2 * m + 1) := by
  have hvhi := (sa_data hv).2.1
  have hp : 4 ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  rw [hp] at hvhi
  have hpos := Nat.two_pow_pos (2 * m)
  rw [pow_succ]
  omega

private lemma sa_block_bound {m v : ℕ} (hv : v ∈ SA m) : block v ≤ 2 * m := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  have hp : 4 ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  simpa only [hp] using (sa_data hv).2.1

/-- An even middle term after 3 sends the other endpoint into an odd block gap. -/
private lemma three_even_gap {m y z : ℕ} (hy : y ∈ SA m) (hz : z ∈ SA m)
    (hylo : 4 < y) (he : y % 2 = 0) (hap : 3 + z = 2 * y) : False := by
  have hy9 : 9 ≤ y := by rcases sa_small hy with h | h | h <;> omega
  have hby : 4 ≤ block y := by
    have hlt : 3 < block y :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
    omega
  have hlo : 2 ^ (block y - 1) < y :=
    Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < y)
  have hhi : y ≤ 2 ^ block y := Nat.le_pow_clog (by decide : 1 < 2) y
  have hp : 2 ^ block y = 2 ^ (block y - 1) * 2 := by
    conv_lhs => rw [show block y = (block y - 1) + 1 by omega]
    rw [pow_succ]
  have hepow : 2 ^ (block y - 1) % 2 = 0 := by
    have h := (by decide : Even (2 : ℕ)).pow_of_ne_zero
      (by omega : block y - 1 ≠ 0)
    exact Nat.even_iff.mp h
  have hzlo : 2 ^ block y < z := by omega
  have hzhi : z ≤ 2 ^ (block y + 1) := by rw [pow_succ]; omega
  have hblock : block z = block y + 1 :=
    block_eq_of_pow_pred_lt_le_pow (by omega) (by simpa using hzlo) hzhi
  have hey := Nat.even_iff.mp (sa_data hy).2.2.2
  have hez := Nat.even_iff.mp (sa_data hz).2.2.2
  rw [hblock] at hez
  omega

private lemma ap_middle_late {m x y z : ℕ} (hx : x ∈ SA m) (hy : y ∈ SA m)
    (hz : z ∈ SA m) (_hxy : x < y) (hyz : y < z) (hap : x + z = 2 * y) :
    4 < y := by
  have hxlo : 3 ≤ x := by rcases sa_small hx with h | h | h <;> omega
  have hzcase := sa_small hz
  rcases sa_small hy with h | h | h
  · omega
  · rcases hzcase with hz | hz | hz <;> omega
  · omega

private lemma early_position {m x y z : ℕ} (hx : x ∈ SA m) (hy : y ∈ SA m)
    (hz : z ∈ SA m) (hxy : x < y) (hyz : y < z) (hap : x + z = 2 * y)
    (hearly : x = 3 ∨ x = 4) : position (2 * m + 1) x < position (2 * m + 1) y := by
  have hne : position (2 * m + 1) x ≠ position (2 * m + 1) y := by
    intro h
    have := position_injective (sa_bit_bound hx) (sa_bit_bound hy) h
    omega
  have hle : position (2 * m + 1) x ≤ position (2 * m + 1) y := by
    rcases hearly with rfl | rfl
    · by_cases he : y % 2 = 0
      · exact (three_even_gap hy hz (ap_middle_late hx hy hz hxy hyz hap) he hap).elim
      · exact position_three_le he
    · exact position_four_le _ _
  omega

private lemma scheme_valid (m : ℕ) (hm : 2 ≤ m) :
    Valid (SA m) (stage m) (position (2 * m + 1)) := by
  constructor
  · intro a ha b hb _ hr
    exact position_injective (sa_bit_bound ha) (sa_bit_bound hb) hr
  · intro x hx y hy z hz hxy hyz hap
    have hylo := ap_middle_late hx hy hz hxy hyz hap
    have hsy : stage m y = m := by simp [stage]; omega
    have hsz : stage m z = m := by simp [stage]; omega
    have hforward := position_no_ap (sa_bit_bound hx) (sa_bit_bound hy) (sa_bit_bound hz) hap
    have hreverse := position_no_ap (sa_bit_bound hz) (sa_bit_bound hy) (sa_bit_bound hx)
      (by omega : z + x = 2 * y)
    by_cases hearly : x = 3 ∨ x = 4
    · have hsx : stage m x = 1 := by simp [stage, hearly]
      have hpos := early_position hx hy hz hxy hyz hap hearly
      constructor
      · intro h
        have hyzpos : position (2 * m + 1) y < position (2 * m + 1) z := by
          simpa only [lexLess, hsy, hsz, lt_self_iff_false, true_and, false_or] using h.2
        exact hforward ⟨hpos, hyzpos⟩
      · simp only [lexLess, hsy, hsz, hsx]
        omega
    · have hsx : stage m x = m := by simp [stage, hearly]
      simpa only [lexLess, hsy, hsz, hsx, lt_self_iff_false, true_and, false_or] using
        And.intro hforward hreverse

private lemma scheme_normalized (m : ℕ) : Normalized (SA m) (stage m) := by
  intro v hv
  by_cases hearly : v = 3 ∨ v = 4
  · rcases hearly with rfl | rfl <;> norm_num [stage, block, Nat.clog]
  · have hb := sa_block_bound hv
    simp only [stage, if_neg hearly]
    omega

theorem upper_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ s r : ℕ → ℕ, Valid (SA m) s r ∧ Normalized (SA m) s ∧
      ∀ v ∈ distinguished, s v ≤ block v / 2 + (m - 2) := by
  refine ⟨stage m, position (2 * m + 1), scheme_valid m hm, scheme_normalized m, ?_⟩
  intro v hv
  simp only [distinguished, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [stage, block, Nat.clog]
  all_goals omega

end D5.S3.Combinatorics.Permutation.KaselDisplacementLadderUpper
