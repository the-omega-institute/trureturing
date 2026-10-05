/- GID: D5/S1/Words/ThueMorseMapFirstStart
   generality: G
   mirror-B: D5/B/S1/Words/ThueMorseMapFirstStart
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: First starts of longest monochromatic Thue-Morse arithmetic progressions. -/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import Mathlib.Tactic.Ring

namespace D5.S1.Words.ThueMorseMapFirstStart

open D5.S1.Words.Complexity

open private thueMorse_zero thueMorse_two_mul thueMorse_two_mul_add_one
  thueMorse_two_pow_add
  from D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd

/-- A monochromatic arithmetic progression in the actual zero-indexed word. -/
def MAP (d s L : Nat) : Prop :=
  ∀ j < L, thueMorse (s + j * d) = thueMorse s

/-- Actual positive attainment, a bound at every start and either color, and firstness. -/
def FirstLongest (d s : Nat) : Prop :=
  ∃ L, 0 < L ∧ MAP d s L ∧
    (∀ a N, MAP d a N → N ≤ L) ∧ (∀ a < s, ¬ MAP d a L)

/- The display in Joshi–Rust, §3.2.2, Conjecture 3.8, omits its ranges.
   This is the contextual e ≥ 2 reading supplied by the preceding maximum formulas.
   The known i(3) = 45 excludes the plus e = 1 extension; it is not a new refutation.
   Recognition and the maximum lengths are attributed to Aedo et al.; their necessary
   binary and all-start arguments are kernel proved inside the settlement. -/
def claim : Prop :=
  ∀ e : Nat, 2 ≤ e →
    let q := 2 ^ e
    FirstLongest (q + 1) (3 * q ^ 2 - q - 1) ∧
    (Even e → FirstLongest (q - 1) (3 * q ^ 2 - q + 1)) ∧
    (Odd e → FirstLongest (q - 1) (q - 1))

theorem result : claim := by
  have block (e a r : Nat) (hr : r < 2 ^ e) :
      thueMorse (a * 2 ^ e + r) = Bool.xor (thueMorse a) (thueMorse r) := by
    induction e generalizing a r with
    | zero =>
        have : r = 0 := by simpa using hr
        subst r
        simp
    | succ e ih =>
        obtain ⟨v, rfl | rfl⟩ := r.even_or_odd'
        · have hv : v < 2 ^ e := by simp only [Nat.pow_succ] at hr; omega
          rw [show a * 2 ^ (e + 1) + 2 * v = 2 * (a * 2 ^ e + v) by
            simp only [Nat.pow_succ]; ring]
          simp only [thueMorse_two_mul, ih a v hv]
        · have hv : v < 2 ^ e := by simp only [Nat.pow_succ] at hr; omega
          rw [show a * 2 ^ (e + 1) + (2 * v + 1) = 2 * (a * 2 ^ e + v) + 1 by
            simp only [Nat.pow_succ]; ring]
          simp only [thueMorse_two_mul_add_one, ih a v hv]
          cases thueMorse a <;> cases thueMorse v <;> rfl
  have complement (e r : Nat) (hr : r < 2 ^ e) :
      thueMorse (2 ^ e - 1 - r) = Bool.xor (thueMorse (2 ^ e - 1)) (thueMorse r) := by
    induction e generalizing r with
    | zero =>
        have : r = 0 := by simpa using hr
        subst r
        simp
    | succ e ih =>
        have hp : 0 < 2 ^ e := Nat.two_pow_pos e
        have hq : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by rw [Nat.pow_succ]; omega
        have top : thueMorse (2 ^ (e + 1) - 1) = !thueMorse (2 ^ e - 1) := by
          rw [show 2 ^ (e + 1) - 1 = 2 ^ e + (2 ^ e - 1) by omega]
          exact thueMorse_two_pow_add e _ (by omega)
        rw [top]
        by_cases h : r < 2 ^ e
        · rw [show 2 ^ (e + 1) - 1 - r = 2 ^ e + (2 ^ e - 1 - r) by omega]
          rw [thueMorse_two_pow_add e _ (by omega), ih r h]
          cases thueMorse (2 ^ e - 1) <;> cases thueMorse r <;> rfl
        · have hr' : r - 2 ^ e < 2 ^ e := by omega
          rw [show 2 ^ (e + 1) - 1 - r = 2 ^ e - 1 - (r - 2 ^ e) by omega]
          have letter := thueMorse_two_pow_add e (r - 2 ^ e) hr'
          rw [show 2 ^ e + (r - 2 ^ e) = r by omega] at letter
          rw [ih _ hr', letter]
          cases thueMorse (2 ^ e - 1) <;> cases thueMorse (r - 2 ^ e) <;> rfl
  have recognize (e : Nat) (he : 1 ≤ e) (B : Nat) (c : Bool)
      (hb : ∀ r < 2 ^ e, thueMorse (B + r) = Bool.xor c (thueMorse r)) :
      (∃ k, B = k * 2 ^ e ∧ thueMorse k = c) ∨
      (∃ k, B = k * 2 ^ e + 2 ^ e / 2 ∧
        thueMorse k = !c ∧ thueMorse (k + 1) = !c) := by
    have t1 : thueMorse 1 = true := by decide
    have t2 : thueMorse 2 = true := by decide
    induction e generalizing B c with
    | zero => omega
    | succ e ih =>
        by_cases he0 : e = 0
        · subst e
          have h0 := hb 0 (by decide)
          have h1 := hb 1 (by decide)
          obtain ⟨k, rfl | rfl⟩ := B.even_or_odd'
          · left
            refine ⟨k, by omega, ?_⟩
            simpa using h0
          · right
            refine ⟨k, by omega, ?_, ?_⟩
            · simpa using congrArg Bool.not h0
            · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at h1
              simpa [t1] using h1
        · have hp : 2 ≤ 2 ^ e := by
            have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ e)
            simpa using h
          have hq : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ]; omega
          obtain ⟨a, hB | hB⟩ := B.even_or_odd'
          · subst B
            have descend (r : Nat) (hr : r < 2 ^ e) :
                thueMorse (a + r) = Bool.xor c (thueMorse r) := by
              have h := hb (2 * r) (by omega)
              rw [show 2 * a + 2 * r = 2 * (a + r) by omega] at h
              simpa using h
            rcases ih (by omega) a c descend with ⟨k, hk, hc⟩ | ⟨k, hk, hc, hc'⟩
            · left
              refine ⟨k, ?_, hc⟩
              rw [hk, hq]
              ring
            · right
              refine ⟨k, ?_, hc, hc'⟩
              rw [hk, hq]
              have heven : 2 * (2 ^ e / 2) = 2 ^ e := by
                have hd : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega : e ≠ 0)
                omega
              rw [show k * (2 * 2 ^ e) = 2 * (k * 2 ^ e) by ring]
              omega
          · subst B
            have h1 := hb 1 (by omega)
            have h2 := hb 2 (by omega)
            rw [show 2 * a + 1 + 1 = 2 * (a + 1) by omega] at h1
            rw [show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega] at h2
            simp [t1, t2] at h1 h2
            cases c <;> cases thueMorse (a + 1) <;> simp_all
  have top (e : Nat) : thueMorse (2 ^ e - 1) = (e % 2 == 1) := by
    induction e with
    | zero => simp
    | succ e ih =>
        have hp : 0 < 2 ^ e := Nat.two_pow_pos e
        rw [show 2 ^ (e + 1) - 1 = 2 ^ e + (2 ^ e - 1) by
          simp only [Nat.pow_succ]; omega]
        rw [thueMorse_two_pow_add e _ (by omega), ih]
        rcases Nat.mod_two_eq_zero_or_one e with he | he <;> simp [Nat.add_mod, he]
  have plus_sample (e a b j h r : Nat) (hr : r < 2 ^ e)
      (hcarry : b + j = h * 2 ^ e + r) :
      thueMorse (a * 2 ^ e + b + j * (2 ^ e + 1)) =
        Bool.xor (thueMorse (a + j + h)) (thueMorse r) := by
    have hi : a * 2 ^ e + b + j * (2 ^ e + 1) = (a + j + h) * 2 ^ e + r := by
      calc
        _ = (a + j) * 2 ^ e + (b + j) := by ring
        _ = _ := by rw [hcarry]; ring
    rw [hi, block e _ _ hr]
  have minus_sample (e a b j h r : Nat) (hr : r < 2 ^ e)
      (hh : h ≤ a + j) (hborrow : j + r = b + h * 2 ^ e) :
      thueMorse (a * 2 ^ e + b + j * (2 ^ e - 1)) =
        Bool.xor (thueMorse (a + j - h)) (thueMorse r) := by
    have hq : 2 ^ e - 1 + 1 = 2 ^ e := by have := Nat.two_pow_pos e; omega
    have hm : j * (2 ^ e - 1) + j = j * 2 ^ e := by
      calc
        _ = j * ((2 ^ e - 1) + 1) := by ring
        _ = _ := by rw [hq]
    have hm' : (a + j - h) * 2 ^ e + h * 2 ^ e = (a + j) * 2 ^ e := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hh]
    have hsum : a * 2 ^ e + b + j * (2 ^ e - 1) + j = (a + j) * 2 ^ e + b := by
      rw [Nat.add_mul]
      omega
    have hi : a * 2 ^ e + b + j * (2 ^ e - 1) = (a + j - h) * 2 ^ e + r := by
      omega
    rw [hi, block e _ _ hr]
  have residues : ∀ e : Nat, 2 ≤ e → ∀ a b : Nat,
    b < 2 ^ e →
    (MAP (2 ^ e + 1) (a * 2 ^ e + b) (2 ^ e + 2) →
      b = 0 ∨ b = 2 ^ e - 2 ∨ b = 2 ^ e - 1) ∧
    (Even e → MAP (2 ^ e - 1) (a * 2 ^ e + b) (2 ^ e + 4) → b = 1) := by
    have cancel (x y z : Bool) (h : Bool.xor x z = Bool.xor y z) : x = y := by
      cases z <;> simpa using h
    have pair_odd (n : Nat) (h : thueMorse n = thueMorse (n + 1)) : n % 2 = 1 := by
      obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
      · rw [thueMorse_two_mul, thueMorse_two_mul_add_one] at h
        exact False.elim (Bool.self_ne_not _ h)
      · omega
    intro e he a b hb
    let q := 2 ^ e
    have hq : 4 ≤ q := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
      simpa [q] using h
    have t1 : thueMorse 1 = true := by decide
    have t2 : thueMorse 2 = true := by decide
    let p := thueMorse (q - 1)
    have low1 : thueMorse (q - 2) = !p := by
      have h := complement e 1 (by omega)
      change thueMorse (q - 1 - 1) = Bool.xor p (thueMorse 1) at h
      simpa only [show q - 1 - 1 = q - 2 by omega, t1, Bool.xor_true] using h
    have low2 : thueMorse (q - 3) = !p := by
      have h := complement e 2 (by omega)
      change thueMorse (q - 1 - 2) = Bool.xor p (thueMorse 2) at h
      simpa only [show q - 1 - 2 = q - 3 by omega, t2, Bool.xor_true] using h
    constructor
    · intro hm
      by_contra bad
      have hb' : 1 ≤ b ∧ b ≤ q - 3 := by change ¬(b = 0 ∨ b = q - 2 ∨ b = q - 1) at bad; omega
      let h := q - 1 - b
      have hlo : 2 ≤ h := by dsimp [h]; omega
      have hhi : h ≤ q - 2 := by dsimp [h]; omega
      let c := thueMorse (a * q + b)
      have sample (j k r : Nat) (hj : j < q + 2) (hr : r < q)
          (hc : b + j = k * q + r) : Bool.xor (thueMorse (a + j + k)) (thueMorse r) = c :=
        (plus_sample e a b j k r hr hc).symm.trans (hm j hj)
      have v0 := sample (h - 2) 0 (q - 3) (by omega) (by omega) (by dsimp [h]; omega)
      have v1 := sample (h - 1) 0 (q - 2) (by omega) (by omega) (by dsimp [h]; omega)
      have v2 := sample (h + 2) 1 1 (by omega) (by omega) (by dsimp [h]; omega)
      have v3 := sample (h + 3) 1 2 (by omega) (by omega) (by dsimp [h]; omega)
      rw [low2] at v0
      rw [low1] at v1
      rw [t1] at v2
      rw [t2] at v3
      have hp0 := cancel _ _ (!p) (v0.trans v1.symm)
      have hp1 := cancel _ _ true (v2.trans v3.symm)
      rw [show a + (h - 1) + 0 = (a + (h - 2) + 0) + 1 by omega] at hp0
      rw [show a + (h + 3) + 1 = (a + (h + 2) + 1) + 1 by omega] at hp1
      have hodd0 := pair_odd _ hp0
      have hodd1 := pair_odd _ hp1
      omega
    · intro hev hm
      have hp : p = false := by
        dsimp [p]
        rw [top]
        simp [Nat.even_iff.mp hev]
      rw [hp] at low1 low2
      have l1 : thueMorse (q - 2) = true := low1
      have l2 : thueMorse (q - 3) = true := low2
      let c := thueMorse (a * q + b)
      have sample (j k r : Nat) (hj : j < q + 4) (hr : r < q)
          (hk : k ≤ a + j) (hc : j + r = b + k * q) :
          Bool.xor (thueMorse (a + j - k)) (thueMorse r) = c :=
        (minus_sample e a b j k r hr hk hc).symm.trans (hm j hj)
      by_cases hb0 : b = 0
      · subst b
        have v0 := sample (q - 2) 1 2 (by omega) (by omega) (by omega) (by omega)
        have v1 := sample (q - 1) 1 1 (by omega) (by omega) (by omega) (by omega)
        have v2 := sample (q + 2) 2 (q - 2) (by omega) (by omega) (by omega) (by omega)
        have v3 := sample (q + 3) 2 (q - 3) (by omega) (by omega) (by omega) (by omega)
        rw [t2] at v0
        rw [t1] at v1
        rw [l1] at v2
        rw [l2] at v3
        have hp0 := cancel _ _ true (v0.trans v1.symm)
        have hp1 := cancel _ _ true (v2.trans v3.symm)
        rw [show a + (q - 1) - 1 = (a + (q - 2) - 1) + 1 by omega] at hp0
        rw [show a + (q + 3) - 2 = (a + (q + 2) - 2) + 1 by omega] at hp1
        have hodd0 := pair_odd _ hp0
        have hodd1 := pair_odd _ hp1
        omega
      · by_contra hb1
        have hb2 : 2 ≤ b := by omega
        have v0 := sample (b - 2) 0 2 (by omega) (by omega) (by omega) (by omega)
        have v1 := sample (b - 1) 0 1 (by omega) (by omega) (by omega) (by omega)
        have v2 := sample (b + 2) 1 (q - 2) (by omega) (by omega) (by omega) (by omega)
        have v3 := sample (b + 3) 1 (q - 3) (by omega) (by omega) (by omega) (by omega)
        rw [t2] at v0
        rw [t1] at v1
        rw [l1] at v2
        rw [l2] at v3
        have hp0 := cancel _ _ true (v0.trans v1.symm)
        have hp1 := cancel _ _ true (v2.trans v3.symm)
        rw [show a + (b - 1) - 0 = (a + (b - 2) - 0) + 1 by omega] at hp0
        rw [show a + (b + 3) - 1 = (a + (b + 2) - 1) + 1 by omega] at hp1
        have hodd0 := pair_odd _ hp0
        have hodd1 := pair_odd _ hp1
        omega
  have plus_barrier : ∀ e : Nat, 2 ≤ e → ∀ a b : Nat,
    b < 2 ^ e → MAP (2 ^ e + 1) (a * 2 ^ e + b) (2 ^ e + 2) →
    ∃ k, 3 ≤ k ∧ a + 2 = k * 2 ^ e ∧ b = 2 ^ e - 1 ∧
      thueMorse (a * 2 ^ e + b + (2 ^ e + 2) * (2 ^ e + 1)) =
      !thueMorse (a * 2 ^ e + b) := by
    have decode (x z c : Bool) (h : Bool.xor x z = c) : x = Bool.xor c z := by
      cases z <;> simpa using h
    have incompatible (x p c : Bool) (h0 : Bool.xor x (!p) = c)
        (h1 : Bool.xor x p = c) : False := by
      have hn : Bool.xor x (!p) = !Bool.xor x p := by cases x <;> cases p <;> rfl
      rw [hn, h1] at h0
      exact Bool.not_ne_self c h0
    have four_eq (n : Nat) : thueMorse (4 * n + 1) = thueMorse (4 * n + 2) := by
      rw [show 4 * n + 1 = 2 * (2 * n) + 1 by omega,
        show 4 * n + 2 = 2 * (2 * n + 1) by omega]
      simp
    have four_three (n : Nat) : thueMorse (4 * n + 3) = thueMorse n := by
      rw [show 4 * n + 3 = 2 * (2 * n + 1) + 1 by omega]
      simp
    have power_factor (e m : Nat) (h : m ≤ e) : 2 ^ e = 2 ^ m * 2 ^ (e - m) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le h]
    intro e he a b hb hm
    let q := 2 ^ e
    let c := thueMorse (a * q + b)
    let p := thueMorse (q - 1)
    have hq : 4 ≤ q := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
      simpa [q] using h
    have t1 : thueMorse 1 = true := by decide
    have t2 : thueMorse 2 = true := by decide
    have low1 : thueMorse (q - 2) = !p := by
      have h := complement e 1 (by omega)
      change thueMorse (q - 1 - 1) = Bool.xor p (thueMorse 1) at h
      simpa only [show q - 1 - 1 = q - 2 by omega, t1, Bool.xor_true] using h
    have sample (j h r : Nat) (hj : j < q + 2) (hr : r < q)
        (hc : b + j = h * q + r) : Bool.xor (thueMorse (a + j + h)) (thueMorse r) = c :=
      (plus_sample e a b j h r hr hc).symm.trans (hm j hj)
    have recognized (B : Nat) (hblock : ∀ r < q, thueMorse (B + r) = Bool.xor c (thueMorse r)) :
        (∃ u, B = 4 * u) ∨ (e = 2 ∧ ∃ k, B = 4 * k + 2 ∧ thueMorse k = !c ∧ thueMorse (k + 1) = !c) := by
      rcases recognize e (by omega) B c hblock with ⟨k, hk, hkc⟩ | ⟨k, hk, hkc, hkp⟩
      · left
        refine ⟨k * 2 ^ (e - 2), ?_⟩
        rw [hk, power_factor e 2 he]
        norm_num
        ring
      · by_cases he2 : e = 2
        · right
          refine ⟨he2, k, ?_, hkc, hkp⟩
          simpa [he2, Nat.mul_comm] using hk
        · left
          refine ⟨2 * k * 2 ^ (e - 3) + 2 ^ (e - 3), ?_⟩
          have hp : q = 8 * 2 ^ (e - 3) := by
            simpa using power_factor e 3 (by omega)
          change B = k * q + q / 2 at hk
          rw [hk, hp]
          rw [show 8 * 2 ^ (e - 3) / 2 = 4 * 2 ^ (e - 3) by omega]
          ring
    have qfour : ∃ v, q = 4 * v := ⟨2 ^ (e - 2), by simpa using power_factor e 2 he⟩
    have hbfinal : b = q - 1 := by
      rcases (residues e he a b hb).1 hm with hb0 | hb2 | hb1
      · change b = 0 at hb0
        have hblock (r : Nat) (hr : r < q) : thueMorse (a + r) = Bool.xor c (thueMorse r) := by
          have h := sample r 0 r (by omega) hr (by omega)
          simpa only [Nat.add_zero] using decode _ _ _ h
        rcases recognized a hblock with ⟨u, hu⟩ | ⟨he2, k, hk, hkc, hkp⟩
        · obtain ⟨v, hv⟩ := qfour
          have h0 := sample q 1 0 (by omega) (by omega) (by omega)
          have h1 := sample (q + 1) 1 1 (by omega) (by omega) (by omega)
          simp only [thueMorse_zero, Bool.xor_false] at h0
          simp only [t1, Bool.xor_true] at h1
          have heq := four_eq (u + v)
          rw [show 4 * (u + v) + 1 = a + q + 1 by omega,
            show 4 * (u + v) + 2 = a + (q + 1) + 1 by omega] at heq
          rw [← heq, h0] at h1
          exact False.elim (Bool.not_ne_self c h1)
        · have hq4 : q = 4 := by simp [q, he2]
          have h0 := sample q 1 0 (by omega) (by omega) (by omega)
          simp only [thueMorse_zero, Bool.xor_false] at h0
          rw [show a + q + 1 = 4 * (k + 1) + 3 by omega, four_three, hkp] at h0
          exact False.elim (Bool.not_ne_self c h0)
      · change b = q - 2 at hb2
        have hblock (r : Nat) (hr : r < q) : thueMorse (a + 3 + r) = Bool.xor c (thueMorse r) := by
          have h := sample (r + 2) 1 r (by omega) hr (by omega)
          rw [show a + (r + 2) + 1 = a + 3 + r by omega] at h
          exact decode _ _ _ h
        have h0 := sample 0 0 (q - 2) (by omega) (by omega) (by omega)
        have h1 := sample 1 0 (q - 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_zero, low1] at h0
        change Bool.xor (thueMorse (a + 1)) p = c at h1
        rcases recognized (a + 3) hblock with ⟨u, hu⟩ | ⟨he2, k, hk, hkc, hkp⟩
        · have heq := four_eq (u - 1)
          rw [show 4 * (u - 1) + 1 = a by omega,
            show 4 * (u - 1) + 2 = a + 1 by omega] at heq
          rw [← heq] at h1
          exact False.elim (incompatible _ _ _ h0 h1)
        · have hp0 : p = false := by
            simpa [p, q, he2] using (show thueMorse 3 = false by decide)
          rw [hp0] at h1
          simp only [Bool.xor_false] at h1
          rw [show a + 1 = 4 * k by omega, show 4 * k = 2 * (2 * k) by omega,
            thueMorse_two_mul, thueMorse_two_mul, hkc] at h1
          exact False.elim (Bool.not_ne_self c h1)
      · exact hb1
    have hblock (r : Nat) (hr : r < q) : thueMorse (a + 2 + r) = Bool.xor c (thueMorse r) := by
      have h := sample (r + 1) 1 r (by omega) hr (by omega)
      rw [show a + (r + 1) + 1 = a + 2 + r by omega] at h
      exact decode _ _ _ h
    rcases recognize e (by omega) (a + 2) c hblock with ⟨k, hk, hkc⟩ | ⟨k, hk, hkc, hkp⟩
    · change a + 2 = k * q at hk
      have hk1 : 1 ≤ k := by
        by_contra h
        have hk0 : k = 0 := by omega
        rw [hk0, Nat.zero_mul] at hk
        omega
      have hleft := sample 0 0 (q - 1) (by omega) (by omega) (by omega)
      simp only [Nat.add_zero] at hleft
      change Bool.xor (thueMorse a) p = c at hleft
      have ha : a = (k - 1) * q + (q - 2) := by
        have hmul : (k - 1) * q + q = k * q := by
          calc
            _ = (k - 1 + 1) * q := by ring
            _ = _ := by rw [Nat.sub_add_cancel hk1]
        omega
      rw [ha, block e _ _ (by omega), low1] at hleft
      have hnleft : thueMorse (k - 1) = !c := by
        have hh : Bool.xor (Bool.xor (thueMorse (k - 1)) (!p)) p =
            !thueMorse (k - 1) := by cases thueMorse (k - 1) <;> cases p <;> rfl
        rw [hh] at hleft
        simpa using congrArg Bool.not hleft
      have hright := sample (q + 1) 2 0 (by omega) (by omega) (by omega)
      simp only [thueMorse_zero, Bool.xor_false] at hright
      have hi : a + (q + 1) + 2 = (k + 1) * q + 1 := by rw [Nat.add_mul]; omega
      rw [hi, block e _ _ (by omega), t1] at hright
      have hnright : thueMorse (k + 1) = !c := by simpa using congrArg Bool.not hright
      have hk3 : 3 ≤ k := by
        by_contra h
        have hh : k = 1 ∨ k = 2 := by omega
        rcases hh with rfl | rfl
        · have : c = true := hkc.symm.trans t1
          rw [this, t2] at hnright
          contradiction
        · have : c = true := hkc.symm.trans t2
          rw [this, t1] at hnleft
          contradiction
      refine ⟨k, hk3, hk, hbfinal, ?_⟩
      have hnext := plus_sample e a b (q + 2) 2 1 (by omega) (by omega)
      have hi' : a + (q + 2) + 2 = (k + 1) * q + 2 := by rw [Nat.add_mul]; omega
      rw [hi', block e _ _ (by omega), t1, t2, hnright] at hnext
      simpa using hnext
    · change a + 2 = k * q + q / 2 at hk
      have hh : thueMorse (q / 2 + 1) = false := by
        have he' : 1 ≤ e - 1 := by omega
        have hp' : 2 ≤ 2 ^ (e - 1) := by
          have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he'
          simpa using h
        have hq' : q / 2 = 2 ^ (e - 1) := by
          have h := power_factor e 1 (by omega)
          change q = 2 * 2 ^ (e - 1) at h
          omega
        rw [hq', thueMorse_two_pow_add (e - 1) 1 (by omega), t1]
        rfl
      have hright := sample (q + 1) 2 0 (by omega) (by omega) (by omega)
      simp only [thueMorse_zero, Bool.xor_false] at hright
      have hi : a + (q + 1) + 2 = (k + 1) * q + (q / 2 + 1) := by rw [Nat.add_mul]; omega
      rw [hi, block e _ _ (by omega), hh, Bool.xor_false, hkp] at hright
      exact False.elim (Bool.not_ne_self c hright)
  have even_minus_barrier : ∀ e : Nat, 2 ≤ e → Even e → ∀ a b : Nat,
    b < 2 ^ e → MAP (2 ^ e - 1) (a * 2 ^ e + b) (2 ^ e + 4) →
    ∃ k, 3 ≤ k ∧ a + 1 = k * 2 ^ e ∧ b = 1 ∧
      thueMorse (a * 2 ^ e + b + (2 ^ e + 4) * (2 ^ e - 1)) =
      !thueMorse (a * 2 ^ e + b) := by
    have decode (x z c : Bool) (h : Bool.xor x z = c) : x = Bool.xor c z := by
      cases z <;> simpa using h
    have power_factor (e m : Nat) (h : m ≤ e) : 2 ^ e = 2 ^ m * 2 ^ (e - m) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le h]
    intro e he hev a b hb hm
    let q := 2 ^ e
    let c := thueMorse (a * q + b)
    have hq : 4 ≤ q := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
      simpa [q] using h
    have t1 : thueMorse 1 = true := by decide
    have t2 : thueMorse 2 = true := by decide
    have hp : thueMorse (q - 1) = false := by
      rw [top]
      simp [Nat.even_iff.mp hev]
    have low1 : thueMorse (q - 2) = true := by
      have h := complement e 1 (by omega)
      change thueMorse (q - 1 - 1) = Bool.xor (thueMorse (q - 1)) (thueMorse 1) at h
      simpa only [show q - 1 - 1 = q - 2 by omega, hp, t1, Bool.false_xor] using h
    have low2 : thueMorse (q - 3) = true := by
      have h := complement e 2 (by omega)
      change thueMorse (q - 1 - 2) = Bool.xor (thueMorse (q - 1)) (thueMorse 2) at h
      simpa only [show q - 1 - 2 = q - 3 by omega, hp, t2, Bool.false_xor] using h
    have hbfinal : b = 1 := (residues e he a b hb).2 hev hm
    have sample (j h r : Nat) (hj : j < q + 4) (hr : r < q)
        (hh : h ≤ a + j) (hc : j + r = b + h * q) :
        Bool.xor (thueMorse (a + j - h)) (thueMorse r) = c :=
      (minus_sample e a b j h r hr hh hc).symm.trans (hm j hj)
    have hblock (r : Nat) (hr : r < q) : thueMorse (a + 1 + r) = Bool.xor c (thueMorse r) := by
      have h := sample (r + 2) 1 (q - 1 - r) (by omega) (by omega) (by omega) (by omega)
      rw [show a + (r + 2) - 1 = a + 1 + r by omega] at h
      have hl := complement e r hr
      change thueMorse (q - 1 - r) = Bool.xor (thueMorse (q - 1)) (thueMorse r) at hl
      rw [hp, Bool.false_xor] at hl
      rw [hl] at h
      exact decode _ _ _ h
    have hleft := sample 0 0 1 (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_zero, Nat.sub_zero, t1, Bool.xor_true] at hleft
    have hright := sample (q + 3) 2 (q - 2) (by omega) (by omega) (by omega) (by omega)
    rw [show a + (q + 3) - 2 = a + 1 + q by omega, low1] at hright
    rcases recognize e (by omega) (a + 1) c hblock with ⟨k, hk, hkc⟩ | ⟨k, hk, hkc, hkp⟩
    · change a + 1 = k * q at hk
      have hk1 : 1 ≤ k := by
        by_contra h
        have hk0 : k = 0 := by omega
        rw [hk0, Nat.zero_mul] at hk
        omega
      have ha : a = (k - 1) * q + (q - 1) := by
        have hmul : (k - 1) * q + q = k * q := by
          calc
            _ = (k - 1 + 1) * q := by ring
            _ = _ := by rw [Nat.sub_add_cancel hk1]
        omega
      rw [ha, block e _ _ (by omega), hp, Bool.xor_false] at hleft
      have hnleft : thueMorse (k - 1) = !c := by simpa using congrArg Bool.not hleft
      have hi : a + 1 + q = (k + 1) * q + 0 := by rw [Nat.add_mul]; omega
      rw [hi, block e _ _ (by omega), thueMorse_zero, Bool.xor_false] at hright
      have hnright : thueMorse (k + 1) = !c := by simpa using congrArg Bool.not hright
      have hk3 : 3 ≤ k := by
        by_contra h
        have hh : k = 1 ∨ k = 2 := by omega
        rcases hh with rfl | rfl
        · have : c = true := hkc.symm.trans t1
          rw [this, t2] at hnright
          contradiction
        · have : c = true := hkc.symm.trans t2
          rw [this, t1] at hnleft
          contradiction
      refine ⟨k, hk3, hk, hbfinal, ?_⟩
      have hnext := minus_sample e a b (q + 4) 2 (q - 3) (by omega) (by omega) (by omega)
      have hi' : a + (q + 4) - 2 = (k + 1) * q + 1 := by rw [Nat.add_mul]; omega
      rw [hi', block e _ _ (by omega), t1, low2, hnright] at hnext
      simpa using hnext
    · change a + 1 = k * q + q / 2 at hk
      have hh : thueMorse (q / 2) = true := by
        have hq' : q / 2 = 2 ^ (e - 1) := by
          have h := power_factor e 1 (by omega)
          change q = 2 * 2 ^ (e - 1) at h
          omega
        rw [hq']
        have h := thueMorse_two_pow_add (e - 1) 0 (Nat.two_pow_pos _)
        simpa using h
      have hi : a + 1 + q = (k + 1) * q + q / 2 := by rw [Nat.add_mul]; omega
      rw [hi, block e _ _ (by omega), hh, hkp] at hright
      simp only [Bool.xor_true, Bool.not_not] at hright
      exact False.elim (Bool.not_ne_self c hright)
  have attainment : ∀ e : Nat, 2 ≤ e →
    MAP (2 ^ e + 1) (3 * (2 ^ e) ^ 2 - 2 ^ e - 1) (2 ^ e + 2) ∧
    (Even e → MAP (2 ^ e - 1) (3 * (2 ^ e) ^ 2 - 2 ^ e + 1) (2 ^ e + 4)) := by
    intro e he
    let q := 2 ^ e
    have hq : 4 ≤ q := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
      simpa [q] using h
    have t1 : thueMorse 1 = true := by decide
    have t2 : thueMorse 2 = true := by decide
    have t3 : thueMorse 3 = false := by decide
    have t4 : thueMorse 4 = true := by decide
    let p := thueMorse (q - 1)
    have low1 : thueMorse (q - 2) = !p := by
      have h := complement e 1 (by omega)
      change thueMorse (q - 1 - 1) = Bool.xor p (thueMorse 1) at h
      simpa only [show q - 1 - 1 = q - 2 by omega, t1, Bool.xor_true] using h
    constructor
    · let a := 3 * q - 2
      have ha : a + 2 = 3 * q := by dsimp [a]; omega
      have hi : a * q + (q - 1) + q + 1 = 3 * q ^ 2 := by
        calc
          _ = (a + 2) * q := by rw [Nat.add_mul]; omega
          _ = _ := by rw [ha]; ring
      have hs : 3 * q ^ 2 - q - 1 = a * q + (q - 1) := by omega
      have hbase : thueMorse (a * q + (q - 1)) = false := by
        rw [block e a _ (by omega), show a = 2 * q + (q - 2) by omega,
          block e 2 _ (by omega), t2, low1]
        change Bool.xor (Bool.xor true (!p)) p = false
        cases p <;> rfl
      change MAP (q + 1) (3 * q ^ 2 - q - 1) (q + 2)
      rw [hs]
      intro j hj
      rw [hbase]
      by_cases hj0 : j = 0
      · subst j
        simpa using hbase
      · by_cases hjq : j ≤ q
        · let r := j - 1
          have hr : r < q := by dsimp [r]; omega
          have h := plus_sample e a (q - 1) j 1 r hr (by dsimp [r]; omega)
          rw [show a + j + 1 = 3 * q + r by dsimp [r]; omega,
            block e 3 r hr, t3] at h
          simpa using h
        · have hj' : j = q + 1 := by omega
          subst j
          have h := plus_sample e a (q - 1) (q + 1) 2 0 (by omega) (by omega)
          rw [show a + (q + 1) + 2 = 4 * q + 1 by omega,
            block e 4 1 (by omega), t4, t1, thueMorse_zero] at h
          simpa using h
    · intro hev
      have hp : p = false := by
        dsimp [p]
        rw [top]
        simp [Nat.even_iff.mp hev]
      let a := 3 * q - 1
      have ha : a + 1 = 3 * q := by dsimp [a]; omega
      have hi : a * q + q = 3 * q ^ 2 := by
        calc
          _ = (a + 1) * q := by ring
          _ = _ := by rw [ha]; ring
      have hs : 3 * q ^ 2 - q + 1 = a * q + 1 := by omega
      have hbase : thueMorse (a * q + 1) = false := by
        rw [block e a 1 (by omega), show a = 2 * q + (q - 1) by omega,
          block e 2 _ (by omega), t2, t1]
        change Bool.xor (Bool.xor true p) true = false
        rw [hp]
        rfl
      change MAP (q - 1) (3 * q ^ 2 - q + 1) (q + 4)
      rw [hs]
      intro j hj
      rw [hbase]
      by_cases hj0 : j = 0
      · subst j
        simpa using hbase
      · by_cases hj1 : j = 1
        · subst j
          have h := minus_sample e a 1 1 0 0 (by omega) (by omega) (by omega)
          rw [show a + 1 - 0 = 3 * q + 0 by omega,
            block e 3 0 (by omega), t3, thueMorse_zero] at h
          simpa using h
        · by_cases hjq : j ≤ q + 1
          · let r := j - 2
            have hr : r < q := by dsimp [r]; omega
            have h := minus_sample e a 1 j 1 (q - 1 - r) (by omega) (by omega) (by dsimp [r]; omega)
            have hl := complement e r hr
            change thueMorse (q - 1 - r) = Bool.xor p (thueMorse r) at hl
            rw [hp, Bool.false_xor] at hl
            rw [show a + j - 1 = 3 * q + r by dsimp [r]; omega,
              block e 3 r hr, t3, hl] at h
            simpa using h
          · have hj' : j = q + 2 ∨ j = q + 3 := by omega
            rcases hj' with rfl | rfl
            · have h := minus_sample e a 1 (q + 2) 2 (q - 1) (by omega) (by omega) (by omega)
              rw [show a + (q + 2) - 2 = 3 * q + (q - 1) by omega,
                block e 3 _ (by omega), t3] at h
              change thueMorse (a * q + 1 + (q + 2) * (q - 1)) = Bool.xor (Bool.xor false p) p at h
              simpa using h
            · have h := minus_sample e a 1 (q + 3) 2 (q - 2) (by omega) (by omega) (by omega)
              rw [show a + (q + 3) - 2 = 4 * q + 0 by omega,
                block e 4 0 (by omega), t4, thueMorse_zero, low1, hp] at h
              simpa using h
  have odd_minus :
    ∀ e : Nat, 2 ≤ e → Odd e → FirstLongest (2 ^ e - 1) (2 ^ e - 1) := by
    intro e he ho
    let q := 2 ^ e
    have hq : 4 ≤ q := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
      simpa [q] using h
    have hq1 : q - 1 + 1 = q := by omega
    have ht : thueMorse (q - 1) = true := by
      rw [top]
      simp [Nat.odd_iff.mp ho]
    have crossing (s : Nat) :
        thueMorse (s + (s % q + 1) * (q - 1)) =
          !thueMorse (s + (s % q) * (q - 1)) := by
      let a := s / q
      let b := s % q
      have hb : b < q := Nat.mod_lt s (by omega)
      have hs : s = a * q + b := by
        dsimp [a, b]
        simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div s q).symm
      have hm : b * (q - 1) + b = b * q := by
        calc
          _ = b * ((q - 1) + 1) := by ring
          _ = _ := by rw [hq1]
      have h0 : s + b * (q - 1) = (a + b) * q := by
        rw [hs, Nat.add_mul]
        omega
      have h1 : s + (b + 1) * (q - 1) = (a + b) * q + (q - 1) := by
        rw [Nat.add_mul]
        omega
      change thueMorse (s + (b + 1) * (q - 1)) = !thueMorse (s + b * (q - 1))
      rw [h0, h1, block e (a + b) (q - 1) (by omega)]
      have hh := block e (a + b) 0 (by omega)
      simp only [Nat.add_zero, thueMorse_zero, Bool.xor_false] at hh
      rw [hh, ht]
      cases thueMorse (a + b) <;> rfl
    have bound (s N : Nat) (h : MAP (q - 1) s N) : N ≤ q := by
      by_contra hN
      have hb : s % q < q := Nat.mod_lt s (by omega)
      have h0 := h (s % q) (by omega)
      have h1 := h (s % q + 1) (by omega)
      have hc := crossing s
      rw [h0, h1] at hc
      exact Bool.not_ne_self (thueMorse s) hc.symm
    have witness : MAP (q - 1) (q - 1) q := by
      intro j hj
      have hm : j * (q - 1) + j = j * q := by
        calc
          _ = j * ((q - 1) + 1) := by ring
          _ = _ := by rw [hq1]
      have hindex : q - 1 + j * (q - 1) = j * q + (q - 1 - j) := by omega
      rw [hindex, block e j _ (by omega), complement e j hj, ht]
      cases thueMorse j <;> rfl
    refine ⟨q, by omega, witness, bound, ?_⟩
    intro s hs h
    have hb : s % q = s := Nat.mod_eq_of_lt (by omega)
    have h0 := h s (by omega)
    have h1 := h (s + 1) (by omega)
    have hc := crossing s
    rw [hb, h0, h1] at hc
    exact Bool.not_ne_self (thueMorse s) hc.symm
  intro e he
  let q := 2 ^ e
  have hq : 4 ≤ q := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
    simpa [q] using h
  have hqq : q ≤ q ^ 2 := by
    calc
      q = q * 1 := by omega
      _ ≤ q * q := Nat.mul_le_mul_left q (by omega)
      _ = q ^ 2 := by ring
  have coordinates (s : Nat) : s = (s / q) * q + s % q := by
    simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div s q).symm
  have plus_all (s : Nat) (hm : MAP (q + 1) s (q + 2)) :
      3 * q ^ 2 - q - 1 ≤ s ∧ thueMorse (s + (q + 2) * (q + 1)) = !thueMorse s := by
    have hb : s % q < q := Nat.mod_lt s (by omega)
    have hm' : MAP (q + 1) ((s / q) * q + s % q) (q + 2) := by
      simpa only [← coordinates s] using hm
    obtain ⟨k, hk3, hk, hres, hnext⟩ := plus_barrier e he (s / q) (s % q) hb hm'
    change s % q = q - 1 at hres
    have hs : s + q + 1 = k * q ^ 2 := by
      calc
        _ = ((s / q) * q + s % q) + q + 1 := by have h := coordinates s; omega
        _ = (s / q + 2) * q := by
          rw [hres, Nat.add_mul]
          omega
        _ = _ := by rw [hk]; ring
    have hbound : 3 * q ^ 2 ≤ k * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hk3
    refine ⟨by omega, ?_⟩
    change thueMorse ((s / q) * q + s % q + (q + 2) * (q + 1)) =
      !thueMorse ((s / q) * q + s % q) at hnext
    rw [← coordinates s] at hnext
    exact hnext
  have minus_all (hev : Even e) (s : Nat) (hm : MAP (q - 1) s (q + 4)) :
      3 * q ^ 2 - q + 1 ≤ s ∧ thueMorse (s + (q + 4) * (q - 1)) = !thueMorse s := by
    have hb : s % q < q := Nat.mod_lt s (by omega)
    have hm' : MAP (q - 1) ((s / q) * q + s % q) (q + 4) := by
      simpa only [← coordinates s] using hm
    obtain ⟨k, hk3, hk, hres, hnext⟩ := even_minus_barrier e he hev (s / q) (s % q) hb hm'
    have hs : s + q = k * q ^ 2 + 1 := by
      calc
        _ = ((s / q) * q + s % q) + q := by have h := coordinates s; omega
        _ = (s / q + 1) * q + 1 := by
          rw [hres, Nat.add_mul]
          omega
        _ = _ := by rw [hk]; ring
    have hbound : 3 * q ^ 2 ≤ k * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hk3
    refine ⟨by omega, ?_⟩
    change thueMorse ((s / q) * q + s % q + (q + 4) * (q - 1)) =
      !thueMorse ((s / q) * q + s % q) at hnext
    rw [← coordinates s] at hnext
    exact hnext
  change FirstLongest (q + 1) (3 * q ^ 2 - q - 1) ∧
    (Even e → FirstLongest (q - 1) (3 * q ^ 2 - q + 1)) ∧
    (Odd e → FirstLongest (q - 1) (q - 1))
  constructor
  · refine ⟨q + 2, by omega, (attainment e he).1, ?_, ?_⟩
    · intro s N hm
      by_contra hN
      have hp : MAP (q + 1) s (q + 2) := fun j hj => hm j (by omega)
      have hnext := (plus_all s hp).2
      have hsame := hm (q + 2) (by omega)
      rw [hsame] at hnext
      exact Bool.self_ne_not (thueMorse s) hnext
    · intro s hs hm
      have hlow := (plus_all s hm).1
      omega
  · constructor
    · intro hev
      refine ⟨q + 4, by omega, (attainment e he).2 hev, ?_, ?_⟩
      · intro s N hm
        by_contra hN
        have hp : MAP (q - 1) s (q + 4) := fun j hj => hm j (by omega)
        have hnext := (minus_all hev s hp).2
        have hsame := hm (q + 4) (by omega)
        rw [hsame] at hnext
        exact Bool.self_ne_not (thueMorse s) hnext
      · intro s hs hm
        have hlow := (minus_all hev s hm).1
        omega
    · exact odd_minus e he

#print axioms result
#check result
end D5.S1.Words.ThueMorseMapFirstStart
