/- GID: D5/S1/Words/Palindromes/ThueMorseSignedCut
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/ThueMorseSignedCut
   mirror-E: none(waiver:literal-word-reflection)
   anchors: []
   utility: none
   digest: Allowed Thue-Morse factors increase signed weight by at most one. -/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import D5.S1.Words.Palindromes.PeriodDoubling.SignedCutLowerBound

/-! Reflections of literal Thue-Morse factors and the signed cut potential. -/

/-
Per-declaration proof shape and candidate admission basis:
* transition_period_doubling: content; escape-witness candidate is the strong
  induction identifying the original adjacent transition with literal u_pd.
  Live consumer: reflect_derivative.
* allowed_factor_signed_cut: content; escape-witness candidates are
  reflect_derivative and reflect_extend, transporting both literal reflection
  laws and resolving the rounded odd endpoints. Live consumer: mixed_signed_lower.
* combined_prefix_signed_lower: content; escape-witness candidate is the
  induction in mixed_signed_lower that extracts consecutive literal factors
  from an arbitrary nonempty mixed factorization.
The finite-factor definitions are consumed by these proofs. Local arithmetic
and list-normalization helpers supply no separate content claim.
The cut and prefix-lower-bound source bindings remain unfinished:
https://github.com/the-omega-institute/trureturing/issues/26539.
Independent pre-freeze classification and fidelity review remain required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.ThueMorse

open D5.S1.Words.Complexity
open D5.S1.Words.Palindromes.PeriodDoubling

/-- Reversal or exchange followed by reversal fixes the finite binary word. -/
def Allowed (w : List Bool) : Prop :=
  List.Palindrome w ∨ w = w.reverse.map Bool.not

/-- The original adjacent transition is the complement of the literal period-doubling word. -/
theorem transition_period_doubling (n : ℕ) :
    transition n = if u_pd n then 0 else 1 := by
  have val (m : ℕ) : u_pd m = decide (padicValNat 2 (m + 1) % 2 = 1) := by
    have hm : m < 2 ^ (m + 1) := by
      have h := Nat.lt_two_pow_self (n := m + 1)
      omega
    have h := (block_valuation (m + 1)).2 m hm
    simp [u_pd, h]
  have even (m : ℕ) : u_pd (2 * m) = false := by
    rw [val, padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * m + 1)]
    rfl
  have odd (m : ℕ) : u_pd (2 * m + 1) = !u_pd m := by
    have hv : padicValNat 2 (2 * m + 1 + 1) = 1 + padicValNat 2 (m + 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
        padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega), padicValNat_self]
    rw [val, val, hv]
    by_cases h : padicValNat 2 (m + 1) % 2 = 1
    · have hh : (1 + padicValNat 2 (m + 1)) % 2 ≠ 1 := by omega
      simp [h, hh]
    · have hh : (1 + padicValNat 2 (m + 1)) % 2 = 1 := by omega
      simp [h, hh]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, hm | hm⟩ := n.even_or_odd'
    · subst n
      simp [even]
    · subst n
      rw [transition_two_mul_add_one, ih m (by omega), odd]
      cases u_pd m <;> rfl

private def Reflect (start length : ℕ) (flip : Bool) : Prop :=
  ∀ r : ℕ, r < length →
    thueMorse (start + r) = (flip != thueMorse (start + (length - 1 - r)))

private theorem allowed_reflect (start length : ℕ)
    (h : Allowed (factor length start)) : ∃ flip, Reflect start length flip := by
  rcases h with h | h
  · refine ⟨false, ?_⟩
    intro r hr
    have he := congrArg (fun w : List Bool => w[r]?) h.reverse_eq
    simpa [List.getElem?_reverse, factor, hr, show length - 1 - r < length by omega] using he.symm
  · refine ⟨true, ?_⟩
    intro r hr
    have he := congrArg (fun w : List Bool => w[r]?) h
    simpa [List.getElem?_reverse, factor, hr, show length - 1 - r < length by omega] using he

private theorem reflect_derivative (start length : ℕ) (flip : Bool)
    (h : Reflect start length flip) :
    List.Palindrome (List.ofFn (fun r : Fin (length - 1) => u_pd (start + r))) := by
  apply List.Palindrome.of_reverse_eq
  apply List.ext_getElem
  · simp
  · intro r hr hs
    simp only [List.length_reverse, List.length_ofFn] at hr
    rw [List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    have h0 := h r (by omega)
    have h1 := h (r + 1) (by omega)
    have hidx : length - 1 - r = length - 1 - 1 - r + 1 := by omega
    have he : transition (start + (length - 1 - 1 - r)) = transition (start + r) := by
      simp only [transition]
      rw [show start + (length - 1 - 1 - r) + 1 = start + (length - 1 - r) by omega]
      rw [show start + r + 1 = start + (r + 1) by omega, h0, h1]
      have hi : start + (length - 1 - (r + 1)) = start + (length - 1 - 1 - r) := by omega
      rw [hi]
      cases flip <;> cases thueMorse (start + (length - 1 - r)) <;>
        cases thueMorse (start + (length - 1 - 1 - r)) <;> decide
    rw [transition_period_doubling, transition_period_doubling] at he
    have inj (x y : Bool) (h : (if x then 0 else 1 : ℕ) = if y then 0 else 1) : x = y := by
      cases x <;> cases y <;> simp_all
    exact inj _ _ he

private theorem reflect_extend (a b : ℕ) (hab : a < b) (flip : Bool)
    (h : Reflect (2 * a + 1) (2 * (b - a)) flip) :
    Reflect (2 * a) (2 * (b - a) + 2) flip := by
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [show 2 * a + 1 + (2 * (b - a) - 1 - 0) = 2 * b by omega] at h0
  simp only [thueMorse_two_mul_add_one, thueMorse_two_mul] at h0
  intro r hr
  by_cases hz : r = 0
  · subst r
    simp only [Nat.add_zero]
    rw [show 2 * a + (2 * (b - a) + 2 - 1 - 0) = 2 * b + 1 by omega]
    simp only [thueMorse_two_mul, thueMorse_two_mul_add_one]
    cases hf : flip <;> cases ha : thueMorse a <;> cases hb : thueMorse b <;> simp_all
  · by_cases he : r = 2 * (b - a) + 1
    · subst r
      rw [show 2 * a + (2 * (b - a) + 1) = 2 * b + 1 by omega]
      rw [show 2 * (b - a) + 2 - 1 - (2 * (b - a) + 1) = 0 by omega]
      simp only [Nat.add_zero, thueMorse_two_mul, thueMorse_two_mul_add_one]
      cases hf : flip <;> cases ha : thueMorse a <;> cases hb : thueMorse b <;> simp_all
    · have hh := h (r - 1) (by omega)
      have hl : 2 * a + 1 + (r - 1) = 2 * a + r := by omega
      have hr : 2 * a + 1 + (2 * (b - a) - 1 - (r - 1)) =
          2 * a + (2 * (b - a) + 2 - 1 - r) := by omega
      rw [hl, hr] at hh
      exact hh

/-- Every nonempty literal palindrome or antipalindrome has signed potential increment at most one. -/
theorem allowed_factor_signed_cut (i j : ℕ) (hij : i < j)
    (h : Allowed (factor (j - i) i)) :
    signedWeight (j : ℤ) ≤ signedWeight (i : ℤ) + 1 := by
  obtain ⟨flip, hr⟩ := allowed_reflect i (j - i) h
  obtain ⟨hzero, hone, hneg, htri, heven, hodd⟩ := signed_weight_arithmetic
  have even (n : ℕ) : signedWeight ((2 * n : ℕ) : ℤ) = signedWeight (n : ℤ) := by
    push_cast
    exact heven _
  have odd (n : ℕ) : signedWeight ((2 * n + 1 : ℕ) : ℤ) =
      1 + min (signedWeight (n : ℤ)) (signedWeight ((n + 1 : ℕ) : ℤ)) := by
    push_cast
    exact hodd _
  have step (n : ℕ) : signedWeight ((n + 1 : ℕ) : ℤ) ≤ signedWeight (n : ℤ) + 1 ∧
      signedWeight (n : ℤ) ≤ signedWeight ((n + 1 : ℕ) : ℤ) + 1 := by
    constructor
    · simpa [hone] using htri (n : ℤ) 1
    · have ht := htri ((n : ℤ) + 1) (-1)
      simpa [hneg, hone] using ht
  have cut (x y : ℕ) (hxy : x + 1 < y) (hf : Reflect x (y - x) flip) :
      signedWeight ((y / 2 : ℕ) : ℤ) ≤ signedWeight (((x + 1) / 2 : ℕ) : ℤ) + 1 := by
    have hp := reflect_derivative x (y - x) flip hf
    have hc := palindromic_suffix_signed_bound.1 (y - 1) x (by omega)
    rw [show y - 1 - x = y - x - 1 by omega] at hc
    have hb := hc hp
    simpa only [show y - 1 + 1 = y by omega] using hb
  obtain ⟨k, hk | hk⟩ := (j - i).even_or_odd'
  · have hkpos : 0 < k := by omega
    obtain ⟨a, ha | ha⟩ := i.even_or_odd'
    · have hj : j = 2 * (a + k) := by omega
      subst i
      subst j
      rw [even, even]
      have hb := cut (2 * a) (2 * (a + k)) (by omega) hr
      simpa only [show (2 * (a + k)) / 2 = a + k by omega,
        show (2 * a + 1) / 2 = a by omega] using hb
    · have hj : j = 2 * (a + k) + 1 := by omega
      subst i
      subst j
      rw [odd, odd]
      have hb := cut (2 * a + 1) (2 * (a + k) + 1) (by omega) hr
      have hs : Reflect (2 * a + 1) (2 * (a + k - a)) flip := by
        convert hr using 1 <;> congr 1 <;> omega
      have he := reflect_extend a (a + k) (by omega) flip hs
      have hb' := cut (2 * a) (2 * (a + k) + 2) (by omega) (by
        convert he using 1 <;> congr 1 <;> omega)
      simp only [show (2 * (a + k) + 1) / 2 = a + k by omega,
        show (2 * a + 1 + 1) / 2 = a + 1 by omega] at hb
      simp only [show (2 * (a + k) + 2) / 2 = a + k + 1 by omega,
        show (2 * a + 1) / 2 = a by omega] at hb'
      omega
  · have hp := reflect_derivative i (j - i) flip hr
    have hl : j - i - 1 = 2 * k := by omega
    rw [hl] at hp
    have hshort := even_palindrome_length i k hp
    have hlen : j = i + 1 ∨ j = i + 3 := by omega
    rcases hlen with rfl | rfl
    · exact (step i).1
    · have hm := hr 1 (by omega)
      have hleft := hr 0 (by omega)
      have hf : flip = false := by
        simp only [show i + 3 - i = 3 by omega] at hm
        simp only [show 3 - 1 - 1 = 1 by decide] at hm
        cases flip <;> cases thueMorse (i + 1) <;> simp_all
      subst flip
      have he : thueMorse i = thueMorse (i + 2) := by simpa using hleft
      generalize hq : i / 4 = a
      have hv : i = 4 * a + i % 4 := by omega
      have hh : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      rcases hh with hh | hh | hh | hh
      · have hi : i = 2 * (2 * a) := by omega
        have hi' : i + 2 = 2 * (2 * a + 1) := by omega
        rw [hi', hi, thueMorse_two_mul, thueMorse_two_mul,
          thueMorse_two_mul, thueMorse_two_mul_add_one] at he
        cases ht : thueMorse a <;> simp only [ht, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false] at he
      · have hi : i = 2 * (2 * a) + 1 := by omega
        have hi' : i + 2 = 2 * (2 * a + 1) + 1 := by omega
        rw [hi', hi, thueMorse_two_mul_add_one, thueMorse_two_mul_add_one,
          thueMorse_two_mul, thueMorse_two_mul_add_one] at he
        cases ht : thueMorse a <;> simp only [ht, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false] at he
      · have hi : i = 2 * (2 * a + 1) := by omega
        have hi' : i + 3 = 2 * (2 * (a + 1)) + 1 := by omega
        rw [hi', hi]
        simp only [even, odd]
        have hs := step a
        omega
      · have hi : i = 2 * (2 * a + 1) + 1 := by omega
        have hi' : i + 3 = 2 * (2 * (a + 1) + 1) := by omega
        rw [hi', hi]
        simp only [even, odd]
        rw [show 2 * a + 1 + 1 = 2 * (a + 1) by omega, even]
        have hs := step a
        omega

/-- Exactly k nonempty consecutive factors, each a palindrome or an antipalindrome. -/
def MixedFactors (w : List Bool) (k : ℕ) : Prop :=
  ∃ ps : List (List Bool), ps.flatten = w ∧ ps.length = k ∧
    ∀ p ∈ ps, p ≠ [] ∧ Allowed p

private theorem mixed_exists (w : List Bool) : ∃ k, MixedFactors w k := by
  refine ⟨w.length, w.map (fun a => [a]), ?_, by simp, ?_⟩
  · induction w with
    | nil => rfl
    | cons a w ih => simpa using congrArg (List.cons a) ih
  · intro p hp
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨by simp, Or.inl (List.Palindrome.singleton a)⟩

/-- The minimum number of nonempty palindrome or antipalindrome factors. -/
noncomputable def combinedLength (w : List Bool) : ℕ := by
  classical
  exact Nat.find (mixed_exists w)

private theorem factor_add (m n start : ℕ) :
    factor (m + n) start = factor m start ++ factor n (start + m) := by
  simp only [factor, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp [Nat.add_assoc]

private theorem mixed_signed_lower (start n k : ℕ)
    (h : MixedFactors (factor n start) k) :
    signedWeight ((start + n : ℕ) : ℤ) ≤ signedWeight (start : ℤ) + k := by
  obtain ⟨ps, hps, rfl, hp⟩ := h
  induction ps generalizing start n with
  | nil =>
    have hn := congrArg List.length hps
    simp [factor] at hn
    subst n
    simp
  | cons p ps ih =>
    have hn := congrArg List.length hps
    simp only [List.flatten_cons, List.length_append, factor, List.length_map,
      List.length_range] at hn
    have hc : p ++ ps.flatten =
        factor p.length start ++ factor ps.flatten.length (start + p.length) := by
      rw [← factor_add, hn]
      exact hps
    have hpword : p = factor p.length start :=
      List.append_inj_left hc (by simp [factor])
    have htail : ps.flatten = factor ps.flatten.length (start + p.length) :=
      List.append_inj_right hc (by simp [factor])
    have hp0 := hp p (by simp)
    have hpos : 0 < p.length := List.length_pos_iff.mpr hp0.1
    have hcut := allowed_factor_signed_cut start (start + p.length) (by omega) (by
      simpa only [Nat.add_sub_cancel_left, ← hpword] using hp0.2)
    have ht := ih (start + p.length) ps.flatten.length htail (by
      intro q hq
      exact hp q (by simp [hq]))
    simp only [List.length_cons]
    rw [show start + n = start + p.length + ps.flatten.length by omega]
    omega

/-- Every literal prefix has mixed cost at least its signed weight and at most its ordinary palindromic length. -/
theorem combined_prefix_signed_lower (n : ℕ) :
    signedWeight (n : ℤ) ≤ combinedLength (factor n 0) ∧
      combinedLength (factor n 0) ≤ D5.S1.Words.FridPrefix.PL (factor n 0) := by
  classical
  constructor
  · have h := mixed_signed_lower 0 n (combinedLength (factor n 0))
      (Nat.find_spec (mixed_exists (factor n 0)))
    simpa [signed_weight_arithmetic.1] using h
  · have hex : D5.S1.Words.FridPrefix.PalFactors (factor n 0)
        (D5.S1.Words.FridPrefix.PL (factor n 0)) := by
      unfold D5.S1.Words.FridPrefix.PL
      exact Nat.find_spec _
    obtain ⟨ps, hps, hk, hp⟩ := hex
    apply Nat.find_le (show MixedFactors (factor n 0)
      (D5.S1.Words.FridPrefix.PL (factor n 0)) from ?_)
    exact ⟨ps, hps, hk, fun p hp' => ⟨(hp p hp').1, Or.inl (hp p hp').2⟩⟩

end D5.S1.Words.Palindromes.ThueMorse

#print axioms D5.S1.Words.Palindromes.ThueMorse.transition_period_doubling

#print axioms D5.S1.Words.Palindromes.ThueMorse.allowed_factor_signed_cut

#print axioms D5.S1.Words.Palindromes.ThueMorse.combined_prefix_signed_lower
