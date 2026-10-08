/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDescent
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDescent
   mirror-E: none(waiver:mechanical-bispecial-descent)
   anchors: []
   utility: none
   digest: Unique block decoding descends bispecial factors with their physical occurrences. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDesubstitution
import D5.S1.Words.BalancedThreshold.BalancedThresholdBispecial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- Decoding the one- and two-letter majority blocks identifies every occurrence and
transfers both special extensions to a strictly shorter factor of the ratio word. -/
theorem mechanical_bispecial_descent {alpha : ℝ}
    (h0 : 0 < alpha) (hhalf : alpha < 1 / 2) {n : ℕ} (hn : 0 < n)
    (w : Fin n → Bool) (hw : BispecialFactor (lowerMechanicalWord alpha alpha) w) :
    let theta := alpha / (1 - alpha)
    let u := lowerMechanicalWord alpha alpha
    let v := lowerMechanicalWord theta theta
    let pos := Nat.nth (fun i => u i = false)
    ∃ (m : ℕ) (z : Fin m → Bool), m < n ∧ BispecialFactor v z ∧
      List.ofFn w = (List.ofFn z).flatMap
        (fun b => if b then [false, true] else [false]) ++ [false] ∧
      (∀ i, wordFactor u n i = w ↔ ∃ k, pos k = i ∧ wordFactor v m k = z) ∧
      ∀ k, wordFactor v m k = z → pos (k + m) + 1 = pos k + n := by
  classical
  let theta := alpha / (1 - alpha)
  let u := lowerMechanicalWord alpha alpha
  let v := lowerMechanicalWord theta theta
  let pos := Nat.nth (fun i => u i = false)
  let U := fun a i => List.ofFn (wordFactor u a i)
  let V := fun a i => List.ofFn (wordFactor v a i)
  let block := fun b : Bool => if b then [false, true] else [false]
  let enc := fun l : List Bool => l.flatMap block
  have source := mechanical_majority_desubstitution h0 hhalf
  have position : ∀ k, pos k = k + (⌊((k + 1 : ℕ) : ℝ) * theta⌋).toNat :=
    fun k => (source k).1
  have hprefix : ∀ k, U (pos k) 0 = enc (V k 0) := by
    intro k
    change List.ofFn (wordFactor u (pos k) 0) = _
    rw [(source k).2]
    have hv : V k 0 = (List.range k).map v := by
      dsimp only [V, wordFactor]
      rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
      congr 1
      funext r
      simp [wordFactor]
    rw [hv]
    dsimp only [enc]
    rw [List.flatMap_map]
  have splitU : ∀ a b i, U (a + b) i = U a i ++ U b (i + a) := by
    intro a b i
    dsimp only [U, wordFactor]
    rw [List.ofFn_add]
    congr 1
    apply congrArg List.ofFn
    funext r
    simp [wordFactor, Nat.add_assoc]
  have splitV : ∀ a b i, V (a + b) i = V a i ++ V b (i + a) := by
    intro a b i
    dsimp only [V, wordFactor]
    rw [List.ofFn_add]
    congr 1
    apply congrArg List.ofFn
    funext r
    simp [wordFactor, Nat.add_assoc]
  have infinite : (Set.ofPred (fun i => u i = false)).Infinite := by
    intro hf
    have hz := Nat.nth_of_card_le hf (n := hf.toFinset.card + 1) (by omega)
    change pos (hf.toFinset.card + 1) = 0 at hz
    rw [position] at hz
    omega
  have mono : StrictMono pos := Nat.nth_strictMono infinite
  have atpos : ∀ k, u (pos k) = false := Nat.nth_mem_of_infinite infinite
  have pos0 : pos 0 = 0 := by
    have ht0 : 0 < theta := div_pos h0 (by linarith)
    have ht1 : theta < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    simp [position, Int.floor_eq_zero_iff.mpr ⟨ht0.le, ht1⟩]
  have interval : ∀ k m,
      U (pos (k + m) - pos k) (pos k) = enc (V m k) := by
    intro k m
    have hle : pos k ≤ pos (k + m) := mono.monotone (by omega)
    have he := hprefix (k + m)
    rw [← Nat.add_sub_of_le hle, splitU, hprefix k, splitV] at he
    simp only [enc, List.flatMap_append, zero_add] at he
    exact List.append_cancel_left he
  have step : ∀ k, pos (k + 1) = pos k + if v k then 2 else 1 := by
    intro k
    have he := congrArg List.length (interval k 1)
    have hle := mono.monotone (show k ≤ k + 1 by omega)
    simp only [U, List.length_ofFn, V, wordFactor, List.ofFn_succ,
      List.ofFn_zero, enc, List.flatMap_cons, List.flatMap_nil] at he
    cases hv : v k <;> simp [block, hv] at he ⊢ <;> omega
  have next : ∀ k, u (pos k + 1) = v k := by
    intro k
    cases hv : v k with
    | false =>
      have hs : pos (k + 1) = pos k + 1 := by simpa [hv] using step k
      simpa [hs, hv] using atpos (k + 1)
    | true =>
      have hs : pos (k + 1) = pos k + 2 := by simpa [hv] using step k
      have he := interval k 1
      rw [hs, Nat.add_sub_cancel_left] at he
      have hl := congrArg (fun l : List Bool => l[1]?) he
      simpa [U, V, enc, block, wordFactor, List.ofFn_succ, hv] using hl
  have previous : ∀ k, 0 < k → u (pos k - 1) = v (k - 1) := by
    intro k hk
    have hs := step (k - 1)
    rw [Nat.sub_add_cancel hk] at hs
    cases hv : v (k - 1) with
    | false =>
      have he : pos k - 1 = pos (k - 1) := by simp [hv] at hs; omega
      rw [he, atpos]
    | true =>
      have he : pos k - 1 = pos (k - 1) + 1 := by simp [hv] at hs; omega
      rw [he, next, hv]
  have encHead : ∀ l, (enc l ++ [false]).head? = some false := by
    intro l
    cases l with
    | nil => simp [enc]
    | cons b l => cases b <;> simp [enc, block]
  have decode : ∀ l r, enc l ++ [false] = enc r ++ [false] → l = r := by
    intro l
    induction l with
    | nil =>
      intro r he
      cases r with
      | nil => rfl
      | cons b r =>
        have hh := congrArg List.length he
        cases b <;> simp [enc, block] at hh
    | cons b l ih =>
      intro r he
      cases r with
      | nil =>
        have hh := congrArg List.length he
        cases b <;> simp [enc, block] at hh
      | cons c r =>
        cases b <;> cases c
        · simp only [enc, List.flatMap_cons, block, Bool.false_eq_true, if_false,
            List.cons_append, List.cons.injEq, true_and] at he
          exact congrArg (List.cons false) (ih r he)
        · simp only [enc, List.flatMap_cons, block, Bool.false_eq_true, if_false,
            if_true, List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
          have hh := congrArg List.head? he
          rw [encHead l] at hh
          simp at hh
        · simp only [enc, List.flatMap_cons, block, Bool.false_eq_true, if_false,
            if_true, List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
          have hh := congrArg List.head? he
          rw [encHead r] at hh
          simp at hh
        · simp only [enc, List.flatMap_cons, block, if_true, List.cons_append,
            List.nil_append, List.cons.injEq, true_and] at he
          exact congrArg (List.cons true) (ih r he)
  have noaa : ∀ i, ¬ (u i = true ∧ u (i + 1) = true) := by
    intro i ⟨hi, hj⟩
    have ha := (lowerMechanicalWord_eq_true_iff alpha alpha i).mp hi
    have hb := (lowerMechanicalWord_eq_true_iff alpha alpha (i + 1)).mp hj
    unfold lowerMechanicalLetter at ha hb
    have he : ⌊alpha + ((i + 1 + 1 : ℕ) : ℝ) * alpha⌋ =
        ⌊alpha + (i : ℝ) * alpha⌋ + 2 := by omega
    have heR := congrArg (fun z : ℤ => (z : ℝ)) he
    have hlo := Int.floor_le (alpha + ((i + 1 + 1 : ℕ) : ℝ) * alpha)
    have hhi := Int.lt_floor_add_one (alpha + (i : ℝ) * alpha)
    push_cast at heR hlo
    nlinarith
  have before : ∀ i, 0 < i → u i = true → u (i - 1) = false := by
    intro i hi hui
    cases hb : u (i - 1) with
    | false => rfl
    | true =>
      exact (noaa (i - 1) ⟨hb, by simpa only [Nat.sub_add_cancel hi] using hui⟩).elim
  have after : ∀ i, u i = true → u (i + 1) = false := by
    intro i hui
    cases hb : u (i + 1) with
    | false => rfl
    | true => exact (noaa i ⟨hui, hb⟩).elim
  have first : w ⟨0, hn⟩ = false := by
    cases hb : w ⟨0, hn⟩ with
    | false => rfl
    | true =>
      obtain ⟨i, j, hi, hj, hwi, hwj, hne⟩ := hw.1
      have hui : u i = true := by
        simpa only [wordFactor, Nat.add_zero, hb] using congrFun hwi ⟨0, hn⟩
      have huj : u j = true := by
        simpa only [wordFactor, Nat.add_zero, hb] using congrFun hwj ⟨0, hn⟩
      exact (hne ((before i hi hui).trans (before j hj huj).symm)).elim
  have last : w ⟨n - 1, by omega⟩ = false := by
    cases hb : w ⟨n - 1, by omega⟩ with
    | false => rfl
    | true =>
      obtain ⟨i, j, hwi, hwj, hne⟩ := hw.2
      have hui : u (i + (n - 1)) = true := by
        simpa only [wordFactor, hb] using congrFun hwi ⟨n - 1, by omega⟩
      have huj : u (j + (n - 1)) = true := by
        simpa only [wordFactor, hb] using congrFun hwj ⟨n - 1, by omega⟩
      have hi := after _ hui
      have hj := after _ huj
      rw [show i + (n - 1) + 1 = i + n by omega] at hi
      rw [show j + (n - 1) + 1 = j + n by omega] at hj
      exact (hne (hi.trans hj.symm)).elim
  have lift : ∀ i, wordFactor u n i = w →
      ∃ k m, pos k = i ∧ pos (k + m) + 1 = i + n ∧
        U n i = enc (V m k) ++ [false] := by
    intro i hi
    have hi0 : u i = false := by simpa [wordFactor, first] using congrFun hi ⟨0, hn⟩
    have hi1 : u (i + n - 1) = false := by
      have hh := congrFun hi ⟨n - 1, by omega⟩
      simpa only [wordFactor, last, show i + (n - 1) = i + n - 1 by omega] using hh
    let k := Nat.count (fun r => u r = false) i
    let e := Nat.count (fun r => u r = false) (i + n - 1)
    have hk : pos k = i := Nat.nth_count hi0
    have he : pos e = i + n - 1 := Nat.nth_count hi1
    have hke : k ≤ e := Nat.count_monotone _ (by omega)
    refine ⟨k, e - k, hk, ?_, ?_⟩
    · rw [Nat.add_sub_of_le hke, he]
      omega
    · have hh := interval k (e - k)
      rw [Nat.add_sub_of_le hke, he, hk,
        show i + n - 1 - i = n - 1 by omega] at hh
      rw [show n = (n - 1) + 1 by omega, splitU, hh]
      simp [U, wordFactor, hi1, show i + (n - 1) = i + n - 1 by omega]
  obtain ⟨i0, _, _, _, hi0, _, _⟩ := hw.1
  obtain ⟨k0, m, hk0, hend0, hcode0⟩ := lift i0 hi0
  let z := wordFactor v m k0
  have representation : List.ofFn w = enc (List.ofFn z) ++ [false] := by
    change wordFactor u n i0 = w at hi0
    simpa only [U, hi0, z, V] using hcode0
  have len : ∀ l, l.length ≤ (enc l).length := by
    intro l
    induction l with
    | nil => simp [enc]
    | cons b l ih =>
      cases b <;> simp [enc, block] at * <;> omega
  have hmn : m < n := by
    have hh := congrArg List.length representation
    have hm := len (List.ofFn z)
    simp only [List.length_ofFn, List.length_append, List.length_singleton] at hh hm
    omega
  have forward : ∀ i, wordFactor u n i = w →
      ∃ k, pos k = i ∧ pos (k + m) + 1 = i + n ∧ wordFactor v m k = z := by
    intro i hi
    obtain ⟨k, m', hk, hend, hcode⟩ := lift i hi
    have hh : enc (V m' k) ++ [false] = enc (List.ofFn z) ++ [false] := by
      rw [← hcode, ← representation]
      exact congrArg List.ofFn hi
    have hd := decode _ _ hh
    have hm := congrArg List.length hd
    simp only [V, List.length_ofFn] at hm
    subst m'
    exact ⟨k, hk, hend, List.ofFn_inj.mp hd⟩
  have endpoint : ∀ k, wordFactor v m k = z → pos (k + m) + 1 = pos k + n := by
    intro k hk
    have hh := congrArg List.length (interval k m)
    have hr := congrArg List.length representation
    have hle := mono.monotone (show k ≤ k + m by omega)
    simp only [U, V, hk, List.length_ofFn] at hh
    simp only [List.length_ofFn, List.length_append, List.length_singleton] at hr
    omega
  have backward : ∀ k, wordFactor v m k = z → wordFactor u n (pos k) = w := by
    intro k hk
    have hend := endpoint k hk
    have hi : u (pos k + (n - 1)) = false := by
      rw [show pos k + (n - 1) = pos (k + m) by omega, atpos]
    have hh := interval k m
    rw [show pos (k + m) - pos k = n - 1 by omega] at hh
    apply List.ofFn_inj.mp
    change U n (pos k) = List.ofFn w
    calc
      U n (pos k) = U ((n - 1) + 1) (pos k) := congrArg (U · (pos k)) (by omega)
      _ = enc (List.ofFn z) ++ [false] := by
        rw [splitU, hh]
        simp [V, hk, U, wordFactor, hi]
      _ = List.ofFn w := representation.symm
  have special : BispecialFactor v z := by
    constructor
    · obtain ⟨i, j, hi, hj, hwi, hwj, hne⟩ := hw.1
      obtain ⟨ki, hki, _, hzi⟩ := forward i hwi
      obtain ⟨kj, hkj, _, hzj⟩ := forward j hwj
      have hi' : 0 < ki := by
        by_contra hh
        have : ki = 0 := by omega
        rw [this, pos0] at hki
        omega
      have hj' : 0 < kj := by
        by_contra hh
        have : kj = 0 := by omega
        rw [this, pos0] at hkj
        omega
      refine ⟨ki, kj, hi', hj', hzi, hzj, ?_⟩
      intro he
      apply hne
      change u (i - 1) = u (j - 1)
      rw [← hki, ← hkj, previous ki hi', previous kj hj', he]
    · obtain ⟨i, j, hwi, hwj, hne⟩ := hw.2
      obtain ⟨ki, _, hendi, hzi⟩ := forward i hwi
      obtain ⟨kj, _, hendj, hzj⟩ := forward j hwj
      refine ⟨ki, kj, hzi, hzj, ?_⟩
      intro he
      apply hne
      change u (i + n) = u (j + n)
      rw [← hendi, ← hendj, next, next, he]
  change ∃ (m : ℕ) (z : Fin m → Bool), m < n ∧ BispecialFactor v z ∧
    List.ofFn w = enc (List.ofFn z) ++ [false] ∧
    (∀ i, wordFactor u n i = w ↔ ∃ k, pos k = i ∧ wordFactor v m k = z) ∧
    ∀ k, wordFactor v m k = z → pos (k + m) + 1 = pos k + n
  refine ⟨m, z, hmn, special, representation, ?_, endpoint⟩
  intro i
  constructor
  · intro hi
    obtain ⟨k, hk, _, hz⟩ := forward i hi
    exact ⟨k, hk, hz⟩
  · rintro ⟨k, hk, hz⟩
    simpa only [hk] using backward k hz

end D5.S1.Words.BalancedThreshold
