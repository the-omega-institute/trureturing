/- GID: D5/S1/Digit/Infinite/WindowSuccessorGraph
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/WindowSuccessorGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite legal digit windows have an increment cycle with one additional reset edge and exact successor locality. -/

import D5.S1.Digit.Infinite.MultiplierObstruction
import D5.S1.Digit.Infinite.InfiniteSuccessorFibres
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.WindowSuccessorGraph

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.InfiniteSuccessorFibres
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit

/-- Binary words of length L with no adjacent occupied positions. -/
def X (L : ℕ) := {p : Fin L → Bool // ∀ (j : ℕ) (h : j + 1 < L),
  ¬ (p ⟨j, by omega⟩ = true ∧ p ⟨j + 1, h⟩ = true)}

/-- Truncation of an infinite legal digit stream to its first L positions. -/
def P (L : ℕ) (x : LegalDigits) : X L :=
  ⟨fun i => x.val i, fun j _ => x.property j⟩

/-- The sum of a word's occupied Fibonacci weights. -/
def V {L : ℕ} (p : X L) : ℕ :=
  ∑ i : Fin L, Nat.fib (i.val + 2) * (if p.val i then 1 else 0)

/-- The number of legal binary words of length L. -/
def G (L : ℕ) : ℕ := Nat.fib (L + 2)

/-- The value of the branching window for positive L. -/
def beta (L : ℕ) : ℕ := Nat.fib (L + 1) - 1

/-- The adjacent-zero successor as a self-map of legal digit streams. -/
noncomputable def T (x : LegalDigits) : LegalDigits := ⟨next x.val, next_fibres.1 x⟩

/-- Pairs of windows observed before and after one successor step. -/
def R (L : ℕ) (p q : X L) : Prop := ∃ x, P L x = p ∧ P L (T x) = q

set_option maxHeartbeats 800000 in
/-- In Fibonacci coordinates the window graph is the increment cycle with one additional reset.
Every edge occurs on a natural digit row. Successor windows depend uniquely on one extra digit,
and cannot depend on the original window alone. Iterating h times requires only h extra digits. -/
theorem window_successor_graph (L : ℕ) (hL : 1 ≤ L) :
    (∀ s t : ℕ, (∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t) ↔
      ((s < G L - 1 ∧ t = s + 1) ∨ (s = G L - 1 ∧ t = 0) ∨
        (s = beta L ∧ t = 0))) ∧
    (∀ p q : X L, R L p q → ∃ n : ℕ,
      P L (zRow n) = p ∧ P L (T (zRow n)) = q) ∧
    (∃! g : X (L+1) → X L, ∀ x, P L (T x) = g (P (L+1) x)) ∧
    (¬ ∃ f : X L → X L, ∀ n : ℕ, P L (T (zRow n)) = f (P L (zRow n))) ∧
    (∀ s < G L,
      Set.ncard {t : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
        (if s = beta L then 2 else 1)) ∧
    (∀ t < G L,
      Set.ncard {s : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
        (if t = 0 then 2 else 1)) ∧
    (∀ h : ℕ, ∀ x y : LegalDigits, P (L+h) x = P (L+h) y →
      P L (T^[h] x) = P L (T^[h] y)) := by
  classical
  let mass (N : ℕ) (x : ℕ → Bool) : ℕ :=
    ∑ i ∈ Finset.range N, Nat.fib (i + 2) * (if x i then 1 else 0)
  have value (N : ℕ) (x : LegalDigits) : V (P N x) = mass N x.val := by
    simp only [V, P, mass]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
    split <;> simp_all
  let pad (N : ℕ) (p : X N) : LegalDigits :=
    ⟨fun i => if hi : i < N then p.val ⟨i, hi⟩ else false, by
      intro i h
      by_cases hi : i + 1 < N
      · have hi' : i < N := by omega
        simp only [dif_pos hi, dif_pos hi'] at h
        exact p.property i hi h
      · simp only [dif_neg hi, Bool.false_eq_true, and_false] at h⟩
  have pad_prefix (N : ℕ) (p : X N) : P N (pad N p) = p := by
    apply Subtype.ext
    funext i
    simp [P, pad]
  have trunc_surj (N : ℕ) : Function.Surjective (P N) :=
    fun p => ⟨pad N p, pad_prefix N p⟩
  let raw (N : ℕ) (x : LegalDigits) : RawDigits := Finsupp.onFinset (Finset.range N)
    (fun i => if i < N ∧ x.val i = true then 1 else 0)
    (by intro i hi; by_contra h; simp only [Finset.mem_range] at h; simp [h] at hi)
  have canonical (N : ℕ) (x : LegalDigits) : CanonicalRaw (raw N x) := by
    constructor
    · intro i
      change (if i < N ∧ x.val i = true then 1 else 0) ≤ 1
      split <;> omega
    · intro i hi
      change (if i < N ∧ x.val i = true then 1 else 0) = 1 at hi
      have hxi : x.val i = true := by split at hi <;> simp_all
      have hn : x.val (i + 1) ≠ true := fun h => x.property i ⟨hxi, h⟩
      change (if i + 1 < N ∧ x.val (i + 1) = true then 1 else 0) = 0
      simp [hn]
  have raw_value (N : ℕ) (x : LegalDigits) : rawValue (raw N x) = mass N x.val := by
    unfold rawValue
    dsimp only [raw]
    rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi, D5.S0.Conventions.wValue]
  have row_mem (n i : ℕ) :
      (zRow n).val i = true ↔ i ∈ (rawOfZeckendorf (Nat.zeckendorf n)).support := by
    have raw_mem : i ∈ (rawOfZeckendorf (Nat.zeckendorf n)).support ↔
        i + 2 ∈ Nat.zeckendorf n := by
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    rw [raw_mem]
    change decide (zeckendorfBit n i = 1) = true ↔ _
    simp only [decide_eq_true_eq]
    by_cases h : i + 2 ∈ Nat.zeckendorf n <;>
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, h]
  have reencode (N : ℕ) (x : LegalDigits) :
      rawOfZeckendorf (Nat.zeckendorf (mass N x.val)) = raw N x := by
    rw [← raw_value, ← rawToZeckendorf_eq_zeckendorf (canonical N x),
      rawOfZeckendorf_rawToZeckendorf]
  have row_bits (N : ℕ) (x : LegalDigits) (i : ℕ) :
      (zRow (mass N x.val)).val i = if i < N then x.val i else false := by
    have hm := row_mem (mass N x.val) i
    rw [reencode, Finsupp.mem_support_iff] at hm
    change ((zRow (mass N x.val)).val i = true ↔
      (if i < N ∧ x.val i = true then 1 else 0) ≠ 0) at hm
    by_cases hi : i < N <;> cases hx : x.val i <;>
      cases hz : (zRow (mass N x.val)).val i <;> simp_all
  have row_prefix (N : ℕ) (x : LegalDigits) : P N (zRow (V (P N x))) = P N x := by
    rw [value]
    apply Subtype.ext
    funext i
    exact (row_bits N x i).trans (if_pos i.isLt)
  have injective (N : ℕ) : Function.Injective (@V N) := by
    intro p q hpq
    obtain ⟨x, rfl⟩ := trunc_surj N p
    obtain ⟨y, rfl⟩ := trunc_surj N q
    rw [← row_prefix N x, ← row_prefix N y, hpq]
  have bound (N : ℕ) (x : LegalDigits) : mass N x.val < Nat.fib (N + 2) := by
    rw [← raw_value, rawValue_eq_sum_rawToZeckendorf]
    apply List.IsZeckendorfRep.sum_fib_lt ((canonicalRaw_iff_isZeckendorfRep _).mp (canonical N x))
    intro k hk
    have hm := List.mem_of_mem_head? hk
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      have hs : i ∈ (raw N x).support := by
        simpa only [Multiset.mem_sort, Finsupp.mem_toMultiset, Finsupp.mem_support_iff] using hi
      have hn := Finsupp.mem_support_iff.mp hs
      change (if i < N ∧ x.val i = true then 1 else 0) ≠ 0 at hn
      split at hn <;> simp_all <;> omega
    · omega
  have alternating_prefix_mass (x : LegalDigits) (j : ℕ)
      (hz : x.val j = false)
      (hp : ∀ i < j, ¬ (x.val i = false ∧ x.val (i + 1) = false)) :
      mass j x.val + 1 = Nat.fib (j + 2) := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      cases j with
      | zero => simp [mass]
      | succ j =>
        have hx : x.val j = true := by
          cases h : x.val j
          · exact False.elim (hp j (by omega) ⟨h, hz⟩)
          · rfl
        cases j with
        | zero => norm_num [mass, hx, Finset.sum_range_succ]
        | succ j =>
          have hj : x.val j = false := by
            cases h : x.val j
            · rfl
            · exact False.elim (x.property j ⟨h, hx⟩)
          have hm := ih j (by omega) hj (fun i hi => hp i (by omega))
          have hf := Nat.fib_add_two (n := j + 2)
          simp only [mass, Finset.sum_range_succ] at hm ⊢
          rw [hj, hx]
          simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero,
            mul_one, Nat.add_assoc, Nat.reduceAdd] at *
          omega
  have window_increment_of_erased_mass (x : ℕ → Bool) (L j : ℕ) (hj : j < L)
      (pair : x j = false ∧ x (j+1) = false)
      (first : ∀ i < j, ¬ (x i = false ∧ x (i+1) = false))
      (erased_mass : mass j x + 1 = Nat.fib (j+2)) :
      mass L (next x) = mass L x + 1 := by
    classical
    have hp : ∃ i, x i = false ∧ x (i+1) = false := ⟨j,pair⟩
    have hf : Nat.find hp = j := (Nat.find_eq_iff hp).mpr ⟨pair,first⟩
    have low : mass j (next x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i < j := Finset.mem_range.mp hi
      simp only [next, dif_pos hp, hf, if_pos hij, Bool.false_eq_true, ↓reduceIte, mul_zero]
    have atj : mass (j+1) (next x) = Nat.fib (j+2) := by
      dsimp only [mass]
      rw [Finset.sum_range_succ]
      change mass j (next x) + _ = _
      rw [low]
      simp [next, hp, hf]
    have atold : mass (j+1) x = mass j x := by
      simp only [mass, Finset.sum_range_succ, pair.1, Bool.false_eq_true, ↓reduceIte,
        mul_zero, add_zero]
    have tails :
        (∑ i ∈ Finset.range (L-(j+1)), Nat.fib (j+1+i+2) * (if next x (j+1+i) then 1 else 0)) =
        (∑ i ∈ Finset.range (L-(j+1)), Nat.fib (j+1+i+2) * (if x (j+1+i) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [next, dif_pos hp, hf, if_neg (show ¬j+1+i<j by omega),
        if_neg (show j+1+i≠j by omega)]
    have splitmass (y : ℕ → Bool) : mass L y = mass (j+1) y +
        ∑ i ∈ Finset.range (L-(j+1)), Nat.fib (j+1+i+2) * (if y (j+1+i) then 1 else 0) := by
      unfold mass
      rw [← Finset.sum_range_add]
      rw [Nat.add_sub_of_le (show j+1 ≤ L by omega)]
    rw [splitmass (next x), splitmass x, atj, atold, tails]
    omega
  have small_bits (N n : ℕ) (hn : n < Nat.fib (N + 2)) (i : ℕ) (hi : N ≤ i) :
      (zRow n).val i = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have hm : i + 2 ∈ Nat.zeckendorf n := by
      change decide (zeckendorfBit n i = 1) = true at hb
      by_contra hm
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, hm] at hb
    have hsum : Nat.fib (i + 2) ≤ n := by
      have h : Nat.fib (i+2) ≤ ((Nat.zeckendorf n).map Nat.fib).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨i + 2, hm, rfl⟩)
      simpa only [Nat.sum_zeckendorf_fib] using h
    have := Nat.fib_mono (show N + 2 ≤ i + 2 by omega)
    omega
  have small_value (N n : ℕ) (hn : n < Nat.fib (N + 2)) : mass N (zRow n).val = n := by
    have he : raw N (zRow n) = rawOfZeckendorf (Nat.zeckendorf n) := by
      apply Finsupp.ext
      intro i
      have hb := (canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)).1 i
      have hm := row_mem n i
      rw [Finsupp.mem_support_iff] at hm
      change (if i < N ∧ (zRow n).val i = true then 1 else 0) = _
      by_cases hi : i < N
      · cases hx : (zRow n).val i <;> simp_all <;> omega
      · have hx := small_bits N n hn i (by omega)
        simp_all
    rw [← raw_value, he, rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n),
      Nat.sum_zeckendorf_fib]
  have early_step (N : ℕ) (x : LegalDigits)
      (he : ∃ j < N, x.val j = false ∧ x.val (j+1) = false) :
      mass N (next x.val) = mass N x.val + 1 := by
    obtain ⟨j, hj, hp⟩ := he
    have hex : ∃ i, x.val i = false ∧ x.val (i+1) = false := ⟨j, hp⟩
    have hf := Nat.find_spec hex
    have hmin : ∀ i < Nat.find hex, ¬ (x.val i = false ∧ x.val (i+1) = false) :=
      fun _ hi => Nat.find_min hex hi
    have hlt : Nat.find hex < N := lt_of_le_of_lt (Nat.find_min' hex hp) hj
    exact window_increment_of_erased_mass x.val N (Nat.find hex) hlt hf hmin
      (alternating_prefix_mass x (Nat.find hex) hf.1 hmin)
  have noearly_zero (N : ℕ) (x : LegalDigits)
      (he : ∀ j < N, ¬ (x.val j = false ∧ x.val (j+1) = false)) :
      mass N (next x.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hz : next x.val i = false := by
      unfold next
      split
      · rename_i hex
        have hge : N ≤ Nat.find hex := by
          by_contra h
          exact he (Nat.find hex) (by omega) (Nat.find_spec hex)
        simp only [if_pos (show i < Nat.find hex by omega)]
      · rfl
    simp [hz]
  have boundary_value (N : ℕ) (hN : 1 ≤ N) (x : LegalDigits)
      (he : ∀ j < N, ¬ (x.val j = false ∧ x.val (j+1) = false)) :
      (x.val N = false → mass N x.val + 1 = Nat.fib (N+2)) ∧
      (x.val N = true → mass N x.val + 1 = Nat.fib (N+1)) := by
    refine ⟨fun hz => alternating_prefix_mass x N hz he, ?_⟩
    intro hx
    have hn : x.val (N-1) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      apply x.property (N-1)
      exact ⟨hb, by simpa only [Nat.sub_add_cancel hN] using hx⟩
    have hm := alternating_prefix_mass x (N-1) hn (fun i hi => he i (by omega))
    have hv : mass N x.val = mass (N-1) x.val := by
      conv_lhs => rw [← Nat.sub_add_cancel hN]
      simp only [mass, Finset.sum_range_succ, hn, Bool.false_eq_true,
        ↓reduceIte, mul_zero, add_zero]
    rw [hv]
    convert hm using 1 <;> congr 1 <;> omega
  have max_noearly (N : ℕ) (x : LegalDigits)
      (hv : mass N x.val = Nat.fib (N+2) - 1) :
      ∀ j < N, ¬ (x.val j = false ∧ x.val (j+1) = false) := by
    intro j hj hp
    have hs := early_step N x ⟨j, hj, hp⟩
    have hb := bound N (T x)
    change mass N (next x.val) < Nat.fib (N+2) at hb
    omega
  have bounds : 0 < G L ∧ beta L < G L - 1 := by
    have hp : 0 < Nat.fib (L+1) := Nat.fib_pos.mpr (by omega)
    have hs := Nat.fib_add_two_strictMono (show L-1 < L by omega)
    have he : L-1+2 = L+1 := by omega
    change Nat.fib (L-1+2) < Nat.fib (L+2) at hs
    rw [he] at hs
    dsimp [G, beta]
    omega
  have forward (x : LegalDigits) :
      (V (P L x) < G L - 1 ∧ V (P L (T x)) = V (P L x) + 1) ∨
      (V (P L x) = G L - 1 ∧ V (P L (T x)) = 0) ∨
      (V (P L x) = beta L ∧ V (P L (T x)) = 0) := by
    simp only [value]
    by_cases he : ∃ j < L, x.val j = false ∧ x.val (j+1) = false
    · have hs := early_step L x he
      have hb := bound L (T x)
      change mass L (next x.val) < Nat.fib (L+2) at hb
      exact Or.inl ⟨by dsimp [G]; omega, hs⟩
    · have hn : ∀ j < L, ¬ (x.val j = false ∧ x.val (j+1) = false) := by
        intro j hj hp
        exact he ⟨j, hj, hp⟩
      have hz := noearly_zero L x hn
      have hv := boundary_value L hL x hn
      cases hx : x.val L
      · exact Or.inr (Or.inl ⟨by have := hv.1 hx; dsimp [G]; omega, hz⟩)
      · exact Or.inr (Or.inr ⟨by have := hv.2 hx; dsimp [beta]; omega, hz⟩)
  have ordinary (s : ℕ) (hs : s < G L - 1) :
      V (P L (zRow s)) = s ∧ V (P L (T (zRow s))) = s+1 := by
    have hb : s < Nat.fib (L+2) := by dsimp [G] at hs; omega
    have hv := small_value L s hb
    have he : ∃ j < L, (zRow s).val j = false ∧ (zRow s).val (j+1) = false := by
      by_contra he
      have hn : ∀ j < L, ¬ ((zRow s).val j = false ∧ (zRow s).val (j+1) = false) := by
        intro j hj hp
        exact he ⟨j, hj, hp⟩
      have hm := (boundary_value L hL (zRow s) hn).1 (small_bits L s hb L le_rfl)
      dsimp [G] at hs
      omega
    exact ⟨(value L _).trans hv, (value L _).trans ((early_step L _ he).trans (by rw [hv]))⟩
  have reset (N : ℕ) :
      mass N (zRow (Nat.fib (N+2)-1)).val = Nat.fib (N+2)-1 ∧
      (∀ j < N, ¬ ((zRow (Nat.fib (N+2)-1)).val j = false ∧
        (zRow (Nat.fib (N+2)-1)).val (j+1) = false)) ∧
      mass N (next (zRow (Nat.fib (N+2)-1)).val) = 0 := by
    have hp : 0 < Nat.fib (N+2) := Nat.fib_pos.mpr (by omega)
    have hv := small_value N (Nat.fib (N+2)-1) (by omega)
    have hn := max_noearly N _ hv
    exact ⟨hv, hn, noearly_zero N _ hn⟩
  have extra : V (P L (zRow (G (L+1)-1))) = beta L ∧
      V (P L (T (zRow (G (L+1)-1)))) = 0 := by
    have hr := reset (L+1)
    let x := zRow (G (L+1)-1)
    have hn : ∀ j < L+1, ¬ (x.val j = false ∧ x.val (j+1) = false) := hr.2.1
    have hp : 0 < Nat.fib (L+1+2) := Nat.fib_pos.mpr (by omega)
    have hz : x.val (L+1) = false := small_bits (L+1) _ (by dsimp [G]; omega) _ le_rfl
    have hx : x.val L = true := by
      cases hh : x.val L
      · exact False.elim (hn L (by omega) ⟨hh, hz⟩)
      · rfl
    have hshort : ∀ j < L, ¬ (x.val j = false ∧ x.val (j+1) = false) :=
      fun j hj => hn j (by omega)
    have hv := (boundary_value L hL x hshort).2 hx
    constructor
    · rw [value]
      change mass L x.val = beta L
      dsimp [beta]
      omega
    · exact (value L _).trans (noearly_zero L x hshort)
  have edge (s t : ℕ) :
      (∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t) ↔
      ((s < G L - 1 ∧ t = s + 1) ∨ (s = G L - 1 ∧ t = 0) ∨
        (s = beta L ∧ t = 0)) := by
    constructor
    · rintro ⟨x, rfl, rfl⟩
      exact forward x
    · rintro (⟨hs, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨zRow s, ordinary s hs⟩
      · exact ⟨zRow (G L-1), (value L _).trans (reset L).1,
          (value L _).trans (reset L).2.2⟩
      · exact ⟨zRow (G (L+1)-1), extra⟩
  have prefix_control (N : ℕ) (x y : ℕ → Bool)
      (agree : ∀ k < N + 1, x k = y k) :
      ∀ i < N, next x i = next y i := by
    classical
    have pairs (j : ℕ) (hj : j < N) :
        (x j = false ∧ x (j + 1) = false) ↔
        (y j = false ∧ y (j + 1) = false) := by
      rw [agree j (by omega), agree (j + 1) (by omega)]
    by_cases early : ∃ j < N, x j = false ∧ x (j + 1) = false
    · obtain ⟨j, hj, hxj⟩ := early
      have hx : ∃ k, x k = false ∧ x (k + 1) = false := ⟨j, hxj⟩
      have hy : ∃ k, y k = false ∧ y (k + 1) = false :=
        ⟨j, (pairs j hj).mp hxj⟩
      have same : Nat.find hx = Nat.find hy :=
        Nat.find_congr hxj (fun k hk => pairs k (by omega))
      intro i hi
      simp only [next, dif_pos hx, dif_pos hy]
      rw [same, agree i (by omega)]
    · have zero_prefix (z : ℕ → Bool)
          (hz : ∀ j < N, ¬ (z j = false ∧ z (j + 1) = false)) :
          ∀ i < N, next z i = false := by
        intro i hi
        unfold next
        split
        · rename_i h
          have bound : N ≤ Nat.find h := by
            by_contra hn
            exact hz (Nat.find h) (by omega) (Nat.find_spec h)
          simp only [if_pos (show i < Nat.find h by omega)]
        · rfl
      have hx : ∀ j < N, ¬ (x j = false ∧ x (j + 1) = false) := by
        intro j hj hp
        exact early ⟨j, hj, hp⟩
      have hy : ∀ j < N, ¬ (y j = false ∧ y (j + 1) = false) := by
        intro j hj hp
        exact hx j hj ((pairs j hj).mpr hp)
      intro i hi
      exact (zero_prefix x hx i hi).trans (zero_prefix y hy i hi).symm
  have local_step (L : ℕ) (x y : LegalDigits) (h : P (L+1) x = P (L+1) y) :
      P L (T x) = P L (T y) := by
    apply Subtype.ext
    funext i
    apply prefix_control L x.val y.val _ i.val i.isLt
    intro k hk
    exact congrArg (fun p : X (L+1) => p.val ⟨k,hk⟩) h
  have h_step_locality (L h : ℕ) (x y : LegalDigits)
      (hxy : P (L+h) x = P (L+h) y) : P L (T^[h] x) = P L (T^[h] y) := by
    induction h generalizing L x y with
    | zero => simpa using hxy
    | succ h ih =>
      have hs : P (L+h) (T x) = P (L+h) (T y) :=
        local_step (L+h) x y (by rw [← Nat.add_assoc] at hxy; exact hxy)
      simpa only [Function.iterate_succ_apply] using ih L (T x) (T y) hs
  have row_edges (p q : X L) (hpq : R L p q) :
      ∃ n : ℕ, P L (zRow n) = p ∧ P L (T (zRow n)) = q := by
    obtain ⟨x, rfl, rfl⟩ := hpq
    refine ⟨V (P (L+1) x), ?_, ?_⟩
    · apply Subtype.ext
      funext i
      exact congrArg (fun p : X (L+1) => p.val ⟨i, by omega⟩) (row_prefix (L+1) x)
    · exact local_step L _ _ (row_prefix (L+1) x)
  have factor : ∃! g : X (L+1) → X L, ∀ x, P L (T x) = g (P (L+1) x) := by
    refine ⟨fun p => P L (T (pad (L+1) p)), ?_, ?_⟩
    · intro x
      exact local_step L x _ (pad_prefix (L+1) (P (L+1) x)).symm
    · intro g hg
      funext p
      have he := hg (pad (L+1) p)
      rw [pad_prefix] at he
      exact he.symm
  have nofactor : ¬ ∃ f : X L → X L,
      ∀ n : ℕ, P L (T (zRow n)) = f (P L (zRow n)) := by
    rintro ⟨f, hf⟩
    have ho := ordinary (beta L) bounds.2
    have he : P L (zRow (beta L)) = P L (zRow (G (L+1)-1)) :=
      injective L (ho.1.trans extra.1.symm)
    have hout := (hf (beta L)).trans ((congrArg f he).trans (hf (G (L+1)-1)).symm)
    have hv := congrArg V hout
    rw [ho.2, extra.2] at hv
    omega
  have outdegrees (s : ℕ) (hs : s < G L) :
      Set.ncard {t : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
        (if s = beta L then 2 else 1) := by
    by_cases hb : s = beta L
    · have he : {t : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
          ({s+1, 0} : Set ℕ) := by
        ext t
        simp only [Set.mem_ofPred_eq, edge, Set.mem_insert_iff, Set.mem_singleton_iff]
        have := bounds.2
        omega
      rw [he, Set.ncard_pair (by omega : s+1 ≠ 0), if_pos hb]
    · by_cases hm : s = G L-1
      · have he : {t : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
            ({0} : Set ℕ) := by
          ext t
          simp only [Set.mem_ofPred_eq, edge, Set.mem_singleton_iff]
          omega
        rw [he, Set.ncard_singleton, if_neg hb]
      · have he : {t : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
            ({s+1} : Set ℕ) := by
          ext t
          simp only [Set.mem_ofPred_eq, edge, Set.mem_singleton_iff]
          omega
        rw [he, Set.ncard_singleton, if_neg hb]
  have indegrees (t : ℕ) (ht : t < G L) :
      Set.ncard {s : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
        (if t = 0 then 2 else 1) := by
    by_cases hz : t = 0
    · have he : {s : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
          ({G L-1, beta L} : Set ℕ) := by
        ext s
        simp only [Set.mem_ofPred_eq, edge, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      rw [he, Set.ncard_pair (ne_of_gt bounds.2), if_pos hz]
    · have he : {s : ℕ | ∃ x : LegalDigits, V (P L x) = s ∧ V (P L (T x)) = t} =
          ({t-1} : Set ℕ) := by
        ext s
        simp only [Set.mem_ofPred_eq, edge, Set.mem_singleton_iff]
        omega
      rw [he, Set.ncard_singleton, if_neg hz]
  exact ⟨edge, row_edges, factor, nofactor, outdegrees, indegrees, h_step_locality L⟩

#print axioms window_successor_graph

end D5.S1.Digit.Infinite.WindowSuccessorGraph
