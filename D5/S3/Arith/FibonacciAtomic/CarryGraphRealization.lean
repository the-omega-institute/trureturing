/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraphRealization
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraphRealization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed-label carry columns drive a bit-charged prefix-tree execution. -/

import D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
import D5.S0.Tower.DBonacci.TerminalSampling
import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraphRealization

open scoped BigOperators ENNReal
open CarryGraphEmbedding MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape fairBit)

/-- The fixed one-label interval, using zero-based indices for labels. -/
def labelSet (m : ℕ) (γ : Path) (d : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    if (γ.action d).b = 1 then (i.val : ℤ) < (γ.state d).e + (γ.action d).c
    else (γ.state d).e - (γ.action d).h ≤ (i.val : ℤ) ∧
      (i.val : ℤ) < (γ.state d).e + (γ.action d).c

/-- Each column emits its selected labels in increasing order. -/
def labels (m : ℕ) (γ : Path) (d : ℕ) : List (Fin m) :=
  (labelSet m γ d).sort (· ≤ ·)

/-- The zero-or-one digit belonging to a fixed output label. -/
def labelDigit {m : ℕ} (γ : Path) (i : Fin m) (d : ℕ) : Fin 2 :=
  if i ∈ labelSet m γ d then 1 else 0

/-- The output law determined by the complete, possibly noncanonical digits. -/
noncomputable def labelLaw {m : ℕ} (γ : Path) (i : Fin m) : ℝ :=
  Real.ofDigits (labelDigit γ i)

/-- Read the next source bit only while active. A left state records the returned
label and the number of charged reads; a right state is a continuing slot. -/
def scan (m : ℕ) (γ : Path) (tape : Tape) : ℕ → Sum (Fin m × ℕ) ℕ
  | 0 => .inr 0
  | d + 1 => match scan m γ tape d with
    | .inl returned => .inl returned
    | .inr j =>
      let z := 2 * j + (tape d).toNat
      if hz : z < (labels m γ d).length then
        .inl ((labels m γ d)[z], d + 1)
      else .inr (z - (labels m γ d).length)

/-- Children are ordered by their parent slot, then by false before true. -/
def children (words : List (List Bool)) : List (List Bool) :=
  words.flatMap fun w => [w ++ [false], w ++ [true]]

/-- The actual continuing words; selected children become leaves and are removed. -/
def continuing (m : ℕ) (γ : Path) : ℕ → List (List Bool)
  | 0 => [[]]
  | d + 1 => (children (continuing m γ d)).drop (labels m γ d).length

/-- The selected children are paired with the corresponding fixed labels. -/
def stopping (m : ℕ) (γ : Path) (d : ℕ) : List (List Bool × Fin m) :=
  (children (continuing m γ d)).zip (labels m γ d)

/-- The first finite return, or exceptional absence of any finite return. -/
noncomputable def sample (m : ℕ) (γ : Path) (tape : Tape) : Option (Fin m × ℕ) := by
  classical
  exact if h : ∃ d, (scan m γ tape d).isLeft then
    (scan m γ tape (Nat.find h)).getLeft?
  else none

/-- Every active scan step contributes one charged read, including divergent tapes. -/
noncomputable def bill (m : ℕ) (γ : Path) (tape : Tape) : ℝ≥0∞ :=
  ∑' d : ℕ, if (scan m γ tape d).isRight then 1 else 0

private theorem tree_layers (m : ℕ) (γ : Path) (hγ : IsRootPath m γ) :
    (∀ d, ((labels m γ d).length : ℤ) = ones (γ.state d) (γ.action d)) ∧
    (∀ d, ((continuing m γ d).length : ℤ) = (γ.state d).r ∧
      (continuing m γ d).Nodup ∧
      (∀ w ∈ continuing m γ d, w.length = d)) ∧
    (∀ d, (stopping m γ d).map Prod.snd = labels m γ d ∧
      (stopping m γ d).Nodup ∧
      (∀ w ∈ stopping m γ d, w.1.length = d + 1)) := by
  classical
  have column (d : ℕ) : ((labels m γ d).length : ℤ) =
      ones (γ.state d) (γ.action d) := by
    let s := γ.state d
    let a := γ.action d
    let lo : ℤ := if a.b = 1 then 0 else s.e - a.h
    let hi : ℤ := s.e + a.c
    have ha := (hγ.2 d).1
    have range_bounds : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ m := by
      rcases ha with ⟨hs, ha, hs'⟩
      rcases hs with ⟨hr0, hr1, he0, he1⟩
      rcases ha with ha | ha
      · rcases ha with ⟨hb, hh, hc0, hc1⟩
        simp only [lo, hi, s, a, hb, ite_true]
        omega
      · rcases ha with ⟨hb, hh0, hh1, hc0, hc1⟩
        simp only [lo, hi, s, a, hb, Int.zero_ne_one, ite_false]
        omega
    have membership (i : Fin m) : i ∈ labelSet m γ d ↔
        (i.val : ℤ) ∈ Finset.Ico lo hi := by
      simp only [labelSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Ico, lo, hi, s, a]
      split_ifs <;> omega
    have card : (labelSet m γ d).card = (Finset.Ico lo hi).card := by
      refine Finset.card_bij (fun i _ => (i.val : ℤ))
        (fun i hi => (membership i).mp hi) ?_ ?_
      · intro i hi j hj he
        exact Fin.ext (by exact_mod_cast he)
      · intro z hz
        have hz0 : 0 ≤ z := le_trans range_bounds.1 (Finset.mem_Ico.mp hz).1
        have hzm : z < m := lt_of_lt_of_le (Finset.mem_Ico.mp hz).2
          range_bounds.2.2
        let i : Fin m := ⟨z.toNat, by omega⟩
        have hi : (i.val : ℤ) = z := Int.toNat_of_nonneg hz0
        refine ⟨i, (membership i).mpr (hi ▸ hz), hi⟩
    rw [labels, Finset.length_sort, card, Int.card_Ico, Int.toNat_of_nonneg
      (sub_nonneg.mpr range_bounds.2.1)]
    dsimp only [hi, lo, ones, s, a]
    split_ifs <;> ring
  have child_length (ws : List (List Bool)) : (children ws).length = 2 * ws.length := by
    simp [children, List.length_flatMap, Nat.mul_comm]
  have child_nodup (ws : List (List Bool)) (hn : ws.Nodup) : (children ws).Nodup := by
    rw [children, List.nodup_flatMap]
    constructor
    · intro w hw
      simp
    · apply hn.imp
      intro u v huv
      simp only [Function.onFun, List.disjoint_left, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false]
      intro w hw hv
      rcases hw with hw | hw <;> rcases hv with hv | hv
      · exact huv (List.append_cancel_right (hw.symm.trans hv))
      · have H := congrArg (fun xs : List Bool => xs.getLast?) (hw.symm.trans hv)
        simp at H
      · have H := congrArg (fun xs : List Bool => xs.getLast?) (hw.symm.trans hv)
        simp at H
      · exact huv (List.append_cancel_right (hw.symm.trans hv))
  have layer : ∀ d, ((continuing m γ d).length : ℤ) = (γ.state d).r ∧
      (continuing m γ d).Nodup ∧ (∀ w ∈ continuing m γ d, w.length = d) := by
    intro d
    induction d with
    | zero => simp [continuing, hγ.1, root]
    | succ d ih =>
      have hr : 0 ≤ (γ.state (d + 1)).r := (hγ.2 (d + 1)).1.1.1
      have hc := column d
      have hnext : (γ.state (d + 1)).r =
          2 * (γ.state d).r - ones (γ.state d) (γ.action d) := by
        rw [(hγ.2 d).2]
        rfl
      have fits : (labels m γ d).length ≤ (children (continuing m γ d)).length := by
        rw [child_length]
        omega
      refine ⟨?_, ?_, ?_⟩
      · rw [continuing, List.length_drop, Nat.cast_sub fits, child_length,
          Nat.cast_mul, Nat.cast_ofNat, ih.1, hc, hnext]
      · exact (child_nodup _ ih.2.1).drop
      · intro w hw
        have hw' := List.mem_of_mem_drop hw
        rcases List.mem_flatMap.mp hw' with ⟨v, hv, hwv⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwv
        rcases hwv with rfl | rfl <;> simp [ih.2.2 v hv]
  refine ⟨column, layer, ?_⟩
  intro d
  have hc := column d
  have hr := (hγ.2 (d + 1)).1.1.1
  have hnext : (γ.state (d + 1)).r =
      2 * (γ.state d).r - ones (γ.state d) (γ.action d) := by
    rw [(hγ.2 d).2]
    rfl
  have fits : (labels m γ d).length ≤ (children (continuing m γ d)).length := by
    rw [child_length]
    have hl := (layer d).1
    omega
  refine ⟨List.map_snd_zip fits, ?_, ?_⟩
  · apply List.Nodup.of_map (f := Prod.snd)
    rw [stopping, List.map_snd_zip fits]
    exact Finset.sort_nodup _ _
  · intro w hw
    have hw' := List.of_mem_zip hw
    rcases List.mem_flatMap.mp hw'.1 with ⟨v, hv, hwv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwv
    rcases hwv with he | he <;> rw [he] <;> simp [(layer d).2.2 v hv]

private theorem scan_tree (m : ℕ) (γ : Path) (hγ : IsRootPath m γ) :
    ∀ d (tape : Tape) j, scan m γ tape d = Sum.inr j ↔
      ∃ hj : j < (continuing m γ d).length,
        List.ofFn (fun i : Fin d => tape i.val) = (continuing m γ d)[j] := by
  classical
  have layers := (tree_layers m γ hγ).2.1
  have child_length (ws : List (List Bool)) : (children ws).length = 2 * ws.length := by
    simp [children, List.length_flatMap, Nat.mul_comm]
  have child_at (ws : List (List Bool)) (j : ℕ) (hj : j < ws.length) (b : Bool) :
      (children ws)[2 * j + b.toNat]'(by rw [child_length]; cases b <;> simp <;> omega) =
        ws[j] ++ [b] := by
    induction ws generalizing j with
    | nil => simp at hj
    | cons w ws ih =>
      cases j with
      | zero => cases b <;> simp [children]
      | succ j =>
        have hj' : j < ws.length := by simpa using hj
        have H := ih j hj'
        cases b <;> simpa [children, List.flatMap_cons, Nat.mul_add, Nat.add_assoc] using H
  intro d
  induction d with
  | zero => intro tape j; simp [scan, continuing, eq_comm]
  | succ d ih =>
    intro tape j
    let ws := continuing m γ d
    let q := (labels m γ d).length
    have next_words : continuing m γ (d + 1) = (children ws).drop q := rfl
    have drop_at (j : ℕ) (hj : j < (continuing m γ (d + 1)).length) :
        (continuing m γ (d + 1))[j] = (children ws)[q + j]'(by rw [next_words, List.length_drop] at hj; omega) := List.getElem_drop
    have word_step : List.ofFn (fun i : Fin (d + 1) => tape i.val) =
        List.ofFn (fun i : Fin d => tape i.val) ++ [tape d] := by
      simpa using List.ofFn_succ_last (f := fun i : Fin (d + 1) => tape i.val)
    constructor
    · intro hs
      cases hp : scan m γ tape d with
      | inl returned => simp [scan, hp] at hs
      | inr a =>
        obtain ⟨ha, hword⟩ := (ih tape a).mp hp
        have hb : (tape d).toNat ≤ 1 := by cases tape d <;> simp
        have hz : 2 * a + (tape d).toNat < (children ws).length := by
          rw [child_length]
          dsimp only [ws]
          omega
        have hq : q ≤ 2 * a + (tape d).toNat := by
          by_contra H
          have H' : 2 * a + (tape d).toNat < (labels m γ d).length := by
            dsimp only [q] at H
            omega
          simp [scan, hp, H'] at hs
        have he : 2 * a + (tape d).toNat - q = j := by
          simpa only [scan, hp, show ¬ 2 * a + (tape d).toNat <
            (labels m γ d).length by change ¬ _ < q; omega,
            dite_false, Sum.inr.injEq] using hs
        have hj : j < (continuing m γ (d + 1)).length := by
          rw [next_words, List.length_drop]
          omega
        refine ⟨hj, ?_⟩
        rw [word_step, hword, drop_at j hj]
        have idx : q + j = 2 * a + (tape d).toNat := by omega
        simpa only [idx] using (child_at ws a ha (tape d)).symm
    · rintro ⟨hj, hword⟩
      let z := q + j
      have hz : z < (children ws).length := by
        rw [next_words, List.length_drop] at hj
        dsimp only [z]
        omega
      let a := z / 2
      let b : Bool := decide (z % 2 = 1)
      have hb : 2 * a + b.toNat = z := by
        dsimp only [a, b]
        by_cases H : z % 2 = 1 <;> simp only [H, decide_true, decide_false,
          Bool.toNat_true, Bool.toNat_false] <;> omega
      have ha : a < ws.length := by
        rw [child_length] at hz
        dsimp only [a]
        omega
      have child_eq : (children ws)[z] = ws[a] ++ [b] := by
        simpa only [hb] using child_at ws a ha b
      rw [word_step, drop_at j hj] at hword
      change List.ofFn (fun i : Fin d => tape i.val) ++ [tape d] =
        (children ws)[z] at hword
      rw [child_eq] at hword
      have split_word := List.append_inj' hword (by simp)
      have ht : tape d = b := by simpa using split_word.2
      have hp : scan m γ tape d = Sum.inr a := (ih tape a).mpr ⟨ha, split_word.1⟩
      have hnot : ¬ 2 * a + (tape d).toNat < (labels m γ d).length := by
        rw [ht, hb]
        change ¬ z < q
        dsimp only [z]
        omega
      simp only [scan, hp]
      rw [dif_neg hnot, ht, hb]
      congr 1
      exact Nat.add_sub_cancel_left q j

private theorem law_bounds (m : ℕ) (hm : 2 ≤ m) (γ : Path) (hγ : IsRootPath m γ) :
    (∀ i : Fin m, 0 ≤ labelLaw γ i) ∧
    (∑ i : Fin m, labelLaw γ i) = 1 ∧
    labelLaw (m := m) γ ⟨0, by omega⟩ = anchorValue γ ∧
    (∀ i : Fin m, anchorValue γ ≤ labelLaw γ i) ∧
    (0 < anchorValue γ → ∀ i : Fin m, 0 < labelLaw γ i) ∧
    Summable (fun d : ℕ => (γ.state d).r / (2 : ℝ) ^ d) ∧
    pathCost γ ≤ m ∧ DyadicSupportLines.cost (labelLaw γ) ≤ pathCost γ := by
  classical
  let k : Fin m := ⟨0, by omega⟩
  let N : ℕ → Fin m → ℤ := Nat.rec (fun _ => 0)
    (fun d prev i => 2 * prev i + (labelDigit γ i d).val)
  have Nzero (i : Fin m) : N 0 i = 0 := rfl
  have Nstep (d : ℕ) (i : Fin m) : N (d + 1) i =
      2 * N d i + (labelDigit γ i d).val := rfl
  have state_bounds (d : ℕ) : IsState m (γ.state d) := (hγ.2 d).1.1
  have digit_bounds (d : ℕ) (i : Fin m) :
      0 ≤ ((labelDigit γ i d).val : ℤ) ∧ ((labelDigit γ i d).val : ℤ) ≤ 1 := by
    have H := (labelDigit γ i d).isLt
    omega
  have column_sum (d : ℕ) : (∑ i : Fin m, ((labelDigit γ i d).val : ℤ)) =
      ones (γ.state d) (γ.action d) := by
    rw [← (tree_layers m γ hγ).1 d]
    have digit_indicator (i : Fin m) : ((labelDigit γ i d).val : ℤ) =
        if i ∈ labelSet m γ d then 1 else 0 := by
      by_cases H : i ∈ labelSet m γ d <;> simp [labelDigit, H]
    simp_rw [digit_indicator]
    simp [labels, Finset.sum_boole]
  have Nsum : ∀ d, (∑ i : Fin m, N d i) = (2 : ℤ) ^ d - (γ.state d).r := by
    intro d
    induction d with
    | zero => simp [Nzero, hγ.1, root]
    | succ d ih =>
      simp_rw [Nstep]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, column_sum, ih, (hγ.2 d).2]
      simp only [successor, pow_succ]
      ring
  have truncation_identity (d : ℕ) (i : Fin m) :
      (N d i : ℝ) / (2 : ℝ) ^ d =
        ∑ j ∈ Finset.range d, Real.ofDigitsTerm (labelDigit γ i) j := by
    induction d with
    | zero => simp [Nzero]
    | succ d ih =>
      rw [Nstep, Finset.sum_range_succ, ← ih]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Real.ofDigitsTerm, pow_succ]
      field_simp
      ring
  have anchor_digit (d : ℕ) : ((labelDigit γ k d).val : ℤ) = (γ.action d).b := by
    have ha := (hγ.2 d).1
    rcases ha with ⟨hs, ha, hs'⟩
    rcases hs with ⟨hr0, hr1, he0, he1⟩
    rcases ha with ha | ha
    · rcases ha with ⟨hb, hh, hc0, hc1⟩
      have H : k ∈ labelSet m γ d := by simp [labelSet, hb, k]; omega
      simp [labelDigit, H, hb]
    · rcases ha with ⟨hb, hh0, hh1, hc0, hc1⟩
      have H : k ∉ labelSet m γ d := by simp [labelSet, hb, k]; omega
      simp [labelDigit, H, hb]
  have group : ∀ d (i : Fin m),
      ((i.val : ℤ) < (γ.state d).e → N d i = N d k) ∧
      ((γ.state d).e ≤ (i.val : ℤ) → N d k + 1 ≤ N d i) := by
    intro d
    induction d with
    | zero => intro i; simp [Nzero, hγ.1, root]; omega
    | succ d ih =>
      intro i
      have ha := (hγ.2 d).1
      have hi0 : (0 : ℤ) ≤ i.val := by positivity
      have he : (γ.state (d + 1)).e = (γ.state d).e - (γ.action d).h := by
        rw [(hγ.2 d).2]; rfl
      have hb := digit_bounds d i
      have hk := anchor_digit d
      rcases ha with ⟨hs, ha, hs'⟩
      rcases hs with ⟨hr0, hr1, he0, he1⟩
      rcases ha with ha | ha
      · rcases ha with ⟨ha, hh, hc0, hc1⟩
        rw [hh, sub_zero] at he
        constructor
        · intro hi
          have old : (i.val : ℤ) < (γ.state d).e := by omega
          have mem : i ∈ labelSet m γ d := by simp [labelSet, ha]; omega
          have bit : ((labelDigit γ i d).val : ℤ) = 1 := by simp [labelDigit, mem]
          rw [Nstep, Nstep, bit, hk, ha, (ih i).1 old]
        · intro hi
          have old : (γ.state d).e ≤ (i.val : ℤ) := by omega
          have gap := (ih i).2 old
          rw [Nstep, Nstep, hk, ha]
          omega
      · rcases ha with ⟨ha, hh0, hh1, hc0, hc1⟩
        constructor
        · intro hi
          have old : (i.val : ℤ) < (γ.state d).e := by omega
          have mem : i ∉ labelSet m γ d := by simp [labelSet, ha]; omega
          have bit : ((labelDigit γ i d).val : ℤ) = 0 := by simp [labelDigit, mem]
          rw [Nstep, Nstep, bit, hk, ha, (ih i).1 old]
        · intro hi
          by_cases old : (i.val : ℤ) < (γ.state d).e
          · have mem : i ∈ labelSet m γ d := by simp [labelSet, ha]; omega
            have bit : ((labelDigit γ i d).val : ℤ) = 1 := by simp [labelDigit, mem]
            rw [Nstep, Nstep, bit, hk, ha, (ih i).1 old]
            omega
          · have gap := (ih i).2 (by omega)
            rw [Nstep, Nstep, hk, ha]
            omega
  have nonneg (i : Fin m) : 0 ≤ labelLaw γ i := Real.ofDigits_nonneg _
  have limit (i : Fin m) : Filter.Tendsto
      (fun d => ∑ j ∈ Finset.range d, Real.ofDigitsTerm (labelDigit γ i) j)
      Filter.atTop (nhds (labelLaw γ i)) := Real.summable_ofDigitsTerm.hasSum.tendsto_sum_nat
  have minimum (i : Fin m) : labelLaw γ k ≤ labelLaw γ i := by
    apply le_of_tendsto_of_tendsto (limit k) (limit i)
    apply Filter.Eventually.of_forall
    intro d
    rw [← truncation_identity d k, ← truncation_identity d i]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have H := group d i
    have H' : N d k ≤ N d i := by
      by_cases hi : (i.val : ℤ) < (γ.state d).e
      · exact le_of_eq ((H.1 hi).symm)
      · have := H.2 (by omega); omega
    exact_mod_cast H'
  have anchor : labelLaw γ k = anchorValue γ := by
    unfold labelLaw Real.ofDigits anchorValue
    apply tsum_congr
    intro d
    have H := anchor_digit d
    have H' : ((labelDigit γ k d).val : ℝ) = (γ.action d).b := by exact_mod_cast H
    simpa only [Real.ofDigitsTerm, div_eq_mul_inv] using
      congrArg (fun x : ℝ => x * ((2 : ℝ) ^ (d + 1))⁻¹) H'
  have residual_nonneg (d : ℕ) : 0 ≤ ((γ.state d).r : ℝ) / (2 : ℝ) ^ d := by
    exact div_nonneg (by exact_mod_cast (state_bounds d).1) (by positivity)
  have residual_upper (d : ℕ) : ((γ.state d).r : ℝ) / (2 : ℝ) ^ d ≤
      (m - 1 : ℝ) * (1 / 2 : ℝ) ^ d := by
    have H : ((γ.state d).r : ℝ) ≤ (m : ℝ) - 1 := by
      exact_mod_cast (state_bounds d).2.1
    simpa only [div_pow, one_div, div_eq_mul_inv, inv_pow] using
      div_le_div_of_nonneg_right H (by positivity : 0 ≤ (2 : ℝ) ^ d)
  have residual_limit : Filter.Tendsto (fun d => ((γ.state d).r : ℝ) / (2 : ℝ) ^ d)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero residual_nonneg residual_upper
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (m - 1 : ℝ)
  have partial_sum (d : ℕ) :
      (∑ i : Fin m, ∑ j ∈ Finset.range d, Real.ofDigitsTerm (labelDigit γ i) j) =
        1 - ((γ.state d).r : ℝ) / (2 : ℝ) ^ d := by
    simp_rw [← truncation_identity d]
    rw [← Finset.sum_div, ← Int.cast_sum, Nsum]
    push_cast
    field_simp
  have normalized : (∑ i : Fin m, labelLaw γ i) = 1 := by
    have H := tendsto_finsetSum (Finset.univ : Finset (Fin m)) (fun i _ => limit i)
    have H' : Filter.Tendsto
        (fun d => ∑ i : Fin m, ∑ j ∈ Finset.range d,
          Real.ofDigitsTerm (labelDigit γ i) j) Filter.atTop (nhds 1) := by
      simp_rw [partial_sum]
      simpa using tendsto_const_nhds.sub residual_limit
    exact tendsto_nhds_unique H H'
  have summable : Summable (fun d : ℕ => ((γ.state d).r : ℝ) / (2 : ℝ) ^ d) :=
    Summable.of_nonneg_of_le residual_nonneg residual_upper
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (m - 1 : ℝ))
  have cost_upper : pathCost γ ≤ m := by
    have head : ((γ.state 0).r : ℝ) / (2 : ℝ) ^ 0 = 1 := by simp [hγ.1, root]
    have split := summable.sum_add_tsum_nat_add 1
    have tail : (∑' d : ℕ, ((γ.state (d + 1)).r : ℝ) / (2 : ℝ) ^ (d + 1)) ≤ m - 1 := by
      calc
        _ ≤ ∑' d : ℕ, (m - 1 : ℝ) * (1 / 2 : ℝ) ^ (d + 1) :=
          Summable.tsum_mono (summable.comp_injective (by intro a b h; omega))
            (((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 / 2 : ℝ) < 1)).comp_injective (by intro a b h; omega)).mul_left _)
            (fun d => residual_upper (d + 1))
        _ = m - 1 := by simp [pow_succ, tsum_mul_left, tsum_mul_right, tsum_geometric_two]
    simp only [Finset.sum_range_one, head] at split
    change _ = pathCost γ at split
    linarith
  have floor_compare (d : ℕ) (i : Fin m) : N d i ≤ ⌊(2 : ℝ) ^ d * labelLaw γ i⌋ := by
    apply Int.le_floor.mpr
    have H := Real.summable_ofDigitsTerm.sum_le_tsum (Finset.range d)
      (fun j _ => Real.ofDigitsTerm_nonneg (digits := labelDigit γ i) (n := j))
    change (∑ j ∈ Finset.range d, Real.ofDigitsTerm (labelDigit γ i) j) ≤ labelLaw γ i at H
    rw [← truncation_identity d i] at H
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ d)).mp H
  have dyadic_nonneg (d : ℕ) : 0 ≤ DyadicSupportLines.residual (labelLaw γ) d := by
    have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => Int.floor_le ((2 : ℝ) ^ d * labelLaw γ i))
    simp only [← Finset.mul_sum, normalized, mul_one] at H
    exact sub_nonneg.mpr H
  have residual_compare (d : ℕ) : DyadicSupportLines.residual (labelLaw γ) d ≤ (γ.state d).r := by
    have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => floor_compare d i)
    rw [Nsum] at H
    have H' : ((2 : ℤ) ^ d - (γ.state d).r : ℝ) ≤
        (∑ i : Fin m, ⌊(2 : ℝ) ^ d * labelLaw γ i⌋ : ℤ) := by exact_mod_cast H
    simpa only [DyadicSupportLines.residual, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] using
      (by linarith only [H'] : (2 : ℝ) ^ d -
        (∑ i : Fin m, ⌊(2 : ℝ) ^ d * labelLaw γ i⌋ : ℤ) ≤ (γ.state d).r)
  have dyadic_summable : Summable (fun d : ℕ =>
      DyadicSupportLines.residual (labelLaw γ) d / (2 : ℝ) ^ d) :=
    Summable.of_nonneg_of_le (fun d => div_nonneg (dyadic_nonneg d) (by positivity))
      (fun d => div_le_div_of_nonneg_right (residual_compare d) (by positivity)) summable
  refine ⟨nonneg, normalized, anchor, ?_, ?_, summable, cost_upper, ?_⟩
  · intro i; rw [← anchor]; exact minimum i
  · intro ht i; rw [← anchor] at ht; exact lt_of_lt_of_le ht (minimum i)
  · exact Summable.tsum_mono dyadic_summable summable
      (fun d => div_le_div_of_nonneg_right (residual_compare d) (by positivity))

end D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
