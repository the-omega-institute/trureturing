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
    (∀ d (tape : Tape) j, scan m γ tape d = Sum.inr j ↔
      ∃ hj : j < (continuing m γ d).length,
        List.ofFn (fun i : Fin d => tape i.val) = (continuing m γ d)[j]) ∧
    (∀ d (tape : Tape) (i : Fin m), scan m γ tape (d + 1) = Sum.inl (i, d + 1) ↔
      (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈ stopping m γ d) ∧
    (∀ d (tape : Tape) (i : Fin m) n, scan m γ tape d = Sum.inl (i, n) →
      1 ≤ n ∧ n ≤ d ∧ scan m γ tape n = Sum.inl (i, n) ∧
        ∀ j < n, (scan m γ tape j).isRight) := by
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
  have active_words : ∀ d (tape : Tape) j, scan m γ tape d = Sum.inr j ↔
      ∃ hj : j < (continuing m γ d).length,
        List.ofFn (fun i : Fin d => tape i.val) = (continuing m γ d)[j] := by
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
  have persistent (d e : ℕ) (hde : d ≤ e) (tape : Tape) (returned : Fin m × ℕ)
      (hs : scan m γ tape d = Sum.inl returned) : scan m γ tape e = Sum.inl returned := by
    induction e, hde using Nat.le_induction with
    | base => exact hs
    | succ e he ih => simp only [scan, ih]
  have active_before (d : ℕ) (tape : Tape) (hd : (scan m γ tape d).isRight)
      (j : ℕ) (hjd : j ≤ d) : (scan m γ tape j).isRight := by
    cases hs : scan m γ tape j with
    | inr a => simp [hs]
    | inl returned =>
      have H := persistent j d hjd tape returned hs
      simp [H] at hd
  have origin : ∀ d (tape : Tape) (i : Fin m) n,
      scan m γ tape d = Sum.inl (i, n) →
        1 ≤ n ∧ n ≤ d ∧ scan m γ tape n = Sum.inl (i, n) ∧
          ∀ j < n, (scan m γ tape j).isRight := by
    intro d
    induction d with
    | zero => intro tape i n H; simp [scan] at H
    | succ d ih =>
      intro tape i n H
      cases hs : scan m γ tape d with
      | inl returned =>
        have Hprev : scan m γ tape d = Sum.inl (i, n) := by
          rw [hs]
          simpa only [scan, hs] using H
        obtain ⟨h1, h2, h3, h4⟩ := ih tape i n Hprev
        exact ⟨h1, by omega, h3, h4⟩
      | inr a =>
        have Hfull := H
        simp only [scan, hs] at H
        split at H
        next hbit =>
          have hn : d + 1 = n := congrArg Prod.snd (Sum.inl.inj H)
          subst n
          refine ⟨by omega, le_rfl, Hfull, ?_⟩
          intro j hj
          exact active_before d tape (by simp [hs]) j (by omega)
        next hbit => simp at H
  have fits (d : ℕ) : (labels m γ d).length ≤ (children (continuing m γ d)).length := by
    rw [child_length]
    have HC := (tree_layers m γ hγ).1 d
    have HL := (layers d).1
    have HR := (hγ.2 (d + 1)).1.1.1
    have Hnext : (γ.state (d + 1)).r =
        2 * (γ.state d).r - ones (γ.state d) (γ.action d) := by
      rw [(hγ.2 d).2]; rfl
    omega
  have stop_index (d : ℕ) (w : List Bool) (i : Fin m) :
      (w, i) ∈ stopping m γ d ↔
        ∃ z : ℕ, ∃ hz : z < (labels m γ d).length,
          (children (continuing m γ d))[z]'(lt_of_lt_of_le hz (fits d)) = w ∧
            (labels m γ d)[z] = i := by
    constructor
    · intro H
      obtain ⟨z, hz, he⟩ := List.mem_iff_getElem.mp H
      have hz' : z < (labels m γ d).length := by
        simp only [stopping, List.length_zip, lt_min_iff] at hz
        exact hz.2
      simp only [stopping, List.getElem_zip] at he
      exact ⟨z, hz', congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rintro ⟨z, hz, hw, hi⟩
      apply List.mem_iff_getElem.mpr
      refine ⟨z, ?_, ?_⟩
      · simpa only [stopping, List.length_zip, lt_min_iff] using
          And.intro (lt_of_lt_of_le hz (fits d)) hz
      · simp only [stopping, List.getElem_zip, hw, hi]
  have leaf_words : ∀ d (tape : Tape) (i : Fin m),
      scan m γ tape (d + 1) = Sum.inl (i, d + 1) ↔
        (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈ stopping m γ d := by
    intro d tape i
    rw [stop_index]
    have word_step : List.ofFn (fun j : Fin (d + 1) => tape j.val) =
        List.ofFn (fun j : Fin d => tape j.val) ++ [tape d] := by
      simpa using List.ofFn_succ_last (f := fun j : Fin (d + 1) => tape j.val)
    constructor
    · intro H
      cases hs : scan m γ tape d with
      | inl returned =>
        have he : returned = (i, d + 1) := Sum.inl.inj (by simpa only [scan, hs] using H)
        have hb := (origin d tape returned.1 returned.2 hs).2.1
        rw [he] at hb
        omega
      | inr a =>
        obtain ⟨ha, hword⟩ := (active_words d tape a).mp hs
        simp only [scan, hs] at H
        split at H
        next hz =>
          have hi := congrArg Prod.fst (Sum.inl.inj H)
          refine ⟨2 * a + (tape d).toNat, hz, ?_, hi⟩
          rw [word_step, hword]
          exact child_at _ a ha (tape d)
        next hz => simp at H
    · rintro ⟨z, hz, hword, hi⟩
      let a := z / 2
      let b : Bool := decide (z % 2 = 1)
      have hb : 2 * a + b.toNat = z := by
        dsimp only [a, b]
        by_cases H : z % 2 = 1 <;> simp only [H, decide_true, decide_false,
          Bool.toNat_true, Bool.toNat_false] <;> omega
      have ha : a < (continuing m γ d).length := by
        have HC := lt_of_lt_of_le hz (fits d)
        rw [child_length] at HC
        dsimp only [a]
        omega
      have child_eq : (children (continuing m γ d))[z]'(lt_of_lt_of_le hz (fits d)) =
          (continuing m γ d)[a] ++ [b] := by simpa only [hb] using child_at _ a ha b
      rw [child_eq, word_step] at hword
      have split_word := List.append_inj' hword.symm (by simp)
      have ht : tape d = b := by simpa using split_word.2
      have hs : scan m γ tape d = Sum.inr a :=
        (active_words d tape a).mpr ⟨ha, split_word.1⟩
      have hz' : 2 * a + (tape d).toNat = z := by rw [ht, hb]
      simpa only [scan, hs, hz', dif_pos hz, hi]
  exact ⟨active_words, leaf_words, origin⟩

private theorem law_bounds (m : ℕ) (hm : 2 ≤ m) (γ : Path) (hγ : IsRootPath m γ) :
    (∀ i : Fin m, 0 ≤ labelLaw γ i) ∧
    (∑ i : Fin m, labelLaw γ i) = 1 ∧
    labelLaw (m := m) γ ⟨0, by omega⟩ = anchorValue γ ∧
    (∀ i : Fin m, anchorValue γ ≤ labelLaw γ i) ∧
    (0 < anchorValue γ → ∀ i : Fin m, 0 < labelLaw γ i) ∧
    Summable (fun d : ℕ => (γ.state d).r / (2 : ℝ) ^ d) ∧
    pathCost γ ≤ m ∧ DyadicSupportLines.cost (labelLaw (m := m) γ) ≤ pathCost γ := by
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
      (Int.cast (R := ℝ) (N d i)) / (2 : ℝ) ^ d =
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
      have H : k ∈ labelSet m γ d := by simp [labelSet, hb, k] <;> omega
      simp [labelDigit, H, hb]
    · rcases ha with ⟨hb, hh0, hh1, hc0, hc1⟩
      have H : k ∉ labelSet m γ d := by simp [labelSet, hb, k] <;> omega
      simp [labelDigit, H, hb]
  have group : ∀ d (i : Fin m),
      ((i.val : ℤ) < (γ.state d).e → N d i = N d k) ∧
      ((γ.state d).e ≤ (i.val : ℤ) → N d k + 1 ≤ N d i) := by
    intro d
    induction d with
    | zero => intro i; simp [Nzero, hγ.1, root] <;> omega
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
          have mem : i ∈ labelSet m γ d := by simp [labelSet, ha] <;> omega
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
          have mem : i ∉ labelSet m γ d := by simp [labelSet, ha] <;> omega
          have bit : ((labelDigit γ i d).val : ℤ) = 0 := by simp [labelDigit, mem]
          rw [Nstep, Nstep, bit, hk, ha, (ih i).1 old]
        · intro hi
          by_cases old : (i.val : ℤ) < (γ.state d).e
          · have mem : i ∈ labelSet m γ d := by simp [labelSet, ha] <;> omega
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
    dsimp only
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
    simpa only [Real.ofDigitsTerm, div_eq_mul_inv, Nat.cast_ofNat] using
      congrArg (fun x : ℝ => x * ((2 : ℝ) ^ (d + 1))⁻¹) H'
  have residual_nonneg (d : ℕ) : 0 ≤ ((γ.state d).r : ℝ) / (2 : ℝ) ^ d := by
    exact div_nonneg (by exact_mod_cast (state_bounds d).1) (by positivity)
  have residual_upper (d : ℕ) : ((γ.state d).r : ℝ) / (2 : ℝ) ^ d ≤
      (m - 1 : ℝ) * (1 / 2 : ℝ) ^ d := by
    have H : ((γ.state d).r : ℝ) ≤ (m : ℝ) - 1 := by
      exact_mod_cast (state_bounds d).2.1
    simpa only [div_pow, one_div, div_eq_mul_inv, inv_pow, one_mul] using
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
          Summable.tsum_mono (summable.comp_injective (fun a b h => Nat.add_right_cancel h))
            (((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 / 2 : ℝ) < 1)).comp_injective (fun a b h => Nat.add_right_cancel h)).mul_left _)
            (fun d => residual_upper (d + 1))
        _ = m - 1 := by
          have geo : (∑' x : ℕ, ((2 : ℝ) ^ x)⁻¹) = 2 := by
            simpa only [inv_pow] using tsum_geometric_inv_two
          simp only [pow_succ, one_div, inv_pow, tsum_mul_left, tsum_mul_right]
          rw [geo]
          ring
    simp only [Finset.sum_range_one, head] at split
    change _ = pathCost γ at split
    linarith
  have floor_compare (d : ℕ) (i : Fin m) : N d i ≤ ⌊(2 : ℝ) ^ d * labelLaw γ i⌋ := by
    apply Int.le_floor.mpr
    have H := Real.summable_ofDigitsTerm.sum_le_tsum (Finset.range d)
      (fun j _ => Real.ofDigitsTerm_nonneg (digits := labelDigit γ i) (n := j))
    change (∑ j ∈ Finset.range d, Real.ofDigitsTerm (labelDigit γ i) j) ≤ labelLaw γ i at H
    rw [← truncation_identity d i] at H
    simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ d)).mp H
  have dyadic_nonneg (d : ℕ) : 0 ≤ DyadicSupportLines.residual (labelLaw (m := m) γ) d := by
    have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => Int.floor_le ((2 : ℝ) ^ d * labelLaw γ i))
    simp only [← Finset.mul_sum, normalized, mul_one] at H
    simpa only [DyadicSupportLines.residual, Int.cast_sum] using sub_nonneg.mpr H
  have residual_compare (d : ℕ) : DyadicSupportLines.residual (labelLaw (m := m) γ) d ≤ (γ.state d).r := by
    have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => floor_compare d i)
    rw [Nsum] at H
    have H' : (↑((2 : ℤ) ^ d - (γ.state d).r) : ℝ) ≤
        (∑ i : Fin m, ⌊(2 : ℝ) ^ d * labelLaw γ i⌋ : ℤ) := by exact_mod_cast H
    dsimp only [DyadicSupportLines.residual]
    push_cast at H' ⊢
    linarith only [H']
  have dyadic_summable : Summable (fun d : ℕ =>
      DyadicSupportLines.residual (labelLaw (m := m) γ) d / (2 : ℝ) ^ d) :=
    Summable.of_nonneg_of_le (fun d => div_nonneg (dyadic_nonneg d) (by positivity))
      (fun d => div_le_div_of_nonneg_right (residual_compare d) (by positivity)) summable
  refine ⟨nonneg, normalized, anchor, ?_, ?_, summable, cost_upper, ?_⟩
  · intro i; rw [← anchor]; exact minimum i
  · intro ht i; rw [← anchor] at ht; exact lt_of_lt_of_le ht (minimum i)
  · exact Summable.tsum_mono dyadic_summable summable
      (fun d => div_le_div_of_nonneg_right (residual_compare d) (by positivity))

private theorem fair_tail (m : ℕ) (hm : 2 ≤ m) (γ : Path) (hγ : IsRootPath m γ) :
    (∀ d, MeasurableSet {tape : Tape | (scan m γ tape d).isRight} ∧
      fairTape {tape : Tape | (scan m γ tape d).isRight} =
        ENNReal.ofReal (((γ.state d).r : ℝ) / (2 : ℝ) ^ d)) ∧
    (∀ᵐ tape ∂fairTape, ∃ d, (scan m γ tape d).isLeft) ∧
    (∫⁻ tape, bill m γ tape ∂fairTape) = ENNReal.ofReal (pathCost γ) ∧
    (∀ d (w : List Bool), w.length = d →
      MeasurableSet {tape : Tape | List.ofFn (fun i : Fin d => tape i.val) = w} ∧
      fairTape {tape : Tape | List.ofFn (fun i : Fin d => tape i.val) = w} =
        (2 : ℝ≥0∞)⁻¹ ^ d) := by
  classical
  have layers := (tree_layers m γ hγ).2.1
  have prefix_event (d : ℕ) (w : List Bool) (hw : w.length = d) :
      {tape : Tape | List.ofFn (fun i : Fin d => tape i.val) = w} =
        D5.S0.Tower.DBonacci.TerminalSampling.traceCylinder 0 d
          (fun n => w.getD n false) := by
    ext tape
    simp only [D5.S0.Tower.DBonacci.TerminalSampling.traceCylinder,
      Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_Ico,
      Set.mem_singleton_iff]
    constructor
    · intro he n hn
      have H := congrArg (fun xs : List Bool => xs.getD n false) he
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hn.2] using H
    · intro he
      apply List.ext_getElem (by simp [hw])
      intro n hn hn'
      rw [List.getElem_ofFn, List.getElem_eq_getD false]
      exact he n ⟨Nat.zero_le _, by simpa using hn⟩
  have prefix_measure (d : ℕ) (w : List Bool) (hw : w.length = d) :
      MeasurableSet {tape : Tape | List.ofFn (fun i : Fin d => tape i.val) = w} ∧
      fairTape {tape : Tape | List.ofFn (fun i : Fin d => tape i.val) = w} =
        (2 : ℝ≥0∞)⁻¹ ^ d := by
    rw [prefix_event d w hw]
    constructor
    · exact MeasurableSet.pi (Finset.countable_toSet _)
        (fun _ _ => measurableSet_singleton _)
    · rw [D5.S0.Tower.DBonacci.TerminalSampling.traceCylinder, fairTape,
        Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
      simp [fairBit]
  have slot_measure (d j : ℕ) (hj : j < (continuing m γ d).length) :
      MeasurableSet {tape : Tape | scan m γ tape d = Sum.inr j} ∧
      fairTape {tape : Tape | scan m γ tape d = Sum.inr j} = (2 : ℝ≥0∞)⁻¹ ^ d := by
    have event : {tape : Tape | scan m γ tape d = Sum.inr j} =
        {tape : Tape | List.ofFn (fun i : Fin d => tape i.val) = (continuing m γ d)[j]} := by
      ext tape
      simp only [Set.mem_ofPred_eq, (scan_tree m γ hγ).1]
      exact ⟨fun H => H.2, fun H => ⟨hj, H⟩⟩
    rw [event]
    exact prefix_measure d _ ((layers d).2.2 _ (List.getElem_mem hj))
  have active (d : ℕ) : MeasurableSet {tape : Tape | (scan m γ tape d).isRight} ∧
      fairTape {tape : Tape | (scan m γ tape d).isRight} =
        ENNReal.ofReal (((γ.state d).r : ℝ) / (2 : ℝ) ^ d) := by
    let slots := Fin (continuing m γ d).length
    let A : slots → Set Tape := fun j => {tape | scan m γ tape d = Sum.inr j.val}
    have event : {tape : Tape | (scan m γ tape d).isRight} = ⋃ j : slots, A j := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro H
        cases hs : scan m γ tape d with
        | inl returned => simp [hs] at H
        | inr j =>
          obtain ⟨hj, _⟩ := ((scan_tree m γ hγ).1 d tape j).mp hs
          exact ⟨⟨j, hj⟩, hs⟩
      · rintro ⟨j, H⟩
        simp [show scan m γ tape d = Sum.inr j.val from H]
    have measurable_A (j : slots) : MeasurableSet (A j) := (slot_measure d j.val j.isLt).1
    have disjoint_A : Pairwise fun i j : slots => Disjoint (A i) (A j) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro tape hi hj
      have H : i.val = j.val := Sum.inr.inj (hi.symm.trans hj)
      exact hij (Fin.ext H)
    rw [event]
    refine ⟨MeasurableSet.iUnion measurable_A, ?_⟩
    rw [measure_iUnion disjoint_A measurable_A]
    simp_rw [show ∀ j : slots, fairTape (A j) = (2 : ℝ≥0∞)⁻¹ ^ d from
      fun j => (slot_measure d j.val j.isLt).2]
    rw [tsum_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, slots]
    rw [← (layers d).1]
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_pow, div_eq_mul_inv, ENNReal.inv_pow]
  have terminates : ∀ᵐ tape ∂fairTape, ∃ d, (scan m γ tape d).isLeft := by
    apply ae_iff.mpr
    apply ENNReal.eq_zero_of_le_mul_pow (ε := (m : NNReal))
      (r := (2 : ℝ≥0∞)⁻¹) (by norm_num)
    intro d
    have subset : {tape : Tape | ¬ ∃ n, (scan m γ tape n).isLeft} ⊆
        {tape : Tape | (scan m γ tape d).isRight} := by
      intro tape H
      cases hs : scan m γ tape d with
      | inl returned => exact False.elim (H ⟨d, by simp [hs]⟩)
      | inr j => simp [hs]
    have width : (continuing m γ d).length ≤ m := by
      have H := (hγ.2 d).1.1.2.1
      have HL := (layers d).1
      omega
    calc
      fairTape {tape : Tape | ¬ ∃ n, (scan m γ tape n).isLeft} ≤
          fairTape {tape : Tape | (scan m γ tape d).isRight} := measure_mono subset
      _ = (continuing m γ d).length * (2 : ℝ≥0∞)⁻¹ ^ d := by
        rw [(active d).2, ← (layers d).1]
        rw [ENNReal.ofReal_div_of_pos (by positivity)]
        simp [ENNReal.ofReal_pow, div_eq_mul_inv, ENNReal.inv_pow]
      _ ≤ ((m : NNReal) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ d := by
        gcongr
        exact_mod_cast width
  have expectation : (∫⁻ tape, bill m γ tape ∂fairTape) =
      ENNReal.ofReal (pathCost γ) := by
    have integrand_measurable (d : ℕ) : Measurable
        (fun tape : Tape => if (scan m γ tape d).isRight then (1 : ℝ≥0∞) else 0) := by
      convert (measurable_const : Measurable (fun _ : Tape => (1 : ℝ≥0∞))).indicator
        (active d).1 using 1
      ext tape
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    unfold bill
    rw [lintegral_tsum (fun d => (integrand_measurable d).aemeasurable)]
    have integral_column (d : ℕ) :
        (∫⁻ tape : Tape, (if (scan m γ tape d).isRight then (1 : ℝ≥0∞) else 0) ∂fairTape) =
          ENNReal.ofReal (((γ.state d).r : ℝ) / (2 : ℝ) ^ d) := by
      rw [← (active d).2]
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
        (lintegral_indicator_one (μ := fairTape) (active d).1)
    simp_rw [integral_column]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rfl
    · intro d; exact div_nonneg (by exact_mod_cast (hγ.2 d).1.1.1) (by positivity)
    · exact (law_bounds m hm γ hγ).2.2.2.2.2.1
  exact ⟨active, terminates, expectation, prefix_measure⟩

private theorem returned_law (m : ℕ) (hm : 2 ≤ m) (γ : Path) (hγ : IsRootPath m γ) :
    (∀ tape (i : Fin m) n, sample m γ tape = some (i, n) ↔
      scan m γ tape n = Sum.inl (i, n)) ∧
    (∀ tape (i : Fin m) n, sample m γ tape = some (i, n) → bill m γ tape = n) ∧
    (∀ d, {tape : Tape | sample m γ tape = none ∨
        ∃ i n, sample m γ tape = some (i, n) ∧ d < n} =
      {tape : Tape | (scan m γ tape d).isRight}) ∧
    D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree
      {w : List Bool | ∃ d : ℕ, ∃ i : Fin m, (w, i) ∈ stopping m γ d} ∧
    (∀ i : Fin m, MeasurableSet {tape : Tape | ∃ n, sample m γ tape = some (i, n)} ∧
      fairTape {tape : Tape | ∃ n, sample m γ tape = some (i, n)} =
        ENNReal.ofReal (labelLaw γ i)) := by
  classical
  have origin := (scan_tree m γ hγ).2.2
  have leaf_words := (scan_tree m γ hγ).2.1
  have layers := (tree_layers m γ hγ).2.2
  have persistent (d e : ℕ) (hde : d ≤ e) (tape : Tape) (returned : Fin m × ℕ)
      (hs : scan m γ tape d = Sum.inl returned) : scan m γ tape e = Sum.inl returned := by
    induction e, hde using Nat.le_induction with
    | base => exact hs
    | succ e he ih => simp only [scan, ih]
  have sample_eq (tape : Tape) (i : Fin m) (n : ℕ) :
      sample m γ tape = some (i, n) ↔ scan m γ tape n = Sum.inl (i, n) := by
    constructor
    · intro H
      unfold sample at H
      split at H
      next hex =>
        cases hs : scan m γ tape (Nat.find hex) with
        | inr a => simp [hs] at H
        | inl returned =>
          have he : returned = (i, n) := by simpa [hs] using H
          rw [he] at hs
          exact (origin _ tape i n hs).2.2.1
      next hnone => simp at H
    · intro H
      have data := origin n tape i n H
      have hex : ∃ d, (scan m γ tape d).isLeft := ⟨n, by simp [H]⟩
      have first : Nat.find hex = n := (Nat.find_eq_iff hex).mpr
        ⟨by simp [H], fun d hd => by
          have HH := data.2.2.2 d hd
          cases hs : scan m γ tape d <;> simp_all⟩
      simp only [sample, dif_pos hex, first, H, Sum.getLeft?_inl]
  have charged (tape : Tape) (i : Fin m) (n : ℕ) (H : sample m γ tape = some (i, n)) :
      bill m γ tape = n := by
    have hs := (sample_eq tape i n).mp H
    have data := origin n tape i n hs
    unfold bill
    rw [tsum_eq_sum (s := Finset.range n) (fun d hd => by
      have hnd : n ≤ d := by simpa only [Finset.mem_range, not_lt] using hd
      have HH := persistent n d hnd tape (i, n) hs
      simp [HH])]
    simp only [Finset.sum_congr rfl (fun d hd =>
      show (if (scan m γ tape d).isRight then (1 : ℝ≥0∞) else 0) = 1 by
        rw [if_pos (data.2.2.2 d (Finset.mem_range.mp hd))]),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have tail_event (d : ℕ) : {tape : Tape | sample m γ tape = none ∨
        ∃ i n, sample m γ tape = some (i, n) ∧ d < n} =
      {tape : Tape | (scan m γ tape d).isRight} := by
    ext tape
    constructor
    · rintro (H | ⟨i, n, H, hdn⟩)
      · cases hs : scan m γ tape d with
        | inr a => simp [hs]
        | inl returned =>
          have hs' := (origin d tape returned.1 returned.2 hs).2.2.1
          have HH := (sample_eq tape returned.1 returned.2).mpr hs'
          rw [H] at HH
          cases HH
      · exact (origin n tape i n ((sample_eq tape i n).mp H)).2.2.2 d hdn
    · intro H
      cases hs : sample m γ tape with
      | none => exact Or.inl hs
      | some returned =>
        rcases returned with ⟨i, n⟩
        refine Or.inr ⟨i, n, hs, ?_⟩
        by_contra hdn
        have HH := persistent n d (by omega) tape (i, n) ((sample_eq tape i n).mp hs)
        simp [HH] at H
  have word_from_prefix (u v : List Bool) (hprefix : u <+: v) (n : ℕ) (hu : u.length = n) :
      List.ofFn (fun j : Fin n => v.getD j.val false) = u := by
    apply List.ext_getElem (by simp [hu])
    intro j hj hj'
    simp only [List.getElem_ofFn]
    have H := hprefix.getElem hj'
    rw [List.getElem_eq_getD false] at H
    exact H.symm
  have prefix_free : D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree
      {w : List Bool | ∃ d : ℕ, ∃ i : Fin m, (w, i) ∈ stopping m γ d} := by
    rintro u ⟨d, i, hu⟩ v ⟨e, j, hv⟩ hp
    have hlu := (layers d).2.2 (u, i) hu
    have hlv := (layers e).2.2 (v, j) hv
    let tape : Tape := fun n => v.getD n false
    have Hu : scan m γ tape (d + 1) = Sum.inl (i, d + 1) := by
      apply (leaf_words d tape i).mpr
      simpa only [word_from_prefix u v hp (d + 1) hlu] using hu
    have Hv : scan m γ tape (e + 1) = Sum.inl (j, e + 1) := by
      apply (leaf_words e tape j).mpr
      simpa only [word_from_prefix v v (List.prefix_refl v) (e + 1) hlv] using hv
    have hde : d + 1 ≤ e + 1 := by simpa [hlu, hlv] using hp.length_le
    have HH := persistent (d + 1) (e + 1) hde tape (i, d + 1) Hu
    have lengths := congrArg Prod.snd (Sum.inl.inj (HH.symm.trans Hv))
    exact hp.eq_of_length (by omega)
  have one_leaf (d : ℕ) (i : Fin m) :
      MeasurableSet {tape : Tape | sample m γ tape = some (i, d + 1)} ∧
      fairTape {tape : Tape | sample m γ tape = some (i, d + 1)} =
        ENNReal.ofReal (Real.ofDigitsTerm (labelDigit γ i) d) := by
    have event : {tape : Tape | sample m γ tape = some (i, d + 1)} =
        {tape : Tape | (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈ stopping m γ d} := by
      ext tape
      exact (sample_eq tape i (d + 1)).trans (leaf_words d tape i)
    rw [event]
    by_cases hi : i ∈ labelSet m γ d
    · have Hmem : i ∈ (stopping m γ d).map Prod.snd := by
        rw [(layers d).1]
        exact (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨pair, hpair, hp⟩ := List.mem_map.mp Hmem
      rcases pair with ⟨w, j⟩
      change j = i at hp
      subst j
      have nodup : ((stopping m γ d).map Prod.snd).Nodup := by
        rw [(layers d).1]; exact Finset.sort_nodup _ _
      have event' : {tape : Tape | (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈
          stopping m γ d} = {tape : Tape | List.ofFn (fun j : Fin (d + 1) => tape j.val) = w} := by
        ext tape
        constructor
        · intro H
          exact congrArg Prod.fst (List.inj_on_of_nodup_map nodup _ H _ hpair rfl)
        · intro H; simpa only [H] using hpair
      rw [event']
      have data := (fair_tail m hm γ hγ).2.2.2 (d + 1) w ((layers d).2.2 (w, i) hpair)
      refine ⟨data.1, ?_⟩
      rw [data.2]
      simp [Real.ofDigitsTerm, labelDigit, hi, ENNReal.ofReal_mul, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_pow, ENNReal.inv_pow]
    · have event' : {tape : Tape | (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈
          stopping m γ d} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro tape H
        have HH := List.mem_map_of_mem Prod.snd H
        rw [(layers d).1] at HH
        exact hi ((Finset.mem_sort (· ≤ ·)).mp HH)
      rw [event']
      simp [Real.ofDigitsTerm, labelDigit, hi]
  have returned (i : Fin m) :
      MeasurableSet {tape : Tape | ∃ n, sample m γ tape = some (i, n)} ∧
      fairTape {tape : Tape | ∃ n, sample m γ tape = some (i, n)} =
        ENNReal.ofReal (labelLaw γ i) := by
    have event : {tape : Tape | ∃ n, sample m γ tape = some (i, n)} =
        ⋃ d : ℕ, {tape : Tape | sample m γ tape = some (i, d + 1)} := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨n, H⟩
        have Hpos := (origin n tape i n ((sample_eq tape i n).mp H)).1
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        exact ⟨d, H⟩
      · rintro ⟨d, H⟩; exact ⟨d + 1, H⟩
    rw [event]
    refine ⟨MeasurableSet.iUnion (fun d => (one_leaf d i).1), ?_⟩
    rw [measure_iUnion (fun d e hde => Set.disjoint_left.mpr (fun tape hd he => by
      have H := congrArg Prod.snd (Option.some.inj (hd.symm.trans he))
      exact hde (by omega))) (fun d => (one_leaf d i).1)]
    simp_rw [(fun d => (one_leaf d i).2)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun d => Real.ofDigitsTerm_nonneg)
      Real.summable_ofDigitsTerm]
    rfl
  exact ⟨sample_eq, charged, tail_event, prefix_free, returned⟩

/-- Every legal root path realizes its fixed-label law on the independent fair
bit tape, with its own prefix leaves, charged stopping length and tail cost. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (γ : Path) (hγ : IsRootPath m γ) :
    (∀ i : Fin m, 0 ≤ labelLaw γ i) ∧
    (∑ i : Fin m, labelLaw γ i) = 1 ∧
    labelLaw (m := m) γ ⟨0, by omega⟩ = anchorValue γ ∧
    (∀ i : Fin m, anchorValue γ ≤ labelLaw γ i) ∧
    (0 < anchorValue γ → ∀ i : Fin m, 0 < labelLaw γ i) ∧
    D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree
      {w : List Bool | ∃ d : ℕ, ∃ i : Fin m, (w, i) ∈ stopping m γ d} ∧
    (∀ d, (stopping m γ d).map Prod.snd = labels m γ d ∧
      (∀ w ∈ stopping m γ d, w.1.length = d + 1)) ∧
    (∀ tape (i : Fin m) d, sample m γ tape = some (i, d + 1) ↔
      (List.ofFn (fun j : Fin (d + 1) => tape j.val), i) ∈ stopping m γ d) ∧
    (∀ tape (i : Fin m) n, sample m γ tape = some (i, n) → bill m γ tape = n) ∧
    (∀ i : Fin m, MeasurableSet {tape : Tape | ∃ n, sample m γ tape = some (i, n)} ∧
      fairTape {tape : Tape | ∃ n, sample m γ tape = some (i, n)} =
        ENNReal.ofReal (labelLaw γ i)) ∧
    (∀ d, MeasurableSet {tape : Tape | sample m γ tape = none ∨
        ∃ i n, sample m γ tape = some (i, n) ∧ d < n} ∧
      fairTape {tape : Tape | sample m γ tape = none ∨
        ∃ i n, sample m γ tape = some (i, n) ∧ d < n} =
          ENNReal.ofReal (((γ.state d).r : ℝ) / (2 : ℝ) ^ d)) ∧
    (∀ᵐ tape ∂fairTape, ∃ i n, sample m γ tape = some (i, n)) ∧
    (∫⁻ tape, bill m γ tape ∂fairTape) = ENNReal.ofReal (pathCost γ) ∧
    pathCost γ ≤ m ∧ DyadicSupportLines.cost (labelLaw (m := m) γ) ≤ pathCost γ := by
  classical
  obtain ⟨nonneg, total, anchor, minimum, positive, _, upper, lower⟩ := law_bounds m hm γ hγ
  obtain ⟨first, charged, tail_event, prefix_free, returned⟩ := returned_law m hm γ hγ
  obtain ⟨tails, terminates, expectation, _⟩ := fair_tail m hm γ hγ
  refine ⟨nonneg, total, anchor, minimum, positive, prefix_free, ?_, ?_, charged,
    returned, ?_, ?_, expectation, upper, lower⟩
  · intro d
    exact ⟨((tree_layers m γ hγ).2.2 d).1, ((tree_layers m γ hγ).2.2 d).2.2⟩
  · intro tape i d
    exact (first tape i (d + 1)).trans ((scan_tree m γ hγ).2.1 d tape i)
  · intro d; rw [tail_event d]; exact tails d
  · filter_upwards [terminates] with tape ht
    obtain ⟨d, hd⟩ := ht
    cases hs : scan m γ tape d with
    | inr j => simp [hs] at hd
    | inl returned =>
      refine ⟨returned.1, returned.2, (first tape returned.1 returned.2).mpr ?_⟩
      exact ((scan_tree m γ hγ).2.2 d tape returned.1 returned.2 hs).2.2.1

end D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
