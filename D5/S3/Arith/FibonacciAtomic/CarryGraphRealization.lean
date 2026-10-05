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
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hwv
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
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hwv
    rcases hwv with he | he <;> rw [he] <;> simp [(layer d).2.2 v hv]

end D5.S3.Arith.FibonacciAtomic.CarryGraphRealization
