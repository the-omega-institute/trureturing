/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Boundary-word encoding of literal stress-three rectangles. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import OmegaBuild.Commands

compile_only_with_mathlib

/-! Boundary-word encoding of literal stress-three rectangles. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding


open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open scoped BigOperators

set_option warningAsError true

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence (fin_constant)

private abbrev Grid (h w : ℕ) := Fin (h + 1) → Fin (w + 1) → Fin 4
abbrev Word (n : ℕ) := Fin (n + 1) → Fin 6

private def stress (a b c d : ℕ) : ℕ :=
  Int.natAbs ((a : ℤ) + d - (b + c))

private abbrev Legal {h w : ℕ} (x : Grid h w) : Prop :=
  D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.Legal 3 (fun p => x p.1 p.2)

private def raw (p q : ℕ) (a b : Fin 6) : ℕ := (a.val + b.val + 3 * p * q) % 6

def Cross (p q : ℕ) (a a' b b' : Fin 6) : Prop :=
  let x := raw p q a b
  let y := raw p (1-q) a b'
  let z := raw (1-p) q a' b
  let t := raw (1-p) (1-q) a' b'
  x < 4 ∧ y < 4 ∧ z < 4 ∧ t < 4 ∧ stress x y z t = 3

instance (p q : ℕ) (a a' b b' : Fin 6) : Decidable (Cross p q a a' b b') := by
  unfold Cross
  infer_instance

def CodeOK {h w : ℕ} (r : Word h) (c : Word w) : Prop :=
  c 0 = 0 ∧ ∀ (i : Fin h) (j : Fin w),
    Cross (i.val % 2) (j.val % 2) (r i.castSucc) (r i.succ) (c j.castSucc) (c j.succ)

theorem next_parity (n : ℕ) : (n+1) % 2 = 1 - n % 2 := by omega

private def GX {h w : ℕ} (x : Grid h w) (i : Fin (h+1)) (j : Fin (w+1)) : ZMod 6 :=
  (x i j).val

private lemma zstress (a b c d : ℕ) (h : stress a b c d = 3) :
    (a : ZMod 6) + d - (b + c) = 3 := by
  unfold stress at h
  rw [Int.natAbs_eq_iff] at h
  rcases h with h | h
  · simpa using congrArg (fun x : ℤ => (x : ZMod 6)) h
  · have hm : (a : ZMod 6) + d - (b + c) = -3 := by
      simpa using congrArg (fun x : ℤ => (x : ZMod 6)) h
    rw [hm]
    decide

private theorem additive_grid {h w : ℕ} (f : Fin (h+1) → Fin (w+1) → ZMod 6)
    (hf : ∀ (i : Fin h) (j : Fin w),
      f i.castSucc j.castSucc + f i.succ j.succ -
        (f i.castSucc j.succ + f i.succ j.castSucc) = 0)
    (i : Fin (h+1)) (j : Fin (w+1)) :
    f i j = f i 0 + (f 0 j - f 0 0) := by
  have hd (j : Fin w) (i : Fin (h+1)) :
      f i j.succ - f i j.castSucc = f 0 j.succ - f 0 j.castSucc := by
    apply fin_constant
      (fun i => f i j.succ - f i j.castSucc) _ i
    intro t
    linear_combination -(hf t j)
  have he : f i j - f 0 j = f i 0 - f 0 0 := by
    apply fin_constant (fun j => f i j - f 0 j) _ j
    intro t
    linear_combination -(hd t i)
  linear_combination he

private theorem parity_term (i j : ℕ) :
    (3 : ZMod 6) * (i : ZMod 6) * (j : ZMod 6) =
      (3 : ZMod 6) * (↑(i % 2) : ZMod 6) * (↑(j % 2) : ZMod 6) := by
  have aux (n : ℕ) : (n : ZMod 6) = ↑(n % 2) + 2 * ↑(n / 2) := by
    have eq := congrArg (fun x : ℕ => (x : ZMod 6)) (Nat.mod_add_div n 2).symm
    simpa using eq
  conv_lhs => rw [aux i, aux j]
  ring_nf
  have zero6 : (6 : ZMod 6) = 0 := by decide
  simp [zero6, show (12 : ZMod 6) = 0 by decide]

private def rowCode {h w : ℕ} (x : Grid h w) : Word h :=
  fun i => ⟨(x i 0).val, (x i 0).isLt.trans (by decide)⟩

private def colCode {h w : ℕ} (x : Grid h w) : Word w :=
  fun j => ⟨(GX x 0 j - GX x 0 0).val, ZMod.val_lt _⟩

private theorem reconstruct {h w : ℕ} {x : Grid h w} (hx : Legal x)
    (i : Fin (h+1)) (j : Fin (w+1)) :
    raw (i.val % 2) (j.val % 2) (rowCode x i) (colCode x j) = (x i j).val := by
  let f (i : Fin (h+1)) (j : Fin (w+1)) :=
    GX x i j - 3 * (i.val : ZMod 6) * (j.val : ZMod 6)
  have haf (i : Fin h) (j : Fin w) :
      f i.castSucc j.castSucc + f i.succ j.succ -
        (f i.castSucc j.succ + f i.succ j.castSucc) = 0 := by
    have hf := zstress _ _ _ _ (hx i j)
    unfold f GX
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    linear_combination hf
  have hf := additive_grid f haf i j
  simp [f, parity_term i.val j.val] at hf
  have hr : ((rowCode x i).val : ZMod 6) = GX x i 0 := rfl
  have hc : ((colCode x j).val : ZMod 6) = GX x 0 j - GX x 0 0 := by
    change (↑((GX x 0 j - GX x 0 0).val) : ZMod 6) = _
    exact ZMod.natCast_zmod_val _
  have hz : ((x i j).val : ZMod 6) =
      ((rowCode x i).val + (colCode x j).val + 3 * (i.val % 2) * (j.val % 2) : ℕ) := by
    push_cast
    rw [hr, hc]
    change GX x i j = _
    linear_combination hf
  have hz' := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt ((x i j).isLt.trans (by decide : 4 < 6)),
    ZMod.val_natCast] at hz'
  exact hz'.symm

private theorem code_of_legal {h w : ℕ} {x : Grid h w} (hx : Legal x) :
    CodeOK (rowCode x) (colCode x) := by
  constructor
  · apply Fin.ext
    simp [colCode]
  · intro i j
    have a := reconstruct hx i.castSucc j.castSucc
    have b := reconstruct hx i.castSucc j.succ
    have c := reconstruct hx i.succ j.castSucc
    have d := reconstruct hx i.succ j.succ
    simp only [Fin.val_castSucc, Fin.val_succ, next_parity] at a b c d
    simpa only [Cross, a, b, c, d, stress] using
      And.intro (x i.castSucc j.castSucc).isLt <|
      And.intro (x i.castSucc j.succ).isLt <|
      And.intro (x i.succ j.castSucc).isLt <|
      And.intro (x i.succ j.succ).isLt (hx i j)

private theorem raw_bound {h w : ℕ} (hh : 0 < h) (hw : 0 < w)
    {r : Word h} {c : Word w} (hc : CodeOK r c) (i : Fin (h+1)) (j : Fin (w+1)) :
    raw (i.val % 2) (j.val % 2) (r i) (c j) < 4 := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0)
  obtain ⟨i', hi⟩ := D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.inPair i
  obtain ⟨j', hj⟩ := D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.inPair j
  have H := hc.2 i' j'
  unfold Cross at H
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp only [Fin.val_castSucc, Fin.val_succ, next_parity]
  exacts [H.1, H.2.1, H.2.2.1, H.2.2.2.1]

private def decode {h w : ℕ} (hh : 0 < h) (hw : 0 < w)
    {r : Word h} {c : Word w} (hc : CodeOK r c) : Grid h w :=
  fun i j => ⟨raw (i.val % 2) (j.val % 2) (r i) (c j), raw_bound hh hw hc i j⟩

private theorem decode_legal {h w : ℕ} (hh : 0 < h) (hw : 0 < w)
    {r : Word h} {c : Word w} (hc : CodeOK r c) : Legal (decode hh hw hc) := by
  intro i j
  simpa only [decode, Fin.val_castSucc, Fin.val_succ, next_parity, stress] using
    (hc.2 i j).2.2.2.2

private theorem decode_row {h w : ℕ} (hh : 0 < h) (hw : 0 < w)
    {r : Word h} {c : Word w} (hc : CodeOK r c) :
    rowCode (decode hh hw hc) = r := by
  funext i
  apply Fin.ext
  simp [rowCode, decode, hc.1, raw, Nat.mod_eq_of_lt (r i).isLt]

private lemma decode_z {h w : ℕ} (hh : 0 < h) (hw : 0 < w)
    {r : Word h} {c : Word w} (hc : CodeOK r c) (j : Fin (w+1)) :
    GX (decode hh hw hc) 0 j = ((r 0).val : ZMod 6) + (c j).val := by
  simp [GX, decode, raw, ZMod.natCast_mod]

private theorem decode_col {h w : ℕ} (hh : 0 < h) (hw : 0 < w)
    {r : Word h} {c : Word w} (hc : CodeOK r c) :
    colCode (decode hh hw hc) = c := by
  funext j
  apply Fin.ext
  change (GX (decode hh hw hc) 0 j - GX (decode hh hw hc) 0 0).val = (c j).val
  rw [decode_z, decode_z, hc.1]
  simp [ZMod.val_natCast_of_lt (c j).isLt]

private def gridEquiv {h w : ℕ} (hh : 0 < h) (hw : 0 < w) :
    {x : Grid h w // Legal x} ≃ {rc : Word h × Word w // CodeOK rc.1 rc.2} where
  toFun x := ⟨(rowCode x.1, colCode x.1), code_of_legal x.2⟩
  invFun rc := ⟨decode hh hw rc.2, decode_legal hh hw rc.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i j
    apply Fin.ext
    exact reconstruct x.2 i j
  right_inv rc := by
    apply Subtype.ext
    exact Prod.ext (decode_row hh hw rc.2) (decode_col hh hw rc.2)


/-- Currying identifies the existing literal rectangle count with pairs of boundary words. -/
theorem count_codes (h w : ℕ) (hh : 0 < h) (hw : 0 < w) :
    C 3 3 h w = Nat.card {rc : Word h × Word w // CodeOK rc.1 rc.2} := by
  unfold C
  apply Nat.card_congr
  let curryEquiv :
      {x : D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.Grid 3 h w // D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.Legal 3 x} ≃
        {x : Grid h w // Legal x} :=
    { toFun := fun x => ⟨fun i j => x.1 (i,j), x.2⟩
      invFun := fun x => ⟨fun p => x.1 p.1 p.2, x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        funext ⟨i,j⟩
        rfl
      right_inv := fun x => rfl }
  exact curryEquiv.trans (gridEquiv hh hw)

/-- Transposition preserves the existing literal rectangle count. -/
theorem count_symm (h w : ℕ) : C 3 3 h w = C 3 3 w h := by
  unfold C
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨fun p => x.1 (p.2,p.1), ?_⟩
    invFun := fun x => ⟨fun p => x.1 (p.2,p.1), ?_⟩
    left_inv := fun x => by apply Subtype.ext; funext ⟨i,j⟩; rfl
    right_inv := fun x => by apply Subtype.ext; funext ⟨i,j⟩; rfl }
  all_goals
    intro i j
    simpa only [add_comm] using x.2 j i

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
