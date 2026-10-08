/- GID: D5/S3/Combinatorics/PathAlignedPacking/Schemes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Schemes
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: [mathlib/module/Mathlib.Data.Fin.VecNotation]
   utility: none
   digest: Repeated four-vertex prefixes give certified colourings of arbitrarily long arcs. -/

import D5.S3.Combinatorics.PathAlignedPacking.Metric
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs
open D5.S3.Combinatorics.PathAlignedPacking.Metric

structure Scheme where
  a : ℕ
  b : ℕ
  period : ℕ
  colours : ℕ
  pumpA : Bool
  pumpB : Bool
  colour : Fin period → Fin (a + b) → ℕ

def WellFormed (s : Scheme) : Prop :=
  1 ≤ s.a ∧ 1 ≤ s.b ∧ 0 < s.period ∧ s.colours ≤ 6 ∧
  (s.pumpA = true → 5 ≤ s.a) ∧ (s.pumpB = true → 5 ≤ s.b)

def Allowed (s : Scheme) (ka kb : ℤ) : Prop :=
  0 ≤ ka ∧ 0 ≤ kb ∧ (s.pumpA = false → ka = 0) ∧ (s.pumpB = false → kb = 0)

def arcA (s : Scheme) (ka : ℤ) : ℤ := s.a + 4 * ka
def arcB (s : Scheme) (kb : ℤ) : ℤ := s.b + 4 * kb

/-- The first four interior vertices of a pumped arc each become an arithmetic progression.
    Every other base vertex is a singleton translated past the inserted prefixes. -/
def position (s : Scheme) (j : Fin (s.a + s.b)) (ka kb r : ℤ) : ℤ :=
  if j.val = 0 then 0
  else if j.val ≤ s.a then
    if s.pumpA = true ∧ j.val ≤ 4 then (j.val : ℤ) + 4 * r
    else (j.val : ℤ) + 4 * ka
  else if s.pumpB = true ∧ j.val ≤ s.a + 4 then (j.val : ℤ) + 4 * ka + 4 * r
  else (j.val : ℤ) + 4 * ka + 4 * kb

def runLimit (s : Scheme) (j : Fin (s.a + s.b)) (ka kb : ℤ) : ℤ :=
  if s.pumpA = true ∧ 1 ≤ j.val ∧ j.val ≤ 4 then ka
  else if s.pumpB = true ∧ s.a < j.val ∧ j.val ≤ s.a + 4 then kb
  else 0

/-- Only four block offsets are needed: an offset at least four costs at least seven edges. -/
def Safe (s : Scheme) : Prop :=
  (∀ i j, 1 ≤ s.colour i j ∧ s.colour i j ≤ s.colours) ∧
  ∀ (i : Fin s.period) (d : Fin 4) (j h : Fin (s.a + s.b)) (ka kb r q : ℤ),
    Allowed s ka kb → 0 ≤ r → r ≤ runLimit s j ka kb →
    0 ≤ q → q ≤ runLimit s h ka kb →
    (d.val = 0 → position s j ka kb r ≠ position s h ka kb q) →
    s.colour i j = s.colour ⟨(i.val + d.val) % s.period,
      Nat.mod_lt _ i.pos⟩ h →
    (s.colour i j : ℤ) < chainSep (arcA s ka) (arcB s kb)
      (0, position s j ka kb r) (d.val, position s h ka kb q)

private theorem cover (s : Scheme) (hw : WellFormed s) (ka kb : ℤ)
    (hk : Allowed s ka kb) (x : ℤ) (hx : 0 ≤ x) (hxn : x < arcA s ka + arcB s kb) :
    ∃ j : Fin (s.a + s.b), ∃ r : ℤ,
      0 ≤ r ∧ r ≤ runLimit s j ka kb ∧ position s j ka kb r = x := by
  rcases hw with ⟨ha, hb, hperiod, hcolours, hpa, hpb⟩
  rcases hk with ⟨hka, hkb, hka0, hkb0⟩
  simp only [arcA, arcB] at hxn
  have index (z r : ℤ) (hz : 0 ≤ z) (hzn : z < (s.a : ℤ) + s.b)
      (hr : 0 ≤ r) (hlim : r ≤ runLimit s ⟨z.toNat, by omega⟩ ka kb)
      (hpos : position s ⟨z.toNat, by omega⟩ ka kb r = x) :
      ∃ j : Fin (s.a + s.b), ∃ r : ℤ,
        0 ≤ r ∧ r ≤ runLimit s j ka kb ∧ position s j ka kb r = x := by
    exact ⟨⟨z.toNat, by omega⟩, r, hr, hlim, hpos⟩
  by_cases hx0 : x = 0
  · subst x
    refine index 0 0 (by omega) (by omega) (by omega) ?_ ?_
    · simp [runLimit]
    · simp [position]
  by_cases hxA : x ≤ (s.a : ℤ) + 4 * ka
  · cases hpa' : s.pumpA with
    | false =>
      have hzero := hka0 hpa'
      subst ka
      refine index x 0 (by omega) (by omega) (by omega) ?_ ?_
      · simp [runLimit, hpa']; split_ifs <;> omega
      · simp [position, hpa', Bool.false_eq_true, false_and, if_false,
          Fin.val_mk, Int.toNat_of_nonneg hx]
        split_ifs <;> omega
    | true =>
      have hlong := hpa hpa'
      by_cases hword : x ≤ 4 * ka + 4
      · let z := (x - 1) % 4 + 1
        let r := (x - 1) / 4
        have hz : 1 ≤ z ∧ z ≤ 4 := by dsimp [z]; omega
        have hr : 0 ≤ r ∧ r ≤ ka := by dsimp [r]; omega
        have hrep : z + 4 * r = x := by dsimp [z, r]; omega
        refine index z r (by omega) (by omega) hr.1 ?_ ?_
        · simp [runLimit, hpa', Fin.val_mk]
          split_ifs <;> dsimp [z, r] at * <;> omega
        · simp [position, hpa', Fin.val_mk, Int.toNat_of_nonneg (by omega : 0 ≤ z)]
          split_ifs <;> dsimp [z, r] at * <;> omega
      · let z := x - 4 * ka
        have hz : 4 < z ∧ z ≤ s.a := by dsimp [z]; omega
        refine index z 0 (by omega) (by omega) (by omega) ?_ ?_
        · simp [runLimit, hpa', Fin.val_mk]; split_ifs <;> dsimp [z] at * <;> omega
        · simp [position, hpa', Fin.val_mk, Int.toNat_of_nonneg (by omega : 0 ≤ z)]
          split_ifs <;> dsimp [z] at * <;> omega
  · let p := x - ((s.a : ℤ) + 4 * ka)
    have hp : 1 ≤ p ∧ p < (s.b : ℤ) + 4 * kb := by dsimp [p]; omega
    cases hpb' : s.pumpB with
    | false =>
      have hzero := hkb0 hpb'
      subst kb
      let z := x - 4 * ka
      have hz : (s.a : ℤ) < z ∧ z < (s.a : ℤ) + s.b := by dsimp [z, p] at *; omega
      refine index z 0 (by omega) hz.2 (by omega) ?_ ?_
      · simp [runLimit, hpb', Fin.val_mk]; split_ifs <;> omega
      · simp [position, hpb', Fin.val_mk, Int.toNat_of_nonneg (by omega : 0 ≤ z)]
        split_ifs <;> dsimp [z] at * <;> omega
    | true =>
      have hlong := hpb hpb'
      by_cases hword : p ≤ 4 * kb + 4
      · let z := (s.a : ℤ) + (p - 1) % 4 + 1
        let r := (p - 1) / 4
        have hz : (s.a : ℤ) + 1 ≤ z ∧ z ≤ (s.a : ℤ) + 4 := by dsimp [z]; omega
        have hr : 0 ≤ r ∧ r ≤ kb := by dsimp [r]; omega
        have hrep : z + 4 * ka + 4 * r = x := by dsimp [z, r, p]; omega
        have hzNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
        have hnotA : ¬ (s.pumpA = true ∧ 1 ≤ z.toNat ∧ z.toNat ≤ 4) := by
          rintro ⟨hpump, _, hfour⟩
          have := hpa hpump
          omega
        refine index z r (by omega) (by omega) hr.1 ?_ ?_
        · have hzgt : s.a < z.toNat := by omega
          have hzle : z.toNat ≤ s.a + 4 := by omega
          have hyes : s.pumpB = true ∧ s.a < z.toNat ∧ z.toNat ≤ s.a + 4 :=
            ⟨hpb', hzgt, hzle⟩
          simp only [runLimit, if_neg hnotA, if_pos hyes]
          exact hr.2
        · simp [position, hpb', Fin.val_mk, Int.toNat_of_nonneg (by omega : 0 ≤ z)]
          split_ifs <;> dsimp [z, r, p] at * <;> omega
      · let z := x - 4 * ka - 4 * kb
        have hz : (s.a : ℤ) + 4 < z ∧ z < (s.a : ℤ) + s.b := by dsimp [z, p] at *; omega
        refine index z 0 (by omega) hz.2 (by omega) ?_ ?_
        · simp [runLimit, hpb', Fin.val_mk]; split_ifs <;> dsimp [z, p] at * <;> omega
        · simp [position, hpb', Fin.val_mk, Int.toNat_of_nonneg (by omega : 0 ≤ z)]
          split_ifs <;> dsimp [z] at * <;> omega

/-- This proves all repetitions at once. The finite `Safe` certificates below are
    universally quantified in the four integer repetition coordinates. -/
theorem exists_metric (s : Scheme) (hw : WellFormed s) (hs : Safe s)
    (ka kb : ℤ) (hk : Allowed s ka kb) : HasMetricColor (arcA s ka) (arcB s kb) s.colours := by
  classical
  have translate (a b : ℤ) (u v : Point) (huv : u.1 ≤ v.1) :
      chainSep a b u v = chainSep a b (0, u.2) (v.1 - u.1, v.2) := by
    simp only [chainSep, Prod.fst, Prod.snd, Nat.cast_zero, Nat.cast_sub huv]
    split_ifs <;> try omega
    all_goals ring
  let a := arcA s ka
  let b := arcB s kb
  have ha : 1 ≤ a := by dsimp [a, arcA]; have := hw.1; have := hk.1; omega
  have hb : 1 ≤ b := by dsimp [b, arcB]; have := hw.2.1; have := hk.2.1; omega
  let U := {u : Point // 0 ≤ u.2 ∧ u.2 < a + b}
  have hc (u : U) := cover s hw ka kb hk u.val.2 u.property.1 u.property.2
  let pick (u : U) : Fin (s.a + s.b) × ℤ :=
    (Classical.choose (hc u), Classical.choose (Classical.choose_spec (hc u)))
  have pick_spec (u : U) :
      0 ≤ (pick u).2 ∧ (pick u).2 ≤ runLimit s (pick u).1 ka kb ∧
        position s (pick u).1 ka kb (pick u).2 = u.val.2 := by
    exact Classical.choose_spec (Classical.choose_spec (hc u))
  let phase (u : Point) : Fin s.period := ⟨u.1 % s.period, Nat.mod_lt _ hw.2.2.1⟩
  let f (u : Point) : ℕ :=
    if h : 0 ≤ u.2 ∧ u.2 < a + b then s.colour (phase u) (pick ⟨u, h⟩).1 else 1
  have forward (u v : Point) (hu : 0 ≤ u.2 ∧ u.2 < a + b)
      (hv : 0 ≤ v.2 ∧ v.2 < a + b) (hne : u ≠ v) (heq : f u = f v)
      (horder : u.1 ≤ v.1) : (f u : ℤ) < chainSep a b u v := by
    have hfu : f u = s.colour (phase u) (pick ⟨u, hu⟩).1 := by simp [f, hu]
    have hfv : f v = s.colour (phase v) (pick ⟨v, hv⟩).1 := by simp [f, hv]
    have hj := pick_spec ⟨u, hu⟩
    have hh := pick_spec ⟨v, hv⟩
    by_cases hfar : u.1 + 4 ≤ v.1
    · have hbound := (hs.1 (phase u) (pick ⟨u, hu⟩).1).2
      have hdist := far_blocks a b u v ha hb hu hv hfar
      have hk6 := hw.2.2.2.1
      omega
    · let d : Fin 4 := ⟨v.1 - u.1, by omega⟩
      have hphase : phase v = ⟨((phase u).val + d.val) % s.period,
          Nat.mod_lt _ (phase u).pos⟩ := by
        apply Fin.ext
        have hvnum : v.1 = u.1 + d.val := by dsimp [d]; omega
        simp [phase, hvnum, Nat.add_mod]
      have hneq : d.val = 0 → position s (pick ⟨u, hu⟩).1 ka kb (pick ⟨u, hu⟩).2 ≠
          position s (pick ⟨v, hv⟩).1 ka kb (pick ⟨v, hv⟩).2 := by
        intro hd hpos
        apply hne; apply Prod.ext
        · dsimp [d] at hd; omega
        · rw [hj.2.2, hh.2.2] at hpos; exact hpos
      have hcolour : s.colour (phase u) (pick ⟨u, hu⟩).1 =
          s.colour ⟨((phase u).val + d.val) % s.period,
            Nat.mod_lt _ (phase u).pos⟩ (pick ⟨v, hv⟩).1 := by
        rw [← hphase, ← hfu, ← hfv]; exact heq
      have hsafe := hs.2 (phase u) d (pick ⟨u, hu⟩).1 (pick ⟨v, hv⟩).1 ka kb
        (pick ⟨u, hu⟩).2 (pick ⟨v, hv⟩).2 hk hj.1 hj.2.1 hh.1 hh.2.1 hneq hcolour
      rw [hj.2.2, hh.2.2, ← hfu] at hsafe
      simpa only [a, b, d, translate a b u v horder] using hsafe
  refine ⟨f, ?_, ?_⟩
  · intro u hu hun
    simpa [f, show 0 ≤ u.2 ∧ u.2 < a + b from ⟨hu, hun⟩] using
      hs.1 (phase u) (pick ⟨u, ⟨hu, hun⟩⟩).1
  · intro u v hu hun hv hvn hne heq
    rcases le_total u.1 v.1 with horder | horder
    · exact forward u v ⟨hu, hun⟩ ⟨hv, hvn⟩ hne heq horder
    · have hh := forward v u ⟨hv, hvn⟩ ⟨hu, hun⟩ (Ne.symm hne) heq.symm horder
      simpa [heq, chain_symm a b v u] using hh

end D5.S3.Combinatorics.PathAlignedPacking.Schemes
