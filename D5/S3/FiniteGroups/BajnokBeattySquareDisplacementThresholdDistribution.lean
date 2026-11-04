/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdDistribution
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdDistribution
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The exact determinant histogram of two actual odd finite-group return thresholds. -/

import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
import D5.S3.Constants.Irrationality.LogNaturalIrrationality
import D5.S1.Phase.IntervalSampling
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution

open Filter Set
open scoped Topology BigOperators
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket

abbrev qAt (k : ℕ) : ℤ := 2 * (k : ℤ) + 3

/-- The five original single-crossing clauses, with no analytic premise. -/
def originalSC (p q : ℤ) (T : ℕ) : Prop :=
  ((q + 1) / 2).toNat < T ∧
    (∀ t : ℕ, ((q + 1) / 2).toNat ≤ t → t < T →
      (square_return_pair p q t).2 < (square_return_pair p q t).1) ∧
    (square_return_pair p q T).1 ≤ (square_return_pair p q T).2 ∧
    (∀ t : ℕ, T < t →
      (square_return_pair p q t).1 < (square_return_pair p q t).2) ∧
    T ≤ ((q * p + 1) / 2).toNat

abbrev bracketSC (p q : ℤ) (T : ℕ) : Prop :=
  originalSC p q T ∧
    ((q : ℝ)^2 - 1) * (p : ℝ) / (4 * (q : ℝ) * Real.log 2) +
        1 / (2 * (q : ℝ)) - 1 / (2 * (q : ℝ) * (p : ℝ)) < (T : ℝ) ∧
    (T : ℤ) ≤ Int.ceil ((p : ℝ) * (q : ℝ) / (4 * Real.log 2))

/-- The closed integer-valued mass.  The support test is in `ℤ`, including the
    divisibility branch, so negative determinant values are represented exactly. -/
def mass (p r z : ℤ) : ℝ :=
  let d : ℤ := Int.gcd p r
  if h : d ∣ z then
    let j : ℤ := z / d
    let a : ℤ := p / d
    let b : ℤ := r / d
    if -a < j ∧ j < b then
      (min (min a b) (min (a + j) (b - j)) : ℝ) /
        ((a : ℝ) * (b : ℝ))
    else 0
  else 0

private theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

private theorem log_two_irrational : Irrational (Real.log 2) :=
  _root_.D5.S3.Constants.Irrationality.LogNaturalIrrationality.irrational_log_natCast 2
    (by norm_num)

private def finiteResidues (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : Fin (a * b)) : Fin a × Fin b :=
  (⟨h.val % a, Nat.mod_lt _ ha⟩, ⟨h.val % b, Nat.mod_lt _ hb⟩)

private theorem finiteResidues_bijective
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    Function.Bijective (finiteResidues a b ha hb) := by
  constructor
  · intro x y hxy
    have hx := congrArg (fun uv : Fin a × Fin b => uv.1.val) hxy
    have hy := congrArg (fun uv : Fin a × Fin b => uv.2.val) hxy
    change x.val % a = y.val % a at hx
    change x.val % b = y.val % b at hy
    have hmod : Nat.ModEq (a * b) x.val y.val :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hx, hy⟩
    exact Fin.ext (hmod.eq_of_lt_of_lt x.isLt y.isLt)
  · rintro ⟨u, v⟩
    let c := Nat.chineseRemainder hab u.val v.val
    refine ⟨⟨c.val, Nat.chineseRemainder_lt_mul hab u.val v.val
      (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)⟩, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change c.val % a = u.val
      exact (show c.val % a = u.val % a from c.property.1).trans (Nat.mod_eq_of_lt u.isLt)
    · apply Fin.ext
      change c.val % b = v.val
      exact (show c.val % b = v.val % b from c.property.2).trans (Nat.mod_eq_of_lt v.isLt)

private def reflection (n : ℕ) (hn : 0 < n) : Fin n ≃ Fin n where
  toFun x := ⟨n - 1 - x.val, by have := x.isLt; omega⟩
  invFun x := ⟨n - 1 - x.val, by have := x.isLt; omega⟩
  left_inv x := by
    apply Fin.ext
    change n - 1 - (n - 1 - x.val) = x.val
    have := x.isLt
    omega
  right_inv x := by
    apply Fin.ext
    change n - 1 - (n - 1 - x.val) = x.val
    have := x.isLt
    omega

private def reflectedResidues (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Fin (a * b) → Fin a × Fin b :=
  (Equiv.prodCongr (reflection a ha) (reflection b hb)) ∘ finiteResidues a b ha hb

private theorem reflectedResidues_bijective
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    Function.Bijective (reflectedResidues a b ha hb) :=
  (Equiv.prodCongr (reflection a ha) (reflection b hb)).bijective.comp
    (finiteResidues_bijective a b ha hb hab)

private theorem reflected_difference
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((b - 1 - h % b : ℕ) : ℤ) - ((a - 1 - h % a : ℕ) : ℤ) =
      (b : ℤ) - a + ((h % a : ℕ) : ℤ) - ((h % b : ℕ) : ℤ) := by
  have hua := Nat.mod_lt h ha
  have hvb := Nat.mod_lt h hb
  omega

private theorem finite_crt_residue_count
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (j : ℤ) :
    ((Finset.range (a * b)).filter (fun h =>
      (b : ℤ) - a + ((h % a : ℕ) : ℤ) - ((h % b : ℕ) : ℤ) = j)).card =
      ((Finset.product (Finset.range a) (Finset.range b)).filter (fun uv =>
        (uv.2 : ℤ) - uv.1 = j)).card := by
  classical
  refine Finset.card_bij (fun h _ => (a - 1 - h % a, b - 1 - h % b)) ?_ ?_ ?_
  · intro h hh
    have hj := (Finset.mem_filter.mp hh).2
    have hua := Nat.mod_lt h ha
    have hvb := Nat.mod_lt h hb
    have hd := reflected_difference a b h ha hb
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      hd.trans hj⟩
  · intro x hx y hy hxy
    have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hu := congrArg (fun uv : ℕ × ℕ => uv.1) hxy
    have hv := congrArg (fun uv : ℕ × ℕ => uv.2) hxy
    have hxa := Nat.mod_lt x ha
    have hya := Nat.mod_lt y ha
    have hxb := Nat.mod_lt x hb
    have hyb := Nat.mod_lt y hb
    have hma : Nat.ModEq a x y := by dsimp at hu; change x % a = y % a; omega
    have hmb : Nat.ModEq b x y := by dsimp at hv; change x % b = y % b; omega
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hma, hmb⟩).eq_of_lt_of_lt
      hxlt hylt
  · intro uv huv
    rcases Finset.mem_filter.mp huv with ⟨hbox, hj⟩
    rcases Finset.mem_product.mp hbox with ⟨hu, hv⟩
    have hult := Finset.mem_range.mp hu
    have hvlt := Finset.mem_range.mp hv
    obtain ⟨h, he⟩ := (reflectedResidues_bijective a b ha hb hab).2
      (⟨uv.1, hult⟩, ⟨uv.2, hvlt⟩)
    have hx := congrArg (fun w : Fin a × Fin b => w.1.val) he
    have hy := congrArg (fun w : Fin a × Fin b => w.2.val) he
    change a - 1 - h.val % a = uv.1 at hx
    change b - 1 - h.val % b = uv.2 at hy
    have hd := reflected_difference a b h.val ha hb
    have hjh : (b : ℤ) - a + ((h.val % a : ℕ) : ℤ) - ((h.val % b : ℕ) : ℤ) = j := by
      rw [← hx, ← hy] at hj
      exact hd.symm.trans hj
    refine ⟨h.val, ?_, Prod.ext hx hy⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.isLt, hjh⟩

private theorem fiber_count_interval (a b : ℕ) (j : ℤ) :
    ((Finset.product (Finset.range a) (Finset.range b)).filter (fun uv =>
      (uv.2 : ℤ) - uv.1 = j)).card =
      (Finset.Icc (max 0 (-j)) (min ((a : ℤ) - 1) ((b : ℤ) - 1 - j))).card := by
  classical
  refine Finset.card_bij (fun uv _ => (uv.1 : ℤ)) ?_ ?_ ?_
  · intro uv huv
    rcases Finset.mem_filter.mp huv with ⟨hbox, hj⟩
    rcases Finset.mem_product.mp hbox with ⟨hu, hv⟩
    have hult := Finset.mem_range.mp hu
    have hvlt := Finset.mem_range.mp hv
    simp only [Finset.mem_Icc]
    omega
  · intro uv huv wx hwx he
    have hj := (Finset.mem_filter.mp huv).2
    have hk := (Finset.mem_filter.mp hwx).2
    apply Prod.ext <;> omega
  · intro u hu
    have hbounds := Finset.mem_Icc.mp hu
    have hu0 : 0 ≤ u := by omega
    have hv0 : 0 ≤ u + j := by omega
    have huc : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu0
    have hvc : ((u + j).toNat : ℤ) = u + j := Int.toNat_of_nonneg hv0
    refine ⟨(u.toNat, (u + j).toNat), ?_, huc⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      by omega⟩

theorem fiber_count_formula (a b : ℕ) (j : ℤ) :
    (((Finset.product (Finset.range a) (Finset.range b)).filter (fun uv =>
      (uv.2 : ℤ) - uv.1 = j)).card : ℤ) =
      max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) := by
  rw [fiber_count_interval, Int.card_Icc]
  omega

private theorem mass_on_support (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (j : ℤ)
    (hj : -(a : ℤ) < j ∧ j < (b : ℤ)) :
    max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) =
      min (min (a : ℤ) (b : ℤ)) (min ((a : ℤ) + j) ((b : ℤ) - j)) := by
  omega

private theorem mass_off_support (a b : ℕ) (j : ℤ)
    (hj : ¬ (-(a : ℤ) < j ∧ j < (b : ℤ))) :
    max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) = 0 := by
  omega

private theorem finite_histogram_formula
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (j : ℤ) :
    (((Finset.range (a * b)).filter (fun h =>
      (b : ℤ) - a + ((h % a : ℕ) : ℤ) - ((h % b : ℕ) : ℤ) = j)).card : ℤ) =
      max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) := by
  rw [finite_crt_residue_count a b ha hb hab j, fiber_count_formula]

private def idealOrbit (lam : ℝ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 3) * lam

private def idealDet (a b : ℕ) (y : ℝ) : ℤ :=
  (b : ℤ) * ⌈(a : ℝ) * y⌉ - (a : ℤ) * ⌈(b : ℝ) * y⌉

private def cellValue (a b h : ℕ) : ℤ :=
  (b : ℤ) - a + ((h % a : ℕ) : ℤ) - ((h % b : ℕ) : ℤ)

private def inCell (m h : ℕ) (y : ℝ) : Prop :=
  (h : ℝ) / (m : ℝ) ≤ Int.fract y ∧
    Int.fract y < ((h : ℝ) + 1) / (m : ℝ)

private def cellAt (m : ℕ) (y : ℝ) : ℕ :=
  ⌊(m : ℝ) * Int.fract y⌋₊

private theorem idealOrbit_irrational (lam : ℝ) (hlam : Irrational lam) (k : ℕ) :
    Irrational (idealOrbit lam k) := by
  have hi : Irrational (((2 * k + 3 : ℕ) : ℝ) * lam) :=
    (irrational_natCast_mul_iff).mpr ⟨by omega, hlam⟩
  simpa only [idealOrbit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hi

private theorem cellAt_lt (m : ℕ) (hm : 0 < m) (y : ℝ) : cellAt m y < m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx : 0 ≤ (m : ℝ) * Int.fract y :=
    mul_nonneg hmR.le (Int.fract_nonneg y)
  apply (Nat.floor_lt hx).mpr
  simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one y) hmR

private theorem cellAt_eq_iff (m : ℕ) (hm : 0 < m) (h : ℕ) (y : ℝ) :
    cellAt m y = h ↔ inCell m h y := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx : 0 ≤ (m : ℝ) * Int.fract y :=
    mul_nonneg hmR.le (Int.fract_nonneg y)
  unfold cellAt inCell
  rw [Nat.floor_eq_iff hx, div_le_iff₀ hmR, lt_div_iff₀ hmR]
  simp only [mul_comm]

private theorem cell_remainder
    (m h : ℕ) (hm : 0 < m) (y : ℝ) (hy : Irrational y) (hc : inCell m h y) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ (m : ℝ) * Int.fract y = (h : ℝ) + u := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlo : (h : ℝ) ≤ (m : ℝ) * Int.fract y := by
    simpa only [mul_comm] using (div_le_iff₀ hmR).mp hc.1
  have hhi : (m : ℝ) * Int.fract y < (h : ℝ) + 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hmR).mp hc.2
  have hf : Irrational (Int.fract y) := by
    simpa only [Int.fract] using hy.sub_intCast ⌊y⌋
  have hi : Irrational ((m : ℝ) * Int.fract y) :=
    (irrational_natCast_mul_iff).mpr ⟨Nat.ne_of_gt hm, hf⟩
  have hstrict : (h : ℝ) < (m : ℝ) * Int.fract y :=
    lt_of_le_of_ne hlo (Ne.symm (hi.ne_nat h))
  refine ⟨(m : ℝ) * Int.fract y - (h : ℝ), ?_, ?_, ?_⟩
  · linarith
  · linarith
  · ring

private theorem ceil_cell_fraction
    (n h : ℕ) (hn : 0 < n) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    ⌈((h : ℝ) + u) / (n : ℝ)⌉ = ((h / n : ℕ) : ℤ) + 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : (n : ℝ) * ((h / n : ℕ) : ℝ) + ((h % n : ℕ) : ℝ) = h := by
    exact_mod_cast Nat.div_add_mod h n
  have hr0 : (0 : ℝ) ≤ ((h % n : ℕ) : ℝ) := by positivity
  have hr1 : ((h % n : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt h hn)
  apply Int.ceil_eq_iff.mpr
  constructor
  · simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    apply (lt_div_iff₀ hnR).mpr
    nlinarith
  · simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    apply (div_le_iff₀ hnR).mpr
    nlinarith

private theorem idealDet_fract (a b : ℕ) (y : ℝ) :
    idealDet a b y = idealDet a b (Int.fract y) := by
  have hs (n : ℕ) :
      ⌈(n : ℝ) * y⌉ = ⌈(n : ℝ) * Int.fract y⌉ + (n : ℤ) * ⌊y⌋ := by
    have he : (n : ℝ) * y = (n : ℝ) * Int.fract y +
        (((n : ℤ) * ⌊y⌋ : ℤ) : ℝ) := by
      calc
        (n : ℝ) * y = (n : ℝ) * (Int.fract y + (⌊y⌋ : ℝ)) := by
          rw [Int.fract_add_floor]
        _ = _ := by push_cast; ring
    rw [he, Int.ceil_add_intCast]
  unfold idealDet
  rw [hs a, hs b]
  ring

private theorem idealDet_on_cell
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℕ)
    (y : ℝ) (hy : Irrational y) (hc : inCell (a * b) h y) :
    idealDet a b y = cellValue a b h := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  obtain ⟨u, hu0, hu1, he⟩ := cell_remainder (a * b) h (Nat.mul_pos ha hb) y hy hc
  have heR : (a : ℝ) * (b : ℝ) * Int.fract y = (h : ℝ) + u := by
    simpa only [Nat.cast_mul] using he
  have hea : (a : ℝ) * Int.fract y = ((h : ℝ) + u) / (b : ℝ) := by
    apply (eq_div_iff (ne_of_gt hbR)).mpr
    nlinarith [heR]
  have heb : (b : ℝ) * Int.fract y = ((h : ℝ) + u) / (a : ℝ) := by
    apply (eq_div_iff (ne_of_gt haR)).mpr
    nlinarith [heR]
  have hca : ⌈(a : ℝ) * Int.fract y⌉ = ((h / b : ℕ) : ℤ) + 1 := by
    rw [hea]
    exact ceil_cell_fraction b h hb u hu0 hu1
  have hcb : ⌈(b : ℝ) * Int.fract y⌉ = ((h / a : ℕ) : ℤ) + 1 := by
    rw [heb]
    exact ceil_cell_fraction a h ha u hu0 hu1
  have hda : (a : ℤ) * ((h / a : ℕ) : ℤ) + ((h % a : ℕ) : ℤ) = h := by
    exact_mod_cast Nat.div_add_mod h a
  have hdb : (b : ℤ) * ((h / b : ℕ) : ℤ) + ((h % b : ℕ) : ℤ) = h := by
    exact_mod_cast Nat.div_add_mod h b
  rw [idealDet_fract a b y]
  unfold idealDet cellValue
  rw [hca, hcb]
  nlinarith

open Classical in
private theorem ideal_histogram_partition
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (lam : ℝ) (hlam : Irrational lam) (j : ℤ) (N : ℕ) :
    ((Finset.range N).filter (fun (k : ℕ) => idealDet a b (idealOrbit lam k) = j)).card =
      ∑ h ∈ ((Finset.range (a * b)).filter (fun h => cellValue a b h = j)),
        ((Finset.range N).filter (fun (k : ℕ) => inCell (a * b) h (idealOrbit lam k))).card := by
  classical
  let s := (Finset.range N).filter (fun (k : ℕ) => idealDet a b (idealOrbit lam k) = j)
  let t := (Finset.range (a * b)).filter (fun h => cellValue a b h = j)
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have hdet (k : ℕ) : idealDet a b (idealOrbit lam k) =
      cellValue a b (cellAt (a * b) (idealOrbit lam k)) :=
    idealDet_on_cell a b ha hb _ _ (idealOrbit_irrational lam hlam k)
      ((cellAt_eq_iff (a * b) hm _ _).mp rfl)
  have hmap : (s : Set ℕ).MapsTo (fun (k : ℕ) => cellAt (a * b) (idealOrbit lam k)) t := by
    intro k hk
    have hkj := (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (cellAt_lt (a * b) hm _),
      (hdet k).symm.trans hkj⟩
  calc
    _ = ∑ h ∈ t, (s.filter (fun (k : ℕ) => cellAt (a * b) (idealOrbit lam k) = h)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      have hhj := (Finset.mem_filter.mp hh).2
      apply congrArg Finset.card
      ext k
      simp only [s, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk, _⟩, hkh⟩
        exact ⟨hk, (cellAt_eq_iff (a * b) hm h _).mp hkh⟩
      · rintro ⟨hk, hcell⟩
        have hkh := (cellAt_eq_iff (a * b) hm h _).mpr hcell
        refine ⟨⟨hk, (hdet k).trans ?_⟩, hkh⟩
        rw [hkh]
        exact hhj

open Classical in
private theorem ideal_cell_sampling
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (lam : ℝ) (hlam : Irrational lam) (h : ℕ) (hh : h < a * b) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => inCell (a * b) h (idealOrbit lam k))).card : ℝ) /
        (N : ℝ)) atTop (𝓝 (1 / ((a : ℝ) * (b : ℝ)))) := by
  classical
  have hmR : 0 < (a : ℝ) * (b : ℝ) := mul_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hhR : (h : ℝ) + 1 ≤ (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hh
  have hAlpha : Irrational (2 * lam) := by
    simpa only [Nat.cast_ofNat] using
      (irrational_natCast_mul_iff (n := 2) (x := lam)).mpr ⟨by norm_num, hlam⟩
  have hlo : 0 ≤ (h : ℝ) / ((a : ℝ) * (b : ℝ)) :=
    div_nonneg (Nat.cast_nonneg h) hmR.le
  have hlh : (h : ℝ) / ((a : ℝ) * (b : ℝ)) ≤
      ((h : ℝ) + 1) / ((a : ℝ) * (b : ℝ)) :=
    div_le_div_of_nonneg_right (by linarith) hmR.le
  have hhi : ((h : ℝ) + 1) / ((a : ℝ) * (b : ℝ)) ≤ 1 :=
    (div_le_iff₀ hmR).mpr (by simpa using hhR)
  have he (k : ℕ) : 3 * lam + (k : ℝ) * (2 * lam) = idealOrbit lam k := by
    unfold idealOrbit
    ring
  have hlen : ((h : ℝ) + 1) / ((a : ℝ) * (b : ℝ)) -
      (h : ℝ) / ((a : ℝ) * (b : ℝ)) = 1 / ((a : ℝ) * (b : ℝ)) := by ring
  have hs := D5.S1.Phase.IntervalSampling.irrational_rotation_interval_sampling
    hAlpha (3 * lam) hlo hlh hhi
  simpa only [inCell, Nat.cast_mul, he, hlen] using hs

private theorem ideal_irrational_histogram
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (lam : ℝ) (hlam : Irrational lam) (j : ℤ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) =>
        (b : ℤ) * ⌈(a : ℝ) * ((2 * (k : ℝ) + 3) * lam)⌉ -
          (a : ℤ) * ⌈(b : ℝ) * ((2 * (k : ℝ) + 3) * lam)⌉ = j)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (((max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) : ℤ) : ℝ) /
        ((a : ℝ) * (b : ℝ)))) := by
  classical
  let t := (Finset.range (a * b)).filter (fun h => cellValue a b h = j)
  have hs := tendsto_finsetSum t (fun h hh =>
    ideal_cell_sampling a b ha hb lam hlam h (Finset.mem_range.mp (Finset.mem_filter.mp hh).1))
  have hc : (t.card : ℤ) = max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) :=
    finite_histogram_formula a b ha hb hab j
  have hcR : (t.card : ℝ) =
      ((max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) : ℤ) : ℝ) := by
    exact_mod_cast hc
  have hmass : (∑ _h ∈ t, 1 / ((a : ℝ) * (b : ℝ))) =
      ((max 0 (min (a : ℤ) ((b : ℤ) - j) - max 0 (-j)) : ℤ) : ℝ) /
        ((a : ℝ) * (b : ℝ)) := by
    calc
      _ = (t.card : ℝ) / ((a : ℝ) * (b : ℝ)) := by simp [div_eq_mul_inv]
      _ = _ := by rw [hcR]
  have hcounts (N : ℕ) :
      (∑ h ∈ t,
        (((Finset.range N).filter (fun (k : ℕ) => inCell (a * b) h (idealOrbit lam k))).card : ℝ) /
          (N : ℝ)) =
      (((Finset.range N).filter (fun (k : ℕ) => idealDet a b (idealOrbit lam k) = j)).card : ℝ) /
        (N : ℝ) := by
    have hp := congrArg (fun q : ℕ => (q : ℝ) / (N : ℝ))
      (ideal_histogram_partition a b ha hb lam hlam j N)
    simpa only [t, Nat.cast_sum, Finset.sum_div] using hp.symm
  rw [hmass] at hs
  simp only [hcounts] at hs
  convert hs using 1
  funext N
  congr 2

private theorem ideal_irrational_histogram_support
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (lam : ℝ) (hlam : Irrational lam) (j : ℤ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) =>
        (b : ℤ) * ⌈(a : ℝ) * ((2 * (k : ℝ) + 3) * lam)⌉ -
          (a : ℤ) * ⌈(b : ℝ) * ((2 * (k : ℝ) + 3) * lam)⌉ = j)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (if -(a : ℤ) < j ∧ j < (b : ℤ) then
        ((min (min (a : ℤ) (b : ℤ)) (min ((a : ℤ) + j) ((b : ℤ) - j)) : ℤ) : ℝ) /
          ((a : ℝ) * (b : ℝ)) else 0)) := by
  have hs := ideal_irrational_histogram a b ha hb hab lam hlam j
  by_cases hj : -(a : ℤ) < j ∧ j < (b : ℤ)
  · simpa only [if_pos hj, mass_on_support a b ha hb j hj] using hs
  · simpa only [if_neg hj, mass_off_support a b j hj, Int.cast_zero, zero_div] using hs

open Classical in
private theorem bad_prefix_le_arc
    (α ρ : ℝ) (Bad : ℕ → Prop) (δ : ℝ) (K : ℕ)
    (hK : ∀ k, K ≤ k → Bad k → Int.fract (ρ + (k : ℝ) * α) < δ)
    (N : ℕ) :
    ((Finset.range N).filter Bad).card ≤ K +
      ((Finset.range N).filter fun (k : ℕ) =>
        0 ≤ Int.fract (ρ + (k : ℝ) * α) ∧
          Int.fract (ρ + (k : ℝ) * α) < δ).card := by
  classical
  let arc := (Finset.range N).filter fun (k : ℕ) =>
    0 ≤ Int.fract (ρ + (k : ℝ) * α) ∧ Int.fract (ρ + (k : ℝ) * α) < δ
  have hsub : (Finset.range N).filter Bad ⊆ Finset.range K ∪ arc := by
    intro k hk
    obtain ⟨hkN, hkBad⟩ := Finset.mem_filter.mp hk
    by_cases hkK : k < K
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hkK))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hkN, Int.fract_nonneg _, hK k (Nat.le_of_not_gt hkK) hkBad⟩))
  calc
    _ ≤ (Finset.range K ∪ arc).card := Finset.card_le_card hsub
    _ ≤ (Finset.range K).card + arc.card := Finset.card_union_le _ _
    _ = K + arc.card := by rw [Finset.card_range]

open Classical in
private theorem shrinking_target_bad_density_zero
    {α : ℝ} (hα : Irrational α) (ρ : ℝ) (Bad : ℕ → Prop)
    (hshrink : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ K : ℕ,
      ∀ k, K ≤ k → Bad k → Int.fract (ρ + (k : ℝ) * α) < δ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter Bad).card : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  classical
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun N => lt_of_lt_of_le ha
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · intro ε hε
    let δ : ℝ := min (ε / 4) (1 / 2)
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδle : δ ≤ 1 :=
      (min_le_right (ε / 4) (1 / 2 : ℝ)).trans (by norm_num)
    have hδsmall : δ ≤ ε / 4 := min_le_left _ _
    obtain ⟨K, hK⟩ := hshrink δ hδpos hδle
    have harc : Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun (k : ℕ) =>
          0 ≤ Int.fract (ρ + (k : ℝ) * α) ∧
            Int.fract (ρ + (k : ℝ) * α) < δ).card : ℝ) / (N : ℝ))
        atTop (𝓝 δ) := by
      simpa only [sub_zero] using
        (D5.S1.Phase.IntervalSampling.irrational_rotation_interval_sampling
          hα ρ (le_refl 0) hδpos.le hδle)
    have hprefix : ∀ᶠ N : ℕ in atTop, (K : ℝ) / (N : ℝ) < ε / 4 :=
      (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))).2
        (ε / 4) (by linarith)
    have harc_lt : ∀ᶠ N : ℕ in atTop,
        (((Finset.range N).filter fun (k : ℕ) =>
          0 ≤ Int.fract (ρ + (k : ℝ) * α) ∧
            Int.fract (ρ + (k : ℝ) * α) < δ).card : ℝ) / (N : ℝ) < δ + ε / 4 :=
      (tendsto_order.mp harc).2 (δ + ε / 4) (by linarith)
    filter_upwards [hprefix, harc_lt, eventually_gt_atTop (0 : ℕ)]
      with N hprefixN harcN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hcount : (((Finset.range N).filter Bad).card : ℝ) ≤ (K : ℝ) +
        (((Finset.range N).filter fun (k : ℕ) =>
          0 ≤ Int.fract (ρ + (k : ℝ) * α) ∧
            Int.fract (ρ + (k : ℝ) * α) < δ).card : ℝ) := by
      exact_mod_cast (bad_prefix_le_arc α ρ Bad δ K hK N)
    have hdiv := div_le_div_of_nonneg_right hcount hNpos.le
    rw [add_div] at hdiv
    linarith
open Classical in
private theorem histogram_count_bounds
    (X Y : ℕ → ℤ) (B C : ℕ → Prop)
    (hXY : ∀ k, ¬ (B k ∨ C k) → X k = Y k) (z : ℤ) (N : ℕ) :
    ((Finset.range N).filter fun (k : ℕ) => X k = z).card ≤
        ((Finset.range N).filter fun (k : ℕ) => Y k = z).card +
          (((Finset.range N).filter B).card + ((Finset.range N).filter C).card) ∧
    ((Finset.range N).filter fun (k : ℕ) => Y k = z).card ≤
        ((Finset.range N).filter fun (k : ℕ) => X k = z).card +
          (((Finset.range N).filter B).card + ((Finset.range N).filter C).card) := by
  classical
  let sX := (Finset.range N).filter fun (k : ℕ) => X k = z
  let sY := (Finset.range N).filter fun (k : ℕ) => Y k = z
  let sB := (Finset.range N).filter B
  let sC := (Finset.range N).filter C
  have hsubX : sX ⊆ sY ∪ (sB ∪ sC) := by
    intro k hk
    obtain ⟨hkN, hkX⟩ := Finset.mem_filter.mp hk
    by_cases hb : B k
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hkN, hb⟩))))
    by_cases hc : C k
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hkN, hc⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hkN, (hXY k (not_or.mpr ⟨hb, hc⟩)).symm.trans hkX⟩))
  have hsubY : sY ⊆ sX ∪ (sB ∪ sC) := by
    intro k hk
    obtain ⟨hkN, hkY⟩ := Finset.mem_filter.mp hk
    by_cases hb : B k
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hkN, hb⟩))))
    by_cases hc : C k
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hkN, hc⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hkN, (hXY k (not_or.mpr ⟨hb, hc⟩)).trans hkY⟩))
  have hunion : (sB ∪ sC).card ≤ sB.card + sC.card := Finset.card_union_le _ _
  constructor
  · calc
      sX.card ≤ (sY ∪ (sB ∪ sC)).card := Finset.card_le_card hsubX
      _ ≤ sY.card + (sB ∪ sC).card := Finset.card_union_le _ _
      _ ≤ sY.card + (sB.card + sC.card) := Nat.add_le_add_left hunion _
  · calc
      sY.card ≤ (sX ∪ (sB ∪ sC)).card := Finset.card_le_card hsubY
      _ ≤ sX.card + (sB ∪ sC).card := Finset.card_union_le _ _
      _ ≤ sX.card + (sB.card + sC.card) := Nat.add_le_add_left hunion _

open Classical in
private theorem histogram_difference_le
    (X Y : ℕ → ℤ) (B C : ℕ → Prop)
    (hXY : ∀ k, ¬ (B k ∨ C k) → X k = Y k) (z : ℤ) (N : ℕ) :
    |(((Finset.range N).filter fun (k : ℕ) => X k = z).card : ℝ) / (N : ℝ) -
      (((Finset.range N).filter fun (k : ℕ) => Y k = z).card : ℝ) / (N : ℝ)| ≤
      (((Finset.range N).filter B).card : ℝ) / (N : ℝ) +
        (((Finset.range N).filter C).card : ℝ) / (N : ℝ) := by
  classical
  obtain ⟨hX, hY⟩ := histogram_count_bounds X Y B C hXY z N
  have hX' : (((Finset.range N).filter fun (k : ℕ) => X k = z).card : ℝ) ≤
      (((Finset.range N).filter fun (k : ℕ) => Y k = z).card : ℝ) +
        ((((Finset.range N).filter B).card : ℝ) +
          (((Finset.range N).filter C).card : ℝ)) := by exact_mod_cast hX
  have hY' : (((Finset.range N).filter fun (k : ℕ) => Y k = z).card : ℝ) ≤
      (((Finset.range N).filter fun (k : ℕ) => X k = z).card : ℝ) +
        ((((Finset.range N).filter B).card : ℝ) +
          (((Finset.range N).filter C).card : ℝ)) := by exact_mod_cast hY
  have habs : |(((Finset.range N).filter fun (k : ℕ) => X k = z).card : ℝ) -
      (((Finset.range N).filter fun (k : ℕ) => Y k = z).card : ℝ)| ≤
      (((Finset.range N).filter B).card : ℝ) +
        (((Finset.range N).filter C).card : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [← sub_div, abs_div, show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg hN]
  exact (div_le_div_of_nonneg_right habs hN).trans_eq (add_div _ _ _)

open Classical in
private theorem histogram_transfer
    (X Y : ℕ → ℤ) (B C : ℕ → Prop)
    (hXY : ∀ k, ¬ (B k ∨ C k) → X k = Y k)
    (hB : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter B).card : ℝ) / (N : ℝ)) atTop (𝓝 0))
    (hC : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter C).card : ℝ) / (N : ℝ)) atTop (𝓝 0))
    (z : ℤ) (L : ℝ)
    (hY : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun (k : ℕ) => Y k = z).card : ℝ) / (N : ℝ))
      atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun (k : ℕ) => X k = z).card : ℝ) / (N : ℝ))
      atTop (𝓝 L) := by
  classical
  have hlow := hY.sub (hB.add hC)
  have hupp := hY.add (hB.add hC)
  simp only [zero_add, sub_zero, add_zero] at hlow hupp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp ?_ ?_
  · intro N
    have h := (abs_le.mp (histogram_difference_le X Y B C hXY z N)).1
    linarith
  · intro N
    have h := (abs_le.mp (histogram_difference_le X Y B C hXY z N)).2
    linarith

private theorem scaled_log_irrational (c : ℤ) (hc : c ≠ 0)
    (n : ℕ) (hn : n ≠ 0) : Irrational ((c : ℝ) / ((n : ℝ) * Real.log 2)) := by
  have he : ((c : ℝ) / Real.log 2) / (n : ℝ) =
      (c : ℝ) / ((n : ℝ) * Real.log 2) := by
    rw [div_div, mul_comm (Real.log 2) (n : ℝ)]
  rw [← he]
  exact (log_two_irrational.intCast_div hc).div_natCast hn

theorem positive_gcd_coordinates (p r : ℤ) (hp : 0 < p) (hr : 0 < r) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      p = (Int.gcd p r : ℤ) * a ∧ r = (Int.gcd p r : ℤ) * b := by
  have hdN : 0 < Int.gcd p r := Int.gcd_pos_of_ne_zero_left r (ne_of_gt hp)
  have hd : (0 : ℤ) < Int.gcd p r := by exact_mod_cast hdN
  obtain ⟨a, b, hab, hpa, hrb⟩ := Int.exists_gcd_one hdN
  have ha : 0 < a := by
    by_contra h
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hd.le
    rw [← hpa] at hmul
    omega
  have hb : 0 < b := by
    by_contra h
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hd.le
    rw [← hrb] at hmul
    omega
  refine ⟨a.natAbs, b.natAbs, Int.natAbs_pos.mpr ha.ne', Int.natAbs_pos.mpr hb.ne',
    ?_, ?_, ?_⟩
  · exact hab
  · simpa only [Int.natAbs_of_nonneg ha.le, mul_comm] using hpa
  · simpa only [Int.natAbs_of_nonneg hb.le, mul_comm] using hrb

private theorem ideal_histogram (p r : ℤ) (hp : 0 < p) (hr : 0 < r) (z : ℤ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) =>
        r * ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ -
          p * ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ = z)).card : ℝ) /
        (N : ℝ)) atTop (𝓝 (mass p r z)) := by
  classical
  let d : ℤ := Int.gcd p r
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left r (ne_of_gt hp)
  have hd0 : d ≠ 0 := ne_of_gt hd
  obtain ⟨a, b, ha, hb, hab, hpa, hrb⟩ := positive_gcd_coordinates p r hp hr
  change p = d * (a : ℤ) at hpa
  change r = d * (b : ℤ) at hrb
  have hadiv : p / d = (a : ℤ) := by rw [hpa, Int.mul_ediv_cancel_left _ hd0]
  have hbdiv : r / d = (b : ℤ) := by rw [hrb, Int.mul_ediv_cancel_left _ hd0]
  let lam : ℝ := (d : ℝ) / (4 * Real.log 2)
  have hlam : Irrational lam := scaled_log_irrational d hd0 4 (by norm_num)
  let J : ℕ → ℤ := fun (k : ℕ) => idealDet a b (idealOrbit lam k)
  have harg (c : ℕ) (k : ℕ) :
      ((d * (c : ℤ) : ℤ) : ℝ) * (qAt k : ℝ) / (4 * Real.log 2) =
        (c : ℝ) * ((2 * (k : ℝ) + 3) * lam) := by
    simp only [qAt, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast]
    dsimp [lam]
    ring
  have hdet (k : ℕ) :
      r * ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ -
        p * ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ = d * J k := by
    rw [hpa, hrb, harg a k, harg b k]
    dsimp [J, idealDet, idealOrbit]
    ring
  by_cases hz : d ∣ z
  · have hzd : d * (z / d) = z := by
      simpa only [mul_comm] using Int.ediv_mul_cancel hz
    have he (k : ℕ) :
        r * ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ -
          p * ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ = z ↔ J k = z / d := by
      rw [hdet k]
      constructor
      · intro h
        exact mul_left_cancel₀ hd0 (h.trans hzd.symm)
      · intro h
        rw [h, hzd]
    have hm : mass p r z = if -(a : ℤ) < z / d ∧ z / d < (b : ℤ) then
        ((min (min (a : ℤ) (b : ℤ)) (min ((a : ℤ) + z / d) ((b : ℤ) - z / d)) : ℤ) : ℝ) /
          ((a : ℝ) * (b : ℝ)) else 0 := by
      unfold mass
      change (if _ : d ∣ z then _ else 0) = _
      rw [dif_pos hz]
      dsimp only
      rw [hadiv, hbdiv]
      simp only [Int.cast_min, Int.cast_add, Int.cast_sub, Int.cast_natCast]
      rfl
    have hs := ideal_irrational_histogram_support a b ha hb hab lam hlam (z / d)
    change Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => J k = z / d)).card : ℝ) / (N : ℝ))
      atTop (𝓝 _) at hs
    rw [hm]
    simpa only [he] using hs
  · have hfalse (k : ℕ) : ¬ (r * ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ -
        p * ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ = z) := by
      intro h
      exact hz ⟨J k, h.symm.trans (hdet k)⟩
    have hzero (N : ℕ) : (Finset.range N).filter (fun (k : ℕ) =>
        r * ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ -
          p * ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ = z) = ∅ := by
      ext k
      simp only [Finset.mem_filter, hfalse, and_false, Finset.notMem_empty]
    have hm : mass p r z = 0 := by
      unfold mass
      change (if _ : d ∣ z then _ else 0) = 0
      exact dif_neg hz
    simpa only [hzero, Finset.card_empty, Nat.cast_zero, zero_div, hm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

set_option maxHeartbeats 1200000 in
private theorem ceiling_bad_density (c : ℤ) (hc : c ≠ 0) (T : ℕ → ℕ)
    (hlo : ∀ k : ℕ,
      ((qAt k : ℝ)^2 - 1) * (c : ℝ) / (4 * (qAt k : ℝ) * Real.log 2) +
        1 / (2 * (qAt k : ℝ)) - 1 / (2 * (qAt k : ℝ) * (c : ℝ)) < (T k : ℝ))
    (hup : ∀ k : ℕ,
      (T k : ℤ) ≤ ⌈(c : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter (fun (k : ℕ) =>
      (T k : ℤ) ≠ ⌈(c : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉)).card : ℝ) /
      (N : ℝ)) atTop (𝓝 0) := by
  classical
  let A : ℝ := (c : ℝ) / (4 * Real.log 2) - 1 / 2 + 1 / (2 * (c : ℝ))
  let M : ℝ := |A| + 1
  have hcR : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hL : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  have hα := scaled_log_irrational c hc 2 (by norm_num)
  have hshrink : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ K : ℕ,
      ∀ k, K ≤ k → ((T k : ℤ) ≠ ⌈(c : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉) →
        Int.fract (3 * (c : ℝ) / (4 * Real.log 2) +
          (k : ℝ) * ((c : ℝ) / (2 * Real.log 2))) < δ := by
    intro δ hδ _
    obtain ⟨K, hK⟩ := exists_nat_gt (M / δ)
    refine ⟨K, ?_⟩
    intro k hk hbad
    have hq : (0 : ℝ) < (qAt k : ℝ) := by
      simp only [qAt, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      positivity
    have hKk : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hqk : (k : ℝ) < (qAt k : ℝ) := by
      simp only [qAt, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hM : M < δ * (qAt k : ℝ) := by
      have hlt : M / δ < (qAt k : ℝ) := lt_trans (lt_of_lt_of_le hK hKk) hqk
      simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hlt
    have hAδ : A / (qAt k : ℝ) < δ := by
      apply (div_lt_iff₀ hq).mpr
      have hAM : A < M := lt_of_le_of_lt (le_abs_self A) (by dsimp [M]; linarith)
      linarith
    let x : ℝ := (c : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)
    have hrewrite :
        ((qAt k : ℝ)^2 - 1) * (c : ℝ) / (4 * (qAt k : ℝ) * Real.log 2) +
          1 / (2 * (qAt k : ℝ)) - 1 / (2 * (qAt k : ℝ) * (c : ℝ)) =
        x - A / (qAt k : ℝ) := by
      dsimp [x, A]
      field_simp [hcR, hL, ne_of_gt hq]
      <;> ring
    have hlower : x - A / (qAt k : ℝ) < (T k : ℝ) := by
      rw [← hrewrite]
      exact hlo k
    have hlt : (T k : ℤ) < ⌈x⌉ := by
      have hu := hup k
      change (T k : ℤ) ≤ ⌈x⌉ at hu
      change (T k : ℤ) ≠ ⌈x⌉ at hbad
      omega
    have hTx : ((T k : ℤ) : ℝ) < x := Int.lt_ceil.mp hlt
    have hfloor : (T k : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr hTx.le
    have hfloorR : (T k : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hfloor
    have hfract : Int.fract x < A / (qAt k : ℝ) := by
      rw [Int.fract]
      linarith
    have hphase : 3 * (c : ℝ) / (4 * Real.log 2) +
        (k : ℝ) * ((c : ℝ) / (2 * Real.log 2)) = x := by
      dsimp [x]
      simp only [qAt, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      field_simp [hL]
      <;> ring
    rw [hphase]
    exact hfract.trans hAδ
  have hs := shrinking_target_bad_density_zero hα
    (3 * (c : ℝ) / (4 * Real.log 2))
    (fun k : ℕ => (T k : ℤ) ≠ ⌈(c : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉) hshrink
  convert hs using 1
  funext N
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
  ext k
  simp only [Finset.mem_filter]

private theorem actual_histogram (p r : ℤ) (hp5 : 5 ≤ p) (hr5 : 5 ≤ r)
    (T U : ℕ → ℕ) (hT : ∀ k, bracketSC p (qAt k) (T k))
    (hU : ∀ k, bracketSC r (qAt k) (U k)) (z : ℤ) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter (fun (k : ℕ) =>
      r * (T k : ℤ) - p * (U k : ℤ) = z)).card : ℝ) / (N : ℝ)) atTop
      (𝓝 (mass p r z)) := by
  classical
  apply histogram_transfer
    (fun (k : ℕ) => r * (T k : ℤ) - p * (U k : ℤ))
    (fun (k : ℕ) => r * ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ -
      p * ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉)
    (fun (k : ℕ) => (T k : ℤ) ≠ ⌈(p : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉)
    (fun (k : ℕ) => (U k : ℤ) ≠ ⌈(r : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉)
  · intro k hk
    rcases not_or.mp hk with ⟨hp, hr⟩
    rw [not_not.mp hp, not_not.mp hr]
  · convert ceiling_bad_density p (by omega) T (fun (k : ℕ) => (hT k).2.1)
      (fun (k : ℕ) => (hT k).2.2) using 1
    funext N
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
    ext k
    simp only [Finset.mem_filter]
  · convert ceiling_bad_density r (by omega) U (fun (k : ℕ) => (hU k).2.1)
      (fun (k : ℕ) => (hU k).2.2) using 1
    funext N
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
    ext k
    simp only [Finset.mem_filter]
  · exact ideal_histogram p r (by omega) (by omega) z

private theorem originalSC_unique (p q : ℤ) (T U : ℕ)
    (hT : originalSC p q T) (hU : originalSC p q U) : U = T := by
  rcases hT with ⟨hTmin, hTb, hTa, _hTafter, _hTlate⟩
  rcases hU with ⟨hUmin, hUb, hUa, _hUafter, _hUlate⟩
  rcases lt_trichotomy U T with h | h | h
  · exact False.elim ((not_lt_of_ge hUa) (hTb U hUmin.le h))
  · exact h
  · exact False.elim ((not_lt_of_ge hTa) (hUb T hTmin.le h))

/-- Exact determinant histogram for the actual finite-group thresholds.  The
    sequences chosen below are the unique thresholds of the original count
    crossings at every odd `q = 2*k+3`; the histogram is then the stated
    closed CRT convolution for every integer value. -/
theorem actual_square_displacement_threshold_distribution
    (p r : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) (hr5 : 5 ≤ r) (hro : Odd r) :
    ∃ T U : ℕ → ℕ,
      (∀ k : ℕ, bracketSC p (qAt k) (T k) ∧
        ∀ t : ℕ, originalSC p (qAt k) t → t = T k) ∧
      (∀ k : ℕ, bracketSC r (qAt k) (U k) ∧
        ∀ u : ℕ, originalSC r (qAt k) u → u = U k) ∧
      (∀ z : ℤ, Tendsto (fun N : ℕ =>
        (((Finset.range N).filter (fun (k : ℕ) =>
          r * (T k : ℤ) - p * (U k : ℤ) = z)).card : ℝ) / (N : ℝ)) atTop
        (𝓝 (mass p r z))) := by
  classical
  have hq3 (k : ℕ) : 3 ≤ qAt k := by dsimp [qAt]; omega
  have hqo (k : ℕ) : Odd (qAt k) := by
    refine ⟨(k : ℤ) + 1, ?_⟩
    dsimp [qAt]
    ring
  choose T hT using fun k : ℕ =>
    (actual_square_displacement_log_two_bracket p (qAt k) hp5 hpo (hq3 k) (hqo k)).exists
  choose U hU using fun k : ℕ =>
    (actual_square_displacement_log_two_bracket r (qAt k) hr5 hro (hq3 k) (hqo k)).exists
  refine ⟨T, U, ?_, ?_, ?_⟩
  · intro k
    rcases hT k with ⟨hmin, hbefore, hat, hafter, hlate, hlo, hup⟩
    refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
    intro v hv
    exact originalSC_unique p (qAt k) (T k) v
      ⟨hmin, hbefore, hat, hafter, hlate⟩ hv
  · intro k
    rcases hU k with ⟨hmin, hbefore, hat, hafter, hlate, hlo, hup⟩
    refine ⟨⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩, ?_⟩
    intro v hv
    exact originalSC_unique r (qAt k) (U k) v
      ⟨hmin, hbefore, hat, hafter, hlate⟩ hv
  · intro z
    refine actual_histogram p r hp5 hr5 T U ?_ ?_ z
    · intro k
      rcases hT k with ⟨hmin, hbefore, hat, hafter, hlate, hlo, hup⟩
      exact ⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩
    · intro k
      rcases hU k with ⟨hmin, hbefore, hat, hafter, hlate, hlo, hup⟩
      exact ⟨⟨hmin, hbefore, hat, hafter, hlate⟩, hlo, hup⟩

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
