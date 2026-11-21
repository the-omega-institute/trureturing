/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/GroupedMasks
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An integer recurrence for checking all mixed derivatives of the cleared discriminant. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetEvaluation
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetMask

/-! The packed mask checker and its connection to the jet of the grouped sparse table. -/

namespace RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks

open Polynomial

/-- Terms with the same four gap exponents, indexed in the X-root list. -/
structure Group where
  x : Nat
  y : Nat
  u : Nat
  v : Nat
  coefficients : List (Nat × Int)
  xIndex : Nat

def Group.rateX (g : Group) : Rate := (3 * (g.x + g.y), g.u + g.v)

def Group.rateY (g : Group) : Rate := (3 * g.y, g.v)

def Group.terms (g : Group) : List Term :=
  g.coefficients.map fun (d, c) => ⟨⟨d, g.x, g.y, g.u, g.v⟩, c⟩

abbrev Column := Rate × List Group

structure Certificate where
  rootsX : List Rate
  columns : List Column

def Certificate.rootsY (c : Certificate) : List Rate := c.columns.map Prod.fst

def Certificate.terms (c : Certificate) : List Term :=
  c.columns.flatMap fun col => col.2.flatMap Group.terms

/-- Check that the indices and column labels encode the rates of the original exponents. -/
def Certificate.checkRates (c : Certificate) : Bool :=
  c.columns.all fun (y, gs) =>
    gs.all fun g => (c.rootsX[g.xIndex]? == some g.rateX) && (g.rateY == y)

def base : Int := 2 ^ 720

private def rate (radix : Int) (a : Rate) : Int := (a.1 : Int) + (a.2 : Int) * (1 + radix)

private def factor (radix : Int) (a : Rate) (rs : List Rate) : Int :=
  (rs.map fun b => rate radix a - rate radix b).prod

private def jetInt (radix : Int) (ts : List Term) (xs ys : List Rate) : Int :=
  (ts.map fun t => t.coefficient * (1 + radix)^t.exponents.p *
    factor radix t.rateX xs * factor radix t.rateY ys).sum

private theorem jet_eval_int (radix : Int) (ts : List Term) (xs ys : List Rate) :
    (jet ts xs ys).eval radix = jetInt radix ts xs ys := by
  have hRate (a : Rate) : (Rate.shifted a).eval radix = rate radix a := by
    simp [Rate.shifted, rate, Polynomial.eval_add, Polynomial.eval_mul]
    ring
  have h (a : Rate) (rs : List Rate) :
      (rateFactor a rs).eval radix = factor radix a rs := by
    simp [factor, rateFactor, Polynomial.eval_list_prod, List.map_map, Function.comp_def,
      Polynomial.eval_sub, hRate]
  induction ts with
  | nil => simp [jet, jetInt]
  | cons t ts ih =>
    simp only [jet, jetInt, List.map_cons, List.sum_cons, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_X, h] at ih ⊢
    rw [ih]

private def masked (value : Int) : Bool :=
  let mask := DimThree.PackedCheck.polynomialMask 719 137
  ((value + (mask : Int)).toNat &&& mask) == mask

private def step (radix : Int) (a : Rate) (tail : List (Rate × Int)) : List (Rate × Int) :=
  tail.map fun (r, v) => (r, v * (rate radix r - rate radix a))

private def sweep (radix : Int) (test : Int → Bool) : Nat → List (Rate × Int) → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | n + 1, (a, w) :: tail =>
    test (w + (tail.map Prod.snd).sum) && sweep radix test n (step radix a tail)

private def prefixMoment (radix : Int) (ws : List (Rate × Int)) (j : Nat) : Int :=
  (ws.map fun (r, v) => v * factor radix r ((ws.map Prod.fst).take j)).sum

private theorem sweep_sound (radix : Int) (test : Int → Bool) (n : Nat) (ws : List (Rate × Int))
    (h : sweep radix test n ws = true) (j : Nat) (hj : j < min n ws.length) :
    test (prefixMoment radix ws j) = true := by
  induction n generalizing ws j with
  | zero => simp at hj
  | succ n ih =>
    cases ws with
    | nil => simp at hj
    | cons p tail =>
      obtain ⟨a, w⟩ := p
      have hh : (test (w + (tail.map Prod.snd).sum) && sweep radix test n (step radix a tail)) = true := h
      simp only [Bool.and_eq_true] at hh
      obtain ⟨hhead, htail⟩ := hh
      cases j with
      | zero => simpa [prefixMoment, factor] using hhead
      | succ j =>
        have hj' : j < min n (step radix a tail).length := by
          simp [step] at hj ⊢
          omega
        have heq : prefixMoment radix ((a, w) :: tail) (j+1) = prefixMoment radix (step radix a tail) j := by
          simp only [prefixMoment, factor, List.map_cons, List.take_succ_cons, List.prod_cons,
            List.sum_cons, sub_self, zero_mul, mul_zero, zero_add, step, List.map_map,
            Function.comp_def]
          congr 1
          apply List.map_congr_left
          rintro ⟨r, v⟩ _
          simp [mul_assoc]
        rw [heq]
        exact ih _ htail _ hj'

private def xFactors (radix : Int) (xs : List Rate) (k : Nat) : Array Int :=
  let roots := xs.take k
  (xs.mapIdx fun i a =>
    if i < k then 0 else factor radix a roots).toArray

private theorem factor_eq_zero (radix : Int) {a : Rate} {rs : List Rate} (h : a ∈ rs) :
    factor radix a rs = 0 := by
  induction rs with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [factor]
    · unfold factor at ih ⊢
      simp only [List.map_cons, List.prod_cons, ih h, mul_zero]

private theorem xFactors_lookup (radix : Int) (xs : List Rate) (k i : Nat) (a : Rate)
    (h : xs[i]? = some a) :
    (xFactors radix xs k)[i]?.getD 0 = factor radix a (xs.take k) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  simp only [xFactors, List.getElem?_toArray, List.getElem?_mapIdx,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  split
  · symm
    apply factor_eq_zero
    exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩
  · rfl

private def Group.weight (g : Group) (radix : Int) : Int :=
  (g.coefficients.map fun (d, c) => c * (1 + radix)^d).sum

private def Certificate.row (c : Certificate) (radix : Int) (k : Nat) : List (Rate × Int) :=
  let factors := xFactors radix c.rootsX k
  c.columns.map fun (y, gs) =>
    (y, (gs.map fun g =>
      if g.xIndex < k then 0 else g.weight radix * factors[g.xIndex]?.getD 0).sum)

private theorem sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Int) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

private theorem Certificate.row_eq_jet (c : Certificate) (radix : Int) (h : c.checkRates = true) (k j : Nat) :
    prefixMoment radix (c.row radix k) j = (jet c.terms (c.rootsX.take k) (c.rootsY.take j)).eval radix := by
  rw [jet_eval_int]
  have hy : (c.row radix k).map Prod.fst = c.rootsY := by simp [Certificate.row, Certificate.rootsY]
  have hRates := h
  simp only [Certificate.checkRates, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hRates
  unfold prefixMoment
  rw [hy]
  simp only [Certificate.row, jetInt, Certificate.terms, List.map_map, Function.comp_def,
    sum_map_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro col hc
  rcases col with ⟨y, gs⟩
  simp only
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  obtain ⟨hx, hy⟩ := hRates _ hc g hg
  have hWeight :
      (if g.xIndex < k then 0 else g.weight radix * (xFactors radix c.rootsX k)[g.xIndex]?.getD 0) =
      g.weight radix * factor radix g.rateX (c.rootsX.take k) := by
    rw [xFactors_lookup radix _ _ _ _ hx]
    split
    · obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hx
      rw [← heq, factor_eq_zero radix (List.mem_take_iff_getElem.mpr ⟨g.xIndex, by omega, rfl⟩),
        mul_zero]
    · rfl
  rw [hWeight]
  simp only [Group.weight, ← List.sum_map_mul_right, Group.terms, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨d, a⟩ _
  change a * (1 + radix)^d * factor radix g.rateX (c.rootsX.take k) * factor radix y (c.rootsY.take j) =
    a * (1 + radix)^d * factor radix g.rateX (c.rootsX.take k) * factor radix g.rateY (c.rootsY.take j)
  rw [hy]

/-- Check the first n Y-prefixes of row k. -/
def Certificate.checkRowPrefix (c : Certificate) (k n : Nat) : Bool :=
  sweep base masked n (c.row base k)

def Certificate.checkRow (c : Certificate) (k : Nat) : Bool :=
  c.checkRowPrefix k c.rootsY.length

def Certificate.checkMasks (c : Certificate) : Bool :=
  c.checkRates && (List.range c.rootsX.length).all c.checkRow

theorem Certificate.mask_of_rowPrefix (c : Certificate) (hrates : c.checkRates = true)
    (k n : Nat) (h : c.checkRowPrefix k n = true) (l : Nat) (hl : l < min n c.rootsY.length) :
    let value := (jet c.terms (c.rootsX.take k) (c.rootsY.take l)).eval (2 ^ 720)
    let mask := DimThree.PackedCheck.polynomialMask 719 137
    (value + ↑mask).toNat &&& mask = mask := by
  have hlength : (c.row base k).length = c.rootsY.length := by
    simp [Certificate.row, Certificate.rootsY]
  have hm := sweep_sound base masked n (c.row base k) h l (by simpa only [hlength] using hl)
  rw [c.row_eq_jet base hrates] at hm
  simpa only [masked, beq_iff_eq, base] using hm

/-- Separate row proofs can be composed without evaluating all rows in one kernel reduction. -/
theorem Certificate.masks_of_rows (c : Certificate) (hrates : c.checkRates = true)
    (hrows : ∀ k < c.rootsX.length, c.checkRow k = true) :
    ∀ k < c.rootsX.length, ∀ l < c.rootsY.length,
    let value := (jet c.terms (c.rootsX.take k) (c.rootsY.take l)).eval (2 ^ 720)
    let mask := DimThree.PackedCheck.polynomialMask 719 137
    (value + ↑mask).toNat &&& mask = mask := by
  intro k hk l hl
  exact c.mask_of_rowPrefix hrates k c.rootsY.length (hrows k hk) l (by simpa using hl)

theorem Certificate.masks_of_check (c : Certificate) (h : c.checkMasks = true) :
    ∀ k < c.rootsX.length, ∀ l < c.rootsY.length,
    let value := (jet c.terms (c.rootsX.take k) (c.rootsY.take l)).eval (2 ^ 720)
    let mask := DimThree.PackedCheck.polynomialMask 719 137
    (value + ↑mask).toNat &&& mask = mask := by
  simp only [Certificate.checkMasks, Bool.and_eq_true] at h
  obtain ⟨hrates, hrows⟩ := h
  exact c.masks_of_rows hrates fun k hk => List.all_eq_true.mp hrows k (List.mem_range.mpr hk)

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
