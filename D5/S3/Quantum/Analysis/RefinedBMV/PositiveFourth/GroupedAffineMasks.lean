/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/GroupedAffineMasks
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Grouped integer mask checks for the mixed affine origins of the four-copy certificate. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedOrigins

/-! The row construction and inner sweep adapt `ThreeSpectrum/GroupedMasks` to
negative affine rates and coefficient lists in the nonnegative degree parameter. -/

open scoped BigOperators
open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

open private affineFactor ratePolynomial_sub from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedOrigins

namespace GroupedAffineMasks

/-- One coefficient list in ascending degree order for a pair of rates.
The V rate is supplied by the column and `uIndex` indexes the U root list. -/
structure Group where
  rateU : AffineRate
  uIndex : ℕ
  coefficients : List ℤ

abbrev Column := AffineRate × List Group

structure Certificate where
  rootsU : List AffineRate
  columns : List Column

def Certificate.rootsV (c : Certificate) : List AffineRate := c.columns.map Prod.fst

def Certificate.terms (c : Certificate) : List (AffineRate × Group) :=
  c.columns.flatMap fun col => col.2.map fun g => (col.1, g)

def Certificate.checkRates (c : Certificate) : Bool :=
  c.columns.all fun col => col.2.all fun g => c.rootsU[g.uIndex]? == some g.rateU

/-- Interpret a coefficient list in the same order as `packSigned`. -/
noncomputable def coefficientPolynomial : List ℤ → ℤ[X]
  | [] => 0
  | a :: as => C a + X * coefficientPolynomial as

private theorem eval_coefficientPolynomial (x : ℤ) (cs : List ℤ) :
    (coefficientPolynomial cs).eval x = DimThree.PackedCheck.packSigned x cs := by
  induction cs with
  | nil => simp [coefficientPolynomial, DimThree.PackedCheck.packSigned]
  | cons a as ih => simp [coefficientPolynomial, DimThree.PackedCheck.packSigned, ih]

abbrev Certificate.Index (c : Certificate) := Fin c.terms.length

noncomputable def Certificate.weight (c : Certificate) (i : c.Index) : ℤ[X] :=
  coefficientPolynomial (c.terms.get i).2.coefficients

def Certificate.rateU (c : Certificate) (i : c.Index) : AffineRate :=
  (c.terms.get i).2.rateU

def Certificate.rateV (c : Certificate) (i : c.Index) : AffineRate :=
  (c.terms.get i).1

/-- Every grouped rate occurs in its corresponding chain. -/
theorem Certificate.rates_mem (c : Certificate) (h : c.checkRates = true) (i : c.Index) :
    c.rateU i ∈ c.rootsU ∧ c.rateV i ∈ c.rootsV := by
  have ht : c.terms.get i ∈ c.columns.flatMap (fun col => col.2.map fun g => (col.1, g)) :=
    List.get_mem c.terms i
  obtain ⟨col, hcol, hgroup⟩ := List.mem_flatMap.mp ht
  obtain ⟨g, hg, heq⟩ := List.mem_map.mp hgroup
  simp only [Certificate.checkRates, List.all_eq_true, beq_iff_eq] at h
  unfold Certificate.rateU Certificate.rateV
  rw [← heq]
  change g.rateU ∈ c.rootsU ∧ col.1 ∈ c.columns.map Prod.fst
  exact ⟨List.mem_of_getElem? (h col hcol g hg), List.mem_map.mpr ⟨col, hcol, rfl⟩⟩

/-- The mixed origin of the grouped weights at the given U and V prefixes. -/
noncomputable def Certificate.origin (c : Certificate) (k l : ℕ) : ℤ[X] :=
  mixedOrigin c.weight c.rateU c.rateV (c.rootsU.take k) (c.rootsV.take l)

private def magnitude (x : ℤ) (a : AffineRate) : ℤ := (a.1 : ℤ) + (a.2 : ℤ) * x

-- The signed rates are negative, so a factor is the root magnitude minus the rate magnitude.
private def factor (a : ℤ) (roots : List ℤ) : ℤ := (roots.map fun b => b - a).prod

private theorem eval_affineFactor_int (x : ℤ) (a : AffineRate) (roots : List AffineRate) :
    (affineFactor a roots).eval x = factor (magnitude x a) (roots.map (magnitude x)) := by
  simp only [affineFactor, Polynomial.eval_list_prod, factor, List.map_map, Function.comp_def,
    ratePolynomial_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  apply congrArg List.prod
  apply List.map_congr_left
  intro b _
  simp only [rateDifference, magnitude]
  ring

private theorem sum_get {T S : Type*} [AddCommMonoid S] (ts : List T) (f : T → S) :
    (∑ i : Fin ts.length, f (ts.get i)) = (ts.map f).sum := by
  rw [← List.sum_ofFn, ← List.ofFn_getElem (xs := ts)]
  simp

private theorem Certificate.eval_origin (c : Certificate) (x : ℤ) (k l : ℕ) :
    (c.origin k l).eval x =
      (c.terms.map fun t => DimThree.PackedCheck.packSigned x t.2.coefficients *
        factor (magnitude x t.2.rateU) ((c.rootsU.map (magnitude x)).take k) *
        factor (magnitude x t.1) ((c.rootsV.map (magnitude x)).take l)).sum := by
  simp only [Certificate.origin, mixedOrigin, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Certificate.weight, eval_coefficientPolynomial, Certificate.rateU, Certificate.rateV,
    eval_affineFactor_int, List.map_take]
  exact sum_get c.terms fun t => DimThree.PackedCheck.packSigned x t.2.coefficients *
    factor (magnitude x t.2.rateU) ((c.rootsU.map (magnitude x)).take k) *
    factor (magnitude x t.1) ((c.rootsV.map (magnitude x)).take l)

private def step (a : ℤ) (tail : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  tail.map fun (r, w) => (r, w * (a - r))

private def sweep (test : ℤ → Bool) : ℕ → List (ℤ × ℤ) → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | n + 1, (a, w) :: tail =>
    test (w + (tail.map Prod.snd).sum) && sweep test n (step a tail)

private def prefixMoment (ws : List (ℤ × ℤ)) (j : ℕ) : ℤ :=
  (ws.map fun (r, w) => w * factor r ((ws.map Prod.fst).take j)).sum

private theorem sweep_sound (test : ℤ → Bool) (n : ℕ) (ws : List (ℤ × ℤ))
    (h : sweep test n ws = true) (j : ℕ) (hj : j < min n ws.length) :
    test (prefixMoment ws j) = true := by
  induction n generalizing ws j with
  | zero => simp at hj
  | succ n ih =>
    cases ws with
    | nil => simp at hj
    | cons p tail =>
      obtain ⟨a, w⟩ := p
      have hh : (test (w + (tail.map Prod.snd).sum) && sweep test n (step a tail)) = true := h
      obtain ⟨hhead, htail⟩ := Bool.and_eq_true_iff.mp hh
      cases j with
      | zero => simpa [prefixMoment, factor] using hhead
      | succ j =>
        have hj' : j < min n (step a tail).length := by
          simp [step] at hj ⊢
          omega
        have heq : prefixMoment ((a, w) :: tail) (j + 1) = prefixMoment (step a tail) j := by
          simp only [prefixMoment, factor, List.map_cons, List.take_succ_cons, List.prod_cons,
            List.sum_cons, sub_self, zero_mul, mul_zero, zero_add, step, List.map_map,
            Function.comp_def]
          congr 1
          apply List.map_congr_left
          rintro ⟨r, v⟩ _
          simp [mul_assoc]
        rw [heq]
        exact ih _ htail _ hj'

private def uFactors (roots : List ℤ) (k : ℕ) : Array ℤ :=
  let precedingRoots := roots.take k
  (roots.mapIdx fun i a => if i < k then 0 else factor a precedingRoots).toArray

private theorem factor_eq_zero {a : ℤ} {roots : List ℤ} (h : a ∈ roots) :
    factor a roots = 0 := by
  induction roots with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [factor]
    · unfold factor at ih ⊢
      simp only [List.map_cons, List.prod_cons, ih h, mul_zero]

private theorem mem_take_of_lookup {roots : List ℤ} {k i : ℕ} {a : ℤ}
    (h : roots[i]? = some a) (hik : i < k) : a ∈ roots.take k := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩

private theorem uFactors_lookup (roots : List ℤ) (k i : ℕ) (a : ℤ)
    (h : roots[i]? = some a) :
    (uFactors roots k)[i]?.getD 0 = factor a (roots.take k) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  simp only [uFactors, List.getElem?_toArray, List.getElem?_mapIdx,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  split
  · symm
    apply factor_eq_zero
    exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩
  · rfl

private def Certificate.packedColumns (c : Certificate) (x : ℤ) :
    List (ℤ × List (ℕ × ℤ)) :=
  c.columns.map fun col => (magnitude x col.1,
    col.2.map fun g => (g.uIndex, DimThree.PackedCheck.packSigned x g.coefficients))

private def packedRow (roots : List ℤ) (columns : List (ℤ × List (ℕ × ℤ))) (k : ℕ) :
    List (ℤ × ℤ) :=
  let factors := uFactors roots k
  columns.map fun col => (col.1, (col.2.map fun (i, w) =>
    if i < k then 0 else w * factors[i]?.getD 0).sum)

private theorem sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β)
    (g : β → ℤ) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

private theorem Certificate.row_eq_origin (c : Certificate) (x : ℤ)
    (h : c.checkRates = true) (k l : ℕ) :
    prefixMoment (packedRow (c.rootsU.map (magnitude x)) (c.packedColumns x) k) l =
      (c.origin k l).eval x := by
  rw [c.eval_origin]
  have hroots : (packedRow (c.rootsU.map (magnitude x)) (c.packedColumns x) k).map Prod.fst =
      c.rootsV.map (magnitude x) := by
    simp [packedRow, Certificate.packedColumns, Certificate.rootsV, List.map_map, Function.comp_def]
  simp only [Certificate.checkRates, List.all_eq_true, beq_iff_eq] at h
  unfold prefixMoment
  rw [hroots]
  simp only [packedRow, Certificate.packedColumns, Certificate.terms, List.map_map,
    Function.comp_def, sum_map_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨v, gs⟩ hcol
  simp only
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  have hrate := h (v, gs) hcol g hg
  have hu : (c.rootsU.map (magnitude x))[g.uIndex]? = some (magnitude x g.rateU) := by
    simp only [List.getElem?_map, hrate, Option.map_some]
  rw [uFactors_lookup _ _ _ _ hu]
  split
  · rename_i hik
    rw [factor_eq_zero (mem_take_of_lookup hu hik), mul_zero]
  · rfl

private def radix (width : ℕ) : ℤ := 2 ^ (width + 1)

private def masked (mask : ℕ) (value : ℤ) : Bool :=
  ((value + (mask : ℤ)).toNat &&& mask) == mask

/-- Check the first `n` V prefixes at U prefix `k`. -/
def Certificate.checkRowPrefix (c : Certificate) (width digits k n : ℕ) : Bool :=
  let x := radix width
  let mask := DimThree.PackedCheck.polynomialMask width digits
  sweep (masked mask) n (packedRow (c.rootsU.map (magnitude x)) (c.packedColumns x) k)

def Certificate.checkRow (c : Certificate) (width digits k : ℕ) : Bool :=
  c.checkRowPrefix width digits k c.rootsV.length

/-- Pack each coefficient list once before checking the rows. -/
def Certificate.checkMasks (c : Certificate) (width digits : ℕ) : Bool :=
  let x := radix width
  let roots := c.rootsU.map (magnitude x)
  let columns := c.packedColumns x
  let mask := DimThree.PackedCheck.polynomialMask width digits
  c.checkRates && (List.range c.rootsU.length).all fun k =>
    sweep (masked mask) c.rootsV.length (packedRow roots columns k)

theorem Certificate.mask_of_rowPrefix (c : Certificate) (width digits : ℕ)
    (hrates : c.checkRates = true) (k n : ℕ) (h : c.checkRowPrefix width digits k n = true)
    (l : ℕ) (hl : l < min n c.rootsV.length) :
    let mask := DimThree.PackedCheck.polynomialMask width digits
    ((c.origin k l).eval (2 ^ (width + 1)) + ↑mask).toNat &&& mask = mask := by
  let x := radix width
  let ws := packedRow (c.rootsU.map (magnitude x)) (c.packedColumns x) k
  have hlength : ws.length = c.rootsV.length := by
    simp [ws, packedRow, Certificate.packedColumns, Certificate.rootsV]
  have hm := sweep_sound (masked (DimThree.PackedCheck.polynomialMask width digits)) n ws h l
    (by simpa only [hlength] using hl)
  change masked _ (prefixMoment
    (packedRow (c.rootsU.map (magnitude x)) (c.packedColumns x) k) l) = true at hm
  rw [c.row_eq_origin x hrates] at hm
  simpa only [masked, beq_iff_eq, x, radix] using hm

/-- Independently checked rows give the packed bit condition for each mixed origin. -/
theorem Certificate.masks_of_rows (c : Certificate) (width digits : ℕ)
    (hrates : c.checkRates = true)
    (hrows : ∀ k < c.rootsU.length, c.checkRow width digits k = true) :
    ∀ k < c.rootsU.length, ∀ l < c.rootsV.length,
    let mask := DimThree.PackedCheck.polynomialMask width digits
    ((c.origin k l).eval (2 ^ (width + 1)) + ↑mask).toNat &&& mask = mask := by
  intro k hk l hl
  exact c.mask_of_rowPrefix width digits hrates k c.rootsV.length (hrows k hk) l (by simpa using hl)

/-- A successful grouped check gives the packed bit condition for each mixed origin. -/
theorem Certificate.masks_of_check (c : Certificate) (width digits : ℕ)
    (h : c.checkMasks width digits = true) :
    ∀ k < c.rootsU.length, ∀ l < c.rootsV.length,
    let mask := DimThree.PackedCheck.polynomialMask width digits
    ((c.origin k l).eval (2 ^ (width + 1)) + ↑mask).toNat &&& mask = mask := by
  simp only [Certificate.checkMasks, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hrates, hrows⟩ := h
  refine c.masks_of_rows width digits hrates ?_
  intro k hk
  simpa only [Certificate.checkRow, Certificate.checkRowPrefix] using
    hrows k (List.mem_range.mpr hk)

/-- The mask and independent size bounds supply the mixed-origin premise of
`nonneg_of_mixed_origin_masks`. -/
theorem Certificate.mixedOrigin_checks_of_rows (c : Certificate) (width digits : ℕ)
    (hrates : c.checkRates = true)
    (hrows : ∀ k < c.rootsU.length, c.checkRow width digits k = true)
    (hbounds : ∀ k < c.rootsU.length, ∀ l < c.rootsV.length,
      let P := c.origin k l
      P.natDegree < digits ∧
        (∀ j, -(2 : ℤ) ^ width ≤ P.coeff j ∧ P.coeff j < (2 : ℤ) ^ width)) :
    ∀ k < c.rootsU.length, ∀ l < c.rootsV.length,
      let P := mixedOrigin c.weight c.rateU c.rateV (c.rootsU.take k) (c.rootsV.take l)
      let mask := DimThree.PackedCheck.polynomialMask width digits
      P.natDegree < digits ∧
        (∀ j, -(2 : ℤ) ^ width ≤ P.coeff j ∧ P.coeff j < (2 : ℤ) ^ width) ∧
        ((P.eval (2 ^ (width + 1)) + ↑mask).toNat &&& mask = mask) := by
  intro k hk l hl
  exact ⟨(hbounds k hk l hl).1, (hbounds k hk l hl).2,
    c.masks_of_rows width digits hrates hrows k hk l hl⟩

end GroupedAffineMasks

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
