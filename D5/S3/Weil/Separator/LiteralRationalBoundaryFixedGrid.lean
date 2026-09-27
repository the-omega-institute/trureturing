/- GID: D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid
   mirror-E: none(waiver:fixed-grid-rational-boundary-enclosure)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified; instance=D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid.fixedGridSemanticCertified
   digest: A checked fixed rational grid encloses both components and their completed-square norm. -/

import D5.S3.Weil.Separator.LiteralRationalBoundaryGrid
import D5.S3.Weil.TestFunctions.RationalCutoffApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGrid

open D5.S3.Weil.Separator.LiteralRationalBoundaryGrid
open Filter Topology Set MeasureTheory Polynomial
open scoped BigOperators ContDiff
open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation

set_option quotPrecheck false
set_option maxRecDepth 4096

private abbrev derivBound (p : Rat[X]) (B : Rat) :=
  p.sum fun n a => |a| * (n : Rat) * B ^ (n - 1)
private abbrev valueBound (p : Rat[X]) (B : Rat) :=
  p.sum fun n a => |a| * B ^ n
private abbrev evenEval (p : Rat[X]) (c : Rat) :=
  (p.eval c + p.eval (-c)) / 2
private abbrev polyBox (p : Rat[X]) (B eta c : Rat) :=
  (evenEval p c - derivBound p B * eta / 2,
   evenEval p c + derivBound p B * eta / 2)
private abbrev mulBox (a b : Rat × Rat) :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
   max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))
private abbrev sqBox (a : Rat × Rat) :=
  (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
   max (a.1 ^ 2) (a.2 ^ 2))
private abbrev cellInputs (w a b : Rat × Rat) (i : Fin 3) :=
  if i = 0 then w else if i = 1 then a else b
private abbrev cellExpr (w a b : Rat × Rat) :=
  let ew : Expr 3 := .input 0 w.1 w.2
  let ea : Expr 3 := .input 1 a.1 a.2
  let eb : Expr 3 := .input 2 b.1 b.2
  let ab := mulBox a b
  let wab := mulBox w ab
  Expr.mul wab.1 wab.2 ew (.mul ab.1 ab.2 ea eb)
private abbrev finalInputs (a b : Rat × Rat) (i : Fin 2) :=
  if i = 0 then a else b
private abbrev finalExpr (a b : Rat × Rat) :=
  let sa := sqBox a
  let sb := sqBox b
  let sum := (sa.1 + sb.1, sa.2 + sb.2)
  let out := (2 * sum.1, 2 * sum.2)
  let ea : Expr 2 := .input 0 a.1 a.2
  let eb : Expr 2 := .input 1 b.1 b.2
  let esa : Expr 2 := .square sa.1 sa.2 ea
  let esb : Expr 2 := .square sb.1 sb.2 eb
  let esum : Expr 2 := .add sum.1 sum.2 esa esb
  Expr.mul out.1 out.2 (.const 2 2 2) esum
local notation "GridNode" =>
  (Nat × Rat × Rat) × ((Nat × Rat × Rat) × (Nat × Rat × Rat))
local notation "GridCell" =>
  ((Fin 3 → Rat × Rat) × Expr 3) × ((Fin 3 → Rat × Rat) × Expr 3)
local notation "GridPayload" =>
  Array GridNode × Array GridCell × (Rat × Rat) × (Rat × Rat) ×
    (Rat × Rat) × Expr 2

set_option maxHeartbeats 2000000 in
-- The fixed-grid enclosure combines interval checking with interval integration.
/-- Every fixed literal-family grid is checker-valid and encloses the real,
imaginary, and completed-square half-line boundary components. -/
theorem fixedGridSemanticCertified (R : Nat) (hR : 0 < R)
    (p q : Rat[X]) (k s : Nat) :
    let N : Nat := 2 ^ k
    let Br : Rat := 2 * R
    let eta : Rat := Br / N
    let raw := boundaryGrid R p q k s
    let cellSize : raw.2.size = N := Array.size_ofFn
    let Jp :=
      (eta * (∑ i : Fin N,
        (bounds (raw.2[i.val]'(i.isLt.trans_eq cellSize.symm)).1.2).1),
       eta * (∑ i : Fin N,
        (bounds (raw.2[i.val]'(i.isLt.trans_eq cellSize.symm)).1.2).2))
    let Jq :=
      (eta * (∑ i : Fin N,
        (bounds (raw.2[i.val]'(i.isLt.trans_eq cellSize.symm)).2.2).1),
       eta * (∑ i : Fin N,
        (bounds (raw.2[i.val]'(i.isLt.trans_eq cellSize.symm)).2.2).2))
    let sf := finalExpr Jp Jq
    let gr := (raw.1, raw.2, Jp, Jq, bounds sf, sf)
    let B : Real := 2 * R
    let H := fun x : Real =>
      ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
        rationalEvenPolynomial p q x
    let z := ∫ x in (0 : Real)..B,
      (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)
    let delta : Rat := (1 / 2) ^ s
    let E : Rat := (boundaryExpCertified_v1 (R : Rat) 0).val.2.2
    let T : Rat := E + 3
    let Ap : Rat := valueBound p Br + Br * derivBound p Br / 2
    let Aq : Rat := valueBound q Br + Br * derivBound q Br / 2
    let Ip : Rat := 2 * Br * T * Ap
    let Iq : Rat := 2 * Br * T * Aq
    let Kmp : Rat := Br * (2 * T * Br * derivBound p Br + (T + 2 * E) * Ap)
    let Kmq : Rat := Br * (2 * T * Br * derivBound q Br + (T + 2 * E) * Aq)
    let Ksp : Rat := Br * Ap * (T + 8)
    let Ksq : Rat := Br * Aq * (T + 8)
    let Cmesh : Rat := 4 * (Ip * Kmp + Iq * Kmq)
    let Cscalar : Rat := 4 * (Ip * Ksp + Iq * Ksq)
    let valid : GridPayload → Bool := fun g =>
      g.2.1.all (fun ce => check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) &&
      check (finalInputs g.2.2.1 g.2.2.2.1) g.2.2.2.2.2 &&
      decide (g.2.2.1.1 <= g.2.2.1.2) &&
      decide (g.2.2.2.1.1 <= g.2.2.2.1.2) &&
      decide (0 <= g.2.2.2.2.1.1) &&
      decide (g.2.2.2.2.1.1 <= g.2.2.2.2.1.2)
    (gr.2.1.all fun ce => check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) = true ∧
    check (finalInputs gr.2.2.1 gr.2.2.2.1) gr.2.2.2.2.2 = true ∧
    gr.2.2.1.1 <= gr.2.2.1.2 ∧ gr.2.2.2.1.1 <= gr.2.2.2.1.2 ∧
    ((gr.2.2.1.1 : Real) <= z.re ∧ z.re <= (gr.2.2.1.2 : Real)) ∧
    ((gr.2.2.2.1.1 : Real) <= z.im ∧ z.im <= (gr.2.2.2.1.2 : Real)) ∧
    ((gr.2.2.2.2.1.1 : Real) <= 2 * Complex.normSq z ∧
      2 * Complex.normSq z <= (gr.2.2.2.2.1.2 : Real)) ∧
    valid gr = true := by
    intro N Br eta raw cellSize Jp Jq sf gr B H z delta E T Ap Aq Ip Iq
      Kmp Kmq Ksp Ksq Cmesh Cscalar valid
    have poly_est (r : Rat[X]) (Br : Rat) (hBr : 0 <= Br) :
        (∀ x : Real, |x| <= (Br : Real) ->
          |aeval x r| <= (valueBound r Br : Real)) ∧
        (∀ x c : Real, |x| <= (Br : Real) -> |c| <= (Br : Real) ->
          |aeval x r - aeval c r| <= (derivBound r Br : Real) * |x - c|) := by
      as_aux_lemma =>
      have heval (x : Real) : aeval x r =
          ∑ n ∈ r.support, (r.coeff n : Real) * x ^ n := by
        simp [aeval_def, eval₂_eq_sum, sum_def]
      constructor
      · intro x hx
        rw [heval]
        calc
          _ <= ∑ n ∈ r.support, |(r.coeff n : Real) * x ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ n ∈ r.support, |(r.coeff n : Real)| * (Br : Real) ^ n := by
            apply Finset.sum_le_sum
            intro n hn
            rw [abs_mul, abs_pow]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg _) hx n) (abs_nonneg _)
          _ = (valueBound r Br : Real) := by
            simp only [sum_def, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow]
      · intro x c hx hc
        rw [heval, heval, <- Finset.sum_sub_distrib]
        calc
          _ <= ∑ n ∈ r.support,
              |(r.coeff n : Real) * x ^ n - (r.coeff n : Real) * c ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ n ∈ r.support,
              |(r.coeff n : Real)| * (|x - c| * n * (Br : Real) ^ (n - 1)) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [<- mul_sub, abs_mul]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply (abs_pow_sub_pow_le x c n).trans
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
            exact pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _))
              (max_le hx hc) _
          _ = (derivBound r Br : Real) * |x - c| := by
            simp only [sum_def, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs,
              Rat.cast_natCast, Rat.cast_pow, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro n hn
            ring
    have mul_ok (a b : Rat × Rat) :
        (mulBox a b).1 <= (mulBox a b).2 ∧
        (mulBox a b).1 <= a.1 * b.1 ∧ (mulBox a b).1 <= a.1 * b.2 ∧
        (mulBox a b).1 <= a.2 * b.1 ∧ (mulBox a b).1 <= a.2 * b.2 ∧
        a.1 * b.1 <= (mulBox a b).2 ∧ a.1 * b.2 <= (mulBox a b).2 ∧
        a.2 * b.1 <= (mulBox a b).2 ∧ a.2 * b.2 <= (mulBox a b).2 := by
      dsimp
      constructor
      · exact (min_le_left _ _ |>.trans (min_le_left _ _)).trans
          ((le_max_left _ _).trans (le_max_left _ _))
      · simp only [min_le_iff, le_max_iff, le_refl, true_or, or_true, and_self]
    have expr_accepts (w a b : Rat × Rat)
        (hw : w.1 <= w.2) (ha : a.1 <= a.2) (hb : b.1 <= b.2) :
        check (cellInputs w a b) (cellExpr w a b) = true := by
      as_aux_lemma =>
      have ei0 : check (cellInputs w a b) (.input (0 : Fin 3) w.1 w.2) = true := by
        simp [cellInputs, check, hw]
      have ei1 : check (cellInputs w a b) (.input (1 : Fin 3) a.1 a.2) = true := by
        simp [cellInputs, check, ha]
      have ei2 : check (cellInputs w a b) (.input (2 : Fin 3) b.1 b.2) = true := by
        simp [cellInputs, check, hb]
      have inner : check (cellInputs w a b)
          (.mul (mulBox a b).1 (mulBox a b).2
            (.input 1 a.1 a.2) (.input 2 b.1 b.2)) = true := by
        rw [check, ei1, ei2, Bool.true_and, Bool.true_and, decide_eq_true_eq]
        exact mul_ok a b
      change check (cellInputs w a b) (.mul (mulBox w (mulBox a b)).1
        (mulBox w (mulBox a b)).2 (.input 0 w.1 w.2)
        (.mul (mulBox a b).1 (mulBox a b).2
          (.input 1 a.1 a.2) (.input 2 b.1 b.2))) = true
      rw [check, ei0, inner, Bool.true_and, Bool.true_and, decide_eq_true_eq]
      exact mul_ok w (mulBox a b)
    have sq_ok (a : Rat × Rat) (ha : a.1 <= a.2) :
        (sqBox a).1 <= (sqBox a).2 ∧
        ((sqBox a).1 <= 0 ∨ (0 <= a.1 ∧ (sqBox a).1 <= a.1 ^ 2) ∨
          (a.2 <= 0 ∧ (sqBox a).1 <= a.2 ^ 2)) ∧
        a.1 ^ 2 <= (sqBox a).2 ∧ a.2 ^ 2 <= (sqBox a).2 := by
      dsimp
      split_ifs with h0 h1
      · exact ⟨le_max_left _ _, Or.inr (Or.inl ⟨h0, le_rfl⟩),
          le_max_left _ _, le_max_right _ _⟩
      · exact ⟨le_max_right _ _, Or.inr (Or.inr ⟨h1, le_rfl⟩),
          le_max_left _ _, le_max_right _ _⟩
      · exact ⟨(sq_nonneg _).trans (le_max_left _ _), Or.inl le_rfl,
          le_max_left _ _, le_max_right _ _⟩
    have final_accepts (a b : Rat × Rat) (ha : a.1 <= a.2) (hb : b.1 <= b.2) :
        check (finalInputs a b) (finalExpr a b) = true := by
      have eia : check (finalInputs a b) (.input (0 : Fin 2) a.1 a.2) = true := by
        simp [finalInputs, check, ha]
      have eib : check (finalInputs a b) (.input (1 : Fin 2) b.1 b.2) = true := by
        simp [finalInputs, check, hb]
      have esa : check (finalInputs a b)
          (.square (sqBox a).1 (sqBox a).2 (.input 0 a.1 a.2)) = true := by
        rw [check, eia, Bool.true_and, decide_eq_true_eq]
        exact sq_ok a ha
      have esb : check (finalInputs a b)
          (.square (sqBox b).1 (sqBox b).2 (.input 1 b.1 b.2)) = true := by
        rw [check, eib, Bool.true_and, decide_eq_true_eq]
        exact sq_ok b hb
      let sumBox := ((sqBox a).1 + (sqBox b).1, (sqBox a).2 + (sqBox b).2)
      let outBox := (2 * sumBox.1, 2 * sumBox.2)
      have esum : check (finalInputs a b)
          (.add sumBox.1 sumBox.2
            (.square (sqBox a).1 (sqBox a).2 (.input 0 a.1 a.2))
            (.square (sqBox b).1 (sqBox b).2 (.input 1 b.1 b.2))) = true := by
        rw [check, esa, esb, Bool.true_and, Bool.true_and, decide_eq_true_eq]
        exact ⟨add_le_add (sq_ok a ha).1 (sq_ok b hb).1, le_rfl, le_rfl⟩
      have ec : check (finalInputs a b) (.const 2 2 2) = true := by
        norm_num [check]
      change check (finalInputs a b) (.mul outBox.1 outBox.2 (.const 2 2 2)
        (.add sumBox.1 sumBox.2
          (.square (sqBox a).1 (sqBox a).2 (.input 0 a.1 a.2))
          (.square (sqBox b).1 (sqBox b).2 (.input 1 b.1 b.2)))) = true
      rw [check, ec, esum, Bool.true_and, Bool.true_and, decide_eq_true_eq]
      have hsum : sumBox.1 <= sumBox.2 :=
        add_le_add (sq_ok a ha).1 (sq_ok b hb).1
      have htwo : 2 * sumBox.1 <= 2 * sumBox.2 :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      simpa only [bounds, outBox] using
        ⟨htwo, le_rfl, htwo, le_rfl, htwo, htwo, le_rfl, htwo, le_rfl⟩
    let eta : Rat := Br / N
    let xq : Nat -> Rat := fun i => i * eta
    let t : Nat -> Rat := fun i => 2 - xq i / R
    let nodeAt : Nat -> GridNode := fun i => gr.1[i]!
    let cp : Nat -> Rat × Rat := fun i => (nodeAt i).1.2
    let ep : Nat -> Rat × Rat := fun i => (nodeAt i).2.1.2
    let em : Nat -> Rat × Rat := fun i => (nodeAt i).2.2.2
    let center : Nat -> Rat := fun i => (xq i + xq (i + 1)) / 2
    let abox : Nat -> Rat × Rat := fun i => ((cp (i + 1)).1, (cp i).2)
    let wbox : Nat -> Rat × Rat := fun i =>
      ((ep i).1 + (em (i + 1)).1, (ep (i + 1)).2 + (em i).2)
    let box : (r : Rat[X]) -> Nat -> Fin 3 -> Rat × Rat := fun r i =>
      cellInputs (wbox i) (abox i) (polyBox r Br eta (center i))
    let ex : (r : Rat[X]) -> Nat -> Expr 3 := fun r i =>
      cellExpr (wbox i) (abox i) (polyBox r Br eta (center i))
    let fr : Rat[X] -> Real -> Real := fun r x =>
      (Real.exp (x / 2) + Real.exp (-x / 2)) *
        Real.smoothTransition (2 - |x| / (R : Real)) *
        ((aeval x r + aeval (-x) r) / 2)
    have hRr : (0 : Real) < R := Nat.cast_pos.mpr hR
    have hRq : (0 : Rat) < R := Nat.cast_pos.mpr hR
    have hB : 0 < Br := by dsimp [Br]; positivity
    have hNnat : 0 < N := by dsimp [N]; positivity
    have hN : (0 : Rat) < N := Nat.cast_pos.mpr hNnat
    have hN1 : (1 : Rat) <= N := by exact_mod_cast hNnat
    have heta : 0 < eta := div_pos hB hN
    have hetaB : eta <= Br := by dsimp [eta]; exact div_le_self hB.le hN1
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hdelta1 : delta <= 1 := by
      dsimp [delta]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hpoint (i : Nat) (hi : i <= N) : 0 <= xq i ∧ xq i <= Br := by
      have hin : (i : Rat) <= N := by exact_mod_cast hi
      dsimp [xq]
      constructor
      · positivity
      · calc
          (i : Rat) * eta <= N * eta := mul_le_mul_of_nonneg_right hin heta.le
          _ = Br := by dsimp [eta]; field_simp
    have hstep (i : Nat) : xq (i + 1) - xq i = eta := by
      dsimp [xq]
      push_cast
      ring
    have hx0 : xq 0 = 0 := by simp [xq]
    have hxN : xq N = Br := by dsimp [xq, eta]; field_simp
    have ht0 : t 0 = 2 := by simp [t, hx0]
    have htN : t N = 0 := by
      dsimp [t]
      rw [hxN]
      dsimp [Br]
      field_simp
      ring
    have hnode (i : Nat) (hi : i <= N) : gr.1[i]! =
        ((cutoffCertified (t i) s).val,
         (boundaryExpCertified_v1 (xq i / 2) s).val,
         (boundaryExpCertified_v1 (-xq i / 2) s).val) := by
      change (Array.ofFn (fun (j : Fin (N + 1)) =>
        ((cutoffCertified (t j) s).val,
         (boundaryExpCertified_v1 (xq j / 2) s).val,
         (boundaryExpCertified_v1 (-xq j / 2) s).val)))[i]! = _
      rw [getElem!_pos (h := by simpa using Nat.lt_succ_of_le hi), Array.getElem_ofFn]
    have hcpNode (i : Nat) (hi : i <= N) :
        cp i = (cutoffCertified (t i) s).val.2 := by
      simpa only [cp, nodeAt] using congrArg (fun o : GridNode => o.1.2) (hnode i hi)
    have hepNode (i : Nat) (hi : i <= N) :
        ep i = (boundaryExpCertified_v1 (xq i / 2) s).val.2 := by
      simpa only [ep, nodeAt] using congrArg (fun o : GridNode => o.2.1.2) (hnode i hi)
    have hemNode (i : Nat) (hi : i <= N) :
        em i = (boundaryExpCertified_v1 (-xq i / 2) s).val.2 := by
      simpa only [em, nodeAt] using congrArg (fun o : GridNode => o.2.2.2) (hnode i hi)
    have cp0 : cp 0 = (1, 1) := by
      rw [hcpNode 0 (Nat.zero_le N)]
      have hh := (cutoffCertified (t 0) s).property.2.2.2.2.2.1
        (by rw [ht0]; norm_num)
      exact congrArg (fun o : Nat × (Rat × Rat) => o.2) hh
    have cpN : cp N = (0, 0) := by
      rw [hcpNode N le_rfl]
      have hh := (cutoffCertified (t N) s).property.2.2.2.2.1 (by rw [htN])
      exact congrArg (fun o : Nat × (Rat × Rat) => o.2) hh
    have hcp (i : Nat) (hi : i <= N) :
        (cp i).1 <= (cp i).2 ∧
        ((cp i).1 : Real) <= Real.smoothTransition (t i : Real) ∧
        Real.smoothTransition (t i : Real) <= ((cp i).2 : Real) ∧
        (cp i).2 - (cp i).1 <= delta ∧
        |(cp i).1| <= 2 ∧ |(cp i).2| <= 2 := by
      rw [hcpNode i hi]
      have hh := (cutoffCertified (t i) s).property
      have hl : (((cutoffCertified (t i) s).val.2.1 : Rat) : Real) <= 1 :=
        hh.2.1.trans (Real.smoothTransition.le_one _)
      have hu : (0 : Real) <= (((cutoffCertified (t i) s).val.2.2 : Rat) : Real) :=
        (Real.smoothTransition.nonneg _).trans hh.2.2.1
      have hlq : (cutoffCertified (t i) s).val.2.1 <= 1 := by exact_mod_cast hl
      have huq : 0 <= (cutoffCertified (t i) s).val.2.2 := by exact_mod_cast hu
      have hw : (cutoffCertified (t i) s).val.2.2 -
          (cutoffCertified (t i) s).val.2.1 <= delta := hh.2.2.2.1
      refine ⟨hh.1, hh.2.1, hh.2.2.1, hw, ?_, ?_⟩ <;>
        rw [abs_le] <;> constructor <;> linarith
    have hscalar (u : Rat) :
        let a := (boundaryExpCertified_v1 u s).val.2
        a.1 <= a.2 ∧ ((a.1 : Real) <= Real.exp (u : Real) ∧
        Real.exp (u : Real) <= (a.2 : Real)) ∧ a.2 - a.1 <= delta := by
      dsimp
      have hh := (boundaryExpCertified_v1 u s).property
      exact ⟨hh.2.2.1, ⟨hh.2.2.2.1, hh.2.2.2.2.1⟩,
        hh.2.2.2.2.2.1⟩
    have hd (r : Rat[X]) : 0 <= derivBound r Br := by
      unfold derivBound Polynomial.sum
      apply Finset.sum_nonneg
      intro n hn
      positivity
    have hm (r : Rat[X]) : 0 <= valueBound r Br := by
      unfold valueBound Polynomial.sum
      apply Finset.sum_nonneg
      intro n hn
      positivity
    have hpoly (r : Rat[X]) (i : Nat) (hi : i < N) :
        (polyBox r Br eta (center i)).1 <= (polyBox r Br eta (center i)).2 ∧
        |(polyBox r Br eta (center i)).1| <= valueBound r Br + Br * derivBound r Br / 2 ∧
        |(polyBox r Br eta (center i)).2| <= valueBound r Br + Br * derivBound r Br / 2 ∧
        ∀ x : Real, x ∈ Icc (xq i : Real) (xq (i + 1) : Real) ->
          ((polyBox r Br eta (center i)).1 : Real) <= (aeval x r + aeval (-x) r) / 2 ∧
          (aeval x r + aeval (-x) r) / 2 <=
            ((polyBox r Br eta (center i)).2 : Real) := by
      have hpi := hpoint i hi.le
      have hpn := hpoint (i + 1) hi
      have hci : 0 <= center i ∧ center i <= Br := by
        dsimp [center]
        constructor <;> linarith
      have hcast (c : Rat) : aeval (c : Real) r = ((r.eval c : Rat) : Real) :=
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval c r
      have hv : |evenEval r (center i)| <= valueBound r Br := by
        have hp := poly_est r Br hB.le
        have hcabsq : |center i| <= Br := by
          rw [abs_of_nonneg hci.1]
          exact hci.2
        have h1 := hp.1 (center i) (by exact_mod_cast hcabsq)
        have h2 := hp.1 (-(center i : Real)) (by
          rw [abs_neg]
          exact_mod_cast hcabsq)
        rw [hcast] at h1
        rw [<- Rat.cast_neg, hcast] at h2
        have : |(((r.eval (center i) : Rat) : Real) +
            ((r.eval (-(center i)) : Rat) : Real)) / 2| <= (valueBound r Br : Real) := by
          rw [abs_div, abs_of_pos (show (0 : Real) < 2 by norm_num)]
          have ha := abs_add_le ((r.eval (center i) : Rat) : Real)
            ((r.eval (-(center i)) : Rat) : Real)
          linarith
        exact_mod_cast this
      have hw : 0 <= derivBound r Br * eta / 2 := by
        exact div_nonneg (mul_nonneg (hd r) heta.le) (by norm_num)
      have hwB : derivBound r Br * eta / 2 <= Br * derivBound r Br / 2 := by
        have := mul_le_mul_of_nonneg_left hetaB (hd r)
        linarith
      have hv' := abs_le.mp hv
      refine ⟨(by dsimp; linarith), (by dsimp; rw [abs_le]; constructor <;> linarith),
        (by dsimp; rw [abs_le]; constructor <;> linarith), ?_⟩
      intro x hx
      have hcabs : |(center i : Real)| <= Br := by
        exact_mod_cast (abs_of_nonneg hci.1 ▸ hci.2)
      have hxabs : |x| <= (Br : Real) := by
        have hh0 : (0 : Real) <= xq i := by exact_mod_cast hpi.1
        have hhB : (xq (i + 1) : Real) <= Br := by exact_mod_cast hpn.2
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      have hdist : |x - (center i : Real)| <= (eta : Real) / 2 := by
        have hstepR : (xq (i + 1) : Real) - (xq i : Real) = eta := by
          exact_mod_cast hstep i
        dsimp [center]
        push_cast
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      have hp := poly_est r Br hB.le
      have h1 := hp.2 x (center i) hxabs hcabs
      have h2 := hp.2 (-x) (-(center i : Real)) (by simpa using hxabs)
        (by simpa using hcabs)
      rw [hcast] at h1
      rw [<- Rat.cast_neg, hcast] at h2
      have hdn : (0 : Real) <= (derivBound r Br : Real) := by exact_mod_cast hd r
      have he1 : |aeval x r - ((r.eval (center i) : Rat) : Real)| <=
          (derivBound r Br : Real) * (eta : Real) / 2 :=
        h1.trans (by nlinarith [mul_le_mul_of_nonneg_left hdist hdn])
      have he2 : |aeval (-x) r - ((r.eval (-(center i)) : Rat) : Real)| <=
          (derivBound r Br : Real) * (eta : Real) / 2 := by
        have he : |(-x) - (-(center i : Real))| = |x - (center i : Real)| := by
          rw [neg_sub_neg, abs_sub_comm]
        rw [Rat.cast_neg, he] at h2
        exact h2.trans (by nlinarith [mul_le_mul_of_nonneg_left hdist hdn])
      obtain ⟨hl1, hu1⟩ := abs_le.mp he1
      obtain ⟨hl2, hu2⟩ := abs_le.mp he2
      dsimp
      push_cast
      constructor <;> linarith
    have hcut (i : Nat) (hi : i < N) :
        (abox i).1 <= (abox i).2 ∧
        ∀ x : Real, x ∈ Icc (xq i : Real) (xq (i + 1) : Real) ->
          ((abox i).1 : Real) <= Real.smoothTransition (2 - |x| / (R : Real)) ∧
          Real.smoothTransition (2 - |x| / (R : Real)) <= ((abox i).2 : Real) := by
      have hti : (t (i + 1) : Real) <= (t i : Real) := by
        have hsx : xq i <= xq (i + 1) := by linarith [hstep i]
        have : (xq i : Real) / (R : Real) <= (xq (i + 1) : Real) / (R : Real) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hsx) hRr.le
        dsimp [t]
        push_cast
        linarith
      have hord := (hcp (i + 1) hi).2.1.trans
        ((Real.smoothTransition.monotone hti).trans (hcp i hi.le).2.2.1)
      refine ⟨(by exact_mod_cast hord), ?_⟩
      intro x hx
      have hx0 : 0 <= x :=
        (by exact_mod_cast (hpoint i hi.le).1 : (0 : Real) <= xq i).trans hx.1
      rw [abs_of_nonneg hx0]
      have htxl : (t (i + 1) : Real) <= 2 - x / (R : Real) := by
        have := div_le_div_of_nonneg_right hx.2 hRr.le
        dsimp [t]
        push_cast
        linarith
      have htxu : 2 - x / (R : Real) <= (t i : Real) := by
        have := div_le_div_of_nonneg_right hx.1 hRr.le
        dsimp [t]
        push_cast
        linarith
      exact ⟨(hcp (i + 1) hi).2.1.trans (Real.smoothTransition.monotone htxl),
        (Real.smoothTransition.monotone htxu).trans (hcp i hi.le).2.2.1⟩
    have hweight (i : Nat) (hi : i < N) :
        (wbox i).1 <= (wbox i).2 ∧
        ∀ x : Real, x ∈ Icc (xq i : Real) (xq (i + 1) : Real) ->
          ((wbox i).1 : Real) <= Real.exp (x / 2) + Real.exp (-x / 2) ∧
          Real.exp (x / 2) + Real.exp (-x / 2) <= ((wbox i).2 : Real) := by
      have hpi := hpoint i hi.le
      have hpn := hpoint (i + 1) hi
      have hxi : (xq i : Real) <= (xq (i + 1) : Real) := by
        exact_mod_cast (by linarith [hstep i] : xq i <= xq (i + 1))
      have hlo : ((wbox i).1 : Real) <=
          Real.exp ((xq i : Real) / 2) + Real.exp (-(xq (i + 1) : Real) / 2) := by
        dsimp [wbox]
        rw [hepNode i hi.le, hemNode (i + 1) hi]
        push_cast
        exact add_le_add
          (by simpa only [Rat.cast_div, Rat.cast_ofNat] using
            (hscalar (xq i / 2)).2.1.1)
          (by simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using
            (hscalar (-xq (i + 1) / 2)).2.1.1)
      have hu : Real.exp ((xq (i + 1) : Real) / 2) + Real.exp (-(xq i : Real) / 2) <=
          ((wbox i).2 : Real) := by
        dsimp [wbox]
        rw [hepNode (i + 1) hi, hemNode i hi.le]
        push_cast
        exact add_le_add
          (by simpa only [Rat.cast_div, Rat.cast_ofNat] using
            (hscalar (xq (i + 1) / 2)).2.1.2)
          (by simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using
            (hscalar (-xq i / 2)).2.1.2)
      constructor
      · exact_mod_cast hlo.trans ((add_le_add
          (Real.exp_monotone (div_le_div_of_nonneg_right hxi (by norm_num)))
          (Real.exp_monotone (div_le_div_of_nonneg_right (neg_le_neg hxi) (by norm_num)))).trans hu)
      · intro x hx
        constructor
        · exact hlo.trans (add_le_add
            (Real.exp_monotone (div_le_div_of_nonneg_right hx.1 (by norm_num)))
            (Real.exp_monotone (div_le_div_of_nonneg_right (neg_le_neg hx.2) (by norm_num))))
        · exact (add_le_add
            (Real.exp_monotone (div_le_div_of_nonneg_right hx.2 (by norm_num)))
            (Real.exp_monotone (div_le_div_of_nonneg_right (neg_le_neg hx.1) (by norm_num)))).trans hu
    have hcheck (r : Rat[X]) (i : Nat) (hi : i < N) :
        check (box r i) (ex r i) = true :=
      expr_accepts _ _ _ (hweight i hi).1 (hcut i hi).1 (hpoly r i hi).1
    have hcell (r : Rat[X]) (i : Nat) (hi : i < N) (x : Real)
        (hx : x ∈ Icc (xq i : Real) (xq (i + 1) : Real)) :
        ((bounds (ex r i)).1 : Real) <= fr r x ∧
          fr r x <= ((bounds (ex r i)).2 : Real) := by
      let v : Fin 3 -> Real := fun j => if j = 0 then
        Real.exp (x / 2) + Real.exp (-x / 2) else if j = 1 then
        Real.smoothTransition (2 - |x| / (R : Real)) else
        (aeval x r + aeval (-x) r) / 2
      have hv : ∀ j, ((box r i j).1 : Real) <= v j ∧ v j <= ((box r i j).2 : Real) := by
        intro j
        fin_cases j
        · simpa [box, cellInputs, v] using (hweight i hi).2 x hx
        · simpa [box, cellInputs, v] using (hcut i hi).2 x hx
        · simpa [box, cellInputs, v] using (hpoly r i hi).2.2.2 x hx
      have hvf : value v (ex r i) = fr r x := by
        simp [ex, value, v, fr]
        ring
      simpa only [hvf] using checked_expression_encloses (box r i) v hv
        (ex r i) (hcheck r i hi)
    let frcont (r : Rat[X]) : Continuous (fr r) := by
      dsimp [fr]
      fun_prop
    have hicell (r : Rat[X]) (i : Nat) (hi : i < N) :
        (((eta * (bounds (ex r i)).1 : Rat) : Real) <=
            ∫ x in (xq i : Real)..(xq (i + 1) : Real), fr r x) ∧
        ((∫ x in (xq i : Real)..(xq (i + 1) : Real), fr r x) <=
            ((eta * (bounds (ex r i)).2 : Rat) : Real)) := by
      have hlen : (xq (i + 1) : Real) - (xq i : Real) = (eta : Real) := by
        exact_mod_cast hstep i
      have hab : (xq i : Real) <= (xq (i + 1) : Real) := by
        have habq : xq i <= xq (i + 1) := by linarith [hstep i, heta.le]
        exact_mod_cast habq
      have hl := intervalIntegral.integral_mono_on (μ := volume) hab
        (continuous_const.intervalIntegrable _ _)
        ((frcont r).intervalIntegrable _ _)
        (fun x hx => (hcell r i hi x hx).1)
      have hu := intervalIntegral.integral_mono_on (μ := volume) hab
        ((frcont r).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
        (fun x hx => (hcell r i hi x hx).2)
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul] at hl hu
      exact ⟨by simpa only [Rat.cast_mul] using hl,
        by simpa only [Rat.cast_mul] using hu⟩
    have hadd (r : Rat[X]) := intervalIntegral.sum_integral_adjacent_intervals (n := N)
      (fun i _ => (frcont r).intervalIntegrable (μ := volume)
        (a := (xq i : Real)) (b := (xq (i + 1) : Real)))
    have hadd' (r : Rat[X]) :
        (∑ i ∈ Finset.range N,
          ∫ x in (xq i : Real)..(xq (i + 1) : Real), fr r x) =
        ∫ x in (0 : Real)..(Br : Real), fr r x := by
      simpa only [hx0, hxN, Rat.cast_zero] using hadd r
    have hisum (r : Rat[X]) :
        (((eta * (∑ i ∈ Finset.range N, (bounds (ex r i)).1) : Rat) : Real) <=
            ∫ x in (0 : Real)..(Br : Real), fr r x) ∧
        ((∫ x in (0 : Real)..(Br : Real), fr r x) <=
            ((eta * (∑ i ∈ Finset.range N, (bounds (ex r i)).2) : Rat) : Real)) := by
      rw [<- hadd' r]
      constructor
      · simpa only [Finset.mul_sum, Rat.cast_sum] using
          Finset.sum_le_sum (s := Finset.range N)
            (fun i hi => (hicell r i (Finset.mem_range.mp hi)).1)
      · simpa only [Finset.mul_sum, Rat.cast_sum] using
          Finset.sum_le_sum (s := Finset.range N)
            (fun i hi => (hicell r i (Finset.mem_range.mp hi)).2)
    have rowsize : gr.2.1.size = N := by
      change (Array.ofFn (fun _i : Fin N => _)).size = N
      exact Array.size_ofFn
    have hrow (i : Nat) (hi : i < gr.2.1.size) :
        gr.2.1[i] = ((box p i, ex p i), (box q i, ex q i)) := by
      have hiN : i < N := by simpa only [rowsize] using hi
      change (Array.ofFn _)[i]'(by simpa only [Array.size_ofFn] using hiN) = _
      rw [Array.getElem_ofFn]
      rfl
    have gall : (gr.2.1.all fun ce =>
        check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) = true := by
      rw [Array.all_eq_true]
      intro i hi
      rw [hrow i hi]
      simp only [Bool.and_eq_true]
      exact ⟨hcheck p i (by simpa only [rowsize] using hi),
        hcheck q i (by simpa only [rowsize] using hi)⟩
    have gJp : gr.2.2.1 =
        (eta * ∑ i ∈ Finset.range N, (bounds (ex p i)).1,
         eta * ∑ i ∈ Finset.range N, (bounds (ex p i)).2) := by
      apply Prod.ext
      · change eta * (∑ i : Fin N,
          (bounds (gr.2.1[i.val]'(by simpa only [rowsize] using i.isLt)).1.2).1) = _
        simp_rw [hrow]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun i => (bounds (ex p i)).1) N
      · change eta * (∑ i : Fin N,
          (bounds (gr.2.1[i.val]'(by simpa only [rowsize] using i.isLt)).1.2).2) = _
        simp_rw [hrow]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun i => (bounds (ex p i)).2) N
    have gJq : gr.2.2.2.1 =
        (eta * ∑ i ∈ Finset.range N, (bounds (ex q i)).1,
         eta * ∑ i ∈ Finset.range N, (bounds (ex q i)).2) := by
      apply Prod.ext
      · change eta * (∑ i : Fin N,
          (bounds (gr.2.1[i.val]'(by simpa only [rowsize] using i.isLt)).2.2).1) = _
        simp_rw [hrow]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun i => (bounds (ex q i)).1) N
      · change eta * (∑ i : Fin N,
          (bounds (gr.2.1[i.val]'(by simpa only [rowsize] using i.isLt)).2.2).2) = _
        simp_rw [hrow]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun i => (bounds (ex q i)).2) N
    have component_bounds (r : Rat[X]) (J : Rat × Rat)
        (hJ : J = (eta * ∑ i ∈ Finset.range N, (bounds (ex r i)).1,
          eta * ∑ i ∈ Finset.range N, (bounds (ex r i)).2)) :
        ((J.1 : Real) <= ∫ x in (0 : Real)..(Br : Real), fr r x) ∧
        ((∫ x in (0 : Real)..(Br : Real), fr r x) <= (J.2 : Real)) := by
      rw [hJ]
      exact hisum r
    have hpBounds := component_bounds p gr.2.2.1 gJp
    have hqBounds := component_bounds q gr.2.2.2.1 gJq
    have hpOrder : gr.2.2.1.1 <= gr.2.2.1.2 := by
      exact_mod_cast hpBounds.1.trans hpBounds.2
    have hqOrder : gr.2.2.2.1.1 <= gr.2.2.2.1.2 := by
      exact_mod_cast hqBounds.1.trans hqBounds.2
    have hfinalCheck := final_accepts gr.2.2.1 gr.2.2.2.1 hpOrder hqOrder
    have hcomplexCont : Continuous (fun x : Real =>
        (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)) := by
      dsimp [H, rationalEvenPolynomial]
      fun_prop
    have hcomplexInt : IntervalIntegrable (fun x : Real =>
        (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x))
        volume 0 B := hcomplexCont.intervalIntegrable _ _
    have hrePoint (x : Real) :
        ((((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)).re =
          fr p x := by
      simp only [H, fr, rationalEvenPolynomial, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, zero_add,
        one_mul]
      ring
    have himPoint (x : Real) :
        ((((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)).im =
          fr q x := by
      simp only [H, fr, rationalEvenPolynomial, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, zero_add,
        one_mul]
      ring
    have hzre : z.re = ∫ x in (0 : Real)..(Br : Real), fr p x := by
      have hBcast : B = (Br : Real) := by
        dsimp [B, Br]
        push_cast
        rfl
      have hh := Complex.reCLM.intervalIntegral_comp_comm hcomplexInt
      rw [hBcast] at hh
      change (∫ x in (0 : Real)..B,
        (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)).re = _
      rw [hBcast]
      simpa only [Complex.reCLM_apply, hrePoint] using hh.symm
    have hzim : z.im = ∫ x in (0 : Real)..(Br : Real), fr q x := by
      have hBcast : B = (Br : Real) := by
        dsimp [B, Br]
        push_cast
        rfl
      have hcomplexInt' : IntervalIntegrable (fun x : Real =>
          (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x))
          volume 0 (Br : Real) := by
        simpa only [hBcast] using hcomplexInt
      have hh := Complex.imCLM.intervalIntegral_comp_comm hcomplexInt'
      change (∫ x in (0 : Real)..B,
        (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)).im = _
      rw [hBcast]
      simpa only [Complex.imCLM_apply, himPoint] using hh.symm
    have hpZ : (gr.2.2.1.1 : Real) <= z.re ∧ z.re <= (gr.2.2.1.2 : Real) := by
      rw [hzre]
      exact hpBounds
    have hqZ : (gr.2.2.2.1.1 : Real) <= z.im ∧ z.im <= (gr.2.2.2.1.2 : Real) := by
      rw [hzim]
      exact hqBounds
    have hfinalSemantic :
        ((gr.2.2.2.2.1.1 : Real) <= 2 * Complex.normSq z ∧
          2 * Complex.normSq z <= (gr.2.2.2.2.1.2 : Real)) := by
      let vals : Fin 2 -> Real := fun i => if i = 0 then z.re else z.im
      have hv : ∀ i, ((finalInputs gr.2.2.1 gr.2.2.2.1 i).1 : Real) <= vals i ∧
          vals i <= ((finalInputs gr.2.2.1 gr.2.2.2.1 i).2 : Real) := by
        intro i
        fin_cases i
        · simpa [finalInputs, vals] using hpZ
        · simpa [finalInputs, vals] using hqZ
      have hh := checked_expression_encloses
        (finalInputs gr.2.2.1 gr.2.2.2.1) vals hv
        gr.2.2.2.2.2 hfinalCheck
      have hvf : value vals gr.2.2.2.2.2 = 2 * Complex.normSq z := by
        change value vals (finalExpr gr.2.2.1 gr.2.2.2.1) = _
        simp [value, vals, Complex.normSq_apply]
        ring
      simpa only [hvf] using hh
    have hL0 : 0 <= gr.2.2.2.2.1.1 := by
      change 0 <= (bounds (finalExpr gr.2.2.1 gr.2.2.2.1)).1
      change 0 <= 2 * ((sqBox gr.2.2.1).1 + (sqBox gr.2.2.2.1).1)
      have hsqa : 0 <= (sqBox gr.2.2.1).1 := by
        dsimp only
        split_ifs <;> positivity
      have hsqb : 0 <= (sqBox gr.2.2.2.1).1 := by
        dsimp only
        split_ifs <;> positivity
      exact mul_nonneg (by norm_num) (add_nonneg hsqa hsqb)
    have hLU : gr.2.2.2.2.1.1 <= gr.2.2.2.2.1.2 := by
      exact_mod_cast hfinalSemantic.1.trans hfinalSemantic.2
    have hpDec : decide (gr.2.2.1.1 <= gr.2.2.1.2) = true :=
      decide_eq_true_eq.mpr hpOrder
    have hqDec : decide (gr.2.2.2.1.1 <= gr.2.2.2.1.2) = true :=
      decide_eq_true_eq.mpr hqOrder
    have hL0Dec : decide (0 <= gr.2.2.2.2.1.1) = true :=
      decide_eq_true_eq.mpr hL0
    have hLUDec : decide (gr.2.2.2.2.1.1 <= gr.2.2.2.2.1.2) = true :=
      decide_eq_true_eq.mpr hLU
    have hvalid : valid gr = true := by
      change (((((
        gr.2.1.all (fun ce => check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) &&
        check (finalInputs gr.2.2.1 gr.2.2.2.1) gr.2.2.2.2.2) &&
        decide (gr.2.2.1.1 <= gr.2.2.1.2)) &&
        decide (gr.2.2.2.1.1 <= gr.2.2.2.1.2)) &&
        decide (0 <= gr.2.2.2.2.1.1)) &&
        decide (gr.2.2.2.2.1.1 <= gr.2.2.2.2.1.2)) = true
      rw [gall, hfinalCheck, hpDec, hqDec, hL0Dec, hLUDec]
      rfl
    exact ⟨gall, hfinalCheck, hpOrder, hqOrder, hpZ, hqZ, hfinalSemantic, hvalid⟩

end D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGrid
