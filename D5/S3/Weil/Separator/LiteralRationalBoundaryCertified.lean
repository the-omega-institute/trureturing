/- GID: D5/S3/Weil/Separator/LiteralRationalBoundaryCertified
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/LiteralRationalBoundaryCertified
   mirror-E: none(waiver:certified-rational-boundary-producer)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified; instance=D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified
   digest: A retained finite rational certificate encloses the exact same-H full-line pole boundary. -/

import D5.S3.Weil.Separator.LiteralRationalBoundaryGrid
import D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGrid
import D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGridRate
import D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
import D5.S3.Weil.TestFunctions.RationalCutoffApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.LiteralRationalBoundaryCertified

open D5.S3.Weil.Separator.LiteralRationalBoundaryGrid
open D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGrid
open D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGridRate
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
-- The all-input interval and integration proof needs a larger elaboration budget.
def boundaryCertified (R : Nat) (hR : 0 < R) (p q : Rat[X]) (m : Nat) :
    { out : Nat × Nat × Nat × GridPayload //
      let s := out.1
      let kCap := out.2.1
      let k := out.2.2.1
      let gr := out.2.2.2
      let Br : Rat := 2 * R
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
      let eps : Rat := (1 / 2) ^ m
      let build : Nat → GridPayload := fun depth =>
        let N : Nat := 2 ^ depth
        let eta : Rat := Br / N
        let raw := boundaryGrid R p q depth s
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
        (raw.1, raw.2, Jp, Jq, bounds sf, sf)
      let valid : GridPayload → Bool := fun g =>
        g.2.1.all (fun ce => check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) &&
        check (finalInputs g.2.2.1 g.2.2.2.1) g.2.2.2.2.2 &&
        decide (g.2.2.1.1 <= g.2.2.1.2) &&
        decide (g.2.2.2.1.1 <= g.2.2.2.1.2) &&
        decide (0 <= g.2.2.2.2.1.1) &&
        decide (g.2.2.2.2.1.1 <= g.2.2.2.2.1.2)
      let stop : GridPayload → Bool := fun g => valid g &&
        decide (g.2.2.2.2.1.2 - g.2.2.2.2.1.1 <= eps)
      let firstStop : Nat → Nat → Option (Nat × GridPayload) :=
        fun fuel start =>
          Nat.rec (motive := fun _ => Nat → Option (Nat × GridPayload))
            (fun d => let g := build d; if stop g then some (d, g) else none)
            (fun _ recur d =>
              let g := build d
              if stop g then some (d, g) else recur (d + 1)) fuel start
      let B : Real := 2 * R
      let H := fun x : Real =>
        ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
          rationalEvenPolynomial p q x
      Cscalar * (1 / 2 : Rat) ^ s <= eps / 2 ∧
      (∀ j < s, ¬ Cscalar * (1 / 2 : Rat) ^ j <= eps / 2) ∧
      Cmesh * (1 / 2 : Rat) ^ kCap <= eps / 2 ∧
      (∀ j < kCap, ¬ Cmesh * (1 / 2 : Rat) ^ j <= eps / 2) ∧
      firstStop kCap 0 = some (k, gr) ∧ k <= kCap ∧ gr = build k ∧
      valid gr = true ∧ stop gr = true ∧
      0 <= gr.2.2.2.2.1.1 ∧
      gr.2.2.2.2.1.1 <= gr.2.2.2.2.1.2 ∧
      gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <= eps ∧
      gr.2.2.2.2.1.1 =
        2 * ((sqBox gr.2.2.1).1 + (sqBox gr.2.2.2.1).1) ∧
      gr.2.2.2.2.1.2 =
        2 * ((sqBox gr.2.2.1).2 + (sqBox gr.2.2.2.1).2) ∧
      ∃ f : WeilTestFunction,
        (∀ x, f x = H x) ∧
        tsupport (f : Real → Complex) ⊆ Icc (-B) B ∧
        Integrable (fun x : Real => Complex.exp ((x : Complex) / 2) * f x) ∧
        (let z := ∫ x : Real, Complex.exp ((x : Complex) / 2) * f x
         let half := ∫ x in (0 : Real)..B,
           (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * f x)
         z = half ∧
         ((gr.2.2.1.1 : Real) <= z.re ∧ z.re <= (gr.2.2.1.2 : Real)) ∧
         ((gr.2.2.2.1.1 : Real) <= z.im ∧ z.im <= (gr.2.2.2.1.2 : Real)) ∧
         ((gr.2.2.2.2.1.1 : Real) <= 2 * Complex.normSq z ∧
           2 * Complex.normSq z <= (gr.2.2.2.2.1.2 : Real))) } := by
  let valid : GridPayload → Bool := fun g =>
    g.2.1.all (fun ce => check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) &&
    check (finalInputs g.2.2.1 g.2.2.2.1) g.2.2.2.2.2 &&
    decide (g.2.2.1.1 <= g.2.2.1.2) &&
    decide (g.2.2.2.1.1 <= g.2.2.2.1.2) &&
    decide (0 <= g.2.2.2.2.1.1) &&
    decide (g.2.2.2.2.1.1 <= g.2.2.2.2.1.2)
  let Br : Rat := 2 * R
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
  let eps : Rat := (1 / 2) ^ m
  have hBr : 0 <= Br := by dsimp [Br]; positivity
  have hd (r : Rat[X]) : 0 <= derivBound r Br := by
    unfold derivBound Polynomial.sum
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hv (r : Rat[X]) : 0 <= valueBound r Br := by
    unfold valueBound Polynomial.sum
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hEexp : Real.exp (R : Real) <= (E : Real) := by
    simpa only [E, Rat.cast_natCast] using
      (boundaryExpCertified_v1 (R : Rat) 0).property.2.2.2.2.1
  have hE : (1 : Rat) <= E := by
    have hR0 : (0 : Real) <= R := Nat.cast_nonneg R
    have h : (1 : Real) <= (E : Real) := by
      rw [← Real.exp_zero]
      exact (Real.exp_monotone hR0).trans hEexp
    exact_mod_cast h
  have hT : 0 <= T := by dsimp [T]; linarith
  have hAp : 0 <= Ap := by
    dsimp [Ap]
    exact add_nonneg (hv p) (div_nonneg (mul_nonneg hBr (hd p)) (by norm_num))
  have hAq : 0 <= Aq := by
    dsimp [Aq]
    exact add_nonneg (hv q) (div_nonneg (mul_nonneg hBr (hd q)) (by norm_num))
  have hIp : 0 <= Ip := by dsimp [Ip]; positivity
  have hIq : 0 <= Iq := by dsimp [Iq]; positivity
  have hKmp : 0 <= Kmp := by
    dsimp [Kmp]
    apply mul_nonneg hBr
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT) hBr) (hd p))
      (mul_nonneg (add_nonneg hT
        (mul_nonneg (by norm_num) (le_trans (by norm_num) hE))) hAp)
  have hKmq : 0 <= Kmq := by
    dsimp [Kmq]
    apply mul_nonneg hBr
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT) hBr) (hd q))
      (mul_nonneg (add_nonneg hT
        (mul_nonneg (by norm_num) (le_trans (by norm_num) hE))) hAq)
  have hKsp : 0 <= Ksp := by dsimp [Ksp]; positivity
  have hKsq : 0 <= Ksq := by dsimp [Ksq]; positivity
  have hCmesh : 0 <= Cmesh := by
    dsimp [Cmesh]
    exact mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg hIp hKmp) (mul_nonneg hIq hKmq))
  have hCscalar : 0 <= Cscalar := by
    dsimp [Cscalar]
    exact mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg hIp hKsp) (mul_nonneg hIq hKsq))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hsExists : ∃ n : Nat, Cscalar * (1 / 2 : Rat) ^ n <= eps / 2 := by
    by_cases hC0 : Cscalar = 0
    · exact ⟨0, by rw [hC0, zero_mul]; positivity⟩
    · have hCp : 0 < Cscalar := lt_of_le_of_ne hCscalar (Ne.symm hC0)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
        (x := eps / (2 * Cscalar)) (y := (1 / 2 : Rat)) (by positivity) (by norm_num)
      refine ⟨n, ?_⟩
      rw [mul_comm]
      apply (le_div_iff₀ hCp).1
      exact hn.le.trans_eq (by field_simp)
  have hkExists : ∃ n : Nat, Cmesh * (1 / 2 : Rat) ^ n <= eps / 2 := by
    by_cases hC0 : Cmesh = 0
    · exact ⟨0, by rw [hC0, zero_mul]; positivity⟩
    · have hCp : 0 < Cmesh := lt_of_le_of_ne hCmesh (Ne.symm hC0)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
        (x := eps / (2 * Cmesh)) (y := (1 / 2 : Rat)) (by positivity) (by norm_num)
      refine ⟨n, ?_⟩
      rw [mul_comm]
      apply (le_div_iff₀ hCp).1
      exact hn.le.trans_eq (by field_simp)
  let s := Nat.find hsExists
  let kCap := Nat.find hkExists
  let build : Nat → GridPayload := fun depth =>
    let N : Nat := 2 ^ depth
    let eta : Rat := Br / N
    let raw := boundaryGrid R p q depth s
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
    (raw.1, raw.2, Jp, Jq, bounds sf, sf)
  let stop : GridPayload → Bool := fun g =>
    valid g &&
    decide (g.2.2.2.2.1.2 - g.2.2.2.2.1.1 <= eps)
  let firstStop : Nat → Nat → Option (Nat × GridPayload) :=
    fun fuel start =>
      Nat.rec (motive := fun _ => Nat → Option (Nat × GridPayload))
        (fun d => let g := build d; if stop g then some (d, g) else none)
        (fun _ recur d =>
          let g := build d
          if stop g then some (d, g) else recur (d + 1)) fuel start
  let selected := firstStop kCap 0
  let accepted : Nat × GridPayload :=
    match selected with
    | none => (0, build 0)
    | some value => value
  let k := accepted.1
  let gr := accepted.2
  refine ⟨(s, kCap, k, gr), ?_⟩
  as_aux_lemma =>
  have hsSpec : Cscalar * (1 / 2 : Rat) ^ s <= eps / 2 := Nat.find_spec hsExists
  have hkSpec : Cmesh * (1 / 2 : Rat) ^ kCap <= eps / 2 := Nat.find_spec hkExists
  have hsMin : ∀ j < s, ¬ Cscalar * (1 / 2 : Rat) ^ j <= eps / 2 := by
    exact @Nat.find_min _ (fun _ => inferInstance) hsExists
  have hkMin : ∀ j < kCap, ¬ Cmesh * (1 / 2 : Rat) ^ j <= eps / 2 := by
    exact @Nat.find_min _ (fun _ => inferInstance) hkExists
  have hfixed (depth : Nat) :
      let N : Nat := 2 ^ depth
      let gr := build depth
      let B : Real := 2 * R
      let H := fun x : Real =>
        ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
          rationalEvenPolynomial p q x
      let z := ∫ x in (0 : Real)..B,
        (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)
      (gr.2.1.all fun ce => check ce.1.1 ce.1.2 && check ce.2.1 ce.2.2) = true ∧
      check (finalInputs gr.2.2.1 gr.2.2.2.1) gr.2.2.2.2.2 = true ∧
      gr.2.2.1.1 <= gr.2.2.1.2 ∧ gr.2.2.2.1.1 <= gr.2.2.2.1.2 ∧
      ((gr.2.2.1.1 : Real) <= z.re ∧ z.re <= (gr.2.2.1.2 : Real)) ∧
      ((gr.2.2.2.1.1 : Real) <= z.im ∧ z.im <= (gr.2.2.2.1.2 : Real)) ∧
      ((gr.2.2.2.2.1.1 : Real) <= 2 * Complex.normSq z ∧
        2 * Complex.normSq z <= (gr.2.2.2.2.1.2 : Real)) ∧
      |gr.2.2.1.1| <= Ip ∧ |gr.2.2.1.2| <= Ip ∧
      |gr.2.2.2.1.1| <= Iq ∧ |gr.2.2.2.1.2| <= Iq ∧
      gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <=
        Cmesh / (N : Rat) + Cscalar * (1 / 2 : Rat) ^ s ∧ valid gr = true := by
    have hsemantic := fixedGridSemanticCertified R hR p q depth s
    have hrate := fixedGridRateCertified R hR p q depth s
    dsimp only at hsemantic hrate ⊢
    rcases hsemantic with ⟨hcells, hfinal, hpOrder, hqOrder, hp, hq, hnorm, hvalid⟩
    rcases hrate with ⟨hpAmp0, hpAmp1, hqAmp0, hqAmp1, hwidth⟩
    exact ⟨hcells, hfinal, hpOrder, hqOrder, hp, hq, hnorm,
      hpAmp0, hpAmp1, hqAmp0, hqAmp1, hwidth, hvalid⟩
  have hdyadic (C : Rat) (n : Nat) :
      C / ((2 ^ n : Nat) : Rat) = C * (1 / 2 : Rat) ^ n := by
    rw [div_eq_mul_inv]
    congr 1
    norm_num [one_div_pow]
  have hcapRate : Cmesh / (((2 ^ kCap : Nat) : Rat)) +
      Cscalar * (1 / 2 : Rat) ^ s <= eps := by
    rw [hdyadic]
    calc
      Cmesh * (1 / 2 : Rat) ^ kCap + Cscalar * (1 / 2 : Rat) ^ s <=
          eps / 2 + eps / 2 := add_le_add hkSpec hsSpec
      _ = eps := by ring
  have hcapData := hfixed kCap
  dsimp only at hcapData
  rcases hcapData with ⟨hcapCells, hcapFinal, hcapPOrder, hcapQOrder,
    hcapP, hcapQ, hcapNorm, hcapAmpP0, hcapAmpP1, hcapAmpQ0,
    hcapAmpQ1, hcapWidth, hcapValid⟩
  have hcapWidthEps : (build kCap).2.2.2.2.1.2 -
      (build kCap).2.2.2.2.1.1 <= eps := hcapWidth.trans hcapRate
  have hcapWidthDec : decide ((build kCap).2.2.2.2.1.2 -
      (build kCap).2.2.2.2.1.1 <= eps) = true :=
    decide_eq_true_eq.mpr hcapWidthEps
  have hstopCap : stop (build kCap) = true := by
    simpa only [stop, Bool.and_eq_true] using
      (And.intro hcapValid hcapWidthDec)
  have search_hits : ∀ fuel start, stop (build (start + fuel)) = true →
      ∃ depth gr, firstStop fuel start = some (depth, gr) := by
    intro fuel
    induction fuel with
    | zero =>
        intro start h
        exact ⟨start, build start, by simpa [firstStop] using h⟩
    | succ fuel ih =>
        intro start hlast
        by_cases hnow : stop (build start) = true
        · exact ⟨start, build start, by simp [firstStop, hnow]⟩
        · have htail : stop (build ((start + 1) + fuel)) = true := by
            have hindex : (start + 1) + fuel = start + Nat.succ fuel := by omega
            rw [hindex]
            exact hlast
          obtain ⟨depth, gr, hfound⟩ := ih (start + 1) htail
          exact ⟨depth, gr, by simpa [firstStop, hnow] using hfound⟩
  have search_sound : ∀ fuel start depth gr,
      firstStop fuel start = some (depth, gr) →
      gr = build depth ∧ stop gr = true ∧ depth <= start + fuel := by
    intro fuel
    induction fuel with
    | zero =>
        intro start depth gr hfound
        by_cases hnow : stop (build start) = true
        · simp [firstStop, hnow] at hfound
          rcases hfound with ⟨rfl, rfl⟩
          exact ⟨rfl, hnow, by omega⟩
        · simp [firstStop, hnow] at hfound
    | succ fuel ih =>
        intro start depth gr hfound
        by_cases hnow : stop (build start) = true
        · simp [firstStop, hnow] at hfound
          rcases hfound with ⟨rfl, rfl⟩
          exact ⟨rfl, hnow, by omega⟩
        · have htail : firstStop fuel (start + 1) = some (depth, gr) := by
            simpa [firstStop, hnow] using hfound
          obtain ⟨hgr, hstop, hbound⟩ := ih (start + 1) depth gr htail
          exact ⟨hgr, hstop, by omega⟩
  have hcapAsLast : stop (build (0 + kCap)) = true := by simpa using hstopCap
  have hselected : selected ≠ none := by
    intro hnone
    obtain ⟨depth, payload, hfound⟩ := search_hits kCap 0 hcapAsLast
    have hsome : selected = some (depth, payload) := by
      simpa only [selected] using hfound
    rw [hnone] at hsome
    contradiction
  have hselectedEq : selected = some accepted := by
    simp only [accepted]
    cases hsel : selected with
    | none => exact (hselected hsel).elim
    | some value => simp only [hsel]
  have hsearch : firstStop kCap 0 = some (k, gr) := by
    change firstStop kCap 0 = some accepted
    simpa only [selected] using hselectedEq
  obtain ⟨hgr, hstop, hkBound⟩ := search_sound kCap 0 k gr hsearch
  have hstopParts := hstop
  simp only [stop, Bool.and_eq_true, decide_eq_true_eq] at hstopParts
  rcases hstopParts with ⟨hvalidAccepted, hWidth⟩
  have hvalidParts := hvalidAccepted
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hvalidParts
  rcases hvalidParts with ⟨⟨⟨⟨⟨hcells, hfinal⟩, hpOrder⟩, hqOrder⟩,
    hL0⟩, hLU⟩
  have hfidelity :
      gr.2.2.2.2.1.1 = 2 * ((sqBox gr.2.2.1).1 + (sqBox gr.2.2.2.1).1) ∧
      gr.2.2.2.2.1.2 = 2 * ((sqBox gr.2.2.1).2 + (sqBox gr.2.2.2.1).2) := by
    rw [hgr]
    exact ⟨rfl, rfl⟩
  have haccepted := hfixed k
  dsimp only at haccepted
  rw [← hgr] at haccepted
  rcases haccepted with ⟨_hcells, _hfinal, _hpOrder, _hqOrder,
    hpHalf, hqHalf, hnormHalf, _⟩
  let B : Real := 2 * R
  let H := fun x : Real =>
    ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
      rationalEvenPolynomial p q x
  have geometry : ∃ f : WeilTestFunction,
      (∀ x, f x = H x) ∧
      tsupport (f : Real → Complex) ⊆ Icc (-B) B ∧
      Integrable (fun x : Real => Complex.exp ((x : Complex) / 2) * f x) ∧
      (∫ x : Real, Complex.exp ((x : Complex) / 2) * f x) =
        ∫ x in (0 : Real)..B,
          (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * f x) := by
    have hRr : (0 : Real) < R := Nat.cast_pos.mpr hR
    have hcut (x : Real) :
        Real.smoothTransition (2 - |x| / (R : Real)) =
          Real.smoothTransition (2 - x / R) * Real.smoothTransition (2 + x / R) := by
      by_cases hx : 0 <= x
      · have hOne : Real.smoothTransition (2 + x / R) = 1 :=
          Real.smoothTransition.one_of_one_le (by
            have : 0 <= x / (R : Real) := div_nonneg hx hRr.le
            linarith)
        rw [abs_of_nonneg hx, hOne, mul_one]
      · have hx' : x < 0 := lt_of_not_ge hx
        have hOne : Real.smoothTransition (2 - x / R) = 1 :=
          Real.smoothTransition.one_of_one_le (by
            have : x / (R : Real) < 0 := div_neg_of_neg_of_pos hx' hRr
            linarith)
        rw [abs_of_neg hx', hOne, one_mul]
        congr 1
        ring
    have hpoly (r : Rat[X]) : ContDiff Real ∞ (fun x : Real =>
        ((aeval x r : Real) + aeval (-x) r) / 2) :=
      ((r.contDiff_aeval ∞).add
        ((r.contDiff_aeval ∞).comp contDiff_neg)).div_const 2
    have hH : H = fun x : Real =>
        (((Real.smoothTransition (2 - x / R) *
          Real.smoothTransition (2 + x / R) : Real) : Complex) *
            rationalEvenPolynomial p q x) := by
      funext x
      dsimp [H]
      rw [hcut]
    have hcont : ContDiff Real ∞ H := by
      rw [hH]
      apply ContDiff.mul
      · exact Complex.ofRealCLM.contDiff.comp
          ((Real.smoothTransition.contDiff.comp
            (contDiff_const.sub (contDiff_id.div_const (R : Real)))).mul
          (Real.smoothTransition.contDiff.comp
            (contDiff_const.add (contDiff_id.div_const (R : Real)))))
      · exact (Complex.ofRealCLM.contDiff.comp (hpoly p)).add
          (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hpoly q)))
    have heven (x : Real) : H (-x) = H x := by
      dsimp [H]
      rw [abs_neg]
      congr 1
      simp only [rationalEvenPolynomial, neg_neg]
      congr 1 <;> ring
    have hsupp : Function.support H ⊆ Icc (-B) B := by
      intro x hx
      have hlt : |x| < B := by
        by_contra hn
        have harg : 2 - |x| / (R : Real) <= 0 := by
          have hle : B <= |x| := le_of_not_gt hn
          dsimp [B] at hle
          have : (2 : Real) <= |x| / R := (le_div_iff₀ hRr).2 (by linarith)
          linarith
        have hz := Real.smoothTransition.zero_of_nonpos harg
        have : H x = 0 := by simp [H, hz]
        exact hx this
      exact abs_le.mp hlt.le
    have hts : tsupport H ⊆ Icc (-B) B := closure_minimal hsupp isClosed_Icc
    have hcompact : HasCompactSupport H :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H) hts
    let f : WeilTestFunction := {
      toFun := H
      contDiff' := hcont
      hasCompactSupport' := hcompact
      even' := heven
    }
    have hgcont : Continuous (fun x : Real =>
        Complex.exp ((x : Complex) / 2) * f x) :=
      (by fun_prop : Continuous fun x : Real =>
        Complex.exp ((x : Complex) / 2)).mul f.continuous
    have hgint : Integrable (fun x : Real =>
        Complex.exp ((x : Complex) / 2) * f x) :=
      hgcont.integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
    have hgsupp : Function.support (fun x : Real =>
        Complex.exp ((x : Complex) / 2) * f x) ⊆ Ioc (-B) B := by
      intro x hx
      have hlt : |x| < B := by
        by_contra hn
        have harg : 2 - |x| / (R : Real) <= 0 := by
          have hle : B <= |x| := le_of_not_gt hn
          dsimp [B] at hle
          have : (2 : Real) <= |x| / R := (le_div_iff₀ hRr).2 (by linarith)
          linarith
        have hz := Real.smoothTransition.zero_of_nonpos harg
        have hfzero : f x = 0 := by change H x = 0; simp [H, hz]
        have : Complex.exp ((x : Complex) / 2) * f x = 0 := by simp [hfzero]
        exact hx this
      exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
    have hfull :
        (∫ x : Real, Complex.exp ((x : Complex) / 2) * f x) =
          ∫ x in (-B)..B, Complex.exp ((x : Complex) / 2) * f x :=
      (intervalIntegral.integral_eq_integral_of_support_subset hgsupp).symm
    have hreflect := intervalIntegral.integral_comp_neg
      (a := (0 : Real)) (b := B)
      (f := fun x : Real => Complex.exp ((x : Complex) / 2) * f x)
    have hreflect' :
        (∫ x in (-B)..(0 : Real), Complex.exp ((x : Complex) / 2) * f x) =
          ∫ x in (0 : Real)..B, Complex.exp (-(x : Complex) / 2) * f x := by
      calc
        _ = ∫ x in (-B)..(-(0 : Real)), Complex.exp ((x : Complex) / 2) * f x := by simp
        _ = ∫ x in (0 : Real)..B, Complex.exp (((-x : Real) : Complex) / 2) * f (-x) :=
          hreflect.symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro x _
          change Complex.exp (((-x : Real) : Complex) / 2) * f (-x) =
            Complex.exp (-(x : Complex) / 2) * f x
          rw [f.even]
          congr 2
          push_cast
          ring
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hgcont.intervalIntegrable (μ := volume) (a := -B) (b := 0))
      (hgcont.intervalIntegrable (μ := volume) (a := 0) (b := B))
    refine ⟨f, fun _ => rfl, ?_, hgint, ?_⟩
    · change tsupport H ⊆ Icc (-B) B
      exact hts
    · rw [hfull, ← hadd, hreflect', ← intervalIntegral.integral_add]
      apply intervalIntegral.integral_congr
      intro x _
      change Complex.exp (-(x : Complex) / 2) * f x +
          Complex.exp ((x : Complex) / 2) * f x =
        ((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * f x
      have hp : Complex.exp ((x : Complex) / 2) = (Real.exp (x / 2) : Complex) := by
        rw [show (x : Complex) / 2 = ((x / 2 : Real) : Complex) by push_cast; rfl]
        exact (Complex.ofReal_exp _).symm
      have hm : Complex.exp (-(x : Complex) / 2) = (Real.exp (-x / 2) : Complex) := by
        rw [show -(x : Complex) / 2 = ((-x / 2 : Real) : Complex) by push_cast; rfl]
        exact (Complex.ofReal_exp _).symm
      rw [hp, hm]
      push_cast
      ring
      · exact (((by fun_prop : Continuous fun x : Real =>
          Complex.exp (-(x : Complex) / 2)).mul f.continuous).intervalIntegrable
            (a := 0) (b := B))
      · exact hgcont.intervalIntegrable (a := 0) (b := B)
  obtain ⟨f, hf, hfsupp, hfint, hfbridge⟩ := geometry
  let z := ∫ x : Real, Complex.exp ((x : Complex) / 2) * f x
  let halfH := ∫ x in (0 : Real)..B,
    (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x)
  have hhalf : (∫ x in (0 : Real)..B,
      (((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * f x)) = halfH := by
    apply intervalIntegral.integral_congr
    intro x _
    change ((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * f x =
      ((Real.exp (x / 2) + Real.exp (-x / 2) : Real) : Complex) * H x
    rw [hf x]
  have hz : z = halfH := hfbridge.trans hhalf
  have hpHalf' : ((gr.2.2.1.1 : Real) <= halfH.re ∧
      halfH.re <= (gr.2.2.1.2 : Real)) := by
    simpa only [halfH, B, H] using hpHalf
  have hqHalf' : ((gr.2.2.2.1.1 : Real) <= halfH.im ∧
      halfH.im <= (gr.2.2.2.1.2 : Real)) := by
    simpa only [halfH, B, H] using hqHalf
  have hnormHalf' : ((gr.2.2.2.2.1.1 : Real) <= 2 * Complex.normSq halfH ∧
      2 * Complex.normSq halfH <= (gr.2.2.2.2.1.2 : Real)) := by
    simpa only [halfH, B, H] using hnormHalf
  have hpFull : ((gr.2.2.1.1 : Real) <= z.re ∧
      z.re <= (gr.2.2.1.2 : Real)) := by
    rw [hz]
    exact hpHalf'
  have hqFull : ((gr.2.2.2.1.1 : Real) <= z.im ∧
      z.im <= (gr.2.2.2.1.2 : Real)) := by
    rw [hz]
    exact hqHalf'
  have hnormFull : ((gr.2.2.2.2.1.1 : Real) <= 2 * Complex.normSq z ∧
      2 * Complex.normSq z <= (gr.2.2.2.2.1.2 : Real)) := by
    rw [hz]
    exact hnormHalf'
  dsimp only
  refine ⟨hsSpec, hsMin, hkSpec, hkMin, hsearch, ?_, hgr, hvalidAccepted, hstop,
    hL0, hLU, hWidth, hfidelity.1, hfidelity.2, f, hf, hfsupp, hfint, ?_⟩
  · simpa using hkBound
  · dsimp only [z] at hpFull hqFull hnormFull ⊢
    exact ⟨hfbridge, hpFull, hqFull, hnormFull⟩
open Set MeasureTheory Polynomial
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition
open D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

set_option autoImplicit false
set_option maxRecDepth 4096

example :
    forall (R : Nat) (hR : 0 < R) (p q : Rat[X]) (m : Nat),
      let out := (boundaryCertified R hR p q m).val
      let gr := out.2.2.2
      let B : Real := 2 * R
      let eps : Rat := (1 / 2) ^ m
      let H := fun x : Real =>
        ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
          rationalEvenPolynomial p q x
      let sq := fun a : Rat × Rat =>
        (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
          max (a.1 ^ 2) (a.2 ^ 2))
      exists f : WeilTestFunction,
        (forall x, f x = H x) ∧
        tsupport (f : Real -> Complex) ⊆ Icc (-B) B ∧
        gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <= eps ∧
        gr.2.2.2.2.1.1 = 2 * ((sq gr.2.2.1).1 + (sq gr.2.2.2.1).1) ∧
        gr.2.2.2.2.1.2 = 2 * ((sq gr.2.2.1).2 + (sq gr.2.2.2.1).2) ∧
        (gr.2.2.2.2.1.1 : Real) <= (poleTerm (convolutionSquare f)).re ∧
        (poleTerm (convolutionSquare f)).re <= (gr.2.2.2.2.1.2 : Real) :=
  by
    intro R hR p q m
    let certified := boundaryCertified R hR p q m
    let out := certified.val
    let gr := out.2.2.2
    let B : Real := 2 * R
    let eps : Rat := (1 / 2) ^ m
    let H := fun x : Real =>
      ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
        rationalEvenPolynomial p q x
    let sq := fun a : Rat × Rat =>
      (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
        max (a.1 ^ 2) (a.2 ^ 2))
    have hcert := certified.property
    dsimp only at hcert
    rcases hcert with
      ⟨hs, hsMin, hk, hkMin, hsearch, hkBound, hgrid, hvalid, hstop,
        hL0, hLU, hwidth, hLower, hUpper, hgeometry⟩
    rcases hgeometry with ⟨f, hf, hsupport, hintegrable, hbridge,
      hRe, hIm, hNorm⟩
    have hpole := pole_rank_one_decomposition f
    have hpoleRe := congrArg Complex.re hpole
    norm_num at hpoleRe
    refine ⟨f, hf, hsupport, ?_, ?_, ?_, ?_⟩
    . exact hwidth
    . exact hLower
    . exact hUpper
    . constructor
      . rw [hpoleRe]
        simpa only [certified, out, gr] using hNorm.1
      . rw [hpoleRe]
        simpa only [certified, out, gr] using hNorm.2

example :
    forall (R : Nat) (hR : 0 < R) (p q : Rat[X]) (m : Nat)
      (Z : ZeroData),
      let out := (boundaryCertified R hR p q m).val
      let gr := out.2.2.2
      let B : Real := 2 * R
      let eps : Rat := (1 / 2) ^ m
      let H := fun x : Real =>
        ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
          rationalEvenPolynomial p q x
      let sq := fun a : Rat × Rat =>
        (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
          max (a.1 ^ 2) (a.2 ^ 2))
      exists f : WeilTestFunction,
        (forall x, f x = H x) ∧
        tsupport (f : Real -> Complex) ⊆ Icc (-B) B ∧
        gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <= eps ∧
        gr.2.2.2.2.1.1 = 2 * ((sq gr.2.2.1).1 + (sq gr.2.2.2.1).1) ∧
        gr.2.2.2.2.1.2 = 2 * ((sq gr.2.2.1).2 + (sq gr.2.2.2.1).2) ∧
        forall (hZero : SymmetricConvergent Z (convolutionSquare f))
          (hArch : ArchimedeanConvergent (convolutionSquare f)),
          let V := archimedeanJumpEnergy f + arithmeticJumpEnergy B f -
            (2 * totalPrimeWeight B - archimedeanConstant) * l2Mass f
          (gr.2.2.2.2.1.1 : Real) + V <=
              (zeroSum Z (convolutionSquare f) hZero).re ∧
            (zeroSum Z (convolutionSquare f) hZero).re <=
              (gr.2.2.2.2.1.2 : Real) + V :=
  by
    intro R hR p q m Z
    let certified := boundaryCertified R hR p q m
    let out := certified.val
    let gr := out.2.2.2
    let B : Real := 2 * R
    let eps : Rat := (1 / 2) ^ m
    let H := fun x : Real =>
      ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
        rationalEvenPolynomial p q x
    let sq := fun a : Rat × Rat =>
      (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
        max (a.1 ^ 2) (a.2 ^ 2))
    have hcert := certified.property
    dsimp only at hcert
    rcases hcert with
      ⟨hs, hsMin, hk, hkMin, hsearch, hkBound, hgrid, hvalid, hstop,
        hL0, hLU, hwidth, hLower, hUpper, hgeometry⟩
    rcases hgeometry with ⟨f, hf, hsupport, hintegrable, hbridge,
      hRe, hIm, hNorm⟩
    refine ⟨f, hf, hsupport, hwidth, hLower, hUpper, ?_⟩
    intro hZero hArch
    let V := archimedeanJumpEnergy f + arithmeticJumpEnergy B f -
      (2 * totalPrimeWeight B - archimedeanConstant) * l2Mass f
    have henergy := (prime_archimedean_energy_identity
      Z f B hsupport hZero hArch).1
    have henergyRe := congrArg Complex.re henergy
    simp only [Complex.ofReal_re] at henergyRe
    dsimp only [V]
    constructor <;> linarith [hNorm.1, hNorm.2, henergyRe]

end D5.S3.Weil.Separator.LiteralRationalBoundaryCertified
