/- GID: D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate
   mirror-E: none(waiver:fixed-grid-rational-boundary-rate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified; instance=D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate.fixedGridRateCertified
   digest: Fixed rational grids have explicit component amplitudes and dyadic mesh-width decay. -/

import D5.S3.Weil.Separator.LiteralRationalBoundaryGrid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGridRate

open D5.S3.Weil.Separator.LiteralRationalBoundaryGrid
open Filter Topology Set Polynomial
open scoped BigOperators ContDiff
open D5.S0.Certificates.BoxCover.RationalIntervalExpression

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
-- The rate proof expands the full dyadic mesh and scalar error calculation.
/-- A fixed literal-family grid has explicit rational amplitude bounds and a
mesh-plus-scalar dyadic width bound for its completed-square enclosure. -/
theorem fixedGridRateCertified (R : Nat) (hR : 0 < R)
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
    |gr.2.2.1.1| <= Ip ∧ |gr.2.2.1.2| <= Ip ∧
    |gr.2.2.2.1.1| <= Iq ∧ |gr.2.2.2.1.2| <= Iq ∧
      gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <=
        Cmesh / (N : Rat) + Cscalar * delta := by
    intro N Br eta raw cellSize Jp Jq sf gr delta E T Ap Aq Ip Iq Kmp Kmq Ksp Ksq
      Cmesh Cscalar
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
        |(polyBox r Br eta (center i)).1| <=
          valueBound r Br + Br * derivBound r Br / 2 ∧
        |(polyBox r Br eta (center i)).2| <=
          valueBound r Br + Br * derivBound r Br / 2 := by
      have hpi := hpoint i hi.le
      have hpn := hpoint (i + 1) hi
      have hci : 0 <= center i ∧ center i <= Br := by
        dsimp [center]
        constructor <;> linarith
      have hcabs : |center i| <= Br := by
        rw [abs_of_nonneg hci.1]
        exact hci.2
      have heval : |r.eval (center i)| <= valueBound r Br := by
        rw [eval_eq_sum]
        calc
          _ <= ∑ n ∈ r.support, |r.coeff n * center i ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ n ∈ r.support, |r.coeff n| * Br ^ n := by
            apply Finset.sum_le_sum
            intro n hn
            rw [abs_mul, abs_pow]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg _) (by simpa using hcabs) n)
              (abs_nonneg _)
          _ = valueBound r Br := by simp only [sum_def]
      have hevalNeg : |r.eval (-(center i))| <= valueBound r Br := by
        rw [eval_eq_sum]
        calc
          _ <= ∑ n ∈ r.support, |r.coeff n * (-(center i)) ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ n ∈ r.support, |r.coeff n| * Br ^ n := by
            apply Finset.sum_le_sum
            intro n hn
            rw [abs_mul, abs_pow, abs_neg]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg _) (by simpa using hcabs) n)
              (abs_nonneg _)
          _ = valueBound r Br := by simp only [sum_def]
      have hv : |evenEval r (center i)| <= valueBound r Br := by
        dsimp only [evenEval]
        rw [abs_div, abs_of_pos (show (0 : Rat) < 2 by norm_num)]
        calc
          |r.eval (center i) + r.eval (-center i)| / 2 <=
              (|r.eval (center i)| + |r.eval (-center i)|) / 2 :=
            div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
          _ <= valueBound r Br := by linarith [heval, hevalNeg]
      have hw : 0 <= derivBound r Br * eta / 2 := by
        exact div_nonneg (mul_nonneg (hd r) heta.le) (by norm_num)
      have hwB : derivBound r Br * eta / 2 <= Br * derivBound r Br / 2 := by
        have := mul_le_mul_of_nonneg_left hetaB (hd r)
        linarith
      obtain ⟨hvl, hvu⟩ := abs_le.mp hv
      refine ⟨(by dsimp; linarith), ?_, ?_⟩ <;>
        dsimp <;> rw [abs_le] <;> constructor <;> linarith
    have hcutOrder (i : Nat) (hi : i < N) : (abox i).1 <= (abox i).2 := by
      have hti : (t (i + 1) : Real) <= (t i : Real) := by
        have hsx : xq i <= xq (i + 1) := by linarith [hstep i]
        have hxdiv : (xq i : Real) / (R : Real) <=
            (xq (i + 1) : Real) / (R : Real) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hsx) hRr.le
        dsimp [t]
        push_cast
        linarith
      exact_mod_cast (hcp (i + 1) hi).2.1.trans
        ((Real.smoothTransition.monotone hti).trans (hcp i hi.le).2.2.1)
    have hweightOrder (i : Nat) (hi : i < N) : (wbox i).1 <= (wbox i).2 := by
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
      have hu : Real.exp ((xq (i + 1) : Real) / 2) +
          Real.exp (-(xq i : Real) / 2) <= ((wbox i).2 : Real) := by
        dsimp [wbox]
        rw [hepNode (i + 1) hi, hemNode i hi.le]
        push_cast
        exact add_le_add
          (by simpa only [Rat.cast_div, Rat.cast_ofNat] using
            (hscalar (xq (i + 1) / 2)).2.1.2)
          (by simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using
            (hscalar (-xq i / 2)).2.1.2)
      exact_mod_cast hlo.trans ((add_le_add
        (Real.exp_monotone (div_le_div_of_nonneg_right hxi (by norm_num)))
        (Real.exp_monotone
          (div_le_div_of_nonneg_right (neg_le_neg hxi) (by norm_num)))).trans hu)
    have rowsize : gr.2.1.size = N := by
      change (Array.ofFn (fun _i : Fin N => _)).size = N
      exact Array.size_ofFn
    have hrow (i : Nat) (hi : i < gr.2.1.size) :
        gr.2.1[i] = ((box p i, ex p i), (box q i, ex q i)) := by
      have hiN : i < N := by simpa only [rowsize] using hi
      change (Array.ofFn _)[i]'(by simpa only [Array.size_ofFn] using hiN) = _
      rw [Array.getElem_ofFn]
      rfl
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
    have rate :
        |gr.2.2.1.1| <= Ip ∧ |gr.2.2.1.2| <= Ip ∧
        |gr.2.2.2.1.1| <= Iq ∧ |gr.2.2.2.1.2| <= Iq ∧
        gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <=
          Cmesh / (N : Rat) + Cscalar * delta := by
      as_aux_lemma =>
      have coarse :
          0 <= T ∧
          (∀ r : Rat[X], 0 <= valueBound r Br + Br * derivBound r Br / 2) ∧
          (∀ (r : Rat[X]) (i : Nat), i < N ->
            let Ar := valueBound r Br + Br * derivBound r Br / 2
            let vi := mulBox (wbox i) (mulBox (abox i) (polyBox r Br eta (center i)))
            vi.1 <= vi.2 ∧ |vi.1| <= 2 * T * Ar ∧ |vi.2| <= 2 * T * Ar ∧
            vi.2 - vi.1 <=
              2 * T * derivBound r Br * eta +
              T * Ar * ((cp i).2 - (cp (i + 1)).1) +
              2 * Ar * ((wbox i).2 - (wbox i).1)) := by
        as_aux_lemma =>
        have hEexp : Real.exp (R : Real) <= (E : Real) := by
          simpa only [E, Rat.cast_natCast] using
            (boundaryExpCertified_v1 (R : Rat) 0).property.2.2.2.2.1
        have hE1 : (1 : Rat) <= E := by
          have hR0 : (0 : Real) <= R := Nat.cast_nonneg R
          have : (1 : Real) <= (E : Real) := by
            rw [<- Real.exp_zero]
            exact (Real.exp_monotone hR0).trans hEexp
          exact_mod_cast this
        have hT : 0 <= T := by dsimp [T]; linarith
        have hA (r : Rat[X]) : 0 <= valueBound r Br + Br * derivBound r Br / 2 := by
          exact add_nonneg (hm r) (div_nonneg (mul_nonneg hB.le (hd r)) (by norm_num))
        have hscalarCap (u cap C : Rat) (hu : u <= cap)
            (hcap : Real.exp (cap : Real) <= (C : Real)) :
            let a := (boundaryExpCertified_v1 u s).val.2
            (-1 : Rat) <= a.1 ∧ a.2 <= C + 1 := by
          intro a
          have hs := hscalar u
          have hw : (((a.2 - a.1 : Rat) : Real) <= (1 : Rat)) := by
            exact_mod_cast hs.2.2.trans hdelta1
          have huexp : Real.exp (u : Real) <= (C : Real) :=
            (Real.exp_monotone (by exact_mod_cast hu)).trans hcap
          have hlo : (-1 : Real) <= (a.1 : Real) := by
            push_cast at hw
            linarith [hs.2.1.2, Real.exp_pos (u : Real)]
          have hup : (a.2 : Real) <= ((C + 1 : Rat) : Real) := by
            push_cast at hw ⊢
            linarith [hs.2.1.1, huexp]
          exact ⟨by exact_mod_cast hlo, by exact_mod_cast hup⟩
        have hweightAmp (i : Nat) (hi : i < N) :
            (wbox i).1 <= (wbox i).2 ∧ |(wbox i).1| <= T ∧ |(wbox i).2| <= T := by
          have hpi := hpoint i hi.le
          have hpn := hpoint (i + 1) hi
          have hepCap (j : Nat) (hj : j <= N) :
              (-1 : Rat) <= (ep j).1 ∧ (ep j).2 <= E + 1 := by
            rw [hepNode j hj]
            apply hscalarCap (xq j / 2) R E
            · have hpj := hpoint j hj
              dsimp [Br] at hpj
              linarith
            · exact hEexp
          have hemCap (j : Nat) (hj : j <= N) :
              (-1 : Rat) <= (em j).1 ∧ (em j).2 <= 2 := by
            rw [hemNode j hj]
            have hzero : Real.exp (((0 : Rat) : Real)) <= (((1 : Rat) : Real)) := by simp
            simpa only [zero_add, one_add_one_eq_two] using
              hscalarCap (-xq j / 2) 0 1 (by have := (hpoint j hj).1; linarith) hzero
          have hw : (wbox i).1 <= (wbox i).2 := hweightOrder i hi
          have hlo : (-2 : Rat) <= (wbox i).1 := by
            dsimp [wbox]
            linarith [(hepCap i hi.le).1, (hemCap (i + 1) hi).1]
          have hup : (wbox i).2 <= T := by
            dsimp [wbox, T]
            linarith [(hepCap (i + 1) hi).2, (hemCap i hi.le).2]
          have hTl : (2 : Rat) <= T := by dsimp [T]; linarith
          have hw0 : 0 <= (wbox i).2 := by
            have hp0 := (boundaryExpCertified_v1 (xq (i + 1) / 2) s).property.2.2.2.2.1
            have hm0 := (boundaryExpCertified_v1 (-xq i / 2) s).property.2.2.2.2.1
            have hp0' : (0 : Real) < ((ep (i + 1)).2 : Real) := by
              rw [hepNode (i + 1) hi]
              simpa only [Rat.cast_div, Rat.cast_ofNat] using
                (Real.exp_pos (((xq (i + 1) / 2 : Rat) : Real))).trans_le hp0
            have hm0' : (0 : Real) < ((em i).2 : Real) := by
              rw [hemNode i hi.le]
              simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using
                (Real.exp_pos (((-xq i / 2 : Rat) : Real))).trans_le hm0
            have : (0 : Real) <= ((wbox i).2 : Real) := by
              dsimp [wbox]
              push_cast
              linarith
            exact_mod_cast this
          refine ⟨hw, ?_, ?_⟩
          · rw [abs_le]
            exact ⟨(by linarith), hw.trans hup⟩
          · rw [abs_of_nonneg hw0]
            exact hup
        have hinner (r : Rat[X]) (i : Nat) (hi : i < N) :
            let Ar := valueBound r Br + Br * derivBound r Br / 2
            let inner := mulBox (abox i) (polyBox r Br eta (center i))
            inner.1 <= inner.2 ∧ |inner.1| <= 2 * Ar ∧ |inner.2| <= 2 * Ar ∧
            inner.2 - inner.1 <=
              2 * derivBound r Br * eta + Ar * ((cp i).2 - (cp (i + 1)).1) := by
          intro Ar inner
          have hh := rationalIntervalMul_bounds
            (abox i) (polyBox r Br eta (center i)) 2 Ar
            (hcutOrder i hi) (hpoly r i hi).1 (by norm_num) (hA r)
            (hcp (i + 1) hi).2.2.2.2.1 (hcp i hi.le).2.2.2.2.2
            (hpoly r i hi).2.1 (hpoly r i hi).2.2
          refine ⟨hh.1, by simpa using hh.2.1, by simpa using hh.2.2.1, ?_⟩
          have hpw : (polyBox r Br eta (center i)).2 -
              (polyBox r Br eta (center i)).1 = derivBound r Br * eta := by
            dsimp
            ring
          dsimp [abox] at hh ⊢
          rw [hpw] at hh
          nlinarith [hh.2.2.2]
        have houter : ∀ (r : Rat[X]) (i : Nat), i < N ->
            let Ar := valueBound r Br + Br * derivBound r Br / 2
            let vi := mulBox (wbox i) (mulBox (abox i) (polyBox r Br eta (center i)))
            vi.1 <= vi.2 ∧ |vi.1| <= 2 * T * Ar ∧ |vi.2| <= 2 * T * Ar ∧
            vi.2 - vi.1 <=
              2 * T * derivBound r Br * eta +
              T * Ar * ((cp i).2 - (cp (i + 1)).1) +
              2 * Ar * ((wbox i).2 - (wbox i).1) := by
          as_aux_lemma =>
          intro r i hi
          intro Ar vi
          let inner := mulBox (abox i) (polyBox r Br eta (center i))
          have hin := hinner r i hi
          have hw := hweightAmp i hi
          have hh := rationalIntervalMul_bounds (wbox i)
            inner T (2 * Ar)
            hw.1 hin.1 hT (mul_nonneg (by norm_num) (hA r))
            hw.2.1 hw.2.2 hin.2.1 hin.2.2.1
          refine ⟨hh.1, ?_, ?_, ?_⟩
          · calc
              |vi.1| <= T * (2 * Ar) := hh.2.1
              _ = 2 * T * Ar := by ring
          · calc
              |vi.2| <= T * (2 * Ar) := hh.2.2.1
              _ = 2 * T * Ar := by ring
          have hinScaled := mul_le_mul_of_nonneg_left hin.2.2.2 hT
          calc
            vi.2 - vi.1 <= T * (inner.2 - inner.1) +
                2 * Ar * ((wbox i).2 - (wbox i).1) := hh.2.2.2
            _ <= T * (2 * derivBound r Br * eta +
                Ar * ((cp i).2 - (cp (i + 1)).1)) +
                2 * Ar * ((wbox i).2 - (wbox i).1) :=
              add_le_add hinScaled le_rfl
            _ = 2 * T * derivBound r Br * eta +
                T * Ar * ((cp i).2 - (cp (i + 1)).1) +
                2 * Ar * ((wbox i).2 - (wbox i).1) := by ring
        exact ⟨hT, hA, houter⟩
      obtain ⟨hT, hA, houter⟩ := coarse
      have amplitudes :
          (|gr.2.2.1.1| <= Ip ∧ |gr.2.2.1.2| <= Ip) ∧
          (|gr.2.2.2.1.1| <= Iq ∧ |gr.2.2.2.1.2| <= Iq) := by
        as_aux_lemma =>
        have hexBounds (r : Rat[X]) (i : Nat) :
          bounds (ex r i) =
            mulBox (wbox i) (mulBox (abox i) (polyBox r Br eta (center i))) := rfl
        have hcomponentAmp (r : Rat[X]) (J : Rat × Rat)
          (hJ : J = (eta * ∑ i ∈ Finset.range N, (bounds (ex r i)).1,
            eta * ∑ i ∈ Finset.range N, (bounds (ex r i)).2)) :
          let Ar := valueBound r Br + Br * derivBound r Br / 2
          let Ir := 2 * Br * T * Ar
          |J.1| <= Ir ∧ |J.2| <= Ir := by
          intro Ar Ir
          have hsumAmp (side : (Rat × Rat) -> Rat)
              (hside : ∀ i, i < N -> |side (bounds (ex r i))| <= 2 * T * Ar) :
              |∑ i ∈ Finset.range N, side (bounds (ex r i))| <= N * (2 * T * Ar) := by
            calc
              _ <= ∑ i ∈ Finset.range N, |side (bounds (ex r i))| :=
                Finset.abs_sum_le_sum_abs _ _
              _ <= ∑ _i ∈ Finset.range N, 2 * T * Ar :=
                Finset.sum_le_sum (fun i hi => hside i (Finset.mem_range.mp hi))
              _ = _ := by simp
          have hlo := hsumAmp Prod.fst (fun i hi => by
            rw [hexBounds]
            exact (houter r i hi).2.1)
          have hup := hsumAmp Prod.snd (fun i hi => by
            rw [hexBounds]
            exact (houter r i hi).2.2.1)
          rw [hJ]
          constructor <;> rw [abs_mul, abs_of_nonneg heta.le]
          · calc
              eta * |∑ i ∈ Finset.range N, (bounds (ex r i)).1| <=
                  eta * (N * (2 * T * Ar)) := mul_le_mul_of_nonneg_left hlo heta.le
              _ = Ir := by dsimp [eta, Ir]; field_simp
          · calc
              eta * |∑ i ∈ Finset.range N, (bounds (ex r i)).2| <=
                  eta * (N * (2 * T * Ar)) := mul_le_mul_of_nonneg_left hup heta.le
              _ = Ir := by dsimp [eta, Ir]; field_simp
        have hpAmp : |gr.2.2.1.1| <= Ip ∧ |gr.2.2.1.2| <= Ip := by
          simpa only [Ap, Ip] using hcomponentAmp p gr.2.2.1 gJp
        have hqAmp : |gr.2.2.2.1.1| <= Iq ∧ |gr.2.2.2.1.2| <= Iq := by
          simpa only [Aq, Iq] using hcomponentAmp q gr.2.2.2.1 gJq
        exact ⟨hpAmp, hqAmp⟩
      have hpAmp := amplitudes.1
      have hqAmp := amplitudes.2
      have hEexp : Real.exp (R : Real) <= (E : Real) := by
        simpa only [E, Rat.cast_natCast] using
          (boundaryExpCertified_v1 (R : Rat) 0).property.2.2.2.2.1
      have hexBounds (r : Rat[X]) (i : Nat) :
          bounds (ex r i) =
            mulBox (wbox i) (mulBox (abox i) (polyBox r Br eta (center i))) := rfl
      have hcutTel :
          (∑ i ∈ Finset.range N, ((cp i).2 - (cp (i + 1)).1)) =
            1 + ∑ i ∈ Finset.range N, ((cp i).2 - (cp i).1) := by
        calc
          _ = (∑ i ∈ Finset.range N, ((cp i).1 - (cp (i + 1)).1)) +
              ∑ i ∈ Finset.range N, ((cp i).2 - (cp i).1) := by
            have hterm (i : Nat) : (cp i).2 - (cp (i + 1)).1 =
                ((cp i).1 - (cp (i + 1)).1) + ((cp i).2 - (cp i).1) := by ring
            simp_rw [hterm, Finset.sum_add_distrib]
          _ = _ := by rw [Finset.sum_range_sub', cp0, cpN]; norm_num
      have hcutSum :
          (∑ i ∈ Finset.range N, ((cp i).2 - (cp (i + 1)).1)) <=
            1 + N * delta := by
        rw [hcutTel]
        gcongr
        calc
          _ <= ∑ _i ∈ Finset.range N, delta :=
            Finset.sum_le_sum (fun i hi =>
              (hcp i (Nat.le_of_lt (Finset.mem_range.mp hi))).2.2.2.1)
          _ = _ := by simp
      have hepUp (i : Nat) (hi : i <= N) :
          ((ep i).2 : Real) <= Real.exp ((xq i : Real) / 2) + (delta : Real) := by
        rw [hepNode i hi]
        have hs := hscalar (xq i / 2)
        have hw : ((((boundaryExpCertified_v1 (xq i / 2) s).val.2.2 -
            (boundaryExpCertified_v1 (xq i / 2) s).val.2.1 : Rat) : Real) <=
            (delta : Real)) := by
          exact_mod_cast hs.2.2
        have hl : (((boundaryExpCertified_v1 (xq i / 2) s).val.2.1 : Rat) : Real) <=
            Real.exp ((xq i : Real) / 2) := by
          simpa only [Rat.cast_div, Rat.cast_ofNat] using hs.2.1.1
        push_cast at hw
        linarith
      have hepLow (i : Nat) (hi : i <= N) :
          Real.exp ((xq i : Real) / 2) - (delta : Real) <= ((ep i).1 : Real) := by
        rw [hepNode i hi]
        have hs := hscalar (xq i / 2)
        have hw : ((((boundaryExpCertified_v1 (xq i / 2) s).val.2.2 -
            (boundaryExpCertified_v1 (xq i / 2) s).val.2.1 : Rat) : Real) <=
            (delta : Real)) := by
          exact_mod_cast hs.2.2
        have hu : Real.exp ((xq i : Real) / 2) <=
            (((boundaryExpCertified_v1 (xq i / 2) s).val.2.2 : Rat) : Real) := by
          simpa only [Rat.cast_div, Rat.cast_ofNat] using hs.2.1.2
        push_cast at hw
        linarith
      have hemUp (i : Nat) (hi : i <= N) :
          ((em i).2 : Real) <= Real.exp (-(xq i : Real) / 2) + (delta : Real) := by
        rw [hemNode i hi]
        have hs := hscalar (-xq i / 2)
        have hw : ((((boundaryExpCertified_v1 (-xq i / 2) s).val.2.2 -
            (boundaryExpCertified_v1 (-xq i / 2) s).val.2.1 : Rat) : Real) <=
            (delta : Real)) := by
          exact_mod_cast hs.2.2
        have hl : (((boundaryExpCertified_v1 (-xq i / 2) s).val.2.1 : Rat) : Real) <=
            Real.exp (-(xq i : Real) / 2) := by
          simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using hs.2.1.1
        push_cast at hw
        linarith
      have hemLow (i : Nat) (hi : i <= N) :
          Real.exp (-(xq i : Real) / 2) - (delta : Real) <= ((em i).1 : Real) := by
        rw [hemNode i hi]
        have hs := hscalar (-xq i / 2)
        have hw : ((((boundaryExpCertified_v1 (-xq i / 2) s).val.2.2 -
            (boundaryExpCertified_v1 (-xq i / 2) s).val.2.1 : Rat) : Real) <=
            (delta : Real)) := by
          exact_mod_cast hs.2.2
        have hu : Real.exp (-(xq i : Real) / 2) <=
            (((boundaryExpCertified_v1 (-xq i / 2) s).val.2.2 : Rat) : Real) := by
          simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using hs.2.1.2
        push_cast at hw
        linarith
      let xp : Nat -> Real := fun i => Real.exp ((xq i : Real) / 2)
      let xm : Nat -> Real := fun i => Real.exp (-(xq i : Real) / 2)
      have hweightCell (i : Nat) (hi : i < N) :
          (((wbox i).2 - (wbox i).1 : Rat) : Real) <=
            (xp (i + 1) - xp i) + (xm i - xm (i + 1)) + 4 * (delta : Real) := by
        dsimp [wbox, xp, xm]
        push_cast
        linarith [hepUp (i + 1) hi, hemUp i hi.le,
          hepLow i hi.le, hemLow (i + 1) hi]
      have hweightSumReal :
          (((∑ i ∈ Finset.range N, ((wbox i).2 - (wbox i).1)) : Rat) : Real) <=
            (E + 4 * N * delta : Rat) := by
        have hsum :
            (((∑ i ∈ Finset.range N, ((wbox i).2 - (wbox i).1)) : Rat) : Real) <=
              (xp N - xp 0) + (xm 0 - xm N) + 4 * (N : Real) * (delta : Real) := by
          push_cast
          calc
            _ <= ∑ i ∈ Finset.range N,
                ((xp (i + 1) - xp i) + (xm i - xm (i + 1)) + 4 * (delta : Real)) :=
              Finset.sum_le_sum (fun i hi => by
                simpa only [Rat.cast_sub] using hweightCell i (Finset.mem_range.mp hi))
            _ = (xp N - xp 0) + (xm 0 - xm N) + 4 * (N : Real) * (delta : Real) := by
              have hp := Finset.sum_range_sub' xp N
              have hm' := Finset.sum_range_sub' xm N
              have hp' := congrArg Neg.neg hp
              simp only [<- Finset.sum_neg_distrib, neg_sub] at hp'
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hp', hm']
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
        have hxpN : xp N = Real.exp (R : Real) := by
          dsimp [xp]
          rw [hxN]
          dsimp [Br]
          push_cast
          congr 1
          ring
        have hxp0 : xp 0 = 1 := by simp [xp, hx0]
        have hxm0 : xm 0 = 1 := by simp [xm, hx0]
        rw [hxpN, hxp0, hxm0] at hsum
        have hmpos : 0 <= xm N := Real.exp_pos _ |>.le
        calc
          _ <= Real.exp (R : Real) - 1 + (1 - xm N) +
              4 * (N : Real) * (delta : Real) := hsum
          _ <= (E : Real) + 4 * (N : Real) * (delta : Real) := by linarith
          _ = ((E + 4 * N * delta : Rat) : Real) := by push_cast; ring
      have hweightSum :
          (∑ i ∈ Finset.range N, ((wbox i).2 - (wbox i).1)) <=
            E + 4 * N * delta := by
        exact_mod_cast hweightSumReal
      have hcomponentWidth (r : Rat[X]) (J : Rat × Rat)
          (hJ : J = (eta * ∑ i ∈ Finset.range N, (bounds (ex r i)).1,
            eta * ∑ i ∈ Finset.range N, (bounds (ex r i)).2)) :
          let Ar := valueBound r Br + Br * derivBound r Br / 2
          let Km := Br * (2 * T * Br * derivBound r Br + (T + 2 * E) * Ar)
          let Ks := Br * Ar * (T + 8)
          J.2 - J.1 <= Km / (N : Rat) + Ks * delta := by
        as_aux_lemma =>
        intro Ar Km Ks
        have hsumOuter :
            (∑ i ∈ Finset.range N,
              ((bounds (ex r i)).2 - (bounds (ex r i)).1)) <=
            N * (2 * T * derivBound r Br * eta) +
              T * Ar * (1 + N * delta) + 2 * Ar * (E + 4 * N * delta) := by
          calc
            _ <= ∑ i ∈ Finset.range N,
                (2 * T * derivBound r Br * eta +
                  T * Ar * ((cp i).2 - (cp (i + 1)).1) +
                  2 * Ar * ((wbox i).2 - (wbox i).1)) :=
              Finset.sum_le_sum (fun i hi => by
                rw [hexBounds]
                exact (houter r i (Finset.mem_range.mp hi)).2.2.2)
            _ = N * (2 * T * derivBound r Br * eta) +
                T * Ar * (∑ i ∈ Finset.range N, ((cp i).2 - (cp (i + 1)).1)) +
                2 * Ar * (∑ i ∈ Finset.range N, ((wbox i).2 - (wbox i).1)) := by
              simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul, <- Finset.mul_sum]
            _ <= N * (2 * T * derivBound r Br * eta) +
                T * Ar * (1 + N * delta) + 2 * Ar * (E + 4 * N * delta) := by
              have hc := mul_le_mul_of_nonneg_left hcutSum (mul_nonneg hT (hA r))
              have hw := mul_le_mul_of_nonneg_left hweightSum
                (mul_nonneg (show (0 : Rat) <= 2 by norm_num) (hA r))
              exact add_le_add (add_le_add le_rfl hc) hw
        rw [hJ]
        have hsumRewrite :
            eta * (∑ i ∈ Finset.range N, (bounds (ex r i)).2) -
              eta * (∑ i ∈ Finset.range N, (bounds (ex r i)).1) =
            eta * (∑ i ∈ Finset.range N,
              ((bounds (ex r i)).2 - (bounds (ex r i)).1)) := by
          rw [Finset.sum_sub_distrib]
          ring
        rw [hsumRewrite]
        calc
          _ <= eta * (N * (2 * T * derivBound r Br * eta) +
              T * Ar * (1 + N * delta) + 2 * Ar * (E + 4 * N * delta)) :=
            mul_le_mul_of_nonneg_left hsumOuter heta.le
          _ = Km / (N : Rat) + Ks * delta := by
            dsimp [eta, Km, Ks]
            field_simp
            ring
      have hpWidth : gr.2.2.1.2 - gr.2.2.1.1 <=
          Kmp / (N : Rat) + Ksp * delta := by
        simpa only [Ap, Kmp, Ksp] using hcomponentWidth p gr.2.2.1 gJp
      have hqWidth : gr.2.2.2.1.2 - gr.2.2.2.1.1 <=
          Kmq / (N : Rat) + Ksq * delta := by
        simpa only [Aq, Kmq, Ksq] using hcomponentWidth q gr.2.2.2.1 gJq
      have hpOrder : gr.2.2.1.1 <= gr.2.2.1.2 := by
        rw [gJp]
        apply mul_le_mul_of_nonneg_left _ heta.le
        exact Finset.sum_le_sum (fun i hi =>
          (houter p i (Finset.mem_range.mp hi)).1)
      have hqOrder : gr.2.2.2.1.1 <= gr.2.2.2.1.2 := by
        rw [gJq]
        apply mul_le_mul_of_nonneg_left _ heta.le
        exact Finset.sum_le_sum (fun i hi =>
          (houter q i (Finset.mem_range.mp hi)).1)
      have hIp : 0 <= Ip := by
        dsimp [Ip, Ap]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB.le) hT) (hA p)
      have hIq : 0 <= Iq := by
        dsimp [Iq, Aq]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB.le) hT) (hA q)
      have hpSq := rationalIntervalSquare_width
        gr.2.2.1 Ip hpOrder hIp hpAmp.1 hpAmp.2
      have hqSq := rationalIntervalSquare_width
        gr.2.2.2.1 Iq hqOrder hIq hqAmp.1 hqAmp.2
      have hpScaled := mul_le_mul_of_nonneg_left hpWidth
        (mul_nonneg (show (0 : Rat) <= 4 by norm_num) hIp)
      have hqScaled := mul_le_mul_of_nonneg_left hqWidth
        (mul_nonneg (show (0 : Rat) <= 4 by norm_num) hIq)
      have hfinalWidth : gr.2.2.2.2.1.2 - gr.2.2.2.2.1.1 <=
          Cmesh / (N : Rat) + Cscalar * delta := by
        change 2 * ((sqBox gr.2.2.1).2 + (sqBox gr.2.2.2.1).2) -
          2 * ((sqBox gr.2.2.1).1 + (sqBox gr.2.2.2.1).1) <= _
        calc
          _ = 2 * ((sqBox gr.2.2.1).2 - (sqBox gr.2.2.1).1) +
              2 * ((sqBox gr.2.2.2.1).2 - (sqBox gr.2.2.2.1).1) := by ring
          _ <= 4 * Ip * (gr.2.2.1.2 - gr.2.2.1.1) +
              4 * Iq * (gr.2.2.2.1.2 - gr.2.2.2.1.1) := by nlinarith
          _ <= 4 * Ip * (Kmp / (N : Rat) + Ksp * delta) +
              4 * Iq * (Kmq / (N : Rat) + Ksq * delta) := by
            exact add_le_add hpScaled hqScaled
          _ = Cmesh / (N : Rat) + Cscalar * delta := by
            dsimp [Cmesh, Cscalar]
            field_simp
            ring
      exact ⟨hpAmp.1, hpAmp.2, hqAmp.1, hqAmp.2, hfinalWidth⟩
    exact rate

end D5.S3.Weil.Separator.LiteralRationalBoundaryFixedGridRate
