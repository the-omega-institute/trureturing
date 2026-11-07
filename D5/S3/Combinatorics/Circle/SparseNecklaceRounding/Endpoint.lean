/- GID: D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact physical sparse-necklace target and explicit threshold-rounding candidate. -/
module
public import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Arithmetic
public import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Rounding
public import Mathlib.Algebra.BigOperators.Fin
public import D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets

@[expose] public section

/-! Physical necklace streams and the uniform rounding conclusion. -/
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open SourceWidth RunFirstEarTransport
open scoped BigOperators

def gapList {p : ℕ} (gaps : Fin p → ℕ) : List ℕ := (List.finRange p).map gaps

def period {p : ℕ} (gaps : Fin p → ℕ) : ℕ := ∑ j, gaps j

/-- The literal seed from the quantified statement, not an unconstrained source. -/
def necklaceSeed {p : ℕ} (gaps : Fin p → ℕ) : ℕ :=
  ∑ j : Fin p, 2 ^ (∑ q ∈ Finset.univ.filter (fun q : Fin p => q < j), gaps q)

def chainStart {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℕ :=
  (((gapList gaps).reverse).take r).sum

def chainGap {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℕ :=
  ((gapList gaps).reverse[r]?).getD 0

def cyclicHead {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℤ :=
  cutHead ((gapList gaps).take (p - r)) ((gapList gaps).drop (p - r))

def winding {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℤ :=
  cutCharge ((gapList gaps).drop (p - r))

def demand {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℤ :=
  (modulus (period gaps) - cyclicHead gaps (r + 1)) / 2

def terminalCharge {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℤ :=
  (winding gaps (r + 1) + 1) / 2

/-- Cumulative demand in the reverse-chain terminal order. -/
def threshold {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℤ :=
  ((List.range p).drop r |>.map (demand gaps)).sum

/-- Rejecting an out-of-range index is total and creates no new label. The
partition proof must show that every generated index is in range. -/
def labelAt (k i : ℕ) : Option (Fin k) := if hi : i < k then some ⟨i,hi⟩ else none

def positiveIndices {p : ℕ} (gaps : Fin p → ℕ) : List ℕ :=
  (List.range p).reverse.flatMap (fun r =>
    (List.range (chainGap gaps r - 1)).map (fun t => chainStart gaps r + t))

def positiveLabels {p : ℕ} (gaps : Fin p → ℕ) : List (Fin (period gaps)) :=
  (positiveIndices gaps).filterMap (labelAt (period gaps))

def terminalIndex {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : ℕ :=
  chainStart gaps (r + 1) - 1

def thresholdTerminals {p : ℕ} (gaps : Fin p → ℕ) :
    List (Fin (period gaps) × ℚ) :=
  (List.range p).reverse.filterMap (fun r =>
    (labelAt (period gaps) (terminalIndex gaps r)).map
      (fun i => (i,(threshold gaps r : ℚ))))

/-- A direct traversal of the two streams. Equality inserts the terminal after
the completed positive label in both words. Only strict inequality creates a
two-label rounding block. No physical path feasibility is an input. -/
def thresholdBlocks {α : Type*} (mass : α → ℚ) :
    List α → List (α × ℚ) → ℚ → List (RoundBlock α)
  | [], ts, _ => ts.map (fun t => .one t.1)
  | i :: ps, [], x => .one i :: thresholdBlocks mass ps [] (x + mass i)
  | i :: ps, (j,d) :: ts, x =>
      if d < x + mass i then
        .cut i j ((d - x) / mass i) :: thresholdBlocks mass ps ts (x + mass i)
      else if d = x + mass i then
        .one i :: .one j :: thresholdBlocks mass ps ts (x + mass i)
      else
        .one i :: thresholdBlocks mass ps ((j,d) :: ts) (x + mass i)

def necklaceBlocks {p : ℕ} (gaps : Fin p → ℕ) :
    List (RoundBlock (Fin (period gaps))) :=
  thresholdBlocks (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))
    (positiveLabels gaps) (thresholdTerminals gaps) 0

def sigmaPlus {p : ℕ} (gaps : Fin p → ℕ) : List (Fin (period gaps)) :=
  plusWord (necklaceBlocks gaps)

def sigmaMinus {p : ℕ} (gaps : Fin p → ℕ) : List (Fin (period gaps)) :=
  minusWord (necklaceBlocks gaps)

def oldPrefix (k e : ℕ) (sigma : List (Fin k)) (q : ℕ) : ℤ :=
  ((sigma.take (q - 1)).map (actualSource k e)).sum

def newPrefix (k e : ℕ) (sigma : List (Fin k)) (q : ℕ) : ℤ :=
  (((earWord k sigma 0).take q).map (actualSource (k + 1) (2 * e))).sum

structure CornerRecord (k : ℕ) where
  prefixLength : ℕ
  positive : Fin k
  terminal : Fin k

/-- Strictness is tested at the specified terminal's native demand threshold
in the actual positive list; endpoint hits are excluded. -/
def IsStrictSplit {p : ℕ} (gaps : Fin p → ℕ)
    (i j : Fin (period gaps)) : Prop :=
  let pos := positiveLabels gaps
  let before := ((pos.take (pos.idxOf i)).map
    (actualSource (period gaps) (necklaceSeed gaps))).sum
  ∃ r : ℕ, r < p ∧ j.val = terminalIndex gaps r ∧
    before < threshold gaps r ∧
    threshold gaps r < before + actualSource (period gaps) (necklaceSeed gaps) i

/-- Full physical conclusion. The only outer assumptions in the intended
theorem are p>=1 and gaps>=2. This predicate adds no feasibility, certificate,
gcd, primitivity, distinct-coordinate or bounded-gap assumption. -/
def PhysicalRounding {p : ℕ} (gaps : Fin p → ℕ) : Prop :=
  let k := period gaps
  let e := necklaceSeed gaps
  let N := modulus k
  let H := N / 2
  ∃ wp wm : List (Fin k), ∃ cs : List (CornerRecord k),
    wp.Perm (List.finRange k) ∧ wm.Perm (List.finRange k) ∧
    (earWord k wp 0).Perm (List.finRange (k + 1)) ∧
    (earWord k wm 0).Perm (List.finRange (k + 1)) ∧
    (earWord k wp 0).head? = some (Fin.last k) ∧
    (earWord k wm 0).head? = some (Fin.last k) ∧
    actualSource (k + 1) (2 * e) (Fin.last k) = (e : ℤ) ∧
    oldPrefix k e wp (k + 1) = 0 ∧ newPrefix k e wp (k + 1) = 0 ∧
    oldPrefix k e wm (k + 1) = 0 ∧ newPrefix k e wm (k + 1) = 0 ∧
    (∀ q : ℕ, 0 ≤ oldPrefix k e wp q ∧ 0 ≤ newPrefix k e wp q) ∧
    (∀ q : ℕ, oldPrefix k e wm q ≤ H ∧ newPrefix k e wm q ≤ N) ∧
    cs.length ≤ p - 1 ∧
    (cs.map CornerRecord.prefixLength).Nodup ∧
    (cs.flatMap (fun c => [c.positive,c.terminal])).Nodup ∧
    (∀ c ∈ cs,
      0 < actualSource k e c.positive ∧
      0 < actualSource (k + 1) (2 * e) c.positive.castSucc ∧
      actualSource k e c.terminal < 0 ∧
      actualSource (k + 1) (2 * e) c.terminal.castSucc < 0 ∧
      IsStrictSplit gaps c.positive c.terminal ∧
      ∃ u v u' v' : List (Fin k),
        wp = u ++ [c.positive,c.terminal] ++ v ∧
        wm = u' ++ [c.terminal,c.positive] ++ v' ∧
        c.prefixLength = u.length + 2 ∧ c.prefixLength = u'.length + 2) ∧
    swapAlong (cs.map (fun c => (c.positive,c.terminal))) wp = wm ∧
    (∀ q : ℕ, H < oldPrefix k e wp q ∨ N < newPrefix k e wp q →
      q ∈ cs.map CornerRecord.prefixLength) ∧
    (∀ q : ℕ, oldPrefix k e wm q < 0 ∨ newPrefix k e wm q < 0 →
      q ∈ cs.map CornerRecord.prefixLength) ∧
    ((Finset.univ : Finset (Fin (k + 2))).filter (fun q =>
      H < oldPrefix k e wp q.val ∨ N < newPrefix k e wp q.val)).card ≤ cs.length ∧
    ((Finset.univ : Finset (Fin (k + 2))).filter (fun q =>
      oldPrefix k e wm q.val < 0 ∨ newPrefix k e wm q.val < 0)).card ≤ cs.length

/-- The exact unresolved universal proposition, retained without a proof claim.
The target includes p=1 and every tuple with repeated gaps or repeated values. -/
def UniformSparseNecklaceRounding : Prop :=
  ∀ (p : ℕ), 1 ≤ p → ∀ (gaps : Fin p → ℕ),
    (∀ j, 2 ≤ gaps j) → PhysicalRounding gaps

private theorem gap_list_length {p : ℕ} (gaps : Fin p → ℕ) :
    (gapList gaps).length = p := by simp [gapList]

private theorem gap_list_sum {p : ℕ} (gaps : Fin p → ℕ) :
    (gapList gaps).sum = period gaps := by
  simp [gapList, ← List.ofFn_eq_map, period, List.sum_ofFn]

private theorem gap_list_mem {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) : ∀ a ∈ gapList gaps, 2 ≤ a := by
  intro a ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  exact hg j

private theorem bits_fin_sum (l : List ℕ) :
    bits l = ∑ i : Fin l.length, (2 : ℤ) ^ (l.take i.val).sum := by
  induction l with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.length_cons]
    rw [bits, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, List.sum_nil, pow_zero,
      Fin.val_succ, List.take_succ_cons, List.sum_cons, pow_add]
    rw [Finset.mul_sum]

private theorem gap_prefix_sum {p : ℕ} (gaps : Fin p → ℕ) (j : Fin p) :
    ((gapList gaps).take j.val).sum = ∑ q ∈ Finset.univ.filter (fun q : Fin p => q < j), gaps q := by
  rw [gapList, ← List.ofFn_eq_map, List.sum_take_ofFn]
  rfl

private theorem bits_seed {p : ℕ} (gaps : Fin p → ℕ) :
    bits (gapList gaps) = (necklaceSeed gaps : ℤ) := by
  rw [bits_fin_sum]
  simp only [necklaceSeed, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  apply Finset.sum_bij (fun i _ => (⟨i.val, by simpa [gap_list_length] using i.isLt⟩ : Fin p))
  · simp
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun x : Fin p => x.val) hij)
  · intro j _
    exact ⟨⟨j.val, by simpa [gap_list_length] using j.isLt⟩, by simp, rfl⟩
  · intro i _
    congr 1
    exact gap_prefix_sum gaps ⟨i.val, by simpa [gap_list_length] using i.isLt⟩

private theorem chain_start_drop {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) :
    chainStart gaps r = ((gapList gaps).drop (p - r)).sum := by
  simp [chainStart, List.take_reverse, gap_list_length]

private theorem chain_start_step {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) (hr : r < p) :
    chainStart gaps (r + 1) = chainStart gaps r + chainGap gaps r := by
  have hi : r < (gapList gaps).reverse.length := by simpa [gap_list_length] using hr
  simp only [chainStart, chainGap, List.take_succ_eq_append_getElem hi,
    List.sum_append, List.sum_singleton, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem chain_cut {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) (hr : r < p) :
    let l := (gapList gaps).take (p - (r + 1))
    let s := (gapList gaps).drop (p - r)
    (l ++ [chainGap gaps r]) ++ s = gapList gaps ∧
    (gapList gaps).take (p - r) = l ++ [chainGap gaps r] ∧
    (gapList gaps).drop (p - (r + 1)) = chainGap gaps r :: s := by
  dsimp only
  let v := gapList gaps
  have hn : p - (r + 1) < v.length := by dsimp [v]; rw [gap_list_length]; omega
  have hindex : chainGap gaps r = v[p - (r + 1)] := by
    simp only [chainGap]
    rw [List.getElem?_reverse (by simpa [gap_list_length] using hr)]
    simp only [gap_list_length, show p - 1 - r = p - (r + 1) by omega,
      v, List.getElem?_eq_getElem (show p - (r + 1) < (gapList gaps).length from hn),
      Option.getD_some]
  have hstep : p - r = p - (r + 1) + 1 := by omega
  have ht : v.take (p - r) = v.take (p - (r + 1)) ++ [chainGap gaps r] := by
    rw [hstep, List.take_succ_eq_append_getElem hn, hindex]
  refine ⟨?_, ht, ?_⟩
  · rw [← ht, List.take_append_drop]
  · rw [List.drop_eq_getElem_cons hn, ← hindex, ← hstep]

private theorem necklace_endpoints {p : ℕ} (gaps : Fin p → ℕ) :
    cyclicHead gaps 0 = (necklaceSeed gaps : ℤ) ∧
    cyclicHead gaps p = (necklaceSeed gaps : ℤ) ∧
    winding gaps 0 = 0 ∧ winding gaps p = (necklaceSeed gaps : ℤ) ∧
    chainStart gaps 0 = 0 ∧ chainStart gaps p = period gaps := by
  have ht : (gapList gaps).take p = gapList gaps := by
    simpa only [gap_list_length] using (List.take_length (l := gapList gaps))
  have hd : (gapList gaps).drop p = [] := by
    simpa only [gap_list_length] using (List.drop_length (l := gapList gaps))
  have hrt : (gapList gaps).reverse.take p = (gapList gaps).reverse := by
    apply List.take_of_length_le
    simp [gap_list_length]
  simp [cyclicHead, winding, cutHead, cutCharge, chainStart,
    ht, hd, hrt, bits_seed, bits, gap_list_sum]

private theorem necklace_chain_coordinates {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) :
    let k := period gaps
    let e := necklaceSeed gaps
    let N := modulus k
    let h := cyclicHead gaps r
    let h' := cyclicHead gaps (r + 1)
    let z := winding gaps r
    let z' := winding gaps (r + 1)
    let n := (N - h') / 2
    let tau := (z' + 1) / 2
    2 ≤ k ∧ 0 < (e : ℤ) ∧ 3 * (e : ℤ) ≤ N ∧
    0 < h ∧ 3 * h ≤ N ∧ 0 < h' ∧ 3 * h' ≤ N ∧
    h % 2 = 1 ∧ h' % 2 = 1 ∧
    0 ≤ z ∧ z < h ∧ 0 < z' ∧ z' ≤ h' ∧ z' % 2 = 1 ∧
    (2 : ℤ) ^ (chainGap gaps r) * h = N + h' ∧ z' = (2 : ℤ) ^ (chainGap gaps r) * z + 1 ∧
    (2 : ℤ) ^ (chainStart gaps r) * e = h + N * z ∧
    2 * n = N - h' ∧ 2 * tau = z' + 1 ∧
    N ≤ 3 * n ∧ n ≤ N / 2 ∧ 1 ≤ tau ∧ tau ≤ h' ∧
    ((2 : ℤ) ^ ((chainGap gaps r) - 1) - 1) * h = n + h' - h ∧
    ((2 : ℤ) ^ ((chainGap gaps r) - 1) - 1) * z + tau = z' - z ∧
    0 < n + h' - (e : ℤ) ∧ 2 * n + z' ≤ N ∧
    actualSource (k + 1) (2 * e) (Fin.last k) = (e : ℤ) ∧
    (∀ t : ℕ, t ≤ (chainGap gaps r) - 2 → ∃ hi : chainStart gaps r + t < k,
      let i : Fin k := ⟨chainStart gaps r + t, hi⟩
      let mass := (2 : ℤ) ^ t * h
      let charge := (2 : ℤ) ^ t * z
      0 < mass ∧ 3 * mass ≤ N ∧ 0 ≤ charge ∧ charge < mass ∧
      actualSource k e i = mass ∧
      actualSource (k + 1) (2 * e) i.castSucc = 2 * mass - charge) ∧
    (∃ hi : chainStart gaps r + (chainGap gaps r) - 1 < k,
      let i : Fin k := ⟨chainStart gaps r + (chainGap gaps r) - 1, hi⟩
      actualSource k e i = -n ∧
      actualSource (k + 1) (2 * e) i.castSucc = -2 * n - tau ∧
      0 < n ∧ 0 < 2 * n + tau ∧ 2 * n + tau ≤ N) := by
  let l := (gapList gaps).take (p - (r + 1))
  let s := (gapList gaps).drop (p - r)
  let a := chainGap gaps r
  have hc := chain_cut gaps r hr
  dsimp only at hc
  have hcat : (l ++ [a]) ++ s = gapList gaps := hc.1
  have ht : (gapList gaps).take (p - r) = l ++ [a] := hc.2.1
  have hd : (gapList gaps).drop (p - (r + 1)) = a :: s := hc.2.2
  have hm : ∀ b ∈ (l ++ [a]) ++ s, 2 ≤ b := by
    intro b hb
    exact gap_list_mem gaps hg b (by rwa [← hcat])
  have hk : l.sum + a + s.sum = period gaps := by
    calc
      _ = ((l ++ [a]) ++ s).sum := by simp [add_assoc]
      _ = period gaps := by rw [hcat]; exact gap_list_sum gaps
  have he : (bits ((l ++ [a]) ++ s)).toNat = necklaceSeed gaps := by
    rw [hcat, bits_seed, Int.toNat_natCast]
  have hh : cutHead (l ++ [a]) s = cyclicHead gaps r := by
    rw [← ht]; rfl
  have hh' : cutHead l (a :: s) = cyclicHead gaps (r + 1) := by
    rw [← hd]; rfl
  have hz : cutCharge s = winding gaps r := rfl
  have hz' : cutCharge (a :: s) = winding gaps (r + 1) := by
    rw [← hd]; rfl
  have hs : s.sum = chainStart gaps r := (chain_start_drop gaps r).symm
  have h := native_chain_coordinates l s a hm
  dsimp only at h ⊢
  rw [hk, he, hh, hh', hz, hz', hs] at h
  exact h

private theorem indexed_intervals (l : List ℕ) :
    (List.range l.length).flatMap (fun r =>
      (List.range ((l[r]?).getD 0)).map (fun t => (l.take r).sum + t)) =
        List.range l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, List.getElem?_cons_zero, Option.getD_some,
      List.take_zero, List.sum_nil, zero_add, List.map_id_fun',
      List.sum_cons, List.range_add]
    congr 1
    rw [← ih, List.map_flatMap]
    apply List.flatMap_congr
    intro r hr
    simp [List.take_succ_cons, List.sum_cons, Function.comp_def, List.map_map, add_assoc]

private theorem chain_gap_lower {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) : 2 ≤ chainGap gaps r := by
  have hc := chain_cut gaps r hr
  dsimp only at hc
  apply gap_list_mem gaps hg
  rw [← hc.1]
  simp

private theorem raw_inventory {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    (positiveIndices gaps ++ (List.range p).reverse.map (terminalIndex gaps)).Perm
      (List.range (period gaps)) := by
  let rs := (List.range p).reverse
  let pos := fun r => (List.range (chainGap gaps r - 1)).map
    (fun t => chainStart gaps r + t)
  let neg := fun r => [terminalIndex gaps r]
  let all := fun r => (List.range (chainGap gaps r)).map
    (fun t => chainStart gaps r + t)
  have he : ∀ r ∈ rs, all r = pos r ++ neg r := by
    intro r hr
    have hrp : r < p := List.mem_range.mp (List.mem_reverse.mp hr)
    have ha := chain_gap_lower gaps hg r hrp
    have ht : terminalIndex gaps r = chainStart gaps r + (chainGap gaps r - 1) := by
      rw [terminalIndex, chain_start_step gaps r hrp]
      omega
    have hrg : List.range (chainGap gaps r) =
        List.range (chainGap gaps r - 1) ++ [chainGap gaps r - 1] := by
      simpa only [Nat.succ_eq_add_one, show chainGap gaps r - 1 + 1 = chainGap gaps r by omega]
        using (List.range_succ (n := chainGap gaps r - 1))
    simp only [all, pos, neg, hrg, List.map_append, List.map_singleton, ht]
  have hp : (rs.flatMap all).Perm (positiveIndices gaps ++ rs.map (terminalIndex gaps)) := by
    have hh := List.flatMap_append_perm rs pos neg
    rw [List.flatMap_congr he]
    simpa only [← List.map_eq_flatMap, rs, pos, neg, positiveIndices] using hh.symm
  have horder : (rs.flatMap all).Perm ((List.range p).flatMap all) :=
    (List.reverse_perm _).flatMap_right all
  have hfull : (List.range p).flatMap all = List.range (period gaps) := by
    simpa only [List.length_reverse, gap_list_length, List.sum_reverse, gap_list_sum,
      all, chainGap, chainStart] using indexed_intervals (gapList gaps).reverse
  exact hp.symm.trans (horder.trans (by rw [hfull]))

private theorem filterMap_label_values (k : ℕ) (xs : List ℕ)
    (hx : ∀ i ∈ xs, i < k) :
    ((xs.filterMap (labelAt k)).map Fin.val) = xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have hi := hx i (by simp)
    have ht : ∀ j ∈ xs, j < k := fun j hj => hx j (by simp [hj])
    simpa [labelAt, hi] using congrArg (List.cons i) (ih ht)

private theorem terminal_value_stream (k : ℕ) (rs : List ℕ)
    (idx : ℕ → ℕ) (d : ℕ → ℚ) (hb : ∀ r ∈ rs, idx r < k) :
    ((rs.filterMap (fun r => (labelAt k (idx r)).map (fun i => (i, d r)))).map
      (fun t => t.1.val)) = rs.map idx := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hi := hb r (by simp)
    have ht : ∀ j ∈ rs, idx j < k := fun j hj => hb j (by simp [hj])
    simpa [labelAt, hi] using congrArg (List.cons (idx r)) (ih ht)

private theorem physical_inventory {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    (positiveLabels gaps ++ (thresholdTerminals gaps).map Prod.fst).Perm
      (List.finRange (period gaps)) := by
  have hp := raw_inventory gaps hg
  have hb : ∀ i ∈ positiveIndices gaps ++
      (List.range p).reverse.map (terminalIndex gaps), i < period gaps := by
    intro i hi
    exact List.mem_range.mp (hp.mem_iff.mp hi)
  have hpv : (positiveLabels gaps).map Fin.val = positiveIndices gaps :=
    filterMap_label_values _ _ (fun i hi => hb i (by simp [hi]))
  have htv : ((thresholdTerminals gaps).map Prod.fst).map Fin.val =
      (List.range p).reverse.map (terminalIndex gaps) := by
    simpa only [thresholdTerminals, List.map_map, Function.comp_def] using
      terminal_value_stream (period gaps) (List.range p).reverse (terminalIndex gaps)
        (fun r => (threshold gaps r : ℚ)) (by
          intro r hr
          exact hb _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)))
  apply (List.map_perm_map_iff Fin.val_injective).mp
  simpa only [List.map_append, hpv, htv, List.map_coe_finRange_eq_range] using hp

private theorem positive_coordinates {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (i : Fin (period gaps)) (hi : i ∈ positiveLabels gaps) :
    0 < actualSource (period gaps) (necklaceSeed gaps) i ∧
    3 * actualSource (period gaps) (necklaceSeed gaps) i ≤ modulus (period gaps) ∧
    0 < actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc ∧
    actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc ≤
      2 * actualSource (period gaps) (necklaceSeed gaps) i := by
  have hp := raw_inventory gaps hg
  have hb : ∀ n ∈ positiveIndices gaps, n < period gaps := by
    intro n hn
    exact List.mem_range.mp (hp.mem_iff.mp (List.mem_append_left _ hn))
  have hval := filterMap_label_values (period gaps) (positiveIndices gaps) hb
  have hiv : i.val ∈ positiveIndices gaps := by
    rw [← hval]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  obtain ⟨r, hr, hri⟩ := List.mem_flatMap.mp hiv
  obtain ⟨t, ht, hti⟩ := List.mem_map.mp hri
  have hrp : r < p := List.mem_range.mp (List.mem_reverse.mp hr)
  rcases necklace_chain_coordinates gaps hg r hrp with
    ⟨hk, hep, heb, hhp, hhb, hhp', hhb', hho, hho', hz0, hzh,
      hz'p, hz'h, hz'o, hstep, hzstep, hw, hn, htau, hnb, hnh,
      htaup, htaub, hP, hC, hdir, hpeak, hfresh, hpos, hneg⟩
  obtain ⟨hit, hm, hmb, hc, hcl, hf, hgi⟩ := hpos t (by
    have := List.mem_range.mp ht
    omega)
  have heq : (⟨chainStart gaps r + t, hit⟩ : Fin (period gaps)) = i := Fin.ext hti
  rw [heq] at hf hgi
  rw [hf, hgi]
  exact ⟨hm, hmb, by omega, by omega⟩

private theorem terminal_coordinates {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) :
    ∃ hi : terminalIndex gaps r < period gaps,
      actualSource (period gaps) (necklaceSeed gaps) ⟨terminalIndex gaps r, hi⟩ =
        -demand gaps r ∧
      actualSource (period gaps + 1) (2 * necklaceSeed gaps)
        (⟨terminalIndex gaps r, hi⟩ : Fin (period gaps)).castSucc =
          -2 * demand gaps r - terminalCharge gaps r ∧
      0 < demand gaps r ∧ modulus (period gaps) ≤ 3 * demand gaps r ∧
      demand gaps r ≤ modulus (period gaps) / 2 ∧
      1 ≤ terminalCharge gaps r ∧ terminalCharge gaps r ≤ cyclicHead gaps (r + 1) ∧
      2 * demand gaps r + winding gaps (r + 1) ≤ modulus (period gaps) := by
  rcases necklace_chain_coordinates gaps hg r hr with
    ⟨hk, hep, heb, hhp, hhb, hhp', hhb', hho, hho', hz0, hzh,
      hz'p, hz'h, hz'o, hstep, hzstep, hw, hn, htau, hnb, hnh,
      htaup, htaub, hP, hC, hdir, hpeak, hfresh, hpos, hneg⟩
  obtain ⟨hit, hf, hgi, hnp, hgp, hgb⟩ := hneg
  have hind : terminalIndex gaps r = chainStart gaps r + chainGap gaps r - 1 := by
    rw [terminalIndex, chain_start_step gaps r hr]
  have hi : terminalIndex gaps r < period gaps := by rw [hind]; exact hit
  refine ⟨hi, ?_, ?_, hnp, hnb, hnh, htaup, htaub, hpeak⟩
  · simpa only [hind, demand] using hf
  · simpa only [hind, demand, terminalCharge] using hgi

private theorem threshold_step {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) (hr : r < p) :
    threshold gaps r = demand gaps r + threshold gaps (r + 1) := by
  have hi : r < (List.range p).length := by simpa using hr
  simp only [threshold, List.drop_eq_getElem_cons hi,
    List.getElem_range hi, List.map_cons, List.sum_cons]

private theorem threshold_last {p : ℕ} (gaps : Fin p → ℕ) : threshold gaps p = 0 := by
  have hd : (List.range p).drop p = [] := by simp
  simp only [threshold, hd, List.map_nil, List.sum_nil]

private theorem threshold_strict {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) :
    threshold gaps (r + 1) < threshold gaps r := by
  obtain ⟨hi, hf, hgi, hn, hnb, hnh, htaup, htaub, hpeak⟩ :=
    terminal_coordinates gaps hg r hr
  rw [threshold_step gaps r hr]
  linarith

private theorem threshold_blocks_inventory {α : Type*} (mass : α → ℚ)
    (ps : List α) (ts : List (α × ℚ)) (x : ℚ) :
    (plusWord (thresholdBlocks mass ps ts x)).Perm (ps ++ ts.map Prod.fst) := by
  induction ps generalizing ts x with
  | nil =>
    simp only [thresholdBlocks, List.nil_append]
    induction ts with
    | nil => exact .refl _
    | cons t ts ih => simpa only [List.map_cons, plusWord] using ih.cons t.1
  | cons i ps ih =>
    cases ts with
    | nil => simpa only [thresholdBlocks, plusWord, List.map_nil, List.append_nil] using ih [] (x + mass i) |>.cons i
    | cons t ts =>
      rcases t with ⟨j,d⟩
      by_cases hd : d < x + mass i
      · simp only [thresholdBlocks, hd, ↓reduceIte, plusWord, List.map_cons, List.cons_append]
        exact ((ih ts (x + mass i)).cons j |>.cons i).trans
          ((List.perm_middle).symm.cons i)
      · by_cases he : d = x + mass i
        · simp only [thresholdBlocks, he, lt_self_iff_false, ↓reduceIte, plusWord, List.map_cons, List.cons_append]
          exact ((ih ts (x + mass i)).cons j |>.cons i).trans
            ((List.perm_middle).symm.cons i)
        · simpa only [thresholdBlocks, hd, he, ↓reduceIte, plusWord, List.map_cons,
            List.cons_append] using (ih ((j,d)::ts) (x + mass i)).cons i

private theorem threshold_blocks_split_count {α : Type*} (mass : α → ℚ)
    (ps : List α) (ts : List (α × ℚ)) (x : ℚ) :
    (splitPairs (thresholdBlocks mass ps ts x)).length ≤ ts.length := by
  induction ps generalizing ts x with
  | nil =>
    simp only [thresholdBlocks]
    induction ts with
    | nil => simp [splitPairs]
    | cons t ts ih => simpa [splitPairs] using Nat.le_trans ih (Nat.le_succ _)
  | cons i ps ih =>
    cases ts with
    | nil => simpa [thresholdBlocks,splitPairs] using ih [] (x + mass i)
    | cons t ts =>
      rcases t with ⟨j,d⟩
      by_cases hd : d < x + mass i
      · simpa [thresholdBlocks,hd,splitPairs] using Nat.succ_le_succ (ih ts (x + mass i))
      · by_cases he : d = x + mass i
        · simpa [thresholdBlocks,hd,he,splitPairs] using (ih ts (x + mass i)).trans (Nat.le_succ _)
        · simpa [thresholdBlocks,hd,he,splitPairs] using ih ((j,d)::ts) (x + mass i)

private theorem threshold_blocks_strict_provenance {α : Type*} (mass : α → ℚ)
    (L : ℚ) (ps : List α) (ts : List (α × ℚ)) (x : ℚ)
    (hm : ∀ i ∈ ps, 0 < mass i ∧ mass i ≤ L)
    (ht : ts.Pairwise (fun a b => a.2 + L ≤ b.2))
    (hx : ∀ t ∈ ts, x < t.2) :
    ∀ ij ∈ splitPairs (thresholdBlocks mass ps ts x),
      ∃ pre post d, ps = pre ++ ij.1 :: post ∧ (ij.2,d) ∈ ts ∧
        x + (pre.map mass).sum < d ∧ d < x + (pre.map mass).sum + mass ij.1 := by
  induction ps generalizing ts x with
  | nil =>
    simp only [thresholdBlocks]
    have he : splitPairs (ts.map (fun t => RoundBlock.one t.1)) = [] := by
      clear ht hx
      induction ts with
      | nil => rfl
      | cons t ts ih => simpa [splitPairs] using ih
    simp [he]
  | cons i ps ih =>
    have hi := hm i (by simp)
    have hm' : ∀ a ∈ ps, 0 < mass a ∧ mass a ≤ L := fun a ha => hm a (by simp [ha])
    cases ts with
    | nil =>
      have hh := ih [] (x + mass i) hm' (by simp) (by simp)
      simpa [thresholdBlocks,splitPairs] using hh
    | cons t ts =>
      rcases t with ⟨j,d⟩
      have hparts := List.pairwise_cons.mp ht
      have hx' : ∀ t ∈ ts, x + mass i < t.2 := by
        intro t ht
        have := hparts.1 t ht
        have := hx (j,d) (by simp)
        dsimp only at *
        linarith
      by_cases hd : d < x + mass i
      · simp only [thresholdBlocks,hd,↓reduceIte,splitPairs]
        intro ij hij
        rcases List.mem_cons.mp hij with rfl | hij
        · exact ⟨[],ps,d,rfl,by simp,by simpa using hx (j,d) (by simp),by simpa using hd⟩
        · obtain ⟨pre,post,d',hps,hmem,hlo,hup⟩ := ih ts (x + mass i) hm' hparts.2 hx' ij hij
          refine ⟨i::pre,post,d',by simp [hps],by simp [hmem],?_,?_⟩
          · simpa only [List.map_cons,List.sum_cons,add_assoc] using hlo
          · simpa only [List.map_cons,List.sum_cons,add_assoc] using hup
      · by_cases he : d = x + mass i
        · simp only [thresholdBlocks,he,lt_self_iff_false,↓reduceIte,splitPairs]
          intro ij hij
          obtain ⟨pre,post,d',hps,hmem,hlo,hup⟩ := ih ts (x + mass i) hm' hparts.2 hx' ij hij
          refine ⟨i::pre,post,d',by simp [hps],by simp [hmem],?_,?_⟩
          · simpa only [List.map_cons,List.sum_cons,add_assoc] using hlo
          · simpa only [List.map_cons,List.sum_cons,add_assoc] using hup
        · have hall : ∀ t ∈ (j,d)::ts, x + mass i < t.2 := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · dsimp only; exact lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm he)
            · exact hx' t ht
          simp only [thresholdBlocks,hd,he,↓reduceIte,splitPairs]
          intro ij hij
          obtain ⟨pre,post,d',hps,hmem,hlo,hup⟩ := ih ((j,d)::ts) (x + mass i) hm' ht hall ij hij
          refine ⟨i::pre,post,d',by simp [hps],hmem,?_,?_⟩
          · simpa only [List.map_cons,List.sum_cons,add_assoc] using hlo
          · simpa only [List.map_cons,List.sum_cons,add_assoc] using hup

private theorem threshold_blocks_final_not_split {α : Type*} (mass : α → ℚ)
    (ps : List α) (ts : List (α × ℚ)) (x : ℚ) (last : α × ℚ)
    (hm : ∀ i ∈ ps, 0 ≤ mass i)
    (hl : ts.getLast? = some last)
    (hx : x + (ps.map mass).sum ≤ last.2) :
    (splitPairs (thresholdBlocks mass ps ts x)).length ≤ ts.length - 1 := by
  induction ps generalizing ts x with
  | nil =>
    have he : splitPairs (ts.map (fun t => RoundBlock.one t.1)) = [] := by
      clear hl
      induction ts with
      | nil => rfl
      | cons t ts ih => simpa [splitPairs] using ih
    simp [thresholdBlocks,he]
  | cons i ps ih =>
    have hm' : ∀ a ∈ ps, 0 ≤ mass a := fun a ha => hm a (by simp [ha])
    have hs : 0 ≤ (ps.map mass).sum := List.sum_nonneg (by
      intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact hm' b hb)
    have hx' : x + mass i + (ps.map mass).sum ≤ last.2 := by
      simpa only [List.map_cons,List.sum_cons,add_assoc] using hx
    cases ts with
    | nil => simp at hl
    | cons t ts =>
      rcases t with ⟨j,d⟩
      by_cases hd : d < x + mass i
      · have hne : ts ≠ [] := by
          intro he; subst ts
          simp only [List.getLast?_singleton,Option.some.injEq] at hl
          subst last
          dsimp only at hx'
          linarith
        have hlast : ts.getLast? = some last := by
          cases ts with
          | nil => contradiction
          | cons t ts => simpa only [List.getLast?_cons_cons] using hl
        have hh := ih ts (x + mass i) hm' hlast hx'
        have hlen : 1 ≤ ts.length := List.length_pos_iff.mpr hne
        simp only [thresholdBlocks,hd,↓reduceIte,splitPairs,List.length_cons]
        omega
      · by_cases he : d = x + mass i
        · have hh := threshold_blocks_split_count mass ps ts (x + mass i)
          simpa [thresholdBlocks,hd,he,splitPairs] using hh
        · simpa [thresholdBlocks,hd,he,splitPairs] using ih ((j,d)::ts) (x + mass i) hm' hl hx'

private theorem threshold_antitone {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ p) :
    threshold gaps s ≤ threshold gaps r := by
  revert hs
  induction hrs with
  | refl => intro _; exact le_rfl
  | @step s hrs ih =>
    intro hs
    exact (le_of_lt (threshold_strict gaps hg s (by omega))).trans (ih (by omega))

private theorem threshold_spacing {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r s : ℕ) (hsr : s < r) (hr : r < p) :
    modulus (period gaps) ≤ 3 * (threshold gaps s - threshold gaps r) := by
  have hanti := threshold_antitone gaps hg (s + 1) r (by omega) (by omega)
  obtain ⟨hi,hf,hgi,hn,hnb,rest⟩ := terminal_coordinates gaps hg s (by omega)
  rw [threshold_step gaps s (by omega)]
  linarith

private theorem int_list_cast {α : Type*} (f : α → ℤ) (xs : List α) :
    (xs.map (fun i => (f i : ℚ))).sum = ((xs.map f).sum : ℤ) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

private theorem terminal_projection {β : Type*} (k : ℕ) (rs : List ℕ)
    (idx : ℕ → ℕ) (d : ℕ → ℚ) (f : Fin k × ℚ → β) (v : ℕ → β)
    (hv : ∀ r ∈ rs, ∃ hi : idx r < k, f (⟨idx r,hi⟩,d r) = v r) :
    ((rs.filterMap (fun r => (labelAt k (idx r)).map (fun i => (i,d r)))).map f) =
      rs.map v := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨hi,hf⟩ := hv r (by simp)
    have ht : ∀ s ∈ rs, ∃ hi : idx s < k, f (⟨idx s,hi⟩,d s) = v s :=
      fun s hs => hv s (by simp [hs])
    simpa [labelAt,hi,hf] using congrArg (List.cons (v r)) (ih ht)

private theorem necklace_physical_totals {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    ((List.finRange (period gaps)).map (actualSource (period gaps) (necklaceSeed gaps))).sum = 0 ∧
    ((List.finRange (period gaps)).map (fun i =>
      actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc)).sum =
        -(necklaceSeed gaps : ℤ) ∧
    actualSource (period gaps + 1) (2 * necklaceSeed gaps) (Fin.last (period gaps)) =
      (necklaceSeed gaps : ℤ) := by
  rcases necklace_chain_coordinates gaps hg 0 (by omega) with
    ⟨hk,hep,heb,hhp,hhb,hhp',hhb',hho,hho',hz0,hzh,hz'p,hz'h,hz'o,
      hstep,hzstep,hw,hn,htau,hnb,hnh,htaup,htaub,hP,hC,hdir,hpeak,hfresh,rest⟩
  have hold := (ZeroSumSubsets.source_cycle (by omega : 0 < period gaps) (necklaceSeed gaps)).2.1
  have hnew := (ZeroSumSubsets.source_cycle (by omega : 0 < period gaps + 1)
    (2 * necklaceSeed gaps)).2.1
  rw [Fin.sum_univ_castSucc, hfresh] at hnew
  refine ⟨?_,?_,hfresh⟩
  · simpa only [← List.ofFn_eq_map,List.sum_ofFn] using hold
  · have hn : (∑ i : Fin (period gaps),
        actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc) =
          -(necklaceSeed gaps : ℤ) := by linarith
    simpa only [← List.ofFn_eq_map,List.sum_ofFn] using hn

private theorem terminal_mass_sum {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    (((thresholdTerminals gaps).map Prod.fst).map
      (actualSource (period gaps) (necklaceSeed gaps))).sum = -threshold gaps 0 := by
  have hm := terminal_projection (period gaps) (List.range p).reverse
    (terminalIndex gaps) (fun r => (threshold gaps r : ℚ))
    (fun t => actualSource (period gaps) (necklaceSeed gaps) t.1)
    (fun r => -demand gaps r) (by
      intro r hr
      obtain ⟨hi,hf,rest⟩ := terminal_coordinates gaps hg r
        (List.mem_range.mp (List.mem_reverse.mp hr))
      exact ⟨hi,hf⟩)
  rw [List.map_map]
  change ((thresholdTerminals gaps).map
    (fun t => actualSource (period gaps) (necklaceSeed gaps) t.1)).sum = _
  rw [show (thresholdTerminals gaps).map
      (fun t => actualSource (period gaps) (necklaceSeed gaps) t.1) =
      (List.range p).reverse.map (fun r => -demand gaps r) from hm]
  simp only [List.map_reverse,List.sum_reverse,threshold,List.drop_zero]
  induction List.range p with
  | nil => simp
  | cons r rs ih => simp [ih,add_comm]

private theorem total_positive_mass {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    ((positiveLabels gaps).map (actualSource (period gaps) (necklaceSeed gaps))).sum =
      threshold gaps 0 := by
  have hi := (physical_inventory gaps hg).map (actualSource (period gaps) (necklaceSeed gaps))
  have hs := hi.sum_eq
  rw [List.map_append,List.sum_append,(necklace_physical_totals hp gaps hg).1,
    terminal_mass_sum gaps hg] at hs
  linarith

private theorem threshold_terminal_length {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) : (thresholdTerminals gaps).length = p := by
  have hh := terminal_projection (period gaps) (List.range p).reverse
    (terminalIndex gaps) (fun r => (threshold gaps r : ℚ))
    (fun _ => ()) (fun _ => ()) (by
      intro r hr
      obtain ⟨hi,rest⟩ := terminal_coordinates gaps hg r
        (List.mem_range.mp (List.mem_reverse.mp hr))
      exact ⟨hi,rfl⟩)
  simpa only [thresholdTerminals,List.length_map,List.length_reverse,List.length_range] using congrArg List.length hh

private theorem threshold_terminal_spacing {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    (thresholdTerminals gaps).Pairwise
      (fun a b => a.2 + (modulus (period gaps) : ℚ) / 3 ≤ b.2) := by
  have hs : (List.range p).reverse.Pairwise (fun r s => r < p ∧ s < p ∧ s < r) :=
    List.Pairwise.imp_of_mem (fun hr hs h =>
      ⟨List.mem_range.mp (List.mem_reverse.mp hr),
        List.mem_range.mp (List.mem_reverse.mp hs),h⟩)
      (List.pairwise_lt_range.reverse)
  apply hs.filterMap _
  intro r s hrs t ht t' ht'
  have hir : terminalIndex gaps r < period gaps := (terminal_coordinates gaps hg r hrs.1).choose
  have his : terminalIndex gaps s < period gaps := (terminal_coordinates gaps hg s hrs.2.1).choose
  simp only [labelAt,dif_pos hir,Option.map_some,Option.some.injEq] at ht
  simp only [labelAt,dif_pos his,Option.map_some,Option.some.injEq] at ht'
  subst t; subst t'
  dsimp only
  have h := threshold_spacing gaps hg r s hrs.2.2 hrs.1
  have hq : (modulus (period gaps) : ℚ) ≤
      3 * ((threshold gaps s : ℚ) - (threshold gaps r : ℚ)) := by exact_mod_cast h
  linarith

private theorem threshold_terminal_positive {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    ∀ t ∈ thresholdTerminals gaps, 0 < t.2 := by
  intro t ht
  obtain ⟨r,hr,htr⟩ := List.mem_filterMap.mp ht
  have hrp := List.mem_range.mp (List.mem_reverse.mp hr)
  have hir : terminalIndex gaps r < period gaps := (terminal_coordinates gaps hg r hrp).choose
  simp only [labelAt,dif_pos hir,Option.map_some,Option.some.injEq] at htr
  subst t
  have h0 := threshold_antitone gaps hg (r + 1) p (by omega) le_rfl
  rw [threshold_last] at h0
  have h1 := threshold_strict gaps hg r hrp
  dsimp only
  exact_mod_cast (lt_of_le_of_lt h0 h1)

private theorem necklace_blocks_inventory {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    (plusWord (necklaceBlocks gaps)).Perm (List.finRange (period gaps)) := by
  exact (threshold_blocks_inventory _ _ _ _).trans (physical_inventory gaps hg)

private theorem threshold_terminal_last {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    ∃ last, (thresholdTerminals gaps).getLast? = some last ∧
      last.2 = (threshold gaps 0 : ℚ) := by
  have hm := terminal_projection (period gaps) (List.range p).reverse
    (terminalIndex gaps) (fun r => (threshold gaps r : ℚ)) Prod.snd
    (fun r => (threshold gaps r : ℚ)) (by
      intro r hr
      obtain ⟨hi,rest⟩ := terminal_coordinates gaps hg r
        (List.mem_range.mp (List.mem_reverse.mp hr))
      exact ⟨hi,rfl⟩)
  have hv : ((List.range p).reverse.map (fun r => (threshold gaps r : ℚ))).getLast? =
      some (threshold gaps 0 : ℚ) := by
    cases p with
    | zero => omega
    | succ p => simp [List.getLast?_map,List.getLast?_reverse,List.range_succ_eq_map]
  change (thresholdTerminals gaps).map Prod.snd = _ at hm
  rw [← hm,List.getLast?_map] at hv
  cases hl : (thresholdTerminals gaps).getLast? with
  | none => simp [hl] at hv
  | some last => exact ⟨last,rfl,by simpa only [hl,Option.map_some,Option.some.injEq] using hv⟩

private theorem necklace_split_bound {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    (splitPairs (necklaceBlocks gaps)).length ≤ p - 1 := by
  obtain ⟨last,hl,he⟩ := threshold_terminal_last hp gaps hg
  have hm : ∀ i ∈ positiveLabels gaps,
      0 ≤ (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) := by
    intro i hi
    exact_mod_cast le_of_lt (positive_coordinates gaps hg i hi).1
  have hsum : ((positiveLabels gaps).map
      (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))).sum =
      (threshold gaps 0 : ℚ) := by
    rw [int_list_cast,total_positive_mass hp gaps hg]
  have hh := threshold_blocks_final_not_split _ _ _ 0 last hm hl
    (by rw [zero_add,hsum,he])
  simpa only [necklaceBlocks,threshold_terminal_length gaps hg] using hh

private theorem necklace_split_provenance {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    ∀ ij ∈ splitPairs (necklaceBlocks gaps), IsStrictSplit gaps ij.1 ij.2 := by
  intro ij hij
  have hm : ∀ i ∈ positiveLabels gaps,
      0 < (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) ∧
      (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) ≤
        (modulus (period gaps) : ℚ) / 3 := by
    intro i hi
    obtain ⟨hf,hfb,hg,rest⟩ := positive_coordinates gaps hg i hi
    have hfq : (0 : ℚ) < actualSource (period gaps) (necklaceSeed gaps) i := by exact_mod_cast hf
    have hfbq : 3 * (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) ≤
        (modulus (period gaps) : ℚ) := by exact_mod_cast hfb
    exact ⟨hfq,by linarith⟩
  obtain ⟨pre,post,d,hps,ht,hlo,hup⟩ := threshold_blocks_strict_provenance _ _ _ _ 0
    hm (threshold_terminal_spacing gaps hg) (threshold_terminal_positive gaps hg) ij hij
  obtain ⟨r,hr,htr⟩ := List.mem_filterMap.mp ht
  have hrp := List.mem_range.mp (List.mem_reverse.mp hr)
  have hir : terminalIndex gaps r < period gaps := (terminal_coordinates gaps hg r hrp).choose
  simp only [labelAt,dif_pos hir,Option.map_some,Option.some.injEq,Prod.mk.injEq] at htr
  have hj : ij.2.val = terminalIndex gaps r := (congrArg Fin.val htr.1).symm
  have hnd : (positiveLabels gaps ++ (thresholdTerminals gaps).map Prod.fst).Nodup :=
    (physical_inventory gaps hg).nodup_iff.mpr (List.nodup_finRange _)
  have hpnd := (List.nodup_append.mp hnd).1
  rw [hps] at hpnd
  have hnot : ij.1 ∉ pre := by
    have hdis := (List.nodup_append.mp hpnd).2.2
    intro hi
    exact hdis ij.1 hi ij.1 (by simp) rfl
  have htake : (positiveLabels gaps).take ((positiveLabels gaps).idxOf ij.1) = pre := by
    rw [hps,List.idxOf_append_of_notMem hnot,List.idxOf_cons_self]
    simp
  dsimp only [IsStrictSplit]
  rw [htake]
  refine ⟨r,hrp,hj,?_,?_⟩
  · rw [← htr.2] at hlo
    have hh : ((pre.map (actualSource (period gaps) (necklaceSeed gaps))).sum : ℚ) <
        (threshold gaps r : ℚ) := by simpa only [int_list_cast,zero_add] using hlo
    exact_mod_cast hh
  · rw [← htr.2] at hup
    have hh : (threshold gaps r : ℚ) <
        (((pre.map (actualSource (period gaps) (necklaceSeed gaps))).sum +
          actualSource (period gaps) (necklaceSeed gaps) ij.1 : ℤ) : ℚ) := by simpa only [int_list_cast,zero_add,Int.cast_add] using hup
    exact_mod_cast hh

private def physicalCharge {p : ℕ} (gaps : Fin p → ℕ) (i : Fin (period gaps)) : ℤ :=
  2 * actualSource (period gaps) (necklaceSeed gaps) i -
    actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc

private theorem physical_charge_nonneg {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (i : Fin (period gaps)) : 0 ≤ physicalCharge gaps i := by
  have hi : i ∈ positiveLabels gaps ++ (thresholdTerminals gaps).map Prod.fst :=
    (physical_inventory gaps hg).mem_iff.mpr (List.mem_finRange i)
  rcases List.mem_append.mp hi with hi | hi
  · exact sub_nonneg.mpr (positive_coordinates gaps hg i hi).2.2.2
  · obtain ⟨t,ht,hfi⟩ := List.mem_map.mp hi
    obtain ⟨r,hr,htr⟩ := List.mem_filterMap.mp ht
    have hrp := List.mem_range.mp (List.mem_reverse.mp hr)
    obtain ⟨hit,hf,hg',hn,hnb,hnh,htaup,rest⟩ := terminal_coordinates gaps hg r hrp
    simp only [labelAt,dif_pos hit,Option.map_some,Option.some.injEq] at htr
    subst t
    dsimp only at hfi
    rw [← hfi]
    dsimp only [physicalCharge]
    rw [hf,hg']
    linarith

private theorem physical_charge_sum {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    ((List.finRange (period gaps)).map (physicalCharge gaps)).sum = (necklaceSeed gaps : ℤ) := by
  have hlin : ∀ xs : List (Fin (period gaps)),
      (xs.map (physicalCharge gaps)).sum =
        2 * (xs.map (actualSource (period gaps) (necklaceSeed gaps))).sum -
          (xs.map (fun i => actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih => simp only [List.map_cons,List.sum_cons,ih,physicalCharge]; ring
  rw [hlin,(necklace_physical_totals hp gaps hg).1,
    (necklace_physical_totals hp gaps hg).2.1]
  ring

private def positiveChain {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : List (Fin (period gaps)) :=
  (List.range (chainGap gaps r - 1)).filterMap
    (fun t => labelAt (period gaps) (chainStart gaps r + t))

private theorem positive_chain_order {p : ℕ} (gaps : Fin p → ℕ) :
    positiveLabels gaps = (List.range p).reverse.flatMap (positiveChain gaps) := by
  simp only [positiveLabels,positiveIndices,List.filterMap_flatMap,List.filterMap_map]
  rfl

private theorem label_projection {β : Type*} (k : ℕ) (rs : List ℕ) (idx : ℕ → ℕ)
    (f : Fin k → β) (v : ℕ → β)
    (hv : ∀ r ∈ rs, ∃ hi : idx r < k, f ⟨idx r,hi⟩ = v r) :
    ((rs.filterMap (fun r => labelAt k (idx r))).map f) = rs.map v := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨hi,hf⟩ := hv r (by simp)
    have ht : ∀ s ∈ rs, ∃ hi : idx s < k, f ⟨idx s,hi⟩ = v s :=
      fun s hs => hv s (by simp [hs])
    simpa [labelAt,hi,hf] using congrArg (List.cons (v r)) (ih ht)

private theorem geometric_list (n : ℕ) (h : ℤ) :
    ((List.range n).map (fun t => (2 : ℤ)^t * h)).sum = ((2 : ℤ)^n - 1) * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    simp only [List.map_singleton,List.sum_singleton,pow_succ]
    ring

private theorem chain_mass_charge {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) :
    ((positiveChain gaps r).map (actualSource (period gaps) (necklaceSeed gaps))).sum =
      demand gaps r + cyclicHead gaps (r + 1) - cyclicHead gaps r ∧
    ((positiveChain gaps r).map (physicalCharge gaps)).sum + terminalCharge gaps r =
      winding gaps (r + 1) - winding gaps r := by
  rcases necklace_chain_coordinates gaps hg r hr with
    ⟨hk,hep,heb,hhp,hhb,hhp',hhb',hho,hho',hz0,hzh,hz'p,hz'h,hz'o,
      hstep,hzstep,hw,hn,htau,hnb,hnh,htaup,htaub,hP,hC,hdir,hpeak,hfresh,hpos,hneg⟩
  have hm := label_projection (period gaps) (List.range (chainGap gaps r - 1))
    (fun t => chainStart gaps r + t) (actualSource (period gaps) (necklaceSeed gaps))
    (fun t => (2 : ℤ)^t * cyclicHead gaps r) (by
      intro t ht
      obtain ⟨hi,hmp,hmb,hcp,hcb,hf,hg⟩ := hpos t (by have := List.mem_range.mp ht; omega)
      exact ⟨hi,hf⟩)
  have hc := label_projection (period gaps) (List.range (chainGap gaps r - 1))
    (fun t => chainStart gaps r + t) (physicalCharge gaps)
    (fun t => (2 : ℤ)^t * winding gaps r) (by
      intro t ht
      obtain ⟨hi,hmp,hmb,hcp,hcb,hf,hg⟩ := hpos t (by have := List.mem_range.mp ht; omega)
      refine ⟨hi,?_⟩
      dsimp only [physicalCharge]
      rw [hf,hg]
      ring)
  constructor
  · rw [positiveChain,hm,geometric_list]
    exact hP
  · rw [positiveChain,hc,geometric_list]
    exact hC

private theorem chain_suffix_totals {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r ≤ p) :
    ((((List.range p).drop r).flatMap (positiveChain gaps)).map
      (actualSource (period gaps) (necklaceSeed gaps))).sum =
        threshold gaps r + (necklaceSeed gaps : ℤ) - cyclicHead gaps r ∧
    ((((List.range p).drop r).flatMap (positiveChain gaps)).map
      (physicalCharge gaps)).sum +
      (((List.range p).drop r).map (terminalCharge gaps)).sum =
        (necklaceSeed gaps : ℤ) - winding gaps r := by
  by_cases he : r = p
  · subst r
    obtain ⟨h0,hp,z0,zp,s0,sp⟩ := necklace_endpoints gaps
    have hd : (List.range p).drop p = [] := by simp
    rw [hd]
    simp [hp,zp,threshold_last]
  · have hrp : r < p := by omega
    have ih := chain_suffix_totals gaps hg (r + 1) (by omega)
    have hi : r < (List.range p).length := by simpa using hrp
    rw [List.drop_eq_getElem_cons hi,List.getElem_range hi]
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    obtain ⟨hm,hc⟩ := chain_mass_charge gaps hg r hrp
    rw [hm,threshold_step gaps r hrp]
    constructor <;> linarith [ih.1,ih.2]
termination_by p - r


private def shiftCorner {k : ℕ} (d : ℕ) (c : CornerRecord k) : CornerRecord k :=
  { c with prefixLength := c.prefixLength + d }

private def blockCorners {k : ℕ} : List (RoundBlock (Fin k)) → List (CornerRecord k)
  | [] => []
  | .one _ :: bs => (blockCorners bs).map (shiftCorner 1)
  | .cut i j _ :: bs => ⟨2,i,j⟩ :: (blockCorners bs).map (shiftCorner 2)

private theorem block_corner_projections {k : ℕ} (bs : List (RoundBlock (Fin k))) :
    (blockCorners bs).map CornerRecord.prefixLength =
      (cornerPositions bs).map (fun n => n + 1) ∧
    (blockCorners bs).map (fun c => (c.positive,c.terminal)) = splitPairs bs ∧
    (blockCorners bs).length = (splitPairs bs).length := by
  induction bs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons b bs ih =>
    cases b with
    | one i =>
      refine ⟨?_,?_,?_⟩
      · have hs := congrArg (List.map (fun n : ℕ => n + 1)) ih.1
        simpa only [blockCorners,cornerPositions,List.map_map,Function.comp_def,shiftCorner] using hs
      · simpa only [blockCorners,splitPairs,List.map_map,Function.comp_def,shiftCorner] using ih.2.1
      · simpa only [blockCorners,splitPairs,List.length_map] using ih.2.2
    | cut i j t =>
      refine ⟨?_,?_,?_⟩
      · have hs := congrArg (List.map (fun n : ℕ => n + 2)) ih.1
        simp only [blockCorners,cornerPositions,List.map_cons,List.map_map,Function.comp_def,shiftCorner]
        congr 1
        simpa only [List.map_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs
      · simpa only [blockCorners,splitPairs,List.map_cons,List.map_map,Function.comp_def,shiftCorner]
          using congrArg (List.cons (i,j)) ih.2.1
      · simpa only [blockCorners,splitPairs,List.length_cons,List.length_map] using congrArg Nat.succ ih.2.2

private theorem block_corner_locations {k : ℕ} (bs : List (RoundBlock (Fin k))) :
    ∀ c ∈ blockCorners bs, ∃ u v u' v' : List (Fin k),
      plusWord bs = u ++ [c.positive,c.terminal] ++ v ∧
      minusWord bs = u' ++ [c.terminal,c.positive] ++ v' ∧
      c.prefixLength = u.length + 2 ∧ c.prefixLength = u'.length + 2 := by
  induction bs with
  | nil => simp [blockCorners]
  | cons b bs ih =>
    cases b with
    | one i =>
      intro c hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      obtain ⟨u,v,u',v',hwp,hwm,hu,hu'⟩ := ih d hd
      refine ⟨i::u,v,i::u',v',?_,?_,?_,?_⟩
      · simpa only [plusWord,shiftCorner,List.cons_append] using congrArg (List.cons i) hwp
      · simpa only [minusWord,shiftCorner,List.cons_append] using congrArg (List.cons i) hwm
      · dsimp only [shiftCorner]; simp only [List.length_cons]; omega
      · dsimp only [shiftCorner]; simp only [List.length_cons]; omega
    | cut i j t =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨[],plusWord bs,[],minusWord bs,rfl,rfl,rfl,rfl⟩
      · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
        obtain ⟨u,v,u',v',hwp,hwm,hu,hu'⟩ := ih d hd
        refine ⟨i::j::u,v,j::i::u',v',?_,?_,?_,?_⟩
        · simpa only [plusWord,shiftCorner,List.cons_append] using congrArg (fun w => i::j::w) hwp
        · simpa only [minusWord,shiftCorner,List.cons_append] using congrArg (fun w => j::i::w) hwm
        · dsimp only [shiftCorner]; simp only [List.length_cons]; omega
        · dsimp only [shiftCorner]; simp only [List.length_cons]; omega

private theorem int_prefix_cast {α : Type*} (f : α → ℤ) (w : List α) (n : ℕ) :
    prefixSum (fun i => (f i : ℚ)) w n = (((w.take n).map f).sum : ℤ) := by
  unfold prefixSum
  generalize w.take n = xs
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

private theorem new_prefix_succ {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (w : List (Fin (period gaps))) (n : ℕ) :
    newPrefix (period gaps) (necklaceSeed gaps) w (n + 1) =
      (necklaceSeed gaps : ℤ) + ((w.take n).map
        (fun i => actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc)).sum := by
  simp [newPrefix,earWord,List.map_map,Function.comp_def,
    (necklace_physical_totals hp gaps hg).2.2]

private theorem old_prefix_succ {k e : ℕ} (w : List (Fin k)) (n : ℕ) :
    oldPrefix k e w (n + 1) = ((w.take n).map (actualSource k e)).sum := by
  simp [oldPrefix]

private theorem ear0_perm (k : ℕ) (w : List (Fin k))
    (hw : w.Perm (List.finRange k)) :
    (earWord k w 0).Perm (List.finRange (k + 1)) := by
  have hp := (hw.map Fin.castSucc).cons (Fin.last k)
  have hq : (Fin.last k :: (List.finRange k).map Fin.castSucc).Perm
      ((List.finRange k).map Fin.castSucc ++ [Fin.last k]) := List.perm_append_comm
  simpa only [earWord,List.take_zero,List.map_nil,List.drop_zero,List.nil_append,
    List.singleton_append,← List.finRange_succ_last] using hp.trans hq

private theorem physical_error_card (m : ℕ) (P : Fin m → Prop) [DecidablePred P]
    (corners : List ℕ) (h : ∀ q, P q → q.val ∈ corners) :
    (Finset.univ.filter P).card ≤ corners.length := by
  have hc : (Finset.univ.filter P).card ≤ corners.toFinset.card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro q hq
      exact List.mem_toFinset.mpr (h q (Finset.mem_filter.mp hq).2)
    · intro a _ b _ he
      exact Fin.ext he
  exact hc.trans (List.toFinset_card_le _)


private theorem physical_rounding_of_fractional_fit {p : ℕ} (hp : 1 ≤ p)
    (gaps : Fin p → ℕ) (hg : ∀ j, 2 ≤ gaps j)
    (hfit : FractionalFits
      (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))
      (fun i => (actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc : ℚ))
      ((modulus (period gaps) / 2 : ℤ) : ℚ) (modulus (period gaps))
      0 (necklaceSeed gaps) (necklaceBlocks gaps)) : PhysicalRounding gaps := by
  classical
  let k := period gaps
  let e := necklaceSeed gaps
  let N := modulus k
  let H := N / 2
  let f := actualSource k e
  let g := fun i : Fin k => actualSource (k + 1) (2 * e) i.castSucc
  let bs := necklaceBlocks gaps
  let wp := plusWord bs
  let wm := minusWord bs
  let cs := blockCorners bs
  have hwp : wp.Perm (List.finRange k) := necklace_blocks_inventory gaps hg
  have hnd : wp.Nodup := hwp.nodup_iff.mpr (List.nodup_finRange _)
  have hr := simultaneous_rounding (fun i => (f i : ℚ)) (fun i => (g i : ℚ))
    (H : ℚ) (N : ℚ) 0 (e : ℚ) bs hfit hnd
  rcases hr with ⟨hpm,hfs,hgs,hpairnd,hswap,hcornernd,hcornerlen,hcornerrange,
    hsigns,hprefix,hcornerloc,hpairloc,huppercard,hlowercard⟩
  have hwm : wm.Perm (List.finRange k) := hpm.symm.trans hwp
  have hpro := block_corner_projections bs
  have hcsp : cs.map CornerRecord.prefixLength =
      (cornerPositions bs).map (fun n => n + 1) := hpro.1
  have hcsij : cs.map (fun c => (c.positive,c.terminal)) = splitPairs bs := hpro.2.1
  have hlen : cs.length = (splitPairs bs).length := hpro.2.2
  have hcslen : cs.length ≤ p - 1 := hlen.trans_le (necklace_split_bound hp gaps hg)
  have hcsnd : (cs.map CornerRecord.prefixLength).Nodup := by
    rw [hcsp]
    exact hcornernd.map (by intro a b hab; dsimp at hab; omega)
  have hlabels : (cs.flatMap (fun c => [c.positive,c.terminal])).Nodup := by
    rw [← hcsij,List.flatMap_map] at hpairnd
    exact hpairnd
  have hcsmem : ∀ c ∈ cs, (c.positive,c.terminal) ∈ splitPairs bs := by
    intro c hc
    rw [← hcsij]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  have hcsprops : ∀ c ∈ cs,
      0 < f c.positive ∧ 0 < g c.positive ∧ f c.terminal < 0 ∧ g c.terminal < 0 ∧
      IsStrictSplit gaps c.positive c.terminal ∧
      ∃ u v u' v' : List (Fin k), wp = u ++ [c.positive,c.terminal] ++ v ∧
        wm = u' ++ [c.terminal,c.positive] ++ v' ∧
        c.prefixLength = u.length + 2 ∧ c.prefixLength = u'.length + 2 := by
    intro c hc
    obtain ⟨h1,h2,h3,h4⟩ := hsigns (c.positive,c.terminal) (hcsmem c hc)
    refine ⟨?_,?_,?_,?_,necklace_split_provenance gaps hg _ (hcsmem c hc),
      block_corner_locations bs c hc⟩
    · exact_mod_cast h1
    · exact_mod_cast h2
    · exact_mod_cast h3
    · exact_mod_cast h4
  have hpi : ∀ n : ℕ,
      0 ≤ ((wp.take n).map f).sum ∧
      0 ≤ (e : ℤ) + ((wp.take n).map g).sum ∧
      ((wm.take n).map f).sum ≤ H ∧
      (e : ℤ) + ((wm.take n).map g).sum ≤ N ∧
      (n ∉ cornerPositions bs →
        ((wp.take n).map f).sum ≤ H ∧
        (e : ℤ) + ((wp.take n).map g).sum ≤ N ∧
        0 ≤ ((wm.take n).map f).sum ∧
        0 ≤ (e : ℤ) + ((wm.take n).map g).sum) := by
    intro n
    have hh := hprefix n
    simp only [int_prefix_cast,zero_add] at hh
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2.1
    · exact_mod_cast hh.2.2.1
    · exact_mod_cast hh.2.2.2.1
    · intro hn
      have ht := hh.2.2.2.2 hn
      refine ⟨?_,?_,?_,?_⟩
      · exact_mod_cast ht.1
      · exact_mod_cast ht.2.1
      · exact_mod_cast ht.2.2.1
      · exact_mod_cast ht.2.2.2.1
  have hN : 0 ≤ N := by
    have hk := (necklace_chain_coordinates gaps hg 0 (by omega)).1
    exact le_of_lt (ZeroSumSubsets.source_cycle (by omega : 0 < k) e).1
  have hH : 0 ≤ H := Int.ediv_nonneg hN (by norm_num)
  have hplus : ∀ q, 0 ≤ oldPrefix k e wp q ∧ 0 ≤ newPrefix k e wp q := by
    intro q
    cases q with
    | zero => simp [oldPrefix,newPrefix]
    | succ n =>
      rw [old_prefix_succ,new_prefix_succ hp gaps hg]
      exact ⟨(hpi n).1,(hpi n).2.1⟩
  have hminus : ∀ q, oldPrefix k e wm q ≤ H ∧ newPrefix k e wm q ≤ N := by
    intro q
    cases q with
    | zero => simpa [oldPrefix,newPrefix] using And.intro hH hN
    | succ n =>
      rw [old_prefix_succ,new_prefix_succ hp gaps hg]
      exact ⟨(hpi n).2.2.1,(hpi n).2.2.2.1⟩
  have hbadplus : ∀ q, H < oldPrefix k e wp q ∨ N < newPrefix k e wp q →
      q ∈ cs.map CornerRecord.prefixLength := by
    intro q hq
    cases q with
    | zero => simp [oldPrefix,newPrefix] at hq; rcases hq with hq | hq <;> linarith
    | succ n =>
      have hn : n ∈ cornerPositions bs := by
        by_contra hn
        have hh := (hpi n).2.2.2.2 hn
        rw [old_prefix_succ,new_prefix_succ hp gaps hg] at hq
        rcases hq with hq | hq <;> linarith [hh.1,hh.2.1]
      rw [hcsp]
      exact List.mem_map.mpr ⟨n,hn,rfl⟩
  have hbadminus : ∀ q, oldPrefix k e wm q < 0 ∨ newPrefix k e wm q < 0 →
      q ∈ cs.map CornerRecord.prefixLength := by
    intro q hq
    cases q with
    | zero => simp [oldPrefix,newPrefix] at hq
    | succ n =>
      have hn : n ∈ cornerPositions bs := by
        by_contra hn
        have hh := (hpi n).2.2.2.2 hn
        rw [old_prefix_succ,new_prefix_succ hp gaps hg] at hq
        rcases hq with hq | hq <;> linarith [hh.2.2.1,hh.2.2.2]
      rw [hcsp]
      exact List.mem_map.mpr ⟨n,hn,rfl⟩
  have htotal (w : List (Fin k)) (hw : w.Perm (List.finRange k)) :
      oldPrefix k e w (k + 1) = 0 ∧ newPrefix k e w (k + 1) = 0 := by
    have hl : w.length = k := by simpa using hw.length_eq
    have ht : w.take k = w := List.take_of_length_le (by omega)
    have hf := (hw.map f).sum_eq.trans (necklace_physical_totals hp gaps hg).1
    have hg' := (hw.map g).sum_eq.trans (necklace_physical_totals hp gaps hg).2.1
    rw [old_prefix_succ,new_prefix_succ hp gaps hg,ht,hf,hg']
    simp
  unfold PhysicalRounding
  dsimp only
  refine ⟨wp,wm,cs,hwp,hwm,ear0_perm k wp hwp,ear0_perm k wm hwm,
    ?_,?_,(necklace_physical_totals hp gaps hg).2.2,
    (htotal wp hwp).1,(htotal wp hwp).2,(htotal wm hwm).1,(htotal wm hwm).2,
    hplus,hminus,hcslen,hcsnd,hlabels,hcsprops,?_,hbadplus,hbadminus,?_,?_⟩
  · simp [earWord]
  · simp [earWord]
  · rw [hcsij]; exact hswap
  · simpa only [List.length_map] using physical_error_card (k + 2)
      (fun q => H < oldPrefix k e wp q.val ∨ N < newPrefix k e wp q.val)
      (cs.map CornerRecord.prefixLength) (fun q hq => hbadplus q.val hq)
  · simpa only [List.length_map] using physical_error_card (k + 2)
      (fun q => oldPrefix k e wm q.val < 0 ∨ newPrefix k e wm q.val < 0)
      (cs.map CornerRecord.prefixLength) (fun q hq => hbadminus q.val hq)

end D5.S3.Combinatorics.Circle.SparseNecklaceRounding
