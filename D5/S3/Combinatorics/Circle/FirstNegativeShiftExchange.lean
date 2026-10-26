/- GID: D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FirstNegativeShiftExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Physical first-negative descent through prefixes and inverse parents. -/
module
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftCore

/-! # Arrival-free descent and conditional all-SMALL first-negative omission

The conditional shift retains all SMALL occurrences by reordering complete batches.
Low actual arrivals instead permit literal prefix truncation with strict G descent;
the full consumer therefore needs no arrival assumptions. The first-Y>P region
and original-quantifier C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open scoped BigOperators

/-- Inverse rotation keeps physical labels; source parity selects its value. -/
theorem negative_parent (k t : ℕ) (hk : 3 ≤ k) (y : Fin k)
    (hy : s k t y < 0) :
    let b := (finRotate k).symm y
    let Y := -s k t y
    (Y % 2 = 0 ∧ 2 * s k t b = -Y ∧ |s k t b| < Q k ∧ s k t b < 0) ∨
    (Y % 2 = 1 ∧ 2 * s k t b = N k - Y ∧ Q k ≤ s k t b) := by
  dsimp only
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  let b := (finRotate k).symm y
  have hb := centered_bounds hNp hNo ((2 : ℤ) ^ b.val * t)
  change -C k ≤ s k t b ∧ s k t b ≤ C k at hb
  have hyb := centered_bounds hNp hNo ((2 : ℤ) ^ y.val * t)
  change -C k ≤ s k t y ∧ s k t y ≤ C k at hyb
  have he := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2 b
  change 2 * s k t b - s k t (finRotate k b) = N k *
    (if N k < 4 * s k t b then 1 else if 4 * s k t b < -N k then -1 else 0) at he
  have hr : finRotate k b = y := (finRotate k).apply_symm_apply y
  rw [hr] at he
  dsimp only [b] at *
  split_ifs at he with hp hn
  · right
    simp only [mul_one] at he
    refine ⟨by omega, by omega, by omega⟩
  · simp only [mul_neg, mul_one] at he
    omega
  · left
    simp only [mul_zero] at he
    refine ⟨by omega, by omega, ?_, by omega⟩
    exact abs_lt.mpr ⟨by omega, by omega⟩

set_option maxHeartbeats 1400000 in
-- Three complete-batch reorderings and the physical inventory share one proof budget.
/-- Omit the FIRST physical negative y when -s(y)≤s(p).
Actual old arrivals after zpen AND z are measured at their full original
prefixes. All SMALL occurrences remain, in three complete reordered batches.
There is no crossing anchor, extra source edge, Bad count or bound Z≤D. -/
theorem actualSource_threeNegative_firstNegative_shift_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyupper : -s k t y ≤ s k t p)
    (harrivalpen : C k - s k t p ≤ mass (s k t)
      (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen]))
    (harrivalz : C k - s k t p ≤ mass (s k t)
      (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z]))
    (hblocklo : C k - s k t p <
      mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) <
      |s k t (hit k 1 p)|) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let Btail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
    ∃ L01 L2 LE : List (Fin k),
      L01.Perm (T0 ++ T1) ∧ L2.Perm T2 ∧ LE.Perm E ∧
      (let L := L01 ++ [zpen] ++ L2 ++ [z] ++ LE
       let V := A ++ [p, n] ++ L
       let e0 := mass (s k t) W - s k t y - s k t p
       (L ++ [y]).Perm Btail ∧ (∀ i ∈ S, i ∈ L) ∧
       Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧
         mass (s k t) (V.take d) ≤ C k) ∧
       Inventory k t W V [p, n] [x, y] ∧
       (V ++ [x, y]).Perm (W ++ [p, n]) ∧
       (∀ i ∈ [x, y], i ∉ V) ∧ zpen ∈ V ∧ z ∈ V ∧
       (∀ i ∈ W, |s k t i| < Q k → i ∈ V) ∧
       G k t V = G k t W ∧ U V = U W ∧
       remainingSmall t V = remainingSmall t W ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e0 ∧ 0 < e0 ∧ e0 < C k ∧
       remainingMass (s k t) V = -e0) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let S := smallWord T0 T1 T2 E
  let Btail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
  let P := f p
  let D := |f n|
  let r := |f x|
  let Y := -f y
  let δ := Y - P
  let a0 := mass f A
  let b := a0 + P - D
  let h := mass f W
  let e0 := h + Y - P
  -- B1/B2 end IMMEDIATELY BEFORE the respective retained negative.
  let B1 := A ++ [x] ++ T0 ++ [y] ++ T1
  let B2 := B1 ++ [zpen] ++ T2
  let d1 := mass f B1
  let a1 := d1 + f zpen
  let d2 := mass f B2
  let a2 := d2 + f z
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = r := by
    simpa [f, x, r, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : D < P := by
    have hh := geo.strictOrder.1
    change D < |f p| at hh
    simpa only [hpabs] using hh
  have hPr : P < r := by
    have hh := geo.strictOrder.2
    change |f p| < r at hh
    simpa only [hpabs] using hh
  have hD : Q k ≤ D := hnlarge
  have hreq : r = 2 * P - D := by
    have hn := geo.firstEquation
    have hx := geo.secondEquation
    change D = N k - 2 * |f p| at hn
    change r = 4 * |f p| - N k at hx
    rw [hpabs] at hn hx
    omega
  have hbudget : 2 * P ≤ C k + Q k := by
    have hh := geo.budget
    change 2 * |f p| ≤ C k + Q k at hh
    simpa only [hpabs] using hh
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hodd _)
  have hPcap : P ≤ C k := by simpa only [hpabs] using hbound p
  have hY : Q k ≤ Y := hylarge
  have hYP : Y ≤ P := hyupper
  have hδ : δ ≤ 0 := by dsimp only [δ]; omega
  have hfloor : 0 ≤ C k + Y - 2 * P := by omega
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsAfterA⟩ := strip_split A ([x] ++ Btail)
    (by simpa only [W, oldWord, x, Btail, List.append_assoc] using hsW)
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa [a0, mass] using inStrip_prefix hsAfterA 0
  have hax : 0 ≤ a0 + r ∧ a0 + r ≤ C k := by
    simpa [a0, mass, hxval] using inStrip_prefix hsAfterA 1
  have hb : 0 ≤ b ∧ b ≤ C k - P := by dsimp only [b]; omega
  have hbst : 0 ≤ b ∧ b ≤ C k := by omega
  have hs1 := (strip_split B1 ([zpen] ++ T2 ++ [z] ++ E)
    (by simpa only [W, oldWord, B1, x, List.append_assoc] using hsW)).2
  have hd1 : 0 ≤ d1 ∧ d1 ≤ C k := by
    simpa [d1, mass] using inStrip_prefix hs1 0
  have ha1 : 0 ≤ a1 ∧ a1 ≤ C k := by
    simpa [a1, d1, mass] using inStrip_prefix hs1 1
  have hs2old := (strip_split B2 ([z] ++ E)
    (by simpa only [W, oldWord, B2, B1, x, List.append_assoc] using hsW)).2
  have hd2 : 0 ≤ d2 ∧ d2 ≤ C k := by
    simpa [d2, mass] using inStrip_prefix hs2old 0
  have ha2 : 0 ≤ a2 ∧ a2 ≤ C k := by
    simpa [a2, d2, mass] using inStrip_prefix hs2old 1
  have hmeasure1 : C k - P ≤ a1 := by
    simpa [a1, d1, B1, x, P, f, mass, add_assoc] using harrivalpen
  have hmeasure2 : C k - P ≤ a2 := by
    simpa [a2, d2, B2, B1, x, P, f, mass, add_assoc] using harrivalz
  have ha1dep : a1 ≤ d1 := by
    have hz : Q k ≤ -f zpen := hzpenlarge
    dsimp only [a1]
    omega
  have ha2dep : a2 ≤ d2 := by
    have hz : Q k ≤ -f z := hzlarge
    dsimp only [a2]
    omega
  have hshift1 : (0 ≤ d1 + δ ∧ d1 + δ ≤ C k) ∧
      (0 ≤ a1 + δ ∧ a1 + δ ≤ C k) := by
    dsimp only [δ]
    constructor <;> constructor <;> omega
  have hshift2 : (0 ≤ d2 + δ ∧ d2 + δ ≤ C k) ∧
      (0 ≤ a2 + δ ∧ a2 + δ ≤ C k) := by
    dsimp only [δ]
    constructor <;> constructor <;> omega
  have he0 : 0 < e0 ∧ e0 < C k := by
    have hlo : C k - P < h := hblocklo
    have hhi : h < D := hblockhi
    dsimp only [e0]
    omega
  obtain ⟨L01, L2, LE, h01, h2, hE, htail, hSretained,
      hv, hn, hs, hpref, inv, hp, habs, hzp, hz, hretain,
      hg, hu, hsm, hH, hHs, hj, hend, _, _, hcomp⟩ :=
    complete_small_shift k t hk p y zpen z A T0 T1 T2 E [] E []
      hpositive hnlarge hexpand hW hpunused hnunused hsmall hylarge
      (by simp) (by intro i hi; exact hsmall i (by simp [smallWord, hi]))
      (by simp) (by simp) (by simpa using hW.1)
      (by simpa [d1, B1, δ, Y, P, a1, f, x, mass] using hshift1)
      (by simpa [d2, B2, B1, δ, Y, P, a2, f, x, mass, add_assoc] using hshift2)
      (by simpa [e0, h, Y, P, mass, sub_eq_add_neg] using
        (show 0 ≤ e0 ∧ e0 ≤ C k from ⟨he0.1.le, he0.2.le⟩))
  simp only [List.append_nil] at h01 htail inv hp hu hsm
  simp only [mass, List.map_nil, List.sum_nil, add_zero] at hend hcomp
  refine ⟨L01, L2, LE, h01, h2, hE, htail, hSretained, hv, hn, hs, hpref,
    inv, hp, habs, hzp, hz, hretain, hg, hu, hsm, hH, hHs, hj, ?_, ?_, ?_, ?_⟩
  · simpa only [mass] using hend
  · simpa [e0, h, Y, P, sub_eq_add_neg] using he0.1
  · simpa [e0, h, Y, P, sub_eq_add_neg] using he0.2
  · simpa only [mass] using hcomp

/-- A low old prefix can receive the fresh native pair. The discarded suffix may
contain SMALL occurrences: its full physical inventory, rather than uniform
SMALL retention, controls the exact balances. Consumed by the arrival-free exchange. -/
theorem actualSource_prefix_pair_truncation
    (k t : ℕ) (hk : 3 ≤ k) (p : Fin k) (F R : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (F ++ R))
    (hpunused : p ∉ F ++ R) (hnunused : hit k 1 p ∉ F ++ R)
    (hcut : mass (s k t) F ≤ C k - s k t p)
    (hreturn : largeUsed k t R ≤ 1) :
    let n := hit k 1 p
    let W := F ++ R
    let V := F ++ [p, n]
    Legal k t V ∧ Inventory k t W V [p, n] R ∧
    (V ++ R).Perm (W ++ [p, n]) ∧
    G k t V + 2 = G k t W + largeUsed k t R ∧
    G k t V < G k t W ∧ J k t V < J k t W := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let D := |f n|
  have geo := native_geometry hk t p hnlarge hexpand
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hDP : D < f p := by
    simpa only [abs_of_pos hpositive] using geo.strictOrder.1
  have hp0 : 0 < f p := hpositive
  have hD : 0 ≤ D := abs_nonneg _
  have hsF := (strip_split F R (strip_of_legal hW)).1
  have hv : 0 ≤ mass f F ∧ mass f F ≤ C k := by
    simpa [f, mass] using inStrip_prefix hsF F.length
  have hsPN : InStrip f (C k) (mass f F) [p, n] := by
    change 0 ≤ mass f F ∧ mass f F ≤ C k ∧
      0 ≤ mass f F + f p ∧ mass f F + f p ≤ C k ∧
      0 ≤ mass f F + f p + f n ∧ mass f F + f p + f n ≤ C k
    rw [hnval]
    change mass f F ≤ C k - f p at hcut
    omega
  have hsV : InStrip f (C k) 0 (F ++ [p, n]) :=
    inStrip_append hsF (by simpa [mass] using hsPN)
  have hI : [p, n].Nodup := by
    have hpn : p ≠ n := by intro he; have hv := congrArg f he; omega
    simp [hpn]
  have hIW (i : Fin k) (hi : i ∈ [p, n]) : i ∉ F ++ R := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hpunused
    · exact hnunused
  have hIL (i : Fin k) (hi : i ∈ [p, n]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
  have hperm : ((F ++ [p, n]) ++ R).Perm ((F ++ R) ++ [p, n]) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm : ([p, n] ++ R).Perm (R ++ [p, n])).append_left F
  have inv := inventory_of_perm hk t (F ++ R) (F ++ [p, n]) [p, n] R
    hW.1 hI hIW (fun i hi => List.mem_append_right F hi) hIL hperm
  have hIlarge : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  have hbal : G k t (F ++ [p, n]) + 2 = G k t (F ++ R) + largeUsed k t R := by
    simpa only [hIlarge] using inv.largeBalance
  have hG : G k t (F ++ [p, n]) < G k t (F ++ R) := by omega
  have hJ : J k t (F ++ [p, n]) < J k t (F ++ R) :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl hG)
  exact ⟨legal_of_strip inv.nodup hsV, inv, hperm, hbal, hG, hJ⟩

/-- With the original native source hypotheses and Y≤P, an actual strict-J
competitor always exists. Low arrivals give literal prefix cuts; only the
remaining shift branch asserts retention of every SMALL and strict H descent. -/
theorem actualSource_threeNegative_firstNegative_arrival_free_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyupper : -s k t y ≤ s k t p)
    (hblocklo : C k - s k t p <
      mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) <
      |s k t (hit k 1 p)|) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let Btail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
    let Fpen := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
    let Rpen := T2 ++ [z] ++ E
    let Fz := Fpen ++ T2 ++ [z]
    ∃ V R : List (Fin k),
      Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
      (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧
        mass (s k t) (V.take d) ≤ C k) ∧
      Inventory k t W V [p, n] R ∧
      (V ++ R).Perm (W ++ [p, n]) ∧ J k t V < J k t W ∧
      ((mass (s k t) Fpen ≤ C k - s k t p ∧
        V = Fpen ++ [p, n] ∧ R = Rpen ∧ largeUsed k t R = 1 ∧
        G k t V + 1 = G k t W ∧ G k t V < G k t W) ∨
       (C k - s k t p < mass (s k t) Fpen ∧
        mass (s k t) Fz ≤ C k - s k t p ∧
        V = Fz ++ [p, n] ∧ R = E ∧ largeUsed k t R = 0 ∧
        G k t V + 2 = G k t W ∧ G k t V < G k t W) ∨
       (C k - s k t p < mass (s k t) Fpen ∧
        C k - s k t p < mass (s k t) Fz ∧ R = [x, y] ∧
        ∃ L01 L2 LE : List (Fin k),
          L01.Perm (T0 ++ T1) ∧ L2.Perm T2 ∧ LE.Perm E ∧
          (let L := L01 ++ [zpen] ++ L2 ++ [z] ++ LE
           let e0 := mass (s k t) W - s k t y - s k t p
           V = A ++ [p, n] ++ L ∧ (L ++ [y]).Perm Btail ∧
           (∀ i ∈ S, i ∈ L) ∧ (∀ i ∈ R, i ∉ V) ∧ zpen ∈ V ∧ z ∈ V ∧
           (∀ i ∈ W, |s k t i| < Q k → i ∈ V) ∧
           G k t V = G k t W ∧ U V = U W ∧
           remainingSmall t V = remainingSmall t W ∧
           H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs =
             H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
           H k t V < H k t W ∧
           mass (s k t) V = e0 ∧ 0 < e0 ∧ e0 < C k ∧
           remainingMass (s k t) V = -e0))) := by
  classical
  dsimp only
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let Fpen := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
  let Rpen := T2 ++ [z] ++ E
  let Fz := Fpen ++ T2 ++ [z]
  have hWpen : W = Fpen ++ Rpen := by
    simp only [W, oldWord, Fpen, Rpen, x, List.append_assoc]
  have hWz : W = Fz ++ E := by
    simp only [W, oldWord, Fz, Fpen, x, List.append_assoc]
  have hE : largeUsed k t E = 0 := (small_weights t E (by
    intro i hi
    exact hsmall i (by simp [smallWord, hi]))).1
  have hT2 : largeUsed k t T2 = 0 := (small_weights t T2 (by
    intro i hi
    exact hsmall i (by simp [smallWord, hi]))).1
  have hzL : Large k t z := by
    have hz := neg_le_abs (s k t z)
    unfold Large
    change Q k ≤ |s k t z|
    omega
  have hRpen : largeUsed k t Rpen = 1 := by
    simp [Rpen, largeUsed_append, largeUsed_cons, largeWeight, hzL, hT2, hE]
  by_cases hpen : mass (s k t) Fpen ≤ C k - s k t p
  · obtain ⟨hv, inv, hp, hb, hg, hj⟩ := actualSource_prefix_pair_truncation
      k t hk p Fpen Rpen hpositive hnlarge hexpand
      (hWpen ▸ hW) (hWpen ▸ hpunused) (hWpen ▸ hnunused) hpen (by omega)
    rw [← hWpen] at inv hp hb hg hj
    refine ⟨Fpen ++ [p, n], Rpen, hv, hv.1, strip_of_legal hv, hv.2,
      inv, hp, hj, Or.inl ⟨hpen, rfl, rfl, hRpen, ?_, hg⟩⟩
    rw [hRpen] at hb
    change G k t (Fpen ++ [p, n]) + 2 = G k t W + 1 at hb
    change G k t (Fpen ++ [p, n]) + 1 = G k t W
    omega
  · by_cases hzcut : mass (s k t) Fz ≤ C k - s k t p
    · obtain ⟨hv, inv, hp, hb, hg, hj⟩ := actualSource_prefix_pair_truncation
        k t hk p Fz E hpositive hnlarge hexpand
        (hWz ▸ hW) (hWz ▸ hpunused) (hWz ▸ hnunused) hzcut (by omega)
      rw [← hWz] at inv hp hb hg hj
      refine ⟨Fz ++ [p, n], E, hv, hv.1, strip_of_legal hv, hv.2,
        inv, hp, hj, Or.inr (Or.inl ⟨lt_of_not_ge hpen, hzcut, rfl, rfl, hE, ?_, hg⟩)⟩
      simpa only [hE, Nat.add_zero] using hb
    · have hpa : C k - s k t p ≤ mass (s k t)
          (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen]) := by
        change C k - s k t p ≤ mass (s k t) Fpen
        omega
      have hza : C k - s k t p ≤ mass (s k t)
          (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z]) := by
        change C k - s k t p ≤ mass (s k t) Fz
        omega
      obtain ⟨L01, L2, LE, h01, h2, he, htail, hS, hv, hn, hs, hpref,
        inv, hp, hr, hzp, hz, hretain, hg, hu, hsmallEq, henergy, hstrict, hj,
        hend, he0, heC, hcomp⟩ :=
        actualSource_threeNegative_firstNegative_shift_exchange_full
          k t hk p y zpen z A T0 T1 T2 E hpositive hnlarge hexpand hW
          hpunused hnunused hsmall hylarge hzpenlarge hzlarge hyupper hpa hza hblocklo hblockhi
      refine ⟨A ++ [p, n] ++ (L01 ++ [zpen] ++ L2 ++ [z] ++ LE), [x, y],
        hv, hn, hs, hpref, inv, hp, hj, Or.inr (Or.inr ⟨lt_of_not_ge hpen, lt_of_not_ge hzcut, rfl,
          L01, L2, LE, h01, h2, he, rfl, htail, hS, hr, hzp, hz, hretain,
          hg, hu, hsmallEq, henergy, hstrict, hend, he0, heC, hcomp⟩)⟩

set_option maxHeartbeats 1800000 in
/-- An actual even first-negative half is either fresh or relocated out of the
terminal SMALL batch. Low old arrivals use literal G-decreasing truncations;
otherwise every old SMALL survives the complete three-batch H descent. -/
theorem actualSource_threeNegative_even_half_arrival_free_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyhigh : s k t p < -s k t y)
    (hyeven : (-s k t y) % 2 = 0)
    (hyboundary : s k t (hit k 2 p) ≤ -s k t y + 1)
    (hhalf : (finRotate k).symm y ∉ oldWord p y zpen z A T0 T1 T2 E ∨
      (finRotate k).symm y ∈ E)
    (hblocklo : C k - s k t p < mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) <
      |s k t (hit k 1 p)|) :
    let n := hit k 1 p
    let x := hit k 2 p
    let b := (finRotate k).symm y
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let Extra := if b ∈ E then [] else [b]
    let Efinal := if b ∈ E then E.erase b else E
    let Fpen := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
    let Rpen := T2 ++ [z] ++ E
    let Fz := Fpen ++ T2 ++ [z]
    s k t b = -((-s k t y) / 2) ∧ s k t b < 0 ∧ |s k t b| < Q k ∧
    ∃ V R : List (Fin k),
      Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
      (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧ mass (s k t) (V.take d) ≤ C k) ∧
      J k t V < J k t W ∧
      ((Inventory k t W V [p, n] R ∧ (V ++ R).Perm (W ++ [p, n]) ∧
        G k t V < G k t W ∧
        ((mass (s k t) Fpen ≤ C k - s k t p ∧ V = Fpen ++ [p, n] ∧
          R = Rpen ∧ G k t V + 1 = G k t W) ∨
         (C k - s k t p < mass (s k t) Fpen ∧
          mass (s k t) Fz ≤ C k - s k t p ∧ V = Fz ++ [p, n] ∧
          R = E ∧ G k t V + 2 = G k t W))) ∨
       (C k - s k t p < mass (s k t) Fpen ∧
        C k - s k t p < mass (s k t) Fz ∧ R = [x, y] ∧
        ∃ L01 L2 LE : List (Fin k),
          L01.Perm (T0 ++ T1 ++ [b]) ∧ L2.Perm T2 ∧ LE.Perm Efinal ∧
          (let L := L01 ++ [zpen] ++ L2 ++ [z] ++ LE
           let I := [p, n] ++ Extra
           let e := mass (s k t) W - s k t y + mass (s k t) Extra - s k t p
           V = A ++ [p, n] ++ L ∧
           (L ++ [y]).Perm ((T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E) ++ Extra) ∧
           (∀ i ∈ S, i ∈ L) ∧ Inventory k t (W ++ Extra) V [p, n] [x, y] ∧
           (V ++ [x, y]).Perm (W ++ I) ∧
           V.toFinset = (W.toFinset \ {x, y}) ∪ I.toFinset ∧
           Disjoint (W.toFinset \ {x, y}) I.toFinset ∧
           V.toFinsetᶜ = (W.toFinsetᶜ \ I.toFinset) ∪ {x, y} ∧
           Disjoint (W.toFinsetᶜ \ I.toFinset) {x, y} ∧
           (∀ i ∈ [x, y], i ∉ V) ∧ zpen ∈ V ∧ z ∈ V ∧
           (∀ i ∈ W, |s k t i| < Q k → i ∈ V) ∧
           G k t V = G k t W ∧ U V + Extra.length = U W ∧
           remainingSmall t V = remainingSmall t W \ Extra.toFinset ∧
           H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs =
             H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
           H k t V < H k t W ∧ mass (s k t) V = e ∧ 0 ≤ e ∧ e < C k ∧
           (b ∈ E → 0 < e) ∧ remainingMass (s k t) V = -e))) := by
  classical
  dsimp only
  let n := hit k 1 p
  let x := hit k 2 p
  let b := (finRotate k).symm y
  let W := oldWord p y zpen z A T0 T1 T2 E
  let P := (s k t) p
  let D := |(s k t) n|
  let Y := -(s k t) y
  let μ := Y / 2
  let Extra : List (Fin k) := if b ∈ E then [] else [b]
  let Efinal := if b ∈ E then E.erase b else E
  let Fpen := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
  let Rpen := T2 ++ [z] ++ E
  let Fz := Fpen ++ T2 ++ [z]
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hp : 0 < P := hpositive
  have hy : (s k t) y < 0 := by have hh : P < -(s k t) y := hyhigh; omega
  have hbval : (s k t) b = -μ ∧ (s k t) b < 0 ∧ |(s k t) b| < Q k := by
    rcases negative_parent k t hk y hy with he | ho
    · change Y % 2 = 0 ∧ 2 * (s k t) b = -Y ∧ |(s k t) b| < Q k ∧ (s k t) b < 0 at he
      exact ⟨by dsimp only [μ]; omega, he.2.2.2, he.2.2.1⟩
    · omega
  have hYeq : Y = 2 * μ := by change Y % 2 = 0 at hyeven; dsimp only [μ]; omega
  have hμpos : 0 < μ := by have hh := hbval.2.1; rw [hbval.1] at hh; omega
  have hμ : 0 < μ ∧ μ < Q k := by
    refine ⟨hμpos, ?_⟩
    have hh := hbval.2.2
    simpa only [hbval.1, abs_neg, abs_of_pos hμpos] using hh
  have hYP : P < Y := hyhigh
  have hnval : (s k t) n = -D := by
    simpa [n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hDP : D < P := by simpa [D, n, abs_of_pos hpositive] using geo.strictOrder.1
  have hreq : (s k t) x = 2 * P - D := by
    have he1 := geo.firstEquation
    have he2 := geo.secondEquation
    change D = N k - 2 * |(s k t) p| at he1
    change |(s k t) x| = 4 * |(s k t) p| - N k at he2
    have hx : (s k t) x = |(s k t) x| := by
      simpa [x, orient, show ¬ s k t p < 0 by omega] using geo.xValue
    rw [abs_of_pos hpositive] at he1 he2
    omega
  have hDN : D = N k - 2 * P := by simpa [D, n, P, abs_of_pos hpositive] using geo.firstEquation
  have hboundary : 0 ≤ C k + 1 + μ - 2 * P := by
    change (s k t) x ≤ Y + 1 at hyboundary
    omega
  have hdelta : μ - P < 0 := by
    have hb := centered_bounds hNp hNo ((2 : ℤ) ^ y.val * t)
    change -C k ≤ (s k t) y ∧ (s k t) y ≤ C k at hb
    have hd := geo.nLarge
    change Q k ≤ D at hd
    omega
  refine ⟨hbval.1, hbval.2.1, hbval.2.2, ?_⟩
  have hWpen : W = Fpen ++ Rpen := by simp [W, oldWord, Fpen, Rpen, x, List.append_assoc]
  have hWz : W = Fz ++ E := by simp [W, oldWord, Fz, Fpen, x, List.append_assoc]
  have hE : largeUsed k t E = 0 := (small_weights t E (by
    intro i hi; exact hsmall i (by simp [smallWord, hi]))).1
  have hT2 : largeUsed k t T2 = 0 := (small_weights t T2 (by
    intro i hi; exact hsmall i (by simp [smallWord, hi]))).1
  have hzL : Large k t z := by have hh := neg_le_abs ((s k t) z); change Q k ≤ |(s k t) z|; omega
  have hRpen : largeUsed k t Rpen = 1 := by
    simp [Rpen, largeUsed_append, largeUsed_cons, largeWeight, hzL, hT2, hE]
  by_cases hpen : mass (s k t) Fpen ≤ C k - P
  · obtain ⟨hv, inv, hperm, hg, hs, hj⟩ := actualSource_prefix_pair_truncation
      k t hk p Fpen Rpen hpositive hnlarge hexpand
      (hWpen ▸ hW) (hWpen ▸ hpunused) (hWpen ▸ hnunused) hpen (by omega)
    rw [← hWpen] at inv hperm hg hs hj
    refine ⟨Fpen ++ [p, n], Rpen, hv, hv.1, strip_of_legal hv, hv.2, hj,
      Or.inl ⟨inv, hperm, hs, Or.inl ⟨hpen, rfl, rfl, ?_⟩⟩⟩
    rw [hRpen] at hg
    change G k t (Fpen ++ [p, n]) + 2 = G k t W + 1 at hg
    change G k t (Fpen ++ [p, n]) + 1 = G k t W
    omega
  · by_cases hzcut : mass (s k t) Fz ≤ C k - P
    · obtain ⟨hv, inv, hperm, hg, hs, hj⟩ := actualSource_prefix_pair_truncation
        k t hk p Fz E hpositive hnlarge hexpand
        (hWz ▸ hW) (hWz ▸ hpunused) (hWz ▸ hnunused) hzcut (by omega)
      rw [← hWz] at inv hperm hg hs hj
      refine ⟨Fz ++ [p, n], E, hv, hv.1, strip_of_legal hv, hv.2, hj,
        Or.inl ⟨inv, hperm, hs, Or.inr ⟨lt_of_not_ge hpen, hzcut, rfl, rfl, ?_⟩⟩⟩
      simpa only [hE, Nat.add_zero] using hg
    · have hFresh (i : Fin k) (hi : i ∈ Extra) : i ∉ W := by
        dsimp only [Extra] at hi
        split_ifs at hi with he
        · simp at hi
        · have hi' : i = b := by simpa using hi
          subst i
          exact hhalf.resolve_right he
      have hbase : (W ++ Extra).Nodup := by
        have hn : Extra.Nodup := by dsimp only [Extra]; split_ifs <;> simp
        exact hW.1.append hn (List.disjoint_left.mpr (by intro i hi he; exact hFresh i he hi))
      have hExtra (i : Fin k) (hi : i ∈ Extra) : |s k t i| < Q k := by
        by_cases he : b ∈ E
        · simp only [Extra, ite_eq_left he, List.not_mem_nil] at hi
        · have hi' : i = b := by simpa only [Extra, ite_eq_right he, List.mem_singleton] using hi
          rw [hi']; exact hbval.2.2
      have hEF (i : Fin k) (hi : i ∈ Efinal) : |(s k t) i| < Q k := by
        have he : i ∈ E := by
          dsimp only [Efinal] at hi
          split_ifs at hi
          · exact List.mem_of_mem_erase hi
          · exact hi
        exact hsmall i (by simp [smallWord, he])
      have hFE : ([b] ++ Efinal).Perm (E ++ Extra) := by
        dsimp only [Efinal, Extra]
        split_ifs with he
        · simpa using (List.perm_cons_erase he).symm
        · exact List.perm_append_comm
      let δ := Y + mass (s k t) [b] - P
      let d1 := mass (s k t) (A ++ [x] ++ T0 ++ [y] ++ T1)
      let d2 := mass (s k t) (A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2)
      have hδ : δ = μ - P := by simp [δ, mass, hbval.1]; omega
      have hgate1 : (0 ≤ d1 + δ ∧ d1 + δ ≤ C k) ∧
          (0 ≤ d1 + (s k t) zpen + δ ∧ d1 + (s k t) zpen + δ ≤ C k) := by
        have hs := (strip_split (A ++ [x] ++ T0 ++ [y] ++ T1)
          ([zpen] ++ T2 ++ [z] ++ E)
          (by simpa [W, oldWord, x, List.append_assoc] using strip_of_legal hW)).2
        have hd : 0 ≤ d1 ∧ d1 ≤ C k := by
          simpa [d1, mass] using inStrip_prefix hs 0
        have ha : 0 ≤ d1 + s k t zpen ∧ d1 + s k t zpen ≤ C k := by
          simpa [d1, mass] using inStrip_prefix hs 1
        have hm : mass (s k t) Fpen = d1 + (s k t) zpen := by simp [Fpen, d1, mass]; ring
        change Q k ≤ -(s k t) zpen at hzpenlarge
        rw [hδ]; constructor <;> constructor <;> omega
      have hgate2 : (0 ≤ d2 + δ ∧ d2 + δ ≤ C k) ∧
          (0 ≤ d2 + (s k t) z + δ ∧ d2 + (s k t) z + δ ≤ C k) := by
        have hs := (strip_split (A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2)
          ([z] ++ E)
          (by simpa [W, oldWord, x, List.append_assoc] using strip_of_legal hW)).2
        have hd : 0 ≤ d2 ∧ d2 ≤ C k := by
          simpa [d2, mass] using inStrip_prefix hs 0
        have ha : 0 ≤ d2 + s k t z ∧ d2 + s k t z ≤ C k := by
          simpa [d2, mass] using inStrip_prefix hs 1
        have hm : mass (s k t) Fz = d2 + (s k t) z := by simp [Fz, Fpen, d2, mass]; ring
        change Q k ≤ -(s k t) z at hzlarge
        rw [hδ]; constructor <;> constructor <;> omega
      let e := mass (s k t) W + Y + mass (s k t) Extra - P
      have he : 0 ≤ e ∧ e < C k ∧ (b ∈ E → 0 < e) := by
        change C k - P < mass (s k t) W at hblocklo
        change mass (s k t) W < D at hblockhi
        have hYcap := centered_bounds hNp hNo ((2 : ℤ) ^ y.val * t)
        change -C k ≤ (s k t) y ∧ (s k t) y ≤ C k at hYcap
        have hmExtra : mass (s k t) Extra = if b ∈ E then 0 else -μ := by
          dsimp only [Extra]
          split_ifs <;> simp only [mass, List.map_nil, List.map_cons,
            List.sum_nil, List.sum_cons, add_zero, hbval.1]
        dsimp only [e]
        rw [hmExtra]
        split_ifs with hbE
        · exact ⟨by omega, by omega, by intro _; omega⟩
        · exact ⟨by omega, by omega, by intro he; exact (hbE he).elim⟩
      obtain ⟨L01, L2, LE, h01, h2, hLE, htail, hS, hv, hvn, hstrip, hpref,
          inv, hperm0, habs, hzp, hz, hretain, hg, hu, hsm, hH, hHs, hj,
          hend, he0, _, hcomp⟩ :=
        complete_small_shift k t hk p y zpen z A T0 T1 T2 E [b] Efinal Extra
          hpositive hnlarge hexpand hW hpunused hnunused hsmall hylarge
          (by intro i hi; have hi' : i = b := List.mem_singleton.mp hi; rw [hi']; exact hbval.2.2)
          hEF hExtra hFE hbase hgate1 hgate2 ⟨he.1, he.2.1.le⟩
      let L := L01 ++ [zpen] ++ L2 ++ [z] ++ LE
      let V := A ++ [p, n] ++ L
      let I := [p, n] ++ Extra
      have hperm : (V ++ [x, y]).Perm (W ++ I) := by
        apply hperm0.trans
        simpa only [List.append_assoc, I] using
          (List.perm_append_comm : (Extra ++ [p, n]).Perm ([p, n] ++ Extra)).append_left W
      have hIunused (i : Fin k) (hi : i ∈ I) : i ∉ W := by
        rcases List.mem_append.mp hi with hi | hi
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact hpunused
          · exact hnunused
        · exact hFresh i hi
      have hExtraR : Disjoint Extra.toFinset ({x, y} : Finset (Fin k)) := by
        apply Finset.disjoint_left.mpr
        intro i hi hiR
        have hs := hExtra i (List.mem_toFinset.mp hi)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiR
        rcases hiR with rfl | rfl
        · exact (not_lt_of_ge (show Q k ≤ |s k t x| from geo.xLarge)) hs
        · exact (not_lt_of_ge (le_trans hylarge (neg_le_abs _))) hs
      have hxys : ([x, y] : List (Fin k)).toFinset = {x, y} := by simp
      have hused : V.toFinset = (W.toFinset \ {x, y}) ∪ I.toFinset := by
        rw [inv.used, List.toFinset_append, hxys, Finset.union_sdiff_distrib,
          Finset.sdiff_eq_self_of_disjoint hExtraR]
        simp only [I, List.toFinset_append]
        ac_rfl
      have hunused : V.toFinsetᶜ = (W.toFinsetᶜ \ I.toFinset) ∪ {x, y} := by
        rw [inv.unused]
        ext i
        simp [I, W, n, x, Finset.mem_compl, and_assoc, and_left_comm, and_comm]
      have husedDis : Disjoint (W.toFinset \ {x, y}) I.toFinset := by
        apply Finset.disjoint_left.mpr
        intro i hiW hiI
        exact hIunused i (List.mem_toFinset.mp hiI) (List.mem_toFinset.mp (Finset.mem_sdiff.mp hiW).1)
      have hunusedDis : Disjoint (W.toFinsetᶜ \ I.toFinset) {x, y} := by
        apply Finset.disjoint_left.mpr
        intro i hi hiR
        have hiW : i ∈ W := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hiR
          rcases hiR with rfl | rfl <;> simp [W, oldWord, x]
        exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hi).1) (List.mem_toFinset.mpr hiW)
      have invExtra : Inventory k t (W ++ Extra) W [] Extra :=
        inventory_of_perm hk t (W ++ Extra) W [] Extra hbase (by simp)
          (by simp) (by intro i hi; simp [hi]) (by simp) (by simp)
      have hcount : U V + Extra.length = U W := by
        rw [hu]
        simpa only [List.length_nil, Nat.add_zero] using invExtra.countBalance.symm
      have hsmallEq : remainingSmall t V = remainingSmall t W \ Extra.toFinset := by
        rw [hsm]
        ext i
        simp [remainingSmall, W, and_assoc, and_comm]
      refine ⟨V, [x, y], hv, hvn, hstrip, hpref, hj, Or.inr
        ⟨lt_of_not_ge hpen, lt_of_not_ge hzcut, rfl, L01, L2, LE, h01, h2, hLE,
          rfl, htail, hS, inv, hperm, hused, husedDis, hunused, hunusedDis,
          habs, hzp, hz, hretain, hg, hcount, hsmallEq, hH, hHs, hend,
          he.1, he.2.1, he.2.2, hcomp⟩⟩

/-- An actual odd negative with an unused inverse parent supplies a literal
three-LARGE prefix improvement. The old y gate supplies the required valley. -/
theorem actualSource_odd_parent_uniform_prefix_exchange
    (k t : ℕ) (hk : 3 ≤ k) (p y : Fin k) (F R : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (F ++ [y] ++ R))
    (hpunused : p ∉ F ++ [y] ++ R)
    (hnunused : hit k 1 p ∉ F ++ [y] ++ R)
    (hbunused : (finRotate k).symm y ∉ F ++ [y] ++ R)
    (hyhigh : s k t p < -s k t y)
    (hyodd : (-s k t y) % 2 = 1)
    (hreturn : largeUsed k t R ≤ 2)
    (hthreshold : 6 * s k t p - N k ≤ 3 * (-s k t y)) :
    let n := hit k 1 p
    let b := (finRotate k).symm y
    let W := F ++ [y] ++ R
    let V := (F ++ [y]) ++ [p, n, b]
    2 * s k t b = N k + s k t y ∧ Large k t b ∧
    0 ≤ mass (s k t) (F ++ [y]) ∧
    mass (s k t) (F ++ [y]) ≤ C k + s k t y ∧
    Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
    (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧ mass (s k t) (V.take d) ≤ C k) ∧
    Inventory k t W V [p, n, b] R ∧
    (V ++ R).Perm (W ++ [p, n, b]) ∧
    G k t V + 3 = G k t W + largeUsed k t R ∧
    G k t V < G k t W ∧ J k t V < J k t W := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let b := (finRotate k).symm y
  let P := f p
  let D := |f n|
  let Y := -f y
  let L := f b
  let v := mass f (F ++ [y])
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hp : 0 < P := hpositive
  have hn : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hd : D < P := by simpa [f, n, D, abs_of_pos hpositive] using geo.strictOrder.1
  have hd0 : 0 ≤ D := abs_nonneg _
  have heq : D = N k - 2 * P := by
    simpa [f, n, D, P, abs_of_pos hpositive] using geo.firstEquation
  have hy : f y < 0 := by change P < Y at hyhigh; dsimp only [Y] at hyhigh; omega
  have hparent := negative_parent k t hk y hy
  have hb : 2 * L = N k - Y ∧ Q k ≤ L := by
    rcases hparent with he | ho
    · omega
    · exact ⟨ho.2.1, ho.2.2⟩
  have hyb := centered_bounds hNp hNo ((2 : ℤ) ^ y.val * t)
  change -C k ≤ f y ∧ f y ≤ C k at hyb
  have hLpos : 0 < L := by omega
  have hLP : L < P := by change P < Y at hyhigh; omega
  have hsold := strip_of_legal hW
  have hsF := (strip_split F ([y] ++ R) (by simpa only [List.append_assoc] using hsold)).2
  have hdeparture : 0 ≤ mass f F ∧ mass f F ≤ C k := by
    simpa [f, mass] using inStrip_prefix hsF 0
  have hsPrefix := (strip_split (F ++ [y]) R hsold).1
  have hv : 0 ≤ v ∧ v ≤ C k := by
    simpa [v, f, mass] using inStrip_prefix hsPrefix (F ++ [y]).length
  have hval : v = mass f F - Y := by simp [v, Y, mass]
  have hvalley : v ≤ C k - Y := by omega
  have hgate : 0 ≤ v + P ∧ v + P ≤ C k ∧
      0 ≤ v + P - D ∧ v + P - D ≤ C k ∧
      0 ≤ v + P - D + L ∧ v + P - D + L ≤ C k := by
    change 6 * P - N k ≤ 3 * Y at hthreshold
    change P < Y at hyhigh
    constructor <;> [omega; skip]
    constructor <;> [omega; skip]
    constructor <;> [omega; skip]
    constructor <;> [omega; skip]
    constructor <;> omega
  have hsI : InStrip f (C k) v [p, n, b] := by
    change 0 ≤ v ∧ v ≤ C k ∧ 0 ≤ v + f p ∧ v + f p ≤ C k ∧
      0 ≤ v + f p + f n ∧ v + f p + f n ≤ C k ∧
      0 ≤ v + f p + f n + f b ∧ v + f p + f n + f b ≤ C k
    rw [hn]
    exact ⟨hv.1, hv.2, hgate.1, hgate.2.1, hgate.2.2.1,
      hgate.2.2.2.1, hgate.2.2.2.2.1, hgate.2.2.2.2.2⟩
  have hsV := inStrip_append hsPrefix (show InStrip f (C k)
      (0 + ((F ++ [y]).map f).sum) [p, n, b] by simpa [v, mass] using hsI)
  have hI : ([p, n, b] : List (Fin k)).Nodup := by
    have hpn : p ≠ n := by intro he; have hh := congrArg f he; omega
    have hpb : p ≠ b := by intro he; have hh := congrArg f he; omega
    have hnb : n ≠ b := by intro he; have hh := congrArg f he; omega
    simp [hpn, hpb, hnb]
  have hIL (i : Fin k) (hi : i ∈ [p, n, b]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
    · change Q k ≤ |f b|
      rw [abs_of_pos hLpos]; exact hb.2
  have hIW (i : Fin k) (hi : i ∈ [p, n, b]) : i ∉ F ++ [y] ++ R := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpunused
    · exact hnunused
    · exact hbunused
  have hperm : (((F ++ [y]) ++ [p, n, b]) ++ R).Perm
      ((F ++ [y] ++ R) ++ [p, n, b]) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm : ([p, n, b] ++ R).Perm (R ++ [p, n, b])).append_left (F ++ [y])
  have inv := inventory_of_perm hk t (F ++ [y] ++ R) ((F ++ [y]) ++ [p, n, b])
    [p, n, b] R hW.1 hI hIW (by intro i hi; simp [hi]) hIL hperm
  have hcount : largeUsed k t [p, n, b] = 3 := by
    have hpL := hIL p (by simp)
    have hnL := hIL n (by simp)
    have hbL := hIL b (by simp)
    simp [largeUsed, mass, largeWeight, hpL, hnL, hbL]
  have hg := inv.largeBalance
  rw [hcount] at hg
  have hstrict : G k t ((F ++ [y]) ++ [p, n, b]) < G k t (F ++ [y] ++ R) := by omega
  refine ⟨by change 2 * L = N k + f y; dsimp only [Y] at hb; omega,
    hIL b (by simp), hv.1, ?_, legal_of_strip inv.nodup hsV, inv.nodup,
    hsV, ?_, inv, hperm, hg, hstrict, ?_⟩
  · change v ≤ C k + f y; dsimp only [Y] at hvalley; omega
  · intro d; simpa only [f, n, b, mass, zero_add] using inStrip_prefix hsV d
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hstrict)

#print axioms actualSource_threeNegative_even_half_arrival_free_exchange_full
#print axioms actualSource_odd_parent_uniform_prefix_exchange
#print axioms actualSource_threeNegative_firstNegative_shift_exchange_full
#print axioms actualSource_prefix_pair_truncation
#print axioms actualSource_threeNegative_firstNegative_arrival_free_exchange_full
end D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
