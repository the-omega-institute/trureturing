/- GID: D5/S3/Combinatorics/Circle/FreshPairRetainedTailExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FreshPairRetainedTailExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: A fresh physical pair strictly lowers energy while retaining every old SMALL and later negative label. -/
module
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
public import D5.S3.Combinatorics.Circle.LargeSkeletonOrdering

/-! # Fresh pair exchange retaining the complete old tail

One LARGE-skeleton ordering keeps all original SMALL occurrences and both later
negative LARGE labels. The original-quantifier Circle C3.1 remains open. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.FreshPairRetainedTailExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open scoped BigOperators

/-- Lift checked LARGE gates across one complete SMALL block. This only
decomposes physical list splits; it constructs no ordering or inventory. -/
private theorem retained_boundary_block {α : Type*} (f : α → ℤ)
    (threshold cap u : ℤ) (T : List α) (a : α) (R : List α)
    (hT : ∀ i ∈ T, |f i| < threshold)
    (hgate :
      (0 ≤ u + mass f T ∧ u + mass f T ≤ cap) ∧
      (0 ≤ u + mass f T + f a ∧ u + mass f T + f a ≤ cap))
    (hrest : ∀ (R0 : List α) (i : α) (R1 : List α),
      R = R0 ++ [i] ++ R1 → threshold ≤ |f i| →
      (0 ≤ u + mass f T + f a + mass f R0 ∧
        u + mass f T + f a + mass f R0 ≤ cap) ∧
      (0 ≤ u + mass f T + f a + mass f R0 + f i ∧
        u + mass f T + f a + mass f R0 + f i ≤ cap)) :
    ∀ (R0 : List α) (i : α) (R1 : List α),
      T ++ [a] ++ R = R0 ++ [i] ++ R1 → threshold ≤ |f i| →
      (0 ≤ u + mass f R0 ∧ u + mass f R0 ≤ cap) ∧
      (0 ≤ u + mass f R0 + f i ∧ u + mass f R0 + f i ≤ cap) := by
  revert hT hgate hrest
  induction T generalizing u with
  | nil =>
    intro hT hgate hrest R0 i R1 hsplit hi
    cases R0 with
    | nil =>
      have he : a = i := (List.cons.inj (by simpa using hsplit)).1
      subst i
      simpa [mass] using hgate
    | cons b R0 =>
      have he : a = b ∧ R = R0 ++ [i] ++ R1 := by
        simpa only [List.nil_append, List.cons_append, List.cons.injEq] using hsplit
      have hb := hrest R0 i R1 he.2 hi
      simpa [mass, he.1, add_assoc] using hb
  | cons b T ih =>
    intro hT hgate hrest R0 i R1 hsplit hi
    cases R0 with
    | nil =>
      have he : b = i := (List.cons.inj (by simpa using hsplit)).1
      subst i
      exact False.elim ((not_lt_of_ge hi) (hT b (by simp)))
    | cons c R0 =>
      have he : b = c ∧ T ++ [a] ++ R = R0 ++ [i] ++ R1 := by
        simpa only [List.cons_append, List.cons.injEq] using hsplit
      have hT' : ∀ i ∈ T, |f i| < threshold :=
        fun i hi => hT i (by simp [hi])
      have hgate' :
          (0 ≤ (u + f b) + mass f T ∧ (u + f b) + mass f T ≤ cap) ∧
          (0 ≤ (u + f b) + mass f T + f a ∧
            (u + f b) + mass f T + f a ≤ cap) := by
        simpa [mass, add_assoc] using hgate
      have hrest' : ∀ (R0 : List α) (i : α) (R1 : List α),
          R = R0 ++ [i] ++ R1 → threshold ≤ |f i| →
          (0 ≤ (u + f b) + mass f T + f a + mass f R0 ∧
            (u + f b) + mass f T + f a + mass f R0 ≤ cap) ∧
          (0 ≤ (u + f b) + mass f T + f a + mass f R0 + f i ∧
            (u + f b) + mass f T + f a + mass f R0 + f i ≤ cap) := by
        intro R0 i R1 hs hi
        simpa [mass, add_assoc] using hrest R0 i R1 hs hi
      have hb := ih (u + f b) hT' hgate' hrest' R0 i R1 he.2 hi
      simpa [mass, he.1, add_assoc] using hb

set_option maxHeartbeats 1600000 in
/-- Replace x,y by an arbitrary fresh LARGE pair q,n and retain every old
SMALL label and both later negatives. The positive label q need not be the
inverse parent of y. One skeleton-ordering call supplies all SMALL ordering. -/
theorem actualSource_fresh_pair_retained_tail_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hqLower : |s k t (hit k 1 p)| < s k t q)
    (hyhigh : s k t p < -s k t y)
    (hshift : 0 ≤ s k t (hit k 2 p) + s k t y - s k t q -
      s k t (hit k 1 p))
    (harrivalpen : C k - s k t p < mass (s k t)
      (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen]))
    (harrivalz : C k - s k t p < mass (s k t)
      (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z]))
    (hblocklo : C k - s k t p <
      mass (s k t) (oldWord p y zpen z A T0 T1 T2 E)) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let R := [n] ++ T0 ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
    let η := s k t x + s k t y - s k t q - s k t n
    ∃ Lstar : List (Fin k), Lstar.Perm R ∧
      Lstar.filter (fun i => decide (Q k ≤ |s k t i|)) = [n, zpen, z] ∧
      (let V := A ++ [q] ++ Lstar
       Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [q, n] [x, y] ∧
       (V ++ [x, y]).Perm (W ++ [q, n]) ∧
       (∀ i ∈ W, |s k t i| < Q k → i ∈ V) ∧
       G k t V = G k t W ∧ U V = U W ∧
       remainingSmall t V = remainingSmall t W ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs =
         H k t W + 3 ^ (s k t q).natAbs + 3 ^ (s k t n).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = mass (s k t) W - η ∧
       0 < mass (s k t) V ∧
       remainingMass (s k t) V = -(mass (s k t) W - η)) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let R := [n] ++ T0 ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
  let P := f p
  let D := |f n|
  let L := f q
  let r := f x
  let Y := -f y
  let η := f x + f y - f q - f n
  let a0 := mass f A
  let B1 := A ++ [x] ++ T0 ++ [y] ++ T1
  let B2 := B1 ++ [zpen] ++ T2
  let d1 := mass f B1
  let d2 := mass f B2
  let u := a0 + L
  let u1 := u + f n
  let u2 := u1 + mass f (T0 ++ T1) + f zpen
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change C k = 2 * Q k - 1 at hC
  have hP : 0 < P := hpositive
  have hD : Q k ≤ D := hnlarge
  have hLlo : D < L := hqLower
  have hY : P < Y := hyhigh
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxabs : f x = |f x| := by
    simpa [f, x, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : D < P := by
    simpa [f, n, D, P, abs_of_pos hpositive] using geo.strictOrder.1
  have hPr : P < r := by
    have hh : P < |f x| := by
      simpa only [P, f, x, abs_of_pos hpositive] using geo.strictOrder.2
    rw [← hxabs] at hh
    exact hh
  have hreq : r = 2 * P - D := by
    have hh1 : D = N k - 2 * P := by
      simpa only [D, P, f, n, abs_of_pos hpositive] using geo.firstEquation
    have hh2 : |f x| = 4 * P - N k := by
      simpa only [P, f, x, abs_of_pos hpositive] using geo.secondEquation
    rw [← hxabs] at hh2
    change f x = 2 * P - D
    omega
  have hrC : r ≤ C k := (centered_bounds hNp hNo _).2
  have hetaEq : η = r - Y - L + D := by
    dsimp only [η, r, Y, L]
    rw [hnval]
    ring
  have heta : 0 ≤ η := hshift
  have hLhi : L < P := by omega
  have hetaSmall : η < C k - P := by omega
  have hrY : Y < r := by omega
  have hLpos : 0 < L := by omega
  have hrpos : 0 < f x := by change 0 < r; omega
  have hyneg : f y < 0 := by dsimp only [Y] at hY; omega
  have hzpenneg : f zpen < 0 := by
    change Q k ≤ -f zpen at hzpenlarge
    omega
  have hzneg : f z < 0 := by
    change Q k ≤ -f z at hzlarge
    omega
  have hnL : Large k t n := geo.nLarge
  have hxL : Large k t x := geo.xLarge
  have hqL : Large k t q := by
    change Q k ≤ |f q|
    rw [abs_of_pos hLpos]
    omega
  have hyL : Large k t y := by
    change Q k ≤ |f y|
    rw [abs_of_neg hyneg]
    change Q k ≤ Y
    omega
  have hzpenL : Large k t zpen := le_trans hzpenlarge (neg_le_abs _)
  have hzL : Large k t z := le_trans hzlarge (neg_le_abs _)
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsAfterA⟩ := strip_split A
    ([x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
    (by simpa [W, oldWord, x, List.append_assoc] using hsW)
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa [a0, mass] using inStrip_prefix hsAfterA 0
  have hax : 0 ≤ a0 + r ∧ a0 + r ≤ C k := by
    simpa [a0, r, mass] using inStrip_prefix hsAfterA 1
  have hstart : 0 ≤ u ∧ u ≤ C k := by dsimp only [u]; omega
  have hnGate : (0 ≤ u ∧ u ≤ C k) ∧
      (0 ≤ u + f n ∧ u + f n ≤ C k) := by
    rw [hnval]
    dsimp only [u]
    constructor <;> constructor <;> omega
  have hs1 := (strip_split B1 ([zpen] ++ T2 ++ [z] ++ E)
    (by simpa [W, oldWord, B1, x, List.append_assoc] using hsW)).2
  have hd1 : 0 ≤ d1 ∧ d1 ≤ C k := by
    simpa [d1, mass] using inStrip_prefix hs1 0
  have ha1 : 0 ≤ d1 + f zpen ∧ d1 + f zpen ≤ C k := by
    simpa [d1, mass] using inStrip_prefix hs1 1
  have hs2 := (strip_split B2 ([z] ++ E)
    (by simpa [W, oldWord, B2, B1, x, List.append_assoc] using hsW)).2
  have hd2 : 0 ≤ d2 ∧ d2 ≤ C k := by
    simpa [d2, mass] using inStrip_prefix hs2 0
  have ha2 : 0 ≤ d2 + f z ∧ d2 + f z ≤ C k := by
    simpa [d2, mass] using inStrip_prefix hs2 1
  have hmargin1 : C k - P < d1 + f zpen := by
    simpa [d1, B1, x, f, P, mass, add_assoc] using harrivalpen
  have hmargin2 : C k - P < d2 + f z := by
    simpa [d2, B2, B1, x, f, P, mass, add_assoc] using harrivalz
  have hcut1 : u1 + mass f (T0 ++ T1) = d1 - η := by
    dsimp only [u1, u, a0, L, d1, B1, η]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hcut2 : u2 + mass f T2 = d2 - η := by
    dsimp only [u2, u1, u, a0, L, d2, B2, B1, η]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hgate1 :
      (0 ≤ u1 + mass f (T0 ++ T1) ∧ u1 + mass f (T0 ++ T1) ≤ C k) ∧
      (0 ≤ u1 + mass f (T0 ++ T1) + f zpen ∧
        u1 + mass f (T0 ++ T1) + f zpen ≤ C k) := by
    rw [hcut1]
    constructor <;> constructor <;> omega
  have hgate2 :
      (0 ≤ u2 + mass f T2 ∧ u2 + mass f T2 ≤ C k) ∧
      (0 ≤ u2 + mass f T2 + f z ∧ u2 + mass f T2 + f z ≤ C k) := by
    rw [hcut2]
    constructor <;> constructor <;> omega
  have hsmall01 : ∀ i ∈ T0 ++ T1, |f i| < Q k := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi <;>
      exact hsmall i (by simp [smallWord, hi])
  have hsmall2 : ∀ i ∈ T2, |f i| < Q k := by
    intro i hi; exact hsmall i (by simp [smallWord, hi])
  have hsmallE : ∀ i ∈ E, |f i| < Q k := by
    intro i hi; exact hsmall i (by simp [smallWord, hi])
  have hEboundary (v : ℤ) : ∀ (R0 : List (Fin k)) (i : Fin k)
      (R1 : List (Fin k)), E = R0 ++ [i] ++ R1 → Q k ≤ |f i| →
      (0 ≤ v + mass f R0 ∧ v + mass f R0 ≤ C k) ∧
      (0 ≤ v + mass f R0 + f i ∧ v + mass f R0 + f i ≤ C k) := by
    intro R0 i R1 hs hi
    have hiE : i ∈ E := by rw [hs]; simp
    exact False.elim ((not_lt_of_ge hi) (hsmallE i hiE))
  have hboundary2 := retained_boundary_block f (Q k) (C k) u2 T2 z E
    hsmall2 hgate2 (hEboundary (u2 + mass f T2 + f z))
  have hboundary1 := retained_boundary_block f (Q k) (C k) u1
    (T0 ++ T1) zpen (T2 ++ [z] ++ E) hsmall01 hgate1 hboundary2
  have hboundary0 := retained_boundary_block f (Q k) (C k) u [] n
    ((T0 ++ T1) ++ [zpen] ++ (T2 ++ [z] ++ E)) (by simp)
    (by simpa [mass] using hnGate)
    (by simpa [mass, u1, List.append_assoc] using hboundary1)
  have hboundary : ∀ (R0 : List (Fin k)) (i : Fin k) (R1 : List (Fin k)),
      R = R0 ++ [i] ++ R1 → Q k ≤ |f i| →
      (0 ≤ u + (R0.map f).sum ∧ u + (R0.map f).sum ≤ C k) ∧
      (0 ≤ u + (R0.map f).sum + f i ∧
        u + (R0.map f).sum + f i ≤ C k) := by
    simpa only [R, mass, List.nil_append, List.append_assoc] using hboundary0
  have hendEq : u + mass f R = mass f W - η := by
    dsimp only [u, a0, L, R, W, oldWord, η, x]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hWend : 0 ≤ mass f W ∧ mass f W ≤ C k := by
    simpa only [W, f, List.take_length] using hW.2 W.length
  have hendPos : 0 < mass f W - η := by
    change C k - P < mass f W at hblocklo
    omega
  have hend : 0 ≤ u + (R.map f).sum ∧ u + (R.map f).sum ≤ C k := by
    change 0 ≤ u + mass f R ∧ u + mass f R ≤ C k
    rw [hendEq]
    constructor <;> omega
  obtain ⟨Lstar, hLstar, hFilter, hsLstar⟩ :=
    LargeSkeletonOrdering.exists_order_preserving_large f (Q k) (C k)
      (by omega) (by omega) R u hstart hend hboundary
  let V := A ++ [q] ++ Lstar
  have hfilterSmall (T : List (Fin k)) (hT : ∀ i ∈ T, |f i| < Q k) :
      T.filter (fun i => decide (Q k ≤ |f i|)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi hd
    exact (not_le.mpr (hT i hi)) (of_decide_eq_true hd)
  have hsmall0 : ∀ i ∈ T0, |f i| < Q k :=
    fun i hi => hsmall01 i (by simp [hi])
  have hsmall1 : ∀ i ∈ T1, |f i| < Q k :=
    fun i hi => hsmall01 i (by simp [hi])
  have hRfilter : R.filter (fun i => decide (Q k ≤ |f i|)) = [n, zpen, z] := by
    have hn' : Q k ≤ |f n| := hnlarge
    have hzp' : Q k ≤ |f zpen| := hzpenL
    have hz' : Q k ≤ |f z| := hzL
    simp [R, List.filter_append, hn', hzp', hz', hfilterSmall T0 hsmall0,
      hfilterSmall T1 hsmall1, hfilterSmall T2 hsmall2, hfilterSmall E hsmallE]
  have hsQ : InStrip f (C k) a0 [q] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧
      0 ≤ a0 + f q ∧ a0 + f q ≤ C k
    exact ⟨ha0.1, ha0.2, hstart.1, hstart.2⟩
  have hsHead := inStrip_append hsA (show InStrip f (C k)
      (0 + (A.map f).sum) [q] by simpa [a0, mass] using hsQ)
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsHead
    simpa [u, a0, L, mass] using hsLstar
  have hqn : q ≠ n := by
    intro he
    have hh := congrArg f he
    rw [hnval] at hh
    change L = -D at hh
    omega
  have hI : ([q, n] : List (Fin k)).Nodup := by simp [hqn]
  have hIW (i : Fin k) (hi : i ∈ [q, n]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hqunused
    · exact hnunused
  have hIL (i : Fin k) (hi : i ∈ [q, n]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hqL
    · exact hnL
  have hRet (i : Fin k) (hi : i ∈ [x, y]) : i ∈ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [W, oldWord, x]
  have hperm : (V ++ [x, y]).Perm (W ++ [q, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hc := hLstar.count_eq i
    simp only [R, n, List.count_append, List.count_cons, List.count_nil] at hc
    simp only [V, W, oldWord, x, n, List.count_append, List.count_cons, List.count_nil]
    omega
  have inv := inventory_of_perm hk t W V [q, n] [x, y]
    hW.1 hI hIW hRet hIL hperm
  have hRetain (i : Fin k) (hi : i ∈ W) (hsi : |f i| < Q k) : i ∈ V := by
    have hix : i ≠ x := by intro he; subst i; exact (not_lt_of_ge hxL) hsi
    have hiy : i ≠ y := by intro he; subst i; exact (not_lt_of_ge hyL) hsi
    apply List.mem_toFinset.mp
    rw [inv.used]
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hi, by simp [hix, hiy]⟩
  have hGI : largeUsed k t [q, n] = 2 := by
    simp [largeUsed, mass, largeWeight, hqL, hnL]
  have hGR : largeUsed k t [x, y] = 2 := by
    simp [largeUsed, mass, largeWeight, hxL, hyL]
  have hG : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hGI, hGR] at hh
    omega
  have hU : U V = U W := by
    have hh := inv.countBalance
    simp only [List.length_cons, List.length_nil] at hh
    omega
  have hRetSmall : ([x, y] : List (Fin k)).toFinset.filter
      (fun i => ¬ Large k t i) = ∅ := by
    ext i
    have hxi : i = x → Large k t i := by rintro rfl; exact hxL
    have hyi : i = y → Large k t i := by rintro rfl; exact hyL
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, Finset.notMem_empty]
    tauto
  have hRemaining : remainingSmall t V = remainingSmall t W := by
    simpa only [hRetSmall, Finset.union_empty] using inv.smallPartition
  have hHI : H k t [q, n] =
      3 ^ (f q).natAbs + 3 ^ (f n).natAbs := by
    simp [H, mass, energyWeight, hqL, hnL, f, s]
  have hHR : H k t [x, y] =
      3 ^ (f x).natAbs + 3 ^ (f y).natAbs := by
    simp [H, mass, energyWeight, hxL, hyL, f, s]
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs =
      H k t W + 3 ^ (f q).natAbs + 3 ^ (f n).natAbs := by
    simpa only [hHI, hHR, Nat.add_assoc] using inv.energyBalance
  have hqx : (f q).natAbs < (f x).natAbs := by
    exact_mod_cast (show ((f q).natAbs : ℤ) < ((f x).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs,
        abs_of_pos (show 0 < f q from hLpos), abs_of_pos hrpos]
        using (show f q < f x by change L < r; omega))
  have hny : (f n).natAbs < (f y).natAbs := by
    exact_mod_cast (show ((f n).natAbs : ℤ) < ((f y).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs, abs_of_neg hyneg]
        using (show |f n| < -f y by change D < Y; omega))
  have hpow1 : (3 : ℕ) ^ (f q).natAbs < 3 ^ (f x).natAbs :=
    pow_lt_pow_right₀ (by decide : (1 : ℕ) < 3) hqx
  have hpow2 : (3 : ℕ) ^ (f n).natAbs < 3 ^ (f y).natAbs :=
    pow_lt_pow_right₀ (by decide : (1 : ℕ) < 3) hny
  have hHs : H k t V < H k t W := by omega
  have hJs : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHs)⟩
  have hmass : mass f V = mass f W - η := by
    have hm : mass f V + (f x + f y) = mass f W + (f q + f n) := by
      simpa only [mass, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] using inv.sourceBalance
    dsimp only [η]
    omega
  refine ⟨Lstar, hLstar, hFilter.trans hRfilter, legal_of_strip inv.nodup hsV,
    inv.nodup, hsV, ?_, inv, hperm, hRetain, hG, hU, hRemaining, hH,
    hHs, hJs, hmass, ?_, ?_⟩
  · intro j
    simpa only [f, mass, zero_add] using inStrip_prefix hsV j
  · rw [hmass]
    exact hendPos
  · rw [inv.complementSum, hmass]

end D5.S3.Combinatorics.Circle.FreshPairRetainedTailExchange
