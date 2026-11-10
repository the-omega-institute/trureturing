/- GID: D5/S3/Combinatorics/Circle/FirstNegativeShiftCore
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FirstNegativeShiftCore
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Complete SMALL-batch ordering with exact physical exchange balances. -/
module
public import D5.S3.Combinatorics.Circle.ThreeLargePacketExchange

/-! # Complete SMALL-batch first-negative exchange

A partition of the terminal SMALL batch and an additional SMALL list determines
three complete reordered batches. Translated retained gates and a closed final
endpoint give a physical exchange retaining every old SMALL occurrence. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open scoped BigOperators

set_option maxHeartbeats 1400000 in
-- Three complete-batch reorderings and the physical inventory share one proof budget.
/-- One physical three-batch engine. The added SMALL batch and final SMALL
batch partition the old terminal batch plus a Nodup SMALL extension. Only
translated retained gates and a closed final endpoint are needed. -/
theorem complete_small_shift
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E F Efinal Extra : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hF : ∀ i ∈ F, |s k t i| < Q k)
    (hEfinal : ∀ i ∈ Efinal, |s k t i| < Q k)
    (hExtra : ∀ i ∈ Extra, |s k t i| < Q k)
    (hFE : (F ++ Efinal).Perm (E ++ Extra))
    (hbase : (oldWord p y zpen z A T0 T1 T2 E ++ Extra).Nodup)
    (hgate1 :
      (0 ≤ mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1) +
          (-s k t y + mass (s k t) F - s k t p) ∧
       mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1) +
          (-s k t y + mass (s k t) F - s k t p) ≤ C k) ∧
      (0 ≤ mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1) + s k t zpen +
          (-s k t y + mass (s k t) F - s k t p) ∧
       mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1) + s k t zpen +
          (-s k t y + mass (s k t) F - s k t p) ≤ C k))
    (hgate2 :
      (0 ≤ mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2) +
          (-s k t y + mass (s k t) F - s k t p) ∧
       mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2) +
          (-s k t y + mass (s k t) F - s k t p) ≤ C k) ∧
      (0 ≤ mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2) + s k t z +
          (-s k t y + mass (s k t) F - s k t p) ∧
       mass (s k t) (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2) + s k t z +
          (-s k t y + mass (s k t) F - s k t p) ≤ C k))
    (hendpoint :
      0 ≤ mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) -
        s k t y + mass (s k t) Extra - s k t p ∧
      mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) -
        s k t y + mass (s k t) Extra - s k t p ≤ C k) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let Btail := T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E
    ∃ L01 L2 LE : List (Fin k),
      L01.Perm (T0 ++ T1 ++ F) ∧ L2.Perm T2 ∧ LE.Perm Efinal ∧
      (let L := L01 ++ [zpen] ++ L2 ++ [z] ++ LE
       let V := A ++ [p, n] ++ L
       let e0 := mass (s k t) W - s k t y + mass (s k t) Extra - s k t p
       (L ++ [y]).Perm (Btail ++ Extra) ∧ (∀ i ∈ S, i ∈ L) ∧
       Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧
         mass (s k t) (V.take d) ≤ C k) ∧
       Inventory k t (W ++ Extra) V [p, n] [x, y] ∧
       (V ++ [x, y]).Perm ((W ++ Extra) ++ [p, n]) ∧
       (∀ i ∈ [x, y], i ∉ V) ∧ zpen ∈ V ∧ z ∈ V ∧
       (∀ i ∈ W, |s k t i| < Q k → i ∈ V) ∧
       G k t V = G k t W ∧ U V = U (W ++ Extra) ∧
       remainingSmall t V = remainingSmall t (W ++ Extra) ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e0 ∧ 0 ≤ e0 ∧ e0 ≤ C k ∧
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
  let δ := Y + mass f F - P
  let a0 := mass f A
  let b := a0 + P - D
  let h := mass f W
  let e0 := h + Y + mass f Extra - P
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
  have hshift1 : (0 ≤ d1 + δ ∧ d1 + δ ≤ C k) ∧
      (0 ≤ a1 + δ ∧ a1 + δ ≤ C k) := hgate1
  have hshift2 : (0 ≤ d2 + δ ∧ d2 + δ ≤ C k) ∧
      (0 ≤ a2 + δ ∧ a2 + δ ≤ C k) := hgate2
  have he0 : 0 ≤ e0 ∧ e0 ≤ C k := hendpoint
  have hmFE : mass f F + mass f Efinal = mass f E + mass f Extra := by
    simpa [mass] using (hFE.map f).sum_eq
  -- The first identity joins across removed y: no shifted T0/T1 prefixes assumed.
  have hjoin01 : b + mass f (T0 ++ T1 ++ F) = d1 + δ := by
    dsimp only [b, a0, d1, B1, δ, Y]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [hxval]
    omega
  have hjoin2 : a1 + δ + mass f T2 = d2 + δ := by
    simp only [d2, B2, a1, d1, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hjoinE : a2 + δ + mass f Efinal = e0 := by
    dsimp only [a2, d2, B2, B1, e0, h, W, oldWord, x, δ, Y]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hmFE ⊢
    omega
  have hcompatible (B : List (Fin k))
      (hB : ∀ i ∈ B, |f i| < Q k) :
      ∀ i ∈ B, ∀ j ∈ B, 0 < f i → f j < 0 → f i - f j ≤ C k := by
    intro i hi j hj hip hjn
    have hi' := hB i hi
    have hj' := hB j hj
    rw [abs_of_pos hip] at hi'
    rw [abs_of_neg hjn] at hj'
    omega
  have hsmall01 (i : Fin k) (hi : i ∈ T0 ++ T1 ++ F) : |f i| < Q k := by
    rcases List.mem_append.mp hi with hi | hi
    · apply hsmall i
      simp only [smallWord, List.mem_append] at hi ⊢
      tauto
    · exact hF i hi
  have hsmall2 (i : Fin k) (hi : i ∈ T2) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  obtain ⟨L01, h01, hs01⟩ := exists_order_between f (T0 ++ T1 ++ F) (C k) b hbst
    (by
      change 0 ≤ b + mass f (T0 ++ T1 ++ F) ∧ b + mass f (T0 ++ T1 ++ F) ≤ C k
      rw [hjoin01]
      exact hshift1.1) (hcompatible _ hsmall01)
  obtain ⟨L2, h2, hs2⟩ := exists_order_between f T2 (C k) (a1 + δ) hshift1.2
    (by
      change 0 ≤ a1 + δ + mass f T2 ∧ a1 + δ + mass f T2 ≤ C k
      rw [hjoin2]
      exact hshift2.1) (hcompatible _ hsmall2)
  obtain ⟨LE, hE, hsE⟩ := exists_order_between f Efinal (C k) (a2 + δ) hshift2.2
    (by
      change 0 ≤ a2 + δ + mass f Efinal ∧ a2 + δ + mass f Efinal ≤ C k
      rw [hjoinE]
      exact he0)
    (hcompatible _ hEfinal)
  have hm01 : mass f L01 = mass f (T0 ++ T1 ++ F) := by
    simpa only [mass] using (h01.map f).sum_eq
  have hm2 : mass f L2 = mass f T2 := by
    simpa only [mass] using (h2.map f).sum_eq
  have h01end : b + mass f L01 = d1 + δ := by rw [hm01]; exact hjoin01
  have h2end : a1 + δ + mass f L2 = d2 + δ := by rw [hm2]; exact hjoin2
  let L := L01 ++ [zpen] ++ L2 ++ [z] ++ LE
  -- Assemble from the end, checking each literal retained negative gate.
  have hsZEnd : InStrip f (C k) (d2 + δ) ([z] ++ LE) := by
    change 0 ≤ d2 + δ ∧ d2 + δ ≤ C k ∧ InStrip f (C k) (d2 + δ + f z) LE
    have hzstart : d2 + δ + f z = a2 + δ := by dsimp only [a2]; ring
    rw [hzstart]
    exact ⟨hshift2.1.1, hshift2.1.2, hsE⟩
  have hs2ZEnd : InStrip f (C k) (a1 + δ) (L2 ++ [z] ++ LE) := by
    have hh := inStrip_append hs2 (show InStrip f (C k)
        ((a1 + δ) + (L2.map f).sum) ([z] ++ LE) from by
      change InStrip f (C k) (a1 + δ + mass f L2) ([z] ++ LE)
      rw [h2end]
      exact hsZEnd)
    simpa only [List.append_assoc] using hh
  have hsPenEnd : InStrip f (C k) (d1 + δ) ([zpen] ++ L2 ++ [z] ++ LE) := by
    change 0 ≤ d1 + δ ∧ d1 + δ ≤ C k ∧
      InStrip f (C k) (d1 + δ + f zpen) (L2 ++ [z] ++ LE)
    have hpstart : d1 + δ + f zpen = a1 + δ := by dsimp only [a1]; ring
    rw [hpstart]
    exact ⟨hshift1.1.1, hshift1.1.2, hs2ZEnd⟩
  have hsL : InStrip f (C k) b L := by
    have hh := inStrip_append hs01 (show InStrip f (C k)
        (b + (L01.map f).sum) ([zpen] ++ L2 ++ [z] ++ LE) from by
      change InStrip f (C k) (b + mass f L01) ([zpen] ++ L2 ++ [z] ++ LE)
      rw [h01end]
      exact hsPenEnd)
    simpa only [L, List.append_assoc] using hh
  have hsPN : InStrip f (C k) a0 [p, n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P + -D ∧ a0 + P + -D ≤ C k
    dsimp only [b] at hb
    omega
  have hsAPN : InStrip f (C k) 0 (A ++ [p, n]) :=
    inStrip_append hsA (by simpa [a0, mass] using hsPN)
  have hAPN : mass f (A ++ [p, n]) = b := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval]
    dsimp only [b, a0, P, mass]
    ring
  let V := A ++ [p, n] ++ L
  have hsV : InStrip f (C k) 0 V := by
    have hh := inStrip_append hsAPN (show InStrip f (C k)
        (0 + ((A ++ [p, n]).map f).sum) L from by
      change InStrip f (C k) (0 + mass f (A ++ [p, n])) L
      rw [zero_add, hAPN]
      exact hsL)
    simpa only [V, List.append_assoc] using hh
  have htail : (L ++ [y]).Perm (Btail ++ Extra) := by
    apply List.perm_iff_count.mpr
    intro i
    have h01c := h01.count_eq i
    have h2c := h2.count_eq i
    have hEc := hE.count_eq i
    have hFEc := hFE.count_eq i
    simp only [List.count_append] at h01c hFEc
    simp only [L, Btail, List.count_append, List.count_cons, List.count_nil]
    omega
  have hSretained (i : Fin k) (hi : i ∈ S) : i ∈ L := by
    have his : |f i| < Q k := hsmall i hi
    have hiy : i ≠ y := by
      intro he; subst i
      have hh := neg_le_abs (f y)
      omega
    have hiB : i ∈ Btail ++ Extra := by
      simp only [S, smallWord, List.mem_append] at hi
      simp only [Btail, List.mem_append, List.mem_cons, List.not_mem_nil]
      tauto
    have hm := htail.mem_iff.mpr hiB
    simpa [hiy] using hm
  have hWshape : W = A ++ [x] ++ Btail := by
    simp [W, oldWord, Btail, x, List.append_assoc]
  have hI : [p, n].Nodup := by
    have hpn : p ≠ n := by intro hh; have hv := congrArg f hh; omega
    simp [hpn]
  have hIW (i : Fin k) (hi : i ∈ [p, n]) : i ∉ W ++ Extra := by
    have hli : Large k t i := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact geo.pLarge
      · exact geo.nLarge
    have hie : i ∉ Extra := by
      intro he
      exact (not_lt_of_ge hli) (hExtra i he)
    simp only [List.mem_append, not_or]
    refine ⟨?_, hie⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hpunused
    · exact hnunused
  have hIL (i : Fin k) (hi : i ∈ [p, n]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
  have hperm : (V ++ [x, y]).Perm ((W ++ Extra) ++ [p, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hh := htail.count_eq i
    simp only [List.count_append, List.count_cons, List.count_nil] at hh
    simp only [V, hWshape, List.count_append, List.count_cons, List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ [x, y]) : i ∈ W ++ Extra := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [W, oldWord, x]
  have inv : Inventory k t (W ++ Extra) V [p, n] [x, y] :=
    inventory_of_perm hk t (W ++ Extra) V [p, n] [x, y] hbase hI hIW hRold hIL hperm
  have hWI : ((W ++ Extra) ++ [p, n]).Nodup := hbase.append hI (List.disjoint_left.mpr (by
    intro i hiW hiI
    exact hIW i hiI hiW))
  have hdisj := (List.nodup_append'.mp (hperm.nodup_iff.mpr hWI)).2.2
  have hRabs (i : Fin k) (hi : i ∈ [x, y]) : i ∉ V :=
    fun hiv => List.disjoint_left.mp hdisj hiv hi
  have hxLarge : Large k t x := geo.xLarge
  have hyLarge : Large k t y := by
    have hh := neg_le_abs (f y)
    unfold Large
    change Q k ≤ |f y|
    omega
  have hRlarge : largeUsed k t [x, y] = 2 := by
    simp [largeUsed, mass, largeWeight, hxLarge, hyLarge]
  have hIlarge : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  have hRenergy : H k t [x, y] = 3 ^ (f x).natAbs + 3 ^ (f y).natAbs := by
    simp [H, mass, energyWeight, hxLarge, hyLarge, f, s]
  have hIenergy : H k t [p, n] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    simp [H, mass, energyWeight, geo.pLarge, show Large k t n from geo.nLarge, f, s]
  have invExtra : Inventory k t (W ++ Extra) W [] Extra :=
    inventory_of_perm hk t (W ++ Extra) W [] Extra hbase (by simp)
      (by simp) (by intro i hi; simp [hi]) (by simp) (by simp)
  have hexWeights := small_weights t Extra hExtra
  have hgbase : G k t (W ++ Extra) = G k t W := by
    have hh := invExtra.largeBalance
    rw [hexWeights.1] at hh
    simpa only [largeUsed, mass, List.map_nil, List.sum_nil, Nat.add_zero] using hh.symm
  have hhbase : H k t (W ++ Extra) = H k t W := by
    have hh := invExtra.energyBalance
    rw [hexWeights.2] at hh
    simpa only [H, mass, List.map_nil, List.sum_nil, Nat.add_zero] using hh.symm
  have hG : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hRlarge, hIlarge, hgbase] at hh
    omega
  have hU : U V = U (W ++ Extra) := by
    have hh := inv.countBalance
    simp only [List.length_cons, List.length_nil] at hh
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    have hh := inv.energyBalance
    rw [hRenergy, hIenergy, hhbase] at hh
    omega
  have hHstrict : H k t V < H k t W := by
    have hh := geo.energy
    change 3 ^ (f p).natAbs + 3 ^ (f n).natAbs < 3 ^ (f x).natAbs at hh
    have hright := Nat.add_lt_add_left hh (H k t W)
    have hleft : (H k t V + 3 ^ (f y).natAbs) + 3 ^ (f x).natAbs <
        H k t W + 3 ^ (f x).natAbs := by
      calc
        _ = H k t W + (3 ^ (f p).natAbs + 3 ^ (f n).natAbs) := by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hH
        _ < _ := hright
    exact lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_of_add_lt_add_right hleft)
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHstrict)⟩
  have hRfilter : ([x, y] : List (Fin k)).toFinset.filter (fun i => ¬ Large k t i) = ∅ := by
    ext i
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl) hn
    · exact hn hxLarge
    · exact hn hyLarge
  have hSmall : remainingSmall t V = remainingSmall t (W ++ Extra) := by
    simpa only [hRfilter, Finset.union_empty] using inv.smallPartition
  have hretain (i : Fin k) (hi : i ∈ W) (his : |s k t i| < Q k) : i ∈ V := by
    have hiR : i ∉ [x, y] := by
      intro him
      simp only [List.mem_cons, List.not_mem_nil, or_false] at him
      rcases him with rfl | rfl
      · exact (not_lt_of_ge (show Q k ≤ |s k t x| from hxLarge)) his
      · exact (not_lt_of_ge (show Q k ≤ |s k t i| from hyLarge)) his
    apply List.mem_toFinset.mp
    rw [inv.used]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨List.mem_toFinset.mpr (List.mem_append_left Extra hi), by simpa using hiR⟩)
  have hEnd : mass f V = e0 := by
    have hh := inv.sourceBalance
    simp only [mass, List.map_append, List.sum_append] at hh
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero] at hh
    change mass f V + (f x + f y) = h + mass f Extra + (f p + f n) at hh
    rw [hxval, hnval] at hh
    change mass f V + (r + f y) = h + mass f Extra + (P + -D) at hh
    dsimp only [e0, Y]
    omega
  refine ⟨L01, L2, LE, h01, h2, hE, htail, hSretained,
    legal_of_strip inv.nodup hsV, inv.nodup, hsV, ?_, inv, hperm, hRabs,
    by simp, by simp, hretain, hG, hU, hSmall,
    hH, hHstrict, hJ, hEnd, he0.1, he0.2, ?_⟩
  · intro d
    simpa only [mass, f, zero_add] using inStrip_prefix hsV d
  · rw [inv.complementSum, hEnd]
    simp only [e0, h, Y, P, f, W, sub_eq_add_neg]


end D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
