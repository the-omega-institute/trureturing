/- GID: D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FirstNegativeShiftExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Actual last-two arrival bounds permit omission of the first negative LARGE. -/
module
public import D5.S3.Combinatorics.Circle.ThreeLargePacketExchange

/-! # Omitting the first negative LARGE using actual old arrivals

The two old arrival measurements below are premises, not consequences of Legal.
Complete SMALL batches are reordered across the omitted first negative occurrence.
The original-quantifier C3.1 availability problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open scoped BigOperators

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
  -- The first identity joins across removed y: no shifted T0/T1 prefixes assumed.
  have hjoin01 : b + mass f (T0 ++ T1) = d1 + δ := by
    dsimp only [b, a0, d1, B1, δ, Y]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [hxval]
    omega
  have hjoin2 : a1 + δ + mass f T2 = d2 + δ := by
    simp only [d2, B2, a1, d1, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hjoinE : a2 + δ + mass f E = e0 := by
    simp only [a2, d2, B2, B1, e0, h, W, oldWord, x, δ, Y]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hcompatible (B : List (Fin k))
      (hB : ∀ i ∈ B, |f i| < Q k) :
      ∀ i ∈ B, ∀ j ∈ B, 0 < f i → f j < 0 → f i - f j ≤ C k := by
    intro i hi j hj hip hjn
    have hi' := hB i hi
    have hj' := hB j hj
    rw [abs_of_pos hip] at hi'
    rw [abs_of_neg hjn] at hj'
    omega
  have hsmall01 (i : Fin k) (hi : i ∈ T0 ++ T1) : |f i| < Q k := by
    apply hsmall i
    simp only [smallWord, List.mem_append] at hi ⊢
    tauto
  have hsmall2 (i : Fin k) (hi : i ∈ T2) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have hsmallE (i : Fin k) (hi : i ∈ E) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  obtain ⟨L01, h01, hs01⟩ := exists_order_between f (T0 ++ T1) (C k) b hbst
    (by
      change 0 ≤ b + mass f (T0 ++ T1) ∧ b + mass f (T0 ++ T1) ≤ C k
      rw [hjoin01]
      exact hshift1.1) (hcompatible _ hsmall01)
  obtain ⟨L2, h2, hs2⟩ := exists_order_between f T2 (C k) (a1 + δ) hshift1.2
    (by
      change 0 ≤ a1 + δ + mass f T2 ∧ a1 + δ + mass f T2 ≤ C k
      rw [hjoin2]
      exact hshift2.1) (hcompatible _ hsmall2)
  obtain ⟨LE, hE, hsE⟩ := exists_order_between f E (C k) (a2 + δ) hshift2.2
    (by
      change 0 ≤ a2 + δ + mass f E ∧ a2 + δ + mass f E ≤ C k
      rw [hjoinE]
      exact ⟨le_of_lt he0.1, le_of_lt he0.2⟩)
    (hcompatible _ hsmallE)
  have hm01 : mass f L01 = mass f (T0 ++ T1) := by
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
  have htail : (L ++ [y]).Perm Btail := by
    apply List.perm_iff_count.mpr
    intro i
    have h01c := h01.count_eq i
    have h2c := h2.count_eq i
    have hEc := hE.count_eq i
    simp only [List.count_append] at h01c
    simp only [L, Btail, List.count_append, List.count_cons, List.count_nil]
    omega
  have hSretained (i : Fin k) (hi : i ∈ S) : i ∈ L := by
    have hm : i ∈ T0 ++ T1 ∨ i ∈ T2 ∨ i ∈ E := by
      simpa only [S, smallWord, List.mem_append, or_assoc] using hi
    rcases hm with hi | hi | hi
    · have hm := h01.mem_iff.mpr hi
      simp [L, hm]
    · have hm := h2.mem_iff.mpr hi
      simp [L, hm]
    · have hm := hE.mem_iff.mpr hi
      simp [L, hm]
  have hWshape : W = A ++ [x] ++ Btail := by
    simp [W, oldWord, Btail, x, List.append_assoc]
  have hI : [p, n].Nodup := by
    have hpn : p ≠ n := by intro hh; have hv := congrArg f hh; omega
    simp [hpn]
  have hIW (i : Fin k) (hi : i ∈ [p, n]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hpunused
    · exact hnunused
  have hIL (i : Fin k) (hi : i ∈ [p, n]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
  have hperm : (V ++ [x, y]).Perm (W ++ [p, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hh := htail.count_eq i
    simp only [List.count_append, List.count_cons, List.count_nil] at hh
    simp only [V, hWshape, List.count_append, List.count_cons, List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ [x, y]) : i ∈ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [W, oldWord, x]
  have inv : Inventory k t W V [p, n] [x, y] :=
    inventory_of_perm hk t W V [p, n] [x, y] hW.1 hI hIW hRold hIL hperm
  have hWI : (W ++ [p, n]).Nodup := hW.1.append hI (List.disjoint_left.mpr (by
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
  have hG : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hRlarge, hIlarge] at hh
    omega
  have hU : U V = U W := by
    have hh := inv.countBalance
    simp only [List.length_cons, List.length_nil] at hh
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    have hh := inv.energyBalance
    rw [hRenergy, hIenergy] at hh
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
  have hSmall : remainingSmall t V = remainingSmall t W := by
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
      ⟨List.mem_toFinset.mpr hi, by simpa using hiR⟩)
  have hEnd : mass f V = e0 := by
    have hh := inv.sourceBalance
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero] at hh
    change mass f V + (f x + f y) = h + (f p + f n) at hh
    rw [hxval, hnval] at hh
    change mass f V + (r + f y) = h + (P + -D) at hh
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

#print axioms actualSource_threeNegative_firstNegative_shift_exchange_full
end D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
