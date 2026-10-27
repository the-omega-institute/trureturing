/- Transient anonymous application; SOURCE ONLY until this exact source
   passes canonical make lean. No parity or inverse-parent premise is used. -/
import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.Circle
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange

set_option maxHeartbeats 2200000 in
example (k t : ℕ) (hk : 3 ≤ k) (p y zpen z b : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyhigh : s k t p < -s k t y)
    (hbsmall : |s k t b| < Q k)
    (hbandlo : -s k t y - s k t p ≤ -s k t b)
    (hbandhi : -s k t b ≤ (-s k t y - s k t p) + (C k - s k t p))
    (hmin : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V) :
    b ∈ A ++ T0 ++ T1 ++ T2 := by
  classical
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let P := f p
  let D := |f n|
  let Y := -f y
  let B := C k - P
  let δ := Y - P
  let μ := -f b
  let σ := δ - μ
  let B1 := A ++ [x] ++ T0 ++ [y] ++ T1
  let B2 := B1 ++ [zpen] ++ T2
  let Fpen := B1 ++ [zpen]
  let Rpen := T2 ++ [z] ++ E
  let Fz := B2 ++ [z]
  let d1 := mass f B1
  let d2 := mass f B2
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change P < Y at hyhigh
  change ∀ V : List (Fin k), Legal k t V → J k t W ≤ J k t V at hmin
  have hδpos : 0 < δ := by dsimp only [δ]; omega
  have hband : δ ≤ μ ∧ μ ≤ δ + B := ⟨hbandlo, hbandhi⟩
  have hσ : -B ≤ σ ∧ σ ≤ 0 := by dsimp only [σ]; omega
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, _, _, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  have hD : Q k ≤ D := hnlarge
  have hDP : D < P := by
    simpa only [D, P, f, n, abs_of_pos hpositive] using geo.strictOrder.1
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxL : Large k t x := geo.xLarge
  have hyL : Large k t y := by
    have hh := neg_le_abs (f y)
    change Q k ≤ |f y|
    dsimp only [Y] at hyhigh
    omega
  have hylarge : Q k ≤ -s k t y := by
    change Q k ≤ -f y
    omega
  have hzpenL : Large k t zpen := le_trans hzpenlarge (neg_le_abs _)
  have hzL : Large k t z := le_trans hzlarge (neg_le_abs _)
  have hycap : Y ≤ C k := by
    have hh := (centered_bounds hNp hNo ((2 : ℤ) ^ y.val * t)).1
    change -C k ≤ f y at hh
    dsimp only [Y]
    omega
  have hlow : B < mass f W := by
    by_contra hcut
    obtain ⟨hv, _, _, _, _, hj⟩ :=
      FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
        k t hk p W [] hpositive hnlarge hexpand
        (by simpa only [List.append_nil] using hW)
        (by simpa only [List.append_nil] using hpunused)
        (by simpa only [List.append_nil] using hnunused)
        (by dsimp only [B, P] at *; omega) (by simp [largeUsed, mass])
    have hj' : J k t (W ++ [p, n]) < J k t W := by
      simpa only [List.append_nil, n] using hj
    exact (not_lt_of_ge (hmin _ hv)) hj'
  have hWend : 0 ≤ mass f W ∧ mass f W ≤ C k := by
    simpa only [List.take_length] using hW.2 W.length
  have hhigh : mass f W < D := by
    by_contra hfit
    let V := W ++ [n]
    have inv : Inventory k t W V [n] [] :=
      inventory_of_perm hk t W V [n] [] hW.1 (by simp)
        (by intro i hi; obtain rfl := List.mem_singleton.mp hi; exact hnunused)
        (by simp)
        (by intro i hi; obtain rfl := List.mem_singleton.mp hi; exact geo.nLarge)
        (by simp [V])
    have hsN : InStrip f (C k) (mass f W) [n] := by
      change 0 ≤ mass f W ∧ mass f W ≤ C k ∧
        0 ≤ mass f W + f n ∧ mass f W + f n ≤ C k
      rw [hnval]
      exact ⟨hWend.1, hWend.2, by omega, by omega⟩
    have hsV : InStrip f (C k) 0 V :=
      inStrip_append (strip_of_legal hW) (by simpa only [mass, zero_add] using hsN)
    have hv : Legal k t V := legal_of_strip inv.nodup hsV
    have hg : G k t V < G k t W := by
      have hh := inv.largeBalance
      have hnL : Large k t n := geo.nLarge
      simp [largeUsed, mass, largeWeight, hnL] at hh
      omega
    have hj : J k t V < J k t W :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hg)
    exact (not_lt_of_ge (hmin _ hv)) hj
  have hs2 : largeUsed k t T2 = 0 := (small_weights t T2 (by
    intro i hi; exact hsmall i (by simp [smallWord, hi]))).1
  have hsE : largeUsed k t E = 0 := (small_weights t E (by
    intro i hi; exact hsmall i (by simp [smallWord, hi]))).1
  have hRpen : largeUsed k t Rpen = 1 := by
    simp [Rpen, largeUsed_append, largeUsed_cons, largeWeight, hzL, hs2, hsE]
  have hWpen : W = Fpen ++ Rpen := by
    simp only [W, oldWord, Fpen, B1, Rpen, x, List.append_assoc]
  have hWz : W = Fz ++ E := by
    simp only [W, oldWord, Fz, B2, B1, x, List.append_assoc]
  have hpen : B < d1 + f zpen := by
    have hh : B < mass f Fpen := by
      by_contra hcut
      obtain ⟨hv, _, _, _, _, hj⟩ :=
        FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
          k t hk p Fpen Rpen hpositive hnlarge hexpand
          (hWpen ▸ hW) (hWpen ▸ hpunused) (hWpen ▸ hnunused)
          (by dsimp only [B, P] at *; omega) (by omega)
      rw [← hWpen] at hj
      exact (not_lt_of_ge (hmin _ hv)) hj
    simpa [Fpen, d1, mass] using hh
  have hzcut : B < d2 + f z := by
    have hh : B < mass f Fz := by
      by_contra hcut
      obtain ⟨hv, _, _, _, _, hj⟩ :=
        FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
          k t hk p Fz E hpositive hnlarge hexpand
          (hWz ▸ hW) (hWz ▸ hpunused) (hWz ▸ hnunused)
          (by dsimp only [B, P] at *; omega) (by omega)
      rw [← hWz] at hj
      exact (not_lt_of_ge (hmin _ hv)) hj
    simpa [Fz, d2, mass] using hh
  have hsW := strip_of_legal hW
  have hs1 := (strip_split B1 ([zpen] ++ T2 ++ [z] ++ E)
    (by simpa [W, oldWord, B1, x, List.append_assoc] using hsW)).2
  have hd1 : 0 ≤ d1 ∧ d1 ≤ C k := by
    simpa [d1, mass] using inStrip_prefix hs1 0
  have ha1 : 0 ≤ d1 + f zpen ∧ d1 + f zpen ≤ C k := by
    simpa [d1, mass] using inStrip_prefix hs1 1
  have hs2old := (strip_split B2 ([z] ++ E)
    (by simpa [W, oldWord, B2, B1, x, List.append_assoc] using hsW)).2
  have hd2 : 0 ≤ d2 ∧ d2 ≤ C k := by
    simpa [d2, mass] using inStrip_prefix hs2old 0
  have ha2 : 0 ≤ d2 + f z ∧ d2 + f z ≤ C k := by
    simpa [d2, mass] using inStrip_prefix hs2old 1
  by_contra hbEarly
  have hbfresh (hbE : b ∉ E) : b ∉ W := by
    intro hbW
    simp only [W, oldWord, x, List.mem_append, List.mem_singleton, or_assoc] at hbW
    rcases hbW with hbA | hbx | hb0 | hby | hb1 | hbpen | hb2 | hbz | hbE'
    · exact hbEarly (by simp [hbA])
    · have hh := congrArg f hbx
      subst b
      exact (not_lt_of_ge hxL) hbsmall
    · exact hbEarly (by simp [hb0])
    · subst b; exact (not_lt_of_ge hyL) hbsmall
    · exact hbEarly (by simp [hb1])
    · subst b; exact (not_lt_of_ge hzpenL) hbsmall
    · exact hbEarly (by simp [hb2])
    · subst b; exact (not_lt_of_ge hzL) hbsmall
    · exact hbE hbE'
  let Extra : List (Fin k) := if b ∈ E then [] else [b]
  let Efinal := if b ∈ E then E.erase b else E
  have hExtraFresh (i : Fin k) (hi : i ∈ Extra) : i ∉ W := by
    dsimp only [Extra] at hi
    split_ifs at hi with hbE
    · simp at hi
    · have he : i = b := List.mem_singleton.mp hi
      subst i
      exact hbfresh hbE
  have hbase : (W ++ Extra).Nodup := hW.1.append
    (by dsimp only [Extra]; split_ifs <;> simp)
    (List.disjoint_left.mpr (by
      intro i hiW hiExtra
      exact hExtraFresh i hiExtra hiW))
  have hF (i : Fin k) (hi : i ∈ [b]) : |f i| < Q k := by
    obtain rfl := List.mem_singleton.mp hi
    exact hbsmall
  have hEfinal (i : Fin k) (hi : i ∈ Efinal) : |f i| < Q k := by
    have hiE : i ∈ E := by
      dsimp only [Efinal] at hi
      split_ifs at hi
      · exact List.mem_of_mem_erase hi
      · exact hi
    exact hsmall i (by simp [smallWord, hiE])
  have hExtra (i : Fin k) (hi : i ∈ Extra) : |f i| < Q k := by
    dsimp only [Extra] at hi
    split_ifs at hi
    · simp at hi
    · obtain rfl := List.mem_singleton.mp hi
      exact hbsmall
  have hFE : ([b] ++ Efinal).Perm (E ++ Extra) := by
    dsimp only [Efinal, Extra]
    split_ifs with hbE
    · simpa using (List.perm_cons_erase hbE).symm
    · exact List.perm_append_comm
  have hσeq : -s k t y + mass (s k t) [b] - s k t p = σ := by
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    dsimp only [σ, δ, Y, P, μ, f]
    ring
  have hgate1 :
      (0 ≤ mass (s k t) B1 + σ ∧ mass (s k t) B1 + σ ≤ C k) ∧
      (0 ≤ mass (s k t) B1 + s k t zpen + σ ∧
        mass (s k t) B1 + s k t zpen + σ ≤ C k) := by
    change Q k ≤ -f zpen at hzpenlarge
    change (0 ≤ d1 + σ ∧ d1 + σ ≤ C k) ∧
      (0 ≤ d1 + f zpen + σ ∧ d1 + f zpen + σ ≤ C k)
    constructor <;> constructor <;> omega
  have hgate2 :
      (0 ≤ mass (s k t) B2 + σ ∧ mass (s k t) B2 + σ ≤ C k) ∧
      (0 ≤ mass (s k t) B2 + s k t z + σ ∧
        mass (s k t) B2 + s k t z + σ ≤ C k) := by
    change Q k ≤ -f z at hzlarge
    change (0 ≤ d2 + σ ∧ d2 + σ ≤ C k) ∧
      (0 ≤ d2 + f z + σ ∧ d2 + f z + σ ≤ C k)
    constructor <;> constructor <;> omega
  have hend : 0 ≤ mass (s k t) W - s k t y + mass (s k t) Extra - s k t p ∧
      mass (s k t) W - s k t y + mass (s k t) Extra - s k t p ≤ C k := by
    by_cases hbE : b ∈ E
    · have hm : mass f Extra = 0 := by simp [Extra, hbE, mass]
      change 0 ≤ mass f W - f y + mass f Extra - P ∧
        mass f W - f y + mass f Extra - P ≤ C k
      rw [hm]
      dsimp only [Y, δ] at *
      constructor <;> omega
    · have hm : mass f Extra = f b := by simp [Extra, hbE, mass]
      change 0 ≤ mass f W - f y + mass f Extra - P ∧
        mass f W - f y + mass f Extra - P ≤ C k
      rw [hm]
      dsimp only [σ, δ, Y, μ] at *
      constructor <;> omega
  obtain ⟨L01, L2, LE, h01, h2, hLE, htail, hS, hv, hvn, hstrip, hpref,
      inv, hperm, habs, hzp, hz, hretain, hg, hu, hsm, hH, hHs, hj,
      hendV, he0, heC, hcomp⟩ :=
    FirstNegativeShiftExchange.complete_small_shift
      k t hk p y zpen z A T0 T1 T2 E [b] Efinal Extra
      hpositive hnlarge hexpand hW hpunused hnunused hsmall hylarge
      hF hEfinal hExtra hFE hbase
      (by simpa only [B1, x, hσeq] using hgate1)
      (by simpa only [B2, B1, x, hσeq] using hgate2)
      (by simpa only [W] using hend)
  exact (not_lt_of_ge (hmin _ hv)) hj
