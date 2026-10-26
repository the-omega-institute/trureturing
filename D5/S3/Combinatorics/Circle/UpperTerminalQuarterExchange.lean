/- GID: D5/S3/Combinatorics/Circle/UpperTerminalQuarterExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/UpperTerminalQuarterExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Actual early-or-terminal quarter reserve selects a nonempty SMALL return and constructs an arrival-free full physical strict-J exchange. -/
module
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
public import D5.S3.Combinatorics.Circle.SignedShortLargeExchange

/-! The actual inverse quarter-parent in T0, T1 or E supplies a signed reserve. Returning
an actual SMALL batch before the retained negative gates gives a nonpositive
shift. No placement or availability assumption is made on the half-parent.
The theorem concerns this source region; full Circle C3.1 remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.UpperTerminalQuarterExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open FirstNegativeShiftExchange SignedShortLargeExchange
open scoped BigOperators

set_option maxHeartbeats 1600000 in
/-- A full native upper-quarter tail competitor, with two literal low-arrival
cuts or an actual nonempty SMALL return. A is arbitrary, including signed LARGE.
The conclusion accounts for all physical occurrences, original-zero natural
prefixes and every Inventory field. The signed selector's public contract supplies no support refinement
beyond a physical subpermutation of the actual batch S defined below. -/
theorem actualSource_threeNegative_upper_quarter_tail_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * s k t p)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hblocklo : C k - s k t p <
      mass (s k t) (oldWord p y zpen z A T0 T1 T2 E))
    (hblockhi : mass (s k t) (oldWord p y zpen z A T0 T1 T2 E) <
      |s k t (hit k 1 p)|)
    (hyupper : s k t p < -s k t y)
    (hyfour : (-s k t y) % 4 = 0)
    (hquarterupper : 4 * s k t p < 3 * (-s k t y))
    (hcTail : (finRotate k).symm ((finRotate k).symm y) ∈ T0 ++ T1 ++ E) :
    let n := hit k 1 p
    let x := hit k 2 p
    let c := (finRotate k).symm ((finRotate k).symm y)
    let W := oldWord p y zpen z A T0 T1 T2 E
    let P := s k t p
    let D := |s k t n|
    let Y := -s k t y
    let θ := Y / 4
    let B := C k - P
    let h := mass (s k t) W
    let σ := if c ∈ E then θ else 0
    let low := Y - P - σ
    let S := if c ∈ E then T0 ++ T1 ++ [c] else T0 ++ T1
    let E0 := if c ∈ E then E.erase c else E
    let Fpen := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
    let Rpen := T2 ++ [z] ++ E
    let Fz := Fpen ++ T2 ++ [z]
    ∃ V I Ret : List (Fin k), I = [p, n] ∧
      Legal k t V ∧ V.Nodup ∧ InStrip (s k t) (C k) 0 V ∧
      (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
        mass (s k t) (V.take j) ≤ C k) ∧
      Inventory k t W V I Ret ∧
      (V ++ Ret).Perm (W ++ I) ∧ J k t V < J k t W ∧
      ((mass (s k t) Fpen ≤ B ∧ V = Fpen ++ [p, n] ∧
        Ret = Rpen ∧ largeUsed k t Ret = 1 ∧
        G k t V + 1 = G k t W ∧ G k t V < G k t W) ∨
       (B < mass (s k t) Fpen ∧ mass (s k t) Fz ≤ B ∧
        V = Fz ++ [p, n] ∧ Ret = E ∧ largeUsed k t Ret = 0 ∧
        G k t V + 2 = G k t W ∧ G k t V < G k t W) ∨
       (B < mass (s k t) Fpen ∧ B < mass (s k t) Fz ∧
        ∃ R K L01 L2 LE : List (Fin k),
          (K ++ R).Perm S ∧ R.Subperm S ∧
          (∀ i ∈ R, |s k t i| < Q k) ∧
          0 < low ∧ low ≤ mass (s k t) R ∧ mass (s k t) R ≤ low + B ∧
          R ≠ [] ∧ 1 ≤ R.length ∧
          s k t c = -θ ∧ 0 < θ ∧ θ ≤ B ∧ P - Q k - 1 ≤ θ ∧
          L01.Perm K ∧ L2.Perm T2 ∧ LE.Perm E0 ∧
          V = A ++ [p, n] ++ L01 ++ [zpen] ++ L2 ++ [z] ++ LE ∧
          Ret = [x, y] ++ R ∧
          (∀ i ∈ Ret, i ∉ V) ∧ zpen ∈ V ∧ z ∈ V ∧
          (∀ i ∈ W, |s k t i| < Q k → i ∉ R → i ∈ V) ∧
          G k t V = G k t W ∧ U V = U W + R.length ∧
          remainingSmall t V = remainingSmall t W ∪ R.toFinset ∧
          Disjoint (remainingSmall t W) R.toFinset ∧
          H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs =
            H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
          H k t V < H k t W ∧
          (let η := low - mass (s k t) R;
           let e := h + Y - P - mass (s k t) R;
           -B ≤ η ∧ η ≤ 0 ∧ e = h + σ + η ∧
           mass (s k t) V = e ∧ 0 < e ∧ e < C k ∧
           remainingMass (s k t) V = -e))) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let b := (finRotate k).symm y
  let c := (finRotate k).symm b
  let W := oldWord p y zpen z A T0 T1 T2 E
  let P := f p
  let D := |f n|
  let Y := -f y
  let θ := Y / 4
  let B := C k - P
  let h := mass f W
  let σ := if c ∈ E then θ else 0
  let low := Y - P - σ
  let S := if c ∈ E then T0 ++ T1 ++ [c] else T0 ++ T1
  let E0 := if c ∈ E then E.erase c else E
  let Fpen := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
  let Rpen := T2 ++ [z] ++ E
  let Fz := Fpen ++ T2 ++ [z]
  have hex : N k < 3 * |s k t p| := by
    simpa only [abs_of_pos hpositive] using hexpand
  have hWpen : W = Fpen ++ Rpen := by
    simp only [W, oldWord, Fpen, Rpen, x, List.append_assoc]
  have hWz : W = Fz ++ E := by
    simp only [W, oldWord, Fz, Fpen, x, List.append_assoc]
  have hEsmall (i : Fin k) (hi : i ∈ E) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have h2small (i : Fin k) (hi : i ∈ T2) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have hEweight := small_weights t E hEsmall
  have h2weight := small_weights t T2 h2small
  have hzLarge : Large k t z := by
    change Q k ≤ |f z|
    exact le_trans (show Q k ≤ -f z from hzlarge) (neg_le_abs (f z))
  have hRpen : largeUsed k t Rpen = 1 := by
    simp [Rpen, largeUsed_append, largeUsed_cons, largeWeight,
      hzLarge, h2weight.1, hEweight.1]
  by_cases hpen : mass f Fpen ≤ B
  · obtain ⟨hv, inv, hp, hb, hg, hj⟩ := actualSource_prefix_pair_truncation
      k t hk p Fpen Rpen hpositive hnlarge hex
      (hWpen ▸ hW) (hWpen ▸ hpunused) (hWpen ▸ hnunused) hpen (by omega)
    rw [← hWpen] at inv hp hb hg hj
    refine ⟨Fpen ++ [p, n], [p, n], Rpen, rfl, hv, hv.1,
      strip_of_legal hv, hv.2, inv, hp, hj,
      Or.inl ⟨hpen, rfl, rfl, hRpen, ?_, hg⟩⟩
    rw [hRpen] at hb
    change G k t (Fpen ++ [p, n]) + 2 = G k t W + 1 at hb
    change G k t (Fpen ++ [p, n]) + 1 = G k t W
    omega
  by_cases hzcut : mass f Fz ≤ B
  · obtain ⟨hv, inv, hp, hb, hg, hj⟩ := actualSource_prefix_pair_truncation
      k t hk p Fz E hpositive hnlarge hex
      (hWz ▸ hW) (hWz ▸ hpunused) (hWz ▸ hnunused) hzcut (by omega)
    rw [← hWz] at inv hp hb hg hj
    refine ⟨Fz ++ [p, n], [p, n], E, rfl, hv, hv.1,
      strip_of_legal hv, hv.2, inv, hp, hj,
      Or.inr (Or.inl ⟨lt_of_not_ge hpen, hzcut, rfl, rfl, hEweight.1, ?_, hg⟩)⟩
    simpa only [hEweight.1, Nat.add_zero] using hb
  -- Only this branch selects a SMALL return; neither old arrival is assumed.
  have hpenrich : B < mass f Fpen := lt_of_not_ge hpen
  have hzrich : B < mass f Fz := lt_of_not_ge hzcut
  have geo := native_geometry hk t p hnlarge hex
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  let r := |f x|
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
  have hnative : 2 * P + D = N k ∧ r = 2 * P - D := by
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
    abs_le.mpr (centered_bounds hNp hNo _)
  have hPcap : P ≤ C k := by simpa only [hpabs] using hbound p
  have hYcap : Y ≤ C k := by have hh := neg_le_abs (f y); have := hbound y; omega
  have hY : Q k ≤ Y := hylarge
  have hYθ : Y = 4 * θ := by dsimp only [θ, Y, f]; omega
  have hθ : 0 < θ := by omega
  have hquarter : P < 3 * θ := by
    have hh : 4 * P < 3 * Y := hquarterupper
    omega
  have hσcases : σ = 0 ∨ σ = θ := by
    by_cases hc : c ∈ E
    · exact Or.inr (if_pos hc)
    · exact Or.inl (if_neg hc)
  have hσ : 0 ≤ σ ∧ σ ≤ θ := by rcases hσcases with hh | hh <;> omega
  have hlow : 0 < low := by
    have hYP : P < Y := hyupper
    dsimp only [low]
    rcases hσcases with hh | hh <;> omega
  have hB : 0 ≤ B := by dsimp only [B]; omega
  have hθB : θ ≤ B := by dsimp only [B]; omega
  have hθlead : P - Q k - 1 ≤ θ := by omega
  have hDθ : D + θ < C k := by omega
  -- Consume the exact public inverse-source lemma, twice; no odd classifier.
  have hbdata : Y % 2 = 0 ∧ 2 * f b = -Y ∧ |f b| < Q k ∧ f b < 0 := by
    have hb0 := negative_parent k t hk y (by change f y < 0; omega)
    change (Y % 2 = 0 ∧ 2 * f b = -Y ∧ |f b| < Q k ∧ f b < 0) ∨
      (Y % 2 = 1 ∧ 2 * f b = N k - Y ∧ Q k ≤ f b) at hb0
    rcases hb0 with hb0 | hb0
    · exact hb0
    · change (-f y) % 4 = 0 at hyfour
      omega
  have hbeven : (-f b) % 2 = 0 := by omega
  have hcval : f c = -θ := by
    have hc0 := negative_parent k t hk b hbdata.2.2.2
    change ((-f b) % 2 = 0 ∧ 2 * f c = -(-f b) ∧
      |f c| < Q k ∧ f c < 0) ∨
      ((-f b) % 2 = 1 ∧ 2 * f c = N k - (-f b) ∧ Q k ≤ f c) at hc0
    rcases hc0 with hc0 | hc0 <;> omega
  have hE0small (i : Fin k) (hi : i ∈ E0) : |f i| < Q k := by
    by_cases hc : c ∈ E
    · have hi' : i ∈ E.erase c := by simpa only [E0, if_pos hc] using hi
      exact hEsmall i (List.mem_of_mem_erase hi')
    · exact hEsmall i (by simpa only [E0, if_neg hc] using hi)
  -- Partition actual occurrences once: move c only when its old position is in E.
  let TE := T0 ++ T1 ++ E
  have hTEW : TE.Sublist W := by
    simpa only [TE, W, oldWord, List.nil_append, List.append_nil,
      List.append_assoc] using
      ((((((((List.nil_sublist A).append (List.nil_sublist [x])).append
        (List.Sublist.refl T0)).append (List.nil_sublist [y])).append
        (List.Sublist.refl T1)).append (List.nil_sublist [zpen])).append
        (List.nil_sublist T2)).append (List.nil_sublist [z])).append
        (List.Sublist.refl E)
  have hSE : (S ++ E0).Perm TE := by
    by_cases hc : c ∈ E
    · have hcperm : ([c] ++ E.erase c).Perm E := by
        simpa using (List.perm_cons_erase hc).symm
      simpa only [S, E0, if_pos hc, TE, List.append_assoc] using
        hcperm.append_left (T0 ++ T1)
    · simpa only [S, E0, if_neg hc, TE] using
        (List.Perm.refl (T0 ++ T1 ++ E))
  have hcS : c ∈ S := by
    by_cases hc : c ∈ E
    · simp [S, hc]
    · have hh : c ∈ T0 ++ T1 ++ E := hcTail
      have hearly : c ∈ T0 ++ T1 := (List.mem_append.mp hh).resolve_right hc
      simpa only [S, if_neg hc] using hearly
  have hSnod : S.Nodup :=
    (List.nodup_append'.mp (hSE.nodup_iff.mpr (hW.1.sublist hTEW))).1
  have hSsmall (i : Fin k) (hi : i ∈ S) : |f i| < Q k := by
    have hh : i ∈ TE := hSE.mem_iff.mp (List.mem_append_left E0 hi)
    simp only [TE, List.mem_append] at hh
    rcases hh with (hi | hi) | hi <;> exact hsmall i (by simp [smallWord, hi])
  have hSold (i : Fin k) (hi : i ∈ S) : i ∈ W :=
    hTEW.subset (hSE.mem_iff.mp (List.mem_append_left E0 hi))
  let a0 := mass f A
  let β := a0 + P - D
  let B1 := A ++ [x] ++ T0 ++ [y] ++ T1
  let B2 := B1 ++ [zpen] ++ T2
  let d1 := mass f B1
  let a1 := d1 + f zpen
  let d2 := mass f B2
  let a2 := d2 + f z
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsAfterA⟩ := strip_split A
    ([x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
    (by simpa only [W, oldWord, x, List.append_assoc] using hsW)
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa [a0, mass] using inStrip_prefix hsAfterA 0
  have hax : 0 ≤ a0 + r ∧ a0 + r ≤ C k := by
    simpa [a0, mass, hxval] using inStrip_prefix hsAfterA 1
  have hβ : 0 ≤ β ∧ β ≤ B := by dsimp only [β, B]; omega
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
  have ha1rich : B < a1 := by
    simpa [a1, d1, B1, Fpen, mass, add_assoc] using hpenrich
  have ha2rich : B < a2 := by
    simpa [a2, d2, B2, B1, Fz, Fpen, mass, add_assoc] using hzrich
  have hdep1 : a1 + Q k ≤ d1 := by
    have hz : Q k ≤ -f zpen := hzpenlarge
    dsimp only [a1]
    omega
  have hdep2 : a2 + Q k ≤ d2 := by
    have hz : Q k ≤ -f z := hzlarge
    dsimp only [a2]
    omega
  have hmS : mass f S = mass f T0 + mass f T1 - σ := by
    by_cases hc : c ∈ E
    · simp only [S, σ, if_pos hc, mass, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, hcval]
      ring
    · simp only [S, σ, if_neg hc, mass, List.map_append, List.sum_append, sub_zero]
  have hmE : mass f E0 = mass f E + σ := by
    have hh : mass f S + mass f E0 = mass f T0 + mass f T1 + mass f E := by
      simpa only [mass, TE, List.map_append, List.sum_append] using (hSE.map f).sum_eq
    omega
  have hmd1 : d1 = a0 + r + mass f T0 - Y + mass f T1 := by
    simp only [d1, B1, a0, Y, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, hxval]
    ring
  have hsupplyId : β + mass f S = d1 + low := by
    dsimp only [β, low]
    omega
  have hd1β : β < d1 := by omega
  have hSlo : low < mass f S := by omega
  have hsupply : low ≤ mass f (S.filter (fun i => decide (0 < f i))) :=
    hSlo.le.trans (positive_mass_dominates f S)
  have hNreserve : [c].Subperm
      (S.filter (fun i => decide (0 < -f i ∧ -f i ≤ B + 1))) := by
    apply List.Sublist.subperm
    apply List.singleton_sublist.mpr
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hcS, by rw [hcval]; omega⟩
  have hentry (i : Fin k) (hi : i ∈ S) (hip : 0 < f i) : f i ≤ Q k - 1 := by
    have hh := hSsmall i hi
    rw [abs_of_pos hip] at hh
    omega
  have hresource : (Q k - 1) - B - 1 ≤
      mass f ([] : List (Fin k)) + mass (fun i => -f i) [c] := by
    simp only [mass, List.map_nil, List.sum_nil, List.map_cons,
      List.sum_cons, add_zero, zero_add, hcval, neg_neg]
    dsimp only [B]
    omega
  obtain ⟨R, K, hRK, hRlo, hRhi⟩ :=
    signed_short_reserve_select f S [] [c] B (Q k - 1) low
      hSnod hB (by omega) (by simp) hNreserve hentry hlow hsupply hresource
  have hKR : (K ++ R).Perm S := List.perm_append_comm.trans hRK
  have hRsub : R.Subperm S := by
    have hh : R.Subperm (R ++ K) := by
      simpa using (List.Subperm.append (List.Subperm.refl R)
        (List.nil_subperm : ([] : List (Fin k)).Subperm K))
    exact hh.trans hRK.subperm
  have hKsub : K.Subperm S := by
    have hh : K.Subperm (K ++ R) := by
      simpa using (List.Subperm.append (List.Subperm.refl K)
        (List.nil_subperm : ([] : List (Fin k)).Subperm R))
    exact hh.trans hKR.subperm
  have hRsmall (i : Fin k) (hi : i ∈ R) : |f i| < Q k :=
    hSsmall i (hRsub.subset hi)
  have hKsmall (i : Fin k) (hi : i ∈ K) : |f i| < Q k :=
    hSsmall i (hKsub.subset hi)
  have hRlength : 1 ≤ R.length := by
    cases R with
    | nil => simp only [mass, List.map_nil, List.sum_nil] at hRlo; omega
    | cons i R => simp
  have hRne : R ≠ [] := by intro he; rw [he] at hRlength; simp at hRlength
  let η := low - mass f R
  let e := h + Y - P - mass f R
  have hη : -B ≤ η ∧ η ≤ 0 := by dsimp only [η]; omega
  have heq : e = h + σ + η := by dsimp only [e, η, low]; omega
  have he : 0 < e ∧ e < C k := by
    have hlo : B < h := hblocklo
    have hhi : h < D := hblockhi
    omega
  have hshift1 : (0 ≤ d1 + η ∧ d1 + η ≤ C k) ∧
      (0 ≤ a1 + η ∧ a1 + η ≤ C k) := by
    constructor <;> constructor <;> omega
  have hshift2 : (0 ≤ d2 + η ∧ d2 + η ≤ C k) ∧
      (0 ≤ a2 + η ∧ a2 + η ≤ C k) := by
    constructor <;> constructor <;> omega
  -- Actual return allocation, and the three exact complete-batch endpoints.
  have hmKR : mass f K + mass f R = mass f S := by
    simpa only [mass, List.map_append, List.sum_append] using (hKR.map f).sum_eq
  have hjoin01 : β + mass f K = d1 + η := by dsimp only [η]; omega
  have hjoin2 : a1 + η + mass f T2 = d2 + η := by
    simp only [d2, B2, a1, d1, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hOldEnd : a2 + mass f E = h := by
    simp only [a2, d2, B2, B1, h, W, oldWord, x, mass,
      List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
  have hjoinE : a2 + η + mass f E0 = e := by omega
  have hcompatible (L : List (Fin k)) (hL : ∀ i ∈ L, |f i| < Q k) :
      ∀ i ∈ L, ∀ j ∈ L, 0 < f i → f j < 0 → f i - f j ≤ C k := by
    intro i hi j hj hip hjn
    have hi' := hL i hi
    have hj' := hL j hj
    rw [abs_of_pos hip] at hi'
    rw [abs_of_neg hjn] at hj'
    omega
  obtain ⟨L01, h01, hs01⟩ := exists_order_between f K (C k) β
    (by constructor <;> omega)
    (by change 0 ≤ β + mass f K ∧ β + mass f K ≤ C k
        rw [hjoin01]; exact hshift1.1) (hcompatible K hKsmall)
  obtain ⟨L2, h2, hs2⟩ := exists_order_between f T2 (C k) (a1 + η) hshift1.2
    (by change 0 ≤ a1 + η + mass f T2 ∧ a1 + η + mass f T2 ≤ C k
        rw [hjoin2]; exact hshift2.1) (hcompatible T2 h2small)
  obtain ⟨LE, hE, hsE⟩ := exists_order_between f E0 (C k) (a2 + η) hshift2.2
    (by change 0 ≤ a2 + η + mass f E0 ∧ a2 + η + mass f E0 ≤ C k
        rw [hjoinE]; exact ⟨he.1.le, he.2.le⟩) (hcompatible E0 hE0small)
  have hm01 : mass f L01 = mass f K := by
    simpa only [mass] using (h01.map f).sum_eq
  have hm2 : mass f L2 = mass f T2 := by
    simpa only [mass] using (h2.map f).sum_eq
  -- Glue the three new strips at the checked actual retained negative gates.
  have hsZ : InStrip f (C k) (d2 + η) ([z] ++ LE) := by
    change 0 ≤ d2 + η ∧ d2 + η ≤ C k ∧ InStrip f (C k) (d2 + η + f z) LE
    have hez : d2 + η + f z = a2 + η := by dsimp only [a2]; ring
    rw [hez]
    exact ⟨hshift2.1.1, hshift2.1.2, hsE⟩
  have hs2Z : InStrip f (C k) (a1 + η) (L2 ++ [z] ++ LE) := by
    have hh := inStrip_append hs2 (show InStrip f (C k)
        ((a1 + η) + (L2.map f).sum) ([z] ++ LE) from by
      change InStrip f (C k) (a1 + η + mass f L2) ([z] ++ LE)
      rw [hm2, hjoin2]
      exact hsZ)
    simpa only [List.append_assoc] using hh
  have hsPen : InStrip f (C k) (d1 + η) ([zpen] ++ L2 ++ [z] ++ LE) := by
    change 0 ≤ d1 + η ∧ d1 + η ≤ C k ∧
      InStrip f (C k) (d1 + η + f zpen) (L2 ++ [z] ++ LE)
    have hep : d1 + η + f zpen = a1 + η := by dsimp only [a1]; ring
    rw [hep]
    exact ⟨hshift1.1.1, hshift1.1.2, hs2Z⟩
  have hsTail : InStrip f (C k) β (L01 ++ [zpen] ++ L2 ++ [z] ++ LE) := by
    have hh := inStrip_append hs01 (show InStrip f (C k)
        (β + (L01.map f).sum) ([zpen] ++ L2 ++ [z] ++ LE) from by
      change InStrip f (C k) (β + mass f L01) ([zpen] ++ L2 ++ [z] ++ LE)
      rw [hm01, hjoin01]
      exact hsPen)
    simpa only [List.append_assoc] using hh
  have hsPN : InStrip f (C k) a0 [p, n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P + -D ∧ a0 + P + -D ≤ C k
    dsimp only [β] at hβ
    omega
  have hsAPN : InStrip f (C k) 0 (A ++ [p, n]) :=
    inStrip_append hsA (by simpa [a0, mass] using hsPN)
  have hAPN : mass f (A ++ [p, n]) = β := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval]
    dsimp only [β, a0, P, mass]
    ring
  let V := A ++ [p, n] ++ L01 ++ [zpen] ++ L2 ++ [z] ++ LE
  have hsV : InStrip f (C k) 0 V := by
    have hh := inStrip_append hsAPN (show InStrip f (C k)
        (0 + ((A ++ [p, n]).map f).sum)
        (L01 ++ [zpen] ++ L2 ++ [z] ++ LE) from by
      change InStrip f (C k) (0 + mass f (A ++ [p, n]))
        (L01 ++ [zpen] ++ L2 ++ [z] ++ LE)
      rw [zero_add, hAPN]
      exact hsTail)
    simpa only [V, List.append_assoc] using hh
  have hperm : (V ++ ([x, y] ++ R)).Perm (W ++ [p, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hKRc := hKR.count_eq i
    have h01c := h01.count_eq i
    have h2c := h2.count_eq i
    have hEc := hE.count_eq i
    have hSEc := hSE.count_eq i
    simp only [TE, List.count_append] at hKRc hSEc
    simp only [V, W, oldWord, x, List.count_append, List.count_cons, List.count_nil]
    clear * - hKRc h01c h2c hEc hSEc
    omega
  have hI : [p, n].Nodup := by
    have hpn : p ≠ n := by intro he; have hv := congrArg f he; omega
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
  have hRetold (i : Fin k) (hi : i ∈ [x, y] ++ R) : i ∈ W := by
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp [W, oldWord, x]
    · exact hSold i (hRsub.subset hi)
  -- One call supplies every physical Inventory field over the original W.
  have inv : Inventory k t W V [p, n] ([x, y] ++ R) :=
    inventory_of_perm hk t W V [p, n] ([x, y] ++ R)
      hW.1 hI hIW hRetold hIL hperm
  have hWI : (W ++ [p, n]).Nodup := hW.1.append hI
    (List.disjoint_left.mpr (by intro i hiW hiI; exact hIW i hiI hiW))
  have hdisj := (List.nodup_append'.mp (hperm.nodup_iff.mpr hWI)).2.2
  have hRetabs (i : Fin k) (hi : i ∈ [x, y] ++ R) : i ∉ V :=
    fun hiv => List.disjoint_left.mp hdisj hiv hi
  have hxLarge : Large k t x := geo.xLarge
  have hyLarge : Large k t y := by
    have hh := neg_le_abs (f y)
    change Q k ≤ |f y|
    omega
  have hRnotLarge (i : Fin k) (hi : i ∈ R) : ¬ Large k t i :=
    not_le.mpr (hRsmall i hi)
  have hRweights := small_weights t R hRsmall
  have hRetlarge : largeUsed k t ([x, y] ++ R) = 2 := by
    rw [largeUsed_append, hRweights.1]
    simp [largeUsed, mass, largeWeight, hxLarge, hyLarge]
  have hIlarge : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  have hRetenergy : H k t ([x, y] ++ R) =
      3 ^ (f x).natAbs + 3 ^ (f y).natAbs := by
    rw [energy_append, hRweights.2, Nat.add_zero]
    simp [H, mass, energyWeight, hxLarge, hyLarge, f, s]
  have hIenergy : H k t [p, n] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    simp [H, mass, energyWeight, geo.pLarge, show Large k t n from geo.nLarge, f, s]
  have hG : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hIlarge, hRetlarge] at hh
    clear * - hh
    omega
  have hU : U V = U W + R.length := by
    have hh := inv.countBalance
    simp only [List.length_append, List.length_cons, List.length_nil] at hh
    clear * - hh
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    have hh := inv.energyBalance
    rw [hRetenergy, hIenergy] at hh
    clear * - hh
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
  have hRetfilter : (([x, y] ++ R).toFinset.filter (fun i => ¬ Large k t i)) =
      R.toFinset := by
    ext i
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨hi | hi, hn⟩
      · rcases hi with rfl | rfl
        · exact (hn hxLarge).elim
        · exact (hn hyLarge).elim
      · exact hi
    · intro hi
      exact ⟨Or.inr hi, hRnotLarge i hi⟩
  have hSmall : remainingSmall t V = remainingSmall t W ∪ R.toFinset := by
    simpa only [hRetfilter] using inv.smallPartition
  have hSmallDisjoint : Disjoint (remainingSmall t W) R.toFinset := by
    simpa only [hRetfilter] using inv.smallDisjoint
  have hretain (i : Fin k) (hiW : i ∈ W) (his : |s k t i| < Q k)
      (hiR : i ∉ R) : i ∈ V := by
    have hix : i ≠ x := by
      intro he; subst i
      exact (not_lt_of_ge (show Q k ≤ |s k t x| from hxLarge)) his
    have hiy : i ≠ y := by
      intro he; subst i
      exact (not_lt_of_ge (show Q k ≤ |s k t y| from hyLarge)) his
    have hiRet : i ∉ [x, y] ++ R := by simp [hix, hiy, hiR]
    apply List.mem_toFinset.mp
    rw [inv.used]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨List.mem_toFinset.mpr hiW, by simpa only [List.mem_toFinset] using hiRet⟩)
  have hRetmass : mass f ([x, y] ++ R) = r - Y + mass f R := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hxval]
    dsimp only [Y, mass]
    ring
  have hImass : mass f [p, n] = P - D := by
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, hnval]
    dsimp only [P]
    ring
  have hEnd : mass f V = e := by
    have hh := inv.sourceBalance
    change mass f V + mass f ([x, y] ++ R) = h + mass f [p, n] at hh
    rw [hRetmass, hImass] at hh
    dsimp only [e]
    clear * - hh hnative
    omega
  have hcomp : remainingMass f V = -e := by rw [inv.complementSum, hEnd]
  have hv : Legal k t V := legal_of_strip inv.nodup hsV
  refine ⟨V, [p, n], [x, y] ++ R, rfl, hv, inv.nodup, hsV, hv.2,
    inv, hperm, hJ, Or.inr (Or.inr ⟨hpenrich, hzrich,
      R, K, L01, L2, LE, hKR, hRsub, hRsmall, hlow, hRlo, hRhi,
      hRne, hRlength, hcval, hθ, hθB, hθlead, h01, h2, hE, rfl, rfl,
      hRetabs, by simp [V], by simp [V], hretain, hG, hU,
      hSmall, hSmallDisjoint, hH, hHstrict, hη.1, hη.2,
      heq, hEnd, he.1, he.2, hcomp⟩)⟩

end D5.S3.Combinatorics.Circle.UpperTerminalQuarterExchange
