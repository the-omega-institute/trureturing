/- GID: D5/S3/Combinatorics/Circle/LateNegativePrefixExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/LateNegativePrefixExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: An actual late negative SMALL reserve supplies strict-G prefix descent. -/
module
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange

/-! # Pull a late negative reserve across one negative LARGE, then truncate

The original physical prefix F is arbitrary, with unrestricted signs and LARGE
count. The entire old suffix is returned, except for the actual reserve when it
is pulled forward. Full Circle C3.1 remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.LateNegativePrefixExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy
open TwoOppositeLargeExchange FirstNegativeShiftExchange

/-- A physical negative reserve in the old suffix, with magnitude between
P-Q and C-P, supplies a literal improving prefix. No SMALL order, endpoint,
blocking, parity, minimizer, selector, or other return resource is assumed. -/
theorem actualSource_late_negative_reserve_prefix_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p zpen c : Fin k)
    (F R : List (Fin k)) (m : ℤ)
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (F ++ [zpen] ++ R))
    (hpunused : p ∉ F ++ [zpen] ++ R)
    (hnunused : hit k 1 p ∉ F ++ [zpen] ++ R)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hcR : c ∈ R) (hcvalue : s k t c = -m)
    (hmlower : s k t p - Q k ≤ m)
    (hmupper : m ≤ C k - s k t p)
    (hreturn : largeUsed k t R ≤ 1) :
    let n := hit k 1 p
    let W := F ++ [zpen] ++ R
    let a := mass (s k t) (F ++ [zpen])
    let B := C k - s k t p
    0 < m ∧ |s k t c| < Q k ∧
    mass (s k t) F = a - s k t zpen ∧
    0 ≤ a ∧ a ≤ C k + s k t zpen ∧ C k + s k t zpen ≤ Q k - 1 ∧
    ∃ V Ret : List (Fin k),
      ((a ≤ B ∧ V = F ++ [zpen, p, n] ∧ Ret = R ∧
          mass (s k t) V = a + s k t p - |s k t n|) ∨
       (B < a ∧ V = F ++ [c, zpen, p, n] ∧ Ret = R.erase c ∧
          0 < a - m ∧ a - m ≤ B ∧
          mass (s k t) V = a - m + s k t p - |s k t n|)) ∧
      Legal k t V ∧ V.Nodup ∧ Ret.Nodup ∧
      (∀ i ∈ Ret, i ∈ W) ∧ (∀ i ∈ Ret, i ∉ V) ∧
      InStrip (s k t) (C k) 0 V ∧
      (∀ d : ℕ, 0 ≤ mass (s k t) (V.take d) ∧
        mass (s k t) (V.take d) ≤ C k) ∧
      Inventory k t W V [p, n] Ret ∧
      (V ++ Ret).Perm (W ++ [p, n]) ∧
      largeUsed k t Ret = largeUsed k t R ∧
      G k t V + 2 = G k t W + largeUsed k t R ∧
      G k t V < G k t W ∧ J k t V < J k t W ∧
      (0 ≤ mass (s k t) V ∧ mass (s k t) V ≤ C k) ∧
      remainingMass (s k t) V = -mass (s k t) V ∧
      mass (s k t) V + mass (s k t) Ret =
        mass (s k t) W + s k t p - |s k t n| ∧
      remainingSmall t V = remainingSmall t W ∪
        Ret.toFinset.filter (fun i => ¬ Large k t i) ∧
      Disjoint (remainingSmall t W)
        (Ret.toFinset.filter (fun i => ¬ Large k t i)) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let W := F ++ [zpen] ++ R
  let P := f p
  let D := |f n|
  let a := mass f (F ++ [zpen])
  let B := C k - P
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hp : 0 < P := hpositive
  have hex : N k < 3 * P := by simpa [P, f, abs_of_pos hpositive] using hexpand
  have hPQ : Q k < P := by omega
  have hB : B < Q k := by dsimp only [B]; omega
  have hmlo : P - Q k ≤ m := hmlower
  have hmhi : m ≤ B := hmupper
  have hm : 0 < m := by omega
  have hcval : f c = -m := hcvalue
  have hcsmall : |f c| < Q k := by rw [hcval, abs_neg, abs_of_pos hm]; omega
  have hcnotlarge : ¬ Large k t c := not_le.mpr hcsmall
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hDP : D < P := by simpa [f, n, D, P, abs_of_pos hpositive] using geo.strictOrder.1
  have hD0 : 0 ≤ D := abs_nonneg _
  have hz : Q k ≤ -f zpen := hzpenlarge
  have hsold : InStrip f (C k) 0 W := strip_of_legal hW
  have hsold' : InStrip f (C k) 0 (F ++ ([zpen] ++ R)) := by
    simpa [W, List.append_assoc] using hsold
  have hsF := (strip_split F ([zpen] ++ R) hsold').1
  have hsafter := (strip_split F ([zpen] ++ R) hsold').2
  have hd1 : 0 ≤ mass f F ∧ mass f F ≤ C k := by
    simpa [mass] using inStrip_prefix hsF F.length
  have haeq : a = mass f F + f zpen := by simp [a, mass]
  have ha : 0 ≤ a ∧ a ≤ C k := by
    simpa [a, mass] using inStrip_prefix hsafter 1
  have havalley : a ≤ C k + f zpen := by omega
  have hcap : C k + f zpen ≤ Q k - 1 := by omega
  have hI : ([p, n] : List (Fin k)).Nodup := by
    have hpn : p ≠ n := by intro he; have hh := congrArg f he; omega
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
  have hIlarge : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  obtain ⟨V, Ret, hsV, inv, hperm, hRW, hRetlarge, hbranches⟩ :
      ∃ V Ret : List (Fin k),
        InStrip f (C k) 0 V ∧ Inventory k t W V [p, n] Ret ∧
        (V ++ Ret).Perm (W ++ [p, n]) ∧
        (∀ i ∈ Ret, i ∈ W) ∧ largeUsed k t Ret = largeUsed k t R ∧
        ((a ≤ B ∧ V = F ++ [zpen, p, n] ∧ Ret = R ∧
            mass f V = a + P - D) ∨
         (B < a ∧ V = F ++ [c, zpen, p, n] ∧ Ret = R.erase c ∧
            0 < a - m ∧ a - m ≤ B ∧ mass f V = a - m + P - D)) := by
    by_cases hcut : a ≤ B
    · obtain ⟨hv, hinv, hper, _, _, _⟩ :=
        actualSource_prefix_pair_truncation k t hk p (F ++ [zpen]) R
          hpositive hnlarge hexpand
          (by simpa only [List.append_assoc] using hW)
          (by simpa only [List.append_assoc] using hpunused)
          (by simpa only [List.append_assoc] using hnunused) hcut hreturn
      have hmass : mass f ((F ++ [zpen]) ++ [p, n]) = a + P - D := by
        dsimp only [a, P]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        rw [hnval]
        ring
      refine ⟨(F ++ [zpen]) ++ [p, n], R, strip_of_legal hv, ?_, ?_,
        (fun i hi => by simp [W, List.append_assoc, hi]), rfl,
        Or.inl ⟨hcut, by simp only [List.append_assoc, List.cons_append,
          List.nil_append], rfl, hmass⟩⟩
      · simpa only [W, List.append_assoc] using hinv
      · simpa only [W, List.append_assoc] using hper
    · have hhigh : B < a := lt_of_not_ge hcut
      have hshift : 0 < a - m ∧ a - m ≤ B := by omega
      -- The four new heights after the unchanged physical F.
      have hgate :
          (0 ≤ mass f F - m ∧ mass f F - m ≤ C k) ∧
          (0 ≤ a - m ∧ a - m ≤ C k) ∧
          (0 ≤ a - m + P ∧ a - m + P ≤ C k) ∧
          (0 ≤ a - m + P - D ∧ a - m + P - D ≤ C k) := by
        dsimp only [B] at hshift
        exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
          ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      have hsblock : InStrip f (C k) (mass f F) [c, zpen, p, n] := by
        change 0 ≤ mass f F ∧ mass f F ≤ C k ∧
          0 ≤ mass f F + f c ∧ mass f F + f c ≤ C k ∧
          0 ≤ mass f F + f c + f zpen ∧
            mass f F + f c + f zpen ≤ C k ∧
          0 ≤ mass f F + f c + f zpen + f p ∧
            mass f F + f c + f zpen + f p ≤ C k ∧
          0 ≤ mass f F + f c + f zpen + f p + f n ∧
            mass f F + f c + f zpen + f p + f n ≤ C k
        rw [hcval, hnval]
        rcases hgate with ⟨hcg, hzg, hpg, hng⟩
        exact ⟨hd1.1, hd1.2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      have hsnew : InStrip f (C k) 0 (F ++ [c, zpen, p, n]) :=
        inStrip_append hsF (by simpa only [mass, zero_add] using hsblock)
      have hcr : ([c] ++ R.erase c).Perm R := (List.perm_cons_erase hcR).symm
      have hswap : ([c, zpen] ++ R.erase c).Perm ([zpen] ++ R) := by
        have hfirst : ([c, zpen] ++ R.erase c).Perm ([zpen, c] ++ R.erase c) := by
          exact (List.perm_append_comm : ([c] ++ [zpen]).Perm
            ([zpen] ++ [c])).append_right (R.erase c)
        exact hfirst.trans (by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            hcr.append_left [zpen])
      have hslide : ((F ++ [c, zpen, p, n]) ++ R.erase c).Perm
          ((F ++ [c, zpen] ++ R.erase c) ++ [p, n]) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          (List.perm_append_comm : ([p, n] ++ R.erase c).Perm
            (R.erase c ++ [p, n])).append_left (F ++ [c, zpen])
      have hfinish : ((F ++ [c, zpen] ++ R.erase c) ++ [p, n]).Perm
          (W ++ [p, n]) := by
        simpa only [W, List.append_assoc] using (hswap.append_left F).append_right [p, n]
      have hper := hslide.trans hfinish
      have hret (i : Fin k) (hi : i ∈ R.erase c) : i ∈ W := by
        have hiR := List.mem_of_mem_erase hi
        simpa [W, List.append_assoc] using
          (List.mem_append_right (F ++ [zpen]) hiR)
      have hinv := inventory_of_perm hk t W (F ++ [c, zpen, p, n])
        [p, n] (R.erase c) hW.1 hI hIW hret hIL hper
      have hweight : largeWeight k t c = 0 := by simp [largeWeight, hcnotlarge]
      have hlarge : largeUsed k t (R.erase c) = largeUsed k t R := by
        have he := ((List.perm_cons_erase hcR).map (largeWeight k t)).sum_eq
        simpa only [largeUsed, mass, List.map_cons, List.sum_cons, hweight,
          zero_add] using he.symm
      have hmass : mass f (F ++ [c, zpen, p, n]) = a - m + P - D := by
        dsimp only [a, P]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        rw [hcval, hnval]
        ring
      exact ⟨F ++ [c, zpen, p, n], R.erase c, hsnew, hinv, hper, hret,
        hlarge, Or.inr ⟨hhigh, rfl, rfl, hshift.1, hshift.2, hmass⟩⟩
  have hWI : (W ++ [p, n]).Nodup := hW.1.append hI
    (List.disjoint_left.mpr (by intro i hiW hiI; exact hIW i hiI hiW))
  have hVR := List.nodup_append'.mp (hperm.nodup_iff.mpr hWI)
  have hnoRet (i : Fin k) (hi : i ∈ Ret) : i ∉ V := by
    intro hiV
    exact List.disjoint_left.mp hVR.2.2 hiV hi
  have hG : G k t V + 2 = G k t W + largeUsed k t R := by
    simpa only [hIlarge, hRetlarge] using inv.largeBalance
  have hstrict : G k t V < G k t W := by omega
  have hJ : J k t V < J k t W := Prod.Lex.toLex_lt_toLex.mpr (Or.inl hstrict)
  have hend : 0 ≤ mass f V ∧ mass f V ≤ C k := by
    simpa only [mass, List.take_length, zero_add] using inStrip_prefix hsV V.length
  have hsource : mass f V + mass f Ret = mass f W + P - D := by
    have hpnmass : mass f [p, n] = P - D := by
      simp [mass, hnval, P, sub_eq_add_neg]
    have hh := inv.sourceBalance
    change mass f V + mass f Ret = mass f W + mass f [p, n] at hh
    rw [hpnmass] at hh
    omega
  refine ⟨hm, hcsmall, ?_, ha.1, havalley, hcap, V, Ret,
    hbranches, legal_of_strip inv.nodup hsV, inv.nodup, hVR.2.1, hRW, hnoRet,
    hsV, ?_, inv, hperm, hRetlarge, hG, hstrict, hJ, hend,
    inv.complementSum, hsource, inv.smallPartition, inv.smallDisjoint⟩
  · simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ring
  · intro d
    simpa only [mass, zero_add] using inStrip_prefix hsV d

end D5.S3.Combinatorics.Circle.LateNegativePrefixExchange
