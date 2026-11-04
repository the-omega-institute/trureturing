/- GID: D5/S3/Combinatorics/Circle/TerminalSmallOwnership
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TerminalSmallOwnership
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Terminal SMALL ownership and two-step orbit transition for an arbitrary physical signed source word. -/
module
public import D5.S3.Combinatorics.Circle.TerminalLargeSubstitution
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange

/-! Terminal SMALL ownership and the actual two-step orbit transition for an
arbitrary physical signed source word. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.TerminalSmallOwnership
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open FirstNegativeShiftExchange
open scoped BigOperators

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.take_zero, List.take_succ_cons, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero, zero_add] at *) <;> omega))

private theorem small_append_balances (k t : ℕ) (W : List (Fin k))
    (hWnod : W.Nodup) (i : Fin k) (hi : i ∉ W)
      (hiSmall : ¬ Large k t i) :
    G k t (W ++ [i]) = G k t W ∧ H k t (W ++ [i]) = H k t W ∧
      U (W ++ [i]) + 1 = U W := by
  have hVnod : (W ++ [i]).Nodup := hWnod.append (by simp)
    (List.disjoint_left.mpr (by
      intro x hx hxi
      have : x = i := by simpa using hxi
      subst x
      exact hi hx))
  have hwg := physical_balance (largeWeight k t) W hWnod
  have hvg := physical_balance (largeWeight k t) (W ++ [i]) hVnod
  have hwc := physical_balance (fun _ : Fin k => (1 : ℕ)) W hWnod
  have hvc := physical_balance (fun _ : Fin k => (1 : ℕ)) (W ++ [i]) hVnod
  have hL : largeUsed k t (W ++ [i]) = largeUsed k t W := by
    simp [largeUsed, mass, largeWeight, hiSmall]
  have hH : H k t (W ++ [i]) = H k t W := by
    simp [H, mass, energyWeight, hiSmall]
  have hG : G k t (W ++ [i]) = G k t W := by
    change G k t W + largeUsed k t W = _ at hwg
    change G k t (W ++ [i]) + largeUsed k t (W ++ [i]) = _ at hvg
    rw [hL] at hvg
    omega
  have hU : U (W ++ [i]) + 1 = U W := by
    have hwc' : U W + W.length = k := by
      simpa [U, mass, List.map_const'] using hwc
    have hvc' : U (W ++ [i]) + (W ++ [i]).length = k := by
      simpa [U, mass, List.map_const'] using hvc
    simp only [List.length_append, List.length_singleton] at hvc'
    omega
  exact ⟨hG, hH, hU⟩

private theorem fresh_cut (k t : ℕ) (K R S : List (Fin k))
    (hW : (K ++ R).Nodup) (hS : S.Nodup)
    (hfresh : ∀ x ∈ S, x ∉ K ++ R) :
    (K ++ S).Nodup ∧
      G k t (K ++ S) + largeUsed k t S =
        G k t (K ++ R) + largeUsed k t R := by
  have hK := hW.sublist (List.sublist_append_left K R)
  have hV : (K ++ S).Nodup := hK.append hS (List.disjoint_left.mpr (by
    intro x hx hxS
    exact hfresh x hxS (List.mem_append_left R hx)))
  have hw := physical_balance (largeWeight k t) (K ++ R) hW
  have hv := physical_balance (largeWeight k t) (K ++ S) hV
  change G k t (K ++ R) + largeUsed k t (K ++ R) = _ at hw
  change G k t (K ++ S) + largeUsed k t (K ++ S) = _ at hv
  simp only [largeUsed_append] at hw hv
  exact ⟨hV, by omega⟩

theorem actualSource_terminal_small_ownership_prefix
    (k t : ℕ) (hk : 3 ≤ k) (p z : Fin k)
    (F E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (F ++ [z] ++ E))
    (hpunused : p ∉ F ++ [z] ++ E)
    (hnunused : hit k 1 p ∉ F ++ [z] ++ E)
    (hsmall : ∀ i ∈ E, |s k t i| < Q k)
    (hz : Q k ≤ -s k t z)
    (hmin : ∀ V : List (Fin k), Legal k t V →
      J k t (F ++ [z] ++ E) ≤ J k t V) :
    let f := s k t
    let W := F ++ [z] ++ E
    let n := hit k 1 p
    let P := f p
    let D := |f n|
    let B := C k - P
    let d := P - D
    let u := mass f F
    let q := fun m : ℕ => mass f (F ++ [z] ++ E.take m)
    C k - d < u ∧
    (∀ m : ℕ, B < q m ∧ q m < D) ∧
    (∀ i : Fin k, |f i| < Q k → 0 ≤ f i → i ∈ W) := by
  classical
  dsimp only
  let f := s k t
  let W := F ++ [z] ++ E
  let n := hit k 1 p
  let P := f p
  let D := |f n|
  let B := C k - P
  let d := P - D
  let u := mass f F
  let q := fun m : ℕ => mass f (F ++ [z] ++ E.take m)
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change (∀ i ∈ E, |f i| < Q k) at hsmall
  change Q k ≤ -f z at hz
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hD : Q k ≤ D := hnlarge
  have hDP : D < P := by
    simpa only [f, n, D, P, abs_of_pos hpositive] using geo.strictOrder.1
  have hbudget : 2 * P ≤ C k + Q k := by
    simpa [P, f, abs_of_pos hpositive] using geo.budget
  have hDrel : D = 2 * B + 1 := by
    have hh := geo.firstEquation
    change D = N k - 2 * |f p| at hh
    rw [hpabs, hN] at hh
    dsimp [B]
    rw [hC]
    omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have hBq : B ≤ Q k - 2 := by
    dsimp [B] at *
    omega
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hNodd _)
  have hFz : mass f (F ++ [z]) = u + f z := by simp [u, mass]
  have hqzero : q 0 = u + f z := by simp [q, mass, u]
  have hqbound (m : ℕ) : 0 ≤ q m ∧ q m ≤ C k := by
    have hs := strip_of_legal hW
    have hpref := (strip_split (F ++ [z] ++ E.take m) (E.drop m) (by
      simpa [W, List.append_assoc, List.take_append_drop] using hs)).1
    have hh := inStrip_prefix hpref (F ++ [z] ++ E.take m).length
    simp only [List.take_length, zero_add, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hh
    simpa [q, mass, f, add_assoc] using hh
  have htail_small (m : ℕ) : ∀ i ∈ E.drop m, |f i| < Q k := by
    intro i hi
    exact hsmall i (List.mem_of_mem_drop hi)
  have htail_large_zero (m : ℕ) : largeUsed k t (E.drop m) = 0 := by
    exact (small_weights t (E.drop m) (htail_small m)).1
  have hprefix_legal (m : ℕ) : Legal k t (F ++ [z] ++ E.take m ++ E.drop m) := by
    simpa [W, List.append_assoc, List.take_append_drop] using hW
  have hprefix_fresh (m : ℕ) : p ∉ F ++ [z] ++ E.take m ++ E.drop m := by
    simpa [W, List.append_assoc, List.take_append_drop] using hpunused
  have hn_prefix_fresh (m : ℕ) : n ∉ F ++ [z] ++ E.take m ++ E.drop m := by
    simpa [W, List.append_assoc, List.take_append_drop] using hnunused
  have hcorridor_low (m : ℕ) : B < q m := by
    by_contra hnot
    have hcut : q m ≤ C k - P := by simpa [B] using le_of_not_gt hnot
    obtain ⟨hV, _, _, _, _, hJ⟩ :=
      actualSource_prefix_pair_truncation k t hk p
        (F ++ [z] ++ E.take m) (E.drop m) hpositive hnlarge hexpand
        (hprefix_legal m) (hprefix_fresh m) (hn_prefix_fresh m) hcut
        (by rw [htail_large_zero m]; omega)
    have hJ' : J k t (F ++ [z] ++ E.take m ++ [p, n]) < J k t W := by
      simpa [W, List.append_assoc, List.take_append_drop] using hJ
    exact (not_lt_of_ge (hmin _ hV)) hJ'
  have hn_large : Large k t n := geo.nLarge
  have hcorridor_high (m : ℕ) : q m < D := by
    by_contra hnot
    have hge : D ≤ q m := le_of_not_gt hnot
    let K := F ++ [z] ++ E.take m
    let R := E.drop m
    have hsK : InStrip f (C k) 0 K := by
      exact (strip_split K R (by simpa [K, R, W, List.append_assoc,
        List.take_append_drop] using (strip_of_legal hW))).1
    have hgate : 0 ≤ q m - D ∧ q m - D ≤ C k := by
      have hq := hqbound m
      exact ⟨by omega, by omega⟩
    have hsKn : InStrip f (C k) 0 (K ++ [n]) := by
      have hsingle : InStrip f (C k) (0 + mass f K) [n] := by
        have hqK : q m = mass f K := rfl
        have hq := hqbound m
        rw [hqK] at hq
        simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, zero_add]
        rw [hnval]
        exact ⟨by simpa using hq.1, by simpa using hq.2, by omega, by omega⟩
      exact inStrip_append hsK hsingle
    have hnod : (K ++ [n]).Nodup := by
      have hKnod : K.Nodup := (hprefix_legal m).1.sublist (List.sublist_append_left K R)
      apply hKnod.append (by simp)
      apply List.disjoint_left.mpr
      intro x hx hxn
      have : x = n := by simpa using hxn
      subst x
      exact hn_prefix_fresh m (List.mem_append_left R hx)
    have hperm : ((K ++ [n]) ++ R).Perm ((K ++ R) ++ [n]) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm : ([n] ++ R).Perm (R ++ [n])).append_left K
    have hRsub : ∀ x ∈ R, x ∈ K ++ R := by
      intro x hx; exact List.mem_append_right K hx
    have hI : ([n] : List (Fin k)).Nodup := by simp
    have hIW : ∀ x ∈ ([n] : List (Fin k)), x ∉ K ++ R := by
      intro x hx
      have : x = n := by simpa using hx
      subst x
      exact hn_prefix_fresh m
    have hIL : ∀ x ∈ ([n] : List (Fin k)), Large k t x := by
      intro x hx
      have : x = n := by simpa using hx
      simpa [this] using hn_large
    have hinv := inventory_of_perm hk t (K ++ R) (K ++ [n]) [n] R
      (hprefix_legal m).1 hI hIW hRsub hIL hperm
    have hG : G k t (K ++ [n]) < G k t W := by
      have hbal := hinv.largeBalance
      rw [htail_large_zero m] at hbal
      have hIlarge : largeUsed k t [n] = 1 := by
        simp [largeUsed, mass, largeWeight, hn_large]
      have hG' : G k t (K ++ [n]) < G k t (K ++ R) := by omega
      simpa [K, R, W, List.append_assoc, List.take_append_drop] using hG'
    have hJ : J k t (K ++ [n]) < J k t W := by
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inl (show G k t (K ++ [n]) < G k t W from hG)
    exact (not_lt_of_ge (hmin _ (legal_of_strip hnod hsKn))) hJ
  have hWend : mass f W < D := by
    have hh := hcorridor_high E.length
    simpa only [q, W, mass, f, List.take_length, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero] using hh
  have hWend_nonneg : 0 ≤ mass f W := by
    simpa [mass] using (inStrip_prefix (strip_of_legal hW) W.length).1
  have hq0upper : q 0 ≤ Q k - 1 := by
    have hFnonneg : 0 ≤ u := by
      have hh := inStrip_prefix
        ((strip_split F ([z] ++ E) (by simpa [W, List.append_assoc] using
          (strip_of_legal hW))).1) F.length
      simpa [u, mass] using hh.1
    have hFbound : u ≤ C k := by
      have hh := inStrip_prefix
        ((strip_split F ([z] ++ E) (by simpa [W, List.append_assoc] using
          (strip_of_legal hW))).1) F.length
      simpa [u, mass] using hh.2
    have hq := hqzero
    omega
  refine ⟨?_, ?_, ?_⟩
  · by_contra hnot
    have huhi : u ≤ C k - d := le_of_not_gt hnot
    have hq0 := hcorridor_low 0
    have hq0' := hcorridor_high 0
    have hq0eq : q 0 = u + f z := hqzero
    have huD : D ≤ u := by
      rw [hq0eq] at hq0
      have hz' : Q k ≤ -f z := hz
      omega
    let V := F ++ [n, p]
    let R := [z] ++ E
    have hstripF : InStrip f (C k) 0 F :=
      (strip_split F ([z] ++ E) (by simpa [W, List.append_assoc] using
        (strip_of_legal hW))).1
    have hstripV : InStrip f (C k) 0 V := by
      dsimp [V]
      have hsingle : InStrip f (C k) (0 + mass f F) [n, p] := by
        simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        rw [hnval]
        dsimp [d] at huhi
        have hFmass : mass f F = u := rfl
        rw [hFmass]
        exact ⟨by simpa [u, mass] using (inStrip_prefix hstripF F.length).1,
          by simpa [u, mass] using (inStrip_prefix hstripF F.length).2,
          by omega, by omega, by omega, by omega⟩
      exact inStrip_append hstripF hsingle
    have hFnod : F.Nodup := hW.1.sublist
      (by simpa [W, List.append_assoc] using (List.sublist_append_left F ([z] ++ E)))
    have hI : ([n, p] : List (Fin k)).Nodup := by
      have hnp : n ≠ p := by
        intro he
        have hh := congrArg f he
        omega
      simp [hnp]
    have hIW : ∀ x ∈ ([n, p] : List (Fin k)), x ∉ W := by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hnunused
      · exact hpunused
    have hIL : ∀ x ∈ ([n, p] : List (Fin k)), Large k t x := by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simpa [n] using geo.nLarge
      · exact geo.pLarge
    have hRsub : ∀ x ∈ R, x ∈ W := by
      intro x hx
      change x ∈ [z] ++ E at hx
      change x ∈ F ++ [z] ++ E
      rcases List.mem_append.mp hx with hx | hx
      · have hxz : x = z := by simpa using hx
        subst x
        simp [W]
      · exact List.mem_append_right (F ++ [z]) hx
    have hperm : (V ++ R).Perm (W ++ [n, p]) := by
      simpa [V, R, W, List.append_assoc] using
        (List.perm_append_comm : ([n, p] ++ ([z] ++ E)).Perm
          (([z] ++ E) ++ [n, p])).append_left F
    have hinv := inventory_of_perm hk t W V [n, p] R hW.1 hI hIW hRsub hIL hperm
    have hIlarge : largeUsed k t [n, p] = 2 := by
      have hnlarge' : Large k t n := by simpa [n] using geo.nLarge
      simp [largeUsed, mass, largeWeight, hnlarge', geo.pLarge]
    have hRlarge : largeUsed k t R = 1 := by
      have hE0 := (small_weights t E hsmall).1
      have hzlarge : Large k t z := by
        unfold Large
        rw [abs_of_neg (by omega : f z < 0)]
        exact hz
      have hzw : largeWeight k t z = 1 := by
        change (if Large k t z then 1 else 0) = 1
        simp [hzlarge]
      simp [R, largeUsed_append, largeUsed_cons, hE0, hzw]
    have hG : G k t V < G k t W := by
      have hh := hinv.largeBalance
      rw [hIlarge, hRlarge] at hh
      omega
    have hJ : J k t V < J k t W := by
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inl hG
    exact (not_lt_of_ge (hmin V (legal_of_strip hinv.nodup hstripV))) hJ
  · intro m
    exact ⟨hcorridor_low m, hcorridor_high m⟩
  · intro i hiAbs hiNonneg
    by_contra hiUsed
    have hiFresh : i ∉ W := hiUsed
    have hiNonnegF : 0 ≤ f i := by simpa [f] using hiNonneg
    have hiSmall : ¬ Large k t i := by
      have hiAbs' : |s k t i| < Q k := by simpa [f] using hiAbs
      unfold Large
      exact not_le_of_gt hiAbs'
    by_cases happend : mass f W + f i ≤ C k
    · have hsW := strip_of_legal hW
      have hsingle : InStrip f (C k) (0 + mass f W) [i] := by
        simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, zero_add]
        have hWend_bounds : 0 ≤ mass f W ∧ mass f W ≤ C k :=
          ⟨hWend_nonneg, by simpa [mass] using (inStrip_prefix hsW W.length).2⟩
        change 0 ≤ mass f W ∧ mass f W ≤ C k ∧
          0 ≤ mass f W + f i ∧ mass f W + f i ≤ C k
        exact ⟨by omega, by omega, by omega, by omega⟩
      have hVstrip : InStrip f (C k) 0 (W ++ [i]) := inStrip_append hsW hsingle
      have hVnod : (W ++ [i]).Nodup := hW.1.append (by simp)
        (List.disjoint_left.mpr (by
          intro x hx hxi
          have : x = i := by simpa using hxi
          subst x
          exact hiFresh hx))
      obtain ⟨hG, hH, hU⟩ := small_append_balances k t W hW.1 i hiFresh hiSmall
      have hUlt : U (W ++ [i]) < U W := by omega
      have hJ : J k t (W ++ [i]) < J k t W := by
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr
          (Or.inr ⟨hH, hUlt⟩)⟩
      exact (not_lt_of_ge (hmin _ (legal_of_strip hVnod hVstrip))) hJ
    · have hfail : C k < mass f W + f i := lt_of_not_ge happend
      have hiv : f i ≤ Q k - 1 := by
        have hiAbs' : |f i| < Q k := by simpa [f] using hiAbs
        have hiNonneg' : 0 ≤ f i := by simpa [f] using hiNonneg
        rw [abs_of_nonneg hiNonneg'] at hiAbs'
        omega
      have hiB : B < f i := by
        have hWD := hWend
        have hCD : C k - D = B + d := by dsimp [B, d]; ring
        omega
      let K := F ++ [z]
      let V := K ++ [i, n]
      have hsK : InStrip f (C k) 0 K := by
        exact (strip_split K E (by simpa [K, W, List.append_assoc] using
          (strip_of_legal hW))).1
      have hq0K : mass f K = q 0 := by simp [K, q, mass]
      have hgate : 0 ≤ mass f K + f i ∧ mass f K + f i ≤ C k ∧
          0 ≤ mass f K + f i + f n ∧ mass f K + f i + f n ≤ C k := by
        rw [hq0K, hnval]
        have hq0 := hcorridor_low 0
        have hq0u := hq0upper
        omega
      have hsV : InStrip f (C k) 0 V := by
        dsimp [V]
        have hsingle : InStrip f (C k) (0 + mass f K) [i, n] := by
          simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero, zero_add]
          rw [hnval]
          exact ⟨by omega, by omega, by omega, by omega⟩
        exact inStrip_append hsK hsingle
      have hKnod : K.Nodup := hW.1.sublist
        (by simpa [K, W, List.append_assoc] using (List.sublist_append_left K E))
      have hin : i ≠ n := by
        intro he
        have hni : Large k t i := by simpa [he, n] using geo.nLarge
        change Q k ≤ |f i| at hni
        have hiAbs' : |f i| < Q k := by simpa [f] using hiAbs
        have hiNonneg' : 0 ≤ f i := by simpa [f] using hiNonneg
        rw [abs_of_nonneg hiNonneg'] at hiAbs'
        have hni' : Q k ≤ f i := by simpa [abs_of_nonneg hiNonneg'] using hni
        exact (not_le_of_gt hiAbs') hni'
      have hI : ([i, n] : List (Fin k)).Nodup := by simp [hin]
      have hVnod : V.Nodup := by
        apply hKnod.append hI
        apply List.disjoint_left.mpr
        intro x hx hxi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxi
        rcases hxi with rfl | rfl
        · exact hiFresh (by simpa [K, W, List.append_assoc] using
            (List.mem_append_left E hx))
        · exact hnunused (by simpa [K, W, List.append_assoc] using
            (List.mem_append_left E hx))
      let W' := W ++ [i]
      have hW'nod : W'.Nodup := by
        dsimp [W']
        exact hW.1.append (by simp)
          (List.disjoint_left.mpr (by
            intro x hx hxi
            have : x = i := by simpa using hxi
            subst x
            exact hiFresh hx))
      have hIW : ∀ x ∈ ([n] : List (Fin k)), x ∉ W' := by
        intro x hx
        have hx' : x = n := by simpa using hx
        subst x
        intro hnW'
        rcases List.mem_append.mp hnW' with hnW | hni'
        · exact hnunused hnW
        · have hniEq : n = i := by simpa using hni'
          exact hin hniEq.symm
      have hIL : ∀ x ∈ ([n] : List (Fin k)), Large k t x := by
        intro x hx
        simpa [show x = n by simpa using hx, n] using geo.nLarge
      have hRsub : ∀ x ∈ E, x ∈ W' := by
        intro x hx
        change x ∈ W ++ [i]
        have hxW : x ∈ W := by
          simpa [W] using (List.mem_append_right (F ++ [z]) hx)
        exact List.mem_append_left [i] hxW
      have hperm : (V ++ E).Perm (W' ++ [n]) := by
        simpa [V, K, W', W, List.append_assoc] using
          (List.perm_append_comm : ([i, n] ++ E).Perm (E ++ [i, n])).append_left K
      have hinv := inventory_of_perm hk t W' V [n] E hW'nod
        (by simp) hIW hRsub hIL hperm
      have hbal := small_append_balances k t W hW.1 i hiFresh hiSmall
      have hG : G k t V < G k t W := by
        have hh := hinv.largeBalance
        have hE0 := (small_weights t E hsmall).1
        have hiWg := hbal.1
        have hnG : largeUsed k t [n] = 1 := by
          have hnL : Large k t n := by simpa [n] using geo.nLarge
          simp [largeUsed, mass, largeWeight, hnL]
        rw [hE0] at hh
        rw [hnG] at hh
        dsimp [W'] at hh
        rw [hiWg] at hh
        omega
      have hJ : J k t V < J k t W := by
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl hG
      exact (not_lt_of_ge (hmin V (legal_of_strip hinv.nodup hsV))) hJ
theorem actualSource_terminal_small_ownership_transition
    (k t : ℕ) (hk : 3 ≤ k) (p z : Fin k)
    (F E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (F ++ [z] ++ E))
    (hpunused : p ∉ F ++ [z] ++ E)
    (hnunused : hit k 1 p ∉ F ++ [z] ++ E)
    (hsmall : ∀ i ∈ E, |s k t i| < Q k)
    (hz : Q k ≤ -s k t z)
    (hmin : ∀ V : List (Fin k), Legal k t V →
      J k t (F ++ [z] ++ E) ≤ J k t V) :
    let f := s k t
    let W := F ++ [z] ++ E
    let n := hit k 1 p
    let P := f p
    let D := |f n|
    let B := C k - P
    let d := P - D
    let u := mass f F
    let q := fun m : ℕ => mass f (F ++ [z] ++ E.take m)
    C k - d < u ∧
    (∀ m : ℕ, B < q m ∧ q m < D) ∧
    (∀ i : Fin k, |f i| < Q k → 0 ≤ f i → i ∈ W) ∧
    (∀ i : Fin k, i ∉ W → |f i| < Q k →
      let σ := -f i
      0 < σ ∧
      (∀ m : ℕ, q m < σ) ∧
      u - D < σ ∧
      f (hit k 1 i) = -(2 * σ) ∧
      Q k ≤ -f (hit k 1 i) ∧
      (hit k 1 i ∈ W ∨
        (u < 2 * σ ∧ hit k 2 i ∈ W ∧
          0 < f (hit k 2 i) ∧
          f (hit k 2 i) ≤ 2 * d - 3 ∧
          f (hit k 2 i) < Q k))) := by
  classical
  dsimp only
  let f := s k t
  let W := F ++ [z] ++ E
  let n := hit k 1 p
  let P := f p
  let D := |f n|
  let B := C k - P
  let d := P - D
  let u := mass f F
  let q := fun m : ℕ => mass f (F ++ [z] ++ E.take m)
  obtain ⟨hu, hq, hown⟩ := actualSource_terminal_small_ownership_prefix
    k t hk p z F E hpositive hnlarge hexpand hW hpunused hnunused hsmall hz hmin
  change C k - d < u at hu
  change (∀ m : ℕ, B < q m ∧ q m < D) at hq
  change (∀ i : Fin k, |f i| < Q k → 0 ≤ f i → i ∈ W) at hown
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change (∀ i ∈ E, |f i| < Q k) at hsmall
  change Q k ≤ -f z at hz
  change (∀ V, Legal k t V → J k t W ≤ J k t V) at hmin
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hD : Q k ≤ D := hnlarge
  have hDP : D < P := by
    simpa only [f, n, D, P, abs_of_pos hpositive] using geo.strictOrder.1
  have hbudget : 2 * P ≤ C k + Q k := by
    simpa [P, f, abs_of_pos hpositive] using geo.budget
  have hDrel : D = 2 * B + 1 := by
    have hh := geo.firstEquation
    change D = N k - 2 * |f p| at hh
    have hpabs : |f p| = P := abs_of_pos hpositive
    rw [hpabs, hN] at hh
    dsimp [B]
    rw [hC]
    omega
  have hdefs : P = D + d ∧ C k = D + B + d := by
    constructor <;> dsimp [d, B] <;> ring
  have hdpos : 0 < d := by dsimp [d]; omega
  have hBd : d ≤ B := by omega
  have hdQ : 2 * d ≤ Q k - 1 := by omega
  have hpL : Large k t p := geo.pLarge
  have hnL : Large k t n := geo.nLarge
  have hzL : Large k t z := by
    change Q k ≤ |f z|
    rw [abs_of_neg (by omega : f z < 0)]
    exact hz
  have hE0 : largeUsed k t E = 0 := (small_weights t E hsmall).1
  have hR1 : largeUsed k t ([z] ++ E) = 1 := by
    simp [largeUsed_append, largeUsed_cons, hE0, largeWeight, hzL]
  have hsF : InStrip f (C k) 0 F :=
    (strip_split F ([z] ++ E) (by simpa [W, List.append_assoc] using
      (strip_of_legal hW))).1
  have huBounds : 0 ≤ u ∧ u ≤ C k := by
    simpa [u, mass] using inStrip_prefix hsF F.length
  have hqend : q E.length = mass f W := by simp [q, W]
  have hend : B < mass f W ∧ mass f W < D := by simpa [hqend] using hq E.length
  have hend0 : 0 ≤ mass f W := by
    simpa [mass] using (inStrip_prefix (strip_of_legal hW) W.length).1
  have hnp : n ≠ p := by
    intro he
    have he' := congrArg f he
    change f n = P at he'
    omega
  have hstrict (V : List (Fin k)) (hV : Legal k t V)
      (hG : G k t V < G k t W) : False := by
    have hJ : J k t V < J k t W :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hG)
    exact (not_lt_of_ge (hmin V hV)) hJ
  refine ⟨hu, hq, hown, ?_⟩
  intro i hi his
  let σ := -f i
  change 0 < σ ∧ (∀ m : ℕ, q m < σ) ∧ u - D < σ ∧
    f (hit k 1 i) = -(2 * σ) ∧ Q k ≤ -f (hit k 1 i) ∧
    (hit k 1 i ∈ W ∨ (u < 2 * σ ∧ hit k 2 i ∈ W ∧
      0 < f (hit k 2 i) ∧ f (hit k 2 i) ≤ 2 * d - 3 ∧ f (hit k 2 i) < Q k))
  have hineg : f i < 0 := lt_of_not_ge (fun h => hi (hown i his h))
  have hival : f i = -σ := by dsimp [σ]; omega
  have hspos : 0 < σ := by dsimp [σ]; omega
  have hsQ : σ < Q k := by
    have his' : |f i| < Q k := his
    rw [abs_of_neg hineg] at his'
    exact his'
  have hiSmall : ¬ Large k t i := not_le_of_gt his
  have hip : i ≠ p := by
    intro he
    exact hiSmall (he.symm ▸ hpL)
  have hin : i ≠ n := by
    intro he
    exact hiSmall (he.symm ▸ hnL)
  have hsEnd : mass f W < σ := by
    by_contra hnot
    have hle : σ ≤ mass f W := le_of_not_gt hnot
    have hsWi : InStrip f (C k) 0 (W ++ [i]) := by
      have hsW : InStrip f (C k) 0 W := strip_of_legal hW
      apply inStrip_append hsW
      simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, zero_add]
      change 0 ≤ mass f W ∧ mass f W ≤ C k ∧
        0 ≤ mass f W + f i ∧ mass f W + f i ≤ C k
      rw [hival]
      exact ⟨hend0, by omega, by omega, by omega⟩
    have hnod : (W ++ [i]).Nodup := hW.1.append (by simp)
      (List.disjoint_left.mpr (by
        intro x hx hxi
        have : x = i := by simpa using hxi
        subst x
        exact hi hx))
    obtain ⟨hG, hH, hU⟩ := small_append_balances k t W hW.1 i hi hiSmall
    have hJ : J k t (W ++ [i]) < J k t W := by
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hH, by omega⟩)⟩
    exact (not_lt_of_ge (hmin _ (legal_of_strip hnod hsWi))) hJ
  have hsB : B < σ := by omega
  have hsq (m : ℕ) : q m < σ := by
    by_contra hnot
    have hle : σ ≤ q m := le_of_not_gt hnot
    let K := F ++ [z] ++ E.take m
    let R := E.drop m
    have hsplit : K ++ R = W := by simp [K, R, W, List.append_assoc]
    have hsK : InStrip f (C k) 0 K :=
      (strip_split K R (by simpa [hsplit] using (strip_of_legal hW))).1
    have hKmass : mass f K = q m := rfl
    have hqm := hq m
    have hsV : InStrip f (C k) 0 (K ++ [i, p]) := by
      apply inStrip_append hsK
      simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, zero_add]
      change 0 ≤ mass f K ∧ mass f K ≤ C k ∧
        0 ≤ mass f K + f i ∧ mass f K + f i ≤ C k ∧
        0 ≤ mass f K + f i + f p ∧ mass f K + f i + f p ≤ C k
      rw [hKmass, hival]
      change 0 ≤ q m ∧ q m ≤ C k ∧ 0 ≤ q m - σ ∧ q m - σ ≤ C k ∧
        0 ≤ q m - σ + P ∧ q m - σ + P ≤ C k
      omega
    have hS : ([i, p] : List (Fin k)).Nodup := by simp [hip]
    have hfresh : ∀ x ∈ ([i, p] : List (Fin k)), x ∉ K ++ R := by
      intro x hx
      rw [hsplit]
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hpunused
    obtain ⟨hVnod, hbal⟩ := fresh_cut k t K R [i, p]
      (by simpa [hsplit] using hW.1) hS hfresh
    have hS1 : largeUsed k t [i, p] = 1 := by
      simp [largeUsed, mass, largeWeight, hiSmall, hpL]
    have hR0 : largeUsed k t R = 0 :=
      (small_weights t R (fun x hx => hsmall x (List.mem_of_mem_drop hx))).1
    rw [hsplit, hS1, hR0] at hbal
    exact hstrict _ (legal_of_strip hVnod hsV) (by omega)
  have hsuD : u - D < σ := by
    by_contra hnot
    have hle : σ ≤ u - D := le_of_not_gt hnot
    have hsV : InStrip f (C k) 0 (F ++ [n, i, p]) := by
      apply inStrip_append hsF
      simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, zero_add]
      rw [hnval, hival]
      change 0 ≤ u ∧ u ≤ C k ∧ 0 ≤ u - D ∧ u - D ≤ C k ∧
        0 ≤ u - D - σ ∧ u - D - σ ≤ C k ∧
        0 ≤ u - D - σ + P ∧ u - D - σ + P ≤ C k
      omega
    have hS : ([n, i, p] : List (Fin k)).Nodup := by
      simp [hnp, hin.symm, hip]
    have hfresh : ∀ x ∈ ([n, i, p] : List (Fin k)), x ∉ F ++ ([z] ++ E) := by
      intro x hx
      have hsplit : F ++ ([z] ++ E) = W := by simp [W, List.append_assoc]
      rw [hsplit]
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hnunused
      · exact hi
      · exact hpunused
    obtain ⟨hVnod, hbal⟩ := fresh_cut k t F ([z] ++ E) [n, i, p]
      (by simpa [W, List.append_assoc] using hW.1) hS hfresh
    have hS2 : largeUsed k t [n, i, p] = 2 := by
      simp [largeUsed, mass, largeWeight, hnL, hiSmall, hpL]
    rw [hS2, hR1] at hbal
    have hsplit : F ++ ([z] ++ E) = W := by simp [W, List.append_assoc]
    rw [hsplit] at hbal
    exact hstrict _ (legal_of_strip hVnod hsV) (by omega)
  have hstep (m : ℕ) : f (hit k (m + 1) i) =
      doubleStep (N k) (f (hit k m i)) := by
    have hh := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2 (hit k m i)
    change 2 * f (hit k m i) - f (finRotate k (hit k m i)) = N k *
      (if N k < 4 * f (hit k m i) then 1 else
        if 4 * f (hit k m i) < -N k then -1 else 0) at hh
    have hnext : hit k (m + 1) i = finRotate k (hit k m i) := by
      simp only [hit, Function.iterate_succ_apply']
    rw [← hnext] at hh
    unfold doubleStep
    split_ifs at * <;> omega
  have hjval : f (hit k 1 i) = -(2 * σ) := by
    have hh := hstep 0
    change f (hit k 1 i) = doubleStep (N k) (f i) at hh
    rw [hival] at hh
    rw [doubleStep, if_neg (by omega), if_neg (by omega)] at hh
    omega
  have hjL : Q k ≤ -f (hit k 1 i) := by rw [hjval]; omega
  refine ⟨hspos, hsq, hsuD, hjval, hjL, ?_⟩
  by_cases hjUsed : hit k 1 i ∈ W
  · exact Or.inl hjUsed
  · right
    let j := hit k 1 i
    have hjfresh : j ∉ W := hjUsed
    have hjlarge : Large k t j := by
      change Q k ≤ |f (hit k 1 i)|
      rw [hjval, abs_of_neg (by omega : -(2 * σ) < 0)]
      omega
    have hjp : j ≠ p := by
      intro he
      have he' := congrArg f he
      change f (hit k 1 i) = P at he'
      rw [hjval] at he'
      have hp0 : 0 < P := hpositive
      omega
    have hu2s : u < 2 * σ := by
      by_contra hnot
      have hle : 2 * σ ≤ u := le_of_not_gt hnot
      have hjs : f j = -(2 * σ) := hjval
      have hsV : InStrip f (C k) 0 (F ++ [j, p]) := by
        apply inStrip_append hsF
        simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, zero_add]
        rw [hjs]
        change 0 ≤ u ∧ u ≤ C k ∧ 0 ≤ u - 2 * σ ∧ u - 2 * σ ≤ C k ∧
          0 ≤ u - 2 * σ + P ∧ u - 2 * σ + P ≤ C k
        omega
      have hS : ([j, p] : List (Fin k)).Nodup := by simp [hjp]
      have hfresh : ∀ x ∈ ([j, p] : List (Fin k)), x ∉ F ++ ([z] ++ E) := by
        intro x hx
        have hsplit : F ++ ([z] ++ E) = W := by simp [W, List.append_assoc]
        rw [hsplit]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hjfresh
        · exact hpunused
      obtain ⟨hVnod, hbal⟩ := fresh_cut k t F ([z] ++ E) [j, p]
        (by simpa [W, List.append_assoc] using hW.1) hS hfresh
      have hS2 : largeUsed k t [j, p] = 2 := by
        simp [largeUsed, mass, largeWeight, hjlarge, hpL]
      rw [hS2, hR1] at hbal
      have hsplit : F ++ ([z] ++ E) = W := by simp [W, List.append_assoc]
      rw [hsplit] at hbal
      exact hstrict _ (legal_of_strip hVnod hsV) (by omega)
    have hlambda : f (hit k 2 i) = N k - 4 * σ := by
      have hh := hstep 1
      change f (hit k 2 i) = doubleStep (N k) (f (hit k 1 i)) at hh
      rw [hjval, doubleStep, if_neg (by omega), if_pos (by omega)] at hh
      omega
    have hlpos : 0 < f (hit k 2 i) := by rw [hlambda]; omega
    have hlbound : f (hit k 2 i) ≤ 2 * d - 3 := by rw [hlambda]; omega
    have hlQ : f (hit k 2 i) < Q k := by omega
    have hlused : hit k 2 i ∈ W := hown _
      (by rwa [abs_of_pos hlpos]) (le_of_lt hlpos)
    exact ⟨hu2s, hlused, hlpos, hlbound, hlQ⟩

end D5.S3.Combinatorics.Circle.TerminalSmallOwnership
