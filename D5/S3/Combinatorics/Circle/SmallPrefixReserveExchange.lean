/- GID: D5/S3/Combinatorics/Circle/SmallPrefixReserveExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SmallPrefixReserveExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Pull an actual negative SMALL prefix reserve through a compatible suffix, retaining its LARGE labels, and construct a full strict-energy physical exchange. -/
module
public import D5.S3.Combinatorics.Circle.SignedShortLargeExchange

/-! An actual prefix reserve enlarges the signed-short resource. The entire
suffix after that reserve is reordered, including any earlier LARGE labels.
No global minimum, source injectivity, parent placement or translated old
order is assumed. This source draft has not been compiled. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.SmallPrefixReserveExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange SignedShortLargeExchange
open scoped BigOperators

-- Only additive list arithmetic is normalized here; native source geometry
-- is consumed through native_geometry, not reconstructed.
local macro "list_mass" : tactic =>
  `(tactic| simp only [mass, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add])

/-- The changed baseline: delete a physical negative reserve and order ALL
of the suffix between its actual old starting height and the new endpoint.
There is no assertion that the old suffix order survives translation. -/
private theorem pull_prefix_reserve {α : Type*}
    (f : α → ℤ) (cap m : ℤ) (Aminus : List α) (c : α) (K : List α)
    (hc : f c = -m)
    (hs : InStrip f cap 0 (Aminus ++ [c] ++ K))
    (hend : 0 ≤ mass f (Aminus ++ [c] ++ K) + m ∧
      mass f (Aminus ++ [c] ++ K) + m ≤ cap)
    (hcompatible : ∀ i ∈ K, ∀ j ∈ K,
      0 < f i → f j < 0 → f i - f j ≤ cap) :
    ∃ Kstar : List α, Kstar.Perm K ∧
      InStrip f cap 0 (Aminus ++ Kstar) ∧
      mass f (Aminus ++ Kstar) = mass f (Aminus ++ [c] ++ K) + m ∧
      ((Aminus ++ Kstar) ++ [c]).Perm (Aminus ++ [c] ++ K) := by
  classical
  have hsMinus := (strip_split Aminus ([c] ++ K)
    (by simpa only [List.append_assoc] using hs)).1
  have hstart : 0 ≤ mass f Aminus ∧ mass f Aminus ≤ cap := by
    simpa only [mass, List.take_length, zero_add] using
      inStrip_prefix hsMinus Aminus.length
  have heq : mass f Aminus + mass f K =
      mass f (Aminus ++ [c] ++ K) + m := by
    list_mass
    rw [hc]
    ring
  obtain ⟨Kstar, hKstar, hsKstar⟩ := exists_order_between f K cap
    (mass f Aminus) hstart (by
      change 0 ≤ mass f Aminus + mass f K ∧ mass f Aminus + mass f K ≤ cap
      rw [heq]
      exact hend) hcompatible
  have hmass : mass f Kstar = mass f K := by
    simpa only [mass] using (hKstar.map f).sum_eq
  refine ⟨Kstar, hKstar, ?_, ?_, ?_⟩
  · exact inStrip_append hsMinus (by simpa only [mass, zero_add] using hsKstar)
  · calc
      _ = mass f Aminus + mass f Kstar := by
        simp only [mass, List.map_append, List.sum_append]
      _ = mass f Aminus + mass f K := by rw [hmass]
      _ = _ := heq
  · apply List.perm_iff_count.mpr
    intro i
    have hh := hKstar.count_eq i
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega

set_option maxHeartbeats 1400000 in
/-- Full original-word physical exchange from an actual negative SMALL
reserve in the arbitrary prefix. COMP concerns the whole physical K, which
can contain LARGE labels. GATE is the explicit final p-gate; every other
gate, return supply, order, partition and objective identity is derived. -/
theorem actualSource_threeLarge_smallPrefixReserve_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z c : Fin k)
    (A Aminus K T0 T1 T2 E : List (Fin k)) (m : ℤ)
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (hA : A = Aminus ++ [c] ++ K)
    (hc : s k t c = -m)
    (hm : 1 ≤ m)
    (hresource : s k t q - Q k - 1 ≤ m)
    (hmB : m < C k - s k t p)
    (hgate : mass (s k t) A + m ≤ C k - s k t p)
    (hcompatible : ∀ i ∈ K, ∀ j ∈ K,
      0 < s k t i → s k t j < 0 → s k t i - s k t j ≤ C k) :
    let f := s k t
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let F := [c] ++ smallWord T0 T1 T2 E
    let bstar := mass f A + m + f p - |f n|
    let e0 := bstar + mass f F + f z + f q
    ∃ Kstar R Ksmall Lsmall : List (Fin k),
      Kstar.Perm K ∧
      (let Astar := Aminus ++ Kstar
       InStrip f (C k) 0 Astar ∧
       (Astar ++ [c]).Perm A ∧ mass f Astar = mass f A + m ∧
       InStrip f (C k) 0 (Astar ++ [p,n]) ∧
       0 ≤ bstar ∧ bstar ≤ C k - |f n| ∧
       F.Nodup ∧ (∀ i ∈ F, |f i| < Q k) ∧
       R.Subperm F ∧ (R ++ Ksmall).Perm F ∧ Lsmall.Perm Ksmall ∧
       (∀ i ∈ R, |f i| < Q k) ∧
       e0 = prospective k t p q y zpen W ∧ f q < e0 ∧
       (let V := Astar ++ [p,n] ++ Lsmall ++ [z,q]
        let Ret := [x,y,zpen] ++ R
        let e := e0 - mass f R
        Legal k t V ∧ V.Nodup ∧ InStrip f (C k) 0 V ∧
        (∀ j : ℕ, 0 ≤ mass f (V.take j) ∧ mass f (V.take j) ≤ C k) ∧
        (V ++ Ret).Perm (W ++ [p,n,q]) ∧
        Inventory k t W V [p,n,q] Ret ∧
        Ret.Nodup ∧ (∀ i ∈ Ret, i ∉ V) ∧
        remainingSmall t V = remainingSmall t W ∪ R.toFinset ∧
        Disjoint (remainingSmall t W) R.toFinset ∧
        (∀ i ∈ A, Large k t i → i ∈ V) ∧
        G k t V = G k t W ∧ U V = U W + R.length ∧
        H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs +
            3 ^ (f zpen).natAbs =
          H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs ∧
        H k t V < H k t W ∧ J k t V < J k t W ∧
        mass f V = e ∧ f q ≤ e ∧ e ≤ C k ∧ remainingMass f V = -e)) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let S := smallWord T0 T1 T2 E
  let F := [c] ++ S
  let P := f p
  let D := |f n|
  let r := |f x|
  let a0 := mass f A
  let bstar := a0 + m + P - D
  let e0 := bstar + mass f F + f z + f q
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change q ∉ W at hqunused
  change f c = -m at hc
  change f q < P at hqsmaller
  change f q - Q k - 1 ≤ m at hresource
  change m < C k - P at hmB
  change a0 + m ≤ C k - P at hgate
  change Q k ≤ -f y at hylarge
  change Q k ≤ -f zpen at hzpenlarge
  change Q k ≤ -f z at hzlarge
  change -f z ≤ f q at hzupper
  change Q k ≤ f q at hqlarge
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, _, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = r := by
    simpa [f, x, r, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : D < P := by
    simpa only [f, n, D, P, abs_of_pos hpositive] using geo.strictOrder.1
  have hPr : P < r := by
    simpa only [f, x, r, P, abs_of_pos hpositive] using geo.strictOrder.2
  have hreq : r = 2 * P - D := by
    have h1 := geo.firstEquation
    have h2 := geo.secondEquation
    change D = N k - 2 * |f p| at h1
    change r = 4 * |f p| - N k at h2
    rw [hpabs] at h1 h2
    omega
  have hD : Q k ≤ D := hnlarge
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hNodd _)
  have hPcap : P ≤ C k := by simpa only [hpabs] using hbound p
  have hqpos : 0 < f q := by omega
  have hqcap : f q ≤ C k := le_trans (le_abs_self _) (hbound q)
  have hcsmall : |f c| < Q k := by
    rw [hc, abs_of_neg (by omega : -m < 0), neg_neg]
    omega
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsA : InStrip f (C k) 0 A :=
    (strip_split A ([x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [W, oldWord, x, List.append_assoc] using hsW)).1
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa only [a0, mass, List.take_length, zero_add] using inStrip_prefix hsA A.length
  obtain ⟨Kstar, hKstar, hsAstar, hmAstar, hAstar⟩ :=
    pull_prefix_reserve f (C k) m Aminus c K hc (hA ▸ hsA)
      (by rw [← hA]; change 0 ≤ a0 + m ∧ a0 + m ≤ C k; omega) hcompatible
  let Astar := Aminus ++ Kstar
  change InStrip f (C k) 0 Astar at hsAstar
  rw [← hA] at hmAstar hAstar
  change mass f Astar = a0 + m at hmAstar
  have hbstar : 0 ≤ bstar ∧ bstar ≤ C k - D := by
    dsimp only [bstar]
    omega
  have hsPN : InStrip f (C k) (a0 + m) [p,n] := by
    change 0 ≤ a0 + m ∧ a0 + m ≤ C k ∧
      0 ≤ a0 + m + f p ∧ a0 + m + f p ≤ C k ∧
      0 ≤ a0 + m + f p + f n ∧ a0 + m + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 + m ∧ a0 + m ≤ C k ∧
      0 ≤ a0 + m + P ∧ a0 + m + P ≤ C k ∧
      0 ≤ a0 + m + P + -D ∧ a0 + m + P + -D ≤ C k
    dsimp only [bstar] at hbstar
    omega
  have hsApn : InStrip f (C k) 0 (Astar ++ [p,n]) :=
    inStrip_append hsAstar (by
      change InStrip f (C k) (0 + mass f Astar) [p,n]
      rw [zero_add, hmAstar]
      exact hsPN)
  have hmApn : mass f (Astar ++ [p,n]) = bstar := by
    calc
      _ = mass f Astar + (f p + f n) := by
        simp only [mass, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      _ = bstar := by
        rw [hmAstar, hnval]
        change a0 + m + (P + -D) = a0 + m + P - D
        ring
  -- Physical c occurs before every entry of S; remove only the other
  -- occurrences, never identify labels through equal numerical values.
  have hFW : F.Sublist W := by
    simpa only [F, S, smallWord, W, oldWord, x, hA, List.nil_append, List.append_nil,
      List.append_assoc] using
      ((((((((((List.nil_sublist Aminus).append (List.Sublist.refl [c])).append
        (List.nil_sublist K)).append (List.nil_sublist [x])).append
        (List.Sublist.refl T0)).append (List.nil_sublist [y])).append
        (List.Sublist.refl T1)).append (List.nil_sublist [zpen])).append
        (List.Sublist.refl T2)).append (List.nil_sublist [z])).append
        (List.Sublist.refl E)
  have hF : F.Nodup := hW.1.sublist hFW
  have hFsmall (i : Fin k) (hi : i ∈ F) : |f i| < Q k := by
    rcases List.mem_append.mp hi with hi | hi
    · have he : i = c := by simpa only [List.mem_singleton] using hi
      subst i
      exact hcsmall
    · exact hsmall i hi
  have hh : 0 ≤ mass f W := by
    simpa only [mass, List.take_length, zero_add] using (inStrip_prefix hsW W.length).1
  have hmF : mass f F = -m + mass f S := by
    simp only [F, mass, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc]
  have hmW : mass f W = a0 + r + mass f S + f y + f zpen + f z := by
    dsimp only [W, oldWord, a0, S, smallWord]
    list_mass
    change f (hit k 2 p) = r at hxval
    rw [hxval]
    ring
  have he0 : e0 = prospective k t p q y zpen W := by
    change bstar + mass f F + f z + f q =
      mass f W - f y - f zpen + f q - P
    rw [hmF, hmW, hreq]
    dsimp only [bstar]
    ring
  have he0lo : f q < e0 := by
    rw [he0]
    change f q < mass f W - f y - f zpen + f q - P
    omega
  have hsupply : e0 - C k ≤ mass f (positive t F) := by
    have hdom := positive_mass_dominates f F
    change mass f F ≤ mass f (positive t F) at hdom
    dsimp only [e0]
    omega
  obtain ⟨R, Ksmall, hpart, hRlo, hRhi⟩ : ∃ R Ksmall : List (Fin k),
      (R ++ Ksmall).Perm F ∧ e0 - C k ≤ mass f R ∧ mass f R ≤ e0 - f q := by
    by_cases hlow : e0 ≤ C k
    · refine ⟨[], F, by simp, ?_, ?_⟩ <;>
        simp only [mass, List.map_nil, List.sum_nil] <;> omega
    · have hN0 : [c].Subperm (F.filter
          (fun i => decide (0 < -f i ∧ -f i ≤ C k - f q + 1))) := by
        apply List.Sublist.subperm
        apply List.singleton_sublist.mpr
        simp only [List.mem_filter, decide_eq_true_eq]
        refine ⟨by simp [F], ?_, ?_⟩ <;> rw [hc] <;> omega
      obtain ⟨R, Ksmall, hpart, hlo, hhi⟩ := signed_short_reserve_select
        f F [] [c] (C k - f q) (Q k - 1) (e0 - C k) hF (by omega) (by omega)
        List.nil_subperm hN0
        (by intro i hi hip; have his := hFsmall i hi; rw [abs_of_pos hip] at his; omega)
        (by omega) hsupply
        (by
          simp only [mass, List.map_nil, List.map_cons, List.sum_nil,
            List.sum_cons, add_zero, zero_add, hc, neg_neg]
          omega)
      exact ⟨R, Ksmall, hpart, hlo, by omega⟩
  have hRsub : R.Subperm F :=
    (show R.Subperm (R ++ Ksmall) from by
      simpa using (List.Subperm.append (List.Subperm.refl R)
        (List.nil_subperm : ([] : List (Fin k)).Subperm Ksmall))).trans hpart.subperm
  have hRsmall (i : Fin k) (hi : i ∈ R) : |f i| < Q k :=
    hFsmall i (hRsub.subset hi)
  have hKsmall (i : Fin k) (hi : i ∈ Ksmall) : |f i| < Q k :=
    hFsmall i (hpart.mem_iff.mp (List.mem_append_right R hi))
  have hmasspart : mass f R + mass f Ksmall = mass f F := by
    simpa only [mass, List.map_append, List.sum_append] using (hpart.map f).sum_eq
  let e := e0 - mass f R
  let eta := e - f q
  let endSmall := eta - f z
  have he : f q ≤ e ∧ e ≤ C k := by dsimp only [e]; omega
  have heta : 0 ≤ eta ∧ eta ≤ C k := by dsimp only [eta]; omega
  have hendSmall : 0 ≤ endSmall ∧ endSmall ≤ C k := by
    dsimp only [endSmall, eta]
    omega
  have hsum : bstar + mass f Ksmall = endSmall := by
    dsimp only [endSmall, eta, e, e0]
    omega
  obtain ⟨Lsmall, hLsmall, hsLsmall⟩ := exists_order_between f Ksmall (C k) bstar
    ⟨hbstar.1, by omega⟩
    (by change 0 ≤ bstar + mass f Ksmall ∧ bstar + mass f Ksmall ≤ C k
        rw [hsum]; exact hendSmall)
    (by
      intro i hi j hj hip hjn
      have hiS := hKsmall i hi
      have hjS := hKsmall j hj
      rw [abs_of_pos hip] at hiS
      rw [abs_of_neg hjn] at hjS
      omega)
  have hmLsmall : mass f Lsmall = mass f Ksmall := by
    simpa only [mass] using (hLsmall.map f).sum_eq
  have hsApnL : InStrip f (C k) 0 (Astar ++ [p,n] ++ Lsmall) :=
    inStrip_append hsApn (by
      change InStrip f (C k) (0 + mass f (Astar ++ [p,n])) Lsmall
      rw [zero_add, hmApn]
      exact hsLsmall)
  have hmApnL : mass f (Astar ++ [p,n] ++ Lsmall) = endSmall := by
    calc
      _ = mass f (Astar ++ [p,n]) + mass f Lsmall := by
        simp only [mass, List.map_append, List.sum_append]
      _ = endSmall := by rw [hmApn, hmLsmall]; exact hsum
  have hsZQ : InStrip f (C k) endSmall [z,q] := by
    change 0 ≤ endSmall ∧ endSmall ≤ C k ∧
      0 ≤ endSmall + f z ∧ endSmall + f z ≤ C k ∧
      0 ≤ endSmall + f z + f q ∧ endSmall + f z + f q ≤ C k
    have hcz : endSmall + f z = eta := by dsimp only [endSmall]; ring
    have hczq : endSmall + f z + f q = e := by
      rw [hcz]
      dsimp only [eta]
      ring
    rw [hczq, hcz]
    exact ⟨hendSmall.1, hendSmall.2, heta.1, heta.2, by omega, he.2⟩
  let V := Astar ++ [p,n] ++ Lsmall ++ [z,q]
  let Ret := [x,y,zpen] ++ R
  have hsV : InStrip f (C k) 0 V :=
    inStrip_append hsApnL (by
      change InStrip f (C k) (0 + mass f (Astar ++ [p,n] ++ Lsmall)) [z,q]
      rw [zero_add, hmApnL]
      exact hsZQ)
  -- One permutation relative to the ORIGINAL W is the only input to the
  -- existing physical Inventory kernel. No second reconstruction engine.
  have hperm : (V ++ Ret).Perm (W ++ [p,n,q]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hAC := hAstar.count_eq i
    have hFC := hpart.count_eq i
    have hLC := hLsmall.count_eq i
    simp only [F, S, smallWord, List.count_append, List.count_cons, List.count_nil] at hFC
    simp only [List.count_append, List.count_cons, List.count_nil] at hAC
    simp only [V, Ret, W, oldWord, x, Astar, List.count_append, List.count_cons, List.count_nil]
    omega
  have hpn : p ≠ n := by
    intro h
    have hv : P = -D := (congrArg f h).trans hnval
    omega
  have hpq : p ≠ q := by
    intro h
    have hv : P = f q := congrArg f h
    omega
  have hnq : n ≠ q := by
    intro h
    have hv : -D = f q := hnval.symm.trans (congrArg f h)
    omega
  have hI : [p,n,q].Nodup := by simp [hpn, hpq, hnq]
  have hIW (i : Fin k) (hi : i ∈ [p,n,q]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpunused
    · exact hnunused
    · exact hqunused
  have hqL : Large k t q := by
    change Q k ≤ |f q|
    rw [abs_of_pos hqpos]
    exact hqlarge
  have hIL (i : Fin k) (hi : i ∈ [p,n,q]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
    · exact hqL
  have hRold (i : Fin k) (hi : i ∈ Ret) : i ∈ W := by
    simp only [Ret, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | rfl) | hi
    · simp [W, oldWord, x]
    · simp [W, oldWord]
    · simp [W, oldWord]
    · exact hFW.subset (hRsub.subset hi)
  have inv := inventory_of_perm hk t W V [p,n,q] Ret hW.1 hI hIW hRold hIL hperm
  have hWI : (W ++ [p,n,q]).Nodup := hW.1.append hI (List.disjoint_left.mpr
    (by intro i hiW hiI; exact hIW i hiI hiW))
  have hVR := List.nodup_append'.mp (hperm.nodup_iff.mpr hWI)
  have hRetAbs (i : Fin k) (hi : i ∈ Ret) : i ∉ V := by
    intro hiV
    exact List.disjoint_left.mp hVR.2.2 hiV hi
  have hyL : Large k t y := le_trans hylarge (neg_le_abs _)
  have hzpL : Large k t zpen := le_trans hzpenlarge (neg_le_abs _)
  have hxL : Large k t x := geo.xLarge
  have hRweights := small_weights t R hRsmall
  have hRetG : largeUsed k t Ret = 3 := by
    simp [Ret, largeWeight, hxL, hyL, hzpL, hRweights.1]
  have hIG : largeUsed k t [p,n,q] = 3 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge, hqL]
  have hRetH : H k t Ret = 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs := by
    simp [Ret, energyWeight, hxL, hyL, hzpL, hRweights.2, f, s, Nat.add_assoc]
  have hIH : H k t [p,n,q] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    simp [H, mass, energyWeight, geo.pLarge, show Large k t n from geo.nLarge,
      hqL, f, s, Nat.add_assoc]
  have hG : G k t V = G k t W := by
    have ht := inv.largeBalance
    rw [hRetG, hIG] at ht
    omega
  have hU : U V = U W + R.length := by
    have ht := inv.countBalance
    simp only [Ret, List.length_append, List.length_cons, List.length_nil] at ht
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    have ht := inv.energyBalance
    rw [hRetH, hIH] at ht
    omega
  have hDn : (f n).natAbs < (f p).natAbs := by
    exact_mod_cast (show ((f n).natAbs : ℤ) < ((f p).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using geo.strictOrder.1)
  have hQn : (f q).natAbs < (f p).natAbs := by
    exact_mod_cast (show ((f q).natAbs : ℤ) < ((f p).natAbs : ℤ) by
      simp only [Int.natCast_natAbs]
      rw [abs_of_pos hqpos, abs_of_pos hpositive]
      exact hqsmaller)
  have hXn : (f p).natAbs < (f x).natAbs := by
    exact_mod_cast (show ((f p).natAbs : ℤ) < ((f x).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using geo.strictOrder.2)
  -- The existing two-edge energy alone does not include the third inserted
  -- label. Its strict exponent order supplies this short three-term bound.
  have hEnergy : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs <
      (3 : ℕ) ^ (f x).natAbs := by
    have hd := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hDn
    have hq := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hQn
    have ht : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs <
        (3 : ℕ) ^ ((f p).natAbs + 1) := by rw [pow_succ]; omega
    exact ht.trans_le (pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) (by omega))
  have hHstrict : H k t V < H k t W := by
    have hle : H k t V + 3 ^ (f x).natAbs ≤ H k t W +
        (3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs) := by
      calc
        H k t V + 3 ^ (f x).natAbs ≤
            H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs :=
          (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
        _ = _ := by simpa only [Nat.add_assoc] using hH
    exact (Nat.add_lt_add_iff_right).mp
      (hle.trans_lt (Nat.add_lt_add_left hEnergy (H k t W)))
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHstrict)⟩
  have hfilter : Ret.toFinset.filter (fun i => ¬ Large k t i) = R.toFinset := by
    ext i
    have hiR : i ∈ R → ¬ Large k t i := fun hi => not_le.mpr (hRsmall i hi)
    simp only [Ret, Finset.mem_filter, List.mem_toFinset, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨(rfl | rfl | rfl) | hi, hn⟩
      · exact False.elim (hn hxL)
      · exact False.elim (hn hyL)
      · exact False.elim (hn hzpL)
      · exact hi
    · intro hi
      exact ⟨Or.inr hi, hiR hi⟩
  have hretain (i : Fin k) (hi : i ∈ A) (hiL : Large k t i) : i ∈ V := by
    have hiAstar : i ∈ Astar := by
      have hi' := hAstar.mem_iff.mpr hi
      rcases List.mem_append.mp hi' with hi' | hi'
      · exact hi'
      · have he : i = c := by simpa only [List.mem_singleton] using hi'
        subst i
        exact False.elim ((not_lt_of_ge hiL) hcsmall)
    simp [V, hiAstar]
  have hEnd : mass f V = e := by
    calc
      _ = mass f (Astar ++ [p,n] ++ Lsmall) + mass f [z,q] := by
        simp only [V, mass, List.map_append, List.sum_append]
      _ = e := by rw [hmApnL]; dsimp only [endSmall, eta]; list_mass; ring
  refine ⟨Kstar, R, Ksmall, Lsmall, hKstar, hsAstar, hAstar, hmAstar, hsApn,
    hbstar.1, hbstar.2, hF, hFsmall, hRsub, hpart, hLsmall, hRsmall, he0, he0lo,
    legal_of_strip inv.nodup hsV, inv.nodup, hsV, ?_, hperm, inv, hVR.2.1,
    hRetAbs, ?_, ?_, hretain, hG, hU, hH, hHstrict, hJ, hEnd, he.1, he.2, ?_⟩
  · intro j
    simpa only [mass, f, zero_add] using inStrip_prefix hsV j
  · simpa only [hfilter] using inv.smallPartition
  · simpa only [hfilter] using inv.smallDisjoint
  · rw [inv.complementSum, hEnd]

end D5.S3.Combinatorics.Circle.SmallPrefixReserveExchange
