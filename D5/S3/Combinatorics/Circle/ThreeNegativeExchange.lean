/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Full native three-negative physical exchange with arbitrary signed prefix. -/
module
public import D5.S3.Combinatorics.Circle.TerminalSmallOwnership
import all D5.S3.Combinatorics.Circle.OddFirstNegativePlacement

/-! Full three-negative exchange on physical labels, without an extra SMALL
resource or a minimum assumption in the conclusion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.ThreeNegativeExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open ThreeLargePacketExchange FirstNegativeShiftExchange TerminalSmallOwnership
open scoped BigOperators

/-- Select actual positive occurrences, using one sufficiently large entry or
an owned first-crossing scan of strictly shorter entries. -/
private theorem positive_selection {α : Type*} (f : α → ℤ) (T : List α)
    (ell : ℤ) (hell : 0 < ell)
    (hsupply : ell ≤ mass f (T.filter (fun a => decide (0 < f a)))) :
    ∃ S : List α, S.Sublist T ∧ (∀ a ∈ S, 0 < f a) ∧ ell ≤ mass f S ∧
      ((∃ v ∈ T, ell ≤ f v ∧ S = [v]) ∨ mass f S ≤ 2 * ell - 2) := by
  classical
  by_cases hbig : ∃ v ∈ T, ell ≤ f v
  · obtain ⟨v, hv, hve⟩ := hbig
    refine ⟨[v], List.singleton_sublist.mpr hv, ?_, ?_, Or.inl ⟨v, hv, hve, rfl⟩⟩
    · intro a ha
      have : a = v := by simpa using ha
      subst a
      omega
    · simpa [mass] using hve
  · let Pos := T.filter (fun a => decide (0 < f a))
    have hentry (a : α) (ha : a ∈ Pos) : 0 < f a ∧ f a ≤ ell - 1 := by
      have hmem := List.mem_filter.mp ha
      have hp : 0 < f a := of_decide_eq_true hmem.2
      have hn : ¬ ell ≤ f a := fun h => hbig ⟨a, hmem.1, h⟩
      exact ⟨hp, by omega⟩
    have hne : Pos ≠ [] := by
      intro he
      change ell ≤ mass f Pos at hsupply
      simp [he, mass] at hsupply
      omega
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil Pos hne
    have hell2 : 0 ≤ ell - 2 := by have := hentry v hv; omega
    obtain ⟨S, hS, hlo, hhi⟩ := PositiveSmallReturnExchange.first_crossing
      f Pos (ell - 2) hell2 ell hell
      (fun a ha => ⟨(hentry a ha).1, by have := (hentry a ha).2; omega⟩) hsupply
    exact ⟨S, hS.trans (List.filter_sublist),
      fun a ha => (hentry a (hS.subset ha)).1, hlo, Or.inr (by omega)⟩

/-- The physical inventory supplies G,H,U balances before the strict energy
comparison is used. Every insertion in this helper is LARGE. -/
private theorem energy_cut {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (W V I Ret : List (Fin k))
    (hW : W.Nodup) (hI : I.Nodup) (hfresh : ∀ a ∈ I, a ∉ W)
    (hRet : ∀ a ∈ Ret, a ∈ W) (hIL : ∀ a ∈ I, Large k t a)
    (hperm : (V ++ Ret).Perm (W ++ I))
    (hsV : InStrip (s k t) (C k) 0 V)
    (hlarge : largeUsed k t I = largeUsed k t Ret)
    (henergy : H k t I < H k t Ret) :
    Inventory k t W V I Ret ∧ Legal k t V ∧
      G k t V = G k t W ∧ H k t V < H k t W ∧ J k t V < J k t W := by
  have inv := inventory_of_perm hk t W V I Ret hW hI hfresh hRet hIL hperm
  have hg := inv.largeBalance
  have he := inv.energyBalance
  have hG : G k t V = G k t W := by omega
  have hH : H k t V < H k t W := by omega
  exact ⟨inv, legal_of_strip inv.nodup hsV, hG, hH,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hG,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩)⟩

/-- A retained actual subword in the upper pair corridor admits the fresh
negative-positive native pair, returning at most one LARGE occurrence. -/
private theorem upper_pair_cut {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p : Fin k)
    (W K Ret : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : W.Nodup) (hp : p ∉ W) (hn : hit k 1 p ∉ W)
    (hpart : (K ++ Ret).Perm W) (hsK : InStrip (s k t) (C k) 0 K)
    (hlo : |s k t (hit k 1 p)| ≤ mass (s k t) K)
    (hhi : mass (s k t) K ≤ C k - (s k t p - |s k t (hit k 1 p)|))
    (hreturn : largeUsed k t Ret ≤ 1) :
    Legal k t (K ++ [hit k 1 p, p]) ∧
      Inventory k t W (K ++ [hit k 1 p, p]) [hit k 1 p, p] Ret ∧
      J k t (K ++ [hit k 1 p, p]) < J k t W := by
  classical
  let n := hit k 1 p
  let D := |s k t n|
  have geo := native_geometry hk t p hnlarge hexpand
  have hnval : s k t n = -D := by
    simpa [n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hDP : D < s k t p := by simpa [D, n, abs_of_pos hpositive] using geo.strictOrder.1
  have hb : 0 ≤ mass (s k t) K ∧ mass (s k t) K ≤ C k := by
    simpa [mass] using inStrip_prefix hsK K.length
  have hs : InStrip (s k t) (C k) 0 (K ++ [n, p]) := by
    apply inStrip_append hsK
    simp only [zero_add]
    change 0 ≤ mass (s k t) K ∧ mass (s k t) K ≤ C k ∧
      0 ≤ mass (s k t) K + s k t n ∧ mass (s k t) K + s k t n ≤ C k ∧
      0 ≤ mass (s k t) K + s k t n + s k t p ∧
      mass (s k t) K + s k t n + s k t p ≤ C k
    rw [hnval]
    change D ≤ mass (s k t) K at hlo
    change mass (s k t) K ≤ C k - (s k t p - D) at hhi
    omega
  have hD0 : 0 ≤ D := abs_nonneg _
  have hI : ([n, p] : List (Fin k)).Nodup := by
    have hnp : n ≠ p := by intro he; have := congrArg (s k t) he; omega
    simp [hnp]
  have hfresh (a : Fin k) (ha : a ∈ [n, p]) : a ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hn
    · exact hp
  have hIL (a : Fin k) (ha : a ∈ [n, p]) : Large k t a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact geo.nLarge
    · exact geo.pLarge
  have hperm : ((K ++ [n, p]) ++ Ret).Perm (W ++ [n, p]) := by
    have hswap : ((K ++ [n, p]) ++ Ret).Perm ((K ++ Ret) ++ [n, p]) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm : ([n, p] ++ Ret).Perm (Ret ++ [n, p])).append_left K
    exact hswap.trans (hpart.append_right [n, p])
  have inv := inventory_of_perm hk t W (K ++ [n, p]) [n, p] Ret hW hI hfresh
    (fun a ha => hpart.subset (List.mem_append_right K ha)) hIL hperm
  have hbal := inv.largeBalance
  have hi : largeUsed k t [n, p] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  have hg : G k t (K ++ [n, p]) < G k t W := by omega
  exact ⟨legal_of_strip inv.nodup hs, inv, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hg)⟩

set_option maxHeartbeats 1800000 in
/-- The full native three-negative exchange. The prefix A is arbitrary signed,
all labels are physical, and Legal controls every natural take. -/
theorem actualSource_threeNegative_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E))
    (hpunused : p ∉ A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
    (hnunused : hit k 1 p ∉
      A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
    (hsmall : ∀ a ∈ T0 ++ T1 ++ T2 ++ E, |s k t a| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z) :
    ∃ V : List (Fin k), Legal k t V ∧
      J k t V < J k t
        (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E) := by
  classical
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let L := A ++ [x] ++ T0
  let R := L ++ [y] ++ T1 ++ [zpen]
  let F := R ++ T2
  let W := F ++ [z] ++ E
  let P := f p
  let D := |f n|
  let B := C k - P
  let d := P - D
  let Y := -f y
  let Zpen := -f zpen
  let Z := -f z
  let s0 := mass f L
  let w := mass f R
  let u := mass f F
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change ∃ V, Legal k t V ∧ J k t V < J k t W
  by_contra hno
  have hmin (V : List (Fin k)) (hv : Legal k t V) : J k t W ≤ J k t V :=
    le_of_not_gt (fun hj => hno ⟨V, hv, hj⟩)
  have hT1 (a : Fin k) (ha : a ∈ T1) : |f a| < Q k :=
    hsmall a (by simp [ha])
  have hT2 (a : Fin k) (ha : a ∈ T2) : |f a| < Q k :=
    hsmall a (by simp [ha])
  have hE (a : Fin k) (ha : a ∈ E) : |f a| < Q k :=
    hsmall a (by simp [ha])
  obtain ⟨hu, hq, _⟩ := actualSource_terminal_small_ownership_prefix
    k t hk p z F E hpositive hnlarge hexpand hW hpunused hnunused hE hzlarge hmin
  change C k - d < u at hu
  change ∀ m : ℕ, B < mass f (F ++ [z] ++ E.take m) ∧
    mass f (F ++ [z] ++ E.take m) < D at hq
  by_cases hYP : Y ≤ P
  · have hb := hq E.length
    simp only [List.take_length] at hb
    obtain ⟨V, Ret, hv, _, _, _, _, _, hj, _⟩ :=
      actualSource_threeNegative_firstNegative_arrival_free_exchange_full
        k t hk p y zpen z A T0 T1 T2 E hpositive hnlarge hexpand hW
        hpunused hnunused hsmall hylarge hzpenlarge hzlarge hYP hb.1 hb.2
    exact (not_lt_of_ge (hmin V hv)) hj
  have hPY : P < Y := lt_of_not_ge hYP
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have geo := native_geometry hk t p hnlarge hexpand
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hD : Q k ≤ D := hnlarge
  have hDP : D < P := by simpa [P, D, f, n, abs_of_pos hpositive] using geo.strictOrder.1
  have hDrel : D = 2 * B + 1 := by
    have hh := geo.firstEquation
    change D = N k - 2 * |f p| at hh
    rw [hpabs, hN] at hh
    dsimp only [B]
    omega
  have hbudget : 2 * P ≤ C k + Q k := by
    simpa [P, f, abs_of_pos hpositive] using geo.budget
  have hdpos : 0 < d := by dsimp only [d]; omega
  have hdB : d ≤ B := by dsimp only [d, B]; omega
  have hCD : C k - d = B + D := by dsimp only [B, d]; ring
  have hbound (a : Fin k) : |f a| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hNodd _)
  have hPcap : P ≤ C k := by simpa only [hpabs] using hbound p
  have hyneg : f y < 0 := by change Q k ≤ -f y at hylarge; omega
  have hzpenneg : f zpen < 0 := by change Q k ≤ -f zpen at hzpenlarge; omega
  have hzneg : f z < 0 := by change Q k ≤ -f z at hzlarge; omega
  have hyL : Large k t y := by
    change Q k ≤ |f y|
    rw [abs_of_neg hyneg]
    exact hylarge
  have hzpL : Large k t zpen := by
    change Q k ≤ |f zpen|
    rw [abs_of_neg hzpenneg]
    exact hzpenlarge
  have hzL : Large k t z := by
    change Q k ≤ |f z|
    rw [abs_of_neg hzneg]
    exact hzlarge
  have hT10 := small_weights t T1 hT1
  have hT20 := small_weights t T2 hT2
  have hE0 := small_weights t E hE
  simp only [H, mass] at hT10 hT20 hE0
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsF : InStrip f (C k) 0 F :=
    (strip_split F ([z] ++ E) (by simpa [W, List.append_assoc] using hsW)).1
  have hsR : InStrip f (C k) 0 R := (strip_split R T2 hsF).1
  have hsL : InStrip f (C k) 0 L :=
    (strip_split L ([y] ++ T1 ++ [zpen])
      (by simpa [R, List.append_assoc] using hsR)).1
  have hsAfterL := (strip_split L ([y] ++ T1 ++ [zpen])
    (by simpa [R, List.append_assoc] using hsR)).2
  have hs0 : 0 ≤ s0 ∧ s0 ≤ C k := by
    simpa [s0, mass] using inStrip_prefix hsL L.length
  have hYs : Y ≤ s0 := by
    have hh := (inStrip_prefix hsAfterL 1).1
    simp only [List.cons_append, List.nil_append, List.take_succ_cons,
      List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, zero_add] at hh
    change 0 ≤ s0 + f y at hh
    dsimp only [Y]
    omega
  have hw : 0 ≤ w ∧ w ≤ C k := by
    simpa [w, mass] using inStrip_prefix hsR R.length
  have hub : 0 ≤ u ∧ u ≤ C k := by
    simpa [u, mass] using inStrip_prefix hsF F.length
  have hwpre : w + Zpen ≤ C k := by
    have hs := (strip_split (L ++ [y] ++ T1) [zpen]
      (by simpa [R] using hsR)).1
    have hb := (inStrip_prefix hs (L ++ [y] ++ T1).length).2
    have he : mass f (L ++ [y] ++ T1) = w + Zpen := by
      simp [w, R, Zpen, mass]
      ring
    have hb' : mass f (L ++ [y] ++ T1) ≤ C k := by
      simpa only [List.take_length, zero_add] using hb
    rwa [he] at hb'
  have hwQ : w < Q k := by change Q k ≤ Zpen at hzpenlarge; omega
  have hwB : B < w := by
    by_contra hn
    have hret : largeUsed k t (T2 ++ [z] ++ E) = 1 := by
      simp [largeUsed_append, largeUsed_cons, largeWeight, hzL, hT20.1, hE0.1]
    obtain ⟨hv, _, _, _, _, hj⟩ := actualSource_prefix_pair_truncation
      k t hk p R (T2 ++ [z] ++ E) hpositive hnlarge hexpand
      (by simpa [W, F, List.append_assoc] using hW)
      (by simpa [W, F, List.append_assoc] using hpunused)
      (by simpa [W, F, List.append_assoc] using hnunused)
      (by change w ≤ B; omega) (by omega)
    exact (not_lt_of_ge (hmin _ hv)) (by simpa [W, F, List.append_assoc] using hj)
  have hZpenP : Zpen < P := by dsimp only [B] at hwB; omega
  have hpn : p ≠ n := by intro he; have hh := congrArg f he; omega
  have hI : ([p, n] : List (Fin k)).Nodup := by simp [hpn]
  have hIW (a : Fin k) (ha : a ∈ [p, n]) : a ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hpunused
    · exact hnunused
  have hIL (a : Fin k) (ha : a ∈ [p, n]) : Large k t a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
  have hILcount : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, show Large k t n from geo.nLarge]
  -- Every actual positive selection ending in [D,C-d] gives a strict G cut.
  have hforbid (S : List (Fin k)) (hS : S.Sublist T2)
      (hs : InStrip f (C k) 0 (R ++ S))
      (hlo : D ≤ w + mass f S) (hhi : w + mass f S ≤ C k - d) : False := by
    obtain ⟨Rest, hp⟩ := hS.exists_perm_append
    have hrest : ∀ a ∈ Rest, |f a| < Q k := by
      intro a ha
      exact hT2 a (hp.mem_iff.mpr (List.mem_append_right S ha))
    have hrest0 := (small_weights t Rest hrest).1
    have hpart : ((R ++ S) ++ (Rest ++ [z] ++ E)).Perm W := by
      simpa [W, F, List.append_assoc] using
        (hp.symm.append_right ([z] ++ E)).append_left R
    obtain ⟨hv, _, hj⟩ := upper_pair_cut hk t p W (R ++ S) (Rest ++ [z] ++ E)
      hpositive hnlarge hexpand hW.1 hpunused hnunused hpart hs
      (by simpa [w, mass] using hlo) (by simpa [w, mass, d, P, D, f, n] using hhi)
      (by simp [largeUsed_append, largeUsed_cons, largeWeight, hzL, hrest0, hE0.1])
    exact (not_lt_of_ge (hmin _ hv)) hj
  have hmassT2 : u = w + mass f T2 := by simp [u, F, w, mass]
  let ell := D - w
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hellB : ell ≤ B := by dsimp only [ell]; omega
  have hsupply : ell ≤ mass f (T2.filter (fun a => decide (0 < f a))) := by
    have hh := positive_mass_dominates f T2
    dsimp only [ell]
    omega
  obtain ⟨S, hS, hSpos, hSlo, hScase⟩ := positive_selection f T2 ell hell hsupply
  have hovershoot : ∃ v ∈ T2, 0 < f v ∧ C k - d < w + f v := by
    rcases hScase with ⟨v, hv, hvlo, rfl⟩ | hShi
    · have hvpos : 0 < f v := by dsimp only [ell] at hvlo; omega
      have hvsmall : f v < Q k := lt_of_le_of_lt (le_abs_self _) (hT2 v hv)
      have hsRv : InStrip f (C k) 0 (R ++ [v]) := by
        apply inStrip_append hsR
        change InStrip f (C k) (0 + mass f R) [v]
        simp only [InStrip, zero_add]
        change 0 ≤ w ∧ w ≤ C k ∧ 0 ≤ w + f v ∧ w + f v ≤ C k
        omega
      by_cases hh : w + f v ≤ C k - d
      · exact False.elim (hforbid [v] (List.singleton_sublist.mpr hv) hsRv
          (by simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero]; dsimp only [ell] at hvlo; omega) (by simpa [mass] using hh))
      · exact ⟨v, hv, hvpos, lt_of_not_ge hh⟩
    · have hsRS : InStrip f (C k) 0 (R ++ S) := by
        apply inStrip_append hsR
        apply inStrip_reflect
        apply inStrip_nonpos
        · intro a ha; have := hSpos a ha; omega
        · simpa [mass, w] using hw.1
        · rw [sum_neg_map]
          change 0 ≤ C k - (0 + mass f R) + -mass f S
          change 0 ≤ C k - (0 + w) + -mass f S
          omega
      exact False.elim (hforbid S hS hsRS (by dsimp only [ell] at hSlo; omega)
        (by dsimp only [ell] at hShi; omega))
  obtain ⟨v, hvT2, hvpos, hvover⟩ := hovershoot
  let Vv := f v
  have hvsmall : Vv < Q k := lt_of_le_of_lt (le_abs_self _) (hT2 v hvT2)
  have hZle : Z ≤ D := by
    by_contra hnot
    have hDZ : D < Z := lt_of_not_ge hnot
    let V := F ++ [n] ++ E
    have hsE : InStrip f (C k) (u - D) E := by
      apply strip_of_all_prefixes E
      intro m
      have hh := hq m
      have hzcap : Z ≤ C k := by
        have hb := hbound z
        rw [abs_of_neg hzneg] at hb
        exact hb
      have he : mass f (F ++ [z] ++ E.take m) = u - Z + mass f (E.take m) := by
        simp [mass, u, Z]
        ring
      rw [he] at hh
      change 0 ≤ u - D + mass f (E.take m) ∧ u - D + mass f (E.take m) ≤ C k
      omega
    have hsV : InStrip f (C k) 0 V := by
      simp only [V, List.append_assoc, List.cons_append, List.nil_append]
      apply inStrip_append hsF
      change InStrip f (C k) (0 + mass f F) (n :: E)
      simp only [InStrip, zero_add]
      refine ⟨hub.1, hub.2, ?_⟩
      simpa [u, hnval, sub_eq_add_neg] using hsE
    have hp : (V ++ [z]).Perm (W ++ [n]) := by
      apply List.perm_iff_count.mpr
      intro a
      simp only [V, W, List.count_append, List.count_cons, List.count_nil]
      omega
    have hpow : (3 : ℕ) ^ (f n).natAbs < 3 ^ (f z).natAbs := by
      have hne : (f n).natAbs < (f z).natAbs := by
        have hmag : |f n| < |f z| := by rw [abs_of_neg hzneg]; exact hDZ
        exact_mod_cast (show ((f n).natAbs : ℤ) < ((f z).natAbs : ℤ) by
          simpa only [Int.natCast_natAbs] using hmag)
      exact pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hne
    obtain ⟨_, hv, _, _, hj⟩ := energy_cut hk t W V [n] [z] hW.1 (by simp)
      (by
        intro a ha
        have he : a = n := List.mem_singleton.mp ha
        subst a
        exact hnunused)
      (by
        intro a ha
        have he : a = z := List.mem_singleton.mp ha
        subst a
        simp [W])
      (by
        intro a ha
        have he : a = n := List.mem_singleton.mp ha
        subst a
        exact geo.nLarge) hp hsV
      (by simp [largeUsed, mass, largeWeight, hzL, show Large k t n from geo.nLarge])
      (by simpa [H, mass, energyWeight, hzL, show Large k t n from geo.nLarge] using hpow)
    exact (not_lt_of_ge (hmin _ hv)) hj
  let beta := s0 - Zpen
  let delta := D - Vv
  let alpha := beta - delta
  have hbeta : 0 < beta ∧ beta < Q k := by
    dsimp only [beta]
    change Q k ≤ Zpen at hzpenlarge
    omega
  have hdelta : 0 < delta ∧ delta < B := by dsimp only [delta, Vv]; omega
  have halphahi : alpha < Q k := by dsimp only [alpha]; omega
  have hpow : (3 : ℕ) ^ (f p).natAbs + 3 ^ (f n).natAbs <
      3 ^ (f y).natAbs + 3 ^ (f z).natAbs := by
    have hdp : (f n).natAbs < (f p).natAbs := by
      exact_mod_cast (show ((f n).natAbs : ℤ) < ((f p).natAbs : ℤ) by
        simpa only [Int.natCast_natAbs, hpabs] using hDP)
    have hpy : (f p).natAbs < (f y).natAbs := by
      exact_mod_cast (show ((f p).natAbs : ℤ) < ((f y).natAbs : ℤ) by
        simpa only [Int.natCast_natAbs, hpabs, abs_of_neg hyneg] using hPY)
    exact OddFirstNegativePlacement.two_energy_threshold _ _ _ _ hdp
      (Or.inl (lt_of_lt_of_le hpy (le_max_left _ _)))
  -- Case 1: move zpen directly before the unused positive-negative pair.
  by_cases hbB : beta ≤ B
  · let V := L ++ [zpen, p, n]
    let Ret := [y] ++ T1 ++ T2 ++ [z] ++ E
    have hsV : InStrip f (C k) 0 V := by
      apply inStrip_append hsL
      simp only [zero_add]
      change 0 ≤ s0 ∧ s0 ≤ C k ∧
        0 ≤ s0 + f zpen ∧ s0 + f zpen ≤ C k ∧
        0 ≤ s0 + f zpen + f p ∧ s0 + f zpen + f p ≤ C k ∧
        0 ≤ s0 + f zpen + f p + f n ∧ s0 + f zpen + f p + f n ≤ C k
      rw [hnval]
      dsimp only [beta] at hbeta hbB
      dsimp only [B, P] at hbB
      omega
    have hp : (V ++ Ret).Perm (W ++ [p, n]) := by
      apply List.perm_iff_count.mpr
      intro a
      simp only [V, Ret, W, F, R, List.count_append, List.count_cons, List.count_nil]
      omega
    obtain ⟨_, hv, _, _, hj⟩ := energy_cut hk t W V [p, n] Ret hW.1 hI hIW
      (by intro a ha; simp only [Ret, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at ha; simp only [W, F, R, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]; tauto) hIL hp hsV
      (by simp [Ret, largeUsed_append, largeUsed_cons, largeWeight, hyL, hzL,
        hT10.1, hT20.1, hE0.1, hILcount])
      (by simpa [Ret, H, mass, energyWeight, hyL, hzL, geo.pLarge,
        show Large k t n from geo.nLarge, hT10.2, hT20.2, hE0.2] using hpow)
    exact (not_lt_of_ge (hmin _ hv)) hj
  have hbgt : B < beta := lt_of_not_ge hbB
  have halpha : 0 < alpha ∧ alpha < Q k := by dsimp only [alpha]; omega
  have hsBase : InStrip f (C k) 0 (L ++ [n, v, zpen]) := by
    apply inStrip_append hsL
    simp only [zero_add]
    change 0 ≤ s0 ∧ s0 ≤ C k ∧ 0 ≤ s0 + f n ∧ s0 + f n ≤ C k ∧
      0 ≤ s0 + f n + f v ∧ s0 + f n + f v ≤ C k ∧
      0 ≤ s0 + f n + f v + f zpen ∧ s0 + f n + f v + f zpen ≤ C k
    rw [hnval]
    dsimp only [alpha, beta, delta, Vv, Zpen] at halpha
    dsimp only [delta, Vv] at hdelta
    omega
  have hBaseMass : mass f (L ++ [n, v, zpen]) = alpha := by
    simp [alpha, beta, delta, Vv, s0, Zpen, hnval, mass]
    ring
  have hT2perm : T2.Perm (v :: T2.erase v) := List.perm_cons_erase hvT2
  have hT2erase (a : Fin k) (ha : a ∈ T2.erase v) : |f a| < Q k :=
    hT2 a (List.mem_of_mem_erase ha)
  have hT2erase0 := small_weights t (T2.erase v) hT2erase
  simp only [H, mass] at hT2erase0
  -- Case 2: the moved positive v repairs the n,zpen packet before p.
  by_cases haB : alpha ≤ B
  · let V := L ++ [n, v, zpen] ++ [p]
    let Ret := [y] ++ T1 ++ T2.erase v ++ [z] ++ E
    have hsV : InStrip f (C k) 0 V := by
      apply inStrip_append hsBase
      simp only [zero_add]
      change InStrip f (C k) (mass f (L ++ [n, v, zpen])) [p]
      rw [hBaseMass]
      change 0 ≤ alpha ∧ alpha ≤ C k ∧ 0 ≤ alpha + f p ∧ alpha + f p ≤ C k
      dsimp only [B, P] at haB
      omega
    have hp : (V ++ Ret).Perm (W ++ [p, n]) := by
      apply List.perm_iff_count.mpr
      intro a
      have hh := hT2perm.count_eq a
      simp only [V, Ret, W, F, R, List.count_append, List.count_cons, List.count_nil] at *
      omega
    obtain ⟨_, hv, _, _, hj⟩ := energy_cut hk t W V [p, n] Ret hW.1 hI hIW
      (by
        intro a ha
        have hm : a ∈ T2.erase v → a ∈ T2 := fun he => List.mem_of_mem_erase he
        simp only [Ret, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        simp only [W, F, R, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        tauto) hIL hp hsV
      (by simp [Ret, largeUsed_append, largeUsed_cons, largeWeight, hyL, hzL,
        hT10.1, hT2erase0.1, hE0.1, hILcount])
      (by simpa [Ret, H, mass, energyWeight, hyL, hzL, geo.pLarge,
        show Large k t n from geo.nLarge, hT10.2, hT2erase0.2, hE0.2] using hpow)
    exact (not_lt_of_ge (hmin _ hv)) hj
  -- Case 3: refill from actual positive T1 and T2 occurrences, with v erased.
  have haBgt : B < alpha := lt_of_not_ge haB
  let T := T1 ++ T2.erase v
  let ell2 := Z - alpha
  have hell2 : 0 < ell2 ∧ ell2 ≤ B := by dsimp only [ell2]; omega
  have hT (a : Fin k) (ha : a ∈ T) : |f a| < Q k := by
    rcases List.mem_append.mp ha with ha | ha
    · exact hT1 a ha
    · exact hT2erase a ha
  have hTmass : alpha + mass f T = u + Y - D := by
    have he : mass f T2 = Vv + mass f (T2.erase v) := by
      simpa [mass, Vv] using (hT2perm.map f).sum_eq
    have huformula : u = s0 - Y + mass f T1 - Zpen + mass f T2 := by
      simp [u, F, R, s0, Y, Zpen, mass]
      ring
    have ht : mass f T = mass f T1 + mass f (T2.erase v) := by simp [T, mass]
    dsimp only [alpha, beta, delta]
    omega
  have hsupply2 : ell2 ≤ mass f (T.filter (fun a => decide (0 < f a))) := by
    have hh := positive_mass_dominates f T
    dsimp only [ell2]
    omega
  obtain ⟨Sel, hSel, hSelpos, hSello, hSelcase⟩ :=
    positive_selection f T ell2 hell2.1 hsupply2
  have hSelhi : alpha + mass f Sel ≤ C k := by
    rcases hSelcase with ⟨a, ha, _, rfl⟩ | hh
    · have hm : f a < Q k := lt_of_le_of_lt (le_abs_self _) (hT a ha)
      simp only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega
    · dsimp only [ell2] at hh
      omega
  have hsSel : InStrip f (C k) alpha Sel := by
    apply inStrip_reflect
    apply inStrip_nonpos
    · intro a ha; have := hSelpos a ha; omega
    · omega
    · rw [sum_neg_map]
      change 0 ≤ C k - alpha + -mass f Sel
      omega
  obtain ⟨Rest, hRest⟩ := hSel.exists_perm_append
  have hRestSmall (a : Fin k) (ha : a ∈ Rest) : |f a| < Q k :=
    hT a (hRest.mem_iff.mpr (List.mem_append_right Sel ha))
  have hRest0 := small_weights t Rest hRestSmall
  simp only [H, mass] at hRest0
  let V := (L ++ [n, v, zpen]) ++ Sel ++ [z]
  let Ret := [y] ++ Rest ++ E
  have hsV : InStrip f (C k) 0 V := by
    have hsPre : InStrip f (C k) 0 ((L ++ [n, v, zpen]) ++ Sel) :=
      inStrip_append hsBase (by simpa [mass, hBaseMass] using hsSel)
    apply inStrip_append hsPre
    simp only [zero_add]
    have he : mass f ((L ++ [n, v, zpen]) ++ Sel) = alpha + mass f Sel := by
      simpa [mass] using congrArg (fun h => h + mass f Sel) hBaseMass
    change InStrip f (C k) (mass f ((L ++ [n, v, zpen]) ++ Sel)) [z]
    rw [he]
    change 0 ≤ alpha + mass f Sel ∧ alpha + mass f Sel ≤ C k ∧
      0 ≤ alpha + mass f Sel + f z ∧ alpha + mass f Sel + f z ≤ C k
    dsimp only [ell2] at hSello
    omega
  have hp : (V ++ Ret).Perm (W ++ [n]) := by
    apply List.perm_iff_count.mpr
    intro a
    have he := hT2perm.count_eq a
    have hr := hRest.count_eq a
    simp only [V, Ret, W, F, R, T, List.count_append, List.count_cons, List.count_nil] at *
    omega
  have hRet (a : Fin k) (ha : a ∈ Ret) : a ∈ W := by
    have hRestT : ∀ a ∈ Rest, a ∈ T := fun a ha =>
      hRest.mem_iff.mpr (List.mem_append_right Sel ha)
    have he : ∀ a ∈ T2.erase v, a ∈ T2 := fun a ha => List.mem_of_mem_erase ha
    simp only [Ret, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [W, F, R, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases ha with ha | ha | ha
    · tauto
    · have hm := hRestT a ha
      simp only [T, List.mem_append] at hm
      rcases hm with hm | hm
      · tauto
      · have hm' := he a hm
        tauto
    · tauto
  have hny : (3 : ℕ) ^ (f n).natAbs < 3 ^ (f y).natAbs := by
    have he : (f n).natAbs < (f y).natAbs := by
      exact_mod_cast (show ((f n).natAbs : ℤ) < ((f y).natAbs : ℤ) by
        simp only [Int.natCast_natAbs, abs_of_neg hyneg]
        change D < Y
        omega)
    exact pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) he
  obtain ⟨_, hv, _, _, hj⟩ := energy_cut hk t W V [n] Ret hW.1 (by simp)
    (by
        intro a ha
        have he : a = n := List.mem_singleton.mp ha
        subst a
        exact hnunused)
    hRet (by
        intro a ha
        have he : a = n := List.mem_singleton.mp ha
        subst a
        exact geo.nLarge)
    hp hsV
    (by simp [Ret, largeUsed_append, largeUsed_cons, largeWeight, hyL,
      show Large k t n from geo.nLarge, hRest0.1, hE0.1])
    (by simpa [Ret, H, mass, energyWeight, hyL,
      show Large k t n from geo.nLarge, hRest0.2, hE0.2] using hny)
  exact (not_lt_of_ge (hmin _ hv)) hj

#print axioms actualSource_threeNegative_exchange_full

end D5.S3.Combinatorics.Circle.ThreeNegativeExchange
