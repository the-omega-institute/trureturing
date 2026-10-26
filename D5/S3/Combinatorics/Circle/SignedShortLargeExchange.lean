/- GID: D5/S3/Combinatorics/Circle/SignedShortLargeExchange
   generality: I
   mirror-B: none
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic,
     D5/S3/Combinatorics/Circle/PositiveSmallReturnExchange]
   utility: none
   digest: Constructive signed short-reserve selection and the shared physical
     three-LARGE exchange consumer. This is a staging draft; canonical
     compilation belongs in the host-created signed-short worktree. -/
module
public import D5.S3.Combinatorics.Circle.ThreeLargePacketExchange
public import Mathlib.Data.List.Perm.Basic

/-! The selector below is the new mathematics. It retains physical labels,
including a negative correction, and returns its explicit complement. The
consumer is deliberately written after the selector so the old positive
engine can be specialized to the same shared physical proof. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.SignedShortLargeExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange
open ThreeLargePacketExchange
open scoped BigOperators

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add] at *) <;> omega))

private theorem positive_mass_dominates {α : Type*} (f : α → ℤ) (X : List α) :
    mass f X ≤ mass f (X.filter (fun i => decide (0 < f i))) := by
  induction X with
  | nil => simp [mass]
  | cons i X ih =>
    by_cases hi : 0 < f i
    · simpa [mass, hi] using add_le_add_left ih (f i)
    · simp [mass, hi]
      have hn : f i ≤ 0 := by omega
      dsimp only [mass] at ih
      omega

private theorem mass_neg {α : Type*} (f : α → ℤ) (X : List α) :
    mass (fun i => -f i) X = -mass f X := by
  induction X with
  | nil => simp [mass]
  | cons i X ih =>
    change -f i + mass (fun j => -f j) X = -(f i + mass f X)
    rw [ih]
    ring

private theorem filter_subperm_of_imp {α : Type*} [DecidableEq α]
    (L : List α) (p q : α → Bool)
    (himp : ∀ i, p i = true → q i = true) :
    (L.filter p).Subperm (L.filter q) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases hp : p a = true
    · have hq : q a = true := himp a hp
      simpa [List.filter, hp, hq] using (List.subperm_cons a).mpr ih
    · by_cases hq : q a = true
      · simpa [List.filter, hp, hq] using (List.Subperm.cons_right a ih)
      · simpa [List.filter, hp, hq] using ih

private theorem append_signed_subperm {α : Type*} [DecidableEq α]
    (f : α → ℤ) (T U V : List α) (hT : T.Nodup)
    (hU : U.Subperm T) (hV : V.Subperm T)
    (hUpos : ∀ i ∈ U, 0 < f i) (hVneg : ∀ i ∈ V, 0 < -f i) :
    (U ++ V).Subperm T := by
  apply List.subperm_ext_iff.mpr
  intro i hi
  have hTcount : List.count i T ≤ 1 :=
    (List.nodup_iff_count_le_one.mp hT) i
  rcases List.mem_append.mp hi with hiU | hiV
  · have hUi := hU.count_le i
    have hUposVal := hUpos i hiU
    have hiV : i ∉ V := by
      intro hiV
      have hVnegVal := hVneg i hiV
      omega
    have hVcount : List.count i V = 0 := List.count_eq_zero.mpr hiV
    simp only [List.count_append]
    omega
  · have hVi := hV.count_le i
    have hVnegVal := hVneg i hiV
    have hiU : i ∉ U := by
      intro hiU
      have hUposVal := hUpos i hiU
      omega
    have hUcount : List.count i U = 0 := List.count_eq_zero.mpr hiU
    simp only [List.count_append]
    omega

/--
The actual signed short-reserve selector.

`P0` and `N0` are physical subpermutations of the positive and negative
short filters.  The positive remainder is crossed at `low-Sp`; if that
crossing undershoots, a positive reserve is crossed, and if it overshoots
`low+B`, a negative reserve is crossed with weights `-f`.  The final `K` is
the actual list complement, so no subset-sum or return-list existence is
assumed.
-/
theorem signed_short_reserve_select {α : Type*} [DecidableEq α]
    (f : α → ℤ) (T P0 N0 : List α) (B M low : ℤ)
    (hT : T.Nodup) (hB : 0 ≤ B) (hM : 0 < M)
    (hP : P0.Subperm
      (T.filter (fun i => decide (0 < f i ∧ f i ≤ B + 1))))
    (hN : N0.Subperm
      (T.filter (fun i => decide (0 < -f i ∧ -f i ≤ B + 1))))
    (hentry : ∀ i ∈ T, 0 < f i → f i ≤ M)
    (hlow : 0 < low)
    (hsupply : low ≤ mass f
      (T.filter (fun i => decide (0 < f i))))
    (hresource : M - B - 1 ≤ mass f P0 + mass (fun i => -f i) N0) :
    ∃ R K : List α, (R ++ K).Perm T ∧
      low ≤ mass f R ∧ mass f R ≤ low + B := by
  classical
  let Pos := T.filter (fun i => decide (0 < f i))
  let O := Pos.diff P0
  have hPosT : Pos.Subperm T := List.filter_sublist.subperm
  have hPPos : P0.Subperm Pos := by
    apply hP.trans
    apply filter_subperm_of_imp T
    intro i hi
    exact decide_eq_true_eq.mpr (decide_eq_true_eq.mp hi).1
  have hPosSign : ∀ i ∈ Pos, 0 < f i := by
    intro i hi
    have hi' : i ∈ T ∧ 0 < f i := by
      simpa only [Pos, List.mem_filter, decide_eq_true_eq] using hi
    exact hi'.2
  have hPentry : ∀ i ∈ P0, 0 < f i ∧ f i ≤ B + 1 := by
    intro i hi
    have hi' := hP.subset hi
    have hi'' : i ∈ T ∧ 0 < f i ∧ f i ≤ B + 1 := by
      simpa only [List.mem_filter, decide_eq_true_eq] using hi'
    exact hi''.2
  have hNentry : ∀ i ∈ N0, 0 < -f i ∧ -f i ≤ B + 1 := by
    intro i hi
    have hi' := hN.subset hi
    have hi'' : i ∈ T ∧ 0 < -f i ∧ -f i ≤ B + 1 := by
      simpa only [List.mem_filter, decide_eq_true_eq] using hi'
    exact hi''.2
  have hOentry : ∀ i ∈ O, 0 < f i ∧ f i ≤ M := by
    intro i hi
    have hiPos := (List.diff_sublist Pos P0).subset hi
    have hiPos' := (show i ∈ T ∧ 0 < f i from by
      simpa only [Pos, List.mem_filter, decide_eq_true_eq] using hiPos)
    exact ⟨hiPos'.2, hentry i hiPos'.1 hiPos'.2⟩
  have hPpart : (O ++ P0).Perm Pos := by
    have hpcomp := List.subperm_append_diff_self_of_count_le
      (l₁ := P0) (l₂ := Pos) (fun i _ => hPPos.count_le i)
    exact List.perm_append_comm.trans hpcomp
  have hsupplyPos : low ≤ mass f Pos := by
    change low ≤ mass f Pos at hsupply
    exact hsupply
  have hOtotal : low - mass f P0 ≤ mass f O := by
    have hs : mass f O + mass f P0 = mass f Pos := by
      simpa only [mass, List.map_append, List.sum_append] using (hPpart.map f).sum_eq
    omega
  have hPbound : ∀ i ∈ P0, 0 < f i ∧ f i ≤ B + 1 := hPentry
  have hNbound : ∀ i ∈ N0, 0 < -f i ∧ -f i ≤ B + 1 := hNentry
  have hOsub : O.Subperm Pos := (List.diff_sublist Pos P0).subperm
  have hPosSub : Pos.Subperm T := hPosT
  have hPsub : P0.Subperm T := hPPos.trans hPosT
  have hNsub : N0.Subperm T := hN.trans List.filter_sublist.subperm
  have hPosToT (U : List α) (hU : U.Subperm O) : U.Subperm T :=
    (hU.trans hOsub).trans hPosSub
  have hselect_positive (target : ℤ) (htarget : 0 < target)
      (htotal : target ≤ mass f P0) :
      ∃ P : List α, P.Sublist P0 ∧ target ≤ mass f P ∧
        mass f P ≤ target + B := by
    exact PositiveSmallReturnExchange.first_crossing f P0 B hB target
      htarget hPbound htotal
  by_cases hlowP : low ≤ mass f P0
  · obtain ⟨R, hR, hRlo, hRhi⟩ :=
      hselect_positive low hlow hlowP
    have hRsub : R.Subperm T := hR.subperm.trans hPsub
    let K := T.diff R
    have hperm : (R ++ K).Perm T :=
      List.subperm_append_diff_self_of_count_le (fun i _ => hRsub.count_le i)
    exact ⟨R, K, hperm, hRlo, hRhi⟩
  · have htargetO : 0 < low - mass f P0 := by omega
    obtain ⟨U, hU, hUlo, hUhi⟩ :=
      PositiveSmallReturnExchange.first_crossing f O (M - 1)
        (by omega) (low - mass f P0) htargetO
        (by
          intro i hi
          obtain ⟨hi0, hiM⟩ := hOentry i hi
          exact ⟨hi0, by omega⟩)
        (by omega)
    let u := mass f U
    have huupper : u ≤ low + B + mass (fun i => -f i) N0 := by
      dsimp only [u]
      have := hresource
      omega
    by_cases huLow : u < low
    · obtain ⟨P, hPsel, hPlo, hPhi⟩ :=
        hselect_positive (low - u) (by omega) (by omega)
      let R := U ++ P
      have hRsub : R.Subperm T :=
        ((hU.subperm.append hPsel.subperm).trans hPpart.subperm).trans hPosT
      let K := T.diff R
      have hperm : (R ++ K).Perm T :=
        List.subperm_append_diff_self_of_count_le (fun i _ => hRsub.count_le i)
      have hRlo : low ≤ mass f R := by
        have h : low ≤ mass f U + mass f P := by omega
        simpa only [R, mass, List.map_append, List.sum_append] using h
      have hRhi : mass f R ≤ low + B := by
        have h : mass f U + mass f P ≤ low + B := by omega
        simpa only [R, mass, List.map_append, List.sum_append] using h
      exact ⟨R, K, hperm, hRlo, hRhi⟩
    · by_cases huMid : u ≤ low + B
      · have hRsub : U.Subperm T := hPosToT U hU.subperm
        let K := T.diff U
        have hperm : (U ++ K).Perm T :=
          List.subperm_append_diff_self_of_count_le (fun i _ => hRsub.count_le i)
        exact ⟨U, K, hperm, by omega, huMid⟩
      · let d := u - low - B
        have hdpos : 0 < d := by dsimp only [d]; omega
        have hdsn : d ≤ mass (fun i => -f i) N0 := by
          dsimp only [d]
          omega
        obtain ⟨N, hNsel, hNlo, hNhi⟩ :=
          PositiveSmallReturnExchange.first_crossing (fun i => -f i) N0 B hB d
            hdpos hNbound hdsn
        let R := U ++ N
        have hRsub : R.Subperm T := by
          apply append_signed_subperm f T U N hT
          · exact hPosToT U hU.subperm
          · exact hNsel.subperm.trans hNsub
          · intro i hi
            exact hPosSign i ((hU.subperm.trans hOsub).subset hi)
          · intro i hi
            exact (hNentry _ (hNsel.subperm.subset hi)).1
        let K := T.diff R
        have hperm : (R ++ K).Perm T :=
          List.subperm_append_diff_self_of_count_le (fun i _ => hRsub.count_le i)
        have hRlo : low ≤ mass f R := by
          have hneg : mass (fun i => -f i) N = -mass f N := mass_neg f N
          have hNhi' := hNhi
          rw [hneg] at hNhi'
          dsimp only [d] at hNhi'
          have h : low ≤ mass f U + mass f N := by
            omega
          simpa only [R, mass, List.map_append, List.sum_append] using h
        have hRhi : mass f R ≤ low + B := by
          have hneg : mass (fun i => -f i) N = -mass f N := mass_neg f N
          have hNlo' := hNlo
          rw [hneg] at hNlo'
          dsimp only [d] at hNlo'
          have h : mass f U + mass f N ≤ low + B := by
            omega
          simpa only [R, mass, List.map_append, List.sum_append] using h
        exact ⟨R, K, hperm, hRlo, hRhi⟩

/-
Shared consumer design for the canonical tree.

The existing ~300-line physical proof from the former
`actualSource_threeLarge_return_exchange_full` is moved here once, with
the selector hypothesis below.  The only proof edits are: keep `hRtag`, use
the direct `R.Subperm S` supplied by `hselect`, remove the positive-only
`hpositiveR` derivation, and retain `hRtag` in the result.  All geometry,
zero-start gates, `Inventory`, exact `G/H/U` balances, strict descent, and
natural-take checks are shared unchanged.
-/
set_option maxHeartbeats 1200000 in
private theorem signed_three_large_exchange_engine
    (k t : ℕ) (tag : List (Fin k) → Prop)
    (hk : 3 ≤ k) (p q y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ ThreeLargePacketExchange.smallWord T0 T1 T2 E,
      |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (htagNil : tag [])
    (hselect : ∀ low : ℤ, 0 < low →
      low ≤ mass (s k t)
        (ThreeLargePacketExchange.positive t
          (ThreeLargePacketExchange.smallWord T0 T1 T2 E)) →
      ∃ R : List (Fin k),
        R.Subperm (ThreeLargePacketExchange.smallWord T0 T1 T2 E) ∧
        tag R ∧ low ≤ mass (s k t) R ∧
          mass (s k t) R ≤ low +
            (C k - s k t q)) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E
    let S := ThreeLargePacketExchange.smallWord T0 T1 T2 E
    let e0 := ThreeLargePacketExchange.prospective k t p q y zpen W
    ∃ R L : List (Fin k), R.Subperm S ∧ (L ++ R).Perm S ∧ tag R ∧
      (∀ i ∈ R, |s k t i| < Q k) ∧
      (let V := A ++ [p, n] ++ L ++ [z, q]
       let returned := [x, y, zpen] ++ R
       let e := e0 - mass (s k t) R
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [p, n, q] returned ∧
       G k t V = G k t W ∧ U V = U W + R.length ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs +
           3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs +
           3 ^ (s k t q).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e ∧ s k t q ≤ e ∧ e ≤ C k) := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let S := smallWord T0 T1 T2 E
  let Pos := positive t S
  let P := f p
  let D := |f n|
  let r := |f x|
  let qq := f q
  let Y := -f y
  let ZZ := -f zpen
  let Z := -f z
  let B := C k - qq
  let a0 := mass f A
  let b0 := a0 + P - D
  let h := mass f W
  let e0 := prospective k t p q y zpen W
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    have hh := geo.nValue
    simpa [n, D, f, orient, show ¬ s k t p < 0 by omega] using hh
  have hxval : f x = r := by
    have hh := geo.xValue
    simpa [x, r, f, orient, show ¬ s k t p < 0 by omega] using hh
  have hDP : D < P := by simpa [D,P,f,n,abs_of_pos hpositive] using geo.strictOrder.1
  have hPr : P < r := by simpa [P,r,f,x,abs_of_pos hpositive] using geo.strictOrder.2
  have hr : r = 2 * P - D := by
    have h1 : D = N k - 2 * P := by
      simpa [D,P,f,n,abs_of_pos hpositive] using geo.firstEquation
    have h2 : r = 4 * P - N k := by
      simpa [r,P,f,x,abs_of_pos hpositive] using geo.secondEquation
    ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hDbound : Q k ≤ D := hnlarge
  have hqpos : 0 < qq := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hqP : qq < P := hqsmaller
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hNpos hNodd _)
  have hPcap : P ≤ C k := by simpa only [hpabs] using hbound p
  have hY : 0 < Y ∧ Q k ≤ Y := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hZZ : 0 < ZZ ∧ Q k ≤ ZZ := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hZ : 0 < Z ∧ Z ≤ qq := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hpn : p ≠ n := by intro hh; have he := congrArg f hh; ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hpq : p ≠ q := by intro hh; have he := congrArg f hh; ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hnq : n ≠ q := by intro hh; have he := congrArg f hh; ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hpL : Large k t p := geo.pLarge
  have hnL : Large k t n := geo.nLarge
  have hxL : Large k t x := geo.xLarge
  have hqL : Large k t q := by
    change Q k ≤ |qq|
    rw [abs_of_pos hqpos]
    exact hqlarge
  have hyL : Large k t y := by
    change Q k ≤ |f y|
    rw [abs_of_neg (show f y < 0 by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith))]
    exact hylarge
  have hzpL : Large k t zpen := by
    change Q k ≤ |f zpen|
    rw [abs_of_neg (show f zpen < 0 by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith))]
    exact hzpenlarge
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsA : InStrip f (C k) 0 A :=
    (strip_split A ([x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [W, oldWord, x, List.append_assoc] using hsW)).1
  have hsAx : InStrip f (C k) 0 (A ++ [x]) :=
    (strip_split (A ++ [x]) (T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [W, oldWord, x, List.append_assoc] using hsW)).1
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa only [a0, mass, List.take_length, zero_add] using inStrip_prefix hsA A.length
  have hax : a0 + r ≤ C k := by
    have hh := (inStrip_prefix hsAx (A ++ [x]).length).2
    simp only [List.take_length, zero_add, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hh
    change a0 + f x ≤ C k at hh
    rwa [hxval] at hh
  have hh : 0 ≤ h := by
    have ht := (inStrip_prefix hsW W.length).1
    simpa only [h, mass, List.take_length, zero_add] using ht
  have hb0 : 0 ≤ b0 ∧ b0 ≤ C k - P := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have he0 : e0 = h + Y + ZZ + qq - P := rfl
  have he0Eq : e0 = b0 + mass f S - Z + qq := by
    dsimp only [e0, prospective, b0, a0, W, oldWord, S, smallWord, Y, ZZ, Z, qq, P]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    have hxr : f (hit k 2 p) = 2 * f p - D := by
      change f x = 2 * P - D
      rw [hxval, hr]
    dsimp only [f] at hxr ⊢
    rw [hxr]
    ring
  have he0lo : qq < e0 := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hmassPos : mass f S ≤ mass f Pos := positive_mass_dominates f S
  have hsupply : e0 - C k ≤ mass f Pos := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  obtain ⟨R, hRsub, hRtag, hRlo, hRhi⟩ : ∃ R : List (Fin k),
      R.Subperm S ∧ tag R ∧ e0 - C k ≤ mass f R ∧ mass f R ≤ e0 - qq := by
    by_cases hl : e0 - C k ≤ 0
    · refine ⟨[], List.nil_subperm, htagNil, ?_, ?_⟩
      · simp only [mass, List.map_nil, List.sum_nil]
        omega
      · simp only [mass, List.map_nil, List.sum_nil]
        omega
    · obtain ⟨R,hR,hTag,hlo,hhi⟩ := hselect (e0 - C k) (by omega) hsupply
      exact ⟨R,hR,hTag,hlo,by
        change mass f R ≤ (e0 - C k) + (C k - qq) at hhi
        omega⟩
  let Rem := S.diff R
  have hpart : (Rem ++ R).Perm S := by
    have hp := List.subperm_append_diff_self_of_count_le (fun i _ => hRsub.count_le i)
    exact List.perm_append_comm.trans hp
  have hmasspart : mass f Rem + mass f R = mass f S := by
    simpa only [mass, List.map_append, List.sum_append] using (hpart.map f).sum_eq
  have hsmallRem (i : Fin k) (hi : i ∈ Rem) : |f i| < Q k :=
    hsmall i ((List.diff_sublist _ _).subset hi)
  have hsmallR (i : Fin k) (hi : i ∈ R) : |f i| < Q k :=
    hsmall i (hRsub.subset hi)
  let e := e0 - mass f R
  let η := e - qq
  let c := η + Z
  have he : qq ≤ e ∧ e ≤ C k := by dsimp only [e]; omega
  have hη : 0 ≤ η ∧ η ≤ C k := by dsimp only [η]; omega
  have hc : 0 ≤ c ∧ c ≤ C k := by dsimp only [c, η]; omega
  have hsum : b0 + mass f Rem = c := by dsimp only [c, η, e]; omega
  have hcompat : ∀ i ∈ Rem, ∀ j ∈ Rem,
      0 < f i → f j < 0 → f i - f j ≤ C k := by
    intro i hi j hj hip hjn
    have hi' := hsmallRem i hi
    have hj' := hsmallRem j hj
    rw [abs_of_pos hip] at hi'
    rw [abs_of_neg hjn] at hj'
    omega
  have hb0cap : 0 ≤ b0 ∧ b0 ≤ C k := by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)
  have hend : 0 ≤ b0 + mass f Rem ∧ b0 + mass f Rem ≤ C k := by
    rw [hsum]
    exact hc
  obtain ⟨L,hL,hsL⟩ := exists_order_between f Rem (C k) b0 hb0cap
    (by simpa only [mass] using hend) hcompat
  have hLR : (L ++ R).Perm S := (hL.append_right R).trans hpart
  have hmassL : mass f L = mass f Rem := by simpa only [mass] using (hL.map f).sum_eq
  have hpairPN : InStrip f (C k) a0 [p,n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P + -D ∧ a0 + P + -D ≤ C k
    exact ⟨ha0.1,ha0.2,by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith),by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith),by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith),by ((try dsimp only [f,n,x,W,S,Pos,P,D,r,qq,Y,ZZ,Z,B,a0,b0,h,e0] at *); source_arith)⟩
  have hsApn : InStrip f (C k) 0 (A ++ [p,n]) :=
    inStrip_append hsA (by simpa only [zero_add, a0, mass] using hpairPN)
  have hApn : mass f (A ++ [p,n]) = b0 := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval]
    dsimp only [b0, a0, P, mass]
    ring
  have hsApnL : InStrip f (C k) 0 (A ++ [p,n] ++ L) := by
    apply inStrip_append hsApn
    change InStrip f (C k) (0 + mass f (A ++ [p,n])) L
    rw [zero_add,hApn]
    exact hsL
  have hApnL : mass f (A ++ [p,n] ++ L) = c := by
    calc
      _ = mass f (A ++ [p,n]) + mass f L := by simp only [mass,List.map_append,List.sum_append]
      _ = c := by rw [hApn,hmassL]; exact hsum
  have hpairZQ : InStrip f (C k) c [z,q] := by
    change 0 ≤ c ∧ c ≤ C k ∧ 0 ≤ c + f z ∧ c + f z ≤ C k ∧
      0 ≤ c + f z + f q ∧ c + f z + f q ≤ C k
    have hcz : c + f z = η := by dsimp only [c,Z]; ring
    have hczq : c + f z + f q = e := by rw [hcz]; dsimp only [η,qq]; ring
    rw [hczq,hcz]
    exact ⟨hc.1,hc.2,hη.1,hη.2,by omega,he.2⟩
  let V := A ++ [p,n] ++ L ++ [z,q]
  let Ret := [x,y,zpen] ++ R
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsApnL
    change InStrip f (C k) (0 + mass f (A ++ [p,n] ++ L)) [z,q]
    rw [zero_add,hApnL]
    exact hpairZQ
  have hI : [p,n,q].Nodup := by simp [hpn,hpq,hnq]
  have hIW (i : Fin k) (hi : i ∈ [p,n,q]) : i ∉ W := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpunused
    · exact hnunused
    · exact hqunused
  have hIL (i : Fin k) (hi : i ∈ [p,n,q]) : Large k t i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpL
    · exact hnL
    · exact hqL
  have hperm : (V ++ Ret).Perm (W ++ [p,n,q]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hh := hLR.count_eq i
    simp only [S,smallWord,List.count_append] at hh
    simp only [V,Ret,W,oldWord,x,List.count_append,List.count_cons,List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ Ret) : i ∈ W := by
    simp only [Ret,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with (rfl | rfl | rfl) | hi
    · simp [W,oldWord,x]
    · simp [W,oldWord]
    · simp [W,oldWord]
    · have hm := hRsub.subset hi
      simp only [S,smallWord,List.mem_append] at hm
      simp only [W,oldWord,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto
  have inv : Inventory k t W V [p,n,q] Ret :=
    inventory_of_perm hk t W V [p,n,q] Ret hW.1 hI hIW hRold hIL hperm
  have hRweights := small_weights t R hsmallR
  have hRetLarge : largeUsed k t Ret = 3 := by
    simp [Ret,largeWeight,hxL,hyL,hzpL,hRweights.1]
  have hRetEnergy : H k t Ret = 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs := by
    simp [Ret,energyWeight,hxL,hyL,hzpL,hRweights.2,f,s,Nat.add_assoc]
  have hILarge : largeUsed k t [p,n,q] = 3 := by simp [largeWeight,hpL,hnL,hqL]
  have hIEnergy : H k t [p,n,q] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    simp [energyWeight,hpL,hnL,hqL,f,s,Nat.add_assoc]
  have hG : G k t V = G k t W := by
    have ht := inv.largeBalance
    rw [hRetLarge,hILarge] at ht
    omega
  have hU : U V = U W + R.length := by
    have ht := inv.countBalance
    simp only [Ret,List.length_append,List.length_cons,List.length_nil] at ht
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f y).natAbs + 3 ^ (f zpen).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs := by
    have ht := inv.energyBalance
    rw [hRetEnergy,hIEnergy] at ht
    omega
  have hDn : (f n).natAbs < (f p).natAbs := by
    exact_mod_cast (show ((f n).natAbs : ℤ) < ((f p).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using geo.strictOrder.1)
  have hQn : (f q).natAbs < (f p).natAbs := by
    exact_mod_cast (show ((f q).natAbs : ℤ) < ((f p).natAbs : ℤ) by
      simp only [Int.natCast_natAbs]
      rw [abs_of_pos (show 0 < f q from hqpos),hpabs]
      exact hqP)
  have hPn : (f p).natAbs < (f x).natAbs := by
    exact_mod_cast (show ((f p).natAbs : ℤ) < ((f x).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using geo.strictOrder.2)
  have hEnergy : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs <
      (3 : ℕ) ^ (f x).natAbs := by
    have hd := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hDn
    have hq := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hQn
    have htop : 3 ^ (f p).natAbs + 3 ^ (f n).natAbs + 3 ^ (f q).natAbs <
        (3 : ℕ) ^ ((f p).natAbs + 1) := by
      rw [pow_succ]
      omega
    exact htop.trans_le (pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) (by omega))
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
    exact Or.inr ⟨hG,Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHstrict)⟩
  have hEnd : mass f V = e := by
    calc
      _ = mass f (A ++ [p,n] ++ L) + mass f [z,q] := by
        simp only [V,mass,List.map_append,List.sum_append]
      _ = e := by
        rw [hApnL]
        simp only [mass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        dsimp only [c,η,Z,qq]
        ring
  refine ⟨R,L,hRsub,hLR,hRtag,?_,legal_of_strip inv.nodup hsV,hsV,?_,
    inv,hG,hU,hH,hHstrict,hJ,hEnd,he.1,he.2⟩
  · intro i hi
    exact hsmallR i hi
  · intro j
    simpa [mass,f,V,n] using inStrip_prefix hsV j

set_option maxHeartbeats 1200000 in
/-- The constructive signed selector consumed by the shared physical exchange.
The reserve hypotheses are local to the actual SMALL word; no availability
claim is made beyond them. -/
theorem actualSource_threeLarge_signed_short_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (P0 N0 : List (Fin k)) (M : ℤ)
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ ThreeLargePacketExchange.smallWord T0 T1 T2 E,
      |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (hS : (ThreeLargePacketExchange.smallWord T0 T1 T2 E).Nodup)
    (hP0 : P0.Subperm
      ((ThreeLargePacketExchange.smallWord T0 T1 T2 E).filter
        (fun i => decide (0 < s k t i ∧ s k t i ≤ C k - s k t q + 1))))
    (hN0 : N0.Subperm
      ((ThreeLargePacketExchange.smallWord T0 T1 T2 E).filter
        (fun i => decide (0 < -s k t i ∧ -s k t i ≤ C k - s k t q + 1))))
    (hentry : ∀ i ∈ ThreeLargePacketExchange.smallWord T0 T1 T2 E,
      0 < s k t i → s k t i ≤ M)
    (hM : 0 < M)
    (hresource : M - (C k - s k t q) - 1 ≤
      mass (s k t) P0 + mass (fun i => -s k t i) N0) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := ThreeLargePacketExchange.oldWord p y zpen z A T0 T1 T2 E
    let S := ThreeLargePacketExchange.smallWord T0 T1 T2 E
    let e0 := ThreeLargePacketExchange.prospective k t p q y zpen W
    ∃ R L : List (Fin k), R.Subperm S ∧ (L ++ R).Perm S ∧
      (∀ i ∈ R, |s k t i| < Q k) ∧
      (let V := A ++ [p, n] ++ L ++ [z, q]
       let returned := [x, y, zpen] ++ R
       let e := e0 - mass (s k t) R
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [p, n, q] returned ∧
       G k t V = G k t W ∧ U V = U W + R.length ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs +
           3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs +
           3 ^ (s k t q).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e ∧ s k t q ≤ e ∧ e ≤ C k) := by
  classical
  let tag : List (Fin k) → Prop := fun _ => True
  have hB : 0 ≤ C k - s k t q := by
    obtain ⟨hQ, hN, hC, hNpos, hNodd⟩ := source_geometry hk
    change 2 ≤ Q k at hQ
    change C k = 2 * Q k - 1 at hC
    have hqcap : |s k t q| ≤ C k :=
      abs_le.mpr (centered_bounds hNpos hNodd _)
    have hqpos : 0 < s k t q := by
      omega
    rw [abs_of_pos hqpos] at hqcap
    omega
  have hselect : ∀ low : ℤ, 0 < low →
      low ≤ mass (s k t)
        (ThreeLargePacketExchange.positive t
          (ThreeLargePacketExchange.smallWord T0 T1 T2 E)) →
      ∃ R : List (Fin k),
        R.Subperm (ThreeLargePacketExchange.smallWord T0 T1 T2 E) ∧
        tag R ∧ low ≤ mass (s k t) R ∧
          mass (s k t) R ≤ low + (C k - s k t q) := by
    intro low hlow hsupply
    obtain ⟨R, K, hperm, hRlo, hRhi⟩ :=
      signed_short_reserve_select (s k t)
        (ThreeLargePacketExchange.smallWord T0 T1 T2 E) P0 N0
        (C k - s k t q) M low hS hB hM hP0 hN0 hentry hlow hsupply hresource
    have hRK : R.Subperm (R ++ K) := by
      simpa using (List.Subperm.append (List.Subperm.refl R)
        (List.nil_subperm : ([] : List (Fin k)).Subperm K))
    have hRsub : R.Subperm (ThreeLargePacketExchange.smallWord T0 T1 T2 E) :=
      hRK.trans hperm.subperm
    exact ⟨R, hRsub, trivial, hRlo, hRhi⟩
  simpa [tag] using
    (signed_three_large_exchange_engine k t tag hk p q y zpen z A T0 T1 T2 E
      hpositive hnlarge hexpand hW hpunused hnunused hqunused hsmall hylarge
      hzpenlarge hzlarge hzupper hqlarge hqsmaller trivial hselect)


end D5.S3.Combinatorics.Circle.SignedShortLargeExchange
