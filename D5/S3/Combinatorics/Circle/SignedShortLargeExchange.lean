/- GID: D5/S3/Combinatorics/Circle/SignedShortLargeExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SignedShortLargeExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Constructive signed short-reserve selection supplies the shared full physical three-LARGE exchange under actual signed reserve bounds. -/
module
public import D5.S3.Combinatorics.Circle.ThreeLargePacketExchange
public import Mathlib.Data.List.Perm.Basic

/-! The signed selector retains physical labels, including a negative correction,
and returns its explicit complement. Its full exchange uses the tagged
physical engine shared with the positive packet and single-anchor consumers. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.SignedShortLargeExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange
open ThreeLargePacketExchange
open scoped BigOperators

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
          have hneg : mass (fun i => -f i) N = -mass f N := SourceWidth.sum_neg_map f N
          have hNhi' := hNhi
          rw [hneg] at hNhi'
          dsimp only [d] at hNhi'
          have h : low ≤ mass f U + mass f N := by
            omega
          simpa only [R, mass, List.map_append, List.sum_append] using h
        have hRhi : mass f R ≤ low + B := by
          have hneg : mass (fun i => -f i) N = -mass f N := SourceWidth.sum_neg_map f N
          have hNlo' := hNlo
          rw [hneg] at hNlo'
          dsimp only [d] at hNlo'
          have h : mass f U + mass f N ≤ low + B := by
            omega
          simpa only [R, mass, List.map_append, List.sum_append] using h
        exact ⟨R, K, hperm, hRlo, hRhi⟩

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
  have hSW : (smallWord T0 T1 T2 E).Sublist
      (oldWord p y zpen z A T0 T1 T2 E) := by
    simpa only [smallWord, oldWord, List.nil_append, List.append_nil,
      List.append_assoc] using
      ((((((((List.nil_sublist A).append (List.nil_sublist [hit k 2 p])).append
        (List.Sublist.refl T0)).append (List.nil_sublist [y])).append
        (List.Sublist.refl T1)).append (List.nil_sublist [zpen])).append
        (List.Sublist.refl T2)).append (List.nil_sublist [z])).append
        (List.Sublist.refl E)
  have hS : (smallWord T0 T1 T2 E).Nodup := hW.1.sublist hSW
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
    (actualSource_threeLarge_tagged_exchange_full k t tag hk p q y zpen z A T0 T1 T2 E
      hpositive hnlarge hexpand hW hpunused hnunused hqunused hsmall hylarge
      hzpenlarge hzlarge hzupper hqlarge hqsmaller trivial hselect)


end D5.S3.Combinatorics.Circle.SignedShortLargeExchange
