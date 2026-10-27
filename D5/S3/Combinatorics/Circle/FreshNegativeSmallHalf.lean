/- GID: D5/S3/Combinatorics/Circle/FreshNegativeSmallHalf
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FreshNegativeSmallHalf
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: A fresh negative SMALL half and a fresh negative LARGE replace an old LARGE with exact physical inventory and strict energy descent. -/
module
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
public import D5.S3.Combinatorics.Circle.LargeSkeletonOrdering

/-! # Fresh negative SMALL half exchanges -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.FreshNegativeSmallHalf
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange

set_option maxHeartbeats 1400000 in
/-- Replace one negative LARGE c=-2μ by fresh n=-D and its fresh physical
negative SMALL half b=-μ. The old suffix contains only negative LARGE.
The baseline W++[b] need only be Nodup, not Legal. -/
theorem actualSource_fresh_negative_small_half_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (n b c : Fin k)
    (F R : List (Fin k)) (D μ : ℤ)
    (hW : Legal k t (F ++ [c] ++ R))
    (hnunused : n ∉ F ++ [c] ++ R)
    (hbunused : b ∉ F ++ [c] ++ R)
    (hnval : s k t n = -D) (hbval : s k t b = -μ)
    (hcval : s k t c = -(2 * μ))
    (hμ : 0 < μ) (hμQ : μ < Q k) (hD : Q k ≤ D)
    (hDZ : D < 2 * μ)
    (hend : D - μ ≤ mass (s k t) (F ++ [c] ++ R))
    (hboundary : ∀ R0 i R1, R = R0 ++ [i] ++ R1 → Large k t i →
      s k t i < 0 ∧ D - μ ≤ mass (s k t) (F ++ [c] ++ R0 ++ [i])) :
    ∃ L : List (Fin k), L.Perm ([b] ++ R) ∧
      (let W := F ++ [c] ++ R
       let V := F ++ [n] ++ L
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t (W ++ [b]) V [n] [c] ∧
       (V ++ [c]).Perm (W ++ [n,b]) ∧
       V.toFinset = (W.toFinset \ {c}) ∪ {n,b} ∧
       V.toFinsetᶜ = (W.toFinsetᶜ \ {n,b}) ∪ {c} ∧
       G k t V = G k t W ∧ U V + 1 = U W ∧
       H k t V + 3 ^ (s k t c).natAbs = H k t W + 3 ^ (s k t n).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       remainingSmall t V = remainingSmall t W \ {b} ∧
       mass (s k t) V = mass (s k t) W - (D - μ) ∧
       remainingMass (s k t) V = -(mass (s k t) W - (D - μ))) := by
  classical
  dsimp only
  let f := s k t
  let W := F ++ [c] ++ R
  let Wb := W ++ [b]
  let u := mass f F
  let e := D - μ
  change Legal k t W at hW
  change n ∉ W at hnunused
  change b ∉ W at hbunused
  have hμD : μ < D := lt_of_lt_of_le hμQ hD
  have he : 0 < e := by dsimp only [e]; omega
  have hbSmall : ¬ Large k t b := by
    change ¬ Q k ≤ |s k t b|
    rw [hbval, abs_of_neg (by omega : -μ < 0), neg_neg]
    omega
  have hnLarge : Large k t n := by
    change Q k ≤ |s k t n|
    rw [hnval, abs_of_neg (by omega : -D < 0), neg_neg]
    exact hD
  have hcLarge : Large k t c := by
    change Q k ≤ |s k t c|
    rw [hcval, abs_of_neg (by omega : -(2 * μ) < 0), neg_neg]
    omega
  have hcW : c ∈ W := by simp [W]
  have hnb : n ≠ b := by
    intro hh
    have hv := congrArg f hh
    change s k t n = s k t b at hv
    rw [hnval, hbval] at hv
    omega
  have hbc : b ≠ c := by
    intro hh
    subst b
    exact hbunused hcW
  have hnc : n ≠ c := by
    intro hh
    subst n
    exact hnunused hcW
  have hWb : Wb.Nodup := hW.1.append (by simp)
    (List.disjoint_left.mpr (by
      intro i hiW hib
      obtain rfl := List.mem_singleton.mp hib
      exact hbunused hiW))
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsF, hsTail⟩ := strip_split F ([c] ++ R)
    (by simpa only [W, List.append_assoc] using hsW)
  have hu : 0 ≤ u ∧ u ≤ C k := by
    simpa only [u, mass, List.take_zero, List.map_nil, List.sum_nil,
      add_zero, zero_add] using inStrip_prefix hsTail 0
  have ha : 0 ≤ u - 2 * μ ∧ u - 2 * μ ≤ C k := by
    have hh := inStrip_prefix hsTail 1
    simpa [u, mass, hcval] using hh
  have hsR : InStrip f (C k) (u - 2 * μ) R := by
    have hh := hsTail.2.2
    simpa [u, mass, hcval] using hh
  have hwEnd : 0 ≤ mass f W ∧ mass f W ≤ C k := by
    simpa only [List.take_length] using hW.2 W.length
  have hmW : mass f W = u - 2 * μ + mass f R := by
    simp only [W, u, f, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hcval]
    ring
  have hstart : 0 ≤ u - D ∧ u - D ≤ C k := by omega
  have hfinal : 0 ≤ (u - D) + mass f ([b] ++ R) ∧
      (u - D) + mass f ([b] ++ R) ≤ C k := by
    have hm : (u - D) + mass f ([b] ++ R) = mass f W - e := by
      rw [hmW]
      simp only [f, e, mass, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, hbval]
      ring
    rw [hm]
    change e ≤ mass f W at hend
    constructor <;> omega
  have hnewBoundary : ∀ B0 i B1,
      [b] ++ R = B0 ++ [i] ++ B1 → Q k ≤ |f i| →
      (0 ≤ (u - D) + mass f B0 ∧ (u - D) + mass f B0 ≤ C k) ∧
      (0 ≤ (u - D) + mass f B0 + f i ∧
        (u - D) + mass f B0 + f i ≤ C k) := by
    intro B0 i B1 hsplit hi
    cases B0 with
    | nil =>
      have hh : b :: R = i :: B1 := by simpa using hsplit
      have hbi : b = i := (List.cons.inj hh).1
      subst i
      exact False.elim (hbSmall hi)
    | cons j R0 =>
      have hh : b :: R = j :: (R0 ++ [i] ++ B1) := by simpa using hsplit
      have hbj : b = j := (List.cons.inj hh).1
      subst j
      have hRsplit : R = R0 ++ [i] ++ B1 := (List.cons.inj hh).2
      obtain ⟨hineg, himargin⟩ := hboundary R0 i B1 hRsplit hi
      have hsOld := (strip_split R0 ([i] ++ B1)
        (by simpa only [hRsplit, List.append_assoc] using hsR)).2
      have hd : 0 ≤ (u - 2 * μ) + mass f R0 ∧
          (u - 2 * μ) + mass f R0 ≤ C k := by
        simpa only [List.take_zero, mass, List.map_nil, List.sum_nil, add_zero]
          using inStrip_prefix hsOld 0
      have ha' : 0 ≤ (u - 2 * μ) + mass f R0 + f i ∧
          (u - 2 * μ) + mass f R0 + f i ≤ C k := by
        simpa [mass, add_assoc] using inStrip_prefix hsOld 1
      have hmargin : e ≤ (u - 2 * μ) + mass f R0 + f i := by
        have hm : mass f (F ++ [c] ++ R0 ++ [i]) =
            (u - 2 * μ) + mass f R0 + f i := by
          simp only [u, f, mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero, hcval]
          ring
        change e ≤ mass f (F ++ [c] ++ R0 ++ [i]) at himargin
        rwa [hm] at himargin
      have hm : (u - D) + mass f (b :: R0) =
          (u - 2 * μ) + mass f R0 - e := by
        simp only [f, e, mass, List.map_cons, List.sum_cons, hbval]
        ring
      rw [hm]
      change f i < 0 at hineg
      constructor <;> constructor <;> omega
  obtain ⟨hQ, _, hC, _, _⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change C k = 2 * Q k - 1 at hC
  obtain ⟨L, hL, _, hsL⟩ :=
    LargeSkeletonOrdering.exists_order_preserving_large f (Q k) (C k)
      (by omega) (by omega) ([b] ++ R) (u - D) hstart hfinal hnewBoundary
  let V := F ++ [n] ++ L
  have hsN : InStrip f (C k) u [n] := by
    change 0 ≤ u ∧ u ≤ C k ∧ 0 ≤ u + f n ∧ u + f n ≤ C k
    change f n = -D at hnval
    rw [hnval]
    exact ⟨hu.1, hu.2, by omega, by omega⟩
  have hsFn : InStrip f (C k) 0 (F ++ [n]) :=
    inStrip_append hsF (by simpa only [u, zero_add] using hsN)
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsFn
    simpa [u, f, mass, hnval] using hsL
  have hperm : (V ++ [c]).Perm (W ++ [n,b]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hh := hL.count_eq i
    simp only [V, W, List.count_append, List.count_cons, List.count_nil] at hh ⊢
    omega
  have hpermBase : (V ++ [c]).Perm (Wb ++ [n]) := by
    apply hperm.trans
    simpa only [Wb, List.append_assoc] using
      (List.perm_append_comm : ([n] ++ [b]).Perm ([b] ++ [n])).append_left W
  have inv : Inventory k t Wb V [n] [c] :=
    inventory_of_perm hk t Wb V [n] [c] hWb (by simp)
      (by
        intro i hi
        obtain rfl := List.mem_singleton.mp hi
        simpa only [Wb, List.mem_append, List.mem_singleton, not_or] using
          And.intro hnunused hnb)
      (by intro i hi; obtain rfl := List.mem_singleton.mp hi; simp [Wb, hcW])
      (by intro i hi; obtain rfl := List.mem_singleton.mp hi; exact hnLarge)
      hpermBase
  have invBack : Inventory k t Wb W [] [b] :=
    inventory_of_perm hk t Wb W [] [b] hWb (by simp) (by simp)
      (by intro i hi; obtain rfl := List.mem_singleton.mp hi; simp [Wb])
      (by simp) (by simp [Wb])
  have hgBase : G k t Wb = G k t W := by
    simpa [largeUsed, mass, largeWeight, hbSmall] using invBack.largeBalance.symm
  have hhBase : H k t Wb = H k t W := by
    simpa [H, mass, energyWeight, hbSmall] using invBack.energyBalance.symm
  have huBase : U Wb + 1 = U W := by
    simpa only [List.length_nil, List.length_singleton, Nat.add_zero] using
      invBack.countBalance.symm
  have hln : largeUsed k t [n] = 1 := by
    simp [largeUsed, mass, largeWeight, hnLarge]
  have hlc : largeUsed k t [c] = 1 := by
    simp [largeUsed, mass, largeWeight, hcLarge]
  have hg : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hln, hlc, hgBase] at hh
    omega
  have huV : U V + 1 = U W := by
    have hh := inv.countBalance
    simp only [List.length_singleton] at hh
    omega
  have hhn : H k t [n] = 3 ^ (s k t n).natAbs := by
    simp [H, mass, energyWeight, hnLarge]
  have hhc : H k t [c] = 3 ^ (s k t c).natAbs := by
    simp [H, mass, energyWeight, hcLarge]
  have henergy : H k t V + 3 ^ (s k t c).natAbs =
      H k t W + 3 ^ (s k t n).natAbs := by
    simpa only [hhn, hhc, hhBase] using inv.energyBalance
  have hmag : |s k t n| < |s k t c| := by
    rw [hnval, hcval, abs_of_neg (by omega : -D < 0),
      abs_of_neg (by omega : -(2 * μ) < 0)]
    omega
  have hexp : (s k t n).natAbs < (s k t c).natAbs := by
    exact_mod_cast (show ((s k t n).natAbs : ℤ) < (s k t c).natAbs by
      simpa only [Int.natCast_natAbs] using hmag)
  have hpow := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hexp
  have hH : H k t V < H k t W := by omega
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩
  have hsmBase : remainingSmall t Wb = remainingSmall t W \ {b} := by
    ext i
    simp only [remainingSmall, Wb, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, Finset.union_singleton,
      Finset.mem_filter, Finset.mem_compl, Finset.mem_insert,
      Finset.mem_sdiff, Finset.mem_singleton]
    tauto
  have hsm : remainingSmall t V = remainingSmall t W \ {b} := by
    have hh := inv.smallPartition
    simpa [hcLarge, hsmBase] using hh
  have hmass : mass f V = mass f W - e := by
    have hh := inv.sourceBalance
    simp only [Wb, mass, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hh
    change mass f V + f c = mass f W + f b + f n at hh
    change f n = -D at hnval
    change f b = -μ at hbval
    change f c = -(2 * μ) at hcval
    rw [hnval, hbval, hcval] at hh
    dsimp only [e]
    omega
  have hused : V.toFinset = (W.toFinset \ {c}) ∪ {n,b} := by
    rw [inv.used]
    ext i
    by_cases hib : i = b
    · subst i
      simp [Wb, hbc]
    · simp [Wb, hib, List.toFinset_append] <;> tauto
  have hunused : V.toFinsetᶜ = (W.toFinsetᶜ \ {n,b}) ∪ {c} := by
    rw [hused]
    ext i
    by_cases hic : i = c
    · subst i
      simp [hcW, hnc.symm, hbc.symm]
    · simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton]
      simp only [hic, or_false, not_false_eq_true, and_true]
      tauto
  have hv : Legal k t V := legal_of_strip inv.nodup hsV
  refine ⟨L, hL, hv, hsV, hv.2, inv, hperm, hused, hunused,
    hg, huV, henergy, hH, hJ, hsm, hmass, ?_⟩
  simpa only [hmass] using inv.complementSum

end D5.S3.Combinatorics.Circle.FreshNegativeSmallHalf
