/- SOURCE DRAFT: anonymous ALL-Legal-minimum consumer; no kernel receipt. -/
import D5.S3.Combinatorics.Circle.FreshNegativeSmallHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FreshNegativeSmallHalfConsumer
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange FreshNegativeSmallHalf

/-- A fresh negative SMALL append. Kept private: the only public new engine
above concerns the genuine LARGE replacement and its physical Inventory. -/
private theorem negative_small_append_descent
    (k t : ℕ) (hk : 3 ≤ k) (W : List (Fin k)) (b : Fin k)
    (hW : Legal k t W) (hb : b ∉ W)
    (hsmall : |s k t b| < Q k) (hneg : s k t b < 0)
    (hcap : -s k t b ≤ mass (s k t) W) :
    ∃ V : List (Fin k), Legal k t V ∧ J k t V < J k t W := by
  classical
  let V := W ++ [b]
  have hbNot : ¬ Large k t b := by change ¬ Q k ≤ |s k t b|; omega
  have hn : V.Nodup := hW.1.append (by simp) (List.disjoint_left.mpr (by
    intro i hiW hib
    obtain rfl := List.mem_singleton.mp hib
    exact hb hiW))
  have hh : 0 ≤ mass (s k t) W ∧ mass (s k t) W ≤ C k := by
    simpa only [List.take_length] using hW.2 W.length
  have hs : InStrip (s k t) (C k) (mass (s k t) W) [b] := by
    change 0 ≤ mass (s k t) W ∧ mass (s k t) W ≤ C k ∧
      0 ≤ mass (s k t) W + s k t b ∧ mass (s k t) W + s k t b ≤ C k
    exact ⟨hh.1, hh.2, by omega, by omega⟩
  have hv : Legal k t V := legal_of_strip hn
    (inStrip_append (strip_of_legal hW) (by simpa only [mass, zero_add] using hs))
  have inv : Inventory k t V W [] [b] :=
    inventory_of_perm hk t V W [] [b] hn (by simp) (by simp)
      (by intro i hi; obtain rfl := List.mem_singleton.mp hi; simp [V])
      (by simp) (by simp [V])
  have hg : G k t V = G k t W := by
    simpa [largeUsed, mass, largeWeight, hbNot] using inv.largeBalance.symm
  have hH : H k t V = H k t W := by
    simpa [H, mass, energyWeight, hbNot] using inv.energyBalance.symm
  have hU : U V + 1 = U W := by
    simpa only [List.length_nil, List.length_singleton, Nat.add_zero] using
      inv.countBalance.symm
  have hj : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨hH, by omega⟩)⟩
  exact ⟨V, hv, hj⟩

set_option maxHeartbeats 1800000 in
/-- Anonymous ALL-Legal-minimum application. There is no endpoint restriction
on competitors. This applies in particular to c=zpen in the native three-
negative word, where R=T2++[z]++E has exactly one LARGE, negative; it also covers
the first negative when its two remaining LARGE are negative. -/
example (k t : ℕ) (hk : 3 ≤ k) (p c : Fin k) (F R : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (F ++ [c] ++ R))
    (hpunused : p ∉ F ++ [c] ++ R)
    (hnunused : hit k 1 p ∉ F ++ [c] ++ R)
    (hcneg : s k t c < 0) (hceven : (-s k t c) % 2 = 0)
    (hcount : largeUsed k t R ≤ 2)
    (hnegative : ∀ i ∈ R, Large k t i → s k t i < 0)
    (hmin : ∀ V : List (Fin k), Legal k t V →
      J k t (F ++ [c] ++ R) ≤ J k t V) :
    (finRotate k).symm c ∈ F ++ [c] ++ R := by
  classical
  let W := F ++ [c] ++ R
  let n := hit k 1 p
  let b := (finRotate k).symm c
  let P := s k t p
  let D := |s k t n|
  let B := C k - P
  let μ := -s k t b
  change Legal k t W at hW
  change p ∉ W at hpunused
  change n ∉ W at hnunused
  change ∀ V : List (Fin k), Legal k t V → J k t W ≤ J k t V at hmin
  change b ∈ W
  by_contra hb
  obtain ⟨heven, hhalf, hbsmall, hbneg⟩ | hodd :=
    FirstNegativeShiftExchange.negative_parent k t hk c hcneg
  swap
  · omega
  change 2 * s k t b = -(-s k t c) at hhalf
  change |s k t b| < Q k at hbsmall
  change s k t b < 0 at hbneg
  have hμ : 0 < μ := by dsimp only [μ]; omega
  have hbval : s k t b = -μ := by dsimp only [μ]; omega
  have hcval : s k t c = -(2 * μ) := by dsimp only [μ]; omega
  have hμQ : μ < Q k := by simpa [μ, abs_of_neg hbneg] using hbsmall
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, _, _⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hD : Q k ≤ D := hnlarge
  have hnval : s k t n = -D := by
    simpa [n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hDN : D = N k - 2 * P := by
    simpa [n, D, P, abs_of_pos hpositive] using geo.firstEquation
  have hDB : D = 2 * B + 1 := by dsimp only [B]; omega
  have hlow : B < mass (s k t) W := by
    by_contra hcut
    obtain ⟨hv, _, _, _, _, hj⟩ :=
      FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
        k t hk p W [] hpositive hnlarge hexpand
        (by simpa only [List.append_nil] using hW)
        (by simpa only [List.append_nil] using hpunused)
        (by simpa only [List.append_nil] using hnunused)
        (by dsimp only [B, P] at *; omega) (by simp [largeUsed, mass])
    have hj' : J k t (W ++ [p, hit k 1 p]) < J k t W := by
      simpa only [List.append_nil] using hj
    exact (not_lt_of_ge (hmin _ hv)) hj'
  by_cases happend : μ ≤ mass (s k t) W
  · obtain ⟨V, hv, hj⟩ := negative_small_append_descent k t hk W b
      hW hb hbsmall hbneg (by dsimp only [μ] at happend; omega)
    exact (not_lt_of_ge (hmin V hv)) hj
  have hμB : B < μ := by omega
  have hDZ : D < 2 * μ := by omega
  have heB : D - μ ≤ B := by omega
  have hboundary : ∀ R0 i R1, R = R0 ++ [i] ++ R1 → Large k t i →
      s k t i < 0 ∧ D - μ ≤ mass (s k t) (F ++ [c] ++ R0 ++ [i]) := by
    intro R0 i R1 hsplit hi
    have hiR : i ∈ R := by simp [hsplit]
    refine ⟨hnegative i hiR hi, ?_⟩
    have htailcount : largeUsed k t R1 ≤ 1 := by
      have hh := hcount
      rw [hsplit] at hh
      simp only [largeUsed, mass, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hh
      simp only [largeWeight, if_pos hi] at hh
      change (R1.map (largeWeight k t)).sum ≤ 1
      omega
    have hWsplit : W = (F ++ [c] ++ R0 ++ [i]) ++ R1 := by
      simp only [W, hsplit, List.append_assoc]
    have hlowi : B < mass (s k t) (F ++ [c] ++ R0 ++ [i]) := by
      by_contra hcut
      obtain ⟨hv, _, _, _, _, hj⟩ :=
        FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
          k t hk p (F ++ [c] ++ R0 ++ [i]) R1 hpositive hnlarge hexpand
          (hWsplit ▸ hW) (hWsplit ▸ hpunused) (hWsplit ▸ hnunused)
          (by dsimp only [B, P] at *; omega) (by omega)
      rw [← hWsplit] at hj
      exact (not_lt_of_ge (hmin _ hv)) hj
    omega
  obtain ⟨L, _, hv, _, _, _, _, _, _, _, _, _, _, hj, _, _, _⟩ :=
    actualSource_fresh_negative_small_half_exchange_full k t hk n b c F R D μ
      (by simpa only [W] using hW) (by simpa only [W] using hnunused)
      (by simpa only [W] using hb) hnval hbval hcval hμ hμQ hD
      hDZ (by simpa only [W] using (show
        D - μ ≤ mass (s k t) W by omega)) hboundary
  exact (not_lt_of_ge (hmin _ hv)) hj

end D5.S3.Combinatorics.Circle.FreshNegativeSmallHalfConsumer
