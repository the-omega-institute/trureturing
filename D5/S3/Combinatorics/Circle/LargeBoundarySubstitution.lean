/- GID: D5/S3/Combinatorics/Circle/LargeBoundarySubstitution
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/LargeBoundarySubstitution
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Order.Prod.Lex.Basic]
   utility: none
   digest: Whole-suffix LARGE boundaries support positive substitution and a compatible negative prefix pair exchange. -/
module
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
public import D5.S3.Combinatorics.Circle.LargeSkeletonOrdering

/-! # Whole-suffix LARGE boundary exchanges

Replace one positive LARGE by a smaller unused positive LARGE. Only the old
LARGE boundaries of the WHOLE suffix and its endpoint are measured. Complete
SMALL batches are constructed, not supplied, and every LARGE in that suffix keeps its
physical order. A second exchange replaces a negative prefix occurrence c and
the native x by n,p, reordering its compatible intervening block and repairing
the same whole suffix, with nonnegative shift including zero. These are
conditional exchanges, not a full C3.1 proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.LargeBoundarySubstitution
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering TwoOppositeLargeExchange

/-- Derive both retained LARGE boundaries after the downward shift, then use
LargeSkeletonOrdering's single complete-SMALL-batch scan. The old strip bounds
supply the upper bounds; the sign-specific boundary hypothesis and LARGE
magnitude supply both lower bounds. No shifted old SMALL prefix is required. -/
private theorem reconstruct_suffix
    (k t : ℕ) (hk : 3 ≤ k) (δ : ℤ) (hδ : 0 ≤ δ) (hδQ : δ < Q k)
    (B T : List (Fin k)) (h : ℤ)
    (hT : ∀ i ∈ T, |s k t i| < Q k)
    (hold : InStrip (s k t) (C k) h (T ++ B))
    (hstart : 0 ≤ h - δ ∧ h - δ ≤ C k)
    (hend : 0 ≤ h + mass (s k t) (T ++ B) - δ ∧
      h + mass (s k t) (T ++ B) - δ ≤ C k)
    (hboundary : ∀ (B0 : List (Fin k)) (i : Fin k) (B1 : List (Fin k)),
      T ++ B = B0 ++ [i] ++ B1 → Large k t i →
      (s k t i < 0 → δ ≤ h + mass (s k t) B0 + s k t i) ∧
      (0 < s k t i → δ ≤ h + mass (s k t) B0)) :
    ∃ E : List (Fin k), E.Perm (T ++ B) ∧
      E.filter (fun i => decide (Large k t i)) =
        (T ++ B).filter (fun i => decide (Large k t i)) ∧
      InStrip (s k t) (C k) (h - δ) E := by
  classical
  obtain ⟨hQ, _, hC, _, _⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change C k = 2 * Q k - 1 at hC
  have hshifted : ∀ (B0 : List (Fin k)) (i : Fin k) (B1 : List (Fin k)),
      T ++ B = B0 ++ [i] ++ B1 → Q k ≤ |s k t i| →
      (0 ≤ (h - δ) + mass (s k t) B0 ∧
        (h - δ) + mass (s k t) B0 ≤ C k) ∧
      (0 ≤ (h - δ) + mass (s k t) B0 + s k t i ∧
        (h - δ) + mass (s k t) B0 + s k t i ≤ C k) := by
    intro B0 i B1 hsplit hi
    obtain ⟨_, hsTail⟩ := strip_split B0 ([i] ++ B1)
      (by simpa only [hsplit, List.append_assoc] using hold)
    have hsTail' : InStrip (s k t) (C k) (h + mass (s k t) B0) (i :: B1) := by
      simpa only [List.cons_append, List.nil_append] using hsTail
    have hdep : 0 ≤ h + mass (s k t) B0 ∧
        h + mass (s k t) B0 ≤ C k := by
      simpa only [List.take_zero, List.map_nil, List.sum_nil, add_zero]
        using inStrip_prefix hsTail' 0
    have harr : 0 ≤ h + mass (s k t) B0 + s k t i ∧
        h + mass (s k t) B0 + s k t i ≤ C k := by
      simpa only [List.take_succ_cons, List.take_zero, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        using inStrip_prefix hsTail' 1
    have hlow := hboundary B0 i B1 hsplit hi
    by_cases hn : s k t i < 0
    · have hm : Q k ≤ -s k t i := by
        simpa only [abs_of_neg hn] using hi
      have hl := hlow.1 hn
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    · have hp : 0 < s k t i := by
        rw [abs_of_nonneg (by omega)] at hi
        omega
      have hl := hlow.2 hp
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  apply LargeSkeletonOrdering.exists_order_preserving_large (s k t) (Q k) (C k)
    (by omega) (by omega) (T ++ B) (h - δ) hstart
  · change 0 ≤ (h - δ) + mass (s k t) (T ++ B) ∧
      (h - δ) + mass (s k t) (T ++ B) ≤ C k
    constructor <;> omega
  · exact hshifted

/-- One-for-one physical substitution with arbitrary mixed LARGE suffix.
Each boundary premise measures the ORIGINAL zero-start word at that literal
occurrence. No condition is imposed on the old SMALL prefixes. -/
theorem actualSource_largeBoundary_substitution_full
    (k t : ℕ) (hk : 3 ≤ k) (A B : List (Fin k)) (y p : Fin k)
    (hW : Legal k t (A ++ [y] ++ B))
    (hp : p ∉ A ++ [y] ++ B)
    (hpLarge : Q k ≤ s k t p)
    (hpy : s k t p < s k t y)
    (hδQ : s k t y - s k t p < Q k)
    (hend : s k t y - s k t p ≤ mass (s k t) (A ++ [y] ++ B))
    (hboundary : ∀ (B0 : List (Fin k)) (i : Fin k) (B1 : List (Fin k)),
      B = B0 ++ [i] ++ B1 → Q k ≤ |s k t i| →
      (s k t i < 0 → s k t y - s k t p ≤
        mass (s k t) (A ++ [y] ++ B0 ++ [i])) ∧
      (0 < s k t i → s k t y - s k t p ≤
        mass (s k t) (A ++ [y] ++ B0))) :
    ∃ Bprime : List (Fin k), Bprime.Perm B ∧
      Bprime.filter (fun i => decide (Large k t i)) =
        B.filter (fun i => decide (Large k t i)) ∧
      (let W := A ++ [y] ++ B
       let V := A ++ [p] ++ Bprime
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧ mass (s k t) (V.take j) ≤ C k) ∧
       V.Nodup ∧ Inventory k t W V [p] [y] ∧
       (V ++ [y]).Perm (W ++ [p]) ∧
       G k t V = G k t W ∧ U V = U W ∧
       remainingSmall t V = remainingSmall t W ∧
       H k t V + 3 ^ (s k t y).natAbs = H k t W + 3 ^ (s k t p).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = mass (s k t) W - (s k t y - s k t p) ∧
       (0 ≤ mass (s k t) V ∧ mass (s k t) V ≤ C k) ∧
       remainingMass (s k t) V = -(mass (s k t) W - (s k t y - s k t p))) := by
  classical
  let f := s k t
  let W := A ++ [y] ++ B
  let δ := f y - f p
  let a := mass f A
  let h := a + f y
  have hδ : 0 < δ := by dsimp only [δ, f]; omega
  have hp0 : 0 < f p := by
    have hQ := (source_geometry hk).1
    change 2 ≤ Q k at hQ
    dsimp only [f]
    omega
  have hy0 : 0 < f y := lt_trans hp0 hpy
  have hpL : Large k t p := by
    change Q k ≤ |f p|
    simpa only [abs_of_pos hp0] using hpLarge
  have hyL : Large k t y := by
    change Q k ≤ |f y|
    rw [abs_of_pos hy0]
    change Q k ≤ f p at hpLarge
    omega
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsTail⟩ := strip_split A ([y] ++ B)
    (by simpa only [W, List.append_assoc] using hsW)
  have ha : 0 ≤ a ∧ a ≤ C k := by
    simpa only [List.take_zero, List.map_nil, List.sum_nil, add_zero, zero_add, a, mass]
      using inStrip_prefix hsTail 0
  have hh : 0 ≤ h ∧ h ≤ C k := by
    simpa only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add,
      h, a, mass] using inStrip_prefix hsTail 1
  have hstart : 0 ≤ h - δ ∧ h - δ ≤ C k := by
    have heq : h - δ = a + f p := by dsimp only [h, δ]; ring
    constructor <;> omega
  have hmassW : mass f W = h + mass f B := by
    simp only [W, h, a, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  have hend' : 0 ≤ h + mass f ([] ++ B) - δ ∧
      h + mass f ([] ++ B) - δ ≤ C k := by
    have hw := hW.2 W.length
    have hw' : mass f W ≤ C k := by simpa only [W, List.take_length] using hw.2
    change δ ≤ mass f W at hend
    simp only [List.nil_append]
    rw [← hmassW]
    constructor <;> omega
  have hboundary' : ∀ (B0 : List (Fin k)) (i : Fin k) (B1 : List (Fin k)),
      [] ++ B = B0 ++ [i] ++ B1 → Large k t i →
      (f i < 0 → δ ≤ h + mass f B0 + f i) ∧
      (0 < f i → δ ≤ h + mass f B0) := by
    intro B0 i B1 hsplit hi
    have hb := hboundary B0 i B1 (by simpa only [List.nil_append] using hsplit) hi
    simpa only [f, δ, h, a, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero] using hb
  obtain ⟨Bprime, hB, hBlarge, hsB⟩ := reconstruct_suffix k t hk δ (le_of_lt hδ)
    hδQ B [] h (by simp)
    (by change InStrip f (C k) h B
        have ht := hsTail.2.2
        change InStrip f (C k) ((0 + mass f A) + f y) B at ht
        simpa only [zero_add, h, a] using ht) hstart hend' hboundary'
  have hB' : Bprime.Perm B := by simpa only [List.nil_append] using hB
  have hBlarge' : Bprime.filter (fun i => decide (Large k t i)) =
      B.filter (fun i => decide (Large k t i)) := by
    simpa only [List.nil_append] using hBlarge
  let V := A ++ [p] ++ Bprime
  have hsingle : InStrip f (C k) a [p] := by
    change 0 ≤ a ∧ a ≤ C k ∧ 0 ≤ a + f p ∧ a + f p ≤ C k
    have heq : a + f p = h - δ := by dsimp only [h, δ]; ring
    exact ⟨ha.1, ha.2, heq.symm ▸ hstart⟩
  have hsAp : InStrip f (C k) 0 (A ++ [p]) :=
    inStrip_append hsA (by simpa only [zero_add, a, mass] using hsingle)
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsAp
    have heq : 0 + mass f (A ++ [p]) = h - δ := by
      simp only [h, δ, a, mass, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add]
      ring
    change InStrip f (C k) (0 + mass f (A ++ [p])) Bprime
    rw [heq]
    exact hsB
  have hperm : (V ++ [y]).Perm (W ++ [p]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hb := hB'.count_eq i
    simp only [V, W, List.count_append, List.count_cons, List.count_nil]
    omega
  have hyW : y ∈ W := by simp [W]
  have inv : Inventory k t W V [p] [y] := inventory_of_perm hk t W V [p] [y] hW.1
    (by simp)
    (by intro i hi; obtain rfl := List.mem_singleton.mp hi; exact hp)
    (by intro i hi; obtain rfl := List.mem_singleton.mp hi; exact hyW)
    (by intro i hi; obtain rfl := List.mem_singleton.mp hi; exact hpL) hperm
  have hg := inv.largeBalance
  have hu := inv.countBalance
  have he := inv.energyBalance
  simp [largeWeight, energyWeight, hpL, hyL] at hg hu he
  change H k t V + 3 ^ (f y).natAbs = H k t W + 3 ^ (f p).natAbs at he
  have hn : (f p).natAbs < (f y).natAbs := by
    exact_mod_cast (show ((f p).natAbs : ℤ) < ((f y).natAbs : ℤ) by
      simpa only [Int.natCast_natAbs, abs_of_pos hp0, abs_of_pos hy0] using hpy)
  have hpower : (3 : ℕ) ^ (f p).natAbs < 3 ^ (f y).natAbs :=
    pow_lt_pow_right₀ (by decide : (1 : ℕ) < 3) hn
  have hH : H k t V < H k t W := by omega
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩
  have hsmall : remainingSmall t V = remainingSmall t W := by
    simpa [Finset.filter_singleton, hyL] using inv.smallPartition
  have hEnd : mass f V = mass f W - δ := by
    have hm : mass f V + f y = mass f W + f p := by
      simpa only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        using inv.sourceBalance
    dsimp only [δ]
    omega
  have hV := legal_of_strip inv.nodup hsV
  have hVEnd : 0 ≤ mass f V ∧ mass f V ≤ C k := by
    simpa only [List.take_length] using hV.2 V.length
  have hComplement : remainingMass f V = -(mass f W - δ) := by
    rw [inv.complementSum, hEnd]
  exact ⟨Bprime, hB', hBlarge', hV, hsV, hV.2, inv.nodup, inv, hperm,
    hg, hu, hsmall, he, hH, hJ, hEnd, hVEnd, hComplement⟩

/-- Replace an actual negative prefix occurrence c and the native positive x
by the unused native pair n,p. The whole intervening K is pairwise compatible,
but may contain LARGE of either sign. Its order is constructed anew; only the
LARGE order in the WHOLE suffix B is preserved. With M=-s(c), the downward
shift is e=P-M, including e=0. Every boundary measures the OLD zero-start word.
No first-LARGE selection, supplied ordered batch or replacement legality is assumed. -/
theorem actualSource_negativePrefix_pair_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p c : Fin k) (A0 K B : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (A0 ++ [c] ++ K ++ [hit k 2 p] ++ B))
    (hpunused : p ∉ A0 ++ [c] ++ K ++ [hit k 2 p] ++ B)
    (hnunused : hit k 1 p ∉ A0 ++ [c] ++ K ++ [hit k 2 p] ++ B)
    (hM : |s k t (hit k 1 p)| ≤ -s k t c ∧ -s k t c ≤ s k t p)
    (hcompatible : ∀ i ∈ K, ∀ j ∈ K,
      0 < s k t i → s k t j < 0 → s k t i - s k t j ≤ C k)
    (hend : s k t p + s k t c ≤
      mass (s k t) (A0 ++ [c] ++ K ++ [hit k 2 p] ++ B))
    (hboundary : ∀ (B0 : List (Fin k)) (i : Fin k) (B1 : List (Fin k)),
      B = B0 ++ [i] ++ B1 → Q k ≤ |s k t i| →
      (s k t i < 0 → s k t p + s k t c ≤
        mass (s k t) (A0 ++ [c] ++ K ++ [hit k 2 p] ++ B0 ++ [i])) ∧
      (0 < s k t i → s k t p + s k t c ≤
        mass (s k t) (A0 ++ [c] ++ K ++ [hit k 2 p] ++ B0))) :
    ∃ Kprime Bprime : List (Fin k), Kprime.Perm K ∧ Bprime.Perm B ∧
      Bprime.filter (fun i => decide (Large k t i)) =
        B.filter (fun i => decide (Large k t i)) ∧
      (let n := hit k 1 p
       let x := hit k 2 p
       let W := A0 ++ [c] ++ K ++ [x] ++ B
       let V := A0 ++ [n] ++ Kprime ++ [p] ++ Bprime
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧ mass (s k t) (V.take j) ≤ C k) ∧
       V.Nodup ∧ Inventory k t W V [n, p] [c, x] ∧
       (V ++ [c, x]).Perm (W ++ [n, p]) ∧
       G k t V = G k t W ∧ U V = U W ∧
       remainingSmall t V = remainingSmall t W ∧
       H k t V + 3 ^ (s k t c).natAbs + 3 ^ (s k t x).natAbs =
         H k t W + 3 ^ (s k t n).natAbs + 3 ^ (s k t p).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = mass (s k t) W - (s k t p + s k t c) ∧
       (0 ≤ mass (s k t) V ∧ mass (s k t) V ≤ C k) ∧
       remainingMass (s k t) V = -(mass (s k t) W - (s k t p + s k t c))) := by
  classical
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := A0 ++ [c] ++ K ++ [x] ++ B
  let P := f p
  let D := |f n|
  let r := f x
  let M := -f c
  let e := P - M
  let a := mass f A0
  let u := a - M
  let q := u + mass f K
  let h := q + r
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, _, hC, hN0, hodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change C k = 2 * Q k - 1 at hC
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = |f x| := by
    simpa [f, x, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : D < P := by
    simpa only [D, P, f, n, abs_of_pos hpositive] using geo.strictOrder.1
  have hPr : P < r := by
    have hh := geo.strictOrder.2
    change |f p| < |f x| at hh
    rw [abs_of_pos hpositive, ← hxval] at hh
    exact hh
  have hr : r = 2 * P - D := by
    have h1 := geo.firstEquation
    have h2 := geo.secondEquation
    rw [abs_of_pos hpositive] at h1 h2
    change D = N k - 2 * P at h1
    change |f x| = 4 * P - N k at h2
    rw [← hxval] at h2
    change f x = 2 * P - D
    omega
  have hrC : r ≤ C k := by
    -- Use the actual centered source bound, without source-value injectivity.
    have hb' : |s k t x| ≤ C k := abs_le.mpr (centered_bounds hN0 hodd _)
    change |f x| ≤ C k at hb'
    rw [← hxval] at hb'
    exact hb'
  have hD : Q k ≤ D := hnlarge
  have hD0 : 0 < D := by omega
  have hP0 : 0 < P := hpositive
  change D ≤ M ∧ M ≤ P at hM
  have hcneg : f c < 0 := by dsimp only [M] at hM; omega
  have hpL : Large k t p := geo.pLarge
  have hnL : Large k t n := geo.nLarge
  have hxL : Large k t x := geo.xLarge
  have hcL : Large k t c := by
    change Q k ≤ |f c|
    rw [abs_of_neg hcneg]
    change Q k ≤ M
    omega
  have he : 0 ≤ e ∧ e ≤ P - D ∧ e < Q k := by
    dsimp only [e]
    omega
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsRest⟩ := strip_split A0 ([c] ++ K ++ [x] ++ B)
    (by simpa only [W, List.append_assoc] using hsW)
  have hsRest' : InStrip f (C k) a (c :: (K ++ [x] ++ B)) := by
    simpa only [zero_add, a, List.cons_append, List.nil_append] using hsRest
  have ha : 0 ≤ a ∧ a ≤ C k := ⟨hsRest'.1, hsRest'.2.1⟩
  have hsKxB : InStrip f (C k) u (K ++ [x] ++ B) := by
    have hu : a + f c = u := by dsimp only [u, M]; ring
    simpa only [hu] using hsRest'.2.2
  have hu : 0 ≤ u ∧ u ≤ C k := by
    simpa only [List.take_zero, List.map_nil, List.sum_nil, add_zero]
      using inStrip_prefix hsKxB 0
  obtain ⟨_, hsxB⟩ := strip_split K ([x] ++ B)
    (by simpa only [List.append_assoc] using hsKxB)
  have hsxB' : InStrip f (C k) q (x :: B) := by
    simpa only [q, List.cons_append, List.nil_append] using hsxB
  have hq : 0 ≤ q ∧ q ≤ C k := ⟨hsxB'.1, hsxB'.2.1⟩
  have hsBold : InStrip f (C k) h B := by
    simpa only [h, r] using hsxB'.2.2
  have hh : 0 ≤ h ∧ h ≤ C k := by
    simpa only [List.take_zero, List.map_nil, List.sum_nil, add_zero]
      using inStrip_prefix hsBold 0
  have hnewStart : 0 ≤ a - D ∧ a - D ≤ C k := by
    dsimp only [u] at hu
    constructor <;> omega
  have hKjoin : (a - D) + mass f K = q + M - D := by
    dsimp only [q, u]
    ring
  have hpjoin : q + M - D + P = h - e := by
    dsimp only [h, e]
    omega
  have hKend : 0 ≤ (a - D) + mass f K ∧ (a - D) + mass f K ≤ C k := by
    rw [hKjoin]
    constructor <;> omega
  obtain ⟨Kprime, hK, hsK⟩ := exists_order_between f K (C k) (a - D)
    hnewStart hKend hcompatible
  have hmK : mass f Kprime = mass f K := (hK.map f).sum_eq
  have hstart : 0 ≤ h - e ∧ h - e ≤ C k := by
    constructor <;> omega
  have hmassW : mass f W = h + mass f B := by
    simp only [W, h, q, u, a, r, M, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, sub_neg_eq_add]
  have hend' : 0 ≤ h + mass f ([] ++ B) - e ∧
      h + mass f ([] ++ B) - e ≤ C k := by
    have hw : mass f W ≤ C k := by
      simpa only [W, x, List.take_length] using (hW.2 W.length).2
    have heW : e ≤ mass f W := by
      change P + f c ≤ mass f W at hend
      simpa only [e, M, sub_neg_eq_add] using hend
    simp only [List.nil_append]
    rw [← hmassW]
    constructor <;> omega
  have hboundary' : ∀ (B0 : List (Fin k)) (i : Fin k) (B1 : List (Fin k)),
      [] ++ B = B0 ++ [i] ++ B1 → Large k t i →
      (f i < 0 → e ≤ h + mass f B0 + f i) ∧
      (0 < f i → e ≤ h + mass f B0) := by
    intro B0 i B1 hsplit hi
    have hb := hboundary B0 i B1 (by simpa only [List.nil_append] using hsplit) hi
    simpa only [e, P, M, h, q, u, a, r, f, x, mass, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero, sub_neg_eq_add, add_assoc] using hb
  obtain ⟨Bprime, hB, hBlarge, hsB⟩ := reconstruct_suffix k t hk e he.1 he.2.2 B [] h
    (by simp) (by simpa only [List.nil_append] using hsBold) hstart hend' hboundary'
  have hB' : Bprime.Perm B := by simpa only [List.nil_append] using hB
  have hBlarge' : Bprime.filter (fun i => decide (Large k t i)) =
      B.filter (fun i => decide (Large k t i)) := by
    simpa only [List.nil_append] using hBlarge
  let V := A0 ++ [n] ++ Kprime ++ [p] ++ Bprime
  have hsPB : InStrip f (C k) (q + M - D) (p :: Bprime) := by
    change 0 ≤ q + M - D ∧ q + M - D ≤ C k ∧
      InStrip f (C k) (q + M - D + P) Bprime
    rw [hpjoin]
    exact ⟨by omega, by omega, hsB⟩
  have hsKPB : InStrip f (C k) (a - D) (Kprime ++ [p] ++ Bprime) := by
    have hs := inStrip_append hsK (show InStrip f (C k)
        ((a - D) + mass f Kprime) (p :: Bprime) from by
      rw [hmK, hKjoin]
      exact hsPB)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs
  have hsNKPB : InStrip f (C k) a ([n] ++ Kprime ++ [p] ++ Bprime) := by
    change 0 ≤ a ∧ a ≤ C k ∧
      InStrip f (C k) (a + f n) (Kprime ++ [p] ++ Bprime)
    rw [hnval]
    have hnstart : a + -D = a - D := by ring
    rw [hnstart]
    exact ⟨ha.1, ha.2, hsKPB⟩
  have hsV : InStrip f (C k) 0 V := by
    have hs := inStrip_append hsA (by
      simpa only [zero_add, a, mass] using hsNKPB)
    simpa only [V, List.append_assoc] using hs
  have hI : [n, p].Nodup := by
    have hnp : n ≠ p := by intro heq; have hv := congrArg f heq; omega
    simp [hnp]
  have hIW (i : Fin k) (hi : i ∈ [n, p]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hnunused
    · exact hpunused
  have hRold (i : Fin k) (hi : i ∈ [c, x]) : i ∈ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [W]
  have hIL (i : Fin k) (hi : i ∈ [n, p]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hnL
    · exact hpL
  have hperm : (V ++ [c, x]).Perm (W ++ [n, p]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hk' := hK.count_eq i
    have hb' := hB'.count_eq i
    simp only [V, W, List.count_append, List.count_cons, List.count_nil]
    omega
  -- Old Nodup and whole-word freshness are sufficient: inventory_of_perm
  -- derives all physical disjointness, including distinct returned c,x.
  have inv : Inventory k t W V [n, p] [c, x] :=
    inventory_of_perm hk t W V [n, p] [c, x] hW.1 hI hIW hRold hIL hperm
  have hIlarge : largeUsed k t [n, p] = 2 := by
    simp [largeUsed, mass, largeWeight, hnL, hpL]
  have hRlarge : largeUsed k t [c, x] = 2 := by
    simp [largeUsed, mass, largeWeight, hcL, hxL]
  have hg : G k t V = G k t W := by
    have hb := inv.largeBalance
    rw [hIlarge, hRlarge] at hb
    omega
  have huCount : U V = U W := by
    have hb := inv.countBalance
    simp only [List.length_cons, List.length_nil] at hb
    omega
  have hRenergy : H k t [c, x] = 3 ^ (f c).natAbs + 3 ^ (f x).natAbs := by
    simp [H, mass, energyWeight, hcL, hxL, f, s]
  have hIenergy : H k t [n, p] = 3 ^ (f n).natAbs + 3 ^ (f p).natAbs := by
    simp [H, mass, energyWeight, hnL, hpL, f, s]
  have hEnergy : H k t V + 3 ^ (f c).natAbs + 3 ^ (f x).natAbs =
      H k t W + 3 ^ (f n).natAbs + 3 ^ (f p).natAbs := by
    have hb := inv.energyBalance
    rw [hRenergy, hIenergy] at hb
    simpa only [Nat.add_assoc] using hb
  have hH : H k t V < H k t W := by
    have hb := geo.energy
    change 3 ^ (f p).natAbs + 3 ^ (f n).natAbs < 3 ^ (f x).natAbs at hb
    have hsum : H k t V + (3 ^ (f c).natAbs + 3 ^ (f x).natAbs) =
        H k t W + (3 ^ (f n).natAbs + 3 ^ (f p).natAbs) := by
      simpa only [Nat.add_assoc] using hEnergy
    have hremove : (3 : ℕ) ^ (f n).natAbs + 3 ^ (f p).natAbs <
        3 ^ (f c).natAbs + 3 ^ (f x).natAbs := by
      calc
        _ < 3 ^ (f x).natAbs := by simpa only [Nat.add_comm] using hb
        _ ≤ _ := Nat.le_add_left _ _
    have htot := Nat.add_lt_add_left hremove (H k t W)
    rw [← hsum] at htot
    exact Nat.lt_of_add_lt_add_right htot
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩
  have hRfilter : ([c, x] : List (Fin k)).toFinset.filter (fun i => ¬ Large k t i) = ∅ := by
    ext i
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl) hn
    · exact hn hcL
    · exact hn hxL
  have hsmall : remainingSmall t V = remainingSmall t W := by
    simpa only [hRfilter, Finset.union_empty] using inv.smallPartition
  have hEnd : mass f V = mass f W - e := by
    have hb := inv.sourceBalance
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero] at hb
    change mass f V + (f c + r) = mass f W + (f n + P) at hb
    rw [hnval] at hb
    dsimp only [e, M]
    omega
  have hV := legal_of_strip inv.nodup hsV
  have hVEnd : 0 ≤ mass f V ∧ mass f V ≤ C k := by
    simpa only [List.take_length] using hV.2 V.length
  have hComplement : remainingMass f V = -(mass f W - e) := by
    rw [inv.complementSum, hEnd]
  have heq : e = f p + f c := by dsimp only [e, P, M]; ring
  rw [heq] at hEnd hComplement
  exact ⟨Kprime, Bprime, hK, hB', hBlarge', hV, hsV, hV.2, inv.nodup,
    inv, hperm, hg, huCount, hsmall, hEnergy, hH, hJ, hEnd, hVEnd, hComplement⟩

end D5.S3.Combinatorics.Circle.LargeBoundarySubstitution
