/- GID: D5/S3/Combinatorics/Circle/TerminalLargeSubstitution
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TerminalLargeSubstitution
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Strict terminal same-sign physical substitution derives its endpoint from old append blocking. -/
module
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange

/-! Strict substitution uses D < Z and retains every physical SMALL label.
The original append failure derives the new endpoint; equal values do not imply strict descent. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.TerminalLargeSubstitution
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering TwoOppositeLargeExchange
open scoped BigOperators
local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.take_zero, List.take_succ_cons, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero, zero_add] at *) <;> omega))

theorem blocked_gate {k t : ℕ} {W : List (Fin k)} {u : Fin k}
    (hW : Legal k t W) (hu : u ∉ W) (hb : ¬ Legal k t (W ++ [u])) :
    ¬ (0 ≤ mass (s k t) W + s k t u ∧ mass (s k t) W + s k t u ≤ C k) := by
  intro hg
  have hs := strip_of_legal hW
  have hh : 0 ≤ mass (s k t) W ∧ mass (s k t) W ≤ C k := by
    simpa [mass] using inStrip_prefix hs W.length
  have hsingle : InStrip (s k t) (C k) (mass (s k t) W) [u] := ⟨hh.1, hh.2, hg⟩
  have hv := inStrip_append hs (by simpa [mass] using hsingle)
  have hn : (W ++ [u]).Nodup := hW.1.append (by simp) (List.disjoint_left.mpr (by
    intro q hq hqu
    have he : q = u := List.mem_singleton.mp hqu
    subst q
    exact hu hq))
  exact hb (legal_of_strip hn hv)

private theorem exponent_lt {a b : ℤ} (hab : |a| < |b|) :
    (3 : ℕ) ^ a.natAbs < (3 : ℕ) ^ b.natAbs := by
  have hn : a.natAbs < b.natAbs := by
    exact_mod_cast (show (a.natAbs : ℤ) < (b.natAbs : ℤ) by
      simpa only [Int.natCast_natAbs] using hab)
  exact pow_lt_pow_right₀ (by decide : (1 : ℕ) < 3) hn

/-- Complete terminal exchange, including both exact disjoint physical partitions,
all natural takes, unchanged G/U and SMALL complement, and the exact energy balance. -/
theorem actualSource_terminal_sameSign_substitution_full
    (k t : ℕ) (hk : 3 ≤ k)
    (A T : List (Fin k)) (z u : Fin k)
    (hW : Legal k t (A ++ [z] ++ T))
    (hsmall : ∀ q ∈ T, |s k t q| < Q k)
    (hu : u ∉ A ++ [z] ++ T)
    (hularge : Q k ≤ |s k t u|)
    (hsame : 0 < s k t u * s k t z)
    (hmag : |s k t u| < |s k t z|)
    (hblocked : ¬ Legal k t ((A ++ [z] ++ T) ++ [u])) :
    ∃ E : List (Fin k), E.Perm T ∧
      (let W := A ++ [z] ++ T
       let V := A ++ [u] ++ E
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       Inventory k t W V [u] [z] ∧
       G k t V = G k t W ∧ U V = U W ∧
       H k t V + 3 ^ (s k t z).natAbs = H k t W + 3 ^ (s k t u).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = mass (s k t) W - s k t z + s k t u ∧
       remainingSmall t V = remainingSmall t W) := by
  classical
  let f := s k t
  let W := A ++ [z] ++ T
  let a := mass f A
  let b := a + f u
  let e := b + mass f T
  change Large k t u at hularge
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsTail⟩ := strip_split A ([z] ++ T) (by simpa [W, List.append_assoc] using hsW)
  have ha := inStrip_prefix hsTail 0
  have haz := inStrip_prefix hsTail 1
  have hh := inStrip_prefix hsW W.length
  simp only [List.cons_append, List.nil_append, List.take_zero, List.take_succ_cons,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add] at ha haz
  change 0 ≤ a ∧ a ≤ C k at ha
  change 0 ≤ a + f z ∧ a + f z ≤ C k at haz
  have hh' : 0 ≤ mass f W ∧ mass f W ≤ C k := by simpa [mass] using hh
  have hblock : ¬ (0 ≤ mass f W + f u ∧ mass f W + f u ≤ C k) := blocked_gate hW hu hblocked
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  have hbound (q : Fin k) : |f q| ≤ C k := abs_le.mpr (centered_bounds hN0 hodd _)
  have hzlarge : Large k t z := by unfold Large; ((try dsimp only [f, W, a, b, e] at *); source_arith)
  have heq : e = mass f W - f z + f u := by simp [e, b, a, W, mass]; ring
  have hgate : (0 ≤ b ∧ b ≤ C k) ∧ (0 ≤ e ∧ e ≤ C k) := by
    rcases mul_pos_iff.mp hsame with ⟨hup, hzp⟩ | ⟨hun, hzn⟩
    · change 0 < f u at hup
      change 0 < f z at hzp
      have hmag' : f u < f z := by
        have hm := hmag
        change |f u| < |f z| at hm
        simpa only [abs_of_pos hup, abs_of_pos hzp] using hm
      have hZ := hbound z
      rw [abs_of_pos hzp] at hZ
      have hblocked' : C k - f u < mass f W := by ((try dsimp only [f, W, a, b, e] at *); source_arith)
      dsimp [b]
      exact ⟨⟨by ((try dsimp only [f, W, a, b, e] at *); source_arith), by ((try dsimp only [f, W, a, b, e] at *); source_arith)⟩, ⟨by ((try dsimp only [f, W, a, b, e] at *); source_arith), by ((try dsimp only [f, W, a, b, e] at *); source_arith)⟩⟩
    · change f u < 0 at hun
      change f z < 0 at hzn
      have hmag' : f z < f u := by
        have hm := hmag
        change |f u| < |f z| at hm
        rw [abs_of_neg hun, abs_of_neg hzn] at hm
        ((try dsimp only [f, W, a, b, e] at *); source_arith)
      have hZ := hbound z
      rw [abs_of_neg hzn] at hZ
      have hblocked' : mass f W < -f u := by ((try dsimp only [f, W, a, b, e] at *); source_arith)
      dsimp [b]
      exact ⟨⟨by ((try dsimp only [f, W, a, b, e] at *); source_arith), by ((try dsimp only [f, W, a, b, e] at *); source_arith)⟩, ⟨by ((try dsimp only [f, W, a, b, e] at *); source_arith), by ((try dsimp only [f, W, a, b, e] at *); source_arith)⟩⟩
  have hcompatible : ∀ p ∈ T, ∀ n ∈ T, 0 < f p → f n < 0 → f p - f n ≤ C k := by
    intro p hp n hn hpp hnn
    have hp' := hsmall p hp
    have hn' := hsmall n hn
    change |f p| < Q k at hp'
    change |f n| < Q k at hn'
    rw [abs_of_pos hpp] at hp'
    rw [abs_of_neg hnn] at hn'
    ((try dsimp only [f, W, a, b, e] at *); source_arith)
  obtain ⟨E, hE, hsE⟩ := exists_order_between f T (C k) b hgate.1 hgate.2 hcompatible
  let V := A ++ [u] ++ E
  have hsingle : InStrip f (C k) a [u] := ⟨ha.1, ha.2, hgate.1⟩
  have hsAu : InStrip f (C k) 0 (A ++ [u]) :=
    inStrip_append hsA (by simpa [a, mass] using hsingle)
  have hVstrip : InStrip f (C k) 0 V := by
    apply inStrip_append hsAu
    simpa [b, a, mass] using hsE
  have hzW : z ∈ W := by simp [W]
  have hperm : (V ++ [z]).Perm (W ++ [u]) := by
    apply List.perm_iff_count.mpr
    intro q
    have he := hE.count_eq q
    simp only [V, W, List.count_append, List.count_cons, List.count_nil] at *
    ((try dsimp only [f, W, a, b, e] at *); source_arith)
  have inv : Inventory k t W V [u] [z] := inventory_of_perm hk t W V [u] [z] hW.1
    (by simp) (by intro q hq; have he : q = u := List.mem_singleton.mp hq; simpa [he, W] using hu)
    (by intro q hq; have he : q = z := List.mem_singleton.mp hq; simpa [he] using hzW)
    (by intro q hq; have he : q = u := List.mem_singleton.mp hq; simpa [he, W] using hularge) hperm
  have hg := inv.largeBalance
  have hc := inv.countBalance
  have he := inv.energyBalance
  simp [largeWeight, energyWeight, hularge, hzlarge] at hg he hc
  have hpower := exponent_lt hmag
  have hH : H k t V < H k t W := by ((try dsimp only [f, W, a, b, e] at *); source_arith)
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨by ((try dsimp only [f, W, a, b, e] at *); source_arith), Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩
  have hend : mass f V = mass f W - f z + f u := by
    have hm := (hE.map f).sum_eq
    simp only [V, W, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    ((try dsimp only [f, W, a, b, e] at *); source_arith)
  have hsmallRem : remainingSmall t V = remainingSmall t W := by
    simpa [Finset.filter_singleton, hzlarge] using inv.smallPartition
  exact ⟨E, hE, legal_of_strip inv.nodup hVstrip, hVstrip, inv, by ((try dsimp only [f, W, a, b, e] at *); source_arith), by ((try dsimp only [f, W, a, b, e] at *); source_arith),
    he, hH, hJ, hend, hsmallRem⟩


#print axioms D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange.native_geometry
#print axioms D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange.actualSource_twoOpposite_twoStep_full
#print axioms actualSource_terminal_sameSign_substitution_full

end D5.S3.Combinatorics.Circle.TerminalLargeSubstitution
