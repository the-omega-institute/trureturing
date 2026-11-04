/- GID: D5/S3/Combinatorics/Circle/OddHalfParentExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OddHalfParentExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: The actual odd-half child relocates around its old negative parent with exact signed remainder tests. -/
module
public import D5.S3.Combinatorics.Circle.OddHalfParentCore

/-! # The actual negative parent of an odd half

The full original-quantifier Circle C3.1 remains open. All words below carry
physical labels, and Inventory always compares with the original full W.
The actual child can be moved from either side of its parent; both orders
use the same complete-SMALL-batch ordering and physical completion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.OddHalfParentExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open scoped BigOperators

/-- Original-zero HIGH sides: positive arrival and negative departure. B is
an actual old prefix, never a translated start or a new ordered prefix. -/
def HighSides {k t : ℕ} (w : SourceWord k t) (B R : List (Fin k))
    (shift : ℤ) : Prop :=
  ∀ (R0 : List (Fin k)) (i : Fin k) (R1 : List (Fin k)),
    R = R0 ++ [i] ++ R1 → Large k t i →
    (0 < s k t i → mass (s k t) (B ++ R0 ++ [i]) ≤ C k - shift) ∧
    (s k t i < 0 → mass (s k t) (B ++ R0) ≤ C k - shift)

/-- Original-zero LOW sides: positive departure and negative arrival. -/
def LowSides {k t : ℕ} (w : SourceWord k t) (B R : List (Fin k))
    (shift : ℤ) : Prop :=
  ∀ (R0 : List (Fin k)) (i : Fin k) (R1 : List (Fin k)),
    R = R0 ++ [i] ++ R1 → Large k t i →
    (0 < s k t i → shift ≤ mass (s k t) (B ++ R0)) ∧
    (s k t i < 0 → shift ≤ mass (s k t) (B ++ R0 ++ [i]))

/-- The actual post-parent displacement is -kappa in BOTH positional orders.
At kappa=0 the test is vacuous and the ordering proof keeps literal old R. -/
def RemainderTest {k t : ℕ} (w : SourceWord k t) (B R : List (Fin k)) : Prop :=
  (w.kappa < 0 → HighSides w B R (-w.kappa)) ∧
  (0 < w.kappa → LowSides w B R w.kappa)

set_option maxHeartbeats 1400000 in
-- Normalize the exact source equations before the integer remainder bounds.
/-- Exact source inversion and the inherited scalar residual give a sharp
remainder without any new source, placement, cut or SMALL-resource premise. -/
theorem actualSource_oddHalf_sharp_remainder {k t : ℕ}
    (w : SourceWord k t) (h : Residual w) :
    w.theta - w.q = -w.kappa ∧
    8 * w.kappa = 2 * w.D - 5 * w.d - 3 * w.delta ∧
    |8 * w.kappa| < w.d ∧ |w.kappa| < Q k ∧
    0 < w.q ∧ w.q < Q k ∧ s k t w.a = -w.M ∧ 0 < w.D ∧ w.D < w.M := by
  have ar := arithmetic w h
  have heq := ar.parentEquations
  have hnative := ar.native
  have ho := ar.order
  have hc := ar.cap
  have hn := ar.modulus
  have hdef := h.deficit
  have hhigh := h.highD
  have hdelta := h.firstHigh
  have hshift := ar.shift
  have hbase : w.theta - w.q = -w.kappa ∧
      8 * w.kappa = 2 * w.D - 5 * w.d - 3 * w.delta ∧
      -w.d < 8 * w.kappa ∧ 8 * w.kappa < w.d ∧
      -Q k < w.kappa ∧ w.kappa < Q k ∧ 0 < w.q ∧ w.q < Q k := by
    dsimp only [SourceWord.theta, SourceWord.kappa, SourceWord.e,
      SourceWord.tau, SourceWord.d, SourceWord.delta] at *
    omega
  exact ⟨hbase.1, hbase.2.1, abs_lt.mpr ⟨hbase.2.2.1, hbase.2.2.2.1⟩,
    abs_lt.mpr ⟨hbase.2.2.2.2.1, hbase.2.2.2.2.2.1⟩,
    hbase.2.2.2.2.2.2.1, hbase.2.2.2.2.2.2.2, ar.parentValue,
    by have := ar.Qpos; omega, by omega⟩

private theorem old_segment {k t : ℕ} (w : SourceWord k t) (h : Residual w)
    (B R Z : List (Fin k)) (hA : w.A = B ++ R ++ Z) :
    InStrip (s k t) (C k) 0 B ∧
    InStrip (s k t) (C k) (mass (s k t) B) R := by
  have hsA : InStrip (s k t) (C k) 0 w.A :=
    (strip_split w.A ([w.x] ++ w.T0 ++ [w.y] ++ w.ret0)
      (by simpa only [split_word w, SourceWord.F, List.append_assoc]
        using strip_of_legal h.oldLegal)).1
  obtain ⟨hsB, hsRZ⟩ := strip_split B (R ++ Z)
    (by simpa only [hA, List.append_assoc] using hsA)
  exact ⟨hsB, (strip_split R Z (by simpa only [zero_add] using hsRZ)).1⟩

/-- Convert the appropriate computed old side into BOTH new LARGE sides,
then use the existing complete-SMALL-batch engine. No ordering recursion is
introduced. This internal lemma also handles a compatible ENTIRE interval. -/
private theorem order_shift {k t : ℕ} (w : SourceWord k t) (ar : Arithmetic w)
    (B R : List (Fin k)) (shift : ℤ)
    (hsOld : InStrip (s k t) (C k) (mass (s k t) B) R)
    (hstart : 0 ≤ mass (s k t) B + shift ∧ mass (s k t) B + shift ≤ C k)
    (hend : 0 ≤ mass (s k t) B + shift + mass (s k t) R ∧
      mass (s k t) B + shift + mass (s k t) R ≤ C k)
    (horder : Compatible (s k t) (C k) R ∨
      ((0 < shift → HighSides w B R shift) ∧
       (shift < 0 → LowSides w B R (-shift)))) :
    ∃ Rstar : List (Fin k), Rstar.Perm R ∧
      InStrip (s k t) (C k) (mass (s k t) B + shift) Rstar := by
  classical
  by_cases hz : shift = 0
  · exact ⟨R, List.Perm.refl _, by simpa only [hz, add_zero] using hsOld⟩
  rcases horder with hc | ht
  · exact exists_order_between (s k t) R (C k) (mass (s k t) B + shift)
      hstart (by simpa only [mass] using hend) hc
  · have boundaries : ∀ (R0 : List (Fin k)) (i : Fin k) (R1 : List (Fin k)),
        R = R0 ++ [i] ++ R1 → Q k ≤ |s k t i| →
        (0 ≤ (mass (s k t) B + shift) + mass (s k t) R0 ∧
          (mass (s k t) B + shift) + mass (s k t) R0 ≤ C k) ∧
        (0 ≤ (mass (s k t) B + shift) + mass (s k t) R0 + s k t i ∧
          (mass (s k t) B + shift) + mass (s k t) R0 + s k t i ≤ C k) := by
      intro R0 i R1 hsplit hi
      have hs := (strip_split R0 ([i] ++ R1)
        (by simpa only [hsplit, List.append_assoc] using hsOld)).2
      change InStrip (s k t) (C k)
        (mass (s k t) B + mass (s k t) R0) (i :: R1) at hs
      have hd0 := hs.1
      have hdC := hs.2.1
      have ha := inStrip_prefix hs.2.2 0
      simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at ha
      have hdep : mass (s k t) (B ++ R0) =
          mass (s k t) B + mass (s k t) R0 := by
        simp only [mass, List.map_append, List.sum_append]
      have harr : mass (s k t) (B ++ R0 ++ [i]) =
          mass (s k t) B + mass (s k t) R0 + s k t i := by
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      have hQ := ar.Qpos
      by_cases hup : 0 < shift
      · have hh := ht.1 hup R0 i R1 hsplit hi
        by_cases hp : 0 < s k t i
        · have hb := hh.1 hp
          rw [harr] at hb
          omega
        · have hn : s k t i < 0 := by
            have hnonpos : s k t i ≤ 0 := by omega
            rw [abs_of_nonpos hnonpos] at hi
            omega
          have hb := hh.2 hn
          rw [hdep] at hb
          omega
      · have hdown : shift < 0 := by omega
        have hh := ht.2 hdown R0 i R1 hsplit hi
        by_cases hp : 0 < s k t i
        · have hb := hh.1 hp
          rw [hdep] at hb
          omega
        · have hn : s k t i < 0 := by
            have hnonpos : s k t i ≤ 0 := by omega
            rw [abs_of_nonpos hnonpos] at hi
            omega
          have hb := hh.2 hn
          rw [harr] at hb
          omega
    obtain ⟨Rstar, hR, hfilter, hsR⟩ :=
      LargeSkeletonOrdering.exists_order_preserving_large (s k t) (Q k) (C k)
        ar.Qpos (by have hc := ar.cap; omega) R (mass (s k t) B + shift)
        hstart (by simpa only [mass] using hend)
        (by simpa only [mass] using boundaries)
    exact ⟨Rstar, hR, hsR⟩

private theorem order_remainder {k t : ℕ} (w : SourceWord k t)
    (ar : Arithmetic w) (B R : List (Fin k))
    (hsOld : InStrip (s k t) (C k) (mass (s k t) B) R)
    (hstart : 0 ≤ mass (s k t) B - w.kappa ∧
      mass (s k t) B - w.kappa ≤ C k)
    (hend : 0 ≤ mass (s k t) B - w.kappa + mass (s k t) R ∧
      mass (s k t) B - w.kappa + mass (s k t) R ≤ C k)
    (horder : Compatible (s k t) (C k) R ∨ RemainderTest w B R) :
    ∃ Rstar : List (Fin k), Rstar.Perm R ∧
      InStrip (s k t) (C k) (mass (s k t) B - w.kappa) Rstar := by
  apply order_shift w ar B R (-w.kappa) hsOld
    (by simpa only [sub_eq_add_neg] using hstart)
    (by simpa only [sub_eq_add_neg] using hend)
  rcases horder with hc | ht
  · exact Or.inl hc
  · refine Or.inr ⟨?_, ?_⟩
    · intro hs
      exact ht.1 (by omega)
    · intro hs
      simpa only [neg_neg] using ht.2 (by omega)

/-- The complete physical and energy conclusion shared by the two NEW
consumers; FullExchange retains the original Inventory and strict J fields. -/
def RelocatedExchange {k t : ℕ} (w : SourceWord k t)
    (Astar T0star : List (Fin k)) : Prop :=
  let V := Astar ++ T0star ++ [w.beta, w.y, w.p, w.a]
  FullExchange w V w.inserted w.ret (w.v - w.tau) ∧
  s k t w.a = -w.M ∧ V.count w.a = 1 ∧
  G k t V = G k t w.W ∧
  MixedSuffixEnergy.U V = MixedSuffixEnergy.U w.W + w.late.length ∧
  H k t V + 3 ^ (s k t w.x).natAbs + 3 ^ (s k t w.zpen).natAbs +
      3 ^ (s k t w.z).natAbs =
    H k t w.W + 3 ^ (s k t w.p).natAbs + 3 ^ (s k t w.n).natAbs +
      3 ^ (s k t w.beta).natAbs ∧ H k t V < H k t w.W

set_option maxHeartbeats 1800000 in
-- Complete-batch orders, physical partitions and energy balances are composed here.
/-- Move the ACTUAL gamma from AFTER a to immediately before the complete T0.
The actual cuts and the separately computed T/R tests construct all orders. -/
theorem actualSource_child_after_parent_relocation_full
    {k t : ℕ} (w : SourceWord k t) (h : Residual w)
    (U T R : List (Fin k)) (hA : w.A = U ++ [w.a] ++ T ++ [w.gamma] ++ R)
    (hcut : mass (s k t) (U ++ [w.a] ++ T) + w.theta ≤ C k)
    (hfinal : w.kappa ≤ w.a0)
    (hTorder : Compatible (s k t) (C k) T ∨ HighSides w (U ++ [w.a]) T w.theta)
    (hRorder : Compatible (s k t) (C k) R ∨
      RemainderTest w (U ++ [w.a] ++ T ++ [w.gamma]) R) :
    ∃ Tstar Rstar T0star : List (Fin k),
      Tstar.Perm T ∧ Rstar.Perm R ∧ T0star.Perm w.T0 ∧
      (let Astar := U ++ [w.n] ++ Tstar ++ Rstar ++ [w.gamma]
       InStrip (s k t) (C k) 0 Astar ∧
       mass (s k t) Astar = w.a0 + w.theta ∧
       (Astar ++ [w.a]).Perm (w.A ++ [w.n]) ∧
       RelocatedExchange w Astar T0star) := by
  classical
  have ar := arithmetic w h
  obtain ⟨hidentity, height, hsharp, hkQ, hq0, hqQ, haValue, hD0, hDM⟩ :=
    actualSource_oddHalf_sharp_remainder w h
  obtain ⟨hsU, hsTail, hu, hmTail⟩ := old_prefix w h ar U
    (T ++ [w.gamma] ++ R) (by simpa only [List.append_assoc] using hA)
  have hsT := (old_segment w h (U ++ [w.a]) T ([w.gamma] ++ R)
    (by simpa only [List.append_assoc] using hA)).2
  have hsR := (old_segment w h (U ++ [w.a] ++ T ++ [w.gamma]) R []
    (by simpa only [List.append_assoc, List.append_nil] using hA)).2
  let u := mass (s k t) U
  let g := mass (s k t) (U ++ [w.a] ++ T)
  have hmUa : mass (s k t) (U ++ [w.a]) = u - w.M := by
    simp only [u, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, ar.parentValue]
    ring
  have hmT : g = u - w.M + mass (s k t) T := by
    dsimp only [g]
    rw [show mass (s k t) (U ++ [w.a] ++ T) =
      mass (s k t) (U ++ [w.a]) + mass (s k t) T by
        simp only [mass, List.map_append, List.sum_append], hmUa]
  have hmBeforeR : mass (s k t) (U ++ [w.a] ++ T ++ [w.gamma]) = g + w.q := by
    simp only [g, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, SourceWord.q]
  have hmR : g + w.q + mass (s k t) R = w.a0 := by
    change _ = mass (s k t) w.A
    rw [hA]
    simp only [g, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, SourceWord.q]
  have hg : 0 ≤ g ∧ g ≤ C k := by
    have hsGamma := (old_segment w h (U ++ [w.a] ++ T) [w.gamma] R
      (by simpa only [List.append_assoc] using hA)).2
    exact ⟨hsGamma.1, hsGamma.2.1⟩
  have hstart : 0 ≤ u - w.D ∧ u - w.D ≤ C k := by
    have ho := ar.order
    have hQ := ar.Qpos
    dsimp only [u]
    omega
  have hTend : 0 ≤ g + w.theta ∧ g + w.theta ≤ C k := by
    have hs := ar.shift
    exact ⟨by omega, hcut⟩
  obtain ⟨Tstar, hT, hsTstar⟩ := order_shift w ar (U ++ [w.a]) T w.theta hsT
    (by rw [hmUa]; have ht : w.theta = w.M - w.D := rfl; omega)
    (by rw [hmUa]; omega)
    (by
      rcases hTorder with hc | ht
      · exact Or.inl hc
      · exact Or.inr ⟨fun _ => ht, fun hn => by have := ar.shift.1; omega⟩)
  have hmTstar : mass (s k t) Tstar = mass (s k t) T := (hT.map _).sum_eq
  have hRend : 0 ≤ w.a0 - w.kappa ∧ w.a0 - w.kappa ≤ C k := by
    have hb := ar.base
    have ho := ar.order
    have hk := (abs_lt.mp hsharp).1
    dsimp only [SourceWord.B, SourceWord.d] at *
    omega
  obtain ⟨Rstar, hR, hsRstar⟩ := order_remainder w ar
    (U ++ [w.a] ++ T ++ [w.gamma]) R hsR
    (by rw [hmBeforeR]; omega) (by rw [hmBeforeR]; omega) hRorder
  have hmRstar : mass (s k t) Rstar = mass (s k t) R := (hR.map _).sum_eq
  have hsN : InStrip (s k t) (C k) u [w.n] := by
    change 0 ≤ u ∧ u ≤ C k ∧
      0 ≤ u + s k t w.n ∧ u + s k t w.n ≤ C k
    rw [ar.nValue]
    dsimp only [u] at *
    omega
  have hsUN : InStrip (s k t) (C k) 0 (U ++ [w.n]) :=
    inStrip_append hsU (by simpa only [zero_add, u, mass] using hsN)
  have hmUN : mass (s k t) (U ++ [w.n]) = u - w.D := by
    simp only [u, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, ar.nValue]
    ring
  have hsUNT : InStrip (s k t) (C k) 0 (U ++ [w.n] ++ Tstar) := by
    apply inStrip_append hsUN
    change InStrip (s k t) (C k) (0 + mass (s k t) (U ++ [w.n])) Tstar
    rw [zero_add, hmUN]
    have hj : mass (s k t) (U ++ [w.a]) + w.theta = u - w.D := by
      rw [hmUa]
      dsimp only [SourceWord.theta]
      ring
    simpa only [hj] using hsTstar
  have hmUNT : mass (s k t) (U ++ [w.n] ++ Tstar) = g + w.theta := by
    rw [show mass (s k t) (U ++ [w.n] ++ Tstar) =
      mass (s k t) (U ++ [w.n]) + mass (s k t) Tstar by
        simp only [mass, List.map_append, List.sum_append], hmUN, hmTstar]
    dsimp only [SourceWord.theta]
    omega
  have hsBeforeGamma : InStrip (s k t) (C k) 0 (U ++ [w.n] ++ Tstar ++ Rstar) := by
    apply inStrip_append hsUNT
    change InStrip (s k t) (C k) (0 + mass (s k t) (U ++ [w.n] ++ Tstar)) Rstar
    rw [zero_add, hmUNT]
    have hj : mass (s k t) (U ++ [w.a] ++ T ++ [w.gamma]) - w.kappa =
        g + w.theta := by rw [hmBeforeR]; omega
    simpa only [hj] using hsRstar
  have hmBeforeGamma : mass (s k t) (U ++ [w.n] ++ Tstar ++ Rstar) =
      w.a0 - w.kappa := by
    rw [show mass (s k t) (U ++ [w.n] ++ Tstar ++ Rstar) =
      mass (s k t) (U ++ [w.n] ++ Tstar) + mass (s k t) Rstar by
        simp only [mass, List.map_append, List.sum_append], hmUNT, hmRstar]
    omega
  let Astar := U ++ [w.n] ++ Tstar ++ Rstar ++ [w.gamma]
  have hsAstar : InStrip (s k t) (C k) 0 Astar := by
    apply inStrip_append hsBeforeGamma
    change InStrip (s k t) (C k) (0 + mass (s k t) (U ++ [w.n] ++ Tstar ++ Rstar)) [w.gamma]
    rw [zero_add, hmBeforeGamma]
    change 0 ≤ w.a0 - w.kappa ∧ w.a0 - w.kappa ≤ C k ∧
      0 ≤ w.a0 - w.kappa + w.q ∧ w.a0 - w.kappa + w.q ≤ C k
    have he := ar.newEnd
    omega
  have hmAstar : mass (s k t) Astar = w.a0 + w.theta := by
    change mass (s k t) ((U ++ [w.n] ++ Tstar ++ Rstar) ++ [w.gamma]) = _
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hmBeforeGamma ⊢
    change _ + w.q = _
    omega
  have hphysical : (Astar ++ [w.a]).Perm (w.A ++ [w.n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have ht := hT.count_eq i
    have hr := hR.count_eq i
    have ha := congrArg (List.count i) hA
    simp only [Astar, List.count_append, List.count_cons, List.count_nil] at ht hr ha ⊢
    omega
  obtain ⟨T0star, hT0, hcomplete⟩ :=
    complete_constructed w h ar Astar hsAstar hmAstar hphysical
  exact ⟨Tstar, Rstar, T0star, hT, hR, hT0, hsAstar, hmAstar, hphysical, hcomplete⟩

set_option maxHeartbeats 1800000 in
-- Complete-batch orders, physical partitions and energy balances are composed here.
/-- Move the ACTUAL gamma from BEFORE a, shifting the middle interval DOWN
by q. The old arrival at a and the old endpoint a0 are the two actual cuts.
In particular positive kappa does not permit either cut to be discarded. -/
theorem actualSource_child_before_parent_relocation_full
    {k t : ℕ} (w : SourceWord k t) (h : Residual w)
    (U T R : List (Fin k)) (hA : w.A = U ++ [w.gamma] ++ T ++ [w.a] ++ R)
    (hcut : w.kappa ≤ mass (s k t) (U ++ [w.gamma] ++ T ++ [w.a]))
    (hfinal : w.kappa ≤ w.a0)
    (hTorder : Compatible (s k t) (C k) T ∨ LowSides w (U ++ [w.gamma]) T w.q)
    (hRorder : Compatible (s k t) (C k) R ∨
      RemainderTest w (U ++ [w.gamma] ++ T ++ [w.a]) R) :
    ∃ Tstar Rstar T0star : List (Fin k),
      Tstar.Perm T ∧ Rstar.Perm R ∧ T0star.Perm w.T0 ∧
      (let Astar := U ++ Tstar ++ [w.n] ++ Rstar ++ [w.gamma]
       InStrip (s k t) (C k) 0 Astar ∧
       mass (s k t) Astar = w.a0 + w.theta ∧
       (Astar ++ [w.a]).Perm (w.A ++ [w.n]) ∧
       RelocatedExchange w Astar T0star) := by
  classical
  have ar := arithmetic w h
  obtain ⟨hidentity, height, hsharp, hkQ, hq0, hqQ, haValue, hD0, hDM⟩ :=
    actualSource_oddHalf_sharp_remainder w h
  obtain ⟨hsBeforeA, hsOldR, ht, hmOldR⟩ := old_prefix w h ar
    (U ++ [w.gamma] ++ T) R (by simpa only [List.append_assoc] using hA)
  have hsU := (old_segment w h U ([w.gamma] ++ T ++ [w.a] ++ R) []
    (by simpa only [List.append_assoc, List.append_nil] using hA)).1
  have hsT := (old_segment w h (U ++ [w.gamma]) T ([w.a] ++ R)
    (by simpa only [List.append_assoc] using hA)).2
  have hsR := (old_segment w h (U ++ [w.gamma] ++ T ++ [w.a]) R []
    (by simpa only [List.append_assoc, List.append_nil] using hA)).2
  let g := mass (s k t) U
  let t0 := mass (s k t) (U ++ [w.gamma] ++ T)
  let b := t0 - w.M
  have hg : 0 ≤ g ∧ g ≤ C k := by
    simpa only [g, mass, zero_add, List.take_length] using inStrip_prefix hsU U.length
  have hmUg : mass (s k t) (U ++ [w.gamma]) = g + w.q := by
    simp only [g, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, SourceWord.q]
  have hmT : t0 = g + w.q + mass (s k t) T := by
    dsimp only [t0]
    rw [show mass (s k t) (U ++ [w.gamma] ++ T) =
      mass (s k t) (U ++ [w.gamma]) + mass (s k t) T by
        simp only [mass, List.map_append, List.sum_append], hmUg]
  have hmBeforeR : mass (s k t) (U ++ [w.gamma] ++ T ++ [w.a]) = b := by
    simp only [b, t0, mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, ar.parentValue]
    ring
  have hmR : b + mass (s k t) R = w.a0 := hmOldR
  have hTend : 0 ≤ t0 - w.q ∧ t0 - w.q ≤ C k := by
    have ho := ar.order
    change w.M ≤ t0 ∧ t0 ≤ C k at ht
    omega
  obtain ⟨Tstar, hT, hsTstar⟩ := order_shift w ar (U ++ [w.gamma]) T (-w.q) hsT
    (by rw [hmUg]; omega) (by rw [hmUg]; omega)
    (by
      rcases hTorder with hc | ht
      · exact Or.inl hc
      · exact Or.inr ⟨fun hp => by omega, fun _ => by simpa only [neg_neg] using ht⟩)
  have hmTstar : mass (s k t) Tstar = mass (s k t) T := (hT.map _).sum_eq
  have hRstart : 0 ≤ b - w.kappa ∧ b - w.kappa ≤ C k := by
    rw [hmBeforeR] at hcut
    have hQ := ar.Qpos
    have ho := ar.order
    have htC : t0 ≤ C k := ht.2
    have hj : b - w.kappa = t0 - w.q - w.D := by
      dsimp only [b, SourceWord.theta] at *
      omega
    rw [hj]
    omega
  have hRend : 0 ≤ w.a0 - w.kappa ∧ w.a0 - w.kappa ≤ C k := by
    have hb := ar.base
    have ho := ar.order
    have hk := (abs_lt.mp hsharp).1
    dsimp only [SourceWord.B, SourceWord.d] at *
    omega
  obtain ⟨Rstar, hR, hsRstar⟩ := order_remainder w ar
    (U ++ [w.gamma] ++ T ++ [w.a]) R hsR
    (by rw [hmBeforeR]; exact hRstart)
    (by rw [hmBeforeR]; omega) hRorder
  have hmRstar : mass (s k t) Rstar = mass (s k t) R := (hR.map _).sum_eq
  have hsUT : InStrip (s k t) (C k) 0 (U ++ Tstar) := by
    apply inStrip_append hsU
    have hj : mass (s k t) (U ++ [w.gamma]) + -w.q = g := by rw [hmUg]; ring
    rw [hj] at hsTstar
    simpa only [zero_add, g, mass] using hsTstar
  have hmUT : mass (s k t) (U ++ Tstar) = t0 - w.q := by
    rw [show mass (s k t) (U ++ Tstar) = g + mass (s k t) Tstar by
      simp only [g, mass, List.map_append, List.sum_append], hmTstar]
    omega
  have hsN : InStrip (s k t) (C k) (t0 - w.q) [w.n] := by
    change 0 ≤ t0 - w.q ∧ t0 - w.q ≤ C k ∧
      0 ≤ t0 - w.q + s k t w.n ∧ t0 - w.q + s k t w.n ≤ C k
    rw [ar.nValue]
    dsimp only [b, SourceWord.theta] at *
    omega
  have hsUTN : InStrip (s k t) (C k) 0 (U ++ Tstar ++ [w.n]) := by
    apply inStrip_append hsUT
    change InStrip (s k t) (C k) (0 + mass (s k t) (U ++ Tstar)) [w.n]
    rw [zero_add, hmUT]
    exact hsN
  have hmUTN : mass (s k t) (U ++ Tstar ++ [w.n]) = b - w.kappa := by
    rw [show mass (s k t) (U ++ Tstar ++ [w.n]) =
      mass (s k t) (U ++ Tstar) + s k t w.n by
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero], hmUT, ar.nValue]
    dsimp only [b, SourceWord.theta] at *
    omega
  have hsBeforeGamma : InStrip (s k t) (C k) 0 (U ++ Tstar ++ [w.n] ++ Rstar) := by
    apply inStrip_append hsUTN
    change InStrip (s k t) (C k) (0 + mass (s k t) (U ++ Tstar ++ [w.n])) Rstar
    rw [zero_add, hmUTN]
    simpa only [hmBeforeR] using hsRstar
  have hmBeforeGamma : mass (s k t) (U ++ Tstar ++ [w.n] ++ Rstar) =
      w.a0 - w.kappa := by
    rw [show mass (s k t) (U ++ Tstar ++ [w.n] ++ Rstar) =
      mass (s k t) (U ++ Tstar ++ [w.n]) + mass (s k t) Rstar by
        simp only [mass, List.map_append, List.sum_append], hmUTN, hmRstar]
    omega
  let Astar := U ++ Tstar ++ [w.n] ++ Rstar ++ [w.gamma]
  have hsAstar : InStrip (s k t) (C k) 0 Astar := by
    apply inStrip_append hsBeforeGamma
    change InStrip (s k t) (C k) (0 + mass (s k t) (U ++ Tstar ++ [w.n] ++ Rstar)) [w.gamma]
    rw [zero_add, hmBeforeGamma]
    change 0 ≤ w.a0 - w.kappa ∧ w.a0 - w.kappa ≤ C k ∧
      0 ≤ w.a0 - w.kappa + w.q ∧ w.a0 - w.kappa + w.q ≤ C k
    have he := ar.newEnd
    omega
  have hmAstar : mass (s k t) Astar = w.a0 + w.theta := by
    change mass (s k t) ((U ++ Tstar ++ [w.n] ++ Rstar) ++ [w.gamma]) = _
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hmBeforeGamma ⊢
    change _ + w.q = _
    omega
  have hphysical : (Astar ++ [w.a]).Perm (w.A ++ [w.n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have ht := hT.count_eq i
    have hr := hR.count_eq i
    have ha := congrArg (List.count i) hA
    simp only [Astar, List.count_append, List.count_cons, List.count_nil] at ht hr ha ⊢
    omega
  obtain ⟨T0star, hT0, hcomplete⟩ :=
    complete_constructed w h ar Astar hsAstar hmAstar hphysical
  exact ⟨Tstar, Rstar, T0star, hT, hR, hT0, hsAstar, hmAstar, hphysical, hcomplete⟩

end D5.S3.Combinatorics.Circle.OddHalfParentExchange
