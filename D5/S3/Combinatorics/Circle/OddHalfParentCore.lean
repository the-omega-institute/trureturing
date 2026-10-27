/- GID: D5/S3/Combinatorics/Circle/OddHalfParentCore
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OddHalfParentCore
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: The actual odd-half negative parent supplies a four-insertion G descent or a reused-parent three-insertion energy descent. -/
module
public import D5.S3.Combinatorics.Circle.OddFirstNegativePlacement
public import D5.S3.Combinatorics.Circle.LargeSkeletonOrdering

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

/-- Physical input, with no injectivity assumption on the numerical source. -/
structure SourceWord (k t : ℕ) where
  p : Fin k
  y : Fin k
  zpen : Fin k
  z : Fin k
  A : List (Fin k)
  T0 : List (Fin k)
  T1 : List (Fin k)
  T2 : List (Fin k)
  E : List (Fin k)

namespace SourceWord
variable {k t : ℕ} (w : SourceWord k t)
abbrev n := hit k 1 w.p
abbrev x := hit k 2 w.p
abbrev beta := (finRotate k).symm w.y
abbrev gamma := (finRotate k).symm w.beta
abbrev a := (finRotate k).symm w.gamma
abbrev W := oldWord w.p w.y w.zpen w.z w.A w.T0 w.T1 w.T2 w.E
abbrev S := smallWord w.T0 w.T1 w.T2 w.E
abbrev F := w.A ++ [w.x] ++ w.T0 ++ [w.y]
abbrev late := w.T1 ++ w.T2 ++ w.E
abbrev ret0 := w.T1 ++ [w.zpen] ++ w.T2 ++ [w.z] ++ w.E
abbrev ret := [w.x, w.zpen, w.z] ++ w.late
abbrev P : ℤ := s k t w.p
abbrev D : ℤ := |s k t w.n|
abbrev r : ℤ := s k t w.x
abbrev Y : ℤ := -s k t w.y
abbrev L : ℤ := s k t w.beta
abbrev q : ℤ := s k t w.gamma
abbrev M : ℤ := (N k - w.q) / 2
abbrev d : ℤ := w.P - w.D
abbrev B : ℤ := C k - w.P
abbrev delta : ℤ := w.Y - w.P
abbrev e : ℤ := w.M - w.P
abbrev theta : ℤ := w.M - w.D
abbrev tau : ℤ := w.P - w.L
abbrev kappa : ℤ := w.e - w.tau
abbrev a0 : ℤ := mass (s k t) w.A
abbrev v : ℤ := mass (s k t) w.F
end SourceWord

/-- The native residual, rather than a list of prospective new-word gates.
The odd-first-negative classifier supplies beta/gamma placement and the bound
on zpen at a minimum; this theorem does not silently remove that hypothesis.
The three extra scalar inequalities specify the completed HAND subbranch. -/
structure Residual {k t : ℕ} (w : SourceWord k t) : Prop where
  hk : 3 ≤ k
  positive : 0 < w.P
  nlarge : Q k ≤ w.D
  expand : N k < 3 * |w.P|
  oldLegal : Legal k t w.W
  pFresh : w.p ∉ w.W
  nFresh : w.n ∉ w.W
  betaFresh : w.beta ∉ w.W
  small : ∀ i ∈ w.S, |s k t i| < Q k
  zBounds : Q k ≤ -s k t w.z ∧ -s k t w.z ≤ w.D
  zpenBounds : Q k ≤ -s k t w.zpen ∧ -s k t w.zpen ≤ w.L
  firstOdd : w.Y % 2 = 1
  firstHigh : w.P < w.Y
  halfParity : w.L % 4 = 2
  gammaInA : w.gamma ∈ w.A
  blocking : w.B < mass (s k t) w.W ∧ mass (s k t) w.W < w.D
  valley : (w.Y + 1) / 2 - w.d ≤ w.v ∧ w.v < w.d
  deficit : w.D ≤ 3 * w.d - 4
  shortDelta : 3 * w.delta ≤ w.d - 2
  highD : 2 * w.d + 2 * w.delta + 7 < w.D

/-- Entire-list compatibility, including every actual LARGE occurrence. -/
def Compatible {α : Type*} (f : α → ℤ) (cap : ℤ) (R : List α) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, 0 < f i → f j < 0 → f i - f j ≤ cap

/-- Old upper sides of the actual LARGE occurrences strictly after a in A.
Positive arrival and negative departure are measured from ORIGINAL zero. -/
def UpperTest {k t : ℕ} (w : SourceWord k t)
    (U R : List (Fin k)) : Prop :=
  ∀ (R0 : List (Fin k)) (i : Fin k) (R1 : List (Fin k)),
    R = R0 ++ [i] ++ R1 → Large k t i →
    (0 < s k t i →
      mass (s k t) (U ++ [w.a] ++ R0 ++ [i]) ≤ C k - w.theta) ∧
    (s k t i < 0 →
      mass (s k t) (U ++ [w.a] ++ R0) ≤ C k - w.theta)

theorem split_word {k t : ℕ} (w : SourceWord k t) :
    w.W = w.F ++ w.ret0 := by
  simp only [SourceWord.W, oldWord, SourceWord.F, SourceWord.ret0,
    SourceWord.x, List.append_assoc]

/-- Derived source equations and scalar gates; none is an input availability
condition. The positive_parent lemma is private in the immutable input, so
the two required carry cases use its public source_cycle dependency directly;
the full inversion/classification proof is not duplicated. -/
structure Arithmetic {k t : ℕ} (w : SourceWord k t) : Prop where
  Qpos : 0 < Q k
  cap : C k = 2 * Q k - 1
  modulus : N k = 4 * Q k - 1
  nValue : s k t w.n = -w.D
  parentValue : s k t w.a = -w.M
  native : N k = 2 * w.P + w.D ∧ w.r = 2 * w.P - w.D
  parentEquations : 2 * w.L = N k - w.Y ∧
    2 * w.q = w.L ∧ w.q % 2 = 1 ∧ 2 * w.M = N k - w.q
  order : Q k ≤ w.D ∧ w.D < w.L ∧ w.L < w.P ∧
    w.P < w.Y ∧ w.Y < w.M ∧ w.M < w.r ∧ w.r ≤ C k
  base : 0 ≤ w.a0 ∧ w.a0 ≤ w.B - w.d
  shift : 0 < w.theta ∧ w.theta < Q k
  excess : 0 < w.e ∧ w.e < w.d ∧ w.B - w.d < w.e
  valley : w.e < w.v ∧ w.tau < w.v
  spare : w.delta + w.kappa < w.B - w.d
  newEnd : 0 ≤ w.a0 + w.theta ∧ w.a0 + w.theta ≤ C k
  smallEnd : 0 ≤ w.v + w.delta + w.e ∧ w.v + w.delta + w.e ≤ C k
  unusedGates :
    (0 ≤ w.v + w.P ∧ w.v + w.P ≤ C k) ∧
    (0 ≤ w.v - w.e ∧ w.v - w.e ≤ C k) ∧
    (0 ≤ w.v - w.e + w.L ∧ w.v - w.e + w.L ≤ C k) ∧
    (0 ≤ w.v - w.e + w.L - w.D ∧ w.v - w.e + w.L - w.D ≤ C k)
  usedGates :
    (0 ≤ w.v + w.Y + w.kappa ∧ w.v + w.Y + w.kappa ≤ C k) ∧
    (0 ≤ w.v + w.kappa ∧ w.v + w.kappa ≤ C k) ∧
    (0 ≤ w.v + w.kappa + w.P ∧ w.v + w.kappa + w.P ≤ C k) ∧
    (0 < w.v - w.tau ∧ w.v - w.tau ≤ C k)

set_option maxHeartbeats 1400000 in
-- Exact inverse-source carry cases and the scalar gates are resolved together.
theorem arithmetic {k t : ℕ} (w : SourceWord k t) (h : Residual w) :
    Arithmetic w := by
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry h.hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  change 0 < N k at hNp
  change N k % 2 = 1 at hNo
  have geo := native_geometry h.hk t w.p h.nlarge h.expand
  have hn : s k t w.n = -w.D := by
    simpa [SourceWord.n, SourceWord.D, SourceWord.P, orient,
      show ¬ w.P < 0 by have := h.positive; omega] using geo.nValue
  have hx : w.r = |s k t w.x| := by
    simpa [SourceWord.r, SourceWord.x, SourceWord.P, orient,
      show ¬ w.P < 0 by have := h.positive; omega] using geo.xValue
  have hDP : w.D < w.P := by
    simpa only [abs_of_pos h.positive] using geo.strictOrder.1
  have hPr : w.P < w.r := by
    have hh := geo.strictOrder.2
    rw [abs_of_pos h.positive, ← hx] at hh
    exact hh
  have hNP : N k = 2 * w.P + w.D := by
    have hh := geo.firstEquation
    rw [abs_of_pos h.positive] at hh
    change w.D = N k - 2 * w.P at hh
    omega
  have hr : w.r = 2 * w.P - w.D := by
    have hh := geo.secondEquation
    rw [abs_of_pos h.positive, ← hx] at hh
    change w.r = 4 * w.P - N k at hh
    omega
  have bound (i : Fin k) : -C k ≤ s k t i ∧ s k t i ≤ C k :=
    centered_bounds hNp hNo _
  have hrC : w.r ≤ C k := (bound w.x).2
  have hYcap : w.Y ≤ C k := by
    have hb := bound w.y
    change -s k t w.y ≤ C k
    omega
  have hYpos : 0 < w.Y := lt_trans h.positive h.firstHigh
  have hyneg : s k t w.y < 0 := by
    dsimp only [SourceWord.Y] at hYpos
    omega
  have hparent := FirstNegativeShiftExchange.negative_parent k t h.hk w.y
    hyneg
  have hL : 2 * w.L = N k - w.Y := by
    rcases hparent with he | ho
    · have hh := h.firstOdd
      have heven : w.Y % 2 = 0 := he.1
      omega
    · exact ho.2.1
  -- The actual beta has an even value. Its actual inverse gamma has q=L/2.
  have hkpos : 0 < k := by have := h.hk; omega
  have edgeGamma := (ZeroSumSubsets.source_cycle hkpos t).2.2 w.gamma
  change 2 * w.q - s k t (finRotate k w.gamma) = N k *
    (if N k < 4 * w.q then 1 else if 4 * w.q < -N k then -1 else 0)
    at edgeGamma
  have rotGamma : finRotate k w.gamma = w.beta := Equiv.apply_symm_apply _ _
  rw [rotGamma] at edgeGamma
  change 2 * w.q - w.L = N k *
    (if N k < 4 * w.q then 1 else if 4 * w.q < -N k then -1 else 0) at edgeGamma
  have hq : 2 * w.q = w.L := by
    have hm := h.halfParity
    split_ifs at edgeGamma <;>
      simp only [mul_one, mul_neg, mul_zero] at edgeGamma <;> omega
  have hqOdd : w.q % 2 = 1 := by have hh := h.halfParity; omega
  have hqpos : 0 < w.q := by have hh := h.nlarge; omega
  -- Odd positive q excludes both the zero carry and the positive carry.
  have edgeA := (ZeroSumSubsets.source_cycle hkpos t).2.2 w.a
  change 2 * s k t w.a - s k t (finRotate k w.a) = N k *
    (if N k < 4 * s k t w.a then 1
      else if 4 * s k t w.a < -N k then -1 else 0) at edgeA
  have rotA : finRotate k w.a = w.gamma := Equiv.apply_symm_apply _ _
  rw [rotA] at edgeA
  change 2 * s k t w.a - w.q = N k *
    (if N k < 4 * s k t w.a then 1
      else if 4 * s k t w.a < -N k then -1 else 0) at edgeA
  have hMa : s k t w.a = -w.M ∧ 2 * w.M = N k - w.q := by
    have hb := bound w.a
    dsimp only [SourceWord.M]
    split_ifs at edgeA <;>
      simp only [mul_one, mul_neg, mul_zero] at edgeA <;> omega
  have hsA := (strip_split w.A
    ([w.x] ++ w.T0 ++ [w.y] ++ w.ret0)
    (by simpa only [split_word w, SourceWord.F, List.append_assoc]
      using strip_of_legal h.oldLegal))
  have ha0 : 0 ≤ w.a0 ∧ w.a0 ≤ C k := by
    simpa only [mass, zero_add, List.take_length] using
      inStrip_prefix hsA.1 w.A.length
  have hax : w.a0 + w.r ≤ C k := by
    have hb := inStrip_prefix hsA.2 1
    simpa [mass] using hb.2
  have hv := h.valley
  have hdelta := h.shortDelta
  have hhigh := h.highD
  have hdef := h.deficit
  have hZp := h.zpenBounds
  have hZ := h.zBounds
  have hDPQ := h.nlarge
  have hYP := h.firstHigh
  have hYo := h.firstOdd
  -- Linear integer arithmetic uses the exact equations, including parity.
  have hderived :
      w.D < w.L ∧ w.L < w.P ∧ w.Y < w.M ∧ w.M < w.r ∧
      0 < w.theta ∧ w.theta < Q k ∧
      0 < w.e ∧ w.e < w.d ∧ w.B - w.d < w.e ∧
      w.e < w.v ∧ w.tau < w.v ∧
      w.delta + w.kappa < w.B - w.d := by
    dsimp only [SourceWord.d, SourceWord.B, SourceWord.delta,
      SourceWord.e, SourceWord.theta, SourceWord.tau, SourceWord.kappa] at *
    omega
  rcases hderived with ⟨hDL, hLP, hYM, hMr, htheta0, hthetaQ,
    he0, hed, heB, hev, htauv, hspare⟩
  have hbase : 0 ≤ w.a0 ∧ w.a0 ≤ w.B - w.d := by
    dsimp only [SourceWord.B, SourceWord.d]
    omega
  refine ⟨by omega, hC, hN, hn, hMa.1, ⟨hNP, hr⟩,
    ⟨hL, hq, hqOdd, hMa.2⟩,
    ⟨hDPQ, hDL, hLP, hYP, hYM, hMr, hrC⟩, hbase,
    ⟨htheta0, hthetaQ⟩, ⟨he0, hed, heB⟩, ⟨hev, htauv⟩, hspare,
    ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [SourceWord.d, SourceWord.B, SourceWord.delta,
      SourceWord.e, SourceWord.theta, SourceWord.tau, SourceWord.kappa] at * <;>
    omega

private theorem large_labels {k t : ℕ} (w : SourceWord k t)
    (h : Residual w) (ar : Arithmetic w) :
    Large k t w.p ∧ Large k t w.n ∧ Large k t w.beta ∧
    Large k t w.a ∧ Large k t w.x ∧ Large k t w.zpen ∧ Large k t w.z := by
  have ho := ar.order
  have hz := h.zBounds
  have hzp := h.zpenBounds
  have hQ := ar.Qpos
  change Q k ≤ |w.P| ∧ Q k ≤ |s k t w.n| ∧ Q k ≤ |w.L| ∧
    Q k ≤ |s k t w.a| ∧ Q k ≤ |w.r| ∧
    Q k ≤ |s k t w.zpen| ∧ Q k ≤ |s k t w.z|
  exact ⟨by rw [abs_of_pos h.positive]; omega, h.nlarge,
    by rw [abs_of_pos (by omega : 0 < w.L)]; omega,
    by rw [ar.parentValue, abs_neg, abs_of_pos (by omega : 0 < w.M)]; omega,
    by rw [abs_of_pos (by omega : 0 < w.r)]; omega,
    by have := neg_le_abs (s k t w.zpen); omega,
    by have := neg_le_abs (s k t w.z); omega⟩

private theorem late_small {k t : ℕ} (w : SourceWord k t) (h : Residual w) :
    ∀ i ∈ w.late, |s k t i| < Q k := by
  intro i hi
  apply h.small i
  simp only [SourceWord.late, List.mem_append] at hi
  simp only [SourceWord.S, smallWord, List.mem_append]
  tauto

set_option maxHeartbeats 800000 in
-- The two exact filtered physical partitions share the same membership decomposition.
private theorem returned_small {k t : ℕ} (w : SourceWord k t)
    (h : Residual w) (ar : Arithmetic w) :
    w.ret0.toFinset.filter (fun i => ¬ Large k t i) = w.late.toFinset ∧
    w.ret.toFinset.filter (fun i => ¬ Large k t i) = w.late.toFinset := by
  classical
  obtain ⟨hp, hn, hb, ha, hx, hzp, hz⟩ := large_labels w h ar
  have hs : ∀ i ∈ w.late, ¬ Large k t i := by
    intro i hi
    exact not_le.mpr (late_small w h i hi)
  constructor <;> ext i
  all_goals
    have hxi : i = w.x → Large k t i := by rintro rfl; exact hx
    have hzpi : i = w.zpen → Large k t i := by rintro rfl; exact hzp
    have hzi : i = w.z → Large k t i := by rintro rfl; exact hz
    have hsi : (i ∈ w.T1 ∨ i ∈ w.T2 ∨ i ∈ w.E) → ¬ Large k t i := by
      intro hi
      apply hs i
      simpa only [SourceWord.late, List.mem_append, or_assoc] using hi
    simp only [Finset.mem_filter, List.mem_toFinset, SourceWord.ret0,
      SourceWord.ret, SourceWord.late, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto

private theorem tail_weights {k t : ℕ} (w : SourceWord k t)
    (h : Residual w) (ar : Arithmetic w) :
    (largeUsed k t w.ret0 = 2 ∧
      H k t w.ret0 = 3 ^ (s k t w.zpen).natAbs + 3 ^ (s k t w.z).natAbs) ∧
    (largeUsed k t w.ret = 3 ∧
      H k t w.ret = 3 ^ (s k t w.x).natAbs +
        3 ^ (s k t w.zpen).natAbs + 3 ^ (s k t w.z).natAbs) := by
  classical
  obtain ⟨hp, hn, hb, ha, hx, hzp, hz⟩ := large_labels w h ar
  obtain ⟨hsmallG, hsmallH⟩ := small_weights t w.late (late_small w h)
  have hperm : w.ret0.Perm ([w.zpen, w.z] ++ w.late) := by
    apply List.perm_iff_count.mpr
    intro i
    simp only [SourceWord.ret0, SourceWord.late, List.count_append,
      List.count_cons, List.count_nil]
    omega
  have hg := (hperm.map (largeWeight k t)).sum_eq
  have hh := (hperm.map (energyWeight k t)).sum_eq
  change largeUsed k t w.ret0 = largeUsed k t ([w.zpen, w.z] ++ w.late) at hg
  change H k t w.ret0 = H k t ([w.zpen, w.z] ++ w.late) at hh
  have gappend (A B : List (Fin k)) : largeUsed k t (A ++ B) =
      largeUsed k t A + largeUsed k t B := by
    simp only [largeUsed, mass, List.map_append, List.sum_append]
  have eappend (A B : List (Fin k)) : H k t (A ++ B) = H k t A + H k t B := by
    simp only [H, mass, List.map_append, List.sum_append]
  have hg0 : largeUsed k t w.ret0 = 2 := by
    rw [hg, gappend, hsmallG]
    simp [largeUsed, mass, largeWeight, hzp, hz]
  have hh0 : H k t w.ret0 =
      3 ^ (s k t w.zpen).natAbs + 3 ^ (s k t w.z).natAbs := by
    rw [hh, eappend, hsmallH]
    simp [H, mass, energyWeight, hzp, hz, s]
  have hgR : largeUsed k t w.ret = 3 := by
    change largeUsed k t ([w.x, w.zpen, w.z] ++ w.late) = 3
    rw [gappend, hsmallG]
    simp [largeUsed, mass, largeWeight, hx, hzp, hz]
  have hhR : H k t w.ret = 3 ^ (s k t w.x).natAbs +
      3 ^ (s k t w.zpen).natAbs + 3 ^ (s k t w.z).natAbs := by
    change H k t ([w.x, w.zpen, w.z] ++ w.late) = _
    rw [eappend, hsmallH]
    simp [H, mass, energyWeight, hx, hzp, hz, s, Nat.add_assoc]
  exact ⟨⟨hg0, hh0⟩, ⟨hgR, hhR⟩⟩

/-- Common mathematical output. All physical set, source and complement
balances are inherited from Inventory, not from a second inventory engine. -/
structure FullExchange {k t : ℕ} (w : SourceWord k t)
    (V I Ret : List (Fin k)) (endpoint : ℤ) : Prop where
  legal : Legal k t V
  strip : InStrip (s k t) (C k) 0 V
  prefixes : ∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
    mass (s k t) (V.take j) ≤ C k
  inventory : Inventory k t w.W V I Ret
  physical : (V ++ Ret).Perm (w.W ++ I)
  endMass : mass (s k t) V = endpoint
  complementMass : remainingMass (s k t) V = -endpoint
  remainingSmall : remainingSmall t V = remainingSmall t w.W ∪ w.late.toFinset
  smallDisjoint : Disjoint (TwoOppositeLargeExchange.remainingSmall t w.W) w.late.toFinset
  strictJ : J k t V < J k t w.W

set_option maxHeartbeats 1200000 in
-- The full physical inventory and all insertion gates share this proof budget.
/-- The actual a=rho^{-1}(gamma), fresh in ALL W, gives a literal-prefix
four-LARGE insertion. Exactly two LARGE are returned, so G improves by two.
No strict-H assertion is made: H can increase for repeated actual sources. -/
theorem actualSource_unused_oddHalf_parent_exchange_full
    {k t : ℕ} (w : SourceWord k t) (h : Residual w) (haFresh : w.a ∉ w.W) :
    let I := [w.p, w.a, w.beta, w.n]
    let V := w.F ++ I
    FullExchange w V I w.ret0 (w.v - w.e + w.L - w.D) ∧
    s k t w.a = -w.M ∧
    G k t V + 2 = G k t w.W ∧
    U V + 2 = U w.W + w.late.length ∧
    H k t V + 3 ^ (s k t w.zpen).natAbs + 3 ^ (s k t w.z).natAbs =
      H k t w.W + 3 ^ (s k t w.p).natAbs + 3 ^ (s k t w.a).natAbs +
        3 ^ (s k t w.beta).natAbs + 3 ^ (s k t w.n).natAbs := by
  classical
  dsimp only
  let I := [w.p, w.a, w.beta, w.n]
  let V := w.F ++ I
  have ar := arithmetic w h
  obtain ⟨hpL, hnL, hbL, haL, hxL, hzpL, hzL⟩ := large_labels w h ar
  have hp0 := h.positive
  have ho := ar.order
  have hQ := ar.Qpos
  have hpn : w.p ≠ w.n := by
    intro he; have hv := congrArg (s k t) he; rw [ar.nValue] at hv; change w.P = -w.D at hv; omega
  have hpa : w.p ≠ w.a := by
    intro he; have hv := congrArg (s k t) he; rw [ar.parentValue] at hv; change w.P = -w.M at hv; omega
  have hpb : w.p ≠ w.beta := by
    intro he; have hv := congrArg (s k t) he; change w.P = w.L at hv; omega
  have hab : w.a ≠ w.beta := by
    intro he; have hv := congrArg (s k t) he; rw [ar.parentValue] at hv; change -w.M = w.L at hv; omega
  have han : w.a ≠ w.n := by
    intro he; have hv := congrArg (s k t) he
    rw [ar.parentValue, ar.nValue] at hv; omega
  have hbn : w.beta ≠ w.n := by
    intro he; have hv := congrArg (s k t) he; rw [ar.nValue] at hv
    change w.L = -w.D at hv; omega
  have hI : I.Nodup := by simp only [I, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      hpa, hpb, hpn, hab, han, hbn, not_false_eq_true, true_and, List.nodup_nil]
  have hIW : ∀ i ∈ I, i ∉ w.W := by
    intro i hi
    simp only [I, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h.pFresh
    · exact haFresh
    · exact h.betaFresh
    · exact h.nFresh
  have hIL : ∀ i ∈ I, Large k t i := by
    intro i hi
    simp only [I, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  have hsF : InStrip (s k t) (C k) 0 w.F :=
    (strip_split w.F w.ret0 (by rw [← split_word w]; exact strip_of_legal h.oldLegal)).1
  have hv : 0 ≤ w.v ∧ w.v ≤ C k := by
    simpa only [mass, zero_add, List.take_length] using inStrip_prefix hsF w.F.length
  have hsI : InStrip (s k t) (C k) w.v I := by
    change 0 ≤ w.v ∧ w.v ≤ C k ∧
      0 ≤ w.v + w.P ∧ w.v + w.P ≤ C k ∧
      0 ≤ w.v + w.P + s k t w.a ∧ w.v + w.P + s k t w.a ≤ C k ∧
      0 ≤ w.v + w.P + s k t w.a + w.L ∧
        w.v + w.P + s k t w.a + w.L ≤ C k ∧
      0 ≤ w.v + w.P + s k t w.a + w.L + s k t w.n ∧
        w.v + w.P + s k t w.a + w.L + s k t w.n ≤ C k
    rw [ar.parentValue, ar.nValue]
    have hg := ar.unusedGates
    dsimp only [SourceWord.e] at hg
    omega
  have hsV : InStrip (s k t) (C k) 0 V :=
    inStrip_append hsF (by simpa only [zero_add, mass] using hsI)
  have hperm : (V ++ w.ret0).Perm (w.W ++ I) := by
    rw [split_word w]
    simpa only [V, List.append_assoc] using
      (List.perm_append_comm : (I ++ w.ret0).Perm (w.ret0 ++ I)).append_left w.F
  have inv := inventory_of_perm h.hk t w.W V I w.ret0 h.oldLegal.1 hI hIW
    (by intro i hi; rw [split_word w]; exact List.mem_append_right _ hi) hIL hperm
  have hIg : largeUsed k t I = 4 := by
    simp only [I, largeUsed, mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, largeWeight, hpL, haL, hbL, hnL, ite_true, add_zero]
    rfl
  have hIh : H k t I = 3 ^ (s k t w.p).natAbs + 3 ^ (s k t w.a).natAbs +
      3 ^ (s k t w.beta).natAbs + 3 ^ (s k t w.n).natAbs := by
    simp only [I, H, mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      energyWeight, hpL, haL, hbL, hnL, ite_true, s, add_zero, Nat.add_assoc]
  obtain ⟨⟨hRg, hRh⟩, _⟩ := tail_weights w h ar
  have hG : G k t V + 2 = G k t w.W := by
    have hb := inv.largeBalance
    rw [hIg, hRg] at hb
    omega
  have hU : U V + 2 = U w.W + w.late.length := by
    have hb := inv.countBalance
    simp only [I, SourceWord.ret0, SourceWord.late, List.length_append,
      List.length_cons, List.length_nil] at hb ⊢
    omega
  have hEnergy := inv.energyBalance
  rw [hIh, hRh] at hEnergy
  have hend : mass (s k t) V = w.v - w.e + w.L - w.D := by
    change mass (s k t) (w.F ++ I) = _
    rw [show mass (s k t) (w.F ++ I) = w.v + mass (s k t) I by
      simp only [mass, List.map_append, List.sum_append]]
    simp only [I, mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [ar.parentValue, ar.nValue]
    dsimp only [SourceWord.e]
    ring
  have hj : J k t V < J k t w.W :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
  have hsm := (returned_small w h ar).1
  refine ⟨⟨legal_of_strip inv.nodup hsV, hsV,
    fun j => by simpa only [mass, zero_add] using inStrip_prefix hsV j,
    inv, hperm, hend, ?_, ?_, ?_, hj⟩, ar.parentValue, hG, hU, ?_⟩
  · simpa only [hend] using inv.complementSum
  · simpa only [hsm] using inv.smallPartition
  · simpa only [hsm] using inv.smallDisjoint
  · dsimp only [V, I] at hEnergy
    omega

theorem old_prefix {k t : ℕ} (w : SourceWord k t)
    (h : Residual w) (ar : Arithmetic w) (U R : List (Fin k))
    (hA : w.A = U ++ [w.a] ++ R) :
    InStrip (s k t) (C k) 0 U ∧
    InStrip (s k t) (C k) (mass (s k t) U - w.M) R ∧
    (w.M ≤ mass (s k t) U ∧ mass (s k t) U ≤ C k) ∧
    mass (s k t) U - w.M + mass (s k t) R = w.a0 := by
  have hsA : InStrip (s k t) (C k) 0 w.A :=
    (strip_split w.A ([w.x] ++ w.T0 ++ [w.y] ++ w.ret0)
      (by simpa only [split_word w, SourceWord.F, List.append_assoc]
        using strip_of_legal h.oldLegal)).1
  obtain ⟨hsU, hsRest⟩ := strip_split U ([w.a] ++ R)
    (by simpa only [hA, List.append_assoc] using hsA)
  have hsRest' : InStrip (s k t) (C k) (mass (s k t) U) (w.a :: R) := by
    simpa only [zero_add, List.cons_append, List.nil_append] using hsRest
  have hsR : InStrip (s k t) (C k) (mass (s k t) U - w.M) R := by
    simpa only [ar.parentValue, sub_eq_add_neg] using hsRest'.2.2
  have huM : w.M ≤ mass (s k t) U := by
    have hh := (inStrip_prefix hsR 0).1
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at hh
    omega
  have hm : mass (s k t) U - w.M + mass (s k t) R = w.a0 := by
    change _ = mass (s k t) w.A
    rw [hA]
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [ar.parentValue]
    ring
  exact ⟨hsU, hsR, ⟨huM, hsRest'.2.1⟩, hm⟩

private theorem three_energy (P D L r : ℕ) (hDP : D < P)
    (hLP : L < P) (hPr : P < r) :
    (3 : ℕ) ^ P + 3 ^ D + 3 ^ L < 3 ^ r := by
  have hD := pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) hDP
  have hL := pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) (Nat.le_of_lt hLP)
  have hnext := pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ))
    (show P + 1 ≤ r by omega)
  rw [pow_succ] at hnext
  omega

namespace SourceWord
variable {k t : ℕ} (w : SourceWord k t)
abbrev usedWord (U Rstar Tstar : List (Fin k)) :=
  U ++ [w.n] ++ Rstar ++ Tstar ++ [w.beta, w.y, w.p, w.a]
abbrev inserted := [w.n, w.beta, w.p]
end SourceWord

set_option maxHeartbeats 1800000 in
-- Complete-batch orders, physical partitions and energy balances are composed here.
/-- One physical, energy and COMPLETE-T0 completion for every constructed
prefix. Actual positional consumers supply its strip, mass and physical partition. -/
theorem complete_constructed {k t : ℕ} (w : SourceWord k t) (h : Residual w)
    (ar : Arithmetic w) (Astar : List (Fin k))
    (hsPstar : InStrip (s k t) (C k) 0 Astar)
    (hmPstar : mass (s k t) Astar = w.a0 + w.theta)
    (hphysical : (Astar ++ [w.a]).Perm (w.A ++ [w.n])) :
    ∃ Tstar : List (Fin k), Tstar.Perm w.T0 ∧
      (let V := Astar ++ Tstar ++ [w.beta, w.y, w.p, w.a]
       FullExchange w V w.inserted w.ret (w.v - w.tau) ∧
       s k t w.a = -w.M ∧ V.count w.a = 1 ∧
       G k t V = G k t w.W ∧ MixedSuffixEnergy.U V = MixedSuffixEnergy.U w.W + w.late.length ∧
       H k t V + 3 ^ (s k t w.x).natAbs + 3 ^ (s k t w.zpen).natAbs +
           3 ^ (s k t w.z).natAbs =
         H k t w.W + 3 ^ (s k t w.p).natAbs + 3 ^ (s k t w.n).natAbs +
           3 ^ (s k t w.beta).natAbs ∧ H k t V < H k t w.W) := by
  classical
  obtain ⟨hpL, hnL, hbL, haL, hxL, hzpL, hzL⟩ := large_labels w h ar
  have ho := ar.order
  have hQ := ar.Qpos
  have hp0 := h.positive
  have hmT0 : w.a0 + w.theta + mass (s k t) w.T0 =
      w.v + w.delta + w.e := by
    have hv : w.v = w.a0 + w.r + mass (s k t) w.T0 - w.Y := by
      simp only [SourceWord.v, SourceWord.F, mass, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, add_zero]
      ring
    have hr := ar.native.2
    dsimp only [SourceWord.theta, SourceWord.delta, SourceWord.e]
    omega
  obtain ⟨Tstar, hT, hsT⟩ := exists_order_between (s k t) w.T0 (C k)
    (w.a0 + w.theta) ar.newEnd
    (by
      change 0 ≤ w.a0 + w.theta + mass (s k t) w.T0 ∧
        w.a0 + w.theta + mass (s k t) w.T0 ≤ C k
      rw [hmT0]
      exact ar.smallEnd)
    (by
      intro i hi j hj hip hjn
      have hiQ := h.small i (by simp [SourceWord.S, smallWord, hi])
      have hjQ := h.small j (by simp [SourceWord.S, smallWord, hj])
      rw [abs_of_pos hip] at hiQ
      rw [abs_of_neg hjn] at hjQ
      have hc := ar.cap
      omega)
  have hmTstar : mass (s k t) Tstar = mass (s k t) w.T0 := (hT.map _).sum_eq
  have hsCore : InStrip (s k t) (C k) 0 (Astar ++ Tstar) := by
    apply inStrip_append hsPstar
    change InStrip (s k t) (C k)
      (0 + mass (s k t) (Astar)) Tstar
    rw [zero_add, hmPstar]
    exact hsT
  have hmCore : mass (s k t) (Astar ++ Tstar) =
      w.v + w.delta + w.e := by
    calc
      _ = mass (s k t) (Astar) + mass (s k t) Tstar := by
        simp only [mass, List.map_append, List.sum_append]
      _ = _ := by rw [hmPstar, hmTstar, hmT0]
  have hsPacket : InStrip (s k t) (C k) (w.v + w.delta + w.e)
      [w.beta, w.y, w.p, w.a] := by
    change 0 ≤ w.v + w.delta + w.e ∧ w.v + w.delta + w.e ≤ C k ∧
      0 ≤ w.v + w.delta + w.e + w.L ∧
        w.v + w.delta + w.e + w.L ≤ C k ∧
      0 ≤ w.v + w.delta + w.e + w.L + s k t w.y ∧
        w.v + w.delta + w.e + w.L + s k t w.y ≤ C k ∧
      0 ≤ w.v + w.delta + w.e + w.L + s k t w.y + w.P ∧
        w.v + w.delta + w.e + w.L + s k t w.y + w.P ≤ C k ∧
      0 ≤ w.v + w.delta + w.e + w.L + s k t w.y + w.P + s k t w.a ∧
        w.v + w.delta + w.e + w.L + s k t w.y + w.P + s k t w.a ≤ C k
    rw [ar.parentValue]
    have hs := ar.smallEnd
    have hg := ar.usedGates
    dsimp only [SourceWord.Y, SourceWord.delta, SourceWord.e,
      SourceWord.tau, SourceWord.kappa] at *
    omega
  let V := Astar ++ Tstar ++ [w.beta, w.y, w.p, w.a]
  have hsV : InStrip (s k t) (C k) 0 V := by
    apply inStrip_append hsCore
    change InStrip (s k t) (C k)
      (0 + mass (s k t) (Astar ++ Tstar))
        [w.beta, w.y, w.p, w.a]
    rw [zero_add, hmCore]
    exact hsPacket
  have hpn : w.p ≠ w.n := by
    intro he; have hv := congrArg (s k t) he; rw [ar.nValue] at hv; change w.P = -w.D at hv; omega
  have hpb : w.p ≠ w.beta := by
    intro he; have hv := congrArg (s k t) he; change w.P = w.L at hv; omega
  have hnb : w.n ≠ w.beta := by
    intro he; have hv := congrArg (s k t) he; rw [ar.nValue] at hv; change -w.D = w.L at hv; omega
  have hI : w.inserted.Nodup := by simp only [SourceWord.inserted, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, hpn.symm, hnb, hpb.symm,
      not_false_eq_true, true_and, List.nodup_nil]
  have hIW : ∀ i ∈ w.inserted, i ∉ w.W := by
    intro i hi
    simp only [SourceWord.inserted, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact h.nFresh
    · exact h.betaFresh
    · exact h.pFresh
  have hIL : ∀ i ∈ w.inserted, Large k t i := by
    intro i hi
    simp only [SourceWord.inserted, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> assumption
  have hperm : (V ++ w.ret).Perm (w.W ++ w.inserted) := by
    apply List.perm_iff_count.mpr
    intro i
    have hcT := hT.count_eq i
    have hcA := hphysical.count_eq i
    simp only [V, SourceWord.ret, SourceWord.late,
      SourceWord.W, oldWord, SourceWord.inserted, SourceWord.x,
      List.count_append, List.count_cons, List.count_nil] at hcT hcA ⊢
    omega
  have hRetOld : ∀ i ∈ w.ret, i ∈ w.W := by
    intro i hi
    simp only [SourceWord.ret, SourceWord.late, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    simp only [SourceWord.W, oldWord, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have inv := inventory_of_perm h.hk t w.W V w.inserted w.ret
    h.oldLegal.1 hI hIW hRetOld hIL hperm
  have hIg : largeUsed k t w.inserted = 3 := by
    simp only [SourceWord.inserted, largeUsed, mass, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, largeWeight, hnL, hbL, hpL, ite_true, add_zero]
    rfl
  have hIh : H k t w.inserted = 3 ^ (s k t w.n).natAbs +
      3 ^ (s k t w.beta).natAbs + 3 ^ (s k t w.p).natAbs := by
    simp only [SourceWord.inserted, H, mass, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, energyWeight, hnL, hbL, hpL, ite_true, s,
      add_zero, Nat.add_assoc]
  obtain ⟨_, hRg, hRh⟩ := tail_weights w h ar
  have hG : G k t V = G k t w.W := by
    have hb := inv.largeBalance
    rw [hIg, hRg] at hb
    omega
  have hU : MixedSuffixEnergy.U V = MixedSuffixEnergy.U w.W + w.late.length := by
    have hb := inv.countBalance
    simp only [SourceWord.inserted, SourceWord.ret, SourceWord.late,
      List.length_append, List.length_cons, List.length_nil] at hb ⊢
    omega
  have hEnergy := inv.energyBalance
  rw [hIh, hRh] at hEnergy
  have hPabs : ((s k t w.p).natAbs : ℤ) = w.P := by
    rw [Int.natCast_natAbs, abs_of_pos hp0]
  have hDabs : ((s k t w.n).natAbs : ℤ) = w.D := Int.natCast_natAbs _
  have hLabs : ((s k t w.beta).natAbs : ℤ) = w.L := by
    rw [Int.natCast_natAbs, abs_of_pos (by omega : 0 < w.L)]
  have hrabs : ((s k t w.x).natAbs : ℤ) = w.r := by
    rw [Int.natCast_natAbs, abs_of_pos (by omega : 0 < w.r)]
  have h3 := three_energy (s k t w.p).natAbs (s k t w.n).natAbs
    (s k t w.beta).natAbs (s k t w.x).natAbs
    (by omega) (by omega) (by omega)
  have hH : H k t V < H k t w.W := by omega
  have hj : J k t V < J k t w.W :=
    Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩)
  have hend : mass (s k t) V = w.v - w.tau := by
    change mass (s k t) ((Astar ++ Tstar) ++
      [w.beta, w.y, w.p, w.a]) = _
    rw [show mass (s k t) ((Astar ++ Tstar) ++
        [w.beta, w.y, w.p, w.a]) =
        mass (s k t) (Astar ++ Tstar) +
          mass (s k t) [w.beta, w.y, w.p, w.a] by
      simp only [mass, List.map_append, List.sum_append]]
    rw [hmCore]
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, ar.parentValue]
    dsimp only [SourceWord.delta, SourceWord.e, SourceWord.tau, SourceWord.Y]
    ring
  have hcountA : V.count w.a = 1 := by
    have hle := (List.nodup_iff_count_le_one.mp inv.nodup) w.a
    have hmem : w.a ∈ V := by simp [V]
    have hne : V.count w.a ≠ 0 := fun he => (List.count_eq_zero.mp he) hmem
    omega
  have hsm := (returned_small w h ar).2
  refine ⟨Tstar, hT, ⟨⟨legal_of_strip inv.nodup hsV, hsV,
    fun j => by simpa only [mass, zero_add] using inStrip_prefix hsV j,
    inv, hperm, hend, ?_, ?_, ?_, hj⟩, ar.parentValue, hcountA, hG, hU, ?_, hH⟩⟩
  · simpa only [hend] using inv.complementSum
  · simpa only [hsm] using inv.smallPartition
  · simpa only [hsm] using inv.smallDisjoint
  · dsimp only [V] at hEnergy
    omega

/-- The old one-slot construction is an adapter into the same completion. -/
private theorem complete_used {k t : ℕ} (w : SourceWord k t) (h : Residual w)
    (ar : Arithmetic w) (U R Rstar : List (Fin k))
    (hA : w.A = U ++ [w.a] ++ R) (hR : Rstar.Perm R)
    (hsR : InStrip (s k t) (C k) (mass (s k t) U - w.D) Rstar) :
    ∃ Tstar : List (Fin k), Tstar.Perm w.T0 ∧
      (let V := w.usedWord U Rstar Tstar
       FullExchange w V w.inserted w.ret (w.v - w.tau) ∧
       s k t w.a = -w.M ∧ V.count w.a = 1 ∧
       G k t V = G k t w.W ∧ MixedSuffixEnergy.U V = MixedSuffixEnergy.U w.W + w.late.length ∧
       H k t V + 3 ^ (s k t w.x).natAbs + 3 ^ (s k t w.zpen).natAbs +
           3 ^ (s k t w.z).natAbs =
         H k t w.W + 3 ^ (s k t w.p).natAbs + 3 ^ (s k t w.n).natAbs +
           3 ^ (s k t w.beta).natAbs ∧ H k t V < H k t w.W) := by
  classical
  obtain ⟨hsU, hsOldR, hu, hmR⟩ := old_prefix w h ar U R hA
  have ho := ar.order
  have hQ := ar.Qpos
  have hstart : 0 ≤ mass (s k t) U - w.D ∧
      mass (s k t) U - w.D ≤ C k := by omega
  have hmRstar : mass (s k t) Rstar = mass (s k t) R := (hR.map _).sum_eq
  have hsN : InStrip (s k t) (C k) (mass (s k t) U) [w.n] := by
    change 0 ≤ mass (s k t) U ∧ mass (s k t) U ≤ C k ∧
      0 ≤ mass (s k t) U + s k t w.n ∧
        mass (s k t) U + s k t w.n ≤ C k
    rw [ar.nValue]
    omega
  have hsUN : InStrip (s k t) (C k) 0 (U ++ [w.n]) :=
    inStrip_append hsU (by simpa only [zero_add, mass] using hsN)
  have hsPstar : InStrip (s k t) (C k) 0 (U ++ [w.n] ++ Rstar) := by
    apply inStrip_append hsUN
    simpa only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add,
      ar.nValue, sub_eq_add_neg] using hsR
  have hmPstar : mass (s k t) (U ++ [w.n] ++ Rstar) = w.a0 + w.theta := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    change mass (s k t) U + s k t w.n + mass (s k t) Rstar = w.a0 + w.theta
    rw [ar.nValue, hmRstar]
    dsimp only [SourceWord.theta]
    omega
  have hphysical : ((U ++ [w.n] ++ Rstar) ++ [w.a]).Perm (w.A ++ [w.n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hcR := hR.count_eq i
    have hcA := congrArg (List.count i) hA
    simp only [List.count_append, List.count_cons, List.count_nil] at hcR hcA ⊢
    omega
  simpa only [SourceWord.usedWord, List.append_assoc] using
    complete_constructed w h ar (U ++ [w.n] ++ Rstar) hsPstar hmPstar hphysical

set_option maxHeartbeats 1800000 in
-- Complete-batch orders, physical partitions and energy balances are composed here.
/-- Reuse the ACTUAL parent occurring in A=U,[a],R. Either compatibility of
the FULL R or the explicit old LARGE upper test constructs Rstar. Both
endpoints and both literal LARGE sides are proved below from source+oldLegal.
Complete T0 is then reordered in the shared completion. No new arrival,
endpoint, reserve, favorable competitor or fixed-orbit minimum is a premise. -/
theorem actualSource_used_oddHalf_parent_exchange_full
    {k t : ℕ} (w : SourceWord k t) (h : Residual w)
    (U R : List (Fin k)) (hA : w.A = U ++ [w.a] ++ R)
    (horder : Compatible (s k t) (C k) R ∨ UpperTest w U R) :
    ∃ Rstar Tstar : List (Fin k), Rstar.Perm R ∧ Tstar.Perm w.T0 ∧
      (let V := w.usedWord U Rstar Tstar
       FullExchange w V w.inserted w.ret (w.v - w.tau) ∧
       s k t w.a = -w.M ∧ V.count w.a = 1 ∧
       G k t V = G k t w.W ∧ MixedSuffixEnergy.U V = MixedSuffixEnergy.U w.W + w.late.length ∧
       H k t V + 3 ^ (s k t w.x).natAbs + 3 ^ (s k t w.zpen).natAbs +
           3 ^ (s k t w.z).natAbs =
         H k t w.W + 3 ^ (s k t w.p).natAbs + 3 ^ (s k t w.n).natAbs +
           3 ^ (s k t w.beta).natAbs ∧ H k t V < H k t w.W) := by
  classical
  have ar := arithmetic w h
  obtain ⟨hsU, hsOldR, hu, hmR⟩ := old_prefix w h ar U R hA
  have ho := ar.order
  have hQ := ar.Qpos
  have hshift := ar.shift
  have hstart : 0 ≤ mass (s k t) U - w.D ∧
      mass (s k t) U - w.D ≤ C k := by omega
  have hend : 0 ≤ mass (s k t) U - w.D + mass (s k t) R ∧
      mass (s k t) U - w.D + mass (s k t) R ≤ C k := by
    have he := ar.newEnd
    dsimp only [SourceWord.theta] at he
    omega
  have ordered : ∃ Rstar : List (Fin k), Rstar.Perm R ∧
      InStrip (s k t) (C k) (mass (s k t) U - w.D) Rstar := by
    rcases horder with hcompatible | htest
    · exact exists_order_between (s k t) R (C k) (mass (s k t) U - w.D)
        hstart (by simpa only [mass] using hend) hcompatible
    · have boundaries : ∀ (R0 : List (Fin k)) (i : Fin k) (R1 : List (Fin k)),
          R = R0 ++ [i] ++ R1 → Q k ≤ |s k t i| →
          (0 ≤ (mass (s k t) U - w.D) + mass (s k t) R0 ∧
            (mass (s k t) U - w.D) + mass (s k t) R0 ≤ C k) ∧
          (0 ≤ (mass (s k t) U - w.D) + mass (s k t) R0 + s k t i ∧
            (mass (s k t) U - w.D) + mass (s k t) R0 + s k t i ≤ C k) := by
        intro R0 i R1 hsplit hi
        have hs := (strip_split R0 ([i] ++ R1)
          (by simpa only [hsplit, List.append_assoc] using hsOldR)).2
        change InStrip (s k t) (C k)
          ((mass (s k t) U - w.M) + mass (s k t) R0) (i :: R1) at hs
        have hd0 := hs.1
        have hdC := hs.2.1
        have harr := inStrip_prefix hs.2.2 0
        simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at harr
        have ht := htest R0 i R1 hsplit hi
        have hdep : mass (s k t) (U ++ [w.a] ++ R0) =
            mass (s k t) U - w.M + mass (s k t) R0 := by
          simp only [mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero, ar.parentValue]
          ring
        have harrEq : mass (s k t) (U ++ [w.a] ++ R0 ++ [i]) =
            mass (s k t) U - w.M + mass (s k t) R0 + s k t i := by
          simp only [mass, List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero, ar.parentValue]
          ring
        by_cases hpos : 0 < s k t i
        · have hupper := ht.1 hpos
          rw [harrEq] at hupper
          rw [abs_of_pos hpos] at hi
          -- Positive LARGE: its old departure is <=Q-1. Its old ARRIVAL
          -- is the tested upper side. Both lower sides rise by theta>0.
          have hc := ar.cap
          dsimp only [SourceWord.theta] at hshift hupper
          omega
        · have hneg : s k t i < 0 := by
            have hnonpos : s k t i ≤ 0 := by omega
            rw [abs_of_nonpos hnonpos] at hi
            omega
          have hupper := ht.2 hneg
          rw [hdep] at hupper
          rw [abs_of_neg hneg] at hi
          -- Negative LARGE: its old arrival is <=Q-1. Its old DEPARTURE
          -- is the tested upper side. No translated SMALL prefix is used.
          have hc := ar.cap
          dsimp only [SourceWord.theta] at hshift hupper
          omega
      obtain ⟨Rstar, hR, hfilter, hsR⟩ :=
        LargeSkeletonOrdering.exists_order_preserving_large (s k t) (Q k) (C k)
          ar.Qpos (by have hc := ar.cap; omega) R (mass (s k t) U - w.D)
          hstart (by simpa only [mass] using hend)
          (by simpa only [mass] using boundaries)
      exact ⟨Rstar, hR, hsR⟩
  obtain ⟨Rstar, hR, hsR⟩ := ordered
  obtain ⟨Tstar, hT, hcomplete⟩ := complete_used w h ar U R Rstar hA hR hsR
  exact ⟨Rstar, Tstar, hR, hT, hcomplete⟩

end D5.S3.Combinatorics.Circle.OddHalfParentExchange
