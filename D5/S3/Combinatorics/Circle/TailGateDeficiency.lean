/- GID: D5/S3/Combinatorics/Circle/TailGateDeficiency
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TailGateDeficiency
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: A minimum forces a sharp gate-specific sign deficiency in its physical middle tail. -/
module
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange
public import D5.S3.Combinatorics.Circle.PositiveSmallReturnExchange

/-! # Two gates sharing one physical tail

Negative mass moved left repairs the first retained negative gate; positive
mass moved right independently repairs the second. One complement retains every
other physical occurrence. The resulting deficiency is necessary at the original
minimum; it does not supply a global transport across arbitrary signed A.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.TailGateDeficiency
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange FirstNegativeShiftExchange

/-- The complete bounded positive pool, with each physical occurrence retained. -/
def signPool {k : ℕ} (f : Fin k → ℤ) (T : List (Fin k)) (cutoff : ℤ) : List (Fin k) :=
  T.filter (fun i => decide (0 < f i ∧ f i ≤ cutoff))

private theorem select_gate {k : ℕ} (f : Fin k → ℤ) (T : List (Fin k))
    (a theta delta : ℤ) (ha : 0 ≤ a) (htheta : 0 ≤ theta)
    (hdelta : 0 < delta)
    (hsupply : delta ≤ theta + mass f (signPool f T (a + theta + 1))) :
    ∃ L : List (Fin k), L.Sublist T ∧ (∀ i ∈ L, 0 < f i) ∧
      delta - theta ≤ mass f L ∧ mass f L ≤ delta + a := by
  classical
  by_cases htarget : 0 < delta - theta
  · obtain ⟨L, hL, hlo, hhi⟩ := PositiveSmallReturnExchange.first_crossing f
      (signPool f T (a + theta + 1)) (a + theta) (by omega)
      (delta - theta) htarget
      (by intro i hi; simpa [signPool] using (List.mem_filter.mp hi).2)
      (by omega)
    refine ⟨L, hL.trans (List.filter_sublist), ?_, hlo, by omega⟩
    intro i hi
    exact (of_decide_eq_true (List.mem_filter.mp (hL.subset hi)).2).1
  · exact ⟨[], List.nil_sublist _, by simp, by simpa [mass] using (show delta - theta ≤ 0 by omega),
      by simpa [mass] using (show 0 ≤ delta + a by omega)⟩

private theorem one_complement {k : ℕ} (f : Fin k → ℤ)
    (T N P : List (Fin k)) (hT : T.Nodup)
    (hN : N.Sublist T) (hP : P.Sublist T)
    (hNneg : ∀ i ∈ N, 0 < -f i) (hPpos : ∀ i ∈ P, 0 < f i) :
    ∃ R : List (Fin k), (N ++ R ++ P).Perm T := by
  classical
  have hdis : N.Disjoint P := List.disjoint_left.mpr (by
    intro i hiN hiP
    have hn := hNneg i hiN
    have hp := hPpos i hiP
    omega)
  have hnod : (N ++ P).Nodup := (hN.nodup hT).append (hP.nodup hT) hdis
  have hsub : (N ++ P).Subperm T := List.subperm_of_subset hnod (by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hN.subset hi
    · exact hP.subset hi)
  let R := T.diff (N ++ P)
  have hp : ((N ++ P) ++ R).Perm T :=
    List.subperm_append_diff_self_of_count_le (fun i _ => hsub.count_le i)
  refine ⟨R, (List.perm_iff_count.mpr ?_).trans hp⟩
  intro i
  simp only [List.count_append]
  omega

private theorem no_large_append {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (W : List (Fin k)) (u : Fin k) (hW : Legal k t W) (hu : u ∉ W)
    (hL : Large k t u) (hmin : ∀ V, Legal k t V → J k t W ≤ J k t V) :
    ¬ (0 ≤ mass (s k t) W + s k t u ∧
      mass (s k t) W + s k t u ≤ C k) := by
  classical
  apply TerminalLargeSubstitution.blocked_gate hW hu
  intro hv
  have inv := inventory_of_perm hk t W (W ++ [u]) [u] [] hW.1
    (by simp) (by simpa) (by simp) (by simpa using hL) (by simp)
  have hg := inv.largeBalance
  simp only [largeUsed, mass, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, largeWeight, ite_eq_left hL, add_zero] at hg
  have hj : J k t (W ++ [u]) < J k t W :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
  exact (not_lt_of_ge (hmin _ hv)) hj

set_option maxHeartbeats 1600000 in
/-- Under the original twelve conditions, one complete gate-specific sign pool
in the SAME physical T2 is insufficient. There is no clearance, supplied old
margin, favorable-resource or numerical-injectivity premise. -/
theorem actualSource_threeNegative_twoGate_tail_deficiency
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyhigh : s k t p < -s k t y)
    (hminimum : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V) :
    let f := s k t
    let delta := -f y - f p
    let c1 := mass f (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1)
    let c2 := mass f (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2)
    C k - c1 + mass (fun i => -f i) (signPool (fun i => -f i) T2 (C k + f zpen + 1)) < delta ∨
    C k - c2 + mass f (signPool f T2 (C k + f z + 1)) < delta := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let P := f p
  let D := |f n|
  let r := f x
  let B := C k - P
  let delta := -f y - P
  let a0 := mass f A
  let c1 := mass f (A ++ [x] ++ T0 ++ [y] ++ T1)
  let a1 := c1 + f zpen
  let c2 := mass f (A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2)
  let a2 := c2 + f z
  let h := mass f W
  change 0 < f p at hpositive
  change Q k ≤ |f n| at hnlarge
  change N k < 3 * |f p| at hexpand
  change Q k ≤ -f zpen at hzpenlarge
  change Q k ≤ -f z at hzlarge
  change f p < -f y at hyhigh
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hNp, hNo⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    have hv := geo.nValue
    change orient (decide (f p < 0)) (f n) = -D at hv
    simpa only [orient, show ¬ f p < 0 by omega, decide_false, Bool.false_eq_true, ite_false] using hv
  have hxabs : f x = |f x| := by
    have hv := geo.xValue
    change orient (decide (f p < 0)) (f x) = |f x| at hv
    simpa only [orient, show ¬ f p < 0 by omega, decide_false, Bool.false_eq_true, ite_false] using hv
  have hDP : D < P := by simpa [D, n, f, hpabs] using geo.strictOrder.1
  have hPr : P < r := by
    simpa only [P, r, f, x, abs_of_pos hpositive, ← hxabs] using geo.strictOrder.2
  have hD : Q k ≤ D := hnlarge
  have hnative : D = 2 * B + 1 ∧ r = 2 * P - D := by
    have he1 := geo.firstEquation
    have he2 := geo.secondEquation
    change D = N k - 2 * |f p| at he1
    change |f x| = 4 * |f p| - N k at he2
    rw [hpabs] at he1 he2
    rw [← hxabs] at he2
    dsimp only [B, P, r]
    omega
  have hbnd (i : Fin k) : -C k ≤ f i ∧ f i ≤ C k := by
    exact centered_bounds hNp hNo _
  have hdelta : 0 < delta ∧ delta ≤ B := by
    have hyb := hbnd y
    dsimp only [delta, B, P, f] at *
    omega
  have hpL := geo.pLarge
  have hnL : Large k t n := geo.nLarge
  have hxL : Large k t x := geo.xLarge
  have hyL : Large k t y := by
    change Q k ≤ |f y|
    have ha := neg_le_abs (f y)
    dsimp only [P, f] at hDP hD
    omega
  have hzL : Large k t z := le_trans hzlarge (neg_le_abs _)
  have hsW := strip_of_legal hW
  have hsA := (strip_split A ([x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
    (by simpa only [W, oldWord, x, List.append_assoc] using hsW)).1
  have ha0 : 0 ≤ a0 := by simpa [a0, mass] using (inStrip_prefix hsA A.length).1
  have ha0r : a0 + r ≤ C k := by
    have hsAx := (strip_split (A ++ [x]) (T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [oldWord, x, List.append_assoc] using hsW)).1
    simpa [a0, r, mass] using (inStrip_prefix hsAx (A ++ [x]).length).2
  have hh : 0 ≤ h ∧ h ≤ C k := by
    simpa [h, W, mass] using inStrip_prefix hsW W.length
  have hbp := no_large_append hk t W p hW hpunused hpL hminimum
  have hbn := no_large_append hk t W n hW hnunused hnL hminimum
  have hblocks : B < h ∧ h < D := by
    change ¬ (0 ≤ h + P ∧ h + P ≤ C k) at hbp
    change ¬ (0 ≤ h + f n ∧ h + f n ≤ C k) at hbn
    rw [hnval] at hbn
    dsimp only [B]
    have hp0 : 0 < P := hpositive
    omega
  have hEsmall (i : Fin k) (hi : i ∈ E) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have h2small (i : Fin k) (hi : i ∈ T2) : |f i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have hEweight := (small_weights t E hEsmall).1
  have h2weight := (small_weights t T2 h2small).1
  have harr1 : B < a1 := by
    by_contra hn
    let F := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen]
    let R := T2 ++ [z] ++ E
    have hw : W = F ++ R := by simp [W, oldWord, F, R, x, List.append_assoc]
    have hr : largeUsed k t R = 1 := by
      simp [R, largeUsed_append, largeUsed_cons, largeWeight, hzL, hEweight, h2weight]
    have hcut : mass f F ≤ B := by
      have hm : mass f F = a1 := by simp [F, a1, c1, mass, add_assoc]
      rw [hm]; omega
    obtain ⟨hv, _, _, _, _, hj⟩ := actualSource_prefix_pair_truncation k t hk p F R
      hpositive hnlarge hexpand (hw ▸ hW) (hw ▸ hpunused) (hw ▸ hnunused) hcut (by omega)
    exact (not_lt_of_ge (hminimum _ hv)) (by simpa [← hw] using hj)
  have harr2 : B < a2 := by
    by_contra hn
    let F := A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2 ++ [z]
    have hw : W = F ++ E := by simp [W, oldWord, F, x, List.append_assoc]
    have hcut : mass f F ≤ B := by
      have hm : mass f F = a2 := by simp [F, a2, c2, mass, add_assoc]
      rw [hm]; omega
    obtain ⟨hv, _, _, _, _, hj⟩ := actualSource_prefix_pair_truncation k t hk p F E
      hpositive hnlarge hexpand (hw ▸ hW) (hw ▸ hpunused) (hw ▸ hnunused) hcut (by omega)
    exact (not_lt_of_ge (hminimum _ hv)) (by simpa [← hw] using hj)
  have hc1 : c1 ≤ C k := by
    have hs : InStrip f (C k) 0 (A ++ [x] ++ T0 ++ [y] ++ T1) := (strip_split (A ++ [x] ++ T0 ++ [y] ++ T1) ([zpen] ++ T2 ++ [z] ++ E)
      (by simpa only [oldWord, x, List.append_assoc] using hsW)).1
    simpa only [List.take_length, zero_add, c1, mass] using (inStrip_prefix hs (A ++ [x] ++ T0 ++ [y] ++ T1).length).2
  have hc2 : c2 ≤ C k := by
    have hs : InStrip f (C k) 0 (A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2) := (strip_split (A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2) ([z] ++ E)
      (by simpa only [oldWord, x, List.append_assoc] using hsW)).1
    simpa only [List.take_length, zero_add, c2, mass] using (inStrip_prefix hs (A ++ [x] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2).length).2
  change C k - c1 + mass (fun i => -f i) (signPool (fun i => -f i) T2 (C k + f zpen + 1)) < delta ∨
    C k - c2 + mass f (signPool f T2 (C k + f z + 1)) < delta
  by_contra hnot
  push Not at hnot
  have ha1 : 0 ≤ a1 := by dsimp only [B] at hnative; omega
  have ha2 : 0 ≤ a2 := by dsimp only [B] at hnative; omega
  obtain ⟨Nm, hNm, hNmneg, hNmlo, hNmhi⟩ := select_gate (fun i => -f i) T2
    a1 (C k - c1) delta ha1 (by omega) hdelta.1 (by
      simpa only [a1, show c1 + f zpen + (C k - c1) + 1 = C k + f zpen + 1 by omega] using hnot.1)
  obtain ⟨Pp, hPp, hPppos, hPplo, hPphi⟩ := select_gate f T2
    a2 (C k - c2) delta ha2 (by omega) hdelta.1 (by
      simpa only [a2, show c2 + f z + (C k - c2) + 1 = C k + f z + 1 by omega] using hnot.2)
  have hT2nod : T2.Nodup := hW.1.sublist (by
    dsimp only [oldWord]
    apply (List.sublist_append_left T2 ([z] ++ E)).trans
    simpa only [List.append_assoc] using
      (List.sublist_append_right (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen]) (T2 ++ [z] ++ E)))
  obtain ⟨R, hpart⟩ := one_complement f T2 Nm Pp hT2nod hNm hPp hNmneg hPppos
  let ns := mass (fun i => -f i) Nm
  let ps := mass f Pp
  have hmneg : mass f Nm = -ns := by
    have hn := List.sum_neg_reverse (Nm.map f)
    simp only [List.sum_reverse, List.map_map, Function.comp_def] at hn
    dsimp only [ns, mass]
    omega
  have hmR : mass f R = mass f T2 + ns - ps := by
    have hm := (hpart.map f).sum_eq
    change mass f (Nm ++ R ++ Pp) = mass f T2 at hm
    simp only [mass, List.map_append, List.sum_append] at hm
    change (Nm.map f).sum = -ns at hmneg
    change (Nm.map f).sum + (R.map f).sum + (Pp.map f).sum = (T2.map f).sum at hm
    change (R.map f).sum = (T2.map f).sum + ns - (Pp.map f).sum
    omega
  have hRsmall (i : Fin k) (hi : i ∈ R) : |f i| < Q k :=
    h2small i (hpart.mem_iff.mp (by simp [hi]))
  let b := a0 + P - D
  let S0 := T0 ++ T1 ++ Nm
  let S2 := E ++ Pp
  have hm1 : b + mass f S0 = c1 + delta - ns := by
    have hr := hnative.2
    dsimp only [r, P] at hr
    have hn := hmneg
    simp only [b, S0, a0, c1, delta, P, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hn ⊢
    omega
  have hc2eq : c2 = a1 + mass f T2 := by
    simp only [a1, c1, c2, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  have hm2 : a1 + delta - ns + mass f R = c2 + delta - ps := by omega
  have heq : h = a2 + mass f E := by
    simp only [h, W, oldWord, a2, c2, x, mass, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  have hmend : a2 + delta - ps + mass f S2 = h + delta := by
    have hm : mass f S2 = mass f E + ps := by simp [S2, ps, mass]
    omega
  have hstart : 0 ≤ b ∧ b ≤ C k := by dsimp only [b]; omega
  have hgate1 : (0 ≤ c1 + delta - ns ∧ c1 + delta - ns ≤ C k) ∧
      (0 ≤ a1 + delta - ns ∧ a1 + delta - ns ≤ C k) := by
    have hz : f zpen < 0 := by omega
    have ha := show a1 = c1 + f zpen from rfl
    change delta - (C k - c1) ≤ ns at hNmlo
    change ns ≤ delta + a1 at hNmhi
    omega
  have hgate2 : (0 ≤ c2 + delta - ps ∧ c2 + delta - ps ≤ C k) ∧
      (0 ≤ a2 + delta - ps ∧ a2 + delta - ps ≤ C k) := by
    have hz' : f z < 0 := by omega
    have ha := show a2 = c2 + f z from rfl
    change delta - (C k - c2) ≤ ps at hPplo
    change ps ≤ delta + a2 at hPphi
    omega
  have hfinal : 0 ≤ h + delta ∧ h + delta ≤ C k := by dsimp only [B] at *; omega
  have compatible (S : List (Fin k)) (hs : ∀ i ∈ S, |f i| < Q k) :
      ∀ q ∈ S, ∀ j ∈ S, 0 < f q → f j < 0 → f q - f j ≤ C k := by
    intro q hq j hj hqp hjn
    have hq' := hs q hq
    have hj' := hs j hj
    rw [abs_of_pos hqp] at hq'
    rw [abs_of_neg hjn] at hj'
    omega
  have hs0 (i : Fin k) (hi : i ∈ S0) : |f i| < Q k := by
    rcases List.mem_append.mp hi with hi | hi
    · exact hsmall i (List.mem_append_left E (List.mem_append_left T2 hi))
    · exact h2small i (hNm.subset hi)
  have hs2 (i : Fin k) (hi : i ∈ S2) : |f i| < Q k := by
    rcases List.mem_append.mp hi with hi | hi
    · exact hEsmall i hi
    · exact h2small i (hPp.subset hi)
  obtain ⟨L0, hL0, hsL0⟩ := exists_order_between f S0 (C k) b hstart
    (by simpa only [mass] using (hm1.symm ▸ hgate1.1)) (compatible S0 hs0)
  obtain ⟨L1, hL1, hsL1⟩ := exists_order_between f R (C k) (a1 + delta - ns) hgate1.2
    (by simpa only [mass] using (hm2.symm ▸ hgate2.1)) (compatible R hRsmall)
  obtain ⟨L2, hL2, hsL2⟩ := exists_order_between f S2 (C k) (a2 + delta - ps) hgate2.2
    (by simpa only [mass] using (hmend.symm ▸ hfinal)) (compatible S2 hs2)
  let V := A ++ [p, n] ++ L0 ++ [zpen] ++ L1 ++ [z] ++ L2
  have hmL0 : mass f L0 = mass f S0 := (hL0.map f).sum_eq
  have hmL1 : mass f L1 = mass f R := (hL1.map f).sum_eq
  have hmL2 : mass f L2 = mass f S2 := (hL2.map f).sum_eq
  have hsPN : InStrip f (C k) a0 [p, n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧
      0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P - D ∧ a0 + P - D ≤ C k
    omega
  have hsHead : InStrip f (C k) 0 (A ++ [p, n]) :=
    inStrip_append hsA (by simpa only [a0, mass, zero_add] using hsPN)
  have madd (X Y : List (Fin k)) : mass f (X ++ Y) = mass f X + mass f Y := by
    simp only [mass, List.map_append, List.sum_append]
  have mh : mass f (A ++ [p, n]) = b := by
    rw [madd]
    simp only [b, a0, mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hnval]
    change (A.map f).sum + (P + -D) = (A.map f).sum + P - D
    omega
  have m0 : mass f (A ++ [p, n] ++ L0) = c1 + delta - ns := by
    rw [madd, mh, hmL0, hm1]
  have m1 : mass f (A ++ [p, n] ++ L0 ++ [zpen]) = a1 + delta - ns := by
    rw [madd, m0]
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    dsimp only [a1]
    omega
  have mR : mass f (A ++ [p, n] ++ L0 ++ [zpen] ++ L1) = c2 + delta - ps := by
    rw [madd, m1, hmL1, hm2]
  have m2 : mass f (A ++ [p, n] ++ L0 ++ [zpen] ++ L1 ++ [z]) = a2 + delta - ps := by
    rw [madd, mR]
    simp only [mass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    dsimp only [a2]
    omega
  simp only [mass] at mh m0 m1 mR m2
  have hsV : InStrip f (C k) 0 V := by
    have hs0' := inStrip_append hsHead (show InStrip f (C k)
        (0 + ((A ++ [p, n]).map f).sum) L0 by
      simpa only [zero_add, mh] using hsL0)
    have hsz1 : InStrip f (C k) (c1 + delta - ns) [zpen] := by
      simp only [InStrip]
      exact ⟨hgate1.1.1, hgate1.1.2, by
        simpa only [a1, add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using hgate1.2⟩
    have hs1' := inStrip_append hs0' (show InStrip f (C k)
        (0 + ((A ++ [p, n] ++ L0).map f).sum) [zpen] by
      simpa only [zero_add, m0] using hsz1)
    have hsR' := inStrip_append hs1' (show InStrip f (C k)
        (0 + ((A ++ [p, n] ++ L0 ++ [zpen]).map f).sum) L1 by
      simpa only [zero_add, m1] using hsL1)
    have hsz2 : InStrip f (C k) (c2 + delta - ps) [z] := by
      simp only [InStrip]
      exact ⟨hgate2.1.1, hgate2.1.2, by
        simpa only [a2, add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using hgate2.2⟩
    have hs2' := inStrip_append hsR' (show InStrip f (C k)
        (0 + ((A ++ [p, n] ++ L0 ++ [zpen] ++ L1).map f).sum) [z] by
      simpa only [zero_add, mR] using hsz2)
    exact inStrip_append hs2' (show InStrip f (C k)
        (0 + ((A ++ [p, n] ++ L0 ++ [zpen] ++ L1 ++ [z]).map f).sum) L2 by
      simpa only [zero_add, m2] using hsL2)
  have hperm : (V ++ [x, y]).Perm (W ++ [p, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have h0 := hL0.count_eq i
    have h1 := hL1.count_eq i
    have h2 := hL2.count_eq i
    have hp := hpart.count_eq i
    simp only [S0, S2, List.count_append] at h0 h2 hp
    simp only [V, W, oldWord, x, n, List.count_append, List.count_cons, List.count_nil]
    omega
  have hpn : p ≠ n := by intro he; have hh := hnval; rw [← he] at hh; change P = -D at hh; omega
  have inv := inventory_of_perm hk t W V [p, n] [x, y] hW.1 (by simp [hpn])
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp [W, oldWord, x])
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hpL
        · exact hnL) hperm
  have hg := inv.largeBalance
  have he := inv.energyBalance
  have hgi : largeUsed k t [p, n] = 2 := by simp [largeUsed, mass, largeWeight, hpL, hnL]
  have hgr : largeUsed k t [x, y] = 2 := by simp [largeUsed, mass, largeWeight, hxL, hyL]
  rw [hgi, hgr] at hg
  have hG : G k t V = G k t W := by omega
  have hei : H k t [p, n] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    simp [H, mass, energyWeight, hpL, hnL, f, s]
  have her : H k t [x, y] = 3 ^ (f x).natAbs + 3 ^ (f y).natAbs := by
    simp [H, mass, energyWeight, hxL, hyL, f, s]
  rw [hei, her] at he
  have henergy := geo.energy
  change (3 : ℕ) ^ (f p).natAbs + 3 ^ (f n).natAbs < 3 ^ (f x).natAbs at henergy
  have hret : (3 : ℕ) ^ (f p).natAbs + 3 ^ (f n).natAbs <
      3 ^ (f x).natAbs + 3 ^ (f y).natAbs :=
    lt_of_lt_of_le henergy (Nat.le_add_right _ _)
  have hHs : H k t V < H k t W := by
    exact Nat.lt_of_add_lt_add_right (he.trans_lt (Nat.add_lt_add_left hret _))
  have hj : J k t V < J k t W := Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHs)⟩)
  exact (not_lt_of_ge (hminimum V (legal_of_strip inv.nodup hsV))) hj

-- Transient integral endpoint application.
example
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyhigh : s k t p < -s k t y)
    (hminimum : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V) :
    let f := s k t
    let delta := -f y - f p
    let c1 := mass f (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1)
    let c2 := mass f (A ++ [hit k 2 p] ++ T0 ++ [y] ++ T1 ++ [zpen] ++ T2)
    C k - c1 + mass (fun i => -f i) (signPool (fun i => -f i) T2 (C k + f zpen + 1)) ≤ delta - 1 ∨
    C k - c2 + mass f (signPool f T2 (C k + f z + 1)) ≤ delta - 1 := by
  have h := actualSource_threeNegative_twoGate_tail_deficiency k t hk p y zpen z A T0 T1 T2 E
    hpositive hnlarge hexpand hW hpunused hnunused hsmall hzpenlarge hzlarge hyhigh hminimum
  dsimp only at h ⊢
  omega

#print axioms actualSource_threeNegative_twoGate_tail_deficiency

end D5.S3.Combinatorics.Circle.TailGateDeficiency
