/- GID: D5/S3/Combinatorics/Circle/FourNegativeSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegativeSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Physical positive flux excludes four negative LARGE labels at an original minimum. -/
import D5.S3.Combinatorics.Circle.BinaryRunSource
import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange

/-! Positive supply is counted on physical labels, including repeated values and zero.
The original arbitrary signed-prefix minimum has at least five negative LARGE labels.
The remaining branches of Circle C3.1 are open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace D5.S3.Combinatorics.Circle.FourNegativeSource
open SourceWidth ExpandingSourcePath MixedSuffixEnergy
open TwoOppositeLargeExchange ThreeLargePacketExchange BinaryRunSource
open scoped BigOperators

/-- A finite centered-doubling permutation balances the LARGE sign crossings.
Its positive SMALL mass is exactly the excess of positive LARGE mass over the
positive arrivals from negative LARGE labels. No orbit or value injectivity is assumed. -/
theorem permutation_doubleStep_positive_flux
    {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Equiv.Perm α) (f : α → ℤ) (q : ℤ)
    (hq : 0 < q)
    (hbound : ∀ i, -(2 * q - 1) ≤ f i ∧ f i ≤ 2 * q - 1)
    (hstep : ∀ i, f (ρ i) = doubleStep (4 * q - 1) (f i)) :
    let SP := Finset.univ.filter (fun i => 0 < f i ∧ f i < q)
    let PL := Finset.univ.filter (fun i => q ≤ f i)
    let NL := Finset.univ.filter (fun i => f i ≤ -q)
    PL.card = NL.card ∧
      (∑ i ∈ SP, f i) + (∑ i ∈ NL, f (ρ i)) = ∑ i ∈ PL, f i := by
  classical
  dsimp only
  let SP := Finset.univ.filter (fun i => 0 < f i ∧ f i < q)
  let PL := Finset.univ.filter (fun i => q ≤ f i)
  let NL := Finset.univ.filter (fun i => f i ≤ -q)
  let Pos := Finset.univ.filter (fun i => 0 < f i)
  have hpos (i : α) : 0 < f (ρ i) ↔ (0 < f i ∧ f i < q) ∨ f i ≤ -q := by
    rw [hstep]
    have hb := hbound i
    unfold doubleStep
    split_ifs <;> omega
  have hsmall (i : α) (hi : i ∈ SP) : f (ρ i) = 2 * f i := by
    have hi' : 0 < f i ∧ f i < q := (Finset.mem_filter.mp hi).2
    rw [hstep, doubleStep, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hd1 : Disjoint SP PL := by
    simp only [Finset.disjoint_left, SP, PL, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hd2 : Disjoint SP NL := by
    simp only [Finset.disjoint_left, SP, NL, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hp1 : Pos = SP ∪ PL := by
    ext i
    simp only [Pos, SP, PL, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hp2 : Pos = (SP ∪ NL).image ρ := by
    ext i
    constructor
    · intro hi
      refine Finset.mem_image.mpr ⟨ρ.symm i, ?_, ρ.apply_symm_apply i⟩
      have hh : 0 < f (ρ (ρ.symm i)) := by simpa [Pos] using hi
      simpa only [SP, NL, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] using (hpos (ρ.symm i)).mp hh
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hh : (0 < f j ∧ f j < q) ∨ f j ≤ -q := by
        simpa only [SP, NL, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and] using hj
      simpa only [Pos, Finset.mem_filter, Finset.mem_univ, true_and] using (hpos j).mpr hh
  have hc1 : Pos.card = SP.card + PL.card := by rw [hp1, Finset.card_union_of_disjoint hd1]
  have hc2 : Pos.card = SP.card + NL.card := by
    rw [hp2, Finset.card_image_of_injective _ ρ.injective, Finset.card_union_of_disjoint hd2]
  have hs1 : (∑ i ∈ Pos, f i) = (∑ i ∈ SP, f i) + ∑ i ∈ PL, f i := by
    rw [hp1, Finset.sum_union hd1]
  have hs2 : (∑ i ∈ Pos, f i) = 2 * (∑ i ∈ SP, f i) + ∑ i ∈ NL, f (ρ i) := by
    rw [hp2, Finset.sum_image (fun _ _ _ _ h => ρ.injective h), Finset.sum_union hd2]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hsmall
  change PL.card = NL.card ∧
    (∑ i ∈ SP, f i) + (∑ i ∈ NL, f (ρ i)) = ∑ i ∈ PL, f i
  exact ⟨by omega, by omega⟩

set_option maxHeartbeats 1200000 in
/-- In the literal original arbitrary signed-A configuration, an all-length
Legal J minimum has at least five physical negative LARGE source labels.
The proof excludes four by global positive supply and one original tail cut. -/
theorem actualSource_minimum_negativeLargeCount_ge_five
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * s k t p)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hPY : s k t p < -s k t y)
    (hmin : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V) :
    5 ≤ actualNegativeLargeCount k t := by
  classical
  by_contra hgoal
  let f := s k t
  change 0 < f p at hpositive
  change f p < -f y at hPY
  change Q k ≤ -f zpen at hzpenlarge
  change Q k ≤ -f z at hzlarge
  let ρ := finRotate k
  let n := hit k 1 p
  let x := hit k 2 p
  let W := oldWord p y zpen z A T0 T1 T2 E
  let L0 := A ++ [x] ++ T0
  let L1 := L0 ++ [y] ++ T1
  let F1 := L1 ++ [zpen]
  let L2 := F1 ++ T2
  let F2 := L2 ++ [z]
  let SP := Finset.univ.filter (fun i => 0 < f i ∧ f i < Q k)
  let PL := Finset.univ.filter (fun i => Q k ≤ f i)
  let NL := Finset.univ.filter (fun i => f i ≤ -Q k)
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have hbound (i : Fin k) : -C k ≤ f i ∧ f i ≤ C k := centered_bounds hNpos hodd _
  have hstep (i : Fin k) : f (ρ i) = doubleStep (N k) (f i) := by
    have he := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2 i
    change 2 * f i - f (ρ i) = N k *
      (if N k < 4 * f i then 1 else if 4 * f i < -N k then -1 else 0) at he
    unfold doubleStep
    split_ifs at * <;> omega
  have hflux := permutation_doubleStep_positive_flux ρ f (Q k) (by omega)
    (by intro i; simpa only [← hC] using hbound i)
    (by intro i; simpa only [← hN] using hstep i)
  change PL.card = NL.card ∧
    (∑ i ∈ SP, f i) + (∑ i ∈ NL, f (ρ i)) = ∑ i ∈ PL, f i at hflux
  have hpabs : |s k t p| = s k t p := abs_of_pos hpositive
  have geo := native_geometry hk t p hnlarge (by simpa [hpabs] using hexpand)
  have hnval : f n = -|f n| := by
    simpa [f, n, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = |f x| := by
    simpa [f, x, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : |f n| < f p := by simpa [f, n, hpabs] using geo.strictOrder.1
  have hPx : f p < f x := by simpa [f, x, abs_of_pos hpositive, ← hxval] using geo.strictOrder.2
  have hfirst : |f n| = N k - 2 * f p := by
    simpa [f, n, hpabs] using geo.firstEquation
  have hD : Q k ≤ |f n| := hnlarge
  have hY : Q k ≤ -f y := by omega
  have hrot : ρ n = x := by simp [ρ, n, x, hit, Function.iterate_succ_apply']
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  have hsub : [y,zpen,z].Sublist W := by
    simpa only [W, oldWord, x, List.nil_append, List.append_nil, List.cons_append] using
      ((((((((List.nil_sublist A).append (List.nil_sublist [x])).append
        (List.nil_sublist T0)).append (List.Sublist.refl [y])).append
        (List.nil_sublist T1)).append (List.Sublist.refl [zpen])).append
        (List.nil_sublist T2)).append (List.Sublist.refl [z])).append (List.nil_sublist E)
  have hnd : [n,y,zpen,z].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, hW.1.sublist hsub⟩
    intro hn
    exact hnunused (hsub.subset hn)
  have hcard : ({n,y,zpen,z} : Finset (Fin k)).card = 4 := by
    simpa using List.toFinset_card_of_nodup hnd
  have hsubset : ({n,y,zpen,z} : Finset (Fin k)) ⊆ NL := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [NL, Finset.mem_filter, Finset.mem_univ, true_and] <;> omega
  have hfour : NL.card = 4 := by
    have hlo := Finset.card_le_card hsubset
    have hhi : NL.card < 5 := by simpa only [NL, f, s, Q, actualNegativeLargeCount] using Nat.lt_of_not_ge hgoal
    omega
  have hNL : NL = {n,y,zpen,z} := (Finset.eq_of_subset_of_card_le hsubset (by omega)).symm
  have hnd' : [n,zpen,z].Nodup := hnd.sublist (by simp)
  have hnegstep (i : Fin k) (hi : Q k ≤ -f i) :
      f (ρ i) = N k + 2 * f i ∧ 0 < f (ρ i) := by
    have hb := hbound i
    rw [hstep, doubleStep, ite_eq_right (by omega), ite_eq_left (by omega)]
    constructor <;> omega
  have hzp := hnegstep zpen hzpenlarge
  have hz := hnegstep z hzlarge
  have hy := hnegstep y hY
  have hchild : (0 < f (ρ zpen) ∧ f (ρ zpen) < Q k) ∨
      (0 < f (ρ z) ∧ f (ρ z) < Q k) := by
    by_contra hc
    have hzpPL : Q k ≤ f (ρ zpen) := by omega
    have hzPL : Q k ≤ f (ρ z) := by omega
    let K : Finset (Fin k) := {ρ n,ρ zpen,ρ z}
    have hKcard : K.card = 3 := by
      have hh := List.toFinset_card_of_nodup (hnd'.map ρ.injective)
      simpa [K] using hh
    have hKsub : K ⊆ PL := by
      intro i hi
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;>
        simp only [PL, Finset.mem_filter, Finset.mem_univ, true_and]
      · rw [hrot]; omega
      · exact hzpPL
      · exact hzPL
    have hres : (PL \ K).card = 1 := by
      rw [Finset.card_sdiff_of_subset hKsub, hflux.1, hfour, hKcard]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hres
    have hsumPL : (∑ i ∈ PL, f i) = f u + f (ρ n) + f (ρ zpen) + f (ρ z) := by
      have he := Finset.sum_sdiff (f := f) hKsub
      rw [hu, Finset.sum_singleton] at he
      have hsumK : (∑ i ∈ K, f i) = f (ρ n) + f (ρ zpen) + f (ρ z) := by
        have hh := List.sum_toFinset f (hnd'.map ρ.injective)
        simpa [K, mass, add_assoc] using hh
      rw [hsumK] at he
      omega
    have hsumNL : (∑ i ∈ NL, f (ρ i)) =
        f (ρ n) + f (ρ y) + f (ρ zpen) + f (ρ z) := by
      have hh := List.sum_toFinset (fun i => f (ρ i)) hnd
      simpa [hNL, add_assoc] using hh
    have hsupply : (∑ i ∈ SP, f i) ≤ -f y - 1 := by
      have hb := hbound u
      have hyb := hbound y
      have he := hflux.2
      rw [hsumPL, hsumNL] at he
      omega
    let v := mass f (L0 ++ [y])
    let a2 := mass f F2
    have hdep : v - f y ≤ C k := by
      have hh := inStrip_prefix ((strip_split L0 ([y] ++ T1 ++ [zpen] ++ T2 ++ [z] ++ E)
        (by simpa only [L0, W, oldWord, x, List.append_assoc] using hsW)).2) 0
      have hv : v = mass f L0 + f y := by simp [v, mass]
      simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero, zero_add] at hh
      omega
    have ha2 : 0 ≤ a2 := by
      have hh := inStrip_prefix ((strip_split F2 E
        (by simpa only [F2, L2, F1, L1, L0, W, oldWord, x, List.append_assoc] using hsW)).2) 0
      simpa only [a2, List.take_zero, List.map_nil, List.sum_nil, add_zero, zero_add] using hh.1
    have hmass : mass f (T1 ++ T2) = -f zpen - f z + a2 - v := by
      simp only [a2, F2, L2, F1, L1, v, mass, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      ring
    have hdemand : -f y + 1 ≤ mass f (T1 ++ T2) := by rw [hmass]; omega
    have hsubT : (T1 ++ T2).Sublist W := by
      simpa only [W, oldWord, x, List.nil_append, List.append_nil] using
        ((((((((List.nil_sublist A).append (List.nil_sublist [x])).append
          (List.nil_sublist T0)).append (List.nil_sublist [y])).append
          (List.Sublist.refl T1)).append (List.nil_sublist [zpen])).append
          (List.Sublist.refl T2)).append (List.nil_sublist [z])).append (List.nil_sublist E)
    let Pos := (T1 ++ T2).filter (fun i => decide (0 < f i))
    have hPosnd : Pos.Nodup := (hW.1.sublist hsubT).filter _
    have hPosSub : Pos.toFinset ⊆ SP := by
      intro i hi
      have hm := List.mem_filter.mp (List.mem_toFinset.mp hi)
      have hsm := hsmall i (by
        simp only [smallWord, List.mem_append] at *
        tauto)
      simp only [SP, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨of_decide_eq_true hm.2, (abs_lt.mp hsm).2⟩
    have hbank : mass f (T1 ++ T2) ≤ ∑ i ∈ SP, f i := by
      calc
        _ ≤ mass f Pos := positive_mass_dominates f (T1 ++ T2)
        _ = ∑ i ∈ Pos.toFinset, f i := (List.sum_toFinset f hPosnd).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hPosSub (by
          intro i hi _
          exact ((Finset.mem_filter.mp hi).2.1).le)
    omega
  have hcut (u : Fin k) (L R : List (Fin k))
      (hword : L ++ [u] ++ R = W) (hu : Q k ≤ -f u)
      (hsc : 0 < f (ρ u) ∧ f (ρ u) < Q k) :
      mass f (L ++ [u]) < C k - f p := by
    have hs := (strip_split L ([u] ++ R)
      (by simpa only [← List.append_assoc, hword] using hsW)).2
    have hd := inStrip_prefix hs 0
    have ha := inStrip_prefix hs 1
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero, zero_add] at hd
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, zero_add] at ha
    have hmag : 3 * Q k ≤ -2 * f u := by
      have he := (hnegstep u hu).1
      omega
    have hm : mass f (L ++ [u]) = mass f L + f u := by simp [mass]
    omega
  have hsmallT2 (i : Fin k) (hi : i ∈ T2) : |s k t i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have hsmallE (i : Fin k) (hi : i ∈ E) : |s k t i| < Q k :=
    hsmall i (by simp [smallWord, hi])
  have hT2 := (small_weights t T2 hsmallT2).1
  have hE := (small_weights t E hsmallE).1
  have hzL : Large k t z := by
    have : f z < 0 := by omega
    change Q k ≤ |f z|
    rw [abs_of_neg this]
    exact hzlarge
  rcases hchild with hc | hc
  · have hcut1 := hcut zpen L1 (T2 ++ [z] ++ E)
      (by simp only [L1, L0, W, oldWord, x, List.append_assoc]) hzpenlarge hc
    have hw : F1 ++ (T2 ++ [z] ++ E) = W := by
      simp only [F1, L1, L0, W, oldWord, x, List.append_assoc]
    have hreturn : largeUsed k t (T2 ++ [z] ++ E) ≤ 1 := by
      simpa [largeUsed, mass, largeWeight, hzL, add_assoc] using (show
        largeUsed k t T2 + 1 + largeUsed k t E ≤ 1 by omega)
    have hh := FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
      k t hk p F1 (T2 ++ [z] ++ E) hpositive hnlarge
      (by simpa [hpabs] using hexpand)
      (by simpa only [hw] using hW) (by simpa only [hw] using hpunused)
      (by simpa only [hw] using hnunused) hcut1.le hreturn
    have hstrict : J k t (F1 ++ [p,n]) < J k t W := by simpa only [hw, n] using hh.2.2.2.2.2
    exact (not_lt_of_ge (hmin _ hh.1)) hstrict
  · have hcut2 := hcut z L2 E
      (by simp only [L2, F1, L1, L0, W, oldWord, x, List.append_assoc]) hzlarge hc
    have hw : F2 ++ E = W := by
      simp only [F2, L2, F1, L1, L0, W, oldWord, x, List.append_assoc]
    have hh := FirstNegativeShiftExchange.actualSource_prefix_pair_truncation
      k t hk p F2 E hpositive hnlarge (by simpa [hpabs] using hexpand)
      (by simpa only [hw] using hW) (by simpa only [hw] using hpunused)
      (by simpa only [hw] using hnunused) hcut2.le (by omega)
    have hstrict : J k t (F2 ++ [p,n]) < J k t W := by simpa only [hw, n] using hh.2.2.2.2.2
    exact (not_lt_of_ge (hmin _ hh.1)) hstrict

end D5.S3.Combinatorics.Circle.FourNegativeSource
