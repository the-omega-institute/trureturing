/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck
   digest: Seven-bit reachability masks soundly retain cyclic gap prefixes. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute

private def indexedValue {c : Nat} (hc : 0 < c) (h : Fin c → Nat)
    (i : Fin c) (reverse : Bool) (j : Nat) : Nat :=
  h ⟨if reverse then backward c i.val j else forward c i.val j,
    by cases reverse <;> simp [backward, forward, Nat.mod_lt, hc]⟩

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapMaskBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests

/-- A fold of shifted masks records the disjunction of their individual bits. -/
private theorem fold_or_bit (l : List Nat) (old acc s : Nat) :
    (l.foldl (fun mask x => mask ||| (old <<< x)) acc).testBit s =
      (acc.testBit s || l.any fun x => (old <<< x).testBit s) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.any_cons, ih, Nat.testBit_or]
      cases acc.testBit s <;> cases (old <<< x).testBit s <;>
        cases (xs.any fun y => (old <<< y).testBit s) <;> rfl

/-- Every attained prefix sum at most six has its bit set. -/
private theorem reachMask_sound (c m : Nat) (p : List Nat) (i : Nat) (reverse : Bool)
    (value : Nat → Nat)
    (hchoices : ∀ k : Nat, k < c →
      value k ∈ choices m p
        (if reverse then backward c i k else forward c i k))
    (k : Nat) (hk : k ≤ c)
    (hsmall : (∑ j ∈ Finset.range k, value j) ≤ 6) :
    (reachMask c m p i reverse k).testBit
      (∑ j ∈ Finset.range k, value j) = true := by
  induction k with
  | zero => simp [reachMask]
  | succ k ih =>
      have hk' : k ≤ c := by omega
      have hklt : k < c := by omega
      have hprev : (∑ j ∈ Finset.range k, value j) ≤ 6 := by
        rw [Finset.sum_range_succ] at hsmall
        omega
      have hbit := ih hk' hprev
      let t := ∑ j ∈ Finset.range k, value j
      let s := ∑ j ∈ Finset.range (k + 1), value j
      have hst : s = t + value k := by simp [s, t, Finset.sum_range_succ]
      have hv := hchoices k hklt
      have hbit' : (reachMask c m p i reverse k).testBit t = true := hbit
      have hshift : ((reachMask c m p i reverse k) <<< value k).testBit s = true := by
        rw [Nat.testBit_shiftLeft]
        have hs : value k ≤ s := by omega
        have heq : s - value k = t := by omega
        simp [hs, heq, hbit']
      have hany : ((choices m p
          (if reverse then backward c i k else forward c i k)).any
          fun x => ((reachMask c m p i reverse k) <<< x).testBit s) = true := by
        apply List.any_eq_true.mpr
        exact ⟨value k, hv, hshift⟩
      change ((((choices m p
          (if reverse then backward c i k else forward c i k)).foldl
          (fun mask x => mask ||| (reachMask c m p i reverse k <<< x)) 0) % 2 ^ 7).testBit
          (∑ j ∈ Finset.range (k + 1), value j)) = true
      rw [Nat.testBit_mod_two_pow]
      have hs : s < 7 := by dsimp [s]; omega
      simp only [show (∑ j ∈ Finset.range (k + 1), value j) < 7 by exact hs,
        decide_true, Bool.true_and]
      rw [fold_or_bit]
      have hany' : ((choices m p
          (if reverse then backward c i k else forward c i k)).any
          fun x => ((reachMask c m p i reverse k) <<< x).testBit
            (∑ j ∈ Finset.range (k + 1), value j)) = true := by
        simpa only [s] using hany
      have hz : Nat.testBit 0 (∑ j ∈ Finset.range (k + 1), value j) = false := by
        simp
      simpa only [hz, Bool.false_or] using hany'

/-- An attained cyclic prefix appears in the bit-mask hit scan. -/
private theorem maskHit_of_prefix {c : Nat} (hc : 0 < c) (m : Nat) (p : List Nat)
    (h : Fin c → Nat) (i : Fin c) (reverse : Bool)
    (hprefix : ∀ j : Fin c, ∀ hj : j.val < p.length, h j = p[j.val])
    (hlo : ∀ j, 1 ≤ h j) (hhi : ∀ j, h j ≤ m)
    (k d : Nat) (hk : k ∈ Finset.Icc 1 c) (hd : d ≤ 6)
    (hsum : (∑ j ∈ Finset.range k, indexedValue hc h i reverse j) = d) :
    maskHit c m p i.val reverse d = true := by
  have hchoices (j : Nat) (hj : j < c) :
      indexedValue hc h i reverse j ∈ choices m p
        (if reverse then backward c i.val j else forward c i.val j) := by
    let x : Fin c := ⟨if reverse then backward c i.val j else forward c i.val j,
      by cases reverse <;> exact Nat.mod_lt _ hc⟩
    change h x ∈ choices m p x.val
    by_cases hx : x.val < p.length
    · simp [choices, hx, hprefix x hx]
    · simp only [choices, dif_neg hx, List.mem_map]
      have hl := hlo x
      have hh := hhi x
      refine ⟨h x - 1, List.mem_range.mpr (by omega), by omega⟩
  have hflag := reachMask_sound c m p i.val reverse
    (indexedValue hc h i reverse) hchoices k (Finset.mem_Icc.mp hk).2
    (hsum ▸ hd)
  unfold maskHit
  apply List.any_eq_true.mpr
  refine ⟨k - 1, ?_, ?_⟩
  · simp only [List.mem_range]
    have := Finset.mem_Icc.mp hk
    omega
  · have hk1 : k - 1 + 1 = k := by
      have := Finset.mem_Icc.mp hk
      omega
    simpa [hk1, hsum] using hflag

/-- The bit-mask directional score dominates an actual prefix score. -/
private theorem maskDirection_le {c : Nat} (hc : 0 < c) (m : Nat) (p : List Nat)
    (h : Fin c → Nat) (i : Fin c) (reverse : Bool)
    (hprefix : ∀ j : Fin c, ∀ hj : j.val < p.length, h j = p[j.val])
    (hlo : ∀ j, 1 ≤ h j) (hhi : ∀ j, h j ≤ m)
    (sums : (Fin c → Nat) → Fin c → Nat → Nat)
    (hsums : ∀ k ≤ c,
      sums h i k = ∑ j ∈ Finset.range k, indexedValue hc h i reverse j) :
    prefixScore h i sums ≤ maskDirection c m p i.val reverse := by
  classical
  have hit (d : Nat) (hd : d ≤ 6)
      (hh : ∃ k ∈ Finset.Icc 1 c, sums h i k = d) :
      maskHit c m p i.val reverse d = true := by
    obtain ⟨k, hk, heq⟩ := hh
    apply maskHit_of_prefix hc m p h i reverse hprefix hlo hhi k d hk hd
    rw [← hsums k (Finset.mem_Icc.mp hk).2]
    exact heq
  unfold prefixScore maskDirection
  by_cases h3 : ∃ k ∈ Finset.Icc 1 c, sums h i k = 3
  · have hb := hit 3 (by omega) h3
    simp only [Finset.mem_Icc] at h3
    simp [h3, hb]
  · by_cases h6 : ∃ k ∈ Finset.Icc 1 c, sums h i k = 6
    · have hb := hit 6 (by omega) h6
      simp only [Finset.mem_Icc] at h3 h6
      by_cases hbound3 : maskHit c m p i.val reverse 3 = true <;>
        simp [h3, h6, hb, hbound3]
    · simp only [Finset.mem_Icc] at h3 h6
      simp [h3, h6]

/-- Each literal outer or inner slot is below its seven-bit upper score. -/
private theorem maskSlot_le {c : Nat} (hc : 0 < c) (m : Nat) (p : List Nat)
    (h : Fin c → Nat)
    (hprefix : ∀ j : Fin c, ∀ hj : j.val < p.length, h j = p[j.val])
    (hlo : ∀ j, 1 ≤ h j) (hhi : ∀ j, h j ≤ m)
    (v : Bool × Fin c) :
    (if v.1 then B h v.2 else A h v.2) ≤
      (if v.1 then maskInner c m p v.2.val else outer c m p v.2.val) := by
  rcases v with ⟨b, i⟩
  have hphi (j : Fin c) : phi (h j) ≤ phiUpper m p j.val := by
    have hj : h j ∈ choices m p j.val := by
      by_cases hj : j.val < p.length
      · simp [choices, hj, hprefix j hj]
      · simp only [choices, dif_neg hj, List.mem_map]
        have hl := hlo j
        have hh := hhi j
        refine ⟨h j - 1, List.mem_range.mpr (by omega), by omega⟩
    unfold phi phiUpper
    by_cases h1 : h j = 1
    · simp [h1, h1 ▸ hj]
    · by_cases h2 : h j = 2
      · have h2mem : 2 ∈ choices m p j.val := by simpa [h2] using hj
        simp [phi, phiUpper, h1, h2, h2mem]
        split_ifs <;> omega
      · simp [h1, h2]
  cases b
  · have hback := hphi (cyclicIndex i (c - 1))
    have hfront := hphi i
    have hidx : backward c i.val 0 = (cyclicIndex i (c - 1)).val := by
      unfold backward cyclicIndex
      congr 1
      omega
    simpa [A, outer, hidx] using add_le_add hback hfront
  · have hf := maskDirection_le hc m p h i false hprefix hlo hhi
      positivePrefix (fun k _ => rfl)
    have hindexed (k : Nat) (hk : k ≤ c) :
        negativePrefix h i k =
          ∑ j ∈ Finset.range k, indexedValue hc h i true j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjc : j + 1 ≤ c := by
        have := Finset.mem_range.mp hj
        omega
      have heq : backward c i.val j = (cyclicIndex i (c - (j + 1))).val := by
        unfold backward cyclicIndex
        congr 1
        omega
      unfold indexedValue
      exact congrArg h (Fin.ext heq.symm)
    have hb := maskDirection_le hc m p h i true hprefix hlo hhi
      negativePrefix hindexed
    simpa [B, maskInner] using add_le_add hf hb

/-- Every ten-slot subset is bounded by a fixed bit-mask dual price. -/
theorem T_le_maskPrice {c : Nat} (hc : 0 < c) (m : Nat) (p : List Nat)
    (h : Fin c → Nat)
    (hprefix : ∀ j : Fin c, ∀ hj : j.val < p.length, h j = p[j.val])
    (hlo : ∀ j, 1 ≤ h j) (hhi : ∀ j, h j ≤ m)
    (price : Nat) : T h ≤ priceBound (maskSlots c m p) price := by
  classical
  let f : Bool × Fin c → Nat := fun v =>
    if v.1 then maskInner c m p v.2.val else outer c m p v.2.val
  unfold T
  apply Finset.sup_le
  intro Y hY
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hY
  have hslot := Finset.sum_le_sum (s := Y)
    (fun v (_ : v ∈ Y) => maskSlot_le hc m p h hprefix hlo hhi v)
  have hprice : ∀ v : Bool × Fin c, f v ≤ price + (f v - price) := by
    intro v
    omega
  have hsum := Finset.sum_le_sum (s := Y) (fun v (_ : v ∈ Y) => hprice v)
  have hexcess := Finset.sum_le_sum_of_subset
    (f := fun v : Bool × Fin c => f v - price) hsub
  have hlist : ((maskSlots c m p).map fun s => s - price).sum =
      ∑ v : Bool × Fin c, (f v - price) := by
    simp [f, maskSlots, List.map_flatten, List.sum_flatten, List.map_ofFn,
      List.sum_ofFn, Fintype.sum_prod_type_right,
      Finset.sum_add_distrib, add_comm]
  change ((maskSlots c m p).map fun s => s - price).sum =
    ∑ v : Bool × Fin c, (f v - price) at hlist
  unfold priceBound
  rw [hlist]
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  dsimp [f] at hslot hsum hexcess ⊢
  omega

/-- Successful bit-mask search covers every bounded completion of the prefix. -/
theorem maskCheck_sound {c : Nat} (hc : 0 < c) (fuel m : Nat) (p : List Nat)
    (h : Fin c → Nat) (hlen : p.length + fuel = c)
    (hprefix : ∀ j : Fin c, ∀ hj : j.val < p.length, h j = p[j.val])
    (hlo : ∀ j, 1 ≤ h j) (hhi : ∀ j, h j ≤ m)
    (hcheck : maskCheck c fuel m p = true)
    (hsum : 14 ≤ ∑ j : Fin c, h j)
    (hlarge : 4 * c + 6 ≤ T h) :
    ∃ e ∈ exceptionalRoots, e.length = c ∧
      (∀ j : Fin c, ∀ hj : j.val < e.length, h j = e[j.val]) := by
  have hupper (q : List Nat)
      (hq : ∀ j : Fin c, ∀ hj : j.val < q.length, h j = q[j.val]) :
      T h ≤ maskUpper c m q := by
    unfold maskUpper
    apply (le_min_iff).2
    constructor
    · exact T_le_maskPrice hc m q h hq hlo hhi 0
    apply (le_min_iff).2
    constructor
    · exact T_le_maskPrice hc m q h hq hlo hhi 1
    apply (le_min_iff).2
    constructor
    · exact T_le_maskPrice hc m q h hq hlo hhi 2
    apply (le_min_iff).2
    exact ⟨T_le_maskPrice hc m q h hq hlo hhi 3,
      T_le_maskPrice hc m q h hq hlo hhi 4⟩
  induction fuel generalizing p with
  | zero =>
      have hnot : ¬ maskUpper c m p ≤ 4 * c + 5 := by
        intro hub
        have ht := hupper p hprefix
        omega
      have hleaf : p.sum < 14 ∨ p ∈ exceptionalRoots := by
        simpa [maskCheck, hnot] using hcheck
      have hword : p = List.ofFn h := by
        apply List.ext_getElem
        · simpa using hlen
        · intro j hj1 hj2
          have hj : j < c := by omega
          have heq := hprefix ⟨j, hj⟩ (by omega)
          simpa using heq.symm
      have hpSum : p.sum = ∑ j : Fin c, h j := by
        rw [hword, List.sum_ofFn]
      rcases hleaf with hsmall | hex
      · omega
      · exact ⟨p, hex, by omega, hprefix⟩
  | succ fuel ih =>
      have hnot : ¬ maskUpper c m p ≤ 4 * c + 5 := by
        intro hub
        have ht := hupper p hprefix
        omega
      have hall : (List.range m).all
          (fun j => maskCheck c fuel m (p ++ [j + 1])) = true := by
        simpa [maskCheck, hnot] using hcheck
      have hidx : p.length < c := by omega
      let x := h ⟨p.length, hidx⟩
      have hxlo : 1 ≤ x := hlo _
      have hxhi : x ≤ m := hhi _
      have hmember : x - 1 ∈ List.range m := by simp; omega
      have hchild : maskCheck c fuel m (p ++ [x]) = true := by
        have hh := (List.all_eq_true.mp hall) (x - 1) hmember
        simpa [Nat.sub_add_cancel hxlo] using hh
      have hp' : ∀ j : Fin c, ∀ hj : j.val < (p ++ [x]).length,
          h j = (p ++ [x])[j.val] := by
        intro j hj
        by_cases hjold : j.val < p.length
        · simpa [List.getElem_append_left, hjold] using hprefix j hjold
        · have heq : j.val = p.length := by simp at hj; omega
          have hjfin : j = ⟨p.length, hidx⟩ := Fin.ext heq
          have hr : (p ++ [x])[j.val] = x := by simp [heq]
          calc
            h j = x := congrArg h hjfin
            _ = (p ++ [x])[j.val] := hr.symm
      exact ih (p ++ [x]) (by simp; omega) hp' hchild

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapMaskBridge
