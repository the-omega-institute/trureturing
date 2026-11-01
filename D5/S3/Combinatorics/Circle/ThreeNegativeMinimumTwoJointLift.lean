/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete physical mask construction and literal ear for minimum gap two. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! The minimum - gap - two base of the three - negative joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

open private ThreeBitSource.mask_labels ThreeBitSource.mask_labels_bound
  ThreeBitSource.mask_labels_disjoint ThreeBitSource.mask_labels_sum
  ThreeBitSource.labelled_permutation
  from D5.S3.Combinatorics.Circle.ThreeBitSource
open private ThreeNegativeEqualOuterJointLift.label ThreeNegativeEqualOuterJointLift.lift_order
  ThreeNegativeEqualOuterJointLift.marked_word ThreeNegativeEqualOuterJointLift.schedule_from_tail
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open private Mask Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Ear Ear.p Ear.q Ear.t Plan.p Plan.t Plan.order Plan.ear atNegative Order.first Order.middle Order.last oldMass
  newMass cap oldHeight newHeight Plan constructor Bounded Seams Certificate makePlan chooseEar Separate
  axes_two axes_three axes_six exceptionalTriples a_two_twice
  c_two_small_s_eight c_two_small_s_sixteen c_two_small_r_eight c_two_small_r_sixteen
  c_two_small_r_thirtytwo a_two_four_times b_two_twice c_two_equal c_two_double_s
  c_two_double_r
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private a_two_far c_two_far_s c_two_far_r b_two_diagonal b_two_tall b_two_next b_two_far
  a_two_ordered_small a_two_ordered
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private theorem paired_chains (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let r : ℤ := 2 ^ a
    let s : ℤ := 2 ^ b
    let t : ℤ := 2 ^ c
    let k := a + b + c
    let N := modulus k
    let v := 1 + r + r * s
    let B := 1 + t + t * r
    let L := 1 + s + s * t
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
    let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * v))
    (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧ (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧ (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧ g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧ (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧ g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧ f (c - 1) = -(N - B) / 2 ∧ f (c + b - 1) = -(N - L) / 2 ∧ f (k - 1) = -(N - v) / 2 ∧ g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧ g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧ g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v := by
  dsimp only
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let t : ℤ := 2 ^ c
  let k := a + b + c
  let N := modulus k
  let M := modulus (k + 1)
  let v := 1 + r + r * s
  let B := 1 + t + t * r
  let L := 1 + s + s * t
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
  let F := fun i : ℕ => centered M ((2 : ℤ) ^ i * v)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * (2 * v))
  change (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧ (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧ (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧ g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧ (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧ g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧ f (c - 1) = -(N - B) / 2 ∧ f (c + b - 1) = -(N - L) / 2 ∧ f (k - 1) = -(N - v) / 2 ∧ g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧ g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧ g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v
  obtain ⟨hv, hB, hL, _, hU, hV, hW⟩ :=
    ThreeNegativeEqualOuterSourceBridge.actual_source_chains a b c (by omega) (by omega) hc
  change (1 ≤ v ∧ v < N) at hv
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ e < c, f e = if e + 1 < c then (2 : ℤ) ^ e * v else -(N - B) / 2 at hU
  change ∀ e < b, f (c + e) = if e + 1 < b then (2 : ℤ) ^ e * B else -(N - L) / 2 at hV
  change ∀ e < a, f (c + b + e) = if e + 1 < a then (2 : ℤ) ^ e * L else -(N - v) / 2 at hW
  obtain ⟨_, _, _, _, hU', hV', hW'⟩ :=
    ThreeNegativeEqualOuterSourceBridge.actual_source_chains a b (c + 1) (by omega) (by omega) (by omega)
  have hM : modulus (a + b + (c + 1)) = M := rfl
  have ht : (2 : ℤ) ^ (c + 1) = 2 * t := by dsimp [t]; rw [pow_succ]; ring
  have hB' : 1 + (2 : ℤ) ^ (c + 1) + 2 ^ (c + 1) * 2 ^ a = 2 * B - 1 := by
    rw [ht]; change 1 + 2 * t + 2 * t * r = _; dsimp [B]; ring
  have hL' : 1 + (2 : ℤ) ^ b + 2 ^ b * 2 ^ (c + 1) = 2 * L - s - 1 := by
    rw [ht]; change 1 + s + s * (2 * t) = _; dsimp [L]; ring
  rw [hM, hB'] at hU'
  rw [hM, hB', hL'] at hV'
  rw [hM, hL'] at hW'
  have hshift (i : ℕ) : g i = F (i + 1) := by
    dsimp [g, F]; rw [pow_succ]; congr 1; ring
  have hMN : M = 2 * N + 1 := by dsimp [M, N, modulus]; rw [pow_succ]; ring
  refine ⟨hv, hB, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < c by omega)] using hU i (by omega)
    · rw [hshift]
      have h := hU' (i + 1) (by omega)
      rw [ite_eq_left (by omega), pow_succ] at h
      change F (i + 1) = _ at h
      rw [h]; ring
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < b by omega)] using hV i (by omega)
    · rw [hshift, show c + i + 1 = (c + 1) + i by omega]
      exact (hV' i (by omega)).trans (ite_eq_left (by omega))
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < a by omega)] using hW i (by omega)
    · rw [hshift, show c + b + i + 1 = (c + 1) + b + i by omega]
      exact (hW' i (by omega)).trans (ite_eq_left (by omega))
  · simpa only [ite_eq_right (by omega : ¬ c - 1 + 1 < c)] using hU (c - 1) (by omega)
  · simpa only [show c + (b - 1) = c + b - 1 by omega,
      ite_eq_right (by omega : ¬ b - 1 + 1 < b)] using hV (b - 1) (by omega)
  · simpa only [show c + b + (a - 1) = k - 1 by dsimp [k]; omega,
      ite_eq_right (by omega : ¬ a - 1 + 1 < a)] using hW (a - 1) (by omega)
  · rw [hshift, show c - 1 + 1 = c by omega]
    simpa only [ite_eq_right (by omega : ¬ c + 1 < c + 1), F, hMN] using hU' c (by omega)
  · rw [hshift, show c + b - 1 + 1 = (c + 1) + (b - 1) by omega]
    simpa only [ite_eq_right (by omega : ¬ b - 1 + 1 < b), F, hMN] using hV' (b - 1) (by omega)
  · rw [hshift, show k - 1 + 1 = (c + 1) + b + (a - 1) by dsimp [k]; omega]
    simpa only [ite_eq_right (by omega : ¬ a - 1 + 1 < a), F, hMN] using hW' (a - 1) (by omega)
  · have hvNat : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = v := by
      push_cast; dsimp [v, r, s]; rw [pow_add]
    have hp : g k = centered M v := by
      rw [hshift]
      change centered M ((2 : ℤ) ^ (k + 1) * v) = _
      rw [← hvNat]
      exact centered_full_period (k + 1) _
    rw [hp]
    dsimp [centered]
    have hhalf : M / 2 = N := by omega
    rw [hhalf, Int.emod_eq_of_lt (by omega) (by omega)]
    omega


private abbrev PhysicalMask (a b c : ℕ) :=
  Fin (2 ^ (c - 1)) × Fin (2 ^ (b - 1)) × Fin (2 ^ (a - 1))
private def support (a b c : ℕ) (m : PhysicalMask a b c) : Finset ℕ :=
  ThreeBitSource.mask_labels (c - 1) 0 m.1 m.1.isLt ∪
  ThreeBitSource.mask_labels (b - 1) c m.2.1 m.2.1.isLt ∪
  ThreeBitSource.mask_labels (a - 1) (c + b) m.2.2 m.2.2.isLt

private theorem support_good (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (m : PhysicalMask a b c) (i : ℕ) (hi : i ∈ support a b c m) :
    i < a + b + c ∧ i ≠ c - 1 ∧ i ≠ c + b - 1 ∧ i ≠ a + b + c - 1 := by
  simp only [support, Finset.mem_union] at hi
  rcases hi with (hi|hi)|hi <;>
    have := ThreeBitSource.mask_labels_bound hi <;> omega

private theorem support_sum (a b c : ℕ) (m : PhysicalMask a b c)
    (f : ℕ → ℤ) (u v w : ℤ)
    (hU : ∀ e < c - 1, f e = (2 : ℤ) ^ e * u)
    (hV : ∀ e < b - 1, f (c + e) = (2 : ℤ) ^ e * v)
    (hW : ∀ e < a - 1, f (c + b + e) = (2 : ℤ) ^ e * w) :
    ((support a b c m).toList.map f).sum = (m.1.val : ℤ) * u + m.2.1.val * v + m.2.2.val * w := by
  classical
  have hUV : Disjoint (ThreeBitSource.mask_labels (c - 1) 0 m.1 m.1.isLt)
      (ThreeBitSource.mask_labels (b - 1) c m.2.1 m.2.1.isLt) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  have hWsep : Disjoint (ThreeBitSource.mask_labels (c - 1) 0 m.1 m.1.isLt ∪
      ThreeBitSource.mask_labels (b - 1) c m.2.1 m.2.1.isLt)
      (ThreeBitSource.mask_labels (a - 1) (c + b) m.2.2 m.2.2.isLt) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have := ThreeBitSource.mask_labels_bound hj
    rcases Finset.mem_union.mp hi with hi|hi <;>
      have := ThreeBitSource.mask_labels_bound hi <;> omega
  have hsum (S : Finset ℕ) : (S.toList.map f).sum = ∑ i ∈ S,f i := by
    change ((S.toList:Multiset ℕ).map f).sum = _
    rw [Finset.coe_toList] <;> rfl
  rw [hsum, support, Finset.sum_union hWsep, Finset.sum_union hUV]
  rw [ThreeBitSource.mask_labels_sum (c - 1) 0 _ _ f u (by simpa using hU),
    ThreeBitSource.mask_labels_sum (b - 1) c _ _ f v hV,
    ThreeBitSource.mask_labels_sum (a - 1) (c + b) _ _ f w hW]

private theorem support_disjoint (a b c : ℕ) (p z : PhysicalMask a b c)
    (hU : Disjoint p.1.val.bitIndices.toFinset z.1.val.bitIndices.toFinset)
    (hV : Disjoint p.2.1.val.bitIndices.toFinset z.2.1.val.bitIndices.toFinset)
    (hW : Disjoint p.2.2.val.bitIndices.toFinset z.2.2.val.bitIndices.toFinset) :
    Disjoint (support a b c p) (support a b c z) := by
  have hu := ThreeBitSource.mask_labels_disjoint (len := c - 1) (off := 0) (hx := p.1.isLt) (hy := z.1.isLt) hU
  have hv := ThreeBitSource.mask_labels_disjoint (len := b - 1) (off := c) (hx := p.2.1.isLt) (hy := z.2.1.isLt) hV
  have hw := ThreeBitSource.mask_labels_disjoint (len := a - 1) (off := c + b) (hx := p.2.2.isLt) (hy := z.2.2.isLt) hW
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [support, Finset.mem_union] at hi hj
  rcases hi with (hi|hi)|hi <;> rcases hj with (hj|hj)|hj
  · exact Finset.disjoint_left.mp hu hi hj
  · have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  · have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  · have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  · exact Finset.disjoint_left.mp hv hi hj
  · have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  · have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  · have := ThreeBitSource.mask_labels_bound hi
    have := ThreeBitSource.mask_labels_bound hj
    omega
  · exact Finset.disjoint_left.mp hw hi hj

private theorem order_labels (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (o : Order) :
    let n := atNegative (c - 1) (c + b - 1) (a + b + c - 1)
    n (Order.first o) ≠ n (Order.middle o) ∧ n (Order.first o) ≠ n (Order.last o) ∧ n (Order.middle o) ≠ n (Order.last o) ∧ n (Order.first o) < a + b + c ∧ n (Order.middle o) < a + b + c ∧ n (Order.last o) < a + b + c := by
  cases o <;> simp only [Order.first, Order.middle, Order.last, atNegative] <;> omega

private theorem assemble (k n1 n2 n3 : ℕ) (P T : Finset ℕ)
    (hP : ∀ i ∈ P, i < k ∧ i ≠ n1 ∧ i ≠ n2 ∧ i ≠ n3)
    (hT : ∀ i ∈ T, i < k ∧ i ≠ n1 ∧ i ≠ n2 ∧ i ≠ n3)
    (hd : Disjoint P T)
    (hn : n1 ≠ n2 ∧ n1 ≠ n3 ∧ n2 ≠ n3 ∧ n1 < k ∧ n2 < k ∧ n3 < k) :
    let Q := Finset.range k \ (P ∪ T ∪ {n1,n3,n2})
    (P.toList ++ n1 :: Q.toList ++ n2 :: T.toList ++ [n3]).Perm (List.range k) := by
  classical
  dsimp only
  have hp := ThreeBitSource.labelled_permutation k n1 n3 n2 P T
    (fun i hi => Finset.mem_range.mpr (hP i hi).1)
    (fun i hi => Finset.mem_range.mpr (hT i hi).1) hd
    ⟨hn.2.1,hn.1,hn.2.2.1.symm⟩ ⟨hn.2.2.2.1,hn.2.2.2.2.2,hn.2.2.2.2.1⟩
    (fun i hi => ⟨(hP i hi).2.1,(hP i hi).2.2.2,(hP i hi).2.2.1⟩)
    (fun i hi => ⟨(hT i hi).2.1,(hT i hi).2.2.2,(hT i hi).2.2.1⟩)
  apply List.Perm.trans _ hp
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add, List.singleton_append, List.cons_append,
    List.nil_append, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.coe_singleton]
  ac_rfl

private theorem block_cut_bounds {α : Type*} (P Q T : List α) (x y z : α) (k : ℕ)
    (hl : (P ++ x :: Q ++ y :: T ++ [z]).length = k) :
    P.length + 1 ≤ k ∧ P.length + 1 + Q.length + 1 ≤ k := by
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

set_option maxHeartbeats 1000000 in
private theorem realize (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (plan : Plan) (cert : Certificate (2 ^ a) (2 ^ b) (2 ^ c) plan) :
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ, j ≤ a + b + c ∧ OriginalOrder (a + b + c) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧ OriginalOrder (a + b + c + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (earWord (a + b + c) sigma j) := by
  classical
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let t : ℤ := 2 ^ c
  let k := a + b + c
  let N := modulus k
  let C := cap r s t
  let u := 1 + r + r * s
  let B := 1 + t + t * r
  let L := 1 + s + s * t
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
  let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * u))
  let H := oldHeight r s t
  let K := newHeight r s t
  let n := atNegative (c - 1) (c + b - 1) (k - 1)
  have halves (x : ℕ) (hx : 2 ≤ x) : (2 : ℤ) ^ x = 2 * (2 : ℤ) ^ (x - 1) := by
    calc
      (2 : ℤ) ^ x = 2 ^ ((x - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (x - 1) := by rw [pow_succ]; ring
  have hR := halves a ha
  have hS := halves b hb
  have hT := halves c hc
  have hr : 4 ≤ r := by simpa [r] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
  have hs : 4 ≤ s := by simpa [s] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
  have ht : 4 ≤ t := by simpa [t] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hc
  change r = 2 * (2 : ℤ) ^ (a - 1) at hR
  change s = 2 * (2 : ℤ) ^ (b - 1) at hS
  change t = 2 * (2 : ℤ) ^ (c - 1) at hT
  have hrhalf : r / 2 = (2 : ℤ) ^ (a - 1) := by omega
  have hshalf : s / 2 = (2 : ℤ) ^ (b - 1) := by omega
  have hthalf : t / 2 = (2 : ℤ) ^ (c - 1) := by omega
  have hN : N = 2 * C + 1 := by
    dsimp [N,modulus,k,C,cap]
    rw [pow_add,pow_add]
    change r * s * t - 1 = 2 * (r * s * (t / 2) - 1) + 1
    have h := congrArg (fun z : ℤ => r * s * z) (show t = 2 * (t / 2) by omega)
    nlinarith only [h]
  have hM : modulus (k + 1) = 2 * N + 1 := by dsimp [N,modulus]; rw [pow_succ]; ring
  have hhalf : modulus k / 2 = C := by change N / 2 = C; omega
  have hnewhalf : modulus (k + 1) / 2 = N := by omega
  have hNpos : 0 < N := by
    have hp : (0 : ℤ) < 2 ^ k := by positivity
    have hp2 : (2 : ℤ) ^ 6 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by dsimp [k]; omega)
    dsimp [N,modulus]; norm_num at hp2; omega
  have hNodd : N%2 = 1 := by omega
  obtain ⟨hu,hB,hL,hU,hV,hW,hfA,hfB,hfG,hgA,hgB,hgG,hfresh⟩ :=
    paired_chains a b c ha hb hc
  change (1 ≤ u ∧ u < N) at hu
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ i < c - 1, f i = (2 : ℤ) ^ i * u ∧ g i = (2 : ℤ) ^ i * (2 * u) at hU
  change ∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧ g (c + i) = (2 : ℤ) ^ i * (2 * B - 1) at hV
  change ∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧ g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1) at hW
  change f (c - 1) = -(N - B) / 2 at hfA
  change f (c + b - 1) = -(N - L) / 2 at hfB
  change f (k - 1) = -(N - u) / 2 at hfG
  change g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 at hgA
  change g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 at hgB
  change g (k - 1) = -((2 * N + 1) - u) / 2 at hgG
  change g k = u at hfresh
  have hHA : 2 * H Negative.alpha = N - B := by
    change 2 * (C - (r + 1) * (t / 2)) = N - B
    rw [hN]
    dsimp [B]
    have he : t = 2 * (t / 2) := by omega
    nlinarith only [congrArg (fun z : ℤ => (r + 1) * z) he]
  have hHB : 2 * H Negative.beta = N - L := by
    change 2 * (C - (t + 1) * (s / 2)) = N - L
    rw [hN]
    dsimp [L]
    have he : s = 2 * (s / 2) := by omega
    nlinarith only [congrArg (fun z : ℤ => (t + 1) * z) he]
  have hHG : 2 * H Negative.gamma = N - u := by
    change 2 * (C - (s + 1) * (r / 2)) = N - u
    rw [hN]
    dsimp [u]
    have he : r = 2 * (r / 2) := by omega
    nlinarith only [congrArg (fun z : ℤ => (s + 1) * z) he]
  have hKA : 2 * K Negative.alpha = (2 * N + 1) - (2 * B - 1) := by
    change 2 * (2 * H Negative.alpha + 1) = _
    omega
  have hKB : 2 * K Negative.beta = (2 * N + 1) - (2 * L - s - 1) := by
    change 2 * (2 * H Negative.beta + (s / 2 + 1)) = _
    have he : s = 2 * (s / 2) := by omega
    omega
  have hKG : 2 * K Negative.gamma = (2 * N + 1) - u := by
    change 2 * (2 * H Negative.gamma + ((s + 1) * (r / 2) + 1)) = _
    have he : 2 * ((s + 1) * (r / 2)) = u - 1 := by
      dsimp [u]
      have he : r = 2 * (r / 2) := by omega
      nlinarith only [congrArg (fun z : ℤ => (s + 1) * z) he]
    omega
  have hfneg (d : Negative) : f (n d) = -H d := by
    cases d <;> simp only [n,atNegative] <;> omega
  have hgneg (d : Negative) : g (n d) = -K d := by
    cases d <;> simp only [n,atNegative] <;> omega
  have hH (d : Negative) : 0 ≤ H d ∧ H d ≤ C := by
    cases d <;> constructor <;> omega
  have hK (d : Negative) : 0 ≤ K d ∧ K d ≤ N := by
    have hh := hH d
    have hbnd := centered_bounds (by omega : 0 < modulus (k + 1))
      (by omega : modulus (k + 1)%2 = 1) ((2 : ℤ) ^ (n d) * (2 * u))
    change -(modulus (k + 1) / 2) ≤ g (n d) ∧ g (n d) ≤ modulus (k + 1) / 2 at hbnd
    rw [hgneg] at hbnd
    have hnonneg : 0 ≤ K d := by
      cases d
      · change 0 ≤ 2 * H Negative.alpha + 1
        have := (hH Negative.alpha).1
        omega
      · change 0 ≤ 2 * H Negative.beta + (s / 2 + 1)
        have := (hH Negative.beta).1
        omega
      · change 0 ≤ 2 * H Negative.gamma + ((s + 1) * (r / 2) + 1)
        have := (hH Negative.gamma).1
        have : 0 ≤ (s + 1) * (r / 2) := mul_nonneg (by omega) (by omega)
        omega
    exact ⟨hnonneg, by omega⟩
  have hpositive (i : ℕ) (hi : i < k) (hnA : i ≠ c - 1) (hnB : i ≠ c + b - 1)
      (hnG : i ≠ k - 1) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hBg : 0 ≤ 2 * B - 1 := by omega
    have hLg : 0 ≤ 2 * L - s - 1 := by dsimp [L]; nlinarith
    by_cases hiU : i < c
    · obtain ⟨hf,hg⟩ := hU i (by omega)
      rw [hf,hg]; constructor <;> positivity
    · by_cases hiV : i < c + b
      · have hie : c + (i - c) = i := by omega
        obtain ⟨hf,hg⟩ := hV (i - c) (by omega)
        rw [hie] at hf hg
        rw [hf,hg]; constructor <;> positivity
      · have hie : c + b + (i - (c + b)) = i := by omega
        obtain ⟨hf,hg⟩ := hW (i - (c + b)) (by dsimp [k] at hi hnG; omega)
        rw [hie] at hf hg
        rw [hf,hg]; constructor <;> positivity
  obtain ⟨hpB,htB,hsep,hseams⟩ := cert
  change Bounded r s t (Plan.p plan) at hpB
  change Bounded r s t (Plan.t plan) at htB
  have convertU (m : ℤ) (hm0 : 0 ≤ m) (hm : m < t / 2) : m.toNat < 2 ^ (c - 1) := by
    have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
    rw [hthalf] at hm
    exact_mod_cast (show (m.toNat : ℤ) < (2 : ℤ) ^ (c - 1) by omega)
  have convertV (m : ℤ) (hm0 : 0 ≤ m) (hm : m < s / 2) : m.toNat < 2 ^ (b - 1) := by
    have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
    rw [hshalf] at hm
    exact_mod_cast (show (m.toNat : ℤ) < (2 : ℤ) ^ (b - 1) by omega)
  have convertW (m : ℤ) (hm0 : 0 ≤ m) (hm : m < r / 2) : m.toNat < 2 ^ (a - 1) := by
    have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
    rw [hrhalf] at hm
    exact_mod_cast (show (m.toNat : ℤ) < (2 : ℤ) ^ (a - 1) by omega)
  let pm : PhysicalMask a b c :=
    (⟨(Mask.u (Plan.p plan)).toNat,convertU _ hpB.1 hpB.2.1⟩,
     ⟨(Mask.v (Plan.p plan)).toNat,convertV _ hpB.2.2.1 hpB.2.2.2.1⟩,
     ⟨(Mask.w (Plan.p plan)).toNat,convertW _ hpB.2.2.2.2.1 hpB.2.2.2.2.2⟩)
  let tm : PhysicalMask a b c :=
    (⟨(Mask.u (Plan.t plan)).toNat,convertU _ htB.1 htB.2.1⟩,
     ⟨(Mask.v (Plan.t plan)).toNat,convertV _ htB.2.2.1 htB.2.2.2.1⟩,
     ⟨(Mask.w (Plan.t plan)).toNat,convertW _ htB.2.2.2.2.1 htB.2.2.2.2.2⟩)
  let PS := support a b c pm
  let TS := support a b c tm
  let QS := Finset.range k \ (PS∪TS∪{n (Order.first (Plan.order plan)),n (Order.last (Plan.order plan)),n (Order.middle (Plan.order plan))})
  let P := PS.toList
  let Q := QS.toList
  let T := TS.toList
  let word := P ++ n (Order.first (Plan.order plan)) :: Q ++ n (Order.middle (Plan.order plan)) :: T ++ [n (Order.last (Plan.order plan))]
  have hgood (m : PhysicalMask a b c) (i : ℕ) (hi : i ∈ support a b c m) :
      i < k ∧ i ≠ n (Order.first (Plan.order plan)) ∧ i ≠ n (Order.middle (Plan.order plan)) ∧ i ≠ n (Order.last (Plan.order plan)) := by
    have h := support_good a b c ha hb hc m i hi
    cases (Plan.order plan) <;> simp only [n,Order.first,Order.middle,Order.last,atNegative,k] <;> omega
  have hperm : word.Perm (List.range k) := assemble k _ _ _ PS TS
    (hgood pm) (hgood tm) (support_disjoint a b c pm tm hsep.1 hsep.2.1 hsep.2.2)
    (order_labels a b c ha hb hc (Plan.order plan))
  have hQpos (i : ℕ) (hi : i ∈ Q) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hq := Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)
    have hnot : i∉{n (Order.first (Plan.order plan)),n (Order.last (Plan.order plan)),n (Order.middle (Plan.order plan))} :=
      fun hh => hq.2 (Finset.mem_union_right _ hh)
    have hn : i ≠ c - 1 ∧ i ≠ c + b - 1 ∧ i ≠ k - 1 := by
      cases he : (Plan.order plan) <;> simp only [he,n,Order.first,Order.middle,Order.last,atNegative,
        Finset.mem_insert,Finset.mem_singleton,not_or] at hnot <;> omega
    exact hpositive i (Finset.mem_range.mp hq.1) hn.1 hn.2.1 hn.2.2
  have hPpos (i : ℕ) (hi : i ∈ P) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := support_good a b c ha hb hc pm i (Finset.mem_toList.mp hi)
    exact hpositive i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hTpos (i : ℕ) (hi : i ∈ T) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := support_good a b c ha hb hc tm i (Finset.mem_toList.mp hi)
    exact hpositive i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have sums (m : Mask) (mB : Bounded r s t m) (fm : PhysicalMask a b c)
      (he : fm.1.val = (Mask.u m).toNat ∧ fm.2.1.val = (Mask.v m).toNat ∧ fm.2.2.val = (Mask.w m).toNat) :
      ((support a b c fm).toList.map f).sum = oldMass r s t m ∧ ((support a b c fm).toList.map g).sum = newMass r s t m := by
    have ho := support_sum a b c fm f u B L
      (fun i hi => (hU i hi).1) (fun i hi => (hV i hi).1) (fun i hi => (hW i hi).1)
    have hn := support_sum a b c fm g (2 * u) (2 * B - 1) (2 * L - s - 1)
      (fun i hi => (hU i hi).2) (fun i hi => (hV i hi).2) (fun i hi => (hW i hi).2)
    simp only [he.1,he.2.1,he.2.2,Int.toNat_of_nonneg mB.1,
      Int.toNat_of_nonneg mB.2.2.1,Int.toNat_of_nonneg mB.2.2.2.2.1] at ho hn
    exact ⟨by rw [ho]; dsimp [oldMass,u,B,L]; ring,
      by rw [hn]; dsimp [newMass,u,B,L]; ring⟩
  have hPs := sums (Plan.p plan) hpB pm ⟨rfl,rfl,rfl⟩
  have hTs := sums (Plan.t plan) htB tm ⟨rfl,rfl,rfl⟩
  change (P.map f).sum = _ ∧ (P.map g).sum = _ at hPs
  change (T.map f).sum = _ ∧ (T.map g).sum = _ at hTs
  have hseed : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = u := by push_cast; dsimp [u,r,s]; rw [pow_add]
  have hz : ((List.range k).map f).sum = 0 := by
    simpa only [hseed] using ThreeNegativeEqualOuterSourceBridge.source_zero k (1 + 2 ^ a + 2 ^ (a + b)) (by dsimp [k]; omega)
  have hzn : ((List.range (k + 1)).map g).sum = 0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,hseed] using
      ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by dsimp [k]; omega)
  dsimp only [Seams] at hseams
  have hold : InStrip f C 0 word :=
    ThreeNegativeEqualOuterJointLift.schedule_from_tail f (List.range k) P Q T _ _ _ _ _ _ C
      hperm (hfneg _) (hfneg _) (hfneg _) (hH _).1 (hH _).1 (hH _)
      (fun i hi => (hPpos i hi).1) (fun i hi => (hQpos i hi).1) (fun i hi => (hTpos i hi).1)
      (by rw [hPs.1]; exact ⟨hseams.1,hseams.2.1⟩)
      (by rw [hTs.1]; exact ⟨hseams.2.2.1,hseams.2.2.2.1⟩) hz
  let PN := if (Plan.ear plan) = Ear.p then k::P else P
  let QN := if (Plan.ear plan) = Ear.q then k::Q else Q
  let TN := if (Plan.ear plan) = Ear.t then k::T else T
  let plus := PN ++ n (Order.first (Plan.order plan)) :: QN ++ n (Order.middle (Plan.order plan)) :: TN ++ [n (Order.last (Plan.order plan))]
  have hplus : plus.Perm (List.range (k + 1)) := by
    have hp : plus.Perm (word ++ [k]) := by
      cases he : (Plan.ear plan) <;> simp only [plus,word,PN,QN,TN,he,ite_true,ite_false,
        reduceCtorEq,List.cons_append] <;>
        apply Multiset.coe_eq_coe.mp <;>
        simp only [← Multiset.coe_add,← Multiset.cons_coe, ← Multiset.singleton_add,Multiset.coe_singleton] <;> ac_rfl
    exact hp.trans (by simpa only [List.range_succ] using hperm.append_right [k])
  have hnpos (S : List ℕ) (e : Ear) (hS : ∀ i ∈ S,0 ≤ g i) :
      ∀ i ∈ (if (Plan.ear plan) = e then k::S else S),0 ≤ g i := by
    split_ifs
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · rw [hfresh]; omega
      · exact hS i hi
    · exact hS
  have hPN : (PN.map g).sum = newMass r s t (Plan.p plan) + (if (Plan.ear plan) = Ear.p then u else 0) := by
    dsimp only [PN]; split_ifs <;> simp_all only [List.map_cons,List.sum_cons,hfresh,hPs.2] <;> ring
  have hTN : (TN.map g).sum = newMass r s t (Plan.t plan) + (if (Plan.ear plan) = Ear.t then u else 0) := by
    dsimp only [TN]; split_ifs <;> simp_all only [List.map_cons,List.sum_cons,hfresh,hTs.2] <;> ring
  have hnew : InStrip g N 0 plus :=
    ThreeNegativeEqualOuterJointLift.schedule_from_tail g (List.range (k + 1)) PN QN TN _ _ _ _ _ _ N
      hplus (hgneg _) (hgneg _) (hgneg _) (hK _).1 (hK _).1 (hK _)
      (hnpos P Ear.p (fun i hi => (hPpos i hi).2))
      (hnpos Q Ear.q (fun i hi => (hQpos i hi).2))
      (hnpos T Ear.t (fun i hi => (hTpos i hi).2))
      (by rw [hPN]; change K (Order.first (Plan.order plan)) ≤ _ ∧ _ ≤ N; rw [hN]; exact ⟨hseams.2.2.2.2.1,hseams.2.2.2.2.2.1⟩)
      (by rw [hTN]; rw [hN]; exact ⟨hseams.2.2.2.2.2.2.1,hseams.2.2.2.2.2.2.2⟩) hzn
  let cut : ℕ := match (Plan.ear plan) with
    | Ear.p => 0 | Ear.q => P.length + 1 | Ear.t => P.length + 1 + Q.length + 1
  have hcut : cut ≤ k := by
    have hl : word.length = k := by
      simpa only [List.length_range] using hperm.length_eq
    have hbnd := block_cut_bounds P Q T _ _ _ k hl
    cases he : (Plan.ear plan)
    · simpa only [cut,he] using (Nat.zero_le k)
    · simpa only [cut,he] using hbnd.1
    · simpa only [cut,he] using hbnd.2
  have hear : earWord k (word.map (ThreeNegativeEqualOuterJointLift.label k (by dsimp [k]; omega))) cut =
      plus.map (ThreeNegativeEqualOuterJointLift.label (k + 1) (by dsimp [k]; omega)) := by
    cases he : (Plan.ear plan)
    · simpa only [cut,he,plus,PN,QN,TN,word,ite_true,ite_false,reduceCtorEq,List.nil_append,List.cons_append,List.append_assoc] using
        ThreeNegativeEqualOuterJointLift.marked_word k 0 (by dsimp [k]; omega) [] word rfl hperm
    · let pre := P ++ [n (Order.first (Plan.order plan))]
      let post := Q ++ n (Order.middle (Plan.order plan))::T ++ [n (Order.last (Plan.order plan))]
      have hw : pre ++ post = word := by simp [pre,post,word,List.append_assoc]
      simpa only [cut,he,plus,PN,QN,TN,ite_true,ite_false,reduceCtorEq,pre,post,word,
        List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        ThreeNegativeEqualOuterJointLift.marked_word k (P.length + 1) (by dsimp [k]; omega)
          pre post (by simp [pre]) (by rw [hw]; exact hperm)
    · let pre := P ++ n (Order.first (Plan.order plan))::Q ++ [n (Order.middle (Plan.order plan))]
      let post := T ++ [n (Order.last (Plan.order plan))]
      have hw : pre ++ post = word := by simp [pre,post,word,List.append_assoc]
      simpa only [cut,he,plus,PN,QN,TN,ite_true,ite_false,reduceCtorEq,pre,post,word,
        List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        ThreeNegativeEqualOuterJointLift.marked_word k (P.length + 1 + Q.length + 1) (by dsimp [k]; omega)
          pre post (by simp [pre]; omega) (by rw [hw]; exact hperm)
  refine ⟨word.map (ThreeNegativeEqualOuterJointLift.label k (by dsimp [k]; omega)),cut,hcut,?_,?_⟩
  · apply ThreeNegativeEqualOuterJointLift.lift_order k _ (by dsimp [k]; omega) word hperm
    · simpa only [hseed,hhalf] using hold
    · simpa only [hseed] using hz
  · rw [hear]
    apply ThreeNegativeEqualOuterJointLift.lift_order (k + 1) _ (by dsimp [k]; omega) plus hplus
    · simpa only [Nat.cast_mul,Nat.cast_ofNat,hseed,hnewhalf] using hnew
    · simpa only [Nat.cast_mul,Nat.cast_ofNat,hseed] using hzn

private theorem constructor_certificate (a b c : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hmin : min a (min b c)=2) :
    Certificate (2^a) (2^b) (2^c) (constructor (2^a) (2^b) (2^c)) := by
  by_cases hexceptional : ((2 : ℤ)^a,(2 : ℤ)^b,(2 : ℤ)^c) ∈ exceptionalTriples
  · generalize hr : (2 : ℤ)^a = r at hexceptional ⊢
    generalize hs : (2 : ℤ)^b = s at hexceptional ⊢
    generalize ht : (2 : ℤ)^c = t at hexceptional ⊢
    simp [exceptionalTriples,Prod.mk.injEq] at hexceptional
    rcases hexceptional with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals
      rcases h with ⟨rfl,rfl,rfl⟩
      norm_num [Certificate,constructor,makePlan,chooseEar,Bounded,Separate,Seams,
        oldMass,newMass,cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,
        atNegative,Nat.bitIndices_two_mul,Nat.bitIndices_one] <;>
        simp [List.disjoint_left,
          show (2:ℕ).bitIndices=[1] by decide,
          show (3:ℕ).bitIndices=[0,1] by decide,
          show (4:ℕ).bitIndices=[2] by decide,
          show (6:ℕ).bitIndices=[1,2] by decide,
          show (9:ℕ).bitIndices=[0,3] by decide,
          show (10:ℕ).bitIndices=[1,3] by decide]
  have factor (x m : ℕ) (hm : m≤x) : (2:ℤ)^x=2^m*2^(x-m) := by
    rw [←pow_add]
    congr 1
    omega
  have lower (x m : ℕ) (hm : m≤x) : (2:ℤ)^m≤2^x := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hm
  have shift (x m n : ℕ) (hm : m≤x) : (2:ℤ)^(x+n)=2^(m+n)*2^(x-m) := by
    rw [←pow_add]; congr 1; omega
  by_cases hab : a=2 ∧ b=2
  · obtain ⟨rfl,rfl⟩ := hab
    by_cases hc2 : c=2
    · subst c
      norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
        cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
        Nat.bitIndices_two_mul,Nat.bitIndices_one]
    · by_cases hc3 : c=3
      · subst c
        norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
          cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
          Nat.bitIndices_two_mul,Nat.bitIndices_one]
      · have hcf : (2:ℤ)^c=16*2^(c-4) := by simpa using factor c 4 (by omega)
        rw [hcf]
        exact axes_two (c-4)
  · by_cases hac : a=2 ∧ c=2
    · obtain ⟨rfl,rfl⟩ := hac
      have hbf : (2:ℤ)^b=8*2^(b-3) := by simpa using factor b 3 (by omega)
      rw [hbf]
      exact axes_three (b-3)
    · by_cases hbc : b=2 ∧ c=2
      · obtain ⟨rfl,rfl⟩ := hbc
        by_cases ha3 : a=3
        · subst a
          norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
            cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
            Nat.bitIndices_two_mul,Nat.bitIndices_one]
        · by_cases ha4 : a=4
          · subst a
            norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
              cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
              Nat.bitIndices_two_mul,Nat.bitIndices_one]
          · have haf : (2:ℤ)^a=32*2^(a-5) := by simpa using factor a 5 (by omega)
            rw [haf]
            exact axes_six (a-5)
      · by_cases ha2 : a=2
        · subst a
          have hb3 : 3≤b := by omega
          have hc3 : 3≤c := by omega
          by_cases htwice : b=c+1 ∧ 4≤c
          · obtain ⟨hbc,hc4⟩ := htwice
            have hcf : (2:ℤ)^c=16*2^(c-4) := by simpa using factor c 4 hc4
            have hbf : (2:ℤ)^b=32*2^(c-4) := by
              rw [hbc,pow_succ,hcf]; ring
            rw [hbf,hcf]
            exact a_two_twice (c-4)
          · by_cases hf : (4,(2:ℤ)^b,(2:ℤ)^c) ∈ exceptionalTriples
            · exact False.elim (hexceptional (by simpa using hf))
            · by_cases hordered : b≤c
              · have hq : 1≤(2:ℤ)^(c-b) := by exact_mod_cast Nat.one_le_two_pow
                by_cases hbthree : b=3
                · subst b
                  have hc4 : 4≤c := by
                    by_contra ht
                    have he : c=3 := by omega
                    subst c; norm_num [exceptionalTriples] at hf
                  have htf : (2:ℤ)^c=8*2^(c-3) := by simpa using factor c 3 (by omega)
                  have hqp : 2≤(2:ℤ)^(c-3) := by simpa using lower (c-3) 1 (by omega)
                  rw [htf]
                  exact a_two_ordered_small _ hqp
                · have hbf : (2:ℤ)^b=2*2^(b-1) := by simpa using factor b 1 (by omega)
                  have htf : (2:ℤ)^c=2*2^(b-1)*2^(c-b) := by rw [factor c b hordered,hbf]
                  have hhp : 8≤(2:ℤ)^(b-1) := by simpa using lower (b-1) 3 (by omega)
                  rw [hbf,htf]
                  exact a_two_ordered _ _ hhp hq
              · by_cases hfour : b=c+2
                · have hc5 : 5≤c := by
                    by_contra hh
                    have hv : c=3 ∨ c=4 := by omega
                    rcases hv with rfl|rfl <;> subst b <;> norm_num [exceptionalTriples] at hf
                  have hcf : (2:ℤ)^c=32*2^(c-5) := by simpa using factor c 5 hc5
                  have hbf : (2:ℤ)^b=128*2^(c-5) := by
                    rw [hfour,pow_add,hcf]; norm_num <;> ring
                  rw [hbf,hcf]
                  exact a_two_four_times (c-5)
                · have hfar : c+3≤b := by
                    by_contra ht
                    have he : b=c+1 := by omega
                    have hcval : c=3 := by omega
                    subst c; subst b; norm_num [exceptionalTriples] at hf
                  have hbf : (2:ℤ)^b=2*2^(b-1) := by simpa using factor b 1 (by omega)
                  have htf : (2:ℤ)^c=8*2^(c-3) := by simpa using factor c 3 (by omega)
                  have hq : 1≤(2:ℤ)^(c-3) := by exact_mod_cast Nat.one_le_two_pow
                  have hh : 32*(2:ℤ)^(c-3)≤2^(b-1) := by
                    have hp := lower (b-1) (c+2) (by omega)
                    have he : (2:ℤ)^(c+2)=32*2^(c-3) := by simpa using shift c 3 2 (by omega)
                    rwa [he] at hp
                  rw [hbf,htf]
                  exact a_two_far _ _ hq hh
        · have hwhich : b=2 ∨ c=2 := by omega
          rcases hwhich with hb2|hc2
          · subst b
            by_cases hf : ((2:ℤ)^a,4,(2:ℤ)^c) ∈ exceptionalTriples
            · exact False.elim (hexceptional (by simpa using hf))
            · by_cases hlarge : a<c
              · by_cases hnext : c=a+1
                · have haf : (2:ℤ)^a=8*2^(a-3) := by simpa using factor a 3 (by omega)
                  have hcf : (2:ℤ)^c=16*2^(a-3) := by rw [hnext,pow_succ,haf]; ring
                  rw [haf,hcf]
                  exact b_two_next (a-3)
                · have haf : (2:ℤ)^a=2*2^(a-1) := by simpa using factor a 1 (by omega)
                  have hcf : (2:ℤ)^c=2*2^(c-1) := by simpa using factor c 1 (by omega)
                  have hh : 4≤(2:ℤ)^(a-1) := by simpa using lower (a-1) 2 (by omega)
                  have hw : 4*(2:ℤ)^(a-1)≤2^(c-1) := by
                    have hp := lower (c-1) (a+1) (by omega)
                    have he : (2:ℤ)^(a+1)=4*2^(a-1) := by simpa using shift a 1 1 (by omega)
                    rwa [he] at hp
                  rw [haf,hcf]
                  exact b_two_tall _ _ hh hw
              · by_cases hdiag : a=c
                · subst c
                  have ha4 : 4≤a := by
                    by_contra ht
                    have he : a=3 := by omega
                    subst a; norm_num [exceptionalTriples] at hf
                  have haf : (2:ℤ)^a=16*2^(a-4) := by simpa using factor a 4 ha4
                  rw [haf]
                  exact b_two_diagonal _ (by exact_mod_cast Nat.one_le_two_pow)
                · by_cases htwice : a=c+1
                  · have hc4 : 4≤c := by
                      by_contra hh
                      have hv : c=3 := by omega
                      subst c; subst a; norm_num [exceptionalTriples] at hf
                    have hcf : (2:ℤ)^c=16*2^(c-4) := by simpa using factor c 4 hc4
                    have haf : (2:ℤ)^a=32*2^(c-4) := by
                      rw [htwice,pow_succ,hcf]; ring
                    rw [haf,hcf]
                    exact b_two_twice (c-4)
                  · have haf : (2:ℤ)^a=2*2^(a-1) := by simpa using factor a 1 (by omega)
                    have hcf : (2:ℤ)^c=8*2^(c-3) := by simpa using factor c 3 (by omega)
                    have hq : 1≤(2:ℤ)^(c-3) := by exact_mod_cast Nat.one_le_two_pow
                    have hh : 16*(2:ℤ)^(c-3)≤2^(a-1) := by
                      have hp := lower (a-1) (c+1) (by omega)
                      have he : (2:ℤ)^(c+1)=16*2^(c-3) := by simpa using shift c 3 1 (by omega)
                      rwa [he] at hp
                    have hex : 2≤(2:ℤ)^(c-3) ∨ 32≤(2:ℤ)^(a-1) := by
                      by_cases hc4 : 4≤c
                      · left; simpa using lower (c-3) 1 (by omega)
                      · have hcval : c=3 := by omega
                        have ha6 : 6≤a := by
                          by_contra ht
                          have he : a=5 := by omega
                          subst a; subst c; norm_num [exceptionalTriples] at hf
                        right; simpa using lower (a-1) 5 (by omega)
                    rw [haf,hcf]
                    exact b_two_far _ _ hq hh hex
          · subst c
            by_cases hf : ((2:ℤ)^a,(2:ℤ)^b,4) ∈ exceptionalTriples
            · exact False.elim (hexceptional (by simpa using hf))
            · by_cases hb3 : b=3
              · subst b
                have ha5 : 5≤a := by
                  by_contra hh
                  have hv : a=3 ∨ a=4 := by omega
                  rcases hv with rfl|rfl <;> norm_num [exceptionalTriples] at hf
                have haf : (2:ℤ)^a=32*2^(a-5) := by simpa using factor a 5 ha5
                rw [haf]
                exact c_two_small_s_eight (a-5)
              · by_cases hb4 : b=4
                · subst b
                  have ha7 : 7≤a := by
                    by_contra hh
                    have hv : a=3 ∨ a=4 ∨ a=5 ∨ a=6 := by omega
                    rcases hv with rfl|rfl|rfl|rfl <;> norm_num [exceptionalTriples] at hf
                  have haf : (2:ℤ)^a=128*2^(a-7) := by simpa using factor a 7 ha7
                  rw [haf]
                  exact c_two_small_s_sixteen (a-7)
                · by_cases ha3 : a=3
                  · subst a
                    have hb6 : 6≤b := by
                      by_contra hh
                      have hv : b=5 := by omega
                      subst b; norm_num [exceptionalTriples] at hf
                    have hbf : (2:ℤ)^b=64*2^(b-6) := by simpa using factor b 6 hb6
                    rw [hbf]
                    exact c_two_small_r_eight (b-6)
                  · by_cases ha4 : a=4
                    · subst a
                      have hb6 : 6≤b := by
                        by_contra hh
                        have hv : b=5 := by omega
                        subst b; norm_num [exceptionalTriples] at hf
                      have hbf : (2:ℤ)^b=64*2^(b-6) := by simpa using factor b 6 hb6
                      rw [hbf]
                      exact c_two_small_r_sixteen (b-6)
                    · by_cases ha5 : a=5
                      · subst a
                        have hb7 : 7≤b := by
                          by_contra hh
                          have hv : b=5 ∨ b=6 := by omega
                          rcases hv with rfl|rfl <;> norm_num [exceptionalTriples] at hf
                        have hbf : (2:ℤ)^b=128*2^(b-7) := by simpa using factor b 7 hb7
                        rw [hbf]
                        exact c_two_small_r_thirtytwo (b-7)
                      · by_cases heq : a=b ∨ a+1=b
                        · have ha6 : 6≤a := by omega
                          have haf : (2:ℤ)^a=64*2^(a-6) := by simpa using factor a 6 ha6
                          rcases heq with heq|heq
                          · subst b
                            rw [haf]
                            exact c_two_equal (a-6)
                          · have hbf : (2:ℤ)^b=128*2^(a-6) := by
                              rw [←heq,pow_succ,haf]; ring
                            rw [haf,hbf]
                            exact c_two_double_s (a-6)
                        · by_cases htwice : a=b+1
                          · have ha6 : 6≤a := by omega
                            have hb5 : 5≤b := by omega
                            have hbf : (2:ℤ)^b=32*2^(b-5) := by simpa using factor b 5 hb5
                            have haf : (2:ℤ)^a=64*2^(b-5) := by rw [htwice,pow_succ,hbf]; ring
                            rw [haf,hbf]
                            exact c_two_double_r (b-5)
                          · by_cases hhigh : b+2≤a
                            · have ha7 : 7≤a := by omega
                              have haf : (2:ℤ)^a=64*2^(a-6) := by simpa using factor a 6 (by omega)
                              have hbf : (2:ℤ)^b=4*2^(b-2) := by simpa using factor b 2 (by omega)
                              have hq : 2≤(2:ℤ)^(a-6) := by simpa using lower (a-6) 1 (by omega)
                              have hh : 8≤(2:ℤ)^(b-2) := by simpa using lower (b-2) 3 (by omega)
                              have hr : (2:ℤ)^(b-2)≤4*2^(a-6) := by
                                have hp := lower (a-2) b (by omega)
                                have he : (2:ℤ)^(a-2)=16*2^(a-6) := by
                                  simpa only [show a-2-4=a-6 by omega,show (2:ℤ)^4=16 by norm_num] using factor (a-2) 4 (by omega)
                                rw [he,hbf] at hp; omega
                              rw [haf,hbf]
                              exact c_two_far_r (a-6) _ hq hh hr
                            · have haf : (2:ℤ)^a=64*2^(a-6) := by simpa using factor a 6 (by omega)
                              have hbf : (2:ℤ)^b=4*2^(b-2) := by simpa using factor b 2 (by omega)
                              have hq : 1≤(2:ℤ)^(a-6) := by exact_mod_cast Nat.one_le_two_pow
                              have hh : 64*(2:ℤ)^(a-6)≤2^(b-2) := by
                                have hp := lower (b-2) a (by omega)
                                rwa [haf] at hp
                              rw [haf,hbf]
                              exact c_two_far_s _ _ hq hh

/-- One complete physical list, with its literal identity-embedded ear, for all minimum-two gaps. -/
theorem actualSource_three_negative_minimum_two_joint_lift (a b c : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hmin : min a (min b c)=2) :
    ∃ sigma : List (Fin (a+b+c)), ∃ j : ℕ, j≤a+b+c ∧
      OriginalOrder (a+b+c) (1+2^a+2^(a+b)) sigma ∧
      OriginalOrder (a+b+c+1) (2*(1+2^a+2^(a+b))) (earWord (a+b+c) sigma j) := by
  exact realize a b c ha hb hc (constructor (2^a) (2^b) (2^c))
    (constructor_certificate a b c ha hb hc hmin)

#print axioms actualSource_three_negative_minimum_two_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
