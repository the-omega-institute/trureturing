/- GID: D5 / S3 / Combinatorics / Circle / ThreeNegativeMinimumTwoJointLift
   generality: I
   mirror - B: D5 / B / S3 / Combinatorics / Circle / ThreeNegativeMinimumTwoJointLift
   mirror - E: none(waiver:no - escape - mirror - specified)
   anchors: [mathlib / module / Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete physical mask construction and literal ear for minimum gap two. -/
import D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! The minimum - gap - two base of the three - negative joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

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


private structure Mask where
  u : ℤ
  v : ℤ
  w : ℤ

private inductive Negative | alpha | beta | gamma
  deriving DecidableEq
private inductive Order | abg | bag | gba | agb | bga | gab
  deriving DecidableEq
private inductive Ear | p | q | t
  deriving DecidableEq

private def atNegative {α : Type* } (A B G : α) : Negative → α
  | .alpha => A | .beta => B | .gamma => G
private def Order.first : Order → Negative
  | .abg | .agb => .alpha
  | .bag | .bga => .beta
  | .gba | .gab => .gamma
private def Order.middle : Order → Negative
  | .abg | .gba => .beta
  | .bag | .gab => .alpha
  | .agb | .bga => .gamma
private def Order.last : Order → Negative
  | .abg | .bag => .gamma
  | .gba | .bga => .alpha
  | .agb | .gab => .beta

private def oldMass (r s t : ℤ) (m : Mask) : ℤ :=
  (1 + r + r * s) * m.u + (1 + t + t * r) * m.v + (1 + s + s * t) * m.w
private def newMass (r s t : ℤ) (m : Mask) : ℤ :=
  (2 * (1 + r + r * s)) * m.u + (2 * (1 + t + t * r) - 1) * m.v + (2 * (1 + s + s * t) - s - 1) * m.w
private def cap (r s t : ℤ) : ℤ := r * s * (t / 2) - 1
private def oldHeight (r s t : ℤ) : Negative → ℤ :=
  atNegative (cap r s t - (r + 1) * (t / 2))
    (cap r s t - (t + 1) * (s / 2)) (cap r s t - (s + 1) * (r / 2))
private def newHeight (r s t : ℤ) (n : Negative) : ℤ :=
  2 * oldHeight r s t n + atNegative 1 (s / 2 + 1) ((s + 1) * (r / 2) + 1) n

private structure Plan where
  row : ℕ
  order : Order
  ear : Ear
  p : Mask
  t : Mask

private def makePlan (row : ℕ) (o : Order) (e : Ear) (p t : Mask) : Plan :=
  ⟨row,o,e,p,t⟩
private def chooseEar (r s t : ℤ) (row : ℕ) (p z : Mask) : Plan :=
  makePlan row .abg
    (if newHeight r s t .gamma - newMass r s t z ≤ s * t + s / 2 then .q else .t) p z

/-- Each branch fixes physical masks; the middle block is their physical complement. -/
private def constructor (r s t : ℤ) : Plan :=
  if r = 4 ∧ s = 4 ∧ t = 4 then makePlan 0 .abg .p ⟨1,0,0⟩ ⟨0,0,1⟩
  else if r = 4 ∧ s = 4 then
    if t = 8 then makePlan 1 .bag .q ⟨1,1,0⟩ ⟨2,0,0⟩
    else makePlan 2 .bag .q ⟨t / 16,1,0⟩ ⟨t / 8,0,1⟩
  else if r = 4 ∧ t = 4 then makePlan 3 .gba .q ⟨0,s / 8,1⟩ ⟨1,s / 8 - 1,0⟩
  else if s = 4 ∧ t = 4 then
    if r = 8 then makePlan 4 .bag .q ⟨1,0,1⟩ ⟨0,0,2⟩
    else if r = 16 then makePlan 5 .agb .q ⟨1,0,1⟩ ⟨0,1,2⟩
    else makePlan 6 .agb .q ⟨1,0,r / 16⟩ ⟨0,1,5 * r / 32⟩
  else if r = 4 then
    if s ≤ t then chooseEar r s t 7 ⟨(t / s) * (s / 2 - 1),0,0⟩
      ⟨0,(s * t - 3 * s - 4) / (5 * t + 1),1⟩
    else if s = 2 * t then
      if t = 8 then makePlan 9 .abg .q ⟨0,6,0⟩ ⟨1,0,1⟩
      else chooseEar r s t 8 ⟨t / 2 - 1,1,0⟩ ⟨0,t / 4,1⟩
    else if s = 4 * t then chooseEar r s t 10 ⟨t / 2 - 3,9,0⟩
      ⟨0,if t = 8 then 2 else if t = 16 then 6 else t / 2,1⟩
    else makePlan 11 .bga .q ⟨t / 8,0,1⟩
      ⟨0,(oldHeight r s t .alpha) / (1 + t + t * r),0⟩
  else if s = 4 then
    if 2 * r ≤ t then makePlan 12 .bag .q ⟨cap r s t / (1 + r + r * s),0,0⟩ ⟨0,0,r / 2 - 1⟩
    else if t = r then makePlan 13 .bag .p ⟨0,0,r / 2 - 1⟩
      ⟨oldHeight r s t .gamma / (1 + r + r * s),0,0⟩
    else if r = 2 * t then
      if t = 8 then makePlan 15 .agb .q ⟨2,0,1⟩ ⟨1,0,4⟩
      else makePlan 14 .agb .t ⟨3 * t / 8,0,0⟩ ⟨1,0,t - 5⟩
    else makePlan 16 .agb .t ⟨3 * t / 8,0,0⟩
      ⟨0,0,(4 * r * t - 5 * r - 4 * t - 4) / (8 * t + 5)⟩
  else if r = 8 ∧ s = 8 then makePlan 17 .abg .t ⟨1,1,0⟩ ⟨0,0,2⟩
  else if (r = 8 ∧ s = 16) ∨ (r = 16 ∧ s = 8) then
    makePlan 18 .bga .q ⟨1,1,1⟩ ⟨0,2,2⟩
  else if r = 16 ∧ s = 16 then makePlan 19 .bga .q ⟨1,3,0⟩ ⟨0,4,2⟩
  else if s = 8 then makePlan 20 .gab .q ⟨1,0,5 * r / 32⟩ ⟨0,3,r / 16⟩
  else if s = 16 then
    let yz := if r = 32 then (5,0) else if r = 64 then (10,1) else (19 * r / 128,r / 32)
    makePlan 21 .gab .q ⟨1,0,yz.1⟩ ⟨0,7,yz.2⟩
  else if r = 8 then makePlan 22 .bga .q ⟨1,3 * s / 16,0⟩
    ⟨0,if s = 32 then 0 else s / 64,3⟩
  else if r = 16 then makePlan 23 .bga .q ⟨1,7 * s / 32,0⟩
    ⟨0,if s = 32 then 0 else s / 64,6⟩
  else if r = 32 then
    if s = 32 ∨ s = 64 then makePlan 24 .agb .q ⟨1,s / 4 - 1,0⟩ ⟨0,0,12⟩
    else makePlan 25 .bga .q ⟨1,29 * s / 128,0⟩ ⟨0,s / 64,12⟩
  else if r = s ∨ 2 * r = s then makePlan 26 .agb .q ⟨1,s / 4 - 1,0⟩ ⟨0,0,25 * r / 64⟩
  else if r = 2 * s then makePlan 27 .gab .q ⟨1,0,3 * r / 16⟩ ⟨0,s / 2 - 1,0⟩
  else if 4 * s ≤ r then makePlan 28 .agb .q
    ⟨1,s / 4 - 1,-(-(2 * r + 2 - 9 * s / 4) / (9 * s + 1))⟩ ⟨0,0,25 * r / 64⟩
  else makePlan 29 .bga .q ⟨1,(r * s - r - 2) / (4 * r + 5),0⟩ ⟨0,0,25 * r / 64⟩

private def Bounded (r s t : ℤ) (m : Mask) : Prop :=
  0 ≤ m.u ∧ m.u < t / 2 ∧ 0 ≤ m.v ∧ m.v < s / 2 ∧ 0 ≤ m.w ∧ m.w < r / 2
private def Separate (p z : Mask) : Prop :=
  Disjoint p.u.toNat.bitIndices.toFinset z.u.toNat.bitIndices.toFinset ∧ Disjoint p.v.toNat.bitIndices.toFinset z.v.toNat.bitIndices.toFinset ∧ Disjoint p.w.toNat.bitIndices.toFinset z.w.toNat.bitIndices.toFinset

private def Seams (r s t : ℤ) (p : Plan) : Prop :=
  let H := oldHeight r s t
  let K := newHeight r s t
  let x := oldMass r s t p.p
  let z := oldMass r s t p.t
  let xn := newMass r s t p.p + if p.ear = .p then 1 + r + r * s else 0
  let zn := newMass r s t p.t + if p.ear = .t then 1 + r + r * s else 0
  H p.order.first ≤ x ∧ x ≤ cap r s t ∧ z ≤ H p.order.last ∧ H p.order.middle + H p.order.last - z ≤ cap r s t ∧ K p.order.first ≤ xn ∧ xn ≤ 2 * cap r s t + 1 ∧ zn ≤ K p.order.last ∧ K p.order.middle + K p.order.last - zn ≤ 2 * cap r s t + 1

private def Certificate (r s t : ℤ) (p : Plan) : Prop :=
  Bounded r s t p.p ∧ Bounded r s t p.t ∧ Separate p.p p.t ∧ Seams r s t p

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
    rw [Finset.coe_toList]; rfl
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
    n o.first ≠ n o.middle ∧ n o.first ≠ n o.last ∧ n o.middle ≠ n o.last ∧ n o.first < a + b + c ∧ n o.middle < a + b + c ∧ n o.last < a + b + c := by
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
  have hHA : 2 * H .alpha = N - B := by
    change 2 * (C - (r + 1) * (t / 2)) = N - B
    rw [hN]
    dsimp [B]
    have he : t = 2 * (t / 2) := by omega
    nlinarith only [congrArg (fun z : ℤ => (r + 1) * z) he]
  have hHB : 2 * H .beta = N - L := by
    change 2 * (C - (t + 1) * (s / 2)) = N - L
    rw [hN]
    dsimp [L]
    have he : s = 2 * (s / 2) := by omega
    nlinarith only [congrArg (fun z : ℤ => (t + 1) * z) he]
  have hHG : 2 * H .gamma = N - u := by
    change 2 * (C - (s + 1) * (r / 2)) = N - u
    rw [hN]
    dsimp [u]
    have he : r = 2 * (r / 2) := by omega
    nlinarith only [congrArg (fun z : ℤ => (s + 1) * z) he]
  have hKA : 2 * K .alpha = (2 * N + 1) - (2 * B - 1) := by
    change 2 * (2 * H .alpha + 1) = _
    omega
  have hKB : 2 * K .beta = (2 * N + 1) - (2 * L - s - 1) := by
    change 2 * (2 * H .beta + (s / 2 + 1)) = _
    have he : s = 2 * (s / 2) := by omega
    omega
  have hKG : 2 * K .gamma = (2 * N + 1) - u := by
    change 2 * (2 * H .gamma + ((s + 1) * (r / 2) + 1)) = _
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
      · change 0 ≤ 2 * H .alpha + 1
        have := (hH .alpha).1
        omega
      · change 0 ≤ 2 * H .beta + (s / 2 + 1)
        have := (hH .beta).1
        omega
      · change 0 ≤ 2 * H .gamma + ((s + 1) * (r / 2) + 1)
        have := (hH .gamma).1
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
  change Bounded r s t plan.p at hpB
  change Bounded r s t plan.t at htB
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
    (⟨plan.p.u.toNat,convertU _ hpB.1 hpB.2.1⟩,
     ⟨plan.p.v.toNat,convertV _ hpB.2.2.1 hpB.2.2.2.1⟩,
     ⟨plan.p.w.toNat,convertW _ hpB.2.2.2.2.1 hpB.2.2.2.2.2⟩)
  let tm : PhysicalMask a b c :=
    (⟨plan.t.u.toNat,convertU _ htB.1 htB.2.1⟩,
     ⟨plan.t.v.toNat,convertV _ htB.2.2.1 htB.2.2.2.1⟩,
     ⟨plan.t.w.toNat,convertW _ htB.2.2.2.2.1 htB.2.2.2.2.2⟩)
  let PS := support a b c pm
  let TS := support a b c tm
  let QS := Finset.range k \ (PS∪TS∪{n plan.order.first,n plan.order.last,n plan.order.middle})
  let P := PS.toList
  let Q := QS.toList
  let T := TS.toList
  let word := P ++ n plan.order.first :: Q ++ n plan.order.middle :: T ++ [n plan.order.last]
  have hgood (m : PhysicalMask a b c) (i : ℕ) (hi : i ∈ support a b c m) :
      i < k ∧ i ≠ n plan.order.first ∧ i ≠ n plan.order.middle ∧ i ≠ n plan.order.last := by
    have h := support_good a b c ha hb hc m i hi
    cases plan.order <;> simp only [n,Order.first,Order.middle,Order.last,atNegative,k] <;> omega
  have hperm : word.Perm (List.range k) := assemble k _ _ _ PS TS
    (hgood pm) (hgood tm) (support_disjoint a b c pm tm hsep.1 hsep.2.1 hsep.2.2)
    (order_labels a b c ha hb hc plan.order)
  have hQpos (i : ℕ) (hi : i ∈ Q) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hq := Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)
    have hnot : i∉{n plan.order.first,n plan.order.last,n plan.order.middle} :=
      fun hh => hq.2 (Finset.mem_union_right _ hh)
    have hn : i ≠ c - 1 ∧ i ≠ c + b - 1 ∧ i ≠ k - 1 := by
      cases he : plan.order <;> simp only [he,n,Order.first,Order.middle,Order.last,atNegative,
        Finset.mem_insert,Finset.mem_singleton,not_or] at hnot <;> omega
    exact hpositive i (Finset.mem_range.mp hq.1) hn.1 hn.2.1 hn.2.2
  have hPpos (i : ℕ) (hi : i ∈ P) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := support_good a b c ha hb hc pm i (Finset.mem_toList.mp hi)
    exact hpositive i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hTpos (i : ℕ) (hi : i ∈ T) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := support_good a b c ha hb hc tm i (Finset.mem_toList.mp hi)
    exact hpositive i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have sums (m : Mask) (mB : Bounded r s t m) (fm : PhysicalMask a b c)
      (he : fm.1.val = m.u.toNat ∧ fm.2.1.val = m.v.toNat ∧ fm.2.2.val = m.w.toNat) :
      ((support a b c fm).toList.map f).sum = oldMass r s t m ∧ ((support a b c fm).toList.map g).sum = newMass r s t m := by
    have ho := support_sum a b c fm f u B L
      (fun i hi => (hU i hi).1) (fun i hi => (hV i hi).1) (fun i hi => (hW i hi).1)
    have hn := support_sum a b c fm g (2 * u) (2 * B - 1) (2 * L - s - 1)
      (fun i hi => (hU i hi).2) (fun i hi => (hV i hi).2) (fun i hi => (hW i hi).2)
    simp only [he.1,he.2.1,he.2.2,Int.toNat_of_nonneg mB.1,
      Int.toNat_of_nonneg mB.2.2.1,Int.toNat_of_nonneg mB.2.2.2.2.1] at ho hn
    exact ⟨by rw [ho]; dsimp [oldMass,u,B,L]; ring,
      by rw [hn]; dsimp [newMass,u,B,L]; ring⟩
  have hPs := sums plan.p hpB pm ⟨rfl,rfl,rfl⟩
  have hTs := sums plan.t htB tm ⟨rfl,rfl,rfl⟩
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
  let PN := if plan.ear = .p then k::P else P
  let QN := if plan.ear = .q then k::Q else Q
  let TN := if plan.ear = .t then k::T else T
  let plus := PN ++ n plan.order.first :: QN ++ n plan.order.middle :: TN ++ [n plan.order.last]
  have hplus : plus.Perm (List.range (k + 1)) := by
    have hp : plus.Perm (word ++ [k]) := by
      cases he : plan.ear <;> simp only [plus,word,PN,QN,TN,he,ite_true,ite_false,
        reduceCtorEq,List.cons_append] <;>
        apply Multiset.coe_eq_coe.mp <;>
        simp only [← Multiset.coe_add,← Multiset.cons_coe, ← Multiset.singleton_add,Multiset.coe_singleton] <;> ac_rfl
    exact hp.trans (by simpa only [List.range_succ] using hperm.append_right [k])
  have hnpos (S : List ℕ) (e : Ear) (hS : ∀ i ∈ S,0 ≤ g i) :
      ∀ i ∈ (if plan.ear = e then k::S else S),0 ≤ g i := by
    split_ifs
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · rw [hfresh]; omega
      · exact hS i hi
    · exact hS
  have hPN : (PN.map g).sum = newMass r s t plan.p + (if plan.ear = .p then u else 0) := by
    dsimp only [PN]; split_ifs <;> simp_all only [List.map_cons,List.sum_cons,hfresh,hPs.2] <;> ring
  have hTN : (TN.map g).sum = newMass r s t plan.t + (if plan.ear = .t then u else 0) := by
    dsimp only [TN]; split_ifs <;> simp_all only [List.map_cons,List.sum_cons,hfresh,hTs.2] <;> ring
  have hnew : InStrip g N 0 plus :=
    ThreeNegativeEqualOuterJointLift.schedule_from_tail g (List.range (k + 1)) PN QN TN _ _ _ _ _ _ N
      hplus (hgneg _) (hgneg _) (hgneg _) (hK _).1 (hK _).1 (hK _)
      (hnpos P .p (fun i hi => (hPpos i hi).2))
      (hnpos Q .q (fun i hi => (hQpos i hi).2))
      (hnpos T .t (fun i hi => (hTpos i hi).2))
      (by rw [hPN]; change K plan.order.first ≤ _ ∧ _ ≤ N; rw [hN]; exact ⟨hseams.2.2.2.2.1,hseams.2.2.2.2.2.1⟩)
      (by rw [hTN]; rw [hN]; exact ⟨hseams.2.2.2.2.2.2.1,hseams.2.2.2.2.2.2.2⟩) hzn
  let cut := match plan.ear with
    | .p => 0 | .q => P.length + 1 | .t => P.length + 1 + Q.length + 1
  have hcut : cut ≤ k := by
    have hl := hperm.length_eq
    simp only [word,List.length_append,List.length_cons,List.length_singleton,List.length_range] at hl
    cases he : plan.ear <;> simp only [cut,he] <;> omega
  have hear : earWord k (word.map (ThreeNegativeEqualOuterJointLift.label k (by dsimp [k]; omega))) cut =
      plus.map (ThreeNegativeEqualOuterJointLift.label (k + 1) (by dsimp [k]; omega)) := by
    cases he : plan.ear
    · simpa only [cut,he,plus,PN,QN,TN,word,ite_true,ite_false,reduceCtorEq,List.nil_append,List.cons_append,List.append_assoc] using
        ThreeNegativeEqualOuterJointLift.marked_word k 0 (by dsimp [k]; omega) [] word rfl hperm
    · let pre := P ++ [n plan.order.first]
      let post := Q ++ n plan.order.middle::T ++ [n plan.order.last]
      have hw : pre ++ post = word := by simp [pre,post,word,List.append_assoc]
      simpa only [cut,he,plus,PN,QN,TN,ite_true,ite_false,reduceCtorEq,pre,post,word,
        List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        ThreeNegativeEqualOuterJointLift.marked_word k (P.length + 1) (by dsimp [k]; omega)
          pre post (by simp [pre]) (by rw [hw]; exact hperm)
    · let pre := P ++ n plan.order.first::Q ++ [n plan.order.middle]
      let post := T ++ [n plan.order.last]
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

private theorem disjoint_scaled_bits (d x y : ℕ)
    (h : Disjoint x.bitIndices.toFinset y.bitIndices.toFinset) :
    Disjoint (2 ^ d * x).bitIndices.toFinset (2 ^ d * y).bitIndices.toFinset := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [Nat.bitIndices_two_pow_mul,List.mem_toFinset,List.mem_map] at hi hj
  obtain ⟨j,hjmem,hji⟩ := hi
  obtain ⟨l,hl,hli⟩ := hj
  have he : j = l := by omega
  subst l
  exact Finset.disjoint_left.mp h (by simpa using hjmem) (by simpa using hl)

private theorem disjoint_low_bits (d x y : ℕ) (hx : x < 2 ^ d) :
    Disjoint x.bitIndices.toFinset (2 ^ d * y).bitIndices.toFinset := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hb : x.testBit i = true := Nat.mem_bitIndices.mp (List.mem_toFinset.mp hi)
  simp only [Nat.bitIndices_two_pow_mul,List.mem_toFinset,List.mem_map] at hj
  obtain ⟨j,_,hji⟩ := hj
  have hi0 : d ≤ i := by omega
  have hxi : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi0)
  rw [Nat.testBit_eq_false_of_lt hxi] at hb
  contradiction

private theorem axes_zero : Certificate 4 4 4 (constructor 4 4 4) := by
  norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
    cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
    Nat.bitIndices_two_mul,Nat.bitIndices_one]

private theorem axes_one : Certificate 4 4 8 (constructor 4 4 8) := by
  norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
    cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
    Nat.bitIndices_two_mul,Nat.bitIndices_one]

private theorem axes_four : Certificate 8 4 4 (constructor 8 4 4) := by
  norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
    cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
    Nat.bitIndices_two_mul,Nat.bitIndices_one]

private theorem axes_five : Certificate 16 4 4 (constructor 16 4 4) := by
  norm_num [Certificate,constructor,makePlan,Bounded,Separate,Seams,oldMass,newMass,
    cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,atNegative,
    Nat.bitIndices_two_mul,Nat.bitIndices_one]

private theorem axes_two (d : ℕ) :
    Certificate 4 4 (16 * (2 : ℤ) ^ d) (constructor 4 4 (16 * (2 : ℤ) ^ d)) := by
  let q : ℤ := 2 ^ d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (Nat.one_le_two_pow)
  have h4 : 16 * q ≠ 4 := by omega
  have h8 : 16 * q ≠ 8 := by omega
  have hd16 : 16 * q / 16 = q := by omega
  have hd8 : 16 * q / 8 = 2 * q := by omega
  have hc : constructor 4 4 (16 * q) = makePlan 2 .bag .q ⟨q,1,0⟩ ⟨2 * q,0,1⟩ := by
    simp [constructor,h4,h8,hd16,hd8]
  change Certificate 4 4 (16 * q) (constructor 4 4 (16 * q))
  rw [hc]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Separate,makePlan]
    have hbits : Disjoint q.toNat.bitIndices.toFinset (2 * q).toNat.bitIndices.toFinset := by
      have hdis : Disjoint (1 : ℕ).bitIndices.toFinset (2 : ℕ).bitIndices.toFinset := by decide
      have hqnat : q.toNat = 2 ^ d := by
        dsimp [q]; rw [Int.toNat_pow_of_nonneg (by norm_num)]; rfl
      rw [Int.toNat_mul (by norm_num) (by omega), hqnat]
      change Disjoint (2 ^ d).bitIndices.toFinset (2 * 2 ^ d).bitIndices.toFinset
      simpa only [mul_one, Nat.mul_comm] using disjoint_scaled_bits d 1 2 hdis
    exact ⟨hbits,by simp,by simp⟩
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    omega

private theorem axes_three (d : ℕ) :
    Certificate 4 (8 * (2 : ℤ) ^ d) 4 (constructor 4 (8 * (2 : ℤ) ^ d) 4) := by
  let q : ℤ := 2 ^ d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 8 * q ≠ 4 := by omega
  have hd8 : 8 * q / 8 = q := by omega
  have hc : constructor 4 (8 * q) 4 = makePlan 3 .gba .q ⟨0,q,1⟩ ⟨1,q - 1,0⟩ := by
    simp [constructor,h4,hd8]
  change Certificate 4 (8 * q) 4 (constructor 4 (8 * q) 4)
  rw [hc]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,?_,by simp⟩
    have hh : (q - 1).toNat < 2 ^ d := by
      have he : ((q - 1).toNat : ℤ) = q - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast (show ((q - 1).toNat : ℤ) < (2 : ℤ) ^ d by dsimp [q] at he; omega)
    have hqnat : q.toNat = 2 ^ d := by
      dsimp [q]; rw [Int.toNat_pow_of_nonneg (by norm_num)]; rfl
    rw [hqnat]
    simpa only [mul_one] using (disjoint_low_bits d (q - 1).toNat 1 hh).symm
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    omega

private theorem axes_six (d : ℕ) :
    Certificate (32 * (2 : ℤ) ^ d) 4 4 (constructor (32 * (2 : ℤ) ^ d) 4 4) := by
  let q : ℤ := 2 ^ d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 32 * q ≠ 4 := by omega
  have h8 : 32 * q ≠ 8 := by omega
  have h16 : 32 * q ≠ 16 := by omega
  have hd16 : 32 * q / 16 = 2 * q := by omega
  have hd32 : 5 * (32 * q) / 32 = 5 * q := by omega
  have hc : constructor (32 * q) 4 4 = makePlan 6 .agb .q ⟨1,0,2 * q⟩ ⟨0,1,5 * q⟩ := by
    simp [constructor,h4,h8,h16,hd16,hd32]
  change Certificate (32 * q) 4 4 (constructor (32 * q) 4 4)
  rw [hc]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Separate,makePlan]
    have hdis : Disjoint (2 : ℕ).bitIndices.toFinset (5 : ℕ).bitIndices.toFinset := by decide
    refine ⟨by simp,by simp,?_⟩
    have hqnat : q.toNat = 2 ^ d := by
      dsimp [q]; rw [Int.toNat_pow_of_nonneg (by norm_num)]; rfl
    rw [Int.toNat_mul (by norm_num) (by omega), Int.toNat_mul (by norm_num) (by omega), hqnat]
    change Disjoint (2 * 2 ^ d).bitIndices.toFinset (5 * 2 ^ d).bitIndices.toFinset
    simpa only [Nat.mul_comm] using disjoint_scaled_bits d 2 5 hdis
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    omega

private def exceptionalTriples : List (ℤ × ℤ × ℤ) :=
  [(4,16,8),(4,32,8),(4,64,16),(16,4,8),(8,8,4),
      (8,16,4),(16,8,4),(16,16,4),(32,16,4),(64,16,4),(8,32,4),
      (16,32,4),(32,32,4),(32,64,4),(32,4,8),(8,4,8)

private theorem finite_rows (r s t : ℤ)
    (h : (r,s,t) ∈ exceptionalTriples) :
    Certificate r s t (constructor r s t) := by
  simp [exceptionalTriples,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals
    rcases h with ⟨rfl,rfl,rfl⟩
    norm_num [Certificate,constructor,makePlan,chooseEar,Bounded,Separate,Seams,
      oldMass,newMass,cap,oldHeight,newHeight,Order.first,Order.middle,Order.last,
      atNegative,Nat.bitIndices_two_mul,Nat.bitIndices_one] <;> decide

private theorem a_two_twice (d : ℕ) :
    Certificate 4 (32 * (2 : ℤ)^d) (16 * (2 : ℤ)^d)
      (constructor 4 (32 * (2 : ℤ)^d) (16 * (2 : ℤ)^d)) := by
  let q : ℤ := 2^d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hs : 32*q≠4 := by omega
  have ht : 16*q≠4 := by omega
  have ht8 : 16*q≠8 := by omega
  have hst : ¬32*q≤16*q := by omega
  have hrel : 32*q=2*(16*q) := by ring
  have ht2 : 16*q/2=8*q := by omega
  have ht4 : 16*q/4=4*q := by omega
  have hs2 : 32*q/2=16*q := by omega
  have hcon : constructor 4 (32*q) (16*q)=
      chooseEar 4 (32*q) (16*q) 8 ⟨8*q-1,1,0⟩ ⟨0,4*q,1⟩ := by
    simp [constructor,hs,ht,hst,ht8,ht2,ht4]
    split_ifs <;> simp_all <;> omega
  change Certificate 4 (32*q) (16*q) (constructor 4 (32*q) (16*q))
  rw [hcon]
  have hsep : Separate (⟨8*q-1,1,0⟩ : Mask) ⟨0,4*q,1⟩ := by
    refine ⟨by simp [Separate],?_,by simp⟩
    have hp : (4*q).toNat=2^(d+2) := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num [pow_add]
      ring
    change Disjoint (1:ℕ).bitIndices.toFinset (4*q).toNat.bitIndices.toFinset
    rw [hp]
    simpa only [mul_one] using disjoint_low_bits (d+2) 1 1 (by
      have h := Nat.one_le_two_pow (n:=d)
      simp only [pow_add] at *
      omega)
  unfold chooseEar
  split_ifs with he
  all_goals
    refine ⟨?_,?_,hsep,?_⟩
    · dsimp [Bounded,makePlan]; rw [ht2,hs2]; omega
    · dsimp [Bounded,makePlan]; rw [ht2,hs2]; omega
    · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
        Order.first,Order.middle,Order.last,atNegative]
      simp only [ht2,hs2]
      dsimp [newHeight,oldHeight,oldMass,newMass,cap,atNegative] at he
      simp only [ht2,hs2] at he
      norm_num at *
      constructor <;> try omega
      all_goals repeat' constructor
      all_goals nlinarith [sq_nonneg (q-1)]

private theorem int_scaled_bits (d x y : ℕ)
    (h : Disjoint x.bitIndices.toFinset y.bitIndices.toFinset) :
    Disjoint ((x:ℤ)*2^d).toNat.bitIndices.toFinset
      ((y:ℤ)*2^d).toNat.bitIndices.toFinset := by
  rw [Int.toNat_mul (by positivity) (by positivity),
    Int.toNat_mul (by positivity) (by positivity),
    Int.toNat_pow_of_nonneg (by norm_num)]
  norm_cast
  simpa only [Nat.mul_comm] using disjoint_scaled_bits d x y h

private theorem c_two_small_s_eight (d : ℕ) :
    Certificate (32*(2:ℤ)^d) 8 4 (constructor (32*(2:ℤ)^d) 8 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 32*q≠4 := by omega
  have h8 : 32*q≠8 := by omega
  have h16 : 32*q≠16 := by omega
  have hd16 : 32*q/16=2*q := by omega
  have hd32 : 5*(32*q)/32=5*q := by omega
  have hr2 : 32*q/2=16*q := by omega
  have hcon : constructor (32*q) 8 4=makePlan 20 .gab .q ⟨1,0,5*q⟩ ⟨0,3,2*q⟩ := by
    simp [constructor,h4,h8,h16,hd16,hd32]
  change Certificate (32*q) 8 4 (constructor (32*q) 8 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · refine ⟨by simp [Separate,makePlan],by simp,?_⟩
    exact int_scaled_bits d 5 2 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hr2]
    omega

private theorem c_two_small_s_sixteen (d : ℕ) :
    Certificate (128*(2:ℤ)^d) 16 4 (constructor (128*(2:ℤ)^d) 16 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 128*q≠4 := by omega
  have h8 : 128*q≠8 := by omega
  have h16 : 128*q≠16 := by omega
  have h32 : 128*q≠32 := by omega
  have h64 : 128*q≠64 := by omega
  have hd128 : 19*(128*q)/128=19*q := by omega
  have hd32 : 128*q/32=4*q := by omega
  have hr2 : 128*q/2=64*q := by omega
  have hcon : constructor (128*q) 16 4=makePlan 21 .gab .q ⟨1,0,19*q⟩ ⟨0,7,4*q⟩ := by
    simp [constructor,h4,h8,h16,h32,h64,hd128,hd32]
  change Certificate (128*q) 16 4 (constructor (128*q) 16 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · refine ⟨by simp [Separate,makePlan],by simp,?_⟩
    exact int_scaled_bits d 19 4 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hr2]
    omega

private theorem c_two_small_r_eight (d : ℕ) :
    Certificate 8 (64*(2:ℤ)^d) 4 (constructor 8 (64*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 64*q≠4 := by omega
  have h8 : 64*q≠8 := by omega
  have h16 : 64*q≠16 := by omega
  have h32 : 64*q≠32 := by omega
  have hd16 : 3*(64*q)/16=12*q := by omega
  have hd64 : 64*q/64=q := by omega
  have hs2 : 64*q/2=32*q := by omega
  have hcon : constructor 8 (64*q) 4=makePlan 22 .bga .q ⟨1,12*q,0⟩ ⟨0,q,3⟩ := by
    simp [constructor,h4,h8,h16,h32,hd16,hd64]
  change Certificate 8 (64*q) 4 (constructor 8 (64*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · refine ⟨by simp [Separate,makePlan],?_,by simp⟩
    simpa only [one_mul] using int_scaled_bits d 12 1 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hs2]
    omega

private theorem c_two_small_r_sixteen (d : ℕ) :
    Certificate 16 (64*(2:ℤ)^d) 4 (constructor 16 (64*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 64*q≠4 := by omega
  have h8 : 64*q≠8 := by omega
  have h16 : 64*q≠16 := by omega
  have h32 : 64*q≠32 := by omega
  have hd32 : 7*(64*q)/32=14*q := by omega
  have hd64 : 64*q/64=q := by omega
  have hs2 : 64*q/2=32*q := by omega
  have hcon : constructor 16 (64*q) 4=makePlan 23 .bga .q ⟨1,14*q,0⟩ ⟨0,q,6⟩ := by
    simp [constructor,h4,h8,h16,h32,hd32,hd64]
  change Certificate 16 (64*q) 4 (constructor 16 (64*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · refine ⟨by simp [Separate,makePlan],?_,by simp⟩
    simpa only [one_mul] using int_scaled_bits d 14 1 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hs2]
    omega

private theorem c_two_small_r_thirtytwo (d : ℕ) :
    Certificate 32 (128*(2:ℤ)^d) 4 (constructor 32 (128*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 128*q≠4 := by omega
  have h8 : 128*q≠8 := by omega
  have h16 : 128*q≠16 := by omega
  have h32 : 128*q≠32 := by omega
  have h64 : 128*q≠64 := by omega
  have hd128 : 29*(128*q)/128=29*q := by omega
  have hd64 : 128*q/64=2*q := by omega
  have hs2 : 128*q/2=64*q := by omega
  have hcon : constructor 32 (128*q) 4=makePlan 25 .bga .q ⟨1,29*q,0⟩ ⟨0,2*q,12⟩ := by
    simp [constructor,h4,h8,h16,h32,h64,hd128,hd64]
  change Certificate 32 (128*q) 4 (constructor 32 (128*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · refine ⟨by simp [Separate,makePlan],?_,by simp⟩
    exact int_scaled_bits d 29 2 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hs2]
    omega

private theorem a_two_four_times (d : ℕ) :
    Certificate 4 (128*(2:ℤ)^d) (32*(2:ℤ)^d)
      (constructor 4 (128*(2:ℤ)^d) (32*(2:ℤ)^d)) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hs4 : 128*q≠4 := by omega
  have ht4 : 32*q≠4 := by omega
  have ht8 : 32*q≠8 := by omega
  have ht16 : 32*q≠16 := by omega
  have hst : ¬128*q≤32*q := by omega
  have htwo : 128*q≠2*(32*q) := by omega
  have hfour : 128*q=4*(32*q) := by ring
  have hth : 32*q/2=16*q := by omega
  have hsh : 128*q/2=64*q := by omega
  have hcon : constructor 4 (128*q) (32*q)=
      chooseEar 4 (128*q) (32*q) 10 ⟨16*q-3,9,0⟩ ⟨0,16*q,1⟩ := by
    simp [constructor,hs4,ht4,ht8,ht16,hst,htwo,hth]
    split_ifs <;> simp_all <;> omega
  change Certificate 4 (128*q) (32*q) (constructor 4 (128*q) (32*q))
  rw [hcon]
  have hsep : Separate (⟨16*q-3,9,0⟩ : Mask) ⟨0,16*q,1⟩ := by
    refine ⟨by simp [Separate],?_,by simp⟩
    have hp : (16*q).toNat=2^(d+4) := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num [pow_add]
      ring
    change Disjoint (9:ℕ).bitIndices.toFinset (16*q).toNat.bitIndices.toFinset
    rw [hp]
    simpa only [mul_one] using disjoint_low_bits (d+4) 9 1 (by
      have h := Nat.one_le_two_pow (n:=d)
      simp only [pow_add] at *
      omega)
  unfold chooseEar
  split_ifs with he
  all_goals
    refine ⟨?_,?_,hsep,?_⟩
    · dsimp [Bounded,makePlan]; rw [hth,hsh]; omega
    · dsimp [Bounded,makePlan]; rw [hth,hsh]; omega
    · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
        Order.first,Order.middle,Order.last,atNegative]
      simp only [hth,hsh]
      dsimp [newHeight,oldHeight,oldMass,newMass,cap,atNegative] at he
      simp only [hth,hsh] at he
      norm_num at *
      repeat' constructor
      all_goals nlinarith [sq_nonneg (q-1)]

private theorem b_two_twice (d : ℕ) :
    Certificate (32*(2:ℤ)^d) 4 (16*(2:ℤ)^d)
      (constructor (32*(2:ℤ)^d) 4 (16*(2:ℤ)^d)) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hr4 : 32*q≠4 := by omega
  have ht4 : 16*q≠4 := by omega
  have ht8 : 16*q≠8 := by omega
  have hlarge : ¬2*(32*q)≤16*q := by omega
  have hdiag : 16*q≠32*q := by omega
  have hrel : 32*q=2*(16*q) := by ring
  have hr2 : 32*q/2=16*q := by omega
  have ht2 : 16*q/2=8*q := by omega
  have hmask : 3*(16*q)/8=6*q := by omega
  have hcon : constructor (32*q) 4 (16*q)=
      makePlan 14 .agb .t ⟨6*q,0,0⟩ ⟨1,0,16*q-5⟩ := by
    simp [constructor,hr4,ht4,ht8,hlarge,hdiag,hmask]
    split_ifs <;> simp_all <;> omega
  change Certificate (32*q) 4 (16*q) (constructor (32*q) 4 (16*q))
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · refine ⟨?_,by simp [Separate,makePlan],by simp⟩
    have hp : (6*q).toNat=2^(d+1)*3 := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num [pow_add]
      ring
    change Disjoint (6*q).toNat.bitIndices.toFinset (1:ℕ).bitIndices.toFinset
    rw [hp]
    exact (disjoint_low_bits (d+1) 1 3 (by
      have h := Nat.one_le_two_pow (n:=d)
      simp only [pow_add] at *
      omega)).symm
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,ht2]
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (q-1)]

private theorem constructor_certificate (a b c : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hmin : min a (min b c)=2) :
    Certificate (2^a) (2^b) (2^c) (constructor (2^a) (2^b) (2^c)) := by
  have factor (x m : ℕ) (hm : m≤x) : (2:ℤ)^x=2^m*2^(x-m) := by
    rw [←pow_add]
    congr 1
    omega
  by_cases hab : a=2 ∧ b=2
  · obtain ⟨rfl,rfl⟩ := hab
    by_cases hc2 : c=2
    · subst c; exact axes_zero
    · by_cases hc3 : c=3
      · subst c; exact axes_one
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
        · subst a; exact axes_four
        · by_cases ha4 : a=4
          · subst a; exact axes_five
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
            · exact finite_rows _ _ _ hf
            · by_cases hordered : b≤c
              · fail "row 7: unbounded ordered a=2 floor, capacities, and seam certificate"
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
                · fail "row 11: s>=8t floor(H_alpha/B), capacity, and Q seam certificate"
        · have hwhich : b=2 ∨ c=2 := by omega
          rcases hwhich with hb2|hc2
          · subst b
            by_cases hf : ((2:ℤ)^a,4,(2:ℤ)^c) ∈ exceptionalTriples
            · exact finite_rows _ _ _ hf
            · by_cases hlarge : a<c
              · fail "row 12: floor(C/u), power-of-two remainder, and physical capacity"
              · by_cases hdiag : a=c
                · fail "row 13: diagonal floor(H_gamma/u) and first-ear seams"
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
                  · fail "row 16: r>=4t floor, exceptional remainder bounds, and T-ear seams"
          · subst c
            by_cases hf : ((2:ℤ)^a,(2:ℤ)^b,4) ∈ exceptionalTriples
            · exact finite_rows _ _ _ hf
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
                        · fail "row 26: large alpha-first equal or adjacent powers, exact tail seams"
                        · by_cases htwice : a=b+1
                          · fail "row 27: gamma-first r=2s and exact paired seams"
                          · by_cases hhigh : b+2≤a
                            · fail "row 28: ceiling mask bound m<r/64, disjointness, and paired seams"
                            · fail "row 29: V floor bound, W=25r/64 capacity, and paired seams"

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
