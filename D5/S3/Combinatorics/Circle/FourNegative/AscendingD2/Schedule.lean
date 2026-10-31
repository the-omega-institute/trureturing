/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Schedule
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-physical-schedule)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Three shifted library masks and four physical negative labels control every prefix. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterFirstEarJointLift

/-! Explicit masks, their uniform strip margins, and every physical prefix. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
private abbrev Coeff := ℤ × ℤ × ℤ
private def oldMass (R T Z : ℤ) (m : Coeff) : ℤ :=
  m.1 * (4 * R * T + 4 * R + 5) + m.2.1 * ((4 * R + 5) * Z + 1) + m.2.2 * (5 * T * Z + T + 1)
private def newMass (R T Z : ℤ) (m : Coeff) : ℤ :=
  m.1 * (8 * R * T + 8 * R + 9) + m.2.1 * ((8 * R + 9) * Z + 1) + m.2.2 * (9 * T * Z + T + 1)
private def margins (R T Z : ℤ) (p q r : Coeff) : Prop :=
  let A := 1 + R + R * T + R * T * Z
  let C := 2 * R * T * Z - 1
  let N := 4 * R * T * Z - 1
  let x := -3 * R * T * Z + R * (T + 1) + 2
  let w := -4 * R * T * Z + 5 * T * Z + T + 2
  let v := -4 * R * T * Z + (4 * R + 5) * Z + 2
  let u := -4 * R * T * Z + 4 * R * T + 4 * R + 6
  let xn := -7 * R * T * Z + R * (T + 1) + 2
  let wn := -8 * R * T * Z + 9 * T * Z + T + 2
  let vn := -8 * R * T * Z + (8 * R + 9) * Z + 2
  let un := -8 * R * T * Z + 8 * R * T + 8 * R + 10
  let P := 2 * oldMass R T Z p
  let Q := 2 * oldMass R T Z q
  let S := 2 * oldMass R T Z r
  let Pn := 2 * A + 2 * newMass R T Z p
  let Qn := 2 * newMass R T Z q
  let Sn := 2 * newMass R T Z r
  0 ≤ A ∧ A ≤ N ∧ P ≤ 2 * C ∧ 0 ≤ P + x ∧ P + x + Q ≤ 2 * C ∧ 0 ≤ P + x + Q + w ∧
    P + x + Q + w + S ≤ 2 * C ∧ 0 ≤ P + x + Q + w + S + v ∧ 0 ≤ -u ∧ -u ≤ 2 * C ∧
    Pn ≤ 2 * N ∧ 0 ≤ Pn + xn ∧ Pn + xn + Qn ≤ 2 * N ∧ 0 ≤ Pn + xn + Qn + wn ∧
    Pn + xn + Qn + wn + Sn ≤ 2 * N ∧ 0 ≤ Pn + xn + Qn + wn + Sn + vn ∧ 0 ≤ -un ∧ -un ≤ 2 * N

set_option maxHeartbeats 2000000 in
private theorem large_margins (r s t : ℤ) (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    margins (16 * r) (32 * r * s) (64 * r * s * t)
      (0, 0, 5 * r) (0, (8 * r + 1) * s, 3 * r - 1) ((16 * r * s + 1) * t, (8 * r - 1) * s - 1, 0) := by
  obtain ⟨r0, hr0, rfl⟩ : ∃ r0 : ℤ, 0 ≤ r0 ∧ r = r0 + 1 := ⟨r - 1, by omega, by omega⟩
  obtain ⟨s0, hs0, rfl⟩ : ∃ s0 : ℤ, 0 ≤ s0 ∧ s = s0 + 1 := ⟨s - 1, by omega, by omega⟩
  obtain ⟨t0, ht0, rfl⟩ : ∃ t0 : ℤ, 0 ≤ t0 ∧ t = t0 + 1 := ⟨t - 1, by omega, by omega⟩
  dsimp [margins, oldMass, newMass]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

set_option maxHeartbeats 1500000 in
private theorem small_margins (r u v : ℤ) (hr : r = 1 ∨ r = 2) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    margins (4 * r) (16 * u) (32 * u * v)
      (0, u, r) (0, 4 * u, r - 1) ((8 * u + 1) * v, 3 * u - 1, 0) := by
  obtain ⟨u0, hu0, rfl⟩ : ∃ u0 : ℤ, 0 ≤ u0 ∧ u = u0 + 1 := ⟨u - 1, by omega, by omega⟩
  obtain ⟨v0, hv0, rfl⟩ : ∃ v0 : ℤ, 0 ≤ v0 ∧ v = v0 + 1 := ⟨v - 1, by omega, by omega⟩
  rcases hr with rfl|rfl <;> dsimp [margins, oldMass, newMass]
  all_goals repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

set_option maxHeartbeats 1000000 in
private theorem tail_margins (z : ℤ) (hz : 1 ≤ z) :
    margins 4 8 (128 * z) (8 * z, 0, 1) (z, 2, 0) (32 * z, 1, 0) := by
  obtain ⟨z0, hz0, rfl⟩ : ∃ z0 : ℤ, 0 ≤ z0 ∧ z = z0 + 1 := ⟨z - 1, by omega, by omega⟩
  dsimp [margins, oldMass, newMass]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private Table Table.u Table.un Table.v Table.vn Table.w Table.wn Table.x Table.xn
  Table.nu Table.nun Table.nv Table.nvn Table.nw Table.nwn Table.nx Table.nxn
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
open private PhysicalMask support support_good support_sum support_disjoint
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource

private abbrev Mask := PhysicalMask
private def shiftedSupport (a b c : ℕ) (m : Mask a b c) : Finset ℕ :=
  (support a b c m).image (fun i => 2 + i)

private theorem shifted_good (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (m : Mask a b c) (i : ℕ) (hi : i ∈ shiftedSupport a b c m) :
    i < a + b + c + 2 ∧ i ≠ a + b + c + 1 ∧ i ≠ c + b + 1 ∧ i ≠ c + 1 ∧ i ≠ 1 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have h := support_good a b c ha hb hc m j hj
  omega

private theorem shifted_sum (a b c : ℕ) (m : Mask a b c) (f : ℕ → ℤ)
    (V W X : ℤ)
    (hv : ∀ i < c - 1, f (2 + i) = (2 : ℤ) ^ i * V)
    (hw : ∀ i < b - 1, f (c + 2 + i) = (2 : ℤ) ^ i * W)
    (hx : ∀ i < a - 1, f (c + b + 2 + i) = (2 : ℤ) ^ i * X) :
    ((shiftedSupport a b c m).toList.map f).sum =
      (m.1.val : ℤ) * V + m.2.1.val * W + m.2.2.val * X := by
  have hs := support_sum a b c m (fun i => f (2 + i)) V W X hv
    (by intro i hi; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw i hi)
    (by intro i hi; simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx i hi)
  have sum_toList (S : Finset ℕ) (v : ℕ → ℤ) : (S.toList.map v).sum = ∑ i ∈ S, v i := by
    change ((S.toList : Multiset ℕ).map v).sum = _
    rw [Finset.coe_toList]; rfl
  rw [sum_toList, shiftedSupport, Finset.sum_image (by intro i hi j hj he; exact Nat.add_left_cancel he)]
  simpa only [sum_toList] using hs

private theorem shifted_disjoint (a b c : ℕ) (p q : Mask a b c)
    (hv : Disjoint p.1.val.bitIndices.toFinset q.1.val.bitIndices.toFinset)
    (hw : Disjoint p.2.1.val.bitIndices.toFinset q.2.1.val.bitIndices.toFinset)
    (hx : Disjoint p.2.2.val.bitIndices.toFinset q.2.2.val.bitIndices.toFinset) :
    Disjoint (shiftedSupport a b c p) (shiftedSupport a b c q) := by
  have hd := support_disjoint a b c p q hv hw hx
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, hjp, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hj
  have : l = j := by omega
  subst l
  exact Finset.disjoint_left.mp hd hjp hl

private theorem table_positive (a b c : ℕ) (R T Z : ℤ) (f g : ℕ → ℤ)
    (hR : 0 < R) (hT : 0 < T) (hZ : 0 < Z) (tab : Table a b c R T Z f g)
    (i : ℕ) (hi : i < a + b + c + 2 ∧ i ≠ a + b + c + 1 ∧ i ≠ c + b + 1 ∧ i ≠ c + 1 ∧ i ≠ 1) :
    0 ≤ f i ∧ 0 ≤ g i := by
  by_cases h0 : i = 0
  · subst i; rw [(Table.u tab), (Table.un tab)]; constructor <;> positivity
  by_cases hv : i < c + 1
  · have he : i = 2 + (i - 2) := by omega
    rw [he, (Table.v tab) _ (by omega), (Table.vn tab) _ (by omega)]
    constructor <;> positivity
  by_cases hw : i < c + b + 1
  · have he : i = c + 2 + (i - (c + 2)) := by omega
    rw [he, (Table.w tab) _ (by omega), (Table.wn tab) _ (by omega)]
    constructor <;> positivity
  · have he : i = c + b + 2 + (i - (c + b + 2)) := by omega
    rw [he, (Table.x tab) _ (by omega), (Table.xn tab) _ (by omega)]
    constructor <;> positivity

private theorem four_perm (k nx nw nv nu : ℕ) (P Q R : Finset ℕ)
    (hp : ∀ i ∈ P, i < k ∧ i ≠ nx ∧ i ≠ nw ∧ i ≠ nv ∧ i ≠ nu)
    (hq : ∀ i ∈ Q, i < k ∧ i ≠ nx ∧ i ≠ nw ∧ i ≠ nv ∧ i ≠ nu)
    (hr : ∀ i ∈ R, i < k ∧ i ≠ nx ∧ i ≠ nw ∧ i ≠ nv ∧ i ≠ nu)
    (hpq : Disjoint P Q) (hpr : Disjoint P R) (hqr : Disjoint Q R)
    (hn : ([nx, nw, nv, nu] : List ℕ).Nodup)
    (hb : ∀ i ∈ ([nx, nw, nv, nu] : List ℕ), i < k) :
    let G := Finset.range k \ (P ∪ Q ∪ R ∪ {nx, nw, nv, nu})
    (P.toList ++ nx :: Q.toList ++ nw :: R.toList ++ nv :: G.toList ++ [nu]).Perm
      (List.range k) := by
  classical
  let E : Finset ℕ := ⟨([nx, nw, nv, nu] : List ℕ), hn⟩
  have hmem (i : ℕ) : i ∈ E ↔ i ∈ ([nx, nw, nv, nu] : List ℕ) := Iff.rfl
  have he : E = {nx, nw, nv, nu} := by ext i; rw [hmem]; simp
  have hsubE : E ⊆ Finset.range k := by intro i hi; exact Finset.mem_range.mpr (hb i ((hmem i).mp hi))
  have hPE : Disjoint P E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hp i hi
    rw [he] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    tauto
  have hQE : Disjoint Q E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hq i hi
    rw [he] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    tauto
  have hRE : Disjoint R E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hr i hi
    rw [he] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    tauto
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ E)
  have hPQ : Disjoint (P.disjUnion Q hpq) R := by
    simpa only [Finset.disjUnion_eq_union] using Finset.disjoint_union_left.mpr ⟨hpr, hqr⟩
  have hG : Disjoint ((P.disjUnion Q hpq).disjUnion R hPQ) G := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hd := (Finset.mem_sdiff.mp hj).2
    simp only [Finset.mem_disjUnion] at hi
    apply hd
    simp only [Finset.mem_union]
    tauto
  have hE : Disjoint (((P.disjUnion Q hpq).disjUnion R hPQ).disjUnion G hG) E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_disjUnion] at hi
    rcases hi with ((hi|hi)|hi)|hi
    · exact Finset.disjoint_left.mp hPE hi hj
    · exact Finset.disjoint_left.mp hQE hi hj
    · exact Finset.disjoint_left.mp hRE hi hj
    · exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_right _ hj)
  let U := (((P.disjUnion Q hpq).disjUnion R hPQ).disjUnion G hG).disjUnion E hE
  have hU : U = Finset.range k := by
    ext i
    have hPi : i ∈ P → i ∈ Finset.range k := fun hi => Finset.mem_range.mpr (hp i hi).1
    have hQi : i ∈ Q → i ∈ Finset.range k := fun hi => Finset.mem_range.mpr (hq i hi).1
    have hRi : i ∈ R → i ∈ Finset.range k := fun hi => Finset.mem_range.mpr (hr i hi).1
    have hEi : i ∈ E → i ∈ Finset.range k := fun hi => hsubE hi
    simp only [U, G, Finset.mem_disjUnion, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hGeq : G = Finset.range k \ (P ∪ Q ∪ R ∪ {nx, nw, nv, nu}) := by dsimp [G]; rw [he]
  rw [←hGeq]
  apply Multiset.coe_eq_coe.mp
  have hs : ((P.toList ++ nx :: Q.toList ++ nw :: R.toList ++ nv :: G.toList ++ [nu] : List ℕ) : Multiset ℕ) = U.val := by
    change (P.toList : Multiset ℕ) + ({nx} + (Q.toList : Multiset ℕ)) + ({nw} + (R.toList : Multiset ℕ)) + ({nv} + (G.toList : Multiset ℕ)) + {nu} =
      P.val + Q.val + R.val + G.val + ({nx} + {nw} + {nv} + {nu})
    simp only [Finset.coe_toList]
    ac_rfl
  rw [hs, hU]
  rfl

/-- Four positive blocks ending at four specified jumps; all natural takes are included. -/
private theorem four_strip (f : ℕ → ℤ) (P Q R G : List ℕ) (nx nw nv nu : ℕ)
    (C h : ℤ)
    (hp : ∀ i ∈ P, 0 ≤ f i) (hq : ∀ i ∈ Q, 0 ≤ f i)
    (hr : ∀ i ∈ R, 0 ≤ f i) (hg : ∀ i ∈ G, 0 ≤ f i)
    (hh : 0 ≤ h)
    (h1 : h + (P.map f).sum ≤ C ∧ 0 ≤ h + (P.map f).sum + f nx)
    (h2 : h + (P.map f).sum + f nx + (Q.map f).sum ≤ C ∧
      0 ≤ h + (P.map f).sum + f nx + (Q.map f).sum + f nw)
    (h3 : h + (P.map f).sum + f nx + (Q.map f).sum + f nw + (R.map f).sum ≤ C ∧
      0 ≤ h + (P.map f).sum + f nx + (Q.map f).sum + f nw + (R.map f).sum + f nv)
    (h4 : 0 ≤ -f nu ∧ -f nu ≤ C)
    (ht : h + ((P ++ nx :: Q ++ nw :: R ++ nv :: G ++ [nu]).map f).sum = 0) :
    InStrip f C h (P ++ nx :: Q ++ nw :: R ++ nv :: G ++ [nu]) := by
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, add_zero] at ht
  have endG : h + (P.map f).sum + f nx + (Q.map f).sum + f nw + (R.map f).sum + f nv + (G.map f).sum = -f nu := by omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply inStrip_append (l := P) (r := nx :: (Q ++ nw :: (R ++ nv :: (G ++ [nu]))))
    (positive_block_strip hp hh h1.1)
  change 0 ≤ h + (P.map f).sum ∧ h + (P.map f).sum ≤ C ∧ _
  refine ⟨by have := inStrip_prefix (positive_block_strip hp hh h1.1) P.length; simpa using this.1, h1.1, ?_⟩
  apply inStrip_append (l := Q) (r := nw :: (R ++ nv :: (G ++ [nu])))
    (positive_block_strip hq h1.2 h2.1)
  change 0 ≤ h + (P.map f).sum + f nx + (Q.map f).sum ∧ _ ∧ _
  refine ⟨?_, h2.1, ?_⟩
  · have := inStrip_prefix (positive_block_strip hq h1.2 h2.1) Q.length
    simpa only [List.take_length, add_assoc] using this.1
  apply inStrip_append (l := R) (r := nv :: (G ++ [nu]))
    (positive_block_strip hr h2.2 h3.1)
  change 0 ≤ h + (P.map f).sum + f nx + (Q.map f).sum + f nw + (R.map f).sum ∧ _ ∧ _
  refine ⟨?_, h3.1, ?_⟩
  · have := inStrip_prefix (positive_block_strip hr h2.2 h3.1) R.length
    simpa only [List.take_length, add_assoc] using this.1
  apply inStrip_append (l := G) (r := [nu])
    (positive_block_strip hg h3.2 (by omega))
  simp only [InStrip]
  exact ⟨by omega, by omega, by omega, by omega⟩

open private complementary_bits high_bit_disjoint from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterFirstEarJointLift

private def coeff (a b c : ℕ) (m : Mask a b c) : Coeff :=
  (m.1.val, m.2.1.val, m.2.2.val)
private def intMask (a b c : ℕ) (v w x : ℤ)
    (hv : 0 ≤ v ∧ v < (2 : ℤ) ^ (c - 1)) (hw : 0 ≤ w ∧ w < (2 : ℤ) ^ (b - 1))
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ (a - 1)) : Mask a b c :=
  (⟨v.toNat, by exact_mod_cast (show (v.toNat : ℤ) < (2 : ℤ) ^ (c - 1) by simpa only [Int.toNat_of_nonneg hv.1] using hv.2)⟩,
   ⟨w.toNat, by exact_mod_cast (show (w.toNat : ℤ) < (2 : ℤ) ^ (b - 1) by simpa only [Int.toNat_of_nonneg hw.1] using hw.2)⟩,
   ⟨x.toNat, by exact_mod_cast (show (x.toNat : ℤ) < (2 : ℤ) ^ (a - 1) by simpa only [Int.toNat_of_nonneg hx.1] using hx.2)⟩)

private theorem coeff_intMask (a b c : ℕ) (v w x : ℤ)
    (hv : 0 ≤ v ∧ v < (2 : ℤ) ^ (c - 1)) (hw : 0 ≤ w ∧ w < (2 : ℤ) ^ (b - 1))
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ (a - 1)) :
    coeff a b c (intMask a b c v w x hv hw hx) = (v, w, x) := by
  simp only [coeff, intMask, Int.toNat_of_nonneg hv.1, Int.toNat_of_nonneg hw.1, Int.toNat_of_nonneg hx.1]

private structure Choice (a b c : ℕ) (R T Z : ℤ) where
  p : Mask a b c
  q : Mask a b c
  r : Mask a b c
  pq : Disjoint (shiftedSupport a b c p) (shiftedSupport a b c q)
  pr : Disjoint (shiftedSupport a b c p) (shiftedSupport a b c r)
  qr : Disjoint (shiftedSupport a b c q) (shiftedSupport a b c r)
  good : margins R T Z (coeff a b c p) (coeff a b c q) (coeff a b c r)

private theorem pow_split (n j : ℕ) (h : j ≤ n) :
    (2 : ℤ) ^ n = 2 ^ j * 2 ^ (n - j) := by rw [←pow_add, Nat.add_sub_of_le h]

set_option maxHeartbeats 1200000 in
private def large_choice (a b c : ℕ) (ha : 4 ≤ a) (hab : a < b) (hbc : b < c) :
    Choice a b c (2 ^ a) (2 ^ b) (2 ^ c) := by
  let r : ℤ := 2 ^ (a - 4)
  let s : ℤ := 2 ^ (b - a - 1)
  let t : ℤ := 2 ^ (c - b - 1)
  have hr : 1 ≤ r := by dsimp [r]; exact one_le_pow₀ (by norm_num)
  have hs : 1 ≤ s := by dsimp [s]; exact one_le_pow₀ (by norm_num)
  have ht : 1 ≤ t := by dsimp [t]; exact one_le_pow₀ (by norm_num)
  have hA : (2 : ℤ) ^ a = 16 * r := by dsimp [r]; rw [pow_split a 4 ha]; norm_num
  have hB : (2 : ℤ) ^ b = 32 * r * s := by
    rw [pow_split b (a + 1) (by omega), pow_succ, hA]
    change 16 * r * 2 * (2 : ℤ) ^ (b - (a + 1)) = 32 * r * s
    rw [show b - (a + 1) = b - a - 1 by omega]; dsimp [s]; ring
  have hC : (2 : ℤ) ^ c = 64 * r * s * t := by
    rw [pow_split c (b + 1) (by omega), pow_succ, hB]
    change 32 * r * s * 2 * (2 : ℤ) ^ (c - (b + 1)) = 64 * r * s * t
    rw [show c - (b + 1) = c - b - 1 by omega]; dsimp [t]; ring
  have halves (n : ℕ) (hn : 1 ≤ n) : 2 * (2 : ℤ) ^ (n - 1) = 2 ^ n := by
    calc
      2 * (2 : ℤ) ^ (n - 1) = 2 ^ ((n - 1) + 1) := by rw [pow_succ]; ring
      _ = 2 ^ n := by congr 1; omega
  have hAh : (2 : ℤ) ^ (a - 1) = 8 * r := by have := halves a (by omega); rw [hA] at this; nlinarith only [this]
  have hBh : (2 : ℤ) ^ (b - 1) = 16 * r * s := by have := halves b (by omega); rw [hB] at this; nlinarith only [this]
  have hCh : (2 : ℤ) ^ (c - 1) = 32 * r * s * t := by have := halves c (by omega); rw [hC] at this; nlinarith only [this]
  have hrS : 1 ≤ r * s := by nlinarith
  have hrST : 1 ≤ r * s * t := by nlinarith
  have hbV : 0 ≤ (16 * r * s + 1) * t ∧ (16 * r * s + 1) * t < (2 : ℤ) ^ (c - 1) := by
    rw [hCh]; constructor <;> nlinarith
  have hbWq : 0 ≤ (8 * r + 1) * s ∧ (8 * r + 1) * s < (2 : ℤ) ^ (b - 1) := by
    rw [hBh]; constructor <;> nlinarith
  have hbWr : 0 ≤ (8 * r - 1) * s - 1 ∧ (8 * r - 1) * s - 1 < (2 : ℤ) ^ (b - 1) := by
    rw [hBh]; constructor <;> nlinarith
  have hbXp : 0 ≤ 5 * r ∧ 5 * r < (2 : ℤ) ^ (a - 1) := by rw [hAh]; omega
  have hbXq : 0 ≤ 3 * r - 1 ∧ 3 * r - 1 < (2 : ℤ) ^ (a - 1) := by rw [hAh]; omega
  have zero (n : ℕ) : 0 ≤ (0 : ℤ) ∧ 0 < (2 : ℤ) ^ n := ⟨le_rfl, by positivity⟩
  let p := intMask a b c 0 0 (5 * r) (zero _) (zero _) hbXp
  let q := intMask a b c 0 ((8 * r + 1) * s) (3 * r - 1) (zero _) hbWq hbXq
  let z := intMask a b c ((16 * r * s + 1) * t) ((8 * r - 1) * s - 1) 0 hbV hbWr (zero _)
  have hX := complementary_bits (a - 1) (8 * r) (5 * r) (3 * r - 1) hAh.symm hbXp.1 hbXq.1 (by ring)
  have hW := complementary_bits (b - 1) (16 * r * s) ((8 * r + 1) * s) ((8 * r - 1) * s - 1)
    hBh.symm hbWq.1 hbWr.1 (by ring)
  refine ⟨p, q, z, ?_, ?_, ?_, ?_⟩
  · apply shifted_disjoint
    · simp [p, q, intMask]
    · simp [p, q, intMask]
    · exact hX
  · apply shifted_disjoint <;> simp [p, z, intMask]
  · apply shifted_disjoint
    · simp [q, z, intMask]
    · exact hW
    · simp [q, z, intMask]
  · dsimp [p, q, z]
    rw [coeff_intMask, coeff_intMask, coeff_intMask, hA, hB, hC]
    exact large_margins r s t hr hs ht

set_option maxHeartbeats 1200000 in
private def small_choice (a b c : ℕ) (ha : a = 2 ∨ a = 3) (hb : 4 ≤ b) (hbc : b < c) :
    Choice a b c (2 ^ a) (2 ^ b) (2 ^ c) := by
  let r : ℤ := 2 ^ (a - 2)
  let u : ℤ := 2 ^ (b - 4)
  let v : ℤ := 2 ^ (c - b - 1)
  have hr : r = 1 ∨ r = 2 := by rcases ha with rfl|rfl <;> norm_num [r]
  have hu : 1 ≤ u := by dsimp [u]; exact one_le_pow₀ (by norm_num)
  have hv : 1 ≤ v := by dsimp [v]; exact one_le_pow₀ (by norm_num)
  have hA : (2 : ℤ) ^ a = 4 * r := by rw [pow_split a 2 (by omega)]; norm_num <;> rfl
  have hB : (2 : ℤ) ^ b = 16 * u := by rw [pow_split b 4 hb]; norm_num <;> rfl
  have hC : (2 : ℤ) ^ c = 32 * u * v := by
    rw [pow_split c (b + 1) (by omega), pow_succ, hB]
    rw [show c - (b + 1) = c - b - 1 by omega]; dsimp [v]; ring
  have hAh : (2 : ℤ) ^ (a - 1) = 2 * r := by rcases ha with rfl|rfl <;> norm_num [r]
  have hBh : (2 : ℤ) ^ (b - 1) = 8 * u := by
    rw [pow_split (b - 1) 3 (by omega)]; rw [show b - 1 - 3 = b - 4 by omega]; norm_num <;> rfl
  have hCh : (2 : ℤ) ^ (c - 1) = 16 * u * v := by
    have he : 2 * (2 : ℤ) ^ (c - 1) = 2 ^ c := by
      calc
        2 * (2 : ℤ) ^ (c - 1) = 2 ^ ((c - 1) + 1) := by rw [pow_succ]; ring
        _ = 2 ^ c := by congr 1; omega
    rw [hC] at he; nlinarith only [he]
  have htop : (2 : ℤ) ^ (b - 2) = 4 * u := by
    rw [pow_split (b - 2) 2 (by omega)]; rw [show b - 2 - 2 = b - 4 by omega]; norm_num <;> rfl
  have zero (n : ℕ) : 0 ≤ (0 : ℤ) ∧ 0 < (2 : ℤ) ^ n := ⟨le_rfl, by positivity⟩
  have bpw : 0 ≤ u ∧ u < (2 : ℤ) ^ (b - 1) := by rw [hBh]; omega
  have bqw : 0 ≤ 4 * u ∧ 4 * u < (2 : ℤ) ^ (b - 1) := by rw [hBh]; omega
  have brw : 0 ≤ 3 * u - 1 ∧ 3 * u - 1 < (2 : ℤ) ^ (b - 1) := by rw [hBh]; omega
  have bpx : 0 ≤ r ∧ r < (2 : ℤ) ^ (a - 1) := by rw [hAh]; omega
  have bqx : 0 ≤ r - 1 ∧ r - 1 < (2 : ℤ) ^ (a - 1) := by rw [hAh]; omega
  have brv : 0 ≤ (8 * u + 1) * v ∧ (8 * u + 1) * v < (2 : ℤ) ^ (c - 1) := by
    rw [hCh]
    have huv : 1 ≤ u * v := by nlinarith
    constructor <;> nlinarith
  let p := intMask a b c 0 u r (zero _) bpw bpx
  let q := intMask a b c 0 (4 * u) (r - 1) (zero _) bqw bqx
  let z := intMask a b c ((8 * u + 1) * v) (3 * u - 1) 0 brv brw (zero _)
  have hX := complementary_bits (a - 1) (2 * r) r (r - 1) hAh.symm bpx.1 bqx.1 (by ring)
  have hWpr := complementary_bits (b - 2) (4 * u) u (3 * u - 1) htop.symm (by omega) (by omega) (by ring)
  have hWqp := high_bit_disjoint (b - 2) (4 * u) u htop.symm (by omega) (by omega)
  have hWqr := high_bit_disjoint (b - 2) (4 * u) (3 * u - 1) htop.symm (by omega) (by omega)
  refine ⟨p, q, z, ?_, ?_, ?_, ?_⟩
  · apply shifted_disjoint
    · simp [p, q, intMask]
    · exact hWqp.symm
    · exact hX
  · apply shifted_disjoint
    · simp [p, z, intMask]
    · exact hWpr
    · simp [p, z, intMask]
  · apply shifted_disjoint
    · simp [q, z, intMask]
    · exact hWqr
    · simp [q, z, intMask]
  · dsimp [p, q, z]
    rw [coeff_intMask, coeff_intMask, coeff_intMask, hA, hB, hC]
    exact small_margins r u v hr hu hv

set_option maxHeartbeats 1200000 in
private def tail_choice (c : ℕ) (hc : 7 ≤ c) : Choice 2 3 c 4 8 (2 ^ c) := by
  let z : ℤ := 2 ^ (c - 7)
  have hz : 1 ≤ z := by dsimp [z]; exact one_le_pow₀ (by norm_num)
  have hC : (2 : ℤ) ^ c = 128 * z := by rw [pow_split c 7 hc]; norm_num <;> rfl
  have hCh : (2 : ℤ) ^ (c - 1) = 64 * z := by
    rw [pow_split (c - 1) 6 (by omega), show c - 1 - 6 = c - 7 by omega]; norm_num <;> rfl
  have hCp : (2 : ℤ) ^ (c - 4) = 8 * z := by
    rw [pow_split (c - 4) 3 (by omega), show c - 4 - 3 = c - 7 by omega]; norm_num <;> rfl
  have hCr : (2 : ℤ) ^ (c - 2) = 32 * z := by
    rw [pow_split (c - 2) 5 (by omega), show c - 2 - 5 = c - 7 by omega]; norm_num <;> rfl
  have bpv : 0 ≤ 8 * z ∧ 8 * z < (2 : ℤ) ^ (c - 1) := by rw [hCh]; omega
  have bqv : 0 ≤ z ∧ z < (2 : ℤ) ^ (c - 1) := by rw [hCh]; omega
  have brv : 0 ≤ 32 * z ∧ 32 * z < (2 : ℤ) ^ (c - 1) := by rw [hCh]; omega
  let p := intMask 2 3 c (8 * z) 0 1 bpv (by norm_num) (by norm_num)
  let q := intMask 2 3 c z 2 0 bqv (by norm_num) (by norm_num)
  let r := intMask 2 3 c (32 * z) 1 0 brv (by norm_num) (by norm_num)
  have hpq := high_bit_disjoint (c - 4) (8 * z) z hCp.symm (by omega) (by omega)
  have hrp := high_bit_disjoint (c - 2) (32 * z) (8 * z) hCr.symm (by omega) (by omega)
  have hrq := high_bit_disjoint (c - 2) (32 * z) z hCr.symm (by omega) (by omega)
  refine ⟨p, q, r, ?_, ?_, ?_, ?_⟩
  · apply shifted_disjoint
    · exact hpq
    · simp [p, q, intMask]
    · simp [p, q, intMask]
  · apply shifted_disjoint
    · exact hrp.symm
    · simp [p, r, intMask]
    · simp [p, r, intMask]
  · apply shifted_disjoint
    · exact hrq.symm
    · change Disjoint (2 : ℕ).bitIndices.toFinset (1 : ℕ).bitIndices.toFinset
      decide
    · simp [q, r, intMask]
  · dsimp [p, q, r]
    rw [coeff_intMask, coeff_intMask, coeff_intMask, hC]
    exact tail_margins z hz

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
