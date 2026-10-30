/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterFirstEarJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualOuterFirstEarJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complementary equal-outer physical orders with literal fresh-first insertion. -/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterSourceBridge
import D5.S3.Combinatorics.Circle.RunFirstEarTransport

/-! One common permutation for the two actual centered source tables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterFirstEarJointLift

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

private theorem mask_complement (u m n : ℕ) (h : m + n = 2 ^ u - 1) :
    Disjoint m.bitIndices.toFinset n.bitIndices.toFinset ∧
      m.bitIndices.toFinset ∪ n.bitIndices.toFinset = Finset.range u := by
  classical
  have hm : m < 2 ^ u := by
    have hp : 0 < 2 ^ u := by positivity
    omega
  have hsub : m.bitIndices.toFinset ⊆ Finset.range u := by
    intro i hi
    have hpow := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    apply Finset.mem_range.mpr
    by_contra h'
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (show u ≤ i by omega)
    omega
  let A := Finset.range u \ m.bitIndices.toFinset
  have hdis : Disjoint A m.bitIndices.toFinset := Finset.disjoint_left.mpr
    (fun i hi hmi => (Finset.mem_sdiff.mp hi).2 hmi)
  have hfull : A ∪ m.bitIndices.toFinset = Finset.range u := Finset.sdiff_union_of_subset hsub
  have hs := Finset.sum_union hdis (f := fun i : ℕ => 2 ^ i)
  have hsum : ∑ i ∈ Finset.range u, 2 ^ i = 2 ^ u - 1 := by
    simpa using Nat.geomSum_eq (by decide : 2 ≤ 2) u
  rw [hfull, Finset.sum_toFinset_bitIndices_two_pow, hsum] at hs
  have hA : n.bitIndices.toFinset = A := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
    dsimp only
    rw [Finset.sum_toFinset_bitIndices_two_pow]
    omega
  rw [hA]
  exact ⟨hdis.symm, by simpa only [Finset.union_comm] using hfull⟩

private def mask_labels (len off x : ℕ) (hx : x < 2 ^ len) : Finset ℕ :=
  (DyadicPrefix.bitSubset len x hx).image (fun i => off + i.val)

private theorem mask_labels_mem (len off x i : ℕ) (hx : x < 2 ^ len) :
    i ∈ mask_labels len off x hx ↔
      ∃ e : ℕ, e < len ∧ x.testBit e = true ∧ off + e = i := by
  classical
  constructor
  · intro hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨e, e.isLt, (DyadicPrefix.bit_subset_mem hx).mp he, rfl⟩
  · rintro ⟨e, he, hb, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨e, he⟩, (DyadicPrefix.bit_subset_mem hx).mpr hb, rfl⟩

private theorem mask_labels_bound {len off x i : ℕ} {hx : x < 2 ^ len}
    (hi : i ∈ mask_labels len off x hx) : off ≤ i ∧ i < off + len := by
  obtain ⟨e, he, _, hi⟩ := (mask_labels_mem len off x i hx).mp hi
  omega

private theorem mask_labels_disjoint {len off x y : ℕ}
    {hx : x < 2 ^ len} {hy : y < 2 ^ len}
    (hxy : Disjoint x.bitIndices.toFinset y.bitIndices.toFinset) :
    Disjoint (mask_labels len off x hx) (mask_labels len off y hy) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e, he, hb, hei⟩ := (mask_labels_mem len off x i hx).mp hi
  obtain ⟨e', he', hb', he'i⟩ := (mask_labels_mem len off y i hy).mp hj
  have heq : e' = e := by omega
  subst e'
  exact Finset.disjoint_left.mp hxy (by simpa using Nat.mem_bitIndices.mpr hb)
    (by simpa using Nat.mem_bitIndices.mpr hb')

private theorem mask_labels_sum (len off x : ℕ) (hx : x < 2 ^ len)
    (f : ℕ → ℤ) (A : ℤ) (hf : ∀ e < len, f (off + e) = (2 : ℤ) ^ e * A) :
    ∑ i ∈ mask_labels len off x hx, f i = (x : ℤ) * A := by
  classical
  have hinj : Function.Injective (fun i : Fin len => off + i.val) := by
    intro i j hij
    apply Fin.ext
    change off + i.val = off + j.val at hij
    omega
  unfold mask_labels
  rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
  simp_rw [hf _ (Fin.isLt _)]
  rw [← Finset.sum_mul]
  have hs : (∑ i ∈ DyadicPrefix.bitSubset len x hx, (2 : ℤ) ^ i.val) = (x : ℤ) := by
    exact_mod_cast DyadicPrefix.bit_subset_sum hx
  rw [hs]

/-- Disjoint physical supports, including three separate event labels, exhaust the whole word. -/
private theorem labelled_permutation (k av aw au : ℕ) (F Q : Finset ℕ)
    (hF : F ⊆ Finset.range k) (hQ : Q ⊆ Finset.range k)
    (hFQ : Disjoint F Q)
    (hne : av ≠ aw ∧ av ≠ au ∧ aw ≠ au)
    (hneg : av < k ∧ aw < k ∧ au < k)
    (hFn : ∀ i ∈ F, i ≠ av ∧ i ≠ aw ∧ i ≠ au)
    (hQn : ∀ i ∈ Q, i ≠ av ∧ i ≠ aw ∧ i ≠ au) :
    let G := Finset.range k \ (F ∪ Q ∪ {av, aw, au})
    (F.toList ++ av :: Q.toList ++ aw :: G.toList ++ [au]).Perm (List.range k) := by
  classical
  let E : Finset ℕ := ⟨(([av, aw, au] : List ℕ) : Multiset ℕ), by
    simpa using (show ([av, aw, au] : List ℕ).Nodup by simp [hne.1, hne.2.1, hne.2.2])⟩
  have hE (i : ℕ) : i ∈ E ↔ i = av ∨ i = aw ∨ i = au := by simp [E]
  have hEs : E = {av, aw, au} := by ext i; simp [hE]
  let G := Finset.range k \ (F ∪ Q ∪ E)
  have hG : G = Finset.range k \ (F ∪ Q ∪ {av, aw, au}) := by dsimp only [G]; rw [hEs]
  have hFG : Disjoint (F.disjUnion Q hFQ) G := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' : i ∈ F ∪ Q ∪ E := by
      simp only [Finset.mem_union]
      have hh := Finset.mem_disjUnion.mp hi
      tauto
    exact (Finset.mem_sdiff.mp hj).2 hi'
  have hNE : Disjoint ((F.disjUnion Q hFQ).disjUnion G hFG) E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have he := (hE i).mp hj
    simp only [Finset.mem_disjUnion] at hi
    rcases hi with (hi | hi) | hi
    · obtain ⟨ha, hb, hc⟩ := hFn i hi
      tauto
    · obtain ⟨ha, hb, hc⟩ := hQn i hi
      tauto
    · exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_right _ hj)
  let T := ((F.disjUnion Q hFQ).disjUnion G hFG).disjUnion E hNE
  have hT : T = Finset.range k := by
    ext i
    have hFi : i ∈ F → i ∈ Finset.range k := fun hi => hF hi
    have hQi : i ∈ Q → i ∈ Finset.range k := fun hi => hQ hi
    have hEi : i ∈ E → i ∈ Finset.range k := by
      intro hi
      rcases (hE i).mp hi with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    simp only [T, G, Finset.mem_disjUnion, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [← hG]
  apply Multiset.coe_eq_coe.mp
  have hs :
      ((F.toList ++ av :: Q.toList ++ aw :: G.toList ++ [au] : List ℕ) : Multiset ℕ) =
        T.val := by
    change (F.toList : Multiset ℕ) + ({av} + (Q.toList : Multiset ℕ)) +
      ({aw} + (G.toList : Multiset ℕ)) + {au} =
        F.val + Q.val + G.val + ({av} + {aw} + {au})
    simp only [Finset.coe_toList]
    ac_rfl
  rw [hs, hT]
  rfl

private def label (k : ℕ) (hk : 0 < k) (i : ℕ) : Fin k :=
  ⟨i % k, Nat.mod_lt i hk⟩

private theorem lift_order (k t : ℕ) (hk : 0 < k) (l : List ℕ)
    (hp : l.Perm (List.range k))
    (hs : InStrip (fun i => centered (modulus k) ((2 : ℤ) ^ i * t))
      (modulus k / 2) 0 l)
    (hz : ((List.range k).map (fun i => centered (modulus k) ((2 : ℤ) ^ i * t))).sum = 0) :
    OriginalOrder k t (l.map (label k hk)) := by
  let f := fun i : ℕ => centered (modulus k) ((2 : ℤ) ^ i * t)
  have hbase : (List.range k).map (label k hk) = List.finRange k := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      apply Fin.ext
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, label]
      exact Nat.mod_eq_of_lt (by simpa using hi)
  have hvalue : ∀ i ∈ l, actualSource k t (label k hk i) = f i := by
    intro i hi
    have hib : i < k := List.mem_range.mp (hp.mem_iff.mp hi)
    simp only [actualSource, label, Nat.mod_eq_of_lt hib, f]
  have hm : (l.map (label k hk)).map (actualSource k t) = l.map f := by
    rw [List.map_map]
    exact List.map_congr_left hvalue
  refine ⟨by rw [← hbase]; exact hp.map _, ?_, ?_⟩
  · rw [hm]
    exact (hp.map f).sum_eq.trans hz
  · intro n
    have hv : ∀ i ∈ l.take n, actualSource k t (label k hk i) = f i :=
      fun i hi => hvalue i (List.mem_of_mem_take hi)
    have hm' := List.map_congr_left hv
    have hn := inStrip_prefix hs n
    simpa only [← List.map_take, List.map_map, Function.comp_def, hm', zero_add,
      Set.mem_Icc] using hn

private theorem marked_word (k cut : ℕ) (hk : 0 < k) (P R : List ℕ)
    (hlen : P.length = cut) (hp : (P ++ R).Perm (List.range k)) :
    earWord k ((P ++ R).map (label k hk)) cut =
      (P ++ k :: R).map (label (k + 1) (by omega)) := by
  have hb : ∀ i ∈ P ++ R, i < k := fun i hi => List.mem_range.mp (hp.mem_iff.mp hi)
  have hcast (L : List ℕ) (hL : ∀ i ∈ L, i < k) :
      (L.map (label k hk)).map Fin.castSucc =
        L.map (label (k + 1) (by omega)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    apply Fin.ext
    simp only [Function.comp_def, label, Fin.val_castSucc, Nat.mod_eq_of_lt (hL i hi),
      Nat.mod_eq_of_lt (show i < k + 1 from by have := hL i hi; omega)]
  have hP := hcast P (fun i hi => hb i (List.mem_append_left R hi))
  have hR := hcast R (fun i hi => hb i (List.mem_append_right P hi))
  have hl : (P.map (label k hk)).length = cut := by simpa using hlen
  have hlast : label (k + 1) (by omega) k = Fin.last k := by
    apply Fin.ext
    simp [label, Nat.mod_eq_of_lt (show k < k + 1 by omega)]
  simp only [earWord, List.map_append, ← hl, List.take_left, List.drop_left, hP, hR,
    List.map_cons, List.map_append, hlast, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]


private theorem paired_chains (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    let r : ℤ := 2 ^ a
    let s : ℤ := 2 ^ b
    let k := a + b + a
    let N := modulus k
    let v := 1 + r + r * s
    let B := 1 + r + r * r
    let L := 1 + s + s * r
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
    let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * v))
    (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (∀ i < a - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
    (∀ i < b - 1, f (a + i) = (2 : ℤ) ^ i * B ∧
      g (a + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
    (∀ i < a - 1, f (a + b + i) = (2 : ℤ) ^ i * L ∧
      g (a + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
    f (a - 1) = -(N - B) / 2 ∧
    f (a + b - 1) = -(N - L) / 2 ∧
    f (k - 1) = -(N - v) / 2 ∧
    g (a - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
    g (a + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
    g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v := by
  dsimp only
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let k := a + b + a
  let N := modulus k
  let M := modulus (k + 1)
  let v := 1 + r + r * s
  let B := 1 + r + r * r
  let L := 1 + s + s * r
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
  let F := fun i : ℕ => centered M ((2 : ℤ) ^ i * v)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * (2 * v))
  change (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (∀ i < a - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
    (∀ i < b - 1, f (a + i) = (2 : ℤ) ^ i * B ∧
      g (a + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
    (∀ i < a - 1, f (a + b + i) = (2 : ℤ) ^ i * L ∧
      g (a + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
    f (a - 1) = -(N - B) / 2 ∧ f (a + b - 1) = -(N - L) / 2 ∧
    f (k - 1) = -(N - v) / 2 ∧
    g (a - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
    g (a + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
    g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v
  obtain ⟨hv, hB, hL, _, hU, hV, hW⟩ :=
    ThreeNegativeEqualOuterSourceBridge.actual_source_chains a b a (by omega) (by omega) ha
  change (1 ≤ v ∧ v < N) at hv
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ e < a, f e = if e + 1 < a then (2 : ℤ) ^ e * v else -(N - B) / 2 at hU
  change ∀ e < b, f (a + e) = if e + 1 < b then (2 : ℤ) ^ e * B else -(N - L) / 2 at hV
  change ∀ e < a, f (a + b + e) = if e + 1 < a then (2 : ℤ) ^ e * L else -(N - v) / 2 at hW
  obtain ⟨_, _, _, _, hU', hV', hW'⟩ :=
    ThreeNegativeEqualOuterSourceBridge.actual_source_chains a b (a + 1) (by omega) (by omega) (by omega)
  have hM : modulus (a + b + (a + 1)) = M := rfl
  have hr : (2 : ℤ) ^ (a + 1) = 2 * r := by dsimp [r]; rw [pow_succ]; ring
  have hB' : 1 + (2 : ℤ) ^ (a + 1) + 2 ^ (a + 1) * 2 ^ a = 2 * B - 1 := by
    rw [hr]; change 1 + 2 * r + 2 * r * r = _; dsimp [B]; ring
  have hL' : 1 + (2 : ℤ) ^ b + 2 ^ b * 2 ^ (a + 1) = 2 * L - s - 1 := by
    rw [hr]; change 1 + s + s * (2 * r) = _; dsimp [L]; ring
  rw [hM, hB'] at hU'
  rw [hM, hB', hL'] at hV'
  rw [hM, hL'] at hW'
  have hshift (i : ℕ) : g i = F (i + 1) := by
    dsimp [g, F]; rw [pow_succ]; congr 1; ring
  have hMN : M = 2 * N + 1 := by dsimp [M, N, modulus]; rw [pow_succ]; ring
  refine ⟨hv, hB, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < a by omega)] using hU i (by omega)
    · rw [hshift]
      have h := hU' (i + 1) (by omega)
      rw [ite_eq_left (by omega), pow_succ] at h
      change F (i + 1) = _ at h
      rw [h]; ring
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < b by omega)] using hV i (by omega)
    · rw [hshift, show a + i + 1 = (a + 1) + i by omega]
      exact (hV' i (by omega)).trans (ite_eq_left (by omega))
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < a by omega)] using hW i (by omega)
    · rw [hshift, show a + b + i + 1 = (a + 1) + b + i by omega]
      exact (hW' i (by omega)).trans (ite_eq_left (by omega))
  · simpa only [ite_eq_right (by omega : ¬ a - 1 + 1 < a)] using hU (a - 1) (by omega)
  · simpa only [show a + (b - 1) = a + b - 1 by omega,
      ite_eq_right (by omega : ¬ b - 1 + 1 < b)] using hV (b - 1) (by omega)
  · simpa only [show a + b + (a - 1) = k - 1 by dsimp [k]; omega,
      ite_eq_right (by omega : ¬ a - 1 + 1 < a)] using hW (a - 1) (by omega)
  · rw [hshift, show a - 1 + 1 = a by omega]
    simpa only [ite_eq_right (by omega : ¬ a + 1 < a + 1), F, hMN] using hU' a (by omega)
  · rw [hshift, show a + b - 1 + 1 = (a + 1) + (b - 1) by omega]
    simpa only [ite_eq_right (by omega : ¬ b - 1 + 1 < b), F, hMN] using hV' (b - 1) (by omega)
  · rw [hshift, show k - 1 + 1 = (a + 1) + b + (a - 1) by dsimp [k]; omega]
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

private def margins (R S pu pv pw tu tv tw : ℤ) : Prop :=
  let N := 8 * R ^ 2 * S - 1
  let C := 4 * R ^ 2 * S - 1
  let v := 1 + 2 * R + 4 * R * S
  let B := 1 + 2 * R + 4 * R ^ 2
  let L := 1 + 2 * S + 4 * R * S
  let Ha := 4 * R ^ 2 * S - 2 * R ^ 2 - R - 1
  let Hb := 4 * R ^ 2 * S - 2 * R * S - S - 1
  let Hg := 4 * R ^ 2 * S - 2 * R * S - R - 1
  let Ka := 2 * Ha + 1
  let Kb := 2 * Hb + S + 1
  let Kg := 8 * R ^ 2 * S - 2 * R * S - R - 1
  let x := v * pu + B * pv + L * pw
  let xn := v + 2 * v * pu + (2 * B - 1) * pv + (2 * L - 2 * S - 1) * pw
  let t := v * tu + B * tv + L * tw
  let tn := 2 * v * tu + (2 * B - 1) * tv + (2 * L - 2 * S - 1) * tw
  0 ≤ C - x ∧ 0 ≤ x - Hb ∧ 0 ≤ N - xn ∧ 0 ≤ xn - Kb ∧
    0 ≤ Hg - t ∧ 0 ≤ Kg - tn ∧
    0 ≤ C - (Ha + Hg - t) ∧ 0 ≤ N - (Ka + Kg - tn)

private structure Choice (R S : ℤ) where
  pu : ℤ
  pv : ℤ
  pw : ℤ
  tu : ℤ
  tv : ℤ
  tw : ℤ
  bounds : (0 ≤ pu ∧ pu < R) ∧ (0 ≤ pv ∧ pv < S) ∧ (0 ≤ pw ∧ pw < R) ∧
    (0 ≤ tu ∧ tu < R) ∧ (0 ≤ tv ∧ tv < S) ∧ (0 ≤ tw ∧ tw < R)
  orthogonal : Disjoint pu.toNat.bitIndices.toFinset tu.toNat.bitIndices.toFinset ∧
    Disjoint pv.toNat.bitIndices.toFinset tv.toNat.bitIndices.toFinset ∧
    Disjoint pw.toNat.bitIndices.toFinset tw.toNat.bitIndices.toFinset
  good : margins R S pu pv pw tu tv tw

private theorem complementary_bits (len : ℕ) (R p t : ℤ) (hR : R = 2 ^ len)
    (hp : 0 ≤ p) (ht : 0 ≤ t) (he : p + t = R - 1) :
    Disjoint p.toNat.bitIndices.toFinset t.toNat.bitIndices.toFinset := by
  have hp' : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp
  have ht' : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
  have hpow : (((2 : ℕ) ^ len : ℕ) : ℤ) = R := by push_cast; exact hR.symm
  have hpos : 0 < (2 : ℕ) ^ len := by positivity
  have hsum : p.toNat + t.toNat = 2 ^ len - 1 := by omega
  exact (mask_complement len p.toNat t.toNat hsum).1

private theorem high_bit_disjoint (len : ℕ) (S t : ℤ) (hS : S = 2 ^ len)
    (ht : 0 ≤ t) (hlt : t < S) :
    Disjoint S.toNat.bitIndices.toFinset t.toNat.bitIndices.toFinset := by
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hs : S.toNat = 2 ^ len := by
    have hh : S = (((2 : ℕ) ^ len : ℕ) : ℤ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hS
    rw [hh, Int.toNat_natCast]
  rw [hs, Nat.bitIndices_two_pow]
  change Disjoint ({len} : Finset ℕ) t.toNat.bitIndices.toFinset
  rw [Finset.disjoint_singleton_left]
  intro hi
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  have ht' : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
  have hpow : (((2 : ℕ) ^ len : ℕ) : ℤ) = S := by push_cast; exact hS.symm
  omega

private def equal_choice (S : ℤ) (hS : 2 ≤ S) : Choice S S where
  pu := 0
  pv := S - 1
  pw := 0
  tu := 0
  tv := 0
  tw := S - 1
  bounds := by omega
  orthogonal := by simp
  good := by
    dsimp [margins]
    have hss : 0 ≤ S * (S - 1) := mul_nonneg (by omega) (by omega)
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> nlinarith

private def adjacent_choice (e : ℕ) (tau : ℤ) (ht : 1 ≤ tau)
    (hR : 8 * tau = (2 : ℤ) ^ (e + 1))
    (hS : 4 * tau = (2 : ℤ) ^ e) : Choice (8 * tau) (4 * tau) where
  pu := 2 * tau - 1
  pv := tau
  pw := 4 * tau
  tu := 6 * tau
  tv := 0
  tw := 2 * tau - 2
  bounds := by omega
  orthogonal := by
    refine ⟨complementary_bits (e + 1) (8 * tau) _ _ hR (by omega) (by omega) (by ring),
      by simp, high_bit_disjoint e (4 * tau) _ hS (by omega) (by omega)⟩
  good := by
    dsimp [margins]
    have ht2 : 1 ≤ tau ^ 2 := by nlinarith
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> nlinarith

set_option maxHeartbeats 4000000 in
-- The paired integer source and mask expressions require a larger elaboration budget.
private def large_choice (len : ℕ) (R S q : ℤ) (hS : 4 ≤ S) (hq : 4 ≤ q)
    (hRS : R = q * S) (hR : R = 2 ^ len) : Choice R S := by
  let v := 1 + 2 * R + 4 * R * S
  let L := 1 + 2 * S + 4 * R * S
  let B := 1 + 2 * R + 4 * R ^ 2
  let n := (3 * q * L) / v
  let d := 3 * q * L - v * n
  let e := 1 + R + 2 * R * S + 2 * d + (2 * S + 1) * (R - 3 * q)
  have hR0 : 16 ≤ R := by nlinarith [mul_nonneg (show 0 ≤ q - 4 by omega) (show 0 ≤ S - 4 by omega)]
  have hRq : 4 * q ≤ R := by nlinarith
  have hRs : 4 * S ≤ R := by nlinarith
  have hv : 0 < v := by dsimp [v]; positivity
  have hL : L ≤ v := by dsimp [L, v]; omega
  have hB : v ≤ B := by dsimp [v, B]; nlinarith [mul_nonneg (show 0 ≤ R by omega) (show 0 ≤ R - S by omega)]
  have hqL : q * L = B + q - 1 := by dsimp [L, B]; rw [hRS]; ring
  have hrem := Int.emod_add_mul_ediv (3 * q * L) v
  have hr0 := Int.emod_nonneg (3 * q * L) (ne_of_gt hv)
  have hrv := Int.emod_lt_of_pos (3 * q * L) hv
  have hd : 0 ≤ d ∧ d ≤ v - 1 := by dsimp [d, n]; omega
  have hn : 1 ≤ n ∧ n ≤ 3 * q := by
    have hmul := mul_le_mul_of_nonneg_left hL (show 0 ≤ 3 * q by omega)
    have hlow : v ≤ q * L := by omega
    dsimp [d] at hd
    constructor
    · by_contra hh
      have hn0 : n ≤ 0 := by omega
      have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hv) hn0
      nlinarith
    · by_contra hh
      have hn0 : 3 * q + 1 ≤ n := by omega
      have hm := mul_le_mul_of_nonneg_left hn0 (le_of_lt hv)
      nlinarith
  have hdB : d ≤ 2 * R ^ 2 + R := by
    have hpos := mul_nonneg (show 0 ≤ R by omega) (show 0 ≤ 2 * R - 4 * S - 1 by omega)
    dsimp [v] at hd
    nlinarith
  have he0 : 0 ≤ e := by
    have hh := mul_nonneg (show 0 ≤ 2 * S + 1 by omega) (show 0 ≤ R - 3 * q by omega)
    have hp : 0 ≤ 2 * R * S := by positivity
    dsimp only [e]
    omega
  have heB : e ≤ 4 * R ^ 2 + 2 * R := by
    have he1 : e ≤ 3 * v - 2 := by
      dsimp [e, v] at *
      nlinarith [mul_nonneg (show 0 ≤ 2 * S + 1 by omega) (show 0 ≤ 3 * q by omega)]
    have hgap : 3 * R ≤ R * (R - 3 * S - 1) :=
      mul_le_mul_of_nonneg_left (show 3 ≤ R - 3 * S - 1 by omega) (show 0 ≤ R by omega)
    dsimp [v] at he1
    nlinarith
  refine {
    pu := 0
    pv := S - 3
    pw := 3 * q - 1
    tu := n - 1
    tv := 0
    tw := R - 3 * q
    bounds := by omega
    orthogonal := ?_
    good := ?_ }
  · exact ⟨by simp, by simp,
      complementary_bits len R _ _ hR (by omega) (by omega) (by ring)⟩
  · dsimp [margins]
    have h1 : 0 ≤ q * (2 * S ^ 2 - 3) + S + 3 := by
      have hh := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ 2 * S ^ 2 - 3 by nlinarith)
      omega
    have h2 : 0 ≤ 3 * (q - 1) := by omega
    have h3 : 0 ≤ q * (4 * S - 3) + S + 2 := by
      have hh := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ 4 * S - 3 by omega)
      omega
    have h4 : 0 ≤ q * (4 * S ^ 2 - 4 * S + 3) - 2 := by
      nlinarith [mul_nonneg (show 0 ≤ q - 4 by omega) (show 0 ≤ 4 * S ^ 2 - 4 * S + 3 by nlinarith)]
    have heqD :
        (4 * R ^ 2 * S - 2 * R * S - R - 1) -
        ((1 + 2 * R + 4 * R * S) * (n - 1) +
          (1 + 2 * S + 4 * R * S) * (R - 3 * q)) = d := by
      dsimp [d, v, L]; ring
    have heqE :
        (8 * R ^ 2 * S - 2 * R * S - R - 1) -
        (2 * (1 + 2 * R + 4 * R * S) * (n - 1) +
          (2 * (1 + 2 * S + 4 * R * S) - 2 * S - 1) * (R - 3 * q)) = e := by
      dsimp [e, d, v, L]; ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert h1 using 1 <;> rw [hRS] <;> ring
    · convert h2 using 1 <;> rw [hRS] <;> ring
    · convert h3 using 1 <;> rw [hRS] <;> ring
    · convert h4 using 1 <;> rw [hRS] <;> ring
    · simpa only [mul_zero, zero_add, add_zero, heqD] using hd.1
    · simpa only [mul_zero, zero_add, add_zero, heqE] using he0
    · nlinarith only [heqD, hdB]
    · nlinarith only [heqE, heB]

set_option maxHeartbeats 4000000 in
-- The paired integer source and mask expressions require a larger elaboration budget.
private def small_choice (R : ℤ) (hR : 16 ≤ R) : Choice R 2 := by
  let v := 1 + 10 * R
  let H := 8 * R ^ 2 - 5 * R - 1
  let z := H / v
  let d := H - v * z
  have hv : 0 < v := by dsimp [v]; omega
  have hH : 0 ≤ H := by dsimp [H]; nlinarith
  have hrem := Int.emod_add_mul_ediv H v
  have hr0 := Int.emod_nonneg H (ne_of_gt hv)
  have hr1 := Int.emod_lt_of_pos H hv
  have hd : 0 ≤ d ∧ d ≤ 10 * R := by dsimp [d, z, v] at *; omega
  have hz0 : 0 ≤ z := Int.ediv_nonneg hH (le_of_lt hv)
  have hzR : z < R := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_left (show R ≤ z by omega) (le_of_lt hv)
    dsimp [d, H, v] at *
    nlinarith
  have hdB : d ≤ 2 * R ^ 2 + R := by nlinarith
  have heB : 1 + 5 * R + 2 * d ≤ 4 * R ^ 2 + 2 * R := by nlinarith
  refine {
    pu := 0
    pv := 0
    pw := R - 1
    tu := z
    tv := 0
    tw := 0
    bounds := by omega
    orthogonal := by simp
    good := ?_ }
  dsimp [margins]
  have heq : (8 * R ^ 2 * 2 - 2 * R * 2 - R - 1) -
      2 * (1 + 2 * R + 4 * R * 2) * z = 1 + 5 * R + 2 * d := by
    dsimp [d, H, v]; ring
  have heqD : (4 * R ^ 2 * 2 - 2 * R * 2 - R - 1) -
      (1 + 2 * R + 4 * R * 2) * z = d := by dsimp [d, H, v]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · simpa only [mul_zero, zero_add, add_zero, heqD] using hd.1
  · simp only [mul_zero, zero_add, add_zero, heq]
    omega
  · nlinarith only [heqD, hdB]
  · nlinarith only [heq, heB]

private def packet (a b u v w : ℕ) (hu : u < 2 ^ (a - 1))
    (hv : v < 2 ^ (b - 1)) (hw : w < 2 ^ (a - 1)) : Finset ℕ :=
  mask_labels (a - 1) 0 u hu ∪
    mask_labels (b - 1) a v hv ∪
    mask_labels (a - 1) (a + b) w hw

private theorem packet_bound (a b u v w : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hu : u < 2 ^ (a - 1)) (hv : v < 2 ^ (b - 1)) (hw : w < 2 ^ (a - 1))
    {i : ℕ} (hi : i ∈ packet a b u v w hu hv hw) :
    i < a + b + a ∧ i ≠ a - 1 ∧ i ≠ a + b - 1 ∧ i ≠ a + b + a - 1 := by
  simp only [packet, Finset.mem_union] at hi
  rcases hi with (hi | hi) | hi <;>
    have hi' := mask_labels_bound hi <;> omega

private theorem packet_sum (a b u v w : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hu : u < 2 ^ (a - 1)) (hv : v < 2 ^ (b - 1)) (hw : w < 2 ^ (a - 1))
    (f : ℕ → ℤ) (U V W : ℤ)
    (hU : ∀ i < a - 1, f i = (2 : ℤ) ^ i * U)
    (hV : ∀ i < b - 1, f (a + i) = (2 : ℤ) ^ i * V)
    (hW : ∀ i < a - 1, f (a + b + i) = (2 : ℤ) ^ i * W) :
    ∑ i ∈ packet a b u v w hu hv hw, f i = u * U + v * V + w * W := by
  have hUV : Disjoint (mask_labels (a - 1) 0 u hu)
      (mask_labels (b - 1) a v hv) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  have hUW : Disjoint (mask_labels (a - 1) 0 u hu)
      (mask_labels (a - 1) (a + b) w hw) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  have hVW : Disjoint (mask_labels (b - 1) a v hv)
      (mask_labels (a - 1) (a + b) w hw) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  unfold packet
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hUW, hVW⟩),
    Finset.sum_union hUV]
  rw [mask_labels_sum (a - 1) 0 u hu f U (by simpa using hU),
    mask_labels_sum (b - 1) a v hv f V hV,
    mask_labels_sum (a - 1) (a + b) w hw f W hW]

private theorem packet_disjoint (a b u v w x y z : ℕ)
    (hu : u < 2 ^ (a - 1)) (hv : v < 2 ^ (b - 1)) (hw : w < 2 ^ (a - 1))
    (hx : x < 2 ^ (a - 1)) (hy : y < 2 ^ (b - 1)) (hz : z < 2 ^ (a - 1))
    (hbits : Disjoint u.bitIndices.toFinset x.bitIndices.toFinset ∧
      Disjoint v.bitIndices.toFinset y.bitIndices.toFinset ∧
      Disjoint w.bitIndices.toFinset z.bitIndices.toFinset) :
    Disjoint (packet a b u v w hu hv hw) (packet a b x y z hx hy hz) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [packet, Finset.mem_union] at hi hj
  rcases hi with (hi | hi) | hi <;> rcases hj with (hj | hj) | hj
  · exact Finset.disjoint_left.mp (mask_labels_disjoint hbits.1) hi hj
  · have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  · have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  · have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  · exact Finset.disjoint_left.mp (mask_labels_disjoint hbits.2.1) hi hj
  · have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  · have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  · have hi' := mask_labels_bound hi
    have hj' := mask_labels_bound hj
    omega
  · exact Finset.disjoint_left.mp (mask_labels_disjoint hbits.2.2) hi hj

set_option maxHeartbeats 4000000 in
-- The paired integer source and mask expressions require a larger elaboration budget.
private theorem realize_choice (a b : ℕ) (hb : 2 ≤ b) (hab : b ≤ a)
    (c : Choice ((2 : ℤ) ^ (a - 1)) ((2 : ℤ) ^ (b - 1))) :
    ∃ sigma : List (Fin (a + b + a)),
      OriginalOrder (a + b + a) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + a + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + a) sigma 0) := by
  classical
  have ha : 2 ≤ a := by omega
  let R : ℤ := 2 ^ (a - 1)
  let S : ℤ := 2 ^ (b - 1)
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let k := a + b + a
  let N := modulus k
  let C := 4 * R ^ 2 * S - 1
  let v := 1 + r + r * s
  let B := 1 + r + r * r
  let L := 1 + s + s * r
  let Ha := 4 * R ^ 2 * S - 2 * R ^ 2 - R - 1
  let Hb := 4 * R ^ 2 * S - 2 * R * S - S - 1
  let Hg := 4 * R ^ 2 * S - 2 * R * S - R - 1
  let Ka := 2 * Ha + 1
  let Kb := 2 * Hb + S + 1
  let Kg := 8 * R ^ 2 * S - 2 * R * S - R - 1
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
  let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * v))
  have hR : 2 ≤ R := by
    simpa [R] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ a - 1 by omega)
  have hS : 2 ≤ S := by
    simpa [S] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ b - 1 by omega)
  have hRS : S ≤ R := by
    dsimp [S, R]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hr : r = 2 * R := by
    calc
      r = (2 : ℤ) ^ ((a - 1) + 1) := by dsimp [r]; congr 1; omega
      _ = 2 * R := by rw [pow_succ]; dsimp [R]; ring
  have hs : s = 2 * S := by
    calc
      s = (2 : ℤ) ^ ((b - 1) + 1) := by dsimp [s]; congr 1; omega
      _ = 2 * S := by rw [pow_succ]; dsimp [S]; ring
  have hN : N = 8 * R ^ 2 * S - 1 := by
    dsimp [N, k, modulus]
    rw [pow_add, pow_add]
    change r * s * r - 1 = _
    rw [hr, hs]; ring
  have hhalf : modulus k / 2 = C := by
    have hNC : N = 2 * C + 1 := by rw [hN]; dsimp [C]; ring
    change N / 2 = C
    omega
  have hnewN : modulus (k + 1) = 2 * N + 1 := by
    dsimp [modulus, N]; rw [pow_succ]; ring
  have hnewhalf : modulus (k + 1) / 2 = N := by rw [hnewN]; omega
  obtain ⟨hv, hB, hL, hU, hV, hW, hfA, hfB, hfG, hgA, hgB, hgG, hgear⟩ :=
    paired_chains a b ha hb
  change (1 ≤ v ∧ v < N) at hv
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ i < a - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v) at hU
  change ∀ i < b - 1, f (a + i) = (2 : ℤ) ^ i * B ∧
    g (a + i) = (2 : ℤ) ^ i * (2 * B - 1) at hV
  change ∀ i < a - 1, f (a + b + i) = (2 : ℤ) ^ i * L ∧
    g (a + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1) at hW
  change f (a - 1) = -(N - B) / 2 at hfA
  change f (a + b - 1) = -(N - L) / 2 at hfB
  change f (k - 1) = -(N - v) / 2 at hfG
  change g (a - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 at hgA
  change g (a + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 at hgB
  change g (k - 1) = -((2 * N + 1) - v) / 2 at hgG
  change g k = v at hgear
  have hHa : 2 * Ha = N - B := by rw [hN]; dsimp [Ha, B]; rw [hr]; ring
  have hHb : 2 * Hb = N - L := by rw [hN]; dsimp [Hb, L]; rw [hr, hs]; ring
  have hHg : 2 * Hg = N - v := by rw [hN]; dsimp [Hg, v]; rw [hr, hs]; ring
  have hKa : 2 * Ka = 2 * N + 1 - (2 * B - 1) := by dsimp [Ka]; omega
  have hKb : 2 * Kb = 2 * N + 1 - (2 * L - s - 1) := by dsimp [Kb]; rw [hs]; omega
  have hKg : 2 * Kg = 2 * N + 1 - v := by rw [hN]; dsimp [Kg, v]; rw [hr, hs]; ring
  have hfA' : f (a - 1) = -Ha := by rw [hfA]; omega
  have hfB' : f (a + b - 1) = -Hb := by rw [hfB]; omega
  have hfG' : f (k - 1) = -Hg := by rw [hfG]; omega
  have hgA' : g (a - 1) = -Ka := by rw [hgA]; omega
  have hgB' : g (a + b - 1) = -Kb := by rw [hgB]; omega
  have hgG' : g (k - 1) = -Kg := by rw [hgG]; omega
  have hneg : 0 ≤ Hb ∧ 0 ≤ Ha ∧ 0 ≤ Hg ∧ Hg ≤ C ∧
      0 ≤ Kb ∧ 0 ≤ Ka ∧ 0 ≤ Kg ∧ Kg ≤ N := by
    have hC : 2 * C = N - 1 := by rw [hN]; dsimp [C]; ring
    dsimp [Ka, Kb] at *
    omega
  have hpositive (i : ℕ) (hi : i < k) (hiA : i ≠ a - 1)
      (hiB : i ≠ a + b - 1) (hiG : i ≠ k - 1) : 0 ≤ f i ∧ 0 ≤ g i := by
    by_cases hia : i < a - 1
    · rw [(hU i hia).1, (hU i hia).2]
      constructor <;> positivity
    · by_cases hib : i < a + b - 1
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ i by omega)
        rw [(hV j (by omega)).1, (hV j (by omega)).2]
        constructor <;> apply mul_nonneg (by positivity) (by omega)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show a + b ≤ i by omega)
        rw [(hW j (by dsimp [k] at *; omega)).1, (hW j (by dsimp [k] at *; omega)).2]
        have hnewL : 0 ≤ 2 * L - s - 1 := by
          dsimp [L]; rw [hr, hs]; ring_nf; positivity
        constructor <;> positivity
  obtain ⟨hpu, hpv, hpw, htu, htv, htw⟩ := c.bounds
  have castU : ∀ (x : ℤ), 0 ≤ x → (x.toNat : ℤ) = x := fun x hx => Int.toNat_of_nonneg hx
  have boundU (x : ℤ) (hx : 0 ≤ x ∧ x < R) : x.toNat < 2 ^ (a - 1) := by
    have hh := castU x hx.1
    have hp : (((2 : ℕ) ^ (a - 1) : ℕ) : ℤ) = R := by simp [R]
    omega
  have boundV (x : ℤ) (hx : 0 ≤ x ∧ x < S) : x.toNat < 2 ^ (b - 1) := by
    have hh := castU x hx.1
    have hp : (((2 : ℕ) ^ (b - 1) : ℕ) : ℤ) = S := by simp [S]
    omega
  let P := packet a b c.pu.toNat c.pv.toNat c.pw.toNat (boundU _ hpu) (boundV _ hpv) (boundU _ hpw)
  let T := packet a b c.tu.toNat c.tv.toNat c.tw.toNat (boundU _ htu) (boundV _ htv) (boundU _ htw)
  let Q := Finset.range k \ (P ∪ T ∪ {a + b - 1, a - 1, k - 1})
  have hPT : Disjoint P T := packet_disjoint a b _ _ _ _ _ _ _ _ _ _ _ _ c.orthogonal
  have hPbound (i : ℕ) (hi : i ∈ P) :
      i < k ∧ i ≠ a - 1 ∧ i ≠ a + b - 1 ∧ i ≠ k - 1 :=
    packet_bound a b _ _ _ ha hb _ _ _ hi
  have hTbound (i : ℕ) (hi : i ∈ T) :
      i < k ∧ i ≠ a - 1 ∧ i ≠ a + b - 1 ∧ i ≠ k - 1 :=
    packet_bound a b _ _ _ ha hb _ _ _ hi
  have hp0 := labelled_permutation k (a + b - 1) (a - 1) (k - 1) P T
    (fun i hi => Finset.mem_range.mpr (hPbound i hi).1)
    (fun i hi => Finset.mem_range.mpr (hTbound i hi).1) hPT
    (by dsimp [k]; omega) (by dsimp [k]; omega)
    (fun i hi => by have := hPbound i hi; tauto)
    (fun i hi => by have := hTbound i hi; tauto)
  change (P.toList ++ (a + b - 1) :: T.toList ++ (a - 1) :: Q.toList ++ [k - 1]).Perm
    (List.range k) at hp0
  let word := P.toList ++ (a + b - 1) :: Q.toList ++ (a - 1) :: T.toList ++ [k - 1]
  have hp : word.Perm (List.range k) := by
    apply List.Perm.trans _ hp0
    apply Multiset.coe_eq_coe.mp
    change (P.toList : Multiset ℕ) + ({a + b - 1} + (Q.toList : Multiset ℕ)) +
      ({a - 1} + (T.toList : Multiset ℕ)) + {k - 1} =
      (P.toList : Multiset ℕ) + ({a + b - 1} + (T.toList : Multiset ℕ)) +
      ({a - 1} + (Q.toList : Multiset ℕ)) + {k - 1}
    ac_rfl
  have posP (i : ℕ) (hi : i ∈ P.toList) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := hPbound i (Finset.mem_toList.mp hi)
    exact hpositive i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have posT (i : ℕ) (hi : i ∈ T.toList) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := hTbound i (Finset.mem_toList.mp hi)
    exact hpositive i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have posQ (i : ℕ) (hi : i ∈ Q.toList) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hh := Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)
    have hi' := Finset.mem_range.mp hh.1
    have hne : i ≠ a - 1 ∧ i ≠ a + b - 1 ∧ i ≠ k - 1 := by
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hh
      tauto
    exact hpositive i hi' hne.1 hne.2.1 hne.2.2
  have hsum (A : Finset ℕ) (f : ℕ → ℤ) : (A.toList.map f).sum = ∑ i ∈ A, f i := by
    change ((A.toList : Multiset ℕ).map f).sum = _
    rw [Finset.coe_toList]
    rfl
  have sums (u w z : ℤ) (hu : 0 ≤ u ∧ u < R) (hw : 0 ≤ w ∧ w < S)
      (hz : 0 ≤ z ∧ z < R) :
      let A := packet a b u.toNat w.toNat z.toNat (boundU _ hu) (boundV _ hw) (boundU _ hz)
      (A.toList.map f).sum = u * v + w * B + z * L ∧
      (A.toList.map g).sum = u * (2 * v) + w * (2 * B - 1) + z * (2 * L - s - 1) := by
    dsimp only
    constructor
    · rw [hsum]
      rw [packet_sum a b _ _ _ ha hb _ _ _ f v B L
        (fun i hi => (hU i hi).1) (fun i hi => (hV i hi).1) (fun i hi => (hW i hi).1)]
      rw [castU u hu.1, castU w hw.1, castU z hz.1]
    · rw [hsum]
      rw [packet_sum a b _ _ _ ha hb _ _ _ g (2 * v) (2 * B - 1) (2 * L - s - 1)
        (fun i hi => (hU i hi).2) (fun i hi => (hV i hi).2) (fun i hi => (hW i hi).2)]
      rw [castU u hu.1, castU w hw.1, castU z hz.1]
  obtain ⟨hPf, hPg⟩ := sums c.pu c.pv c.pw hpu hpv hpw
  obtain ⟨hTf, hTg⟩ := sums c.tu c.tv c.tw htu htv htw
  change (P.toList.map f).sum = _ at hPf
  change (P.toList.map g).sum = _ at hPg
  change (T.toList.map f).sum = _ at hTf
  change (T.toList.map g).sum = _ at hTg
  have hm := c.good
  change margins R S c.pu c.pv c.pw c.tu c.tv c.tw at hm
  dsimp [margins] at hm
  have hmass :
      (Hb ≤ (P.toList.map f).sum ∧ (P.toList.map f).sum ≤ C) ∧
      ((T.toList.map f).sum ≤ Hg ∧ Ha + Hg - (T.toList.map f).sum ≤ C) ∧
      (Kb ≤ v + (P.toList.map g).sum ∧ v + (P.toList.map g).sum ≤ N) ∧
      ((T.toList.map g).sum ≤ Kg ∧ Ka + Kg - (T.toList.map g).sum ≤ N) := by
    rw [hPf, hPg, hTf, hTg]
    dsimp [v, B, L, C, Ha, Hb, Hg, Ka, Kb]
    rw [hr, hs]
    dsimp [Kg]
    rw [hN]
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> nlinarith only [hm.1, hm.2.1, hm.2.2.1,
        hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2]
  have hvNat : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = v := by
    push_cast; dsimp [v, r, s]; rw [pow_add]
  have hfzero : ((List.range k).map f).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero k (1 + 2 ^ a + 2 ^ (a + b)) (by dsimp [k]; omega)
    simpa only [hvNat] using hz
  have hgzero : ((List.range (k + 1)).map g).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by dsimp [k]; omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hvNat] using hz
  have hpnew : (k :: word).Perm (List.range (k + 1)) := by
    rw [List.range_succ]
    exact (hp.cons k).trans (by simpa using (List.perm_append_comm :
      ([k] ++ List.range k).Perm (List.range k ++ [k])))
  have oldStrip : InStrip f C 0 word := by
    have he := (hp.map f).sum_eq
    dsimp [word] at he
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, add_zero, hfA', hfB', hfG', hfzero] at he
    exact ThreeNegativeEqualOuterSourceBridge.physical_schedule f (List.range k) P.toList Q.toList T.toList
      (a + b - 1) (a - 1) (k - 1) Hb Ha Hg C hp hfB' hfA' hfG'
      hneg.1 hneg.2.1 ⟨hneg.2.2.1, hneg.2.2.2.1⟩
      (fun i hi => (posP i hi).1) (fun i hi => (posQ i hi).1) (fun i hi => (posT i hi).1)
      hmass.1 ⟨by omega, by omega⟩ hfzero
  have newStrip : InStrip g N 0 (k :: word) := by
    have he := (hpnew.map g).sum_eq
    dsimp [word] at he
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, add_zero, hgA', hgB', hgG', hgear, hgzero] at he
    change InStrip g N 0 ((k :: P.toList) ++ (a + b - 1) :: Q.toList ++ (a - 1) :: T.toList ++ [k - 1])
    apply ThreeNegativeEqualOuterSourceBridge.physical_schedule g (List.range (k + 1)) (k :: P.toList) Q.toList T.toList
      (a + b - 1) (a - 1) (k - 1) Kb Ka Kg N hpnew hgB' hgA' hgG'
      hneg.2.2.2.2.1 hneg.2.2.2.2.2.1 ⟨hneg.2.2.2.2.2.2.1, hneg.2.2.2.2.2.2.2⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hgear]; omega
      · exact (posP i hi).2
    · exact fun i hi => (posQ i hi).2
    · exact fun i hi => (posT i hi).2
    · simpa only [List.map_cons, List.sum_cons, hgear] using hmass.2.2.1
    · simp only [List.map_cons, List.sum_cons, hgear]
      exact ⟨by omega, by omega⟩
    · exact hgzero
  let sigma := word.map (label k (by dsimp [k]; omega))
  refine ⟨sigma, ?_, ?_⟩
  · apply lift_order k _ (by dsimp [k]; omega) word hp
    · simpa only [hvNat, hhalf] using oldStrip
    · simpa only [hvNat] using hfzero
  · have hear := marked_word k 0 (by dsimp [k]; omega) [] word (by simp) (by simpa using hp)
    simp only [List.nil_append] at hear
    rw [hear]
    apply lift_order (k + 1) _ (by omega) (k :: word) hpnew
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, hvNat, hnewhalf] using newStrip
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, hvNat] using hgzero

private theorem finite_order (k t : ℕ) (word : List (Fin k))
    (hp : word.Perm (List.finRange k))
    (hz : (word.map (actualSource k t)).sum = 0)
    (hs : ∀ n : Fin (k + 1), ((word.take n.val).map (actualSource k t)).sum ∈
      Set.Icc (0 : ℤ) (modulus k / 2)) : OriginalOrder k t word := by
  refine ⟨hp, hz, ?_⟩
  intro n
  by_cases hn : n ≤ k
  · exact hs ⟨n, by omega⟩
  · have hlen : word.length = k := by simpa using hp.length_eq
    simpa only [List.take_of_length_le (show word.length ≤ n by omega),
      List.take_of_length_le (show word.length ≤ k by omega)] using hs ⟨k, by omega⟩

private theorem base_three_two :
    ∃ sigma : List (Fin 8), OriginalOrder 8 41 sigma ∧
      OriginalOrder 9 82 (earWord 8 sigma 0) := by
  let sigma : List (Fin 8) := [3, 5, 4, 0, 6, 2, 1, 7]
  refine ⟨sigma, finite_order 8 41 sigma (by decide) (by decide) (by decide), ?_⟩
  exact finite_order 9 82 (earWord 8 sigma 0) (by decide) (by decide) (by decide)

private theorem base_four_two :
    ∃ sigma : List (Fin 10), OriginalOrder 10 81 sigma ∧
      OriginalOrder 11 162 (earWord 10 sigma 0) := by
  let sigma : List (Fin 10) := [1, 4, 3, 7, 8, 9, 0, 2, 6, 5]
  refine ⟨sigma, finite_order 10 81 sigma (by decide) (by decide) (by decide), ?_⟩
  exact finite_order 11 162 (earWord 10 sigma 0) (by decide) (by decide) (by decide)

set_option maxHeartbeats 4000000 in
-- The paired integer source and mask expressions require a larger elaboration budget.
/-- A complete physical permutation and its literal fresh-first ear for every
complementary equal-outer pair, including nonunit and repeated source values. -/
theorem actualSource_three_negative_equal_outer_first_ear_joint_lift (a b : ℕ)
    (hb : 2 ≤ b) (hab : b ≤ a) :
    ∃ sigma : List (Fin (a + b + a)),
      OriginalOrder (a + b + a) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + a + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + a) sigma 0) := by
  by_cases heq : a = b
  · subst a
    exact realize_choice b b hb (le_refl b)
      (equal_choice _ (by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ b - 1 by omega)))
  by_cases hb2 : b = 2
  · subst b
    by_cases ha3 : a = 3
    · subst a
      exact base_three_two
    by_cases ha4 : a = 4
    · subst a
      exact base_four_two
    have ha5 : 5 ≤ a := by omega
    apply realize_choice a 2 (by omega) hab
    norm_num
    exact small_choice _ (by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 4 ≤ a - 1 by omega))
  have hb3 : 3 ≤ b := by omega
  by_cases hadj : a = b + 1
  · let tau : ℤ := 2 ^ (b - 3)
    have ht : 1 ≤ tau := by
      dsimp [tau]
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (Nat.zero_le (b - 3))
    have hS : (2 : ℤ) ^ (b - 1) = 4 * tau := by
      rw [show b - 1 = (b - 3) + 2 by omega, pow_add]
      norm_num
      dsimp [tau]; ring
    have hR : (2 : ℤ) ^ (a - 1) = 8 * tau := by
      rw [show a - 1 = (b - 3) + 3 by omega, pow_add]
      norm_num
      dsimp [tau]; ring
    apply realize_choice a b hb hab
    rw [hR, hS]
    exact adjacent_choice (b - 1) tau ht (by rw [pow_succ, hS]; ring) hS.symm
  · let q : ℤ := 2 ^ (a - b)
    let R : ℤ := 2 ^ (a - 1)
    let S : ℤ := 2 ^ (b - 1)
    have hq : 4 ≤ q := by
      dsimp [q]
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 2 ≤ a - b by omega)
    have hS : 4 ≤ S := by
      dsimp [S]
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 2 ≤ b - 1 by omega)
    have hRS : R = q * S := by
      dsimp [R, q, S]
      rw [← pow_add]
      congr 1
      omega
    exact realize_choice a b hb hab (large_choice (a - 1) R S q hS hq hRS rfl)

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterFirstEarJointLift
