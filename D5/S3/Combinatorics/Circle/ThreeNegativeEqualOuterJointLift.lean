/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical gamma-beta-alpha schedule and its marked ear for equal outer gaps. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterSourceBridge
import D5.S3.Combinatorics.Circle.RunFirstEarTransport

/-! A common zero cut for the actual three-negative sources with equal outer gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

private theorem ladder_sum (f : ℕ → ℤ) (off len : ℕ) (A : ℤ)
    (hf : ∀ i < len, f (off + i) = (2 : ℤ) ^ i * A) :
    ((List.range' off len).map f).sum = (2 ^ len - 1) * A := by
  rw [List.range'_eq_map_range, List.map_map]
  have hm : (List.range len).map (fun i => f (off + i)) =
      (List.range len).map (fun i => (2 : ℤ) ^ i * A) := by
    apply List.map_congr_left
    intro i hi
    exact hf i (List.mem_range.mp hi)
  change ((List.range len).map (fun i => f (off + i))).sum = _
  rw [hm]
  clear hf hm
  induction len with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton, ih, pow_succ]
    ring

private theorem inventory (a b : ℕ) (ha : 2 ≤ a) (hab : a < b) :
    (List.range' (b - 1) a ++ (a + b + a - 1) ::
      List.range' (a + b) (a - 1) ++ (a + b - 1) ::
      (List.range (a - 1) ++ List.range' a (b - a - 1)) ++ [a - 1]).Perm
      (List.range (a + b + a)) := by
  let U := List.range (a - 1)
  let V := List.range' a (b - a - 1)
  let P := List.range' (b - 1) a
  let Q := List.range' (a + b) (a - 1)
  have hU : U ++ [a - 1] = List.range a := by
    simpa only [U, Nat.succ_eq_add_one, show (a - 1) + 1 = a by omega] using (List.range_succ (n := a - 1)).symm
  have hV : V ++ P = List.range' a (b - 1) := by
    dsimp [V, P]
    simpa only [show a + (b - a - 1) = b - 1 by omega,
      show b - a - 1 + a = b - 1 by omega] using
      List.range'_append_1 (s := a) (m := b - a - 1) (n := a)
  have hUV : (U ++ [a - 1]) ++ (V ++ P) = List.range (a + b - 1) := by
    rw [hU, hV]
    simp only [List.range_eq_range']
    simpa only [Nat.zero_add, show a + (b - 1) = a + b - 1 by omega] using
      List.range'_append_1 (s := 0) (m := a) (n := b - 1)
  have hB : List.range (a + b - 1) ++ [a + b - 1] = List.range (a + b) := by
    simpa only [Nat.succ_eq_add_one, show (a + b - 1) + 1 = a + b by omega] using (List.range_succ (n := a + b - 1)).symm
  have hQ : List.range (a + b) ++ Q = List.range (a + b + a - 1) := by
    dsimp [Q]
    simp only [List.range_eq_range']
    simpa only [Nat.zero_add, show a + b + (a - 1) = a + b + a - 1 by omega] using
      List.range'_append_1 (s := 0) (m := a + b) (n := a - 1)
  have hG : List.range (a + b + a - 1) ++ [a + b + a - 1] = List.range (a + b + a) := by
    simpa only [Nat.succ_eq_add_one, show (a + b + a - 1) + 1 = a + b + a by omega] using (List.range_succ (n := a + b + a - 1)).symm
  have hall : (((U ++ [a - 1]) ++ (V ++ P)) ++ [a + b - 1]) ++ Q ++
      [a + b + a - 1] = List.range (a + b + a) := by
    rw [hUV, hB, hQ, hG]
  have hx : (P ++ [a + b + a - 1] ++ Q ++ [a + b - 1] ++ U ++ V ++ [a - 1]).Perm
      ((((U ++ [a - 1]) ++ (V ++ P)) ++ [a + b - 1]) ++ Q ++ [a + b + a - 1]) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  rw [hall] at hx
  simpa only [P, Q, U, V, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hx


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


private theorem paired_chains (a b : ℕ) (ha : 2 ≤ a) (hab : a < b) :
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

private theorem schedule_from_tail (f : ℕ → ℤ) (labels P Q T : List ℕ)
    (gamma beta alpha : ℕ) (Hg Hb Ha C : ℤ)
    (hp : (P ++ gamma :: Q ++ beta :: T ++ [alpha]).Perm labels)
    (hg : f gamma = -Hg) (hb : f beta = -Hb) (ha : f alpha = -Ha)
    (hHg : 0 ≤ Hg) (hHb : 0 ≤ Hb) (hHa : 0 ≤ Ha ∧ Ha ≤ C)
    (hP : ∀ i ∈ P, 0 ≤ f i) (hQ : ∀ i ∈ Q, 0 ≤ f i)
    (hT : ∀ i ∈ T, 0 ≤ f i)
    (hfirst : Hg ≤ (P.map f).sum ∧ (P.map f).sum ≤ C)
    (htail : (T.map f).sum ≤ Ha ∧ Hb + Ha - (T.map f).sum ≤ C)
    (hz : (labels.map f).sum = 0) :
    InStrip f C 0 (P ++ gamma :: Q ++ beta :: T ++ [alpha]) := by
  have he := (hp.map f).sum_eq
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, add_zero, hg, hb, ha, hz] at he
  exact ThreeNegativeEqualOuterSourceBridge.physical_schedule f labels P Q T
    gamma beta alpha Hg Hb Ha C
    hp hg hb ha hHg hHb hHa hP hQ hT hfirst ⟨by omega, by omega⟩ hz

set_option maxHeartbeats 4000000 in
/-- One physical order and its literal ear at cut a+1 work for every equal-outer
three-negative source with a>=2 and b>a, including b=a+1. -/
theorem actualSource_three_negative_equal_outer_joint_lift (a b : ℕ)
    (ha : 2 ≤ a) (hab : a < b) :
    ∃ sigma : List (Fin (a + b + a)),
      OriginalOrder (a + b + a) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + a + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + a) sigma (a + 1)) := by
  let k := a + b + a
  let m := b - a - 1
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let q : ℤ := 2 ^ (a - 1)
  let tau : ℤ := 2 ^ m
  let N := modulus k
  let C := r ^ 3 * tau - 1
  let v := 1 + r + r * s
  let B := 1 + r + r * r
  let L := 1 + s + s * r
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
  let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * v))
  let P := List.range' (b - 1) a
  let Q := List.range' (a + b) (a - 1)
  let T := List.range (a - 1) ++ List.range' a m
  let word := P ++ (k - 1) :: Q ++ (a + b - 1) :: T ++ [a - 1]
  let plus := P ++ (k - 1) :: k :: Q ++ (a + b - 1) :: T ++ [a - 1]
  have hr : 4 ≤ r := by
    simpa [r] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
  have hq : r = 2 * q := by
    calc
      r = (2 : ℤ) ^ ((a - 1) + 1) := by dsimp [r]; congr 1; omega
      _ = 2 * q := by rw [pow_succ]; dsimp [q]; ring
  have hq0 : 2 ≤ q := by omega
  have htau : 1 ≤ tau := by
    dsimp [tau]
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (Nat.zero_le m)
  have hs : s = 2 * r * tau := by
    dsimp [s, r, tau]
    rw [show b = a + 1 + m by dsimp [m]; omega, pow_add, pow_add]
    norm_num
    ring
  have hN : N = 2 * (r ^ 3 * tau) - 1 := by
    dsimp [N, k, modulus]
    rw [pow_add, pow_add]
    change r * s * r - 1 = _
    rw [hs]; ring
  have hNC : N = 2 * C + 1 := by dsimp [C]; omega
  have hhalf : modulus k / 2 = C := by change N / 2 = C; omega
  have hnewhalf : modulus (k + 1) / 2 = N := by
    have hm : modulus (k + 1) = 2 * N + 1 := by
      dsimp [modulus, N]; rw [pow_succ]; ring
    omega
  obtain ⟨hv, hB, hL, hU, hV, hW, hfA, hfB, hfG, hgA, hgB, hgG, hgear⟩ :=
    paired_chains a b ha hab
  change (1 ≤ v ∧ v < N) at hv
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ i < a - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v) at hU
  change ∀ i < b - 1, f (a + i) = (2 : ℤ) ^ i * B ∧ g (a + i) = (2 : ℤ) ^ i * (2 * B - 1) at hV
  change ∀ i < a - 1, f (a + b + i) = (2 : ℤ) ^ i * L ∧
    g (a + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1) at hW
  change f (a - 1) = -(N - B) / 2 at hfA
  change f (a + b - 1) = -(N - L) / 2 at hfB
  change f (k - 1) = -(N - v) / 2 at hfG
  change g (a - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 at hgA
  change g (a + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 at hgB
  change g (k - 1) = -((2 * N + 1) - v) / 2 at hgG
  change g k = v at hgear
  let Ha := r ^ 3 * tau - r * q - q - 1
  let Hb := r ^ 3 * tau - r * (r + 1) * tau - 1
  let Hg := r ^ 3 * tau - r ^ 2 * tau - q - 1
  let Ka := 2 * Ha + 1
  let Kb := 2 * Hb + r * tau + 1
  let Kg := 2 * Hg + r ^ 2 * tau + q + 1
  have hHa : 2 * Ha = N - B := by
    rw [hN]; dsimp [Ha, B]; rw [hq]; ring
  have hHb : 2 * Hb = N - L := by
    rw [hN]; dsimp [Hb, L]; rw [hs]; ring
  have hHg : 2 * Hg = N - v := by
    rw [hN]; dsimp [Hg, v]; rw [hs, hq]; ring
  have hKa : 2 * Ka = (2 * N + 1) - (2 * B - 1) := by dsimp [Ka]; omega
  have hKb : 2 * Kb = (2 * N + 1) - (2 * L - s - 1) := by
    dsimp [Kb]; rw [hs]; nlinarith only [hHb]
  have hKg : 2 * Kg = (2 * N + 1) - v := by
    rw [hN]; dsimp [Kg, Hg, v]; rw [hs, hq]; ring
  have hfA' : f (a - 1) = -Ha := by rw [hfA]; omega
  have hfB' : f (a + b - 1) = -Hb := by rw [hfB]; omega
  have hfG' : f (k - 1) = -Hg := by rw [hfG]; omega
  have hgA' : g (a - 1) = -Ka := by rw [hgA]; omega
  have hgB' : g (a + b - 1) = -Kb := by rw [hgB]; omega
  have hgG' : g (k - 1) = -Kg := by rw [hgG]; omega
  have hHa0 : 0 ≤ Ha := by omega
  have hHb0 : 0 ≤ Hb := by omega
  have hHg0 : 0 ≤ Hg := by omega
  have hHaC : Ha ≤ C := by omega
  have hKa0 : 0 ≤ Ka := by dsimp [Ka]; omega
  have hKaN : Ka ≤ N := by dsimp [Ka]; omega
  have hKb0 : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hKg0 : 0 ≤ Kg := by dsimp [Kg]; positivity
  let p := (r - 1) * tau * B
  let pn := (r - 1) * tau * (2 * B - 1)
  let t := (q - 1) * v + (tau - 1) * B
  let tn := (q - 1) * (2 * v) + (tau - 1) * (2 * B - 1)
  have hrho : 0 ≤ r ^ 2 - r - 1 := by
    have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ r by omega)
    nlinarith only [hm, hr]
  have hprod : 0 ≤ (r ^ 2 - r - 1) * tau := mul_nonneg hrho (by omega)
  have hpC : C - p = tau - 1 := by dsimp [C, p, B]; ring
  have hpG : p - Hg = (r ^ 2 - 1) * tau + q + 1 := by
    dsimp [p, Hg, B]; ring
  have hpnG : pn - Kg = (r ^ 2 - r - 1) * tau + q + 1 := by
    dsimp [pn, Kg, Hg, B]; ring
  have htp : Ha - t = (r ^ 2 - r - 1) * tau + r + 1 := by
    dsimp [Ha, t, v, B]; rw [hs, hq]; ring
  have htq : C - (Hb + Ha - t) = (2 * r + 1) * tau - r - 1 := by
    dsimp [C, Hb, Ha, t, v, B]; rw [hs, hq]; ring
  have htnq : N - (Kb + Ka - tn) = (3 * r + 1) * tau - 2 * r - 2 := by
    rw [hN]; dsimp [Kb, Ka, Hb, Ha, tn, v, B]; rw [hs, hq]; ring
  have hpn : 2 * p - pn = (r - 1) * tau := by dsimp [p, pn]; ring
  have htn : 2 * t - tn = tau - 1 := by dsimp [t, tn]; ring
  have hpfirst : Hg ≤ p ∧ p ≤ C := by
    have hnon : 0 ≤ (r ^ 2 - 1) * tau := mul_nonneg (by nlinarith only [hrho, hr]) (by omega)
    constructor <;> omega
  have htlast : t ≤ Ha ∧ Hb + Ha - t ≤ C := by
    have hnon := mul_le_mul_of_nonneg_left htau (show 0 ≤ 2 * r + 1 by omega)
    constructor <;> omega
  have hpnfirst : Kg ≤ pn ∧ pn ≤ N := by
    have hnon : 0 ≤ (r - 1) * tau := mul_nonneg (by omega) (by omega)
    constructor <;> omega
  have htnlast : tn ≤ Ka ∧ Kb + Ka - tn ≤ N := by
    have hnon := mul_le_mul_of_nonneg_left htau (show 0 ≤ 3 * r + 1 by omega)
    dsimp only [Ka]
    constructor <;> omega
  have hBdouble : 0 ≤ 2 * B - 1 := by omega
  have hPpos : ∀ i ∈ P, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hi' := List.mem_range'.mp hi
    have he : i = a + (i - a) := by omega
    obtain ⟨hf, hg⟩ := hV (i - a) (by omega)
    rw [he, hf, hg]
    constructor <;> positivity
  have hQpos : ∀ i ∈ Q, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hi' := List.mem_range'.mp hi
    have he : i = a + b + (i - (a + b)) := by omega
    obtain ⟨hf, hg⟩ := hW (i - (a + b)) (by omega)
    have hbase : 0 ≤ 2 * L - s - 1 := by
      have heq : 2 * L - s - 1 = s * (2 * r + 1) + 1 := by dsimp [L]; ring
      rw [heq]
      have hs0 : 0 ≤ s := by dsimp [s]; positivity
      positivity
    rw [he, hf, hg]
    constructor <;> positivity
  have hTpos : ∀ i ∈ T, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨hf, hg⟩ := hU i (List.mem_range.mp hi)
      rw [hf, hg]; constructor <;> positivity
    · have hi' := List.mem_range'.mp hi
      have he : i = a + (i - a) := by omega
      obtain ⟨hf, hg⟩ := hV (i - a) (by dsimp [m] at hi'; omega)
      rw [he, hf, hg]; constructor <;> positivity
  have hPsum : (P.map f).sum = p ∧ (P.map g).sum = pn := by
    have ho : a + m = b - 1 := by dsimp [m]; omega
    have hl : m + a = b - 1 := by dsimp [m]; omega
    have hF (i : ℕ) (hi : i < a) : f (b - 1 + i) = (2 : ℤ) ^ i * (tau * B) := by
      rw [show b - 1 + i = a + (m + i) by omega, (hV (m + i) (by omega)).1]
      dsimp [tau]; rw [pow_add]; ring
    have hG (i : ℕ) (hi : i < a) : g (b - 1 + i) = (2 : ℤ) ^ i * (tau * (2 * B - 1)) := by
      rw [show b - 1 + i = a + (m + i) by omega, (hV (m + i) (by omega)).2]
      dsimp [tau]; rw [pow_add]; ring
    constructor
    · rw [show (P.map f).sum = (2 ^ a - 1) * (tau * B) from ladder_sum f (b - 1) a _ hF]
      dsimp [p, r]; ring
    · rw [show (P.map g).sum = (2 ^ a - 1) * (tau * (2 * B - 1)) from ladder_sum g (b - 1) a _ hG]
      dsimp [pn, r]; ring
  have hTsum : (T.map f).sum = t ∧ (T.map g).sum = tn := by
    have hUF := ladder_sum f 0 (a - 1) v (fun i hi => by simpa using (hU i hi).1)
    have hUG := ladder_sum g 0 (a - 1) (2 * v) (fun i hi => by simpa using (hU i hi).2)
    have hVF := ladder_sum f a m B (fun i hi => (hV i (by dsimp [m] at hi; omega)).1)
    have hVG := ladder_sum g a m (2 * B - 1) (fun i hi => (hV i (by dsimp [m] at hi; omega)).2)
    simp only [← List.range_eq_range'] at hUF hUG
    constructor
    · simpa only [T, List.map_append, List.sum_append, hUF, hVF] using
        (show (2 ^ (a - 1) - 1) * v + (2 ^ m - 1) * B = t by rfl)
    · simpa only [T, List.map_append, List.sum_append, hUG, hVG] using
        (show (2 ^ (a - 1) - 1) * (2 * v) + (2 ^ m - 1) * (2 * B - 1) = tn by rfl)
  have hp : word.Perm (List.range k) := inventory a b ha hab
  have hplus : plus.Perm (List.range (k + 1)) := by
    have he : plus.Perm (word ++ [k]) := by
      have he' : (P ++ [k - 1] ++ [k] ++ Q ++ [a + b - 1] ++ T ++ [a - 1]).Perm
          ((P ++ [k - 1] ++ Q ++ [a + b - 1] ++ T ++ [a - 1]) ++ [k]) := by
        apply Multiset.coe_eq_coe.mp
        simp only [← Multiset.coe_add]
        ac_rfl
      simpa only [plus, word, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using he'

    exact he.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have hseed : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = v := by
    push_cast; dsimp [v, r, s]; rw [pow_add]
  have hzero : ((List.range k).map f).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero k (1 + 2 ^ a + 2 ^ (a + b)) (by dsimp [k]; omega)
    simpa only [hseed] using hz
  have hzero' : ((List.range (k + 1)).map g).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by dsimp [k]; omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed] using hz
  have hold : InStrip f C 0 word := schedule_from_tail f (List.range k) P Q T
    (k - 1) (a + b - 1) (a - 1) Hg Hb Ha C hp hfG' hfB' hfA'
    hHg0 hHb0 ⟨hHa0, hHaC⟩ (fun i hi => (hPpos i hi).1)
    (fun i hi => (hQpos i hi).1) (fun i hi => (hTpos i hi).1)
    (by simpa only [hPsum.1] using hpfirst) (by simpa only [hTsum.1] using htlast) hzero
  have hnew : InStrip g N 0 plus := schedule_from_tail g (List.range (k + 1)) P (k :: Q) T
    (k - 1) (a + b - 1) (a - 1) Kg Kb Ka N hplus hgG' hgB' hgA'
    hKg0 hKb0 ⟨hKa0, hKaN⟩ (fun i hi => (hPpos i hi).2)
    (by intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · rw [hgear]; omega
        · exact (hQpos i hi).2)
    (fun i hi => (hTpos i hi).2)
    (by simpa only [hPsum.2] using hpnfirst) (by simpa only [hTsum.2] using htnlast) hzero'
  have hk : 0 < k := by dsimp [k]; omega
  refine ⟨word.map (label k hk), ?_, ?_⟩
  · refine lift_order k (1 + 2 ^ a + 2 ^ (a + b)) hk word hp ?_ ?_
    · simpa only [hseed, hhalf] using hold
    · simpa only [hseed] using hzero
  · have he : earWord k (word.map (label k hk)) (a + 1) =
        plus.map (label (k + 1) (by omega)) := by
      have hpre : (P ++ [k - 1]).length = a + 1 := by simp [P]
      have hword : (P ++ [k - 1]) ++ (Q ++ (a + b - 1) :: T ++ [a - 1]) = word := by
        simp only [word, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      have hplusword : (P ++ [k - 1]) ++ k :: (Q ++ (a + b - 1) :: T ++ [a - 1]) = plus := by
        simp only [plus, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      simpa only [hword, hplusword] using marked_word k (a + 1) hk
        (P ++ [k - 1]) (Q ++ (a + b - 1) :: T ++ [a - 1]) hpre (by rw [hword]; exact hp)
    rw [he]
    refine lift_order (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by omega) plus hplus ?_ ?_
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed, hnewhalf] using hnew
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed] using hzero'

#print axioms actualSource_three_negative_equal_outer_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
