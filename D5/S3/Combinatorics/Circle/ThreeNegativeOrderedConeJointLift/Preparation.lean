/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Private chain, schedule and charge preparation for the ordered-cone joint lift. -/
import D5.S3.Combinatorics.Circle.ThreeBitSource
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegative.EqualOuterJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private label lift_order marked_word from
  D5.S3.Combinatorics.Circle.ThreeNegative.EqualOuterJointLift
open private mask_labels mask_labels_bound mask_labels_sum labelled_permutation from
  D5.S3.Combinatorics.Circle.ThreeBitSource

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
    (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
    (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧
      g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
    (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
      g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
    f (c - 1) = -(N - B) / 2 ∧
    f (c + b - 1) = -(N - L) / 2 ∧
    f (k - 1) = -(N - v) / 2 ∧
    g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
    g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
    g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v := by
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
  change (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
    (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧
      g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
    (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
      g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
    f (c - 1) = -(N - B) / 2 ∧ f (c + b - 1) = -(N - L) / 2 ∧
    f (k - 1) = -(N - v) / 2 ∧
    g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
    g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
    g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v
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


private theorem positive_block_strip {α : Type*} {f : α → ℤ} {C h : ℤ} {l : List α}
    (hp : ∀ i ∈ l, 0 ≤ f i) (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ C) :
    InStrip f C h l := by
  apply inStrip_reflect
  apply inStrip_nonpos
  · intro i hi
    have := hp i hi
    omega
  · omega
  · rw [sum_neg_map]
    omega

private theorem list_map_cons_sum {α : Type*} (f : α → ℤ) (x : α) (l : List α) :
    ((x :: l).map f).sum = f x + (l.map f).sum := by
  rfl

private theorem int_half_two_mul (p : ℤ) : (2 * p) / 2 = p := by
  exact Int.mul_ediv_cancel_left p (by norm_num)

private theorem fresh_prefix_sum_bridge {α : Type*} (f : α → ℤ)
    (P Q : List α) (fresh : α) (base freshVal A : ℤ)
    (hP : (P.map f).sum = base) (hfresh : f fresh = freshVal) :
    (P.map f).sum - A + ((fresh :: Q).map f).sum =
      base - A + freshVal + (Q.map f).sum := by
  rw [hP, list_map_cons_sum, hfresh]
  exact (add_assoc _ _ _).symm

private theorem fresh_prefix_bounds {α : Type*} (f : α → ℤ)
    (P Q : List α) (fresh : α) (base freshVal A C : ℤ)
    (hP : (P.map f).sum = base) (hfresh : f fresh = freshVal)
    (hbound : 0 ≤ base - A + freshVal + (Q.map f).sum ∧
      base - A + freshVal + (Q.map f).sum ≤ C) :
    0 ≤ (P.map f).sum - A + ((fresh :: Q).map f).sum ∧
      (P.map f).sum - A + ((fresh :: Q).map f).sum ≤ C := by
  rw [fresh_prefix_sum_bridge f P Q fresh base freshVal A hP hfresh]
  exact hbound

private theorem fresh_prefix_bounds_sub {α : Type*} (f : α → ℤ)
    (P Q : List α) (fresh : α) (base freshVal A B C : ℤ)
    (hP : (P.map f).sum = base) (hfresh : f fresh = freshVal)
    (hbound : 0 ≤ base - A + freshVal + (Q.map f).sum - B ∧
      base - A + freshVal + (Q.map f).sum - B ≤ C) :
    0 ≤ (P.map f).sum - A + ((fresh :: Q).map f).sum - B ∧
      (P.map f).sum - A + ((fresh :: Q).map f).sum - B ≤ C := by
  have hEq := fresh_prefix_sum_bridge f P Q fresh base freshVal A hP hfresh
  rw [hEq]
  exact hbound

private theorem add_bound_of_eq {D K X C : ℤ} (hD : D ≤ X) (hX : X + K = C) :
    D + K ≤ C := by omega

private theorem ordered_schedule {α : Type*} (f : α → ℤ) (labels P Q T : List α)
    (alpha beta gamma : α) (Ha Hb Hg C : ℤ)
    (hperm : (P ++ alpha :: Q ++ beta :: T ++ [gamma]).Perm labels)
    (halpha : f alpha = -Ha) (hbeta : f beta = -Hb) (hgamma : f gamma = -Hg)
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) (hHg : 0 ≤ Hg ∧ Hg ≤ C)
    (hPpos : ∀ i ∈ P, 0 ≤ f i) (hQpos : ∀ i ∈ Q, 0 ≤ f i)
    (hTpos : ∀ i ∈ T, 0 ≤ f i)
    (hPmass : 0 ≤ (P.map f).sum ∧ (P.map f).sum ≤ C)
    (hAlpha : 0 ≤ (P.map f).sum - Ha ∧ (P.map f).sum - Ha ≤ C)
    (hQend : 0 ≤ (P.map f).sum - Ha + (Q.map f).sum ∧
      (P.map f).sum - Ha + (Q.map f).sum ≤ C)
    (hBeta : 0 ≤ (P.map f).sum - Ha + (Q.map f).sum - Hb ∧
      (P.map f).sum - Ha + (Q.map f).sum - Hb ≤ C)
    (htotal : (labels.map f).sum = 0) :
    InStrip f C 0 (P ++ alpha :: Q ++ beta :: T ++ [gamma]) := by
  have hs := (hperm.map f).sum_eq
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, add_zero, halpha, hbeta, hgamma, htotal] at hs
  have htail : (P.map f).sum - Ha + (Q.map f).sum - Hb + (T.map f).sum = Hg := by
    omega
  have hT : InStrip f C ((P.map f).sum - Ha + (Q.map f).sum - Hb) T :=
    positive_block_strip hTpos (by omega) (by omega)
  have hT' : InStrip f C ((P.map f).sum - Ha + (Q.map f).sum - Hb)
      (T ++ [gamma]) := by
    apply inStrip_append hT
    simp only [InStrip, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      hgamma]
    omega
  have hQ : InStrip f C ((P.map f).sum - Ha) Q :=
    positive_block_strip hQpos (by omega) hQend.2
  have hQ' : InStrip f C ((P.map f).sum - Ha)
      (Q ++ beta :: (T ++ [gamma])) := by
    apply inStrip_append (l := Q) (r := beta :: (T ++ [gamma])) hQ
    change 0 ≤ (P.map f).sum - Ha + (Q.map f).sum ∧
      (P.map f).sum - Ha + (Q.map f).sum ≤ C ∧ _
    refine ⟨hQend.1, hQend.2, ?_⟩
    simpa only [hbeta, ← sub_eq_add_neg, List.append_assoc] using hT'
  have hP : InStrip f C 0 P := positive_block_strip hPpos (by omega) (by simpa using hPmass.2)
  have hrest : InStrip f C ((P.map f).sum)
      (alpha :: (Q ++ (beta :: (T ++ [gamma])))) := by
    change 0 ≤ (P.map f).sum ∧ (P.map f).sum ≤ C ∧ _
    refine ⟨hPmass.1, hPmass.2, ?_⟩
    simpa only [halpha, ← sub_eq_add_neg] using hQ'
  have hrest0 : InStrip f C (0 + (P.map f).sum)
      (alpha :: (Q ++ (beta :: (T ++ [gamma])))) := by
    simpa only [zero_add] using hrest
  have hstrip :=
    inStrip_append (l := P) (r := alpha :: (Q ++ (beta :: (T ++ [gamma])))) hP hrest0
  have hlist : P ++ (alpha :: (Q ++ (beta :: (T ++ [gamma])))) =
      P ++ alpha :: Q ++ beta :: T ++ [gamma] := by
    simp only [List.cons_append, List.append_assoc]
  rw [hlist] at hstrip
  exact hstrip

private theorem floor_tail_bound (x d rem v : ℤ)
    (h : x = rem + d * v) (hrem : rem < d) : x - d ≤ d * v := by
  omega

private theorem mul_le_mul_left_int {a b c : ℤ} (h : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  exact mul_le_mul_of_nonneg_left h hc

private theorem beta_block_bound (r p t : ℤ) (hrp : r + 1 ≤ p) (ht0 : 0 ≤ t)
    (hp1 : 1 ≤ p) : 1 + t + t * r ≤ p * (t + 1) := by
  have hmul : t * (r + 1) ≤ t * p :=
    mul_le_mul_left_int hrp ht0
  calc
    1 + t + t * r = 1 + t * (r + 1) := by ring
    _ ≤ 1 + t * p := by omega
    _ = 1 + p * t := by rw [mul_comm t p]
    _ ≤ p + p * t := by omega
    _ = p * (t + 1) := by ring

private theorem one_le_of_add_one_le {r p : ℤ} (hr : 0 ≤ r) (h : r + 1 ≤ p) :
    1 ≤ p := by
  omega

private theorem floor_tail_bound_mul (L u B rem v : ℤ)
    (h : L - u = rem + B * v) (hrem : rem < B) :
    L - u - B ≤ B * v := by
  have h' := floor_tail_bound (x := L - u) (d := B) (rem := rem) (v := v) h hrem
  exact h'

private theorem core_from_floor (L u B rem v p r s t : ℤ)
    (h : L - u = rem + B * v) (hrem : rem < B)
    (hLB : p * (t + 1) - r * (s + 1) ≤ L - u - B) :
    0 ≤ v * B + r * (s + 1) - p * (t + 1) := by
  have hfloor := floor_tail_bound_mul L u B rem v h hrem
  linarith only [hLB, hfloor]

private theorem new_margin_bounds (q s r t N : ℤ) (hq : 1 ≤ q)
    (hsr : 0 ≤ s - r - 1) (hr : 4 ≤ r) (hs : 4 ≤ s)
    (htq : t = q * s) (hN : N = r * s * t - 1) :
    0 ≤ 2 * (1 + q * (s - r - 1)) - 1 ∧
      2 * (1 + q * (s - r - 1)) - 1 ≤ N := by
  have hq0 : 0 ≤ q := by omega
  have hqs0 : 0 ≤ q * s := mul_nonneg hq0 (by omega)
  have h2 : 2 ≤ r * s := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right h2 hqs0
  rw [htq] at hN
  constructor
  · nlinarith
  · nlinarith [hmul]

private theorem cone_length_old (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b)
    (hbc : b ≤ c) : 3 ≤ a + b + c := by
  omega

private theorem cone_length_new (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b)
    (hbc : b ≤ c) : 3 ≤ a + b + c + 1 := by
  omega

private theorem split_sum_zero {α : Type*} (f : α → ℤ)
    (P Q T : List α) (alpha beta gamma : α)
    (x y Ha Hb Hg : ℤ)
    (hP : (P.map f).sum = x) (hT : (T.map f).sum = y)
    (hα : f alpha = -Ha) (hβ : f beta = -Hb) (hγ : f gamma = -Hg)
    (hzero : ((P ++ alpha :: Q ++ beta :: T ++ [gamma]).map f).sum = 0) :
    x + (-Ha + (Q.map f).sum) + (-Hb + y) + -Hg = 0 := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, add_zero, hP, hT, hα, hβ, hγ] at hzero
  linarith only [hzero]

private theorem old_beta_bounds (x Ha qsum Hb y Hg C : ℤ)
    (hsum : x + (-Ha + qsum) + (-Hb + y) + -Hg = 0)
    (hdelta0 : 0 ≤ Hg - y) (hdeltaC : Hg - y ≤ C) :
    0 ≤ x - Ha + qsum - Hb ∧ x - Ha + qsum - Hb ≤ C := by
  have hrel : x - Ha + qsum - Hb = Hg - y := by
    linarith only [hsum]
  rw [hrel]
  exact ⟨hdelta0, hdeltaC⟩

private theorem nat_cast_nonneg_mul (u : ℤ) (m : ℕ) (hu : 0 ≤ u) :
    0 ≤ u * (m : ℤ) := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.zero_le m)
  exact mul_nonneg hu hm

private theorem doubled_source_zero_cast (n t : ℕ) (u : ℤ) (hn : 3 ≤ n)
    (ht : (t : ℤ) = u) :
    ((List.range n).map
      (fun i => centered (modulus n) ((2 : ℤ) ^ i * (2 * u)))).sum = 0 := by
  have hz := ThreeNegativeEqualOuterSourceBridge.source_zero n (2 * t) hn
  have htu : ((2 * t : ℕ) : ℤ) = (2 : ℤ) * u := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ht]
  rw [htu] at hz
  exact hz

end D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift
