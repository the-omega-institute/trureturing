/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A physical floor-mask joint constructor for the ordered cone 2 <= a < b <= c. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift.Preparation
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

open private
  paired_chains positive_block_strip list_map_cons_sum
  int_half_two_mul fresh_prefix_sum_bridge fresh_prefix_bounds
  fresh_prefix_bounds_sub add_bound_of_eq ordered_schedule
  floor_tail_bound mul_le_mul_left_int beta_block_bound
  one_le_of_add_one_le floor_tail_bound_mul core_from_floor
  new_margin_bounds cone_length_old cone_length_new
  split_sum_zero old_beta_bounds nat_cast_nonneg_mul
  doubled_source_zero_cast
  from D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift.Preparation

set_option maxHeartbeats 10000000 in
/-- The full ordered cone 2 <= a < b <= c has one physical joint permutation and
one literal ear, with the ear selected by the exact beta charge. -/
theorem actualSource_three_negative_ordered_cone_joint_lift (a b c : ℕ)
    (ha : 2 ≤ a) (hab : a < b) (hbc : b ≤ c) :
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ,
      j ≤ a + b + c ∧
      OriginalOrder (a + b + c) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + c + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + c) sigma j) := by
  classical
  let k := a + b + c
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let t : ℤ := 2 ^ c
  let q : ℤ := 2 ^ (c - b)
  let p : ℤ := 2 ^ (b - 1)
  let ah : ℤ := 2 ^ (a - 1)
  let N := modulus k
  let C := ah * s * t - 1
  let u := 1 + r + r * s
  let B := 1 + t + t * r
  let L := 1 + s + s * t
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
  let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * u))
  have hr : 4 ≤ r := by
    simpa [r] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
  have hs : 4 ≤ s := by
    simpa [s] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : 2 ≤ b)
  have hp_bound : 2 ≤ p := by
    simpa [p] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : 1 ≤ b - 1)
  have hq : 1 ≤ q := by
    have : (0 : ℤ) < q := by dsimp [q]; positivity
    omega
  have hqpow : q * p = 2 ^ (c - 1) := by
    dsimp [q, p]
    rw [← pow_add]
    congr 1
    omega
  have hrhalf : r = 2 * ah := by
    dsimp only [r, ah]
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hrdiv : r / 2 = ah := by rw [hrhalf]; omega
  have hsp : s = 2 * p := by
    dsimp only [s, p]
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  have huHalf : (u + 1) / 2 = 1 + ah * (s + 1) := by
    have hh : u + 1 = 2 * (1 + ah * (s + 1)) := by
      dsimp [u]
      rw [hrhalf]
      ring
    rw [hh]
    omega
  have htq : t = q * s := by
    dsimp [t, q, s]
    rw [← pow_add]
    congr 1
    omega
  have hrp : r ≤ p := by
    dsimp [r, p]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
  have htr : 2 * r ≤ t := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + 1 ≤ c by omega)
    simpa only [pow_succ, r, t, mul_comm] using hh
  have hN : N = r * s * t - 1 := by
    dsimp [N, modulus, k, r, s, t]
    rw [pow_add, pow_add]
  have hC : 2 * C = N - 1 := by rw [hN, hrhalf]; dsimp [C]; ring
  have hhalf : modulus k / 2 = C := by
    change N / 2 = C
    omega
  have hnewhalf : modulus (k + 1) / 2 = N := by
    have hm : modulus (k + 1) = 2 * N + 1 := by
      dsimp [modulus, N]; rw [pow_succ]; ring
    omega
  have hseed : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = u := by
    push_cast
    dsimp [u, r, s]
    rw [pow_add]
  have hzero : ((List.range k).map f).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero k
      (1 + 2 ^ a + 2 ^ (a + b)) (by simpa [k] using cone_length_old a b c ha hab hbc)
    simpa only [hseed] using hz
  have hzero' : ((List.range (k + 1)).map g).sum = 0 := by
    change ((List.range (k + 1)).map
      (fun i => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * u)))).sum = 0
    have hknew : 3 ≤ k + 1 := by
      simpa only [k] using cone_length_new a b c ha hab hbc
    exact doubled_source_zero_cast (k + 1) (1 + 2 ^ a + 2 ^ (a + b)) u hknew hseed
  obtain ⟨hu, hB, hL, hU, hV, hW, hfA, hfB, hfG, hgA, hgB, hgG, hgear⟩ :=
    paired_chains a b c (by omega) (by omega) (by omega)
  change (1 ≤ u ∧ u < N) at hu
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ i < c - 1, f i = (2 : ℤ) ^ i * u ∧ g i = (2 : ℤ) ^ i * (2 * u) at hU
  change ∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧ g (c + i) = (2 : ℤ) ^ i * (2 * B - 1) at hV
  change ∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
    g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1) at hW
  change f (c - 1) = -(N - B) / 2 at hfA
  change f (c + b - 1) = -(N - L) / 2 at hfB
  change f (k - 1) = -(N - u) / 2 at hfG
  change g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 at hgA
  change g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 at hgB
  change g (k - 1) = -((2 * N + 1) - u) / 2 at hgG
  change g k = u at hgear
  let Ha := C - q * p * (r + 1)
  let Hb := C - p * (t + 1)
  let Hg := C - ah * (s + 1)
  let Ka := 2 * Ha + 1
  let Kb := 2 * Hb + s / 2 + 1
  let Kg := 2 * Hg + (u + 1) / 2
  have hHa : 2 * Ha = N - B := by
    dsimp [Ha, C, B]
    rw [hN, htq, hsp, hrhalf]
    ring
  have hHb : 2 * Hb = N - L := by
    dsimp [Hb, C, L]
    rw [hN, hsp, hrhalf]
    ring
  have hHg : 2 * Hg = N - u := by
    dsimp [Hg, C, u]
    rw [hN, hrhalf]
    ring
  have hKa : 2 * Ka = (2 * N + 1) - (2 * B - 1) := by dsimp [Ka]; omega
  have hKb : 2 * Kb = (2 * N + 1) - (2 * L - s - 1) := by dsimp [Kb]; omega
  have hKg : 2 * Kg = (2 * N + 1) - u := by
    dsimp [Kg]
    rw [huHalf]
    omega
  have hfA' : f (c - 1) = -Ha := by rw [hfA]; omega
  have hfB' : f (c + b - 1) = -Hb := by rw [hfB]; omega
  have hfG' : f (k - 1) = -Hg := by rw [hfG]; omega
  have hgA' : g (c - 1) = -Ka := by rw [hgA]; omega
  have hgB' : g (c + b - 1) = -Kb := by rw [hgB]; omega
  have hgG' : g (k - 1) = -Kg := by rw [hgG]; omega
  have hHa0 : 0 ≤ Ha := by
    have hNB : 0 ≤ N - B := by omega
    omega
  have hHb0 : 0 ≤ Hb := by
    have hNL : 0 ≤ N - L := by omega
    omega
  have hHg0 : 0 ≤ Hg := by
    have hNu : 0 ≤ N - u := by omega
    omega
  have hHgC : Hg ≤ C := by
    have hu1 : 1 ≤ u := hu.1
    omega
  have hKa0 : 0 ≤ Ka := by dsimp [Ka]; omega
  have hKb0 : 0 ≤ Kb := by dsimp [Kb]; omega
  have hKg0 : 0 ≤ Kg := by dsimp [Kg]; omega
  have hKgN : Kg ≤ N := by
    have hu1 : 1 ≤ u := hu.1
    omega
  let pMask : ℕ := (q * (p - 1)).toNat
  let tMask : ℕ := (ah - 1).toNat
  have hqp0 : 0 ≤ q * (p - 1) := mul_nonneg (by omega) (by omega)
  have hah0 : 0 ≤ ah - 1 := by dsimp [ah]; omega
  have hpMaskZ : (pMask : ℤ) = q * (p - 1) := by
    dsimp [pMask]
    exact Int.toNat_of_nonneg hqp0
  have htMaskZ : (tMask : ℤ) = ah - 1 := by
    dsimp [tMask]
    exact Int.toNat_of_nonneg hah0
  have hpMask : pMask < 2 ^ (c - 1) := by
    have hh : q * (p - 1) < q * p := by nlinarith
    rw [hqpow] at hh
    have hh' : (pMask : ℤ) < (2 ^ (c - 1) : ℤ) := by rw [hpMaskZ]; exact hh
    exact_mod_cast hh'
  have htMask : tMask < 2 ^ (a - 1) := by
    have hh : ah - 1 < ah := by omega
    have haPow : ah = (2 : ℤ) ^ (a - 1) := rfl
    rw [haPow] at hh
    have hh' : (tMask : ℤ) < (2 ^ (a - 1) : ℤ) := by rw [htMaskZ]; exact hh
    exact_mod_cast hh'
  let vInt : ℤ := (L - u) / B
  let vNat : ℕ := vInt.toNat
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hLu0 : 0 ≤ L - u := by
    have hts : r ≤ t := by omega
    dsimp [L, u]
    nlinarith [mul_nonneg (by positivity : 0 ≤ s) (sub_nonneg.mpr hts)]
  have hv0 : 0 ≤ vInt := by
    dsimp [vInt]
    exact Int.ediv_nonneg hLu0 (by omega)
  have hvCast : (vNat : ℤ) = vInt := by
    dsimp [vNat]
    exact Int.toNat_of_nonneg hv0
  let rem : ℤ := (L - u) % B
  have hrem0 : 0 ≤ rem := by dsimp [rem]; exact Int.emod_nonneg _ (by omega)
  have hremB : rem < B := by dsimp [rem]; exact Int.emod_lt_of_pos _ hB0
  have hdiv : L - u = rem + B * vInt := by
    have hh := Int.emod_add_mul_ediv (L - u) B
    dsimp [rem, vInt]
    nlinarith only [hh]
  have hvle : B * vInt ≤ L - u := by omega
  have hLuLt : L - u < B * p := by
    have hLuLt' : L - u < s * t := by
      dsimp [L, u]
      have hrs : 0 < r * s + r + 1 - s := by nlinarith [hr, hs]
      nlinarith [hrs]
    have hBp : s * t ≤ B * p := by
      have hBtr : t * r ≤ B := by dsimp [B]; omega
      have hrp : 2 * s ≤ r * p := by rw [hsp]; nlinarith [hr]
      have h1 := mul_le_mul_of_nonneg_left hrp (show 0 ≤ t by positivity)
      have h2 := mul_le_mul_of_nonneg_right hBtr (show 0 ≤ p by omega)
      nlinarith
    omega
  have hvlt : vInt < p := by
    by_contra hn
    have hle : p ≤ vInt := by omega
    have hmul := mul_le_mul_of_nonneg_left hle hB0.le
    omega
  have hvNatlt : vNat < 2 ^ (b - 1) := by
    have : (vNat : ℤ) < p := by simpa [hvCast] using hvlt
    simpa [p] using (Int.ofNat_lt.mp this)
  have hcore : 0 ≤ vInt * B + r * (s + 1) - p * (t + 1) := by
    by_cases hba : b = a + 1
    · have hpEq : p = r := by
        dsimp [p, r]
        congr 1
        omega
      by_cases hcb : c = b
      · have htEq : t = s := by
          dsimp [t, s]
          congr 1
        rw [hpEq, htEq]
        have hvB0 : 0 ≤ vInt * B := mul_nonneg hv0 hB0.le
        linarith only [hvB0]
      · have hcb' : b + 1 ≤ c := by omega
        have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show a + 2 ≤ c by omega)
        have htr4 : 4 * r ≤ t := by
          dsimp [r, t]
          calc
            4 * 2 ^ a = 2 ^ (a + 2) := by
              rw [show a + 2 = (a + 1) + 1 by omega, pow_succ, pow_succ]
              ring
            _ ≤ 2 ^ c := hpow
        have hmul := mul_le_mul_of_nonneg_right htr4 (show 0 ≤ r - 1 by omega)
        have hBv : B ≤ L - u := by
          dsimp [B, L, u]
          rw [hsp, hpEq]
          nlinarith only [hmul, hr]
        have hv1 : 1 ≤ vInt := by
          by_contra hn
          have hvz : vInt = 0 := by omega
          have hdiv0 := hdiv
          rw [hvz, mul_zero, add_zero] at hdiv0
          linarith only [hBv, hremB, hdiv0]
        have hvB : B ≤ vInt * B := by
          calc
            B = 1 * B := by ring
            _ ≤ vInt * B := mul_le_mul_of_nonneg_right hv1 hB0.le
        have htarget : r * (t - 2 * r) ≤ B := by
          dsimp [B]
          have ht0 : 0 ≤ t := by positivity
          have hr0 : 0 ≤ r := by omega
          nlinarith only [hr, ht0, hr0, sq_nonneg r]
        rw [hsp, hpEq]
        linarith only [hvB, htarget]
    · have hba' : a + 2 ≤ b := by omega
      have hp2 : 2 * r ≤ p := by
        have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show a + 1 ≤ b - 1 by omega)
        dsimp [r, p]
        convert hpow using 1 <;> ring
      have hpB : B ≤ p * (t + 1) := by
        have hpr : r + 1 ≤ p := by omega
        have ht0 : (0 : ℤ) ≤ t := by positivity
        have hr0 : (0 : ℤ) ≤ r := le_trans (by norm_num) hr
        have hp1 := one_le_of_add_one_le hr0 hpr
        have hpB0 := beta_block_bound r p t hpr ht0 hp1
        simpa only [B] using hpB0
      have hLB : p * (t + 1) - r * (s + 1) ≤ L - u - B := by
        have hnonneg : 0 ≤ p * (t + 1) - B := by linarith only [hpB]
        calc
          p * (t + 1) - r * (s + 1) ≤
              (p * (t + 1) - r * (s + 1)) + (p * (t + 1) - B) := by
                linarith only [hnonneg]
          _ = L - u - B := by
            dsimp [L, u, B]
            rw [hsp]
            ring
      have hcore0 := core_from_floor L u B rem vInt p r s t hdiv hremB hLB
      exact hcore0
  let P := mask_labels (c - 1) 0 pMask hpMask
  let TV := mask_labels (b - 1) c vNat hvNatlt
  let TW := mask_labels (a - 1) (c + b) tMask htMask
  let T := TV ∪ TW
  let Q := Finset.range k \ (P ∪ T ∪ {c - 1, c + b - 1, k - 1})
  let alpha := c - 1
  let beta := c + b - 1
  let gamma := k - 1
  let word := P.toList ++ alpha :: Q.toList ++ beta :: T.toList ++ [gamma]
  let plusQ := P.toList ++ alpha :: k :: Q.toList ++ beta :: T.toList ++ [gamma]
  let plusT := P.toList ++ alpha :: Q.toList ++ beta :: T.toList ++ [k, gamma]
  have hPbound {i : ℕ} (hi : i ∈ P) : i < c - 1 := by
    have hh := mask_labels_bound hi
    omega
  have hTbound {i : ℕ} (hi : i ∈ T) : c ≤ i ∧ i < k - 1 := by
    simp only [T, Finset.mem_union] at hi
    rcases hi with hi | hi
    · have hh := mask_labels_bound hi
      omega
    · have hh := mask_labels_bound hi
      dsimp [k]
      omega
  have hPsub : P ⊆ Finset.range k := by
    intro i hi
    exact Finset.mem_range.mpr (by have := hPbound hi; dsimp [k]; omega)
  have hTsub : T ⊆ Finset.range k := by
    intro i hi
    exact Finset.mem_range.mpr (by have := hTbound hi; omega)
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hp' := hPbound hi
    have ht' := hTbound hj
    omega
  have hPn : ∀ i ∈ P, i ≠ alpha ∧ i ≠ beta ∧ i ≠ gamma := by
    intro i hi
    have hh := hPbound hi
    dsimp [alpha, beta, gamma, k]
    omega
  have hTn : ∀ i ∈ T, i ≠ alpha ∧ i ≠ beta ∧ i ≠ gamma := by
    intro i hi
    simp only [T, Finset.mem_union] at hi
    rcases hi with hi | hi
    · have hh := mask_labels_bound hi
      dsimp [alpha, beta, gamma, k]
      omega
    · have hh := mask_labels_bound hi
      dsimp [alpha, beta, gamma, k]
      omega
  have hp : word.Perm (List.range k) := by
    have hi := labelled_permutation k alpha beta gamma P T hPsub hTsub hPT
      (by dsimp [alpha, beta, gamma, k]; omega)
      (by dsimp [alpha, beta, gamma, k]; omega) hPn hTn
    change (P.toList ++ alpha :: T.toList ++ beta :: Q.toList ++ [gamma]).Perm _ at hi
    have he : word.Perm (P.toList ++ alpha :: T.toList ++ beta :: Q.toList ++ [gamma]) := by
      apply Multiset.coe_eq_coe.mp
      change (P.toList : Multiset ℕ) + ({alpha} + (Q.toList : Multiset ℕ)) +
          ({beta} + (T.toList : Multiset ℕ)) + {gamma} =
        (P.toList : Multiset ℕ) + ({alpha} + (T.toList : Multiset ℕ)) +
          ({beta} + (Q.toList : Multiset ℕ)) + {gamma}
      ac_rfl
    exact he.trans hi
  have hplusQ : plusQ.Perm (List.range (k + 1)) := by
    have he : plusQ.Perm (word ++ [k]) := by
      apply Multiset.coe_eq_coe.mp
      change (P.toList : Multiset ℕ) + ({alpha} + ({k} + (Q.toList : Multiset ℕ))) +
          ({beta} + (T.toList : Multiset ℕ)) + {gamma} =
        (P.toList : Multiset ℕ) + ({alpha} + (Q.toList : Multiset ℕ)) +
          ({beta} + (T.toList : Multiset ℕ)) + {gamma} + {k}
      ac_rfl
    exact he.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have hplusT : plusT.Perm (List.range (k + 1)) := by
    have he : plusT.Perm (word ++ [k]) := by
      apply Multiset.coe_eq_coe.mp
      change (P.toList : Multiset ℕ) + ({alpha} + (Q.toList : Multiset ℕ)) +
          ({beta} + (T.toList : Multiset ℕ)) + ({k} + {gamma}) =
        (P.toList : Multiset ℕ) + ({alpha} + (Q.toList : Multiset ℕ)) +
          ({beta} + (T.toList : Multiset ℕ)) + {gamma} + {k}
      ac_rfl
    exact he.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have hWbase : 0 ≤ 2 * L - s - 1 := by
    dsimp [L]
    have hs0 : (0 : ℤ) ≤ s := by omega
    have ht0 : (0 : ℤ) ≤ t := by omega
    have hst : (0 : ℤ) ≤ s * t := mul_nonneg hs0 ht0
    calc
      (0 : ℤ) ≤ 1 + s + 2 * (s * t) := by omega
      _ = 2 * (1 + s + s * t) - s - 1 := by ring
  have hpositive (i : ℕ) (hi : i < k)
      (hn : i ≠ alpha ∧ i ≠ beta ∧ i ≠ gamma) : 0 ≤ f i ∧ 0 ≤ g i := by
    by_cases h1 : i < c - 1
    · obtain ⟨hf, hg⟩ := hU i h1
      rw [hf, hg]
      constructor <;> positivity
    · by_cases h2 : i < c + b - 1
      · have he : i = c + (i - c) := by omega
        obtain ⟨hf, hg⟩ := hV (i - c) (by omega)
        rw [he, hf, hg]
        have hbb : 0 ≤ 2 * B - 1 := by omega
        constructor <;> positivity
      · have he : i = c + b + (i - (c + b)) := by omega
        obtain ⟨hf, hg⟩ := hW (i - (c + b)) (by dsimp [k] at hi hn; omega)
        rw [he, hf, hg]
        constructor
        · positivity
        · positivity
  have hPpos : ∀ i ∈ P.toList, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hm := Finset.mem_toList.mp hi
    exact hpositive i (Finset.mem_range.mp (hPsub hm)) (hPn i hm)
  have hTpos : ∀ i ∈ T.toList, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hm := Finset.mem_toList.mp hi
    exact hpositive i (Finset.mem_range.mp (hTsub hm)) (hTn i hm)
  have hQpos : ∀ i ∈ Q.toList, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hm := Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)
    have hn : i ≠ alpha ∧ i ≠ beta ∧ i ≠ gamma := by
      have hh : i ∉ ({alpha, beta, gamma} : Finset ℕ) := by
        intro hmem
        exact hm.2 (Finset.mem_union_right _ hmem)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2⟩
    exact hpositive i (Finset.mem_range.mp hm.1) hn
  let x := u * (pMask : ℤ)
  let xn := 2 * x
  let y := vInt * B + (ah - 1) * L
  let yn := vInt * (2 * B - 1) + (ah - 1) * (2 * L - s - 1)
  have hPsum : (P.toList.map f).sum = x ∧ (P.toList.map g).sum = xn := by
    constructor
    · rw [Finset.sum_map_toList]
      rw [mask_labels_sum (c - 1) 0 pMask hpMask f u
        (fun i hi => by simpa using (hU i hi).1)]
      dsimp [x]
      rw [hpMaskZ]
      ring
    · rw [Finset.sum_map_toList]
      rw [mask_labels_sum (c - 1) 0 pMask hpMask g (2 * u)
        (fun i hi => by simpa using (hU i hi).2)]
      dsimp [xn, x]
      rw [hpMaskZ]
      ring
  have hTsum : (T.toList.map f).sum = y ∧ (T.toList.map g).sum = yn := by
    constructor
    · have hdis : Disjoint TV TW := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        have hvv := mask_labels_bound hi
        have hww := mask_labels_bound hj
        omega
      rw [Finset.sum_map_toList, Finset.sum_union hdis,
        mask_labels_sum (b - 1) c vNat hvNatlt f B
          (fun i hi => by simpa using (hV i hi).1),
        mask_labels_sum (a - 1) (c + b) tMask htMask f L
          (fun i hi => by simpa using (hW i hi).1), hvCast, htMaskZ]
    · have hdis : Disjoint TV TW := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        have hvv := mask_labels_bound hi
        have hww := mask_labels_bound hj
        omega
      rw [Finset.sum_map_toList, Finset.sum_union hdis,
        mask_labels_sum (b - 1) c vNat hvNatlt g (2 * B - 1)
          (fun i hi => by simpa using (hV i hi).2),
        mask_labels_sum (a - 1) (c + b) tMask htMask g
          (2 * L - s - 1) (fun i hi => by simpa using (hW i hi).2), hvCast, htMaskZ]
  have heps : x - Ha = 1 + q * (s - r - 1) := by
    dsimp [x, Ha, u, pMask, C]
    rw [hpMaskZ, htq, hsp, hrhalf]
    ring
  have hPnewA : 0 ≤ xn - Ka ∧ xn - Ka ≤ N := by
    have hA : xn - Ka = 2 * (1 + q * (s - r - 1)) - 1 := by
      dsimp [xn, x, Ka]
      have hrewrite : 2 * (u * (pMask : ℤ)) - (2 * Ha + 1) =
          2 * (x - Ha) - 1 := by
        dsimp [x]
        ring
      rw [hrewrite, heps]
    rw [hA]
    have hsr : 0 ≤ s - r - 1 := by rw [hsp]; omega
    exact new_margin_bounds q s r t N hq hsr hr hs htq hN
  have heps0 : 1 ≤ 1 + q * (s - r - 1) := by
    have hsr : 0 ≤ s - r - 1 := by omega
    have hprod : 0 ≤ q * (s - r - 1) := mul_nonneg (by omega) hsr
    linarith only [hprod]
  have hCx : C - x = q * (p * (r - 1) + r + 1) - 1 := by
    dsimp [C, x, u, pMask]
    rw [hpMaskZ, htq, hsp, hrhalf]
    ring
  have hCx0 : 0 ≤ C - x := by
    rw [hCx]
    have hp0 : (0 : ℤ) ≤ p := by linarith only [hp_bound]
    have hrm0 : (0 : ℤ) ≤ r - 1 := by linarith only [hr]
    have hprod : 0 ≤ p * (r - 1) := mul_nonneg hp0 hrm0
    have hinner : 1 ≤ p * (r - 1) + r + 1 := by linarith only [hprod, hr]
    have hq0 : (0 : ℤ) ≤ q := by linarith only [hq]
    have hmul := mul_le_mul_of_nonneg_left hinner hq0
    have hqmul : q ≤ q * (p * (r - 1) + r + 1) := by simpa using hmul
    have hmul' : 1 ≤ q * (p * (r - 1) + r + 1) := le_trans hq hqmul
    linarith only [hmul']
  have hOldAlpha : 0 ≤ x - Ha ∧ x - Ha ≤ C := by
    constructor
    · rw [heps]
      linarith only [heps0]
    · linarith only [hCx0, hHa0]
  have hy_le : y ≤ (r / 2) * L - u := by
    have hmul : vInt * B ≤ L - u := by
      calc
        vInt * B = B * vInt := by rw [mul_comm]
        _ ≤ L - u := hvle
    have hsum : vInt * B + (ah - 1) * L ≤ (L - u) + (ah - 1) * L := by
      linarith only [hmul]
    calc
      y = vInt * B + (ah - 1) * L := rfl
      _ ≤ (L - u) + (ah - 1) * L := hsum
      _ = (r / 2) * L - u := by rw [hrdiv]; ring
  have hHgEq : Hg = (r / 2) * L - u := by
    dsimp [Hg, L, u, C]
    rw [hsp, htq, hrhalf]
    have hhalfAh : (2 * ah : ℤ) / 2 = ah := by omega
    rw [hhalfAh]
    ring
  have hdelta0 : 0 ≤ Hg - y := by
    rw [hHgEq]
    linarith only [hy_le]
  have hdeltaC : Hg - y ≤ C := by
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    linarith only [hHgC, hy0]
  have hwordzero : (word.map f).sum = 0 := by
    have hs := (hp.map f).sum_eq
    rw [hzero] at hs
    exact hs
  have hsum0 : x + (-Ha + (Q.toList.map f).sum) + (-Hb + y) + -Hg = 0 := by
    have hwordzero' :
        ((P.toList ++ alpha :: Q.toList ++ beta :: T.toList ++ [gamma]).map f).sum = 0 := by
      simpa only [word] using hwordzero
    exact split_sum_zero f P.toList Q.toList T.toList alpha beta gamma x y Ha Hb Hg
      hPsum.1 hTsum.1 hfA' hfB' hfG' hwordzero'
  have hOldBeta : 0 ≤ x - Ha + (Q.toList.map f).sum - Hb ∧
      x - Ha + (Q.toList.map f).sum - Hb ≤ C := by
    exact old_beta_bounds x Ha (Q.toList.map f).sum Hb y Hg C hsum0 hdelta0 hdeltaC
  have hOldP : 0 ≤ x ∧ x ≤ C := by
    constructor
    · dsimp [x]
      have hx0 := nat_cast_nonneg_mul u pMask (le_trans (by norm_num) hu.1)
      exact hx0
    · linarith only [hCx0]
  have hE : C - (Hg - y + Hb) =
      vInt * B + r * (s + 1) - p * (t + 1) := by
    dsimp [C, Hg, Hb, y, L]
    rw [hrhalf, hsp]
    ring_nf
  have hQupper : Hg - y + Hb ≤ C := by
    linarith only [hE, hcore]
  have hOldQend : 0 ≤ x - Ha + (Q.toList.map f).sum ∧
      x - Ha + (Q.toList.map f).sum ≤ C := by
    have hs : x - Ha + (Q.toList.map f).sum - Hb + y - Hg = 0 := by
      linarith only [hsum0]
    have hrel : x - Ha + (Q.toList.map f).sum = Hg - y + Hb := by
      linarith only [hs]
    rw [hrel]
    constructor
    · linarith only [hdelta0, hHb0]
    · exact hQupper
  have hOldP' : 0 ≤ (P.toList.map f).sum ∧ (P.toList.map f).sum ≤ C := by
    rw [hPsum.1]
    exact hOldP
  have hOldAlpha' : 0 ≤ (P.toList.map f).sum - Ha ∧
      (P.toList.map f).sum - Ha ≤ C := by
    rw [hPsum.1]
    exact hOldAlpha
  have hOldBeta' : 0 ≤ (P.toList.map f).sum - Ha + (Q.toList.map f).sum - Hb ∧
      (P.toList.map f).sum - Ha + (Q.toList.map f).sum - Hb ≤ C := by
    rw [hPsum.1]
    exact hOldBeta
  have hOldQend' : 0 ≤ (P.toList.map f).sum - Ha + (Q.toList.map f).sum ∧
      (P.toList.map f).sum - Ha + (Q.toList.map f).sum ≤ C := by
    rw [hPsum.1]
    exact hOldQend
  have hPnewMass : 0 ≤ (P.toList.map g).sum ∧ (P.toList.map g).sum ≤ N := by
    rw [hPsum.2]
    constructor
    · dsimp [xn]
      linarith only [hOldP.1]
    · dsimp [xn]
      linarith only [hOldP.2, hC]
  have hNewAlpha : 0 ≤ (P.toList.map g).sum - Ka ∧
      (P.toList.map g).sum - Ka ≤ N := by
    rw [hPsum.2]
    exact hPnewA
  have hDexpr : Kg - yn = 2 * (Hg - y) + (u + 1) / 2 + vInt + (ah - 1) * (s + 1) := by
    dsimp [Kg, yn, y]
    rw [huHalf]
    ring
  let D := Kg - yn
  have hD0 : 0 ≤ D := by
    dsimp [D]
    rw [hDexpr, huHalf]
    have hah0' : (0 : ℤ) ≤ ah := by linarith only [hah0]
    have hsplus : (0 : ℤ) ≤ s + 1 := by linarith only [hs]
    have hterm0 : (0 : ℤ) ≤ 2 * (Hg - y) :=
      mul_nonneg (by norm_num) hdelta0
    have hterm1 : (0 : ℤ) ≤ ah * (s + 1) := mul_nonneg hah0' hsplus
    have hterm2 : (0 : ℤ) ≤ (ah - 1) * (s + 1) := mul_nonneg hah0 hsplus
    linarith only [hterm0, hterm1, hterm2, hv0]
  have hLam : u ≤ s * t + s / 2 := by
    dsimp [u]
    have hst : r * s ≤ s * t := by
      have hrt : r ≤ t := by linarith only [htr, hr]
      have hs0 : (0 : ℤ) ≤ s := by linarith only [hs]
      have hmul := mul_le_mul_of_nonneg_left hrt hs0
      simpa [mul_comm] using hmul
    have hsdiv : s / 2 = p := by
      rw [hsp]
      exact Int.mul_ediv_cancel_left p (by norm_num)
    have hsr : r ≤ s / 2 := by rw [hsdiv]; exact hrp
    have hgap : 1 ≤ s * t - r * s := by
      have htr' : r + 1 ≤ t := by linarith only [htr, hr]
      have hs0 : (0 : ℤ) ≤ s := by linarith only [hs]
      have hmul := mul_le_mul_of_nonneg_left htr' hs0
      have hs1 : (1 : ℤ) ≤ s := by linarith only [hs]
      have hmul' : r * s + s ≤ s * t := by
        simpa [add_mul, mul_comm, add_comm, add_left_comm] using hmul
      linarith only [hmul', hs1]
    linarith only [hst, hsr, hgap]
  have hLamN : s * t + s / 2 ≤ N := by
    rw [hN]
    have hsdiv : s / 2 = p := by
      rw [hsp]
      exact Int.mul_ediv_cancel_left p (by norm_num)
    rw [hsdiv]
    have hs0 : (0 : ℤ) ≤ s := by linarith only [hs]
    have ht1 : (1 : ℤ) ≤ t := by linarith only [htr, hr]
    have hst0 : (0 : ℤ) ≤ s * t := mul_nonneg hs0 (by linarith only [ht1])
    have hst_ge_s : s ≤ s * t := by
      have hmul := mul_le_mul_of_nonneg_left ht1 hs0
      simpa [mul_comm] using hmul
    have hthree : 1 + p ≤ 3 * (s * t) := by
      have hp0 : (0 : ℤ) ≤ p := by linarith only [hp_bound]
      linarith only [hst_ge_s, hs, hp_bound, hsp]
    have hrm3 : (3 : ℤ) ≤ r - 1 := by linarith only [hr]
    have hmul3 := mul_le_mul_of_nonneg_right hrm3 hst0
    have hdiff : 1 + p ≤ (r - 1) * (s * t) := by
      linarith only [hthree, hmul3]
    have hident : (r - 1) * (s * t) = r * s * t - s * t := by ring
    linarith only [hdiff, hident]
  have hDleN_of_le (hcut : D ≤ s * t + s / 2) : D ≤ N :=
    le_trans hcut hLamN
  have hQcase : D ≤ s * t + s / 2 ∨ s * t + s / 2 < D := le_or_gt D (s * t + s / 2)
  have hold := ordered_schedule f (List.range k) P.toList Q.toList T.toList
    alpha beta gamma Ha Hb Hg C hp hfA' hfB' hfG' hHa0 hHb0 ⟨hHg0, hHgC⟩
    (fun i hi => (hPpos i hi).1) (fun i hi => (hQpos i hi).1) (fun i hi => (hTpos i hi).1)
    hOldP' hOldAlpha' hOldQend' hOldBeta' hzero
  have hyn0 : 0 ≤ yn := by
    rw [← hTsum.2]
    apply List.sum_nonneg
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    exact (hTpos i hi).2
  have hTailEndpoint : D - u + Kb =
      2 * (Hg - y + Hb) + vInt - p := by
    dsimp only [D]
    rw [hDexpr, huHalf]
    dsimp only [Kb, u]
    have hsdiv : s / 2 = p := by
      rw [hsp]
      exact Int.mul_ediv_cancel_left p (by norm_num)
    rw [hsdiv, hrhalf, hsp]
    ring
  by_cases hcut : D ≤ s * t + s / 2
  · have hDleN := hDleN_of_le hcut
    have hsumQ : xn - Ka + u + (Q.toList.map g).sum - Kb + yn - Kg = 0 := by
      have hpluszero : (plusQ.map g).sum = 0 := by
        have hs' := (hplusQ.map g).sum_eq
        rw [hzero'] at hs'
        exact hs'
      have hs0 : xn + (-Ka + (u + (Q.toList.map g).sum)) + (-Kb + yn) + -Kg = 0 := by
        simpa only [plusQ, alpha, beta, gamma, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hPsum.2, hTsum.2, hgA', hgB', hgG', hgear] using hpluszero
      linarith only [hs0]
    have hBetaEqQ : xn - Ka + u + (Q.toList.map g).sum - Kb = D := by
      dsimp [D]
      linarith only [hsumQ]
    have hNewBetaQ : 0 ≤ xn - Ka + u + (Q.toList.map g).sum - Kb ∧
        xn - Ka + u + (Q.toList.map g).sum - Kb ≤ N := by
      rw [hBetaEqQ]
      exact ⟨hD0, hDleN⟩
    have hCutKb : s * t + s / 2 + Kb = N := by
      have hsdiv : s / 2 = p := by
        have hs : s / 2 = (2 * p) / 2 :=
          congrArg (fun z : ℤ => z / 2) hsp
        exact hs.trans (int_half_two_mul p)
      rw [hsdiv]
      have hKb' : 2 * Kb = (2 * N + 1) -
          (2 * (1 + s + s * t) - s - 1) := by
        exact hKb
      linarith only [hKb', hsp]
    have hNewQend : 0 ≤ xn - Ka + u + (Q.toList.map g).sum ∧
        xn - Ka + u + (Q.toList.map g).sum ≤ N := by
      have hqeq : xn - Ka + u + (Q.toList.map g).sum = D + Kb := by
        exact sub_eq_iff_eq_add.mp hBetaEqQ
      rw [hqeq]
      constructor
      · exact add_nonneg hD0 hKb0
      · exact add_bound_of_eq hcut hCutKb
    have hNewQend' : 0 ≤ (P.toList.map g).sum - Ka + ((k :: Q.toList).map g).sum ∧
        (P.toList.map g).sum - Ka + ((k :: Q.toList).map g).sum ≤ N := by
      exact fresh_prefix_bounds g P.toList Q.toList k xn u Ka N hPsum.2 hgear hNewQend
    have hNewBetaQ' : 0 ≤ (P.toList.map g).sum - Ka + ((k :: Q.toList).map g).sum - Kb ∧
        (P.toList.map g).sum - Ka + ((k :: Q.toList).map g).sum - Kb ≤ N := by
      exact fresh_prefix_bounds_sub g P.toList Q.toList k xn u Ka Kb N hPsum.2 hgear hNewBetaQ
    change (P.toList ++ alpha :: k :: Q.toList ++ beta :: T.toList ++ [gamma]).Perm
        (List.range (k + 1)) at hplusQ
    have hnew := ordered_schedule g (List.range (k + 1)) P.toList
      (k :: Q.toList) T.toList alpha beta gamma Ka Kb Kg N hplusQ hgA' hgB' hgG'
      hKa0 hKb0 ⟨hKg0, hKgN⟩ (fun i hi => (hPpos i hi).2)
      (by intro i hi; rcases List.mem_cons.mp hi with rfl | hi
          · rw [hgear]; omega
          · exact (hQpos i hi).2)
      (fun i hi => (hTpos i hi).2) hPnewMass hNewAlpha hNewQend' hNewBetaQ'
      hzero'
    let j := P.toList.length + 1
    have hj : j ≤ k := by
      have hh := hp.length_eq
      simp only [word, List.length_append, List.length_cons, List.length_singleton,
        List.length_range] at hh
      dsimp only [j]
      omega
    have hk : 0 < k := by dsimp [k]; omega
    refine ⟨word.map (label k hk), j, hj, ?_, ?_⟩
    · refine lift_order k (1 + 2 ^ a + 2 ^ (a + b)) hk word hp ?_ ?_
      · simpa only [word, hseed, hhalf] using hold
      · simpa only [hseed] using hzero
    · have he : earWord k (word.map (label k hk)) j = plusQ.map (label (k + 1) (by omega)) := by
        have hpre : (P.toList ++ [alpha]).length = j := by simp [j]
        have hw : (P.toList ++ [alpha]) ++ (Q.toList ++ beta :: T.toList ++ [gamma]) = word := by
          simp only [word, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
        have hpw : (P.toList ++ [alpha]) ++ k :: (Q.toList ++ beta :: T.toList ++ [gamma]) = plusQ := by
          simp only [plusQ, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
        simpa only [hw, hpw] using marked_word k j hk (P.toList ++ [alpha])
          (Q.toList ++ beta :: T.toList ++ [gamma]) hpre (by rw [hw]; exact hp)
      rw [he]
      refine lift_order (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by omega) plusQ hplusQ ?_ ?_
      · simpa only [plusQ, Nat.cast_mul, Nat.cast_ofNat, hseed, hnewhalf] using hnew
      · simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed] using hzero'
  · have hDminusU : 0 ≤ D - u := by
      have hstrict : s * t + s / 2 < D := lt_of_not_ge hcut
      linarith only [hLam, hstrict]
    have hNewBetaT : 0 ≤ xn - Ka + (Q.toList.map g).sum - Kb ∧
        xn - Ka + (Q.toList.map g).sum - Kb ≤ N := by
      have hs : xn - Ka + (Q.toList.map g).sum - Kb + yn + u - Kg = 0 := by
        have hpluszero : (plusT.map g).sum = 0 := by
          have hs' := (hplusT.map g).sum_eq
          rw [hzero'] at hs'
          exact hs'
        simp only [plusT, alpha, beta, gamma, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, hPsum.2, hTsum.2, hgA', hgB', hgG', hgear]
          at hpluszero
        linarith only [hpluszero]
      have heq : xn - Ka + (Q.toList.map g).sum - Kb = D - u := by
        dsimp only [D]
        linarith only [hs]
      rw [heq]
      refine ⟨hDminusU, ?_⟩
      dsimp only [D]
      linarith only [hKgN, hyn0, hu.1]
    have hNewBetaT' : 0 ≤ (P.toList.map g).sum - Ka + (Q.toList.map g).sum - Kb ∧
        (P.toList.map g).sum - Ka + (Q.toList.map g).sum - Kb ≤ N := by
      rw [hPsum.2]
      exact hNewBetaT
    have hNewQendT : 0 ≤ xn - Ka + (Q.toList.map g).sum ∧
        xn - Ka + (Q.toList.map g).sum ≤ N := by
      constructor
      · linarith only [hNewBetaT.1, hKb0]
      · have hEndpoint : xn - Ka + (Q.toList.map g).sum = D - u + Kb := by
          have hpluszero := (hplusT.map g).sum_eq
          rw [hzero'] at hpluszero
          simp only [plusT, alpha, beta, gamma, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero, hPsum.2, hTsum.2,
            hgA', hgB', hgG', hgear] at hpluszero
          dsimp only [D]
          linarith only [hpluszero]
        rw [hEndpoint, hTailEndpoint]
        linarith only [hQupper, hvlt, hC]
    have hNewQendT' : 0 ≤ (P.toList.map g).sum - Ka + (Q.toList.map g).sum ∧
        (P.toList.map g).sum - Ka + (Q.toList.map g).sum ≤ N := by
      rw [hPsum.2]
      exact hNewQendT
    have hplusT' : (P.toList ++ alpha :: Q.toList ++
        beta :: (T.toList ++ [k]) ++ [gamma]).Perm (List.range (k + 1)) := by
      simpa only [plusT, List.append_assoc, List.cons_append,
        List.singleton_append, List.nil_append] using hplusT
    have hnew0 := ordered_schedule g (List.range (k + 1)) P.toList
      Q.toList (T.toList ++ [k]) alpha beta gamma Ka Kb Kg N hplusT' hgA' hgB' hgG'
      hKa0 hKb0 ⟨hKg0, hKgN⟩ (fun i hi => (hPpos i hi).2) (fun i hi => (hQpos i hi).2)
      (by intro i hi; rcases List.mem_append.mp hi with hi | hi
          · exact (hTpos i hi).2
          · simp only [List.mem_singleton] at hi
            subst hi
            rw [hgear]
            omega)
      hPnewMass hNewAlpha hNewQendT' hNewBetaT' hzero'
    have hnew : InStrip g N 0 plusT := by
      simpa only [plusT, List.append_assoc, List.cons_append,
        List.singleton_append, List.nil_append] using hnew0
    let pre := P.toList ++ alpha :: Q.toList ++ beta :: T.toList
    let j := pre.length
    have hj : j ≤ k := by
      have hh := hp.length_eq
      simp only [word, List.length_append, List.length_cons, List.length_singleton,
        List.length_range] at hh
      dsimp [j, pre]
      simp only [List.length_append, List.length_cons]
      omega
    have hk : 0 < k := by dsimp [k]; omega
    refine ⟨word.map (label k hk), j, hj, ?_, ?_⟩
    · refine lift_order k (1 + 2 ^ a + 2 ^ (a + b)) hk word hp ?_ ?_
      · simpa only [word, hseed, hhalf] using hold
      · simpa only [hseed] using hzero
    · have he : earWord k (word.map (label k hk)) j = plusT.map (label (k + 1) (by omega)) := by
        have hw : pre ++ [gamma] = word := by
          simp only [pre, word, List.append_assoc, List.cons_append]
        have hpw : pre ++ k :: [gamma] = plusT := by
          simp only [pre, plusT, List.append_assoc, List.cons_append]
        simpa only [hw, hpw] using marked_word k j hk pre [gamma] rfl
          (by rw [hw]; exact hp)
      rw [he]
      refine lift_order (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by omega) plusT hplusT ?_ ?_
      · simpa only [plusT, Nat.cast_mul, Nat.cast_ofNat, hseed, hnewhalf] using hnew
      · simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed] using hzero'

#print axioms actualSource_three_negative_ordered_cone_joint_lift
end D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift
