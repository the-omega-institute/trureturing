/- GID: D5/S1/Words/Forbidden/BorderImbalanceExclusion
   generality: G
   mirror-B: D5/B/S1/Words/Forbidden/BorderImbalanceExclusion
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The longest nonzero border imbalance excludes cancellation at the growth root. -/
/-
proof_shape: lowerPoly_identity: content
proof_shape: lowerPoly_positive: bind-only; consumer: dominance_kernel
proof_shape: root_envelope: bind-only; consumer: dominance_kernel
proof_shape: dominance_kernel: bind-only; consumer: longest_positive_H_pos
proof_shape: prefix_imbalance_lower: bind-only; consumer: coeff_lower_at_longest_positive
proof_shape: linearEnvelope_succ: bind-only; consumer: lowerPoly_eq_linearEnvelope
proof_shape: lowerPoly_eq_linearEnvelope: bind-only; consumer: longest_positive_H_pos
proof_shape: signedCoeff_zero: bind-only; consumer: hEval_lower_envelope
proof_shape: coeff_lower_at_longest_positive: bind-only; consumer: hEval_lower_envelope
proof_shape: hEval_cut: bind-only; consumer: hEval_lower_envelope
proof_shape: hEval_lower_envelope: content
proof_shape: longest_positive_H_pos: content
proof_shape: balanced_iff_imbalance_zero: bind-only; consumer: unbalanced_hEval_ne_zero
proof_shape: corrEval_ge_full: bind-only; consumer: root_equation_envelope
proof_shape: root_equation_envelope: bind-only; consumer: unbalanced_boundary_moment_ne_zero
proof_shape: hEval_eq_border_sum: bind-only; consumer: reciprocal_overlapMoment
proof_shape: flip_flip: bind-only; consumer: flip_suffix_iff
proof_shape: flip_suffix_iff: bind-only; consumer: flip_borderLengths
proof_shape: flip_borderLengths: bind-only; consumer: signedCoeff_flip
proof_shape: flip_infix_iff: bind-only; consumer: flip_mem_omega
proof_shape: count_flip: bind-only; consumer: flip_imbalance
proof_shape: flip_imbalance: bind-only; consumer: signedCoeff_flip
proof_shape: signedCoeff_flip: bind-only; consumer: hEval_flip
proof_shape: hEval_flip: bind-only; consumer: unbalanced_hEval_ne_zero
proof_shape: unbalanced_hEval_ne_zero: content
escape_witness: unbalanced_hEval_ne_zero on result's live proof path.
admission_basis: escape-witness
Direct frozen dependencies: none on the protected baseline.
Same-delivery dependencies: ForbiddenWordCounting.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.Forbidden.ForbiddenWordCounting
import Mathlib.Data.Bool.Count

open Filter Finset
open scoped Topology

namespace D5.S1.Words.Forbidden.BorderImbalanceExclusion
open D5.S1.Words.Forbidden.ForbiddenWordCounting

private def lowerPoly : ℕ → ℝ → ℝ
  | 0, x => x ^ 2
  | k + 1, x => x * lowerPoly k x - (k + 1 : ℝ) * x

private theorem lowerPoly_identity (k : ℕ) (x : ℝ) :
    (x - 1) ^ 2 * lowerPoly k x =
      -(2 - x) * x ^ (k + 3) + (k + 1 : ℝ) * x ^ 2 - (k : ℝ) * x := by
  induction k with
  | zero => simp [lowerPoly]; ring
  | succ k ih =>
      simp only [lowerPoly, Nat.cast_add, Nat.cast_one]
      rw [show (x - 1) ^ 2 * (x * lowerPoly k x - ((k : ℝ) + 1) * x) =
          x * ((x - 1) ^ 2 * lowerPoly k x) - ((k : ℝ) + 1) * x * (x - 1) ^ 2 by ring]
      rw [ih]
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
      ring

private theorem lowerPoly_positive {k : ℕ} {x : ℝ} (hk : 0 < k) (hx : 1 < x)
    (hroot : (2 - x) * x ^ (k + 3) ≤ x ^ 2) :
    0 < lowerPoly k x := by
  have hden : 0 < (x - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hkp : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hgain : 0 < (k : ℝ) * x * (x - 1) :=
    mul_pos (mul_pos hkp (by linarith)) (by linarith)
  have hnum : 0 < (x - 1) ^ 2 * lowerPoly k x := by
    rw [lowerPoly_identity]
    nlinarith
  exact (mul_pos_iff_of_pos_left hden).mp hnum

private theorem root_envelope {k n : ℕ} {x : ℝ} (hn : k + 2 ≤ n)
    (hx : 1 < x) (hx2 : x < 2)
    (hroot : (2 - x) * x ^ (n - 1) ≤ 1) :
    (2 - x) * x ^ (k + 3) ≤ x ^ 2 := by
  have hpow : x ^ (k + 3) ≤ x ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith : 1 ≤ x) (by omega)
  calc
    (2 - x) * x ^ (k + 3) ≤ (2 - x) * x ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = ((2 - x) * x ^ (n - 1)) * x ^ 2 := by
      rw [show n + 1 = n - 1 + 2 by omega, pow_add]
      ring
    _ ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right hroot (sq_nonneg x)
    _ = x ^ 2 := one_mul _

private theorem dominance_kernel {k n : ℕ} {x H : ℝ} (hk : 0 < k)
    (hn : k + 2 ≤ n) (hx : 1 < x) (hx2 : x < 2)
    (hroot : (2 - x) * x ^ (n - 1) ≤ 1)
    (hlower : lowerPoly k x ≤ H) : 0 < H :=
  lt_of_lt_of_le (lowerPoly_positive hk hx (root_envelope hn hx hx2 hroot)) hlower

noncomputable def signedCoeff (w : List Bool) (j : ℕ) : ℝ :=
  if j ∈ borderLengths w then (imbalance w j : ℝ) else 0

noncomputable def corrEval (w : List Bool) (x : ℝ) : ℝ :=
  ∑ j ∈ borderLengths w, x ^ j

noncomputable def hEval (w : List Bool) (x : ℝ) : ℝ :=
  ∑ j ∈ range (w.length + 1), signedCoeff w j * x ^ j

private theorem prefix_imbalance_lower {w : List Bool} {j k : ℕ}
    (hjk : j ≤ k) (hkn : k ≤ w.length) :
    imbalance w k - (k - j : ℕ) ≤ imbalance w j := by
  have hlt : (w.take k).length = k := List.length_take_of_le hkn
  have hlj : (w.take j).length = j := List.length_take_of_le (hjk.trans hkn)
  have hd : ((w.take k).drop j).length = k - j := by simp [hlt]
  have he : (w.take k).count true = (w.take j).count true +
      ((w.take k).drop j).count true := by
    have ht := congrArg (fun u : List Bool => u.count true) (List.take_append_drop j (w.take k))
    simpa [List.count_append, List.take_take, Nat.min_eq_left hjk] using ht.symm
  have hc := List.count_le_length (a := true) (l := ((w.take k).drop j))
  rw [hd] at hc
  unfold imbalance
  rw [hlt, hlj]
  omega

private noncomputable def linearEnvelope (n : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ range (n + 1), ((j : ℝ) + 1 - n) * x ^ j) + n - 1

private theorem linearEnvelope_succ (n : ℕ) (x : ℝ) :
    linearEnvelope (n + 1) x = x * linearEnvelope n x - (n - 1 : ℝ) * x := by
  unfold linearEnvelope
  rw [sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, pow_zero, mul_one]
  simp only [mul_add, mul_sub, Finset.mul_sum]
  have he : (∑ j ∈ range (n + 1), (((j : ℝ) + 1) + 1 - ((n : ℝ) + 1)) * x ^ (j + 1)) =
      ∑ j ∈ range (n + 1), x * (((j : ℝ) + 1 - n) * x ^ j) := by
    apply sum_congr rfl
    intro j _
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  rw [he]
  ring

private theorem lowerPoly_eq_linearEnvelope (k : ℕ) (x : ℝ) :
    lowerPoly k x = linearEnvelope (k + 2) x := by
  induction k with
  | zero => simp [lowerPoly, linearEnvelope, sum_range_succ]; ring
  | succ k ih =>
    rw [lowerPoly, show k + 1 + 2 = (k + 2) + 1 by omega, linearEnvelope_succ, ih]
    push_cast
    ring

private theorem signedCoeff_zero (w : List Bool) : signedCoeff w 0 = 0 := by
  simp [signedCoeff, mem_borderLengths]

private theorem coeff_lower_at_longest_positive {w : List Bool} {k j : ℕ}
    (hk : k ∈ borderLengths w) (hdk : 1 ≤ imbalance w k)
    (hj : 0 < j) (hjk : j ≤ k) :
    (j : ℝ) + 1 - k ≤ signedCoeff w j := by
  by_cases hmem : j ∈ borderLengths w
  · rw [signedCoeff, if_pos hmem]
    have hpre := prefix_imbalance_lower hjk (mem_borderLengths.mp hk).2.1
    have hsub : ((k - j : ℕ) : ℤ) = (k : ℤ) - j := by omega
    rw [hsub] at hpre
    have hi : (j : ℤ) + 1 - k ≤ imbalance w j := by omega
    exact_mod_cast hi
  · rw [signedCoeff, if_neg hmem]
    have hjlt : j < k := lt_of_le_of_ne hjk (by intro h; exact hmem (h ▸ hk))
    have hi : (j : ℤ) + 1 - k ≤ 0 := by omega
    exact_mod_cast hi

private theorem hEval_cut {w : List Bool} {k : ℕ} (hk : k ≤ w.length)
    (hmax : ∀ j ∈ range (w.length + 1), k < j → signedCoeff w j = 0) (x : ℝ) :
    hEval w x = ∑ j ∈ range (k + 1), signedCoeff w j * x ^ j := by
  unfold hEval
  symm
  apply sum_subset
  · exact range_mono (by omega)
  · intro j hj hjk
    have hkj : k < j := by simp only [mem_range] at hjk; omega
    rw [hmax j hj hkj, zero_mul]

private theorem hEval_lower_envelope {w : List Bool} {k : ℕ}
    (hk : k ∈ borderLengths w) (hdk : 1 ≤ imbalance w k)
    (hmax : ∀ j ∈ range (w.length + 1), k < j → signedCoeff w j = 0)
    {x : ℝ} (hx : 0 ≤ x) : linearEnvelope k x ≤ hEval w x := by
  obtain ⟨hk0, hkn, _⟩ := mem_borderLengths.mp hk
  rw [hEval_cut hkn hmax]
  have hl : (∑ j ∈ range (k + 1), if j = 0 then 0 else ((j : ℝ) + 1 - k) * x ^ j) =
      linearEnvelope k x := by
    unfold linearEnvelope
    rw [sum_range_succ', sum_range_succ']
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, pow_zero, mul_one, ite_true]
    ring
  rw [← hl]
  apply sum_le_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [signedCoeff_zero]
  · rw [if_neg hj0]
    exact mul_le_mul_of_nonneg_right
      (coeff_lower_at_longest_positive hk hdk (by omega) (by simp only [mem_range] at hj; omega))
      (pow_nonneg hx j)

private theorem longest_positive_H_pos {w : List Bool} {k : ℕ}
    (hk : k ∈ borderLengths w) (hdk : 1 ≤ imbalance w k)
    (hmax : ∀ j ∈ range (w.length + 1), k < j → signedCoeff w j = 0)
    {x : ℝ} (hx : 1 < x) (hx2 : x < 2)
    (hroot : (2 - x) * x ^ (w.length - 1) ≤ 1) : 0 < hEval w x := by
  have hkn := (mem_borderLengths.mp hk).2.1
  have hk0 := (mem_borderLengths.mp hk).1
  have hl := hEval_lower_envelope hk hdk hmax (by linarith : 0 ≤ x)
  rcases k with _ | _ | k
  · omega
  · simp [linearEnvelope, sum_range_succ] at hl
    linarith
  · by_cases hkz : k = 0
    · subst k
      have he := lowerPoly_eq_linearEnvelope 0 x
      simp only [lowerPoly] at he
      have hxpos : 0 < x ^ 2 := sq_pos_of_pos (by linarith)
      rw [← he] at hl
      linarith
    · have hkp : 0 < k := by omega
      have hknew : k + 2 ∈ borderLengths w := by simpa [Nat.succ_eq_add_one, add_assoc] using hk
      have hlnew : lowerPoly k x ≤ hEval w x := by
        rw [lowerPoly_eq_linearEnvelope]
        simpa [Nat.succ_eq_add_one, add_assoc] using hl
      exact dominance_kernel hkp (by omega) hx hx2 hroot hlnew

theorem balanced_iff_imbalance_zero (w : List Bool) :
    BalancedBorders w ↔ ∀ j ∈ borderLengths w, imbalance w j = 0 := by
  constructor
  · intro h j hj
    have hb : IsBorder w (w.take j) := borderLengths_iff_border.mpr ⟨j, hj, rfl⟩
    have hn := h _ hb
    unfold imbalance
    omega
  · intro h b hb
    obtain ⟨j, hj, rfl⟩ := borderLengths_iff_border.mp hb
    have hd := h j hj
    unfold imbalance at hd
    omega

theorem corrEval_ge_full {w : List Bool} (hw : w ≠ []) {x : ℝ} (hx : 0 ≤ x) :
    x ^ w.length ≤ corrEval w x := by
  exact single_le_sum (fun j _ => pow_nonneg hx j) (full_mem_borderLengths hw)

theorem root_equation_envelope {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx : 1 < x) (hx2 : x < 2) (hroot : (2 - x) * corrEval w x = x) :
    (2 - x) * x ^ (w.length - 1) ≤ 1 := by
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  have hC := corrEval_ge_full hw (by linarith : 0 ≤ x)
  have hpow : x ^ w.length = x ^ (w.length - 1) * x := by
    rw [← pow_succ]
    congr 1
    omega
  have hb : (2 - x) * x ^ w.length ≤ x := by
    calc
      (2 - x) * x ^ w.length ≤ (2 - x) * corrEval w x := by gcongr
      _ = x := hroot
  rw [hpow] at hb
  nlinarith

theorem hEval_eq_border_sum (w : List Bool) (x : ℝ) :
    hEval w x = ∑ j ∈ borderLengths w, (imbalance w j : ℝ) * x^j := by
  classical
  have hb : borderLengths w ⊆ range (w.length+1) := filter_subset _ _
  unfold hEval
  calc
    _ = ∑ j ∈ borderLengths w, signedCoeff w j * x^j := by
      symm
      apply sum_subset hb
      intro j _ hj
      simp [signedCoeff,hj]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      simp [signedCoeff,hj]

theorem flip_flip (u : List Bool) : (List.map Bool.not) ((List.map Bool.not) u) = u := by
  simp [ List.map_map, Function.comp_def]

private theorem flip_suffix_iff (v w : List Bool) : (List.map Bool.not) v <:+ (List.map Bool.not) w ↔ v <:+ w := by
  constructor
  · intro h
    have hh := h.map Bool.not
    change (List.map Bool.not) ((List.map Bool.not) v) <:+ (List.map Bool.not) ((List.map Bool.not) w) at hh
    simpa only [flip_flip] using hh
  · intro h
    exact h.map Bool.not

private theorem flip_borderLengths (w : List Bool) : borderLengths ((List.map Bool.not) w) = borderLengths w := by
  ext j
  rw [mem_borderLengths, mem_borderLengths]
  simp only [ List.length_map, ← List.map_take]
  change (0 < j ∧ j ≤ w.length ∧ (List.map Bool.not) (w.take j) <:+ (List.map Bool.not) w) ↔ _
  rw [flip_suffix_iff]

theorem flip_infix_iff (w u : List Bool) : (List.map Bool.not) w <:+: (List.map Bool.not) u ↔ w <:+: u := by
  constructor
  · intro h
    have hh := h.map Bool.not
    change (List.map Bool.not) ((List.map Bool.not) w) <:+: (List.map Bool.not) ((List.map Bool.not) u) at hh
    simpa only [flip_flip] using hh
  · intro h
    exact h.map Bool.not

theorem count_flip (u : List Bool) : ((List.map Bool.not) u).count true = u.count false := by
  exact List.count_map_of_injective u Bool.not (by
    intro a b hab
    cases a <;> cases b <;> simp_all) false

private theorem flip_imbalance (w : List Bool) (j : ℕ) :
    imbalance ((List.map Bool.not) w) j = -imbalance w j := by
  unfold imbalance
  simp only [ ← List.map_take, List.length_map]
  have hc := List.count_false_add_count_true (w.take j)
  have hf := count_flip (w.take j)
  change List.count true ((w.take j).map Bool.not) = _ at hf
  rw [hf]
  omega

private theorem signedCoeff_flip (w : List Bool) (j : ℕ) :
    signedCoeff ((List.map Bool.not) w) j = -signedCoeff w j := by
  unfold signedCoeff
  rw [flip_borderLengths, flip_imbalance]
  by_cases h : j ∈ borderLengths w <;> simp [h]

private theorem hEval_flip (w : List Bool) (x : ℝ) : hEval ((List.map Bool.not) w) x = -hEval w x := by
  unfold hEval
  simp only [signedCoeff_flip, neg_mul, sum_neg_distrib]
  simp only [ List.length_map]

theorem unbalanced_hEval_ne_zero {w : List Bool} (hw : ¬ BalancedBorders w)
    {x : ℝ} (hx : 1 < x) (hx2 : x < 2)
    (hroot : (2 - x) * x ^ (w.length - 1) ≤ 1) : hEval w x ≠ 0 := by
  classical
  let S := (borderLengths w).filter fun j => imbalance w j ≠ 0
  have hS : S.Nonempty := by
    rw [balanced_iff_imbalance_zero] at hw
    push_neg at hw
    obtain ⟨j, hj, hd⟩ := hw
    exact ⟨j, mem_filter.mpr ⟨hj, hd⟩⟩
  let k := S.max' hS
  have hkS : k ∈ S := max'_mem S hS
  have hk : k ∈ borderLengths w := (mem_filter.mp hkS).1
  have hdk : imbalance w k ≠ 0 := (mem_filter.mp hkS).2
  have hmax : ∀ j ∈ range (w.length + 1), k < j → signedCoeff w j = 0 := by
    intro j _ hkj
    unfold signedCoeff
    by_cases hj : j ∈ borderLengths w
    · have hdj : imbalance w j = 0 := by
        by_contra hdj
        have hjS : j ∈ S := mem_filter.mpr ⟨hj, hdj⟩
        have hle : j ≤ k := le_max' S j hjS
        omega
      simp [hj, hdj]
    · simp [hj]
  rcases lt_or_gt_of_ne hdk with hneg | hpos
  · have hdkf : 1 ≤ imbalance ((List.map Bool.not) w) k := by rw [flip_imbalance]; omega
    have hkf : k ∈ borderLengths ((List.map Bool.not) w) := by rw [flip_borderLengths]; exact hk
    have hmaxf : ∀ j ∈ range (((List.map Bool.not) w).length + 1), k < j → signedCoeff ((List.map Bool.not) w) j = 0 := by
      intro j hj hkj
      rw [signedCoeff_flip, hmax j (by simpa [] using hj) hkj, neg_zero]
    have hrootf : (2 - x) * x ^ (((List.map Bool.not) w).length - 1) ≤ 1 := by simpa [] using hroot
    have hp := longest_positive_H_pos hkf hdkf hmaxf hx hx2 hrootf
    rw [hEval_flip] at hp
    linarith
  · have hp := longest_positive_H_pos hk (by omega) hmax hx hx2 hroot
    exact hp.ne'

end D5.S1.Words.Forbidden.BorderImbalanceExclusion
