/- GID: D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/ArcCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/ArcCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Non-arc spin configurations have strictly smaller HKNN coefficient modulus. -/

/-
proof_shape: strict_coefficient_non_arc: content
escape_witness: Form (2): strict_coefficient_non_arc combines cyclic convexity with a
  constructed pair of interleaving matchings of opposite sign.
admission_basis: escape-witness
Direct frozen dependencies: none on immutable baseline; foundation imports belong to this delivery.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight.PairingCoefficients
import D5.S1.Phase.SeatTowerCombinatorics
import D5.S3.Zeros.Convolution.PerfectMatchingCount

noncomputable section
open scoped BigOperators
open Fin.NatCast
open D5.S1.Phase.SeatTowerCombinatorics (Stationing)
open D5.S3.Zeros.Convolution.PerfectMatchingCount

namespace D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight



theorem strict_coefficient_non_arc (m : ℕ) (hm : 1 ≤ m) (σ : Stationing (2 * m))
    (hσ : ¬ isArc m σ) : |psi m σ| < K m := by
  classical
  have crossing_balanced (m : ℕ) := (pairing_data m).1
  have K_positive (m : ℕ) := (pairing_data m).2.1.1
  have abs_psi_block (m : ℕ) := (pairing_data m).2.1.2.1
  have psi_zero_of_unbalanced (m : ℕ) := (pairing_data m).2.1.2.2.1
  have strict_coefficient_interleaving (m : ℕ) := (pairing_data m).2.2.1
  have psi_shift (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (σ : Stationing (2 * m)) :
      psi m (shift m σ) = -psi m σ := (pairing_data m).2.2.2.1 hm σ
  have shift_iterate_apply (m : ℕ) := (pairing_data m).2.2.2.2.1
  have shift_iterate_sub (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (j : ℕ) (i : Fin (2 * m)) :
      ((shift m)^[j]) σ i = σ (i - (j : Fin (2 * m))) :=
    (pairing_data m).2.2.2.2.2 hm σ j i
  have card_down_eq (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      Fintype.card (Down m σ) = m := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
    simpa [Down, Fintype.card_subtype, balanced] using hσ
  have card_up_eq (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      Fintype.card (Up m σ) = m := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
    classical
    have he := Fintype.card_congr (Equiv.sumCompl (fun i : Fin (2 * m) => σ i = true))
    simp only [Fintype.card_sum, Fintype.card_fin] at he
    change Fintype.card (Down m σ) + Fintype.card (Up m σ) = 2 * m at he
    rw [card_down_eq m σ hσ] at he
    omega
  have convex_or_complement_convex {n : ℕ} (σ : Fin n → Bool)
      (hDU : ∀ a b c d, a < b → b < c → c < d →
        σ a = true → σ b = false → σ c = true → σ d = false → False)
      (hUD : ∀ a b c d, a < b → b < c → c < d →
        σ a = false → σ b = true → σ c = false → σ d = true → False) :
      (∀ a b c, a < b → b < c → σ a = true → σ c = true → σ b = true) ∨
      (∀ a b c, a < b → b < c → σ a = false → σ c = false → σ b = false) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq
    classical
    by_cases hd : ∀ a b c, a < b → b < c → σ a = true → σ c = true → σ b = true
    · exact Or.inl hd
    · right
      push Not at hd
      obtain ⟨a, b, c, hab, hbc, ha, hc, hb⟩ := hd
      have hb' : σ b = false := Bool.eq_false_of_not_eq_true hb
      intro u v w huv hvw hu hw
      by_contra hv
      have hv' : σ v = true := Bool.eq_true_of_not_eq_false hv
      have hua : u ≠ a := by
        intro he
        rw [he, ha] at hu
        cases hu
      rcases lt_or_gt_of_ne hua with hlt | hgt
      · exact hUD u a b c hlt hab hbc hu ha hb' hc
      · exact hDU a u v w hgt huv hvw ha hu hv' hw
  have linear_interval_is_arc (m : ℕ) (hm : 1 ≤ m) (σ : Stationing (2 * m))
      (a : ℕ) (ha : a + m ≤ 2 * m)
      (hσ : ∀ i, σ i = decide (a ≤ i.val ∧ i.val < a + m)) : isArc m σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply card_down_eq card_up_eq
      convex_or_complement_convex
    have : NeZero (2 * m) := ⟨by omega⟩
    refine ⟨a, ?_⟩
    funext i
    rw [shift_iterate_sub m hm]
    rw [hσ i]
    unfold block
    have hav : (a : Fin (2 * m)).val = a := Fin.val_cast_of_lt (by omega)
    rw [Fin.sub_def]
    simp only [hav]
    congr 1
    apply propext
    by_cases hi : a ≤ i.val
    · have he : 2 * m - a + i.val = i.val - a + 2 * m := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - a < 2 * m)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega : 2 * m - a + i.val < 2 * m)]
      omega
  have convex_color_interval {n k : ℕ} (hk : 0 < k) (σ : Fin n → Bool) (c : Bool)
      (hcard : (Finset.univ.filter (fun i => σ i = c)).card = k)
      (hconv : ∀ a b d, a < b → b < d → σ a = c → σ d = c → σ b = c) :
      ∃ a : ℕ, a + k ≤ n ∧ ∀ i, σ i = c ↔ a ≤ i.val ∧ i.val < a + k := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq convex_or_complement_convex linear_interval_is_arc
    classical
    let D := Finset.univ.filter (fun i => σ i = c)
    have hn : D.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hk)
    let a := D.min' hn
    let b := D.max' hn
    have ha : σ a = c := (Finset.mem_filter.mp (Finset.min'_mem D hn)).2
    have hb : σ b = c := (Finset.mem_filter.mp (Finset.max'_mem D hn)).2
    have hab : a ≤ b := Finset.min'_le D b (Finset.max'_mem D hn)
    have he (i : Fin n) : σ i = c ↔ a ≤ i ∧ i ≤ b := by
      constructor
      · intro hi
        have hd : i ∈ D := by simp [D, hi]
        exact ⟨Finset.min'_le D i hd, Finset.le_max' D i hd⟩
      · rintro ⟨hai, hib⟩
        rcases eq_or_lt_of_le hai with hei | hli
        · simpa [← hei] using ha
        rcases eq_or_lt_of_le hib with hei | hri
        · simpa [hei] using hb
        exact hconv a i b hli hri ha hb
    have hD : D = Finset.Icc a b := by ext i; simp [D, he]
    have hc : b.val + 1 - a.val = k := by
      change D.card = k at hcard
      rw [hD, Fin.card_Icc] at hcard
      exact hcard
    refine ⟨a.val, ?_, ?_⟩
    · have hbn := b.isLt
      change a.val ≤ b.val at hab
      omega
    · intro i
      rw [he i]
      change (a.val ≤ i.val ∧ i.val ≤ b.val) ↔ _
      change a.val ≤ b.val at hab
      omega
  have singlet_not (a b : Bool) : s (!a) (!b) = -s a b := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq convex_or_complement_convex linear_interval_is_arc convex_color_interval
    cases a <;> cases b <;> decide
  have term_not (m : ℕ) (σ : Stationing (2 * m)) (f : FixedPointFreeInvolution (Fin (2 * m))) :
      term m (fun i => !(σ i)) f = (-1 : ℤ) ^ m * term m σ f := by
    clear K_positive abs_psi_block psi_zero_of_unbalanced strict_coefficient_interleaving psi_shift
      shift_iterate_apply shift_iterate_sub card_down_eq card_up_eq convex_or_complement_convex
      linear_interval_is_arc convex_color_interval
    let orient : Stationing (2 * m) := fun i => decide (i < f.val i)
    have hc : crossing orient f := by
      intro i
      have hn := (f.prop.2 i)
      rcases lt_or_gt_of_ne hn with hi | hi
      · simp [orient, (f.prop.1 i), hi, not_lt_of_gt hi]
      · simp [orient, (f.prop.1 i), hi, not_lt_of_gt hi]
    have hh := crossing_balanced m orient f hc
    have hcard : (Finset.univ.filter (fun i => i < f.val i)).card = m := by
      simpa [balanced, orient] using hh
    unfold term
    simp_rw [singlet_not]
    rw [Finset.prod_neg, hcard]
  have psi_not (m : ℕ) (σ : Stationing (2 * m)) :
      psi m (fun i => !(σ i)) = (-1 : ℤ) ^ m * psi m σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq convex_or_complement_convex linear_interval_is_arc convex_color_interval
      singlet_not
    unfold psi
    simp_rw [term_not]
    rw [Finset.mul_sum]
  have abs_psi_not (m : ℕ) (σ : Stationing (2 * m)) :
      |psi m (fun i => !(σ i))| = |psi m σ| := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq convex_or_complement_convex linear_interval_is_arc convex_color_interval
      singlet_not term_not
    rw [psi_not, abs_mul]
    simp
  have balanced_not (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      balanced m (fun i => !(σ i)) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      convex_or_complement_convex linear_interval_is_arc convex_color_interval singlet_not term_not
      psi_not abs_psi_not
    have hc := card_up_eq m σ hσ
    have he : Finset.univ.filter (fun i => σ i ≠ true) =
        Finset.univ.filter (fun i => (!(σ i)) = true) := by
      ext i
      cases hs : σ i <;> simp
    unfold balanced
    rw [← he]
    simpa only [Up, Fintype.card_subtype] using hc
  have iterate_shift_not (m : ℕ) (σ : Stationing (2 * m)) (j : ℕ) :
      ((shift m)^[j]) (fun i => !(σ i)) = fun i => !(((shift m)^[j]) σ i) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_sub card_down_eq card_up_eq
      convex_or_complement_convex linear_interval_is_arc convex_color_interval singlet_not term_not
      psi_not abs_psi_not balanced_not
    funext i
    simp only [shift_iterate_apply]
  have not_block_half_shift (m : ℕ) (hm : 1 ≤ m) :
      (fun i => !(block m i)) = ((shift m)^[m]) (block m) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply card_down_eq card_up_eq
      convex_or_complement_convex linear_interval_is_arc convex_color_interval singlet_not term_not
      psi_not abs_psi_not balanced_not iterate_shift_not
    funext i
    have : NeZero (2 * m) := ⟨by omega⟩
    rw [shift_iterate_sub m hm]
    simp only [block]
    have hmv : (m : Fin (2 * m)).val = m := Fin.val_cast_of_lt (by omega)
    rw [Fin.sub_def]
    simp only [hmv]
    by_cases hi : m ≤ i.val
    · have he : 2 * m - m + i.val = i.val - m + 2 * m := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - m < 2 * m)]
      simp [show ¬i.val < m by omega, show i.val - m < m by omega]
    · rw [Nat.mod_eq_of_lt (by omega : 2 * m - m + i.val < 2 * m)]
      simp [show i.val < m by omega, show ¬2 * m - m + i.val < m by omega]
  have not_arc_iff (m : ℕ) (hm : 1 ≤ m) (σ : Stationing (2 * m)) :
      isArc m (fun i => !(σ i)) ↔ isArc m σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq convex_or_complement_convex linear_interval_is_arc convex_color_interval
      singlet_not term_not psi_not abs_psi_not balanced_not
    have hforward (τ : Stationing (2 * m)) (hτ : isArc m τ) : isArc m (fun i => !(τ i)) := by
      obtain ⟨j, rfl⟩ := hτ
      refine ⟨j + m, ?_⟩
      rw [← iterate_shift_not, not_block_half_shift m hm, Function.iterate_add_apply]
    constructor
    · intro h
      simpa using hforward (fun i => !(σ i)) h
    · exact hforward σ
  have no_interleave_is_arc (m : ℕ) (hm : 1 ≤ m) (σ : Stationing (2 * m))
      (hσ : balanced m σ)
      (hDU : ∀ a b c d, a < b → b < c → c < d →
        σ a = true → σ b = false → σ c = true → σ d = false → False)
      (hUD : ∀ a b c d, a < b → b < c → c < d →
        σ a = false → σ b = true → σ c = false → σ d = true → False) : isArc m σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub card_down_eq
      card_up_eq singlet_not term_not psi_not abs_psi_not iterate_shift_not not_block_half_shift
    rcases convex_or_complement_convex σ hDU hUD with hc | hc
    · obtain ⟨a, ha, he⟩ := convex_color_interval (by omega : 0 < m) σ true hσ hc
      apply linear_interval_is_arc m hm σ a ha
      intro i
      apply Bool.eq_iff_iff.mpr
      simpa using he i
    · have hnot := balanced_not m σ hσ
      have hc' : ∀ a b c, a < b → b < c → (!σ a) = true → (!σ c) = true → (!σ b) = true := by
        simpa using hc
      obtain ⟨a, ha, he⟩ := convex_color_interval (by omega : 0 < m)
        (fun i => !(σ i)) true hnot hc'
      apply (not_arc_iff m hm σ).mp
      apply linear_interval_is_arc m hm (fun i => !(σ i)) a ha
      intro i
      apply Bool.eq_iff_iff.mpr
      simpa using he i
  by_cases hs : balanced m σ
  · by_contra hbound
    apply hσ
    refine no_interleave_is_arc m hm σ hs ?_ ?_
    · intro a b c d hab hbc hcd ha hb hc hd
      have hlt := strict_coefficient_interleaving m σ hs
        (⟨a, ha⟩ : Down m σ) (⟨c, hc⟩ : Down m σ)
        (⟨b, by simp [hb]⟩ : Up m σ) (⟨d, by simp [hd]⟩ : Up m σ) hab hbc hcd
      exact hbound hlt
    · intro a b c d hab hbc hcd ha hb hc hd
      have hlt := strict_coefficient_interleaving m (fun i => !(σ i)) (balanced_not m σ hs)
        (⟨a, by simp [ha]⟩ : Down m (fun i => !(σ i)))
        (⟨c, by simp [hc]⟩ : Down m (fun i => !(σ i)))
        (⟨b, by simp [hb]⟩ : Up m (fun i => !(σ i)))
        (⟨d, by simp [hd]⟩ : Up m (fun i => !(σ i))) hab hbc hcd
      rw [abs_psi_not] at hlt
      exact hbound hlt
  · rw [psi_zero_of_unbalanced m σ hs]
    have hk := K_positive m
    simpa using hk

#print axioms strict_coefficient_non_arc

end D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight
