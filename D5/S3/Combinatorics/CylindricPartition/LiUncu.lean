/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncu
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncu
   mirror-E: none(waiver:li-uncu-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted path deletion and Gaussian images prove the Li-Uncu identity. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuImages

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs

/-- Li and Uncu, Conjecture 1.3, equation (1.5). -/
theorem result : LiUncuDefs.claim := by
  classical
  intro n k i hk hi hik
  let H := k - 1
  let a : ℤ := k - i
  let p : ℤ := 2 * k + 1
  let c : ℤ := 2 * k - 2 * i + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have ha : 0 ≤ a := by dsimp [a]; omega
  have haH : a ≤ H := by dsimp [a, H]; omega
  have hp : 11 ≤ p := by dsimp [p]; omega
  have hc : 1 ≤ c ∧ c < p := by dsimp [c, p]; omega
  have hpa : (2 * H + 3 : ℤ) = p := by dsimp [H, p]; omega
  have hca : 2 * a + 1 = c := by dsimp [a, c]; ring
  have hia : (H : ℤ) + 1 - a = i := by dsimp [H, a]; omega
  have diagonal : lhs n k i = pathPolynomial H (2 * n) a a := by
    rw [lhs_path_expansion n k i (by omega) hi (by omega)]
    change (∑ N ∈ Finset.range (n + 1), refinedPathSum H a (2 * n) N) = _
    unfold refinedPathSum
    simp only [show ¬(2 * (n : ℤ) < 0) by omega, ite_false,
      show (2 * (n : ℤ)).toNat = 2 * n by omega]
    rw [Finset.sum_comm]
    unfold pathPolynomial
    apply Finset.sum_congr rfl
    intro w hw
    have words_mem (m : ℕ) (w : List Step) : w ∈ pathWords m ↔ w.length = m := by
      induction m generalizing w with
      | zero => simp [pathWords]
      | succ m ih =>
          cases w with
          | nil => simp [pathWords]
          | cons s w => cases s <;> simp [pathWords, ih]
    obtain ⟨e, he, hinv, hlen, hweight⟩ := peak_deletion_bijection
    have hn : (peakData w).2.1 + (peakData w).2.2.sum ≤ n := by
      have hl := hlen (e w)
      rw [e.symm_apply_apply, he w] at hl
      have hw' := (words_mem (2 * n) w).mp hw
      omega
    by_cases hv : ValidPath H a a w
    · simp only [hv, true_and, ite_true]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_range, hn]
    · simp [hv]
  have ordinary_support (v : ℤ) (hv : v < 0 ∨ (2 * n : ℕ) < v) :
      gaussInt (2 * n : ℕ) v = 0 := by
    rcases hv with hv | hv
    · simp only [gaussInt, if_pos (Or.inr hv)]
    · rw [gaussInt, if_neg (by omega)]
      exact gauss_zero_of_lt (2 * n) v.toNat (by omega)
  have complement (v : ℤ) : gaussInt (2 * n : ℕ) v =
      gaussInt (2 * n : ℕ) ((2 * n : ℕ) - v) := by
    by_cases hz : v = 0
    · subst v
      simp only [gaussInt, not_lt.mpr (Int.natCast_nonneg (2 * n)),
        lt_self_iff_false, or_self, ite_false, Int.toNat_natCast,
        sub_zero, Int.toNat_zero, gauss]
      have rectangle := gauss_rectangle 0 (2 * n)
      simp only [Nat.zero_add] at rectangle
      rw [rectangle]
      let w : {v : Fin (2 * n) → Fin 1 // Antitone v} :=
        ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
      symm
      rw [Finset.sum_eq_single w]
      · simp [w]
      · intro v _ hv
        exact (hv (Subtype.ext (funext fun j => Subsingleton.elim _ _))).elim
      · simp
    by_cases hv : v < 0 ∨ (2 * n : ℕ) < v
    · rw [ordinary_support v hv, ordinary_support _ (by omega)]
    · simp only [gaussInt, if_neg (by omega : ¬((↑(2 * n) : ℤ) < 0 ∨ v < 0)),
        if_neg (by omega : ¬((↑(2 * n) : ℤ) < 0 ∨ (2 * n : ℕ) - v < 0)),
        Int.toNat_natCast]
      rw [gauss_symmetry (2 * n) v.toNat (by omega)]
      congr 1; omega
  have outside (r : ℤ) (hr : r < -(n + 1 : ℤ) ∨ (n + 1 : ℤ) < r) :
      rightTerm n k i r = 0 := by
    let parity : ℤ := if Even r then 0 else -1
    have hpar : -1 ≤ parity ∧ parity ≤ 0 := by dsimp [parity]; split_ifs <;> omega
    have hv : (2 * (n : ℤ) - p * r + c * parity) / 2 < 0 ∨
        (2 * n : ℕ) < (2 * (n : ℤ) - p * r + c * parity) / 2 := by
      rcases hr with hr | hr
      · right
        have hp' : 0 ≤ p := by omega
        have hmul : p * r ≤ p * (-(n + 2 : ℤ)) := mul_le_mul_of_nonneg_left
          (by omega) hp'
        have hmul' : -c ≤ c * parity := by nlinarith [hc.1]
        have hnn : 2 * (n : ℤ) ≤ p * n :=
          mul_le_mul_of_nonneg_right (by omega) (by omega)
        have hnum : 4 * n + 2 ≤ 2 * (n : ℤ) - p * r + c * parity := by nlinarith
        omega
      · left
        have hp' : 0 ≤ p := by omega
        have hmul : p * (n + 2 : ℤ) ≤ p * r := mul_le_mul_of_nonneg_left
          (by omega) hp'
        have hmul' : c * parity ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) hpar.2
        have hnn : 2 * (n : ℤ) ≤ p * n :=
          mul_le_mul_of_nonneg_right (by omega) (by omega)
        have hnum : 2 * (n : ℤ) - p * r + c * parity < 0 := by nlinarith
        omega
    unfold rightTerm
    change (-1) ^ r.natAbs * X ^ _ *
      gaussInt (2 * n : ℕ) ((2 * (n : ℤ) - p * r + c * parity) / 2) = 0
    rw [ordinary_support _ hv, mul_zero]
  have finite : Function.HasFiniteSupport (rightTerm n k i) := by
    apply (Set.finite_Icc (-(n + 1 : ℤ)) (n + 1)).subset
    intro r hr
    by_contra hn
    exact hr (outside r (by simpa only [Set.mem_Icc, not_and_or, not_le] using hn))
  have rhs_all : rhs n k i = ∑ᶠ r : ℤ, rightTerm n k i r := by
    symm
    apply finsum_eq_sum_of_support_subset
    intro r hr
    by_contra hn
    exact hr (outside r (by simpa only [Finset.mem_coe, Finset.mem_Icc,
      not_and_or, not_le] using hn))
  let ev : Set ℤ := Set.range (fun t : ℤ => 2 * t)
  let od : Set ℤ := Set.range (fun t : ℤ => -2 * t - 1)
  have hdis : Disjoint ev od := by
    apply Set.disjoint_left.mpr
    rintro r ⟨t, ht⟩ ⟨u, hu⟩
    dsimp at ht hu
    omega
  have hunion : ev ∪ od = Set.univ := by
    ext r
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases he : r % 2 = 0
    · left
      exact ⟨r / 2, by dsimp; omega⟩
    · right
      exact ⟨(-r - 1) / 2, by dsimp; omega⟩
  have split : (∑ᶠ r : ℤ, rightTerm n k i r) =
      (∑ᶠ t : ℤ, rightTerm n k i (2 * t)) +
        (∑ᶠ t : ℤ, rightTerm n k i (-2 * t - 1)) := by
    rw [← finsum_mem_univ, ← hunion,
      finsum_mem_union' hdis (finite.inter_of_right ev) (finite.inter_of_right od)]
    have hev : Function.Injective (fun t : ℤ => 2 * t) := by
      intro x y h
      dsimp at h
      omega
    have hod : Function.Injective (fun t : ℤ => -2 * t - 1) := by
      intro x y h
      dsimp at h
      omega
    rw [finsum_mem_range hev, finsum_mem_range hod]
  have group_exp (r : ℤ) :
      r * ((2 * (k : ℤ) + 1) * r + 2 * k - 2 * i + 1) = r * (p * r + c) := by
    dsimp [p, c]
    ring
  have even_term (t : ℤ) : rightTerm n k i (2 * t) =
      X ^ (2 * p * t ^ 2 + c * t).toNat * gaussInt (2 * n : ℕ) (n - p * t) := by
    have he : Even (2 * t) := ⟨t, by ring⟩
    unfold rightTerm
    rw [if_pos he, he.natAbs.neg_one_pow, one_mul]
    push_cast
    rw [group_exp]
    have hexp : (2 * t) * (p * (2 * t) + c) = 2 * (2 * p * t ^ 2 + c * t) := by ring
    have hbot : 2 * (n : ℤ) - p * (2 * t) + c * 0 = 2 * ((n : ℤ) - p * t) := by ring
    change X ^ ((2 * t * (p * (2 * t) + c)) / 2).toNat *
      gaussInt (2 * (n : ℤ)) ((2 * (n : ℤ) - p * (2 * t) + c * 0) / 2) = _
    rw [hexp, hbot]
    simp
  have odd_term (t : ℤ) : rightTerm n k i (-2 * t - 1) =
      -(X ^ ((2 * t + 1) * (p * t + i)).toNat *
        gaussInt (2 * n : ℕ) (n - p * t - i)) := by
    have ho : Odd (-2 * t - 1) := ⟨-t - 1, by ring⟩
    have he : ¬Even (-2 * t - 1) := by rw [Int.even_iff]; omega
    unfold rightTerm
    rw [if_neg he, ho.natAbs.neg_one_pow]
    push_cast
    rw [group_exp]
    have hci : p - c = 2 * i := by dsimp [p, c]; ring
    have hexp : (-2 * t - 1) * (p * (-2 * t - 1) + c) =
        2 * ((2 * t + 1) * (p * t + i)) := by
      dsimp [p, c]
      ring
    have hbot : 2 * (n : ℤ) - p * (-2 * t - 1) + c * -1 =
        2 * ((n : ℤ) + p * t + i) := by linear_combination hci
    change (-1) * X ^ (((-2 * t - 1) * (p * (-2 * t - 1) + c)) / 2).toNat *
      gaussInt (2 * (n : ℤ)) ((2 * (n : ℤ) - p * (-2 * t - 1) + c * -1) / 2) = _
    rw [hexp, hbot]
    simp only [Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
    have hcomp := complement ((n : ℤ) + p * t + i)
    push_cast at hcomp
    rw [hcomp]
    rw [show 2 * (n : ℤ) - ((n : ℤ) + p * t + i) = (n : ℤ) - p * t - i by
      ring]
    ring
  have image_diagonal : imagePolynomial H (2 * n) a a =
      (∑ᶠ t : ℤ, X ^ (2 * p * t ^ 2 + c * t).toNat *
        gaussInt (2 * n : ℕ) (n - p * t)) -
      (∑ᶠ t : ℤ, X ^ ((2 * t + 1) * (p * t + i)).toNat *
        gaussInt (2 * n : ℕ) (n - p * t - i)) := by
    have kernel_even (z : ℤ) : imageKernel (2 * n) (2 * z) =
        gaussInt (2 * n : ℕ) ((n : ℤ) + z) := by
      have he : ((2 * n : ℕ) + 2 * z : ℤ) % 2 = 0 := by omega
      rw [imageKernel, if_pos he]
      congr 1; omega
    have kernel_odd (z : ℤ) : imageKernel (2 * n) (2 * z + 1) = 0 := by
      have he : ((2 * n : ℕ) + (2 * z + 1) : ℤ) % 2 ≠ 0 := by omega
      rw [imageKernel, if_neg he]
    unfold imagePolynomial
    rw [hpa, hca, hia]
    have argA (t : ℤ) : a - a - 2 * p * t = 2 * (-p * t) := by ring
    have argB (t : ℤ) : a + a + 1 + 2 * p * t = 2 * (a + p * t) + 1 := by ring
    have argE (t : ℤ) : a - p + 1 + a - 2 * p * t = 2 * (-p * t - i) := by
      have he : 2 * a + 1 - p = -2 * i := by dsimp [a, p]; ring
      linear_combination he
    have argF (t : ℤ) : a + p - a + 2 * p * t = 2 * ((p - 1) / 2 + p * t) + 1 := by
      have he : p % 2 = 1 := by dsimp [p]; omega
      have hpval : p = 2 * ((p - 1) / 2) + 1 := by omega
      linear_combination hpval
    simp only [argA, argB, argE, argF, kernel_even, kernel_odd, mul_zero, finsum_zero,
      add_zero, sub_zero]
    simp only [sub_eq_add_neg, neg_mul, add_assoc]
  rw [diagonal, ← path_image_formula H hH a a ha haH ha haH (2 * n),
    image_diagonal, rhs_all, split]
  simp only [even_term, odd_term]
  rw [finsum_neg_distrib]
  rfl

end D5.S3.Combinatorics.CylindricPartition.LiUncu
