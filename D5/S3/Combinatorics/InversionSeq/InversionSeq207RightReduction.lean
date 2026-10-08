/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207RightReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207RightReduction
   mirror-E: none(waiver:right-signed-continuation-reduction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Induction identifies the four-type right tree with its signed two-label walks. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207RightReduction

inductive RightType where
  | diagonal
  | unbanned
  | lowerBanned
  | upperBanned

def rightCount : ℕ → RightType → ℕ → ℕ → ℤ
  | 0, _, _, _ => 1
  | depth + 1, .diagonal, reserve, _ =>
      rightCount depth .diagonal (reserve + 1) 0 +
        ∑ distance ∈ Finset.range reserve,
          rightCount depth .unbanned (reserve - distance) (distance + 1)
  | depth + 1, .unbanned, reserve, gap =>
      rightCount depth .diagonal (reserve + 1) 0 +
        (∑ distance ∈ Finset.range reserve,
          rightCount depth .unbanned (reserve - distance) (distance + 1)) +
        ∑ distance ∈ Finset.range gap,
          rightCount depth .upperBanned (reserve + 1) (distance + 1)
  | depth + 1, .lowerBanned, reserve, gap =>
      rightCount depth .diagonal (reserve + 1) 0 +
        (∑ distance ∈ Finset.range reserve,
          rightCount depth .unbanned (reserve - distance) (distance + 1)) +
        ∑ distance ∈ Finset.range (gap - 1),
          rightCount depth .upperBanned (reserve + 1) (distance + 1)
  | depth + 1, .upperBanned, reserve, gap =>
      (∑ distance ∈ Finset.range gap,
        rightCount depth .upperBanned (reserve + 1) (distance + 1)) +
        ∑ distance ∈ Finset.range reserve,
          rightCount depth .lowerBanned (reserve - distance) (distance + 1)

def rightSignedCount : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | depth + 1, reserve, gap =>
      (1 - (gap : ℤ)) * rightSignedCount depth (reserve + 1) 0 +
        (gap : ℤ) * rightSignedCount depth reserve 0 +
        (∑ distance ∈ Finset.range reserve,
          rightSignedCount depth (reserve - distance) (distance + 1)) +
        ∑ distance ∈ Finset.range gap,
          rightSignedCount depth (reserve + 1) (distance + 1)

theorem right_signed_reduction (depth : ℕ) :
    ∀ reserve gap : ℕ,
      rightCount depth .unbanned reserve gap = rightSignedCount depth reserve gap := by
  have hdiagonal (length reserve : ℕ) :
      rightCount length .unbanned reserve 0 = rightCount length .diagonal reserve 0 := by
    cases length <;> simp [rightCount]
  have hshift (length reserve gap : ℕ) :
      rightCount length .lowerBanned reserve (gap + 1) =
        rightCount length .unbanned reserve gap := by
    cases length <;> simp [rightCount]
  have hdifference (length reserve gap : ℕ) :
      rightCount length .unbanned (reserve + 1) gap -
          rightCount length .upperBanned (reserve + 1) gap =
        rightCount length .diagonal (reserve + 1) 0 -
          rightCount length .diagonal reserve 0 := by
    cases length with
    | zero => simp [rightCount]
    | succ length =>
        have hhigh :
            (∑ distance ∈ Finset.range (reserve + 1),
              rightCount length .lowerBanned (reserve + 1 - distance) (distance + 1)) =
              rightCount (length + 1) .diagonal reserve 0 := by
          simp_rw [hshift]
          rw [Finset.sum_range_succ']
          have htail :
              (∑ distance ∈ Finset.range reserve,
                rightCount length .unbanned (reserve + 1 - (distance + 1))
                  (distance + 1)) =
              ∑ distance ∈ Finset.range reserve,
                rightCount length .unbanned (reserve - distance) (distance + 1) := by
            apply Finset.sum_congr rfl
            intro distance hdistance
            congr 1; omega
          rw [htail, hdiagonal]
          simp only [Nat.sub_zero, rightCount]
          ring
        change _ - ((∑ distance ∈ Finset.range gap,
          rightCount length .upperBanned (reserve + 1 + 1) (distance + 1)) +
          ∑ distance ∈ Finset.range (reserve + 1),
            rightCount length .lowerBanned (reserve + 1 - distance) (distance + 1)) = _
        rw [hhigh]
        simp only [rightCount]
        ring
  induction depth with
  | zero => intro reserve gap; rfl
  | succ depth ih =>
      intro reserve gap
      have hupper (distance : ℕ) :
          rightCount depth .upperBanned (reserve + 1) (distance + 1) =
          rightCount depth .unbanned (reserve + 1) (distance + 1) -
            rightCount depth .diagonal (reserve + 1) 0 +
            rightCount depth .diagonal reserve 0 := by
        have := hdifference depth reserve (distance + 1)
        omega
      simp only [rightCount, rightSignedCount]
      simp_rw [hupper]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← hdiagonal depth (reserve + 1), ← hdiagonal depth reserve]
      simp_rw [ih]
      ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq207RightReduction
