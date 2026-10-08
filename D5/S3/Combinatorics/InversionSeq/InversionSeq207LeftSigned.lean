/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftSigned
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftSigned
   mirror-E: none(waiver:left-signed-continuation-reduction)
   anchors: []
   utility: none
   digest: Degree induction and reserve telescoping identify the left signed walk recursion. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftSigned

open InversionSeq207LeftTree InversionSeq207LeftReduction

def leftSignedCount : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | depth + 1, reserve, gap =>
      (∑ index ∈ Finset.range gap, leftSignedCount depth (reserve + 1) index) +
        (∑ distance ∈ Finset.range (reserve + 1),
          leftSignedCount depth (reserve - distance) (gap + distance)) +
        leftSignedCount depth (reserve + 1) 0 - leftSignedCount depth 0 0

theorem left_signed_reduction (depth : ℕ) :
    ∀ reserve gap : ℕ,
      (leftCount depth (List.replicate gap false) (reserve + 1) false : ℤ) =
        leftSignedCount depth reserve gap := by
  have hcorrection (length gap capacity : ℕ) :
      leftCorrection length (List.replicate gap false ++ [true]) capacity =
        (leftCount length [false] capacity false : ℤ) -
          leftCount length [] capacity false := by
    induction gap with
    | zero => simp [leftCorrection]
    | succ gap ih => simpa [List.replicate_succ, leftCorrection] using ih
  have hhigh (length gap capacity : ℕ) :
      (leftCount length (List.replicate gap false ++ [true]) capacity true : ℤ) =
        leftCount length (List.replicate gap false) capacity false +
          (leftCount length [] (capacity + 1) false : ℤ) -
            leftCount length [] capacity false := by
    have hlinear := left_linear_reduction length
      (List.replicate gap false ++ [true]) capacity true
      (fun _ => ⟨List.replicate gap false, rfl⟩)
    simp only [List.count_append, List.count_replicate_self,
      List.count_cons_of_ne (by decide : true ≠ false), List.count_nil, Nat.add_zero,
      ite_true] at hlinear
    rw [hcorrection] at hlinear
    omega
  induction depth with
  | zero => intro reserve gap; rfl
  | succ depth ih =>
      intro reserve gap
      have hsplit :
          (leftCount (depth + 1) (List.replicate gap false) (reserve + 1) false : ℤ) =
            (∑ index ∈ Finset.range gap,
              (leftCount depth (List.replicate index false) (reserve + 2) false : ℤ)) +
            ∑ distance ∈ Finset.range (reserve + 1),
              (leftCount depth (List.replicate (gap + distance) false ++ [true])
                (reserve + 1 - distance) true : ℤ) := by
        simp only [leftCount, Nat.cast_sum, List.length_replicate]
        rw [Finset.sum_range_add]
        congr 1
        · apply Finset.sum_congr rfl
          intro index hindex
          have hindex' : index < gap := Finset.mem_range.mp hindex
          have htake : (List.replicate gap false).take index = List.replicate index false := by
            simp [List.take_replicate, Nat.min_eq_left (Nat.le_of_lt hindex')]
          simp [leftChild, hindex', htake]
        · apply Finset.sum_congr rfl
          intro distance _hdistance
          simp [leftChild, Nat.not_lt.mpr (Nat.le_add_right _ _)]
      have htelescoping :
          (∑ distance ∈ Finset.range (reserve + 1),
            ((leftCount depth [] (reserve + 1 - distance + 1) false : ℤ) -
              leftCount depth [] (reserve + 1 - distance) false)) =
            (leftCount depth [] (reserve + 2) false : ℤ) -
              leftCount depth [] 1 false := by
        rw [← Finset.sum_range_reflect]
        have hindices :
            (∑ distance ∈ Finset.range (reserve + 1),
              ((leftCount depth [] (reserve + 1 - (reserve + 1 - 1 - distance) + 1)
                  false : ℤ) -
                leftCount depth [] (reserve + 1 - (reserve + 1 - 1 - distance)) false)) =
              ∑ distance ∈ Finset.range (reserve + 1),
                ((leftCount depth [] (distance + 2) false : ℤ) -
                  leftCount depth [] (distance + 1) false) := by
          apply Finset.sum_congr rfl
          intro distance hdistance
          have hdistance' := Finset.mem_range.mp hdistance
          have hcapacity : reserve + 1 - (reserve + 1 - 1 - distance) = distance + 1 := by
            omega
          rw [hcapacity]
        rw [hindices]
        exact Finset.sum_range_sub (fun index => (leftCount depth [] (index + 1) false : ℤ))
          (reserve + 1)
      rw [hsplit]
      simp_rw [hhigh]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hsums :
          (∑ distance ∈ Finset.range (reserve + 1),
            (leftCount depth [] (reserve + 1 - distance + 1) false : ℤ)) -
              ∑ distance ∈ Finset.range (reserve + 1),
                (leftCount depth [] (reserve + 1 - distance) false : ℤ) =
            (leftCount depth [] (reserve + 2) false : ℤ) -
              leftCount depth [] 1 false := by
        rw [← Finset.sum_sub_distrib]
        exact htelescoping
      have hlow :
          (∑ index ∈ Finset.range gap,
            (leftCount depth (List.replicate index false) (reserve + 2) false : ℤ)) =
              ∑ index ∈ Finset.range gap, leftSignedCount depth (reserve + 1) index := by
        apply Finset.sum_congr rfl
        intro index _hindex
        exact ih (reserve + 1) index
      have hupper :
          (∑ distance ∈ Finset.range (reserve + 1),
            (leftCount depth (List.replicate (gap + distance) false)
              (reserve + 1 - distance) false : ℤ)) =
              ∑ distance ∈ Finset.range (reserve + 1),
                leftSignedCount depth (reserve - distance) (gap + distance) := by
        apply Finset.sum_congr rfl
        intro distance hdistance
        have hdistance' := Finset.mem_range.mp hdistance
        have hcapacity : reserve + 1 - distance = reserve - distance + 1 := by omega
        rw [hcapacity]
        exact ih (reserve - distance) (gap + distance)
      have hnext := ih (reserve + 1) 0
      have hroot := ih 0 0
      simp only [List.replicate_zero, Nat.zero_add] at hnext hroot
      rw [show reserve + 1 + 1 = reserve + 2 by omega] at hnext
      rw [hlow, hupper]
      simp only [leftSignedCount]
      omega

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftSigned
