/- GID: D5/S3/Combinatorics/PathAlignedPacking/UpperFive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/UpperFive
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: Every nonexceptional path-aligned cycle chain has a packing five-colouring. -/

import D5.S3.Combinatorics.PathAlignedPacking.Base3_3
import D5.S3.Combinatorics.PathAlignedPacking.Base3_4
import D5.S3.Combinatorics.PathAlignedPacking.Base3_5
import D5.S3.Combinatorics.PathAlignedPacking.Base3_6
import D5.S3.Combinatorics.PathAlignedPacking.Base3_7
import D5.S3.Combinatorics.PathAlignedPacking.Base3_8
import D5.S3.Combinatorics.PathAlignedPacking.Base4_4
import D5.S3.Combinatorics.PathAlignedPacking.Base4_5
import D5.S3.Combinatorics.PathAlignedPacking.Base4_6
import D5.S3.Combinatorics.PathAlignedPacking.Base4_7
import D5.S3.Combinatorics.PathAlignedPacking.Base4_8
import D5.S3.Combinatorics.PathAlignedPacking.Base5_5
import D5.S3.Combinatorics.PathAlignedPacking.Base5_6
import D5.S3.Combinatorics.PathAlignedPacking.Base5_7
import D5.S3.Combinatorics.PathAlignedPacking.Base5_8
import D5.S3.Combinatorics.PathAlignedPacking.Base6_6
import D5.S3.Combinatorics.PathAlignedPacking.Base6_7
import D5.S3.Combinatorics.PathAlignedPacking.Base6_8
import D5.S3.Combinatorics.PathAlignedPacking.Base7_7
import D5.S3.Combinatorics.PathAlignedPacking.Base7_8
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8
import D5.S3.Combinatorics.PathAlignedPacking.Base4_2
import D5.S3.Combinatorics.PathAlignedPacking.Base5_2
import D5.S3.Combinatorics.PathAlignedPacking.Base6_2
import D5.S3.Combinatorics.PathAlignedPacking.Base7_2
import D5.S3.Combinatorics.PathAlignedPacking.Base8_2
import D5.S3.Combinatorics.PathAlignedPacking.Base3_1
import D5.S3.Combinatorics.PathAlignedPacking.Base7_1
import D5.S3.Combinatorics.PathAlignedPacking.Base8_1
import D5.S3.Combinatorics.PathAlignedPacking.Base9_1
import D5.S3.Combinatorics.PathAlignedPacking.Base10_1
import D5.S3.Combinatorics.PathAlignedPacking.Base5_1
import D5.S3.Combinatorics.PathAlignedPacking.Base6_1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.UpperFive

open Defs
open D5.S3.Combinatorics.PathAlignedPacking.Metric

/-- The preregistered upper bound for every nonexceptional cycle. -/
theorem result : claimUpperFive := by
  have reduce (L : ℤ) (hL : 3 ≤ L) :
      ∃ i : Fin 6, ∃ k : ℤ, 0 ≤ k ∧ L = 3 + (i.val : ℤ) + 4 * k ∧
        (i.val < 2 → k = 0) := by
    by_cases h3 : L = 3
    · exact ⟨0, 0, by omega, by simp [h3], by simp⟩
    by_cases h4 : L = 4
    · exact ⟨1, 0, by omega, by simp [h4], by simp⟩
    have h5 : 5 ≤ L := by omega
    refine ⟨⟨2 + ((L - 5) % 4).toNat, by omega⟩, (L - 5) / 4,
      by omega, by dsimp; omega, by dsimp; omega⟩

  have many_arcs (a b : ℤ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
      HasMetricColor a b 5 := by
    obtain ⟨i, ka, hka, ea, za⟩ := reduce a ha
    obtain ⟨j, kb, hkb, eb, zb⟩ := reduce b hb
    rw [ea, eb]
    fin_cases i <;> norm_num at *
    · fin_cases j <;> norm_num at *
      · simpa using Base3_3.colouring ka kb hka hkb (by omega) (by omega)
      · simpa using Base3_4.colouring ka kb hka hkb (by omega) (by omega)
      · simpa using Base3_5.colouring ka kb hka hkb (by omega)
      · simpa using Base3_6.colouring ka kb hka hkb (by omega)
      · simpa using Base3_7.colouring ka kb hka hkb (by omega)
      · simpa using Base3_8.colouring ka kb hka hkb (by omega)
    · fin_cases j <;> norm_num at *
      · simpa using metric_swap (3 + 4 * kb) (4 + 4 * ka) 5 (by omega) (by omega)
          (Base3_4.colouring kb ka hkb hka (by omega) (by omega))
      · simpa using Base4_4.colouring ka kb hka hkb (by omega) (by omega)
      · simpa using Base4_5.colouring ka kb hka hkb (by omega)
      · simpa using Base4_6.colouring ka kb hka hkb (by omega)
      · simpa using Base4_7.colouring ka kb hka hkb (by omega)
      · simpa using Base4_8.colouring ka kb hka hkb (by omega)
    · fin_cases j <;> norm_num at *
      · simpa using metric_swap (3 + 4 * kb) (5 + 4 * ka) 5 (by omega) (by omega)
          (Base3_5.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (4 + 4 * kb) (5 + 4 * ka) 5 (by omega) (by omega)
          (Base4_5.colouring kb ka hkb hka (by omega))
      · simpa using Base5_5.colouring ka kb hka hkb
      · simpa using Base5_6.colouring ka kb hka hkb
      · simpa using Base5_7.colouring ka kb hka hkb
      · simpa using Base5_8.colouring ka kb hka hkb
    · fin_cases j <;> norm_num at *
      · simpa using metric_swap (3 + 4 * kb) (6 + 4 * ka) 5 (by omega) (by omega)
          (Base3_6.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (4 + 4 * kb) (6 + 4 * ka) 5 (by omega) (by omega)
          (Base4_6.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (5 + 4 * kb) (6 + 4 * ka) 5 (by omega) (by omega)
          (Base5_6.colouring kb ka hkb hka)
      · simpa using Base6_6.colouring ka kb hka hkb
      · simpa using Base6_7.colouring ka kb hka hkb
      · simpa using Base6_8.colouring ka kb hka hkb
    · fin_cases j <;> norm_num at *
      · simpa using metric_swap (3 + 4 * kb) (7 + 4 * ka) 5 (by omega) (by omega)
          (Base3_7.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (4 + 4 * kb) (7 + 4 * ka) 5 (by omega) (by omega)
          (Base4_7.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (5 + 4 * kb) (7 + 4 * ka) 5 (by omega) (by omega)
          (Base5_7.colouring kb ka hkb hka)
      · simpa using metric_swap (6 + 4 * kb) (7 + 4 * ka) 5 (by omega) (by omega)
          (Base6_7.colouring kb ka hkb hka)
      · simpa using Base7_7.colouring ka kb hka hkb
      · simpa using Base7_8.colouring ka kb hka hkb
    · fin_cases j <;> norm_num at *
      · simpa using metric_swap (3 + 4 * kb) (8 + 4 * ka) 5 (by omega) (by omega)
          (Base3_8.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (4 + 4 * kb) (8 + 4 * ka) 5 (by omega) (by omega)
          (Base4_8.colouring kb ka hkb hka (by omega))
      · simpa using metric_swap (5 + 4 * kb) (8 + 4 * ka) 5 (by omega) (by omega)
          (Base5_8.colouring kb ka hkb hka)
      · simpa using metric_swap (6 + 4 * kb) (8 + 4 * ka) 5 (by omega) (by omega)
          (Base6_8.colouring kb ka hkb hka)
      · simpa using metric_swap (7 + 4 * kb) (8 + 4 * ka) 5 (by omega) (by omega)
          (Base7_8.colouring kb ka hkb hka)
      · simpa using Base8_8.colouring ka kb hka hkb

  have reduce_from (L c : ℤ) (hL : c ≤ L) :
      ∃ i : Fin 4, ∃ k : ℤ, 0 ≤ k ∧ L = c + (i.val : ℤ) + 4 * k := by
    exact ⟨⟨((L - c) % 4).toNat, by omega⟩, (L - c) / 4, by omega, by dsimp; omega⟩

  have one_arc (a : ℤ) (ha : 3 ≤ a) (hne : a + 1 ≠ 5) :
      HasMetricColor a 1 5 := by
    by_cases h3 : a = 3
    · subst a; simpa using Base3_1.colouring 0 0 (by omega) (by omega) rfl rfl
    by_cases h5 : a = 5
    · subst a; simpa using Base5_1.colouring 0 0 (by omega) (by omega) rfl rfl
    by_cases h6 : a = 6
    · subst a; simpa using Base6_1.colouring 0 0 (by omega) (by omega) rfl rfl
    obtain ⟨i, ka, hka, ea⟩ := reduce_from a 7 (by omega)
    rw [ea]
    fin_cases i <;> norm_num at *
    · simpa using Base7_1.colouring ka 0 hka (by omega) rfl
    · simpa using Base8_1.colouring ka 0 hka (by omega) rfl
    · simpa using Base9_1.colouring ka 0 hka (by omega) rfl
    · simpa using Base10_1.colouring ka 0 hka (by omega) rfl

  have two_arc (a : ℤ) (ha : 3 ≤ a) (hne : a + 2 ≠ 5) :
      HasMetricColor a 2 5 := by
    by_cases h4 : a = 4
    · subst a; simpa using Base4_2.colouring 0 0 (by omega) (by omega) rfl rfl
    obtain ⟨i, ka, hka, ea⟩ := reduce_from a 5 (by omega)
    rw [ea]
    fin_cases i <;> norm_num at *
    · simpa using Base5_2.colouring ka 0 hka (by omega) rfl
    · simpa using Base6_2.colouring ka 0 hka (by omega) rfl
    · simpa using Base7_2.colouring ka 0 hka (by omega) rfl
    · simpa using Base8_2.colouring ka 0 hka (by omega) rfl
  intro n t ℓ hn hn5 ht hℓ hℓn
  apply metric_to_packing n ℓ t 5 hℓ hℓn
  let a : ℤ := (ℓ - 1 : ℕ)
  let b : ℤ := (n - ℓ + 1 : ℕ)
  have ha : 3 ≤ a := by dsimp [a]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hab : a + b ≠ 5 := by dsimp [a, b]; omega
  change HasMetricColor a b 5
  by_cases hb1 : b = 1
  · rw [hb1]; exact one_arc a ha (by omega)
  by_cases hb2 : b = 2
  · rw [hb2]; exact two_arc a ha (by omega)
  exact many_arcs a b ha (by omega)

end D5.S3.Combinatorics.PathAlignedPacking.UpperFive
