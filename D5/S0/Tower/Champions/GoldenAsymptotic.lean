/- GID: D5/S0/Tower/Champions/GoldenAsymptotic
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/GoldenAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden champion follows a three-phase gap orbit with exact liminf arm. -/

import D5.S0.Tower.GoldenSubstitution
import D5.S0.Tower.MetricGeometry.GoldenSurvivor

/- Library-search audit trail (2026-08-16):
   * Repository search found the frozen golden gap substitution, survivor carrier,
     champion closed form, and the level-five through level-seven phase audit.
   * The historical Tribonacci champion module supplied the corresponding orbit-gap
     and liminf proof structure, but no golden three-phase orbit theorem.
   * Loogle confirmed `Filter.le_liminf_of_le`,
     `Filter.liminf_le_of_frequently_le`, and `Filter.frequently_atTop` in the pinned
     Mathlib.Order.LiminfLimsup API. Reservoir's queried package endpoint returned
     HTTP 404, and no third-party theorem is imported. -/

namespace D5.S0.Tower.Champions.GoldenAsymptotic

open D5.S0.Conventions
open D5.S0.Tower.GoldenChampionPoint
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenSubstitution
open D5.S0.Tower.MetricGeometry.GoldenSurvivor

local notation "φ" => Real.goldenRatio

/-- The two exact expressions for the source's asymptotic champion value agree. -/
theorem golden_asymptotic_value_identity :
    ((2 - φ) / 2 : Real) = φ ^ (-2 : Int) / 2 := by
  have hinvSq : φ ^ (-2 : Int) = 2 - φ := by
    rw [zpow_neg]
    norm_num only [zpow_ofNat]
    apply inv_eq_of_mul_eq_one_right
    nlinarith [Real.goldenRatio_sq]
  rw [hinvSq]

theorem golden_inverse_eq_sub_one : φ ^ (-1 : Int) = φ - 1 := by
  rw [zpow_neg, zpow_one]
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

theorem golden_inverse_square_eq_two_sub : φ ^ (-2 : Int) = 2 - φ := by
  linarith [golden_asymptotic_value_identity]

theorem golden_scale_succ (Q : Nat) :
    φ ^ (-(Q : Int)) = φ * φ ^ (-((Q + 1 : Nat) : Int)) := by
  calc
    φ ^ (-(Q : Int)) = φ ^ ((1 : Int) + -((Q + 1 : Nat) : Int)) := by
      congr 1
      push_cast
      omega
    _ = φ ^ (1 : Int) * φ ^ (-((Q + 1 : Nat) : Int)) := by
      rw [zpow_add₀ Real.goldenRatio_ne_zero]
    _ = φ * φ ^ (-((Q + 1 : Nat) : Int)) := by rw [zpow_one]

theorem golden_phase_b_sum : φ / 2 + φ ^ (-2 : Int) / 2 = 1 := by
  rw [golden_inverse_square_eq_two_sub]
  ring

theorem golden_phase_b_left_scale :
    φ / 2 * φ - 1 = φ ^ (-1 : Int) / 2 := by
  rw [golden_inverse_eq_sub_one]
  nlinarith [Real.goldenRatio_sq]

theorem golden_phase_b_right_scale :
    φ ^ (-2 : Int) / 2 * φ = φ ^ (-1 : Int) / 2 := by
  rw [golden_inverse_square_eq_two_sub, golden_inverse_eq_sub_one]
  nlinarith [Real.goldenRatio_sq]

theorem golden_inverse_mul : φ ^ (-1 : Int) * φ = 1 := by
  rw [golden_inverse_eq_sub_one]
  nlinarith [Real.goldenRatio_sq]

theorem golden_low_le_half : φ ^ (-2 : Int) / 2 ≤ (1 : Real) / 2 := by
  have hpow : φ ^ (-2 : Int) ≤ 1 := by
    simpa using zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le
      (by norm_num : (-2 : Int) ≤ 0)
  linarith

theorem golden_low_le_inverse_half :
    φ ^ (-2 : Int) / 2 ≤ φ ^ (-1 : Int) / 2 := by
  have hpow : φ ^ (-2 : Int) ≤ φ ^ (-1 : Int) := by
    exact zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by norm_num)
  linarith

/-- A containing adjacent gap records the normalized distances to its two endpoints. -/
def IsGoldenOrbitGap (Q : Nat) (x leftArm rightArm : Real) : Prop :=
  ∃ i : Fin (Nat.fib (Q + 2) - 1),
    x - indexedNameValue Q (goldenGapLeft Q i) =
        leftArm * φ ^ (-(Q : Int)) ∧
      indexedNameValue Q (goldenGapRight Q i) - x =
        rightArm * φ ^ (-(Q : Int))

theorem inserted_singleton_positions (Q : Nat)
    (i : Fin (Nat.fib (Q + 2) - 1))
    (j : Fin (Nat.fib (Q + 3)))
    (hset : insertedNameIndices Q i = {j}) :
    (levelEmbedding Q (goldenGapLeft Q i)).1 + 1 = j.1 ∧
      j.1 + 1 = (levelEmbedding Q (goldenGapRight Q i)).1 := by
  have hj : j ∈ insertedNameIndices Q i := by
    rw [hset]
    simp
  have hjbounds :
      levelEmbedding Q (goldenGapLeft Q i) < j ∧
        j < levelEmbedding Q (goldenGapRight Q i) := by
    change j ∈ Finset.Ioo (levelEmbedding Q (goldenGapLeft Q i))
      (levelEmbedding Q (goldenGapRight Q i)) at hj
    simpa only [Finset.mem_Ioo] using hj
  have hcard : (insertedNameIndices Q i).card = 1 := by
    rw [hset]
    simp
  change (Finset.Ioo (levelEmbedding Q (goldenGapLeft Q i))
    (levelEmbedding Q (goldenGapRight Q i))).card = 1 at hcard
  rw [Fin.card_Ioo] at hcard
  constructor <;> omega

theorem inserted_empty_positions (Q : Nat)
    (i : Fin (Nat.fib (Q + 2) - 1))
    (hset : insertedNameIndices Q i = ∅) :
    (levelEmbedding Q (goldenGapRight Q i)).1 =
      (levelEmbedding Q (goldenGapLeft Q i)).1 + 1 := by
  have hcard : (insertedNameIndices Q i).card = 0 := by
    rw [hset]
    simp
  change (Finset.Ioo (levelEmbedding Q (goldenGapLeft Q i))
    (levelEmbedding Q (goldenGapRight Q i))).card = 0 at hcard
  rw [Fin.card_Ioo] at hcard
  have hstrict :
      levelEmbedding Q (goldenGapLeft Q i) <
        levelEmbedding Q (goldenGapRight Q i) := by
    apply levelEmbedding_strictMono Q
    simp [goldenGapLeft, goldenGapRight]
  omega

/-- A large-gap midpoint refines to the large child at coordinate `phi/2`. -/
theorem golden_phase_a_to_b (Q : Nat) (hQ : 2 ≤ Q) (x : Real)
    (hgap : IsGoldenOrbitGap Q x (1 / 2) (1 / 2)) :
    IsGoldenOrbitGap (Q + 1) x (φ / 2) (φ ^ (-2 : Int) / 2) := by
  rcases hgap with ⟨i, hleft, hright⟩
  have hlarge :
      indexedNameValue Q (goldenGapRight Q i) -
          indexedNameValue Q (goldenGapLeft Q i) = φ ^ (-(Q : Int)) := by
    calc
      indexedNameValue Q (goldenGapRight Q i) -
            indexedNameValue Q (goldenGapLeft Q i) =
          (indexedNameValue Q (goldenGapRight Q i) - x) +
            (x - indexedNameValue Q (goldenGapLeft Q i)) := by ring
      _ = ((1 : Real) / 2 + 1 / 2) * φ ^ (-(Q : Int)) := by
        rw [hleft, hright]
        ring
      _ = φ ^ (-(Q : Int)) := by ring
  have hsubstitution := (golden_gap_substitution Q hQ i).2 (by
    simpa [goldenGapLeft, goldenGapRight] using hlarge)
  obtain ⟨j, hset, hjleft, _⟩ := hsubstitution
  change indexedNameValue (Q + 1) j -
      indexedNameValue Q (goldenGapLeft Q i) =
        φ ^ (-((Q + 1 : Nat) : Int)) at hjleft
  have hpositions := inserted_singleton_positions Q i j hset
  let next : Fin (Nat.fib ((Q + 1) + 2) - 1) :=
    ⟨(levelEmbedding Q (goldenGapLeft Q i)).1, by
      change (levelEmbedding Q (goldenGapLeft Q i)).1 < Nat.fib (Q + 3) - 1
      have hjbound := j.2
      omega⟩
  have hnextLeft :
      goldenGapLeft (Q + 1) next = levelEmbedding Q (goldenGapLeft Q i) := by
    apply Fin.ext
    simp [next, goldenGapLeft]
  have hnextRight : goldenGapRight (Q + 1) next = j := by
    apply Fin.ext
    simpa [next, goldenGapRight] using hpositions.1
  refine ⟨next, ?_, ?_⟩
  · rw [hnextLeft, levelEmbedding_value]
    calc
      x - indexedNameValue Q (goldenGapLeft Q i) =
          (1 / 2 : Real) * φ ^ (-(Q : Int)) := hleft
      _ = φ / 2 * φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q]
        ring
  · rw [hnextRight]
    calc
      indexedNameValue (Q + 1) j - x =
          (indexedNameValue (Q + 1) j -
            indexedNameValue Q (goldenGapLeft Q i)) -
              (x - indexedNameValue Q (goldenGapLeft Q i)) := by ring
      _ = φ ^ (-((Q + 1 : Nat) : Int)) -
          (1 / 2 : Real) * φ ^ (-(Q : Int)) := by rw [hjleft, hleft]
      _ = φ ^ (-2 : Int) / 2 * φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q, ← golden_asymptotic_value_identity]
        ring

/-- The right child of the coordinate-`phi/2` large gap is a small midpoint gap. -/
theorem golden_phase_b_to_c (Q : Nat) (hQ : 2 ≤ Q) (x : Real)
    (hgap : IsGoldenOrbitGap Q x (φ / 2) (φ ^ (-2 : Int) / 2)) :
    IsGoldenOrbitGap (Q + 1) x
      (φ ^ (-1 : Int) / 2) (φ ^ (-1 : Int) / 2) := by
  rcases hgap with ⟨i, hleft, hright⟩
  have hlarge :
      indexedNameValue Q (goldenGapRight Q i) -
          indexedNameValue Q (goldenGapLeft Q i) = φ ^ (-(Q : Int)) := by
    calc
      indexedNameValue Q (goldenGapRight Q i) -
            indexedNameValue Q (goldenGapLeft Q i) =
          (indexedNameValue Q (goldenGapRight Q i) - x) +
            (x - indexedNameValue Q (goldenGapLeft Q i)) := by ring
      _ = (φ / 2 + φ ^ (-2 : Int) / 2) * φ ^ (-(Q : Int)) := by
        rw [hleft, hright]
        ring
      _ = φ ^ (-(Q : Int)) := by rw [golden_phase_b_sum, one_mul]
  have hsubstitution := (golden_gap_substitution Q hQ i).2 (by
    simpa [goldenGapLeft, goldenGapRight] using hlarge)
  obtain ⟨j, hset, hjleft, _⟩ := hsubstitution
  change indexedNameValue (Q + 1) j -
      indexedNameValue Q (goldenGapLeft Q i) =
        φ ^ (-((Q + 1 : Nat) : Int)) at hjleft
  have hpositions := inserted_singleton_positions Q i j hset
  let next : Fin (Nat.fib ((Q + 1) + 2) - 1) :=
    ⟨j.1, by
      change j.1 < Nat.fib (Q + 3) - 1
      have hrightbound := (levelEmbedding Q (goldenGapRight Q i)).2
      omega⟩
  have hnextLeft : goldenGapLeft (Q + 1) next = j := by
    apply Fin.ext
    simp [next, goldenGapLeft]
  have hnextRight :
      goldenGapRight (Q + 1) next = levelEmbedding Q (goldenGapRight Q i) := by
    apply Fin.ext
    simpa [next, goldenGapRight] using hpositions.2
  refine ⟨next, ?_, ?_⟩
  · rw [hnextLeft]
    calc
      x - indexedNameValue (Q + 1) j =
          (x - indexedNameValue Q (goldenGapLeft Q i)) -
            (indexedNameValue (Q + 1) j -
              indexedNameValue Q (goldenGapLeft Q i)) := by ring
      _ = φ / 2 * φ ^ (-(Q : Int)) -
          φ ^ (-((Q + 1 : Nat) : Int)) := by rw [hleft, hjleft]
      _ = φ ^ (-1 : Int) / 2 * φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q]
        calc
          φ / 2 * (φ * φ ^ (-((Q + 1 : Nat) : Int))) -
                φ ^ (-((Q + 1 : Nat) : Int)) =
              (φ / 2 * φ - 1) * φ ^ (-((Q + 1 : Nat) : Int)) := by ring
          _ = φ ^ (-1 : Int) / 2 * φ ^ (-((Q + 1 : Nat) : Int)) := by
            rw [golden_phase_b_left_scale]
  · rw [hnextRight, levelEmbedding_value]
    calc
      indexedNameValue Q (goldenGapRight Q i) - x =
          φ ^ (-2 : Int) / 2 * φ ^ (-(Q : Int)) := hright
      _ = φ ^ (-1 : Int) / 2 * φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q]
        calc
          φ ^ (-2 : Int) / 2 *
                (φ * φ ^ (-((Q + 1 : Nat) : Int))) =
              (φ ^ (-2 : Int) / 2 * φ) *
                φ ^ (-((Q + 1 : Nat) : Int)) := by ring
          _ = φ ^ (-1 : Int) / 2 * φ ^ (-((Q + 1 : Nat) : Int)) := by
            rw [golden_phase_b_right_scale]

/-- A small midpoint gap persists as the next level's large midpoint gap. -/
theorem golden_phase_c_to_a (Q : Nat) (hQ : 2 ≤ Q) (x : Real)
    (hgap : IsGoldenOrbitGap Q x
      (φ ^ (-1 : Int) / 2) (φ ^ (-1 : Int) / 2)) :
    IsGoldenOrbitGap (Q + 1) x (1 / 2) (1 / 2) := by
  rcases hgap with ⟨i, hleft, hright⟩
  have hsmall :
      indexedNameValue Q (goldenGapRight Q i) -
          indexedNameValue Q (goldenGapLeft Q i) =
        φ ^ (-((Q + 1 : Nat) : Int)) := by
    calc
      indexedNameValue Q (goldenGapRight Q i) -
            indexedNameValue Q (goldenGapLeft Q i) =
          (indexedNameValue Q (goldenGapRight Q i) - x) +
            (x - indexedNameValue Q (goldenGapLeft Q i)) := by ring
      _ = (φ ^ (-1 : Int) / 2 + φ ^ (-1 : Int) / 2) *
          φ ^ (-(Q : Int)) := by
        rw [hleft, hright]
        ring
      _ = φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q]
        calc
          (φ ^ (-1 : Int) / 2 + φ ^ (-1 : Int) / 2) *
                (φ * φ ^ (-((Q + 1 : Nat) : Int))) =
              (φ ^ (-1 : Int) * φ) *
                φ ^ (-((Q + 1 : Nat) : Int)) := by ring
          _ = φ ^ (-((Q + 1 : Nat) : Int)) := by rw [golden_inverse_mul, one_mul]
  have hsubstitution := (golden_gap_substitution Q hQ i).1 (by
    simpa [goldenGapLeft, goldenGapRight] using hsmall)
  have hset := hsubstitution.1
  have hpositions := inserted_empty_positions Q i hset
  let next : Fin (Nat.fib ((Q + 1) + 2) - 1) :=
    ⟨(levelEmbedding Q (goldenGapLeft Q i)).1, by
      change (levelEmbedding Q (goldenGapLeft Q i)).1 < Nat.fib (Q + 3) - 1
      have hrightbound := (levelEmbedding Q (goldenGapRight Q i)).2
      omega⟩
  have hnextLeft :
      goldenGapLeft (Q + 1) next = levelEmbedding Q (goldenGapLeft Q i) := by
    apply Fin.ext
    simp [next, goldenGapLeft]
  have hnextRight :
      goldenGapRight (Q + 1) next = levelEmbedding Q (goldenGapRight Q i) := by
    apply Fin.ext
    simpa [next, goldenGapRight] using hpositions.symm
  refine ⟨next, ?_, ?_⟩
  · rw [hnextLeft, levelEmbedding_value]
    calc
      x - indexedNameValue Q (goldenGapLeft Q i) =
          φ ^ (-1 : Int) / 2 * φ ^ (-(Q : Int)) := hleft
      _ = (1 / 2 : Real) * φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q]
        calc
          φ ^ (-1 : Int) / 2 *
                (φ * φ ^ (-((Q + 1 : Nat) : Int))) =
              (φ ^ (-1 : Int) * φ) / 2 *
                φ ^ (-((Q + 1 : Nat) : Int)) := by ring
          _ = (1 / 2 : Real) * φ ^ (-((Q + 1 : Nat) : Int)) := by
            rw [golden_inverse_mul]
  · rw [hnextRight, levelEmbedding_value]
    calc
      indexedNameValue Q (goldenGapRight Q i) - x =
          φ ^ (-1 : Int) / 2 * φ ^ (-(Q : Int)) := hright
      _ = (1 / 2 : Real) * φ ^ (-((Q + 1 : Nat) : Int)) := by
        rw [golden_scale_succ Q]
        calc
          φ ^ (-1 : Int) / 2 *
                (φ * φ ^ (-((Q + 1 : Nat) : Int))) =
              (φ ^ (-1 : Int) * φ) / 2 *
                φ ^ (-((Q + 1 : Nat) : Int)) := by ring
          _ = (1 / 2 : Real) * φ ^ (-((Q + 1 : Nat) : Int)) := by
            rw [golden_inverse_mul]

/-- The source champion is the midpoint of the first level-six large gap. -/
theorem golden_champion_base_gap :
    IsGoldenOrbitGap 6 ((13 / 2 : Real) - 4 * φ) (1 / 2) (1 / 2) := by
  let i := firstGoldenGap 6 (by omega)
  have hleftValue : indexedNameValue 6 (goldenGapLeft 6 i) = 0 := by
    change ((wdigits 0).map fun k : Nat =>
      φ ^ ((k : Int) - (((6 : Nat) + 2 : Nat) : Int))).sum = 0
    rw [show wdigits 0 = [] by
      symm
      apply wdigits_unique
      · exact List.IsZeckendorfRep_nil
      · simp]
    simp
  have hgap :
      indexedNameValue 6 (goldenGapRight 6 i) -
          indexedNameValue 6 (goldenGapLeft 6 i) = φ ^ (-6 : Int) := by
    simpa [i] using first_golden_gap_value 6 (by omega)
  have hpoint : ((13 / 2 : Real) - 4 * φ) = φ ^ (-6 : Int) / 2 :=
    golden_champion_point_identity.1.trans golden_champion_point_identity.2
  refine ⟨i, ?_, ?_⟩
  · rw [hleftValue, sub_zero, hpoint]
    ring
  · calc
      indexedNameValue 6 (goldenGapRight 6 i) - ((13 / 2 : Real) - 4 * φ) =
          (indexedNameValue 6 (goldenGapRight 6 i) -
            indexedNameValue 6 (goldenGapLeft 6 i)) -
              (((13 / 2 : Real) - 4 * φ) -
                indexedNameValue 6 (goldenGapLeft 6 i)) := by ring
      _ = φ ^ (-6 : Int) - φ ^ (-6 : Int) / 2 := by
        rw [hgap, hleftValue, sub_zero, hpoint]
      _ = (1 / 2 : Real) * φ ^ (-6 : Int) := by ring

/-- From level six onward, the containing gap follows the exact cycle `L,L,S`. -/
theorem golden_champion_gap_orbit (k : Nat) :
    IsGoldenOrbitGap (3 * k + 6) ((13 / 2 : Real) - 4 * φ) (1 / 2) (1 / 2) ∧
      IsGoldenOrbitGap (3 * k + 7) ((13 / 2 : Real) - 4 * φ)
        (φ / 2) (φ ^ (-2 : Int) / 2) ∧
      IsGoldenOrbitGap (3 * k + 8) ((13 / 2 : Real) - 4 * φ)
        (φ ^ (-1 : Int) / 2) (φ ^ (-1 : Int) / 2) := by
  induction k with
  | zero =>
      have hphaseA := golden_champion_base_gap
      have hphaseB := golden_phase_a_to_b 6 (by omega)
        ((13 / 2 : Real) - 4 * φ) hphaseA
      have hphaseC := golden_phase_b_to_c 7 (by omega)
        ((13 / 2 : Real) - 4 * φ) hphaseB
      constructor
      · norm_num only [Nat.zero_mul, zero_add, Nat.reduceAdd] at hphaseA ⊢
        exact hphaseA
      constructor
      · norm_num only [Nat.zero_mul, zero_add, Nat.reduceAdd] at hphaseB ⊢
        exact hphaseB
      · norm_num only [Nat.zero_mul, zero_add, Nat.reduceAdd] at hphaseC ⊢
        exact hphaseC
  | succ k ih =>
      have hphaseA := golden_phase_c_to_a (3 * k + 8) (by omega)
        ((13 / 2 : Real) - 4 * φ) ih.2.2
      have hphaseB := golden_phase_a_to_b (3 * k + 9) (by omega)
        ((13 / 2 : Real) - 4 * φ) hphaseA
      have hphaseC := golden_phase_b_to_c (3 * k + 10) (by omega)
        ((13 / 2 : Real) - 4 * φ) hphaseB
      constructor
      · simpa [Nat.mul_succ, add_assoc] using hphaseA
      constructor
      · simpa [Nat.mul_succ, add_assoc] using hphaseB
      · simpa [Nat.mul_succ, add_assoc] using hphaseC

theorem goldenSurvivor_eq_of_orbit_gap (Q : Nat) (x leftArm rightArm arm : Real)
    (hgap : IsGoldenOrbitGap Q x leftArm rightArm)
    (hleftArm : 0 ≤ leftArm) (hrightArm : 0 ≤ rightArm)
    (harmLeft : arm ≤ leftArm) (harmRight : arm ≤ rightArm)
    (hnearest : arm = leftArm ∨ arm = rightArm) :
    goldenSurvivor Q x = arm := by
  rcases hgap with ⟨i, hleft, hright⟩
  let a := indexedNameValue Q (goldenGapLeft Q i)
  let b := indexedNameValue Q (goldenGapRight Q i)
  have hscale_nonneg : 0 ≤ φ ^ (-(Q : Int)) :=
    (zpow_pos Real.goldenRatio_pos _).le
  have hleft_nonneg : 0 ≤ x - a := by
    rw [show x - a = leftArm * φ ^ (-(Q : Int)) by exact hleft]
    positivity
  have hright_nonneg : 0 ≤ b - x := by
    rw [show b - x = rightArm * φ ^ (-(Q : Int)) by exact hright]
    positivity
  have hgrid : (goldenNameGrid Q).Nonempty :=
    ⟨a, goldenGapLeft Q i, by simp [a]⟩
  have hlower : arm * φ ^ (-(Q : Int)) ≤
      Metric.infDist x (goldenNameGrid Q) := by
    rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨j, hj⟩
    subst y
    by_cases hjleft : j ≤ goldenGapLeft Q i
    · have hy_le : indexedNameValue Q j ≤ a :=
        (indexed_nameValue_strictMono Q).monotone hjleft
      have hy_x : indexedNameValue Q j ≤ x := hy_le.trans (sub_nonneg.mp hleft_nonneg)
      have hscaled := mul_le_mul_of_nonneg_right harmLeft hscale_nonneg
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_x)]
      linarith
    · have hright_le : goldenGapRight Q i ≤ j := by
        change i.1 + 1 ≤ j.1
        change ¬j.1 ≤ i.1 at hjleft
        omega
      have hb_le : b ≤ indexedNameValue Q j :=
        (indexed_nameValue_strictMono Q).monotone hright_le
      have hx_y : x ≤ indexedNameValue Q j := (sub_nonneg.mp hright_nonneg).trans hb_le
      have hscaled := mul_le_mul_of_nonneg_right harmRight hscale_nonneg
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx_y)]
      linarith
  have hupper : Metric.infDist x (goldenNameGrid Q) ≤
      arm * φ ^ (-(Q : Int)) := by
    rcases hnearest with hnear | hnear
    · calc
        Metric.infDist x (goldenNameGrid Q) ≤ dist x a :=
          Metric.infDist_le_dist_of_mem ⟨goldenGapLeft Q i, by simp [a]⟩
        _ = x - a := by rw [Real.dist_eq, abs_of_nonneg hleft_nonneg]
        _ = arm * φ ^ (-(Q : Int)) := by rw [hleft, hnear]
    · calc
        Metric.infDist x (goldenNameGrid Q) ≤ dist x b :=
          Metric.infDist_le_dist_of_mem ⟨goldenGapRight Q i, by simp [b]⟩
        _ = b - x := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (sub_nonneg.mp hright_nonneg))]
          ring
        _ = arm * φ ^ (-(Q : Int)) := by rw [hright, hnear]
  have hinf : Metric.infDist x (goldenNameGrid Q) =
      arm * φ ^ (-(Q : Int)) := le_antisymm hupper hlower
  have hcancel : φ ^ (Q : Int) * φ ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ Real.goldenRatio_ne_zero]
    simp
  unfold goldenSurvivor
  rw [hinf]
  calc
    φ ^ (Q : Int) * (arm * φ ^ (-(Q : Int))) =
        arm * (φ ^ (Q : Int) * φ ^ (-(Q : Int))) := by ring
    _ = arm := by rw [hcancel]; ring

/-- The first phase of the champion ring has arm `1/2`. -/
theorem golden_champion_survivor_phase_a (k : Nat) :
    goldenSurvivor (3 * k + 6) ((13 / 2 : Real) - 4 * φ) = 1 / 2 := by
  apply goldenSurvivor_eq_of_orbit_gap
      (hgap := (golden_champion_gap_orbit k).1)
  · norm_num
  · norm_num
  · exact le_rfl
  · exact le_rfl
  · exact Or.inl rfl

/-- The second phase of the champion ring has its uniquely lowest arm `phi^-2/2`. -/
theorem golden_champion_survivor_phase_b (k : Nat) :
    goldenSurvivor (3 * k + 7) ((13 / 2 : Real) - 4 * φ) =
      φ ^ (-2 : Int) / 2 := by
  apply goldenSurvivor_eq_of_orbit_gap
      (hgap := (golden_champion_gap_orbit k).2.1)
  · positivity
  · positivity
  · exact golden_low_le_half.trans (by nlinarith [Real.one_lt_goldenRatio])
  · exact le_rfl
  · exact Or.inr rfl

/-- The small-gap phase of the champion ring has arm `phi^-1/2`. -/
theorem golden_champion_survivor_phase_c (k : Nat) :
    goldenSurvivor (3 * k + 8) ((13 / 2 : Real) - 4 * φ) =
      φ ^ (-1 : Int) / 2 := by
  apply goldenSurvivor_eq_of_orbit_gap
      (hgap := (golden_champion_gap_orbit k).2.2)
  · positivity
  · positivity
  · exact le_rfl
  · exact le_rfl
  · exact Or.inl rfl

/-- The actual survivor values form the exact three-phase arm ring. -/
theorem golden_champion_arm_ring (k : Nat) :
    goldenSurvivor (3 * k + 6) ((13 / 2 : Real) - 4 * φ) = 1 / 2 ∧
      goldenSurvivor (3 * k + 7) ((13 / 2 : Real) - 4 * φ) =
        φ ^ (-2 : Int) / 2 ∧
      goldenSurvivor (3 * k + 8) ((13 / 2 : Real) - 4 * φ) =
        φ ^ (-1 : Int) / 2 := by
  exact ⟨golden_champion_survivor_phase_a k,
    golden_champion_survivor_phase_b k, golden_champion_survivor_phase_c k⟩

/-- The one-step in-hull preimage at level five has the third ring arm. -/
theorem golden_champion_survivor_five :
    goldenSurvivor 5 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 := by
  let i := firstGoldenGap 5 (by omega)
  have hleftValue : indexedNameValue 5 (goldenGapLeft 5 i) = 0 := by
    change ((wdigits 0).map fun k : Nat =>
      φ ^ ((k : Int) - (((5 : Nat) + 2 : Nat) : Int))).sum = 0
    rw [show wdigits 0 = [] by
      symm
      apply wdigits_unique
      · exact List.IsZeckendorfRep_nil
      · simp]
    simp
  have hgap :
      indexedNameValue 5 (goldenGapRight 5 i) -
          indexedNameValue 5 (goldenGapLeft 5 i) = φ ^ (-5 : Int) := by
    simpa [i] using first_golden_gap_value 5 (by omega)
  have hpoint : ((13 / 2 : Real) - 4 * φ) = φ ^ (-6 : Int) / 2 :=
    golden_champion_point_identity.1.trans golden_champion_point_identity.2
  have hpowSix : φ ^ (-6 : Int) = φ ^ (-1 : Int) * φ ^ (-5 : Int) := by
    rw [← zpow_add₀ Real.goldenRatio_ne_zero]
    norm_num
  have hleft : ((13 / 2 : Real) - 4 * φ) -
      indexedNameValue 5 (goldenGapLeft 5 i) =
        (φ ^ (-1 : Int) / 2) * φ ^ (-5 : Int) := by
    rw [hleftValue, sub_zero, hpoint, hpowSix]
    ring
  have hright : indexedNameValue 5 (goldenGapRight 5 i) -
      ((13 / 2 : Real) - 4 * φ) =
        ((2 - φ ^ (-1 : Int)) / 2) * φ ^ (-5 : Int) := by
    calc
      indexedNameValue 5 (goldenGapRight 5 i) - ((13 / 2 : Real) - 4 * φ) =
          (indexedNameValue 5 (goldenGapRight 5 i) -
            indexedNameValue 5 (goldenGapLeft 5 i)) -
              (((13 / 2 : Real) - 4 * φ) -
                indexedNameValue 5 (goldenGapLeft 5 i)) := by ring
      _ = φ ^ (-5 : Int) - φ ^ (-6 : Int) / 2 := by
        rw [hgap, hleftValue, sub_zero, hpoint]
      _ = ((2 - φ ^ (-1 : Int)) / 2) * φ ^ (-5 : Int) := by
        rw [hpowSix]
        ring
  apply goldenSurvivor_eq_of_orbit_gap
      (hgap := ⟨i, hleft, hright⟩)
  · positivity
  · have hinv_lt_one : φ ^ (-1 : Int) < 1 := by
      simpa [zpow_neg] using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    linarith
  · exact le_rfl
  · have hinv_le_one : φ ^ (-1 : Int) ≤ 1 := by
      simpa using zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le
        (by norm_num : (-1 : Int) ≤ 0)
    linarith
  · exact Or.inl rfl

theorem nat_three_phase (n : Nat) :
    ∃ k : Nat, n = 3 * k ∨ n = 3 * k + 1 ∨ n = 3 * k + 2 := by
  refine ⟨n / 3, ?_⟩
  have hmod := Nat.mod_lt n (by omega : 0 < 3)
  have hdecomp := Nat.mod_add_div n 3
  omega

/-- The champion's along-level liminf is `phi^-2/2`, not the fixed-level half. -/
theorem golden_champion_liminf :
    Filter.liminf
        (fun Q => goldenSurvivor Q ((13 / 2 : Real) - 4 * φ)) Filter.atTop =
      φ ^ (-2 : Int) / 2 := by
  let low := φ ^ (-2 : Int) / 2
  have heventually_lower :
      ∀ᶠ Q in Filter.atTop,
        low ≤ goldenSurvivor Q ((13 / 2 : Real) - 4 * φ) := by
    rw [Filter.eventually_atTop]
    refine ⟨6, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 6 := ⟨Q - 6, by omega⟩
    rcases nat_three_phase n with ⟨k, hk | hk | hk⟩
    · subst n
      rw [show 3 * k + 6 = 3 * k + 6 by simp,
        golden_champion_survivor_phase_a]
      exact golden_low_le_half
    · subst n
      rw [show (3 * k + 1) + 6 = 3 * k + 7 by omega,
        golden_champion_survivor_phase_b]
    · subst n
      rw [show (3 * k + 2) + 6 = 3 * k + 8 by omega,
        golden_champion_survivor_phase_c]
      exact golden_low_le_inverse_half
  have heventually_upper :
      ∀ᶠ Q in Filter.atTop,
        goldenSurvivor Q ((13 / 2 : Real) - 4 * φ) ≤ (1 : Real) / 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨6, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 6 := ⟨Q - 6, by omega⟩
    rcases nat_three_phase n with ⟨k, hk | hk | hk⟩
    · subst n
      rw [show 3 * k + 6 = 3 * k + 6 by simp,
        golden_champion_survivor_phase_a]
    · subst n
      rw [show (3 * k + 1) + 6 = 3 * k + 7 by omega,
        golden_champion_survivor_phase_b]
      exact golden_low_le_half
    · subst n
      rw [show (3 * k + 2) + 6 = 3 * k + 8 by omega,
        golden_champion_survivor_phase_c]
      have hinv_le_one : φ ^ (-1 : Int) ≤ 1 := by
        simpa using zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le
          (by norm_num : (-1 : Int) ≤ 0)
      exact div_le_div_of_nonneg_right hinv_le_one (by norm_num)
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨3 * N + 7, by omega, ?_⟩
      rw [golden_champion_survivor_phase_b]
    · exact ⟨low, heventually_lower⟩
  · exact Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop heventually_upper)
      heventually_lower

example :
    goldenSurvivor 5 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 := by
  norm_num only
  exact golden_champion_survivor_five

example : goldenSurvivor 6 ((13 / 2 : Real) - 4 * φ) = 1 / 2 := by
  have h := golden_champion_survivor_phase_a 0
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example :
    goldenSurvivor 7 ((13 / 2 : Real) - 4 * φ) = φ ^ (-2 : Int) / 2 := by
  have h := golden_champion_survivor_phase_b 0
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example :
    goldenSurvivor 8 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 := by
  have h := golden_champion_survivor_phase_c 0
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example : goldenSurvivor 9 ((13 / 2 : Real) - 4 * φ) = 1 / 2 := by
  have h := golden_champion_survivor_phase_a 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example :
    goldenSurvivor 10 ((13 / 2 : Real) - 4 * φ) = φ ^ (-2 : Int) / 2 := by
  have h := golden_champion_survivor_phase_b 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

example :
    goldenSurvivor 11 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 := by
  have h := golden_champion_survivor_phase_c 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

end D5.S0.Tower.Champions.GoldenAsymptotic
