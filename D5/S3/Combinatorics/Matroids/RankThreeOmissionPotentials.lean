/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Rank-three omitted triangle gaps identify normalized three-torsion potentials. -/

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials

private theorem cycle_torsion {A : Type*} [AddCommGroup A] (u v w : A)
    (h₁ : v - u = w - v) (h₂ : w - v = u - w) :
    3 • (v - u) = 0 ∧ 3 • (w - v) = 0 ∧ 3 • (u - w) = 0 := by
  have h : 3 • (v - u) = 0 := calc
    3 • (v - u) = (v - u) + (v - u) + (v - u) := by abel
    _ = (v - u) + (w - v) + (u - w) := by
      exact congrArg₂ (· + ·) (congrArg ((v - u) + ·) h₁) (h₁.trans h₂)
    _ = 0 := by abel
  exact ⟨h, h₁ ▸ h, (h₁.trans h₂) ▸ h⟩

private theorem triangle_gaps_torsion {A : Type*} [AddCommGroup A] (u : Fin 3 → A)
    (h₁ : u 1 - u 0 = u 2 - u 1) (h₂ : u 2 - u 1 = u 0 - u 2) :
    ∀ i j : Fin 3, 3 • (u j - u i) = 0 := by
  obtain ⟨ha, hb, hc⟩ := cycle_torsion (u 0) (u 1) (u 2) h₁ h₂
  have ha' : 3 • (u 0 - u 1) = 0 := by
    calc
      3 • (u 0 - u 1) = (-((3 : ℕ) • (u 1 - u 0)) : A) := by abel
      _ = 0 := by rw [ha, neg_zero]
  have hb' : 3 • (u 1 - u 2) = 0 := by
    calc
      3 • (u 1 - u 2) = (-((3 : ℕ) • (u 2 - u 1)) : A) := by abel
      _ = 0 := by rw [hb, neg_zero]
  have hc' : 3 • (u 2 - u 0) = 0 := by
    calc
      3 • (u 2 - u 0) = (-((3 : ℕ) • (u 0 - u 2)) : A) := by abel
      _ = 0 := by rw [hc, neg_zero]
  intro i j
  fin_cases i <;> fin_cases j <;> first | assumption | simp

/-- After fixing one point's potential to zero, constant cyclic gaps on omitted
triangles and zero gaps on uncovered edges become three-torsion line sums. -/
theorem normalized_potential_iff {I T A : Type*} [AddCommGroup A]
    (points : T → Fin 3 → I) (u : I → A) (root : I) :
    let uncovered (i j : I) := ¬ ∃ t a b, points t a = i ∧ points t b = j
    let v (i : I) := u i - u root
    ( (∀ i j, uncovered i j → u i = u j) ∧
      (∀ t, u (points t 1) - u (points t 0) = u (points t 2) - u (points t 1) ∧
        u (points t 2) - u (points t 1) = u (points t 0) - u (points t 2))) ↔
    ( (∀ i, 3 • v i = 0) ∧ (∀ i j, uncovered i j → v i = v j) ∧
      (∀ t, v (points t 0) + v (points t 1) + v (points t 2) = 0)) := by
  classical
  intro uncovered v
  have gap (i j : I) : v j - v i = u j - u i := by dsimp [v]; abel
  have eq_shift (i j : I) : u i = u j ↔ v i = v j := by
    constructor
    · intro h
      simp only [v, h]
    · intro h
      apply sub_eq_zero.mp
      rw [← gap j i, h, sub_self]
  constructor
  · rintro ⟨hedge, hcycle⟩
    have htorsion (i : I) : 3 • v i = 0 := by
      by_cases h : uncovered root i
      · simp [v, hedge root i h]
      · obtain ⟨t, a, b, ha, hb⟩ :
            ∃ t a b, points t a = root ∧ points t b = i := by
          exact not_not.mp h
        have hc := triangle_gaps_torsion (u ∘ points t) (hcycle t).1 (hcycle t).2 a b
        simpa [Function.comp_apply, v, ha, hb] using hc
    refine ⟨htorsion, fun i j h => (eq_shift i j).mp (hedge i j h), ?_⟩
    intro t
    have h : v (points t 1) - v (points t 0) = v (points t 2) - v (points t 1) := by
      simp only [gap]
      exact (hcycle t).1
    calc
      v (points t 0) + v (points t 1) + v (points t 2) =
          3 • v (points t 1) + ((v (points t 2) - v (points t 1)) -
            (v (points t 1) - v (points t 0))) := by abel
      _ = 0 := by rw [← h, sub_self, add_zero, htorsion]
  · rintro ⟨htorsion, hedge, hline⟩
    refine ⟨fun i j h => (eq_shift i j).mpr (hedge i j h), ?_⟩
    intro t
    simp only [← gap]
    constructor
    · calc
        v (points t 1) - v (points t 0) =
            (v (points t 2) - v (points t 1)) + (3 • v (points t 1) -
              (v (points t 0) + v (points t 1) + v (points t 2))) := by abel
        _ = _ := by rw [htorsion, hline, sub_self, add_zero]
    · calc
        v (points t 2) - v (points t 1) =
            (v (points t 0) - v (points t 2)) + (3 • v (points t 2) -
              (v (points t 0) + v (points t 1) + v (points t 2))) := by abel
        _ = _ := by rw [htorsion, hline, sub_self, add_zero]

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials
