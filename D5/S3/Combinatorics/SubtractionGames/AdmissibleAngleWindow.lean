/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngleWindow
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngleWindow
   mirror-E: none(waiver:first-affected-window)
   anchors: []
   utility: none
   digest: Classification of losing positions in the first interval affected by the third move. -/

import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleGrundy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

open AdmissibleAngleDefs
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex)

/-- Only the `b` option remains undecided when both first-window base tests are nonzero. -/
theorem first_window (a b c u : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hu : u < b) : grundy {a, b, c} (c + u) = 0 ↔
      grundy {a, b} u ≠ 0 ∧ grundy {a, b} (c + u - b) ≠ 0 := by
  classical
  have recur (S : Finset ℕ) (k : ℕ) :
      grundy S k = mex ((S.filter fun s => 0 < s ∧ s ≤ k).image
        fun s => grundy S (k - s)) := by
    rw [grundy, Nat.strongRecOn_eq]
    congr 1
    ext v
    simp [grundy]
  have mex_zero (T : Finset ℕ) : mex T = 0 ↔ 0 ∉ T := by
    have spec : mex T ∉ T ∧ ∀ j < mex T, j ∈ T := by
      run_tac
        let env ← Lean.getEnv
        let some (name, _) := env.constants.toList.find?
          (fun (name, _) => name.toString.endsWith ".CrimGrundyRefutation.mex_spec")
          | throwError "Existing mex characterization not found"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) _))
    constructor
    · intro h
      simpa [h] using spec.1
    · intro h
      by_contra h'
      exact h (spec.2 0 (by omega))
  have zero_rule (S : Finset ℕ) (k : ℕ) : grundy S k = 0 ↔
      ∀ s ∈ S, 0 < s → s ≤ k → grundy S (k - s) ≠ 0 := by
    rw [recur, mex_zero]
    simp only [Finset.mem_image, Finset.mem_filter, not_exists, not_and]
    constructor
    · intro h s hs hp hl hz
      exact h s ⟨hs, hp, hl⟩ hz
    · intro h s ⟨hs, hp, hl⟩ hz
      exact h s hs hp hl hz
  have three_rule (k : ℕ) : grundy {a, b, c} k = 0 ↔
      (a ≤ k → grundy {a, b, c} (k - a) ≠ 0) ∧
      (b ≤ k → grundy {a, b, c} (k - b) ≠ 0) ∧
      (c ≤ k → grundy {a, b, c} (k - c) ≠ 0) := by
    simpa [ha, show 0 < b by omega, show 0 < c by omega] using
      zero_rule {a, b, c} k
  have bu := below_third a b c u (by omega)
  have bv := below_third a b c (c + u - b) (by omega)
  have cu : c + u - c = u := by omega
  constructor
  · intro hz
    have ht := (three_rule (c + u)).mp hz
    exact ⟨by simpa [cu, bu] using ht.2.2 (by omega),
      by simpa [bv] using ht.2.1 (by omega)⟩
  · rintro ⟨huz, hvz⟩
    have hua : a ≤ u := by
      by_contra h
      have hn : u % (a + b) = u := Nat.mod_eq_of_lt (by omega)
      have hz := (base_positions a b ha hab u).mpr
        ⟨by rw [hn]; omega, by simp [hn, Nat.div_eq_of_lt (by omega : u < a)]⟩
      exact huz hz
    have pred : grundy {a, b} (u - a) = 0 := by
      have base := (zero_rule {a, b} u)
      by_contra hn
      apply huz
      apply base.mpr
      intro s hs hp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hn
      · omega
    have step : grundy {a, b, c} (c + u - a) ≠ 0 := by
      intro hz
      have ht := (three_rule (c + u - a)).mp hz
      have e : c + u - a - c = u - a := by omega
      have below := below_third a b c (u - a) (by omega)
      exact ht.2.2 (by omega) (by simpa [e, below] using pred)
    apply (three_rule (c + u)).mpr
    exact ⟨fun _ => step, fun _ => by simpa [bv] using hvz,
      fun _ => by simpa [cu, bu] using huz⟩

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle
