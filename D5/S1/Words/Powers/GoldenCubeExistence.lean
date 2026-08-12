/- GID: D5/S1/Words/Powers/GoldenCubeExistence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Fibonacci substitution lifts one golden cube to a full existence tower. -/

import D5.S1.Words.Powers.GoldenCubePeriods

namespace D5.S1.Words.Powers

open D5.S1.Words
open D5.S0.Tower.GoldenGapWord

/-! ### Generic word-power bookkeeping -/

private theorem flatMap_wordPower (f : Bool → List Bool) (k : Nat) (u : List Bool) :
    (wordPower k u).flatMap f = wordPower k (u.flatMap f) := by
  induction k with
  | zero => simp [wordPower]
  | succ k ih =>
      rw [wordPower_succ, List.flatMap_append, ih, wordPower_succ]

private theorem length_flatMap_wordPower (f : Bool → List Bool) (k : Nat) (u : List Bool) :
    ((wordPower k u).flatMap f).length = k * (u.flatMap f).length := by
  rw [flatMap_wordPower]
  rw [length_wordPower]

/-! ### Substitution of a factor window -/

private theorem substitution_factor_of_pointwise (i : Nat) :
    ∀ (w : List Bool),
      (∀ j (hj : j < w.length), w.get ⟨j, hj⟩ = goldenWord (i + j)) →
        goldenFactor (w.flatMap subst).length (goldenSubstStart i) = w.flatMap subst := by
  intro w
  induction w generalizing i with
  | nil =>
      intro h
      simp [goldenFactor]
  | cons a w ih =>
      intro h
      have ha : a = goldenWord i := by
        simpa using h 0 (by simp)
      have htail : ∀ j (hj : j < w.length),
          w.get ⟨j, hj⟩ = goldenWord (i + 1 + j) := by
        intro j hj
        have h' := h (j + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'
      have hi1 := ih (i := i + 1) htail
      have hstart : goldenSubstStart (i + 1) =
          goldenSubstStart i + (subst (goldenWord i)).length := by
        simpa [ha] using goldenSubstStart_succ i
      let b := (subst (goldenWord i)).length
      let t := (w.flatMap subst).length
      have hlen : ((a :: w).flatMap subst).length = b + t := by
        simp [List.flatMap, ha, b, t, List.length_flatMap, Function.comp_def]
      apply List.ext_get
      · simp [goldenFactor]
      · intro x hxleft hxright
        have happ : (a :: w).flatMap subst = subst a ++ w.flatMap subst := by
          simp [List.flatMap]
        have hgold :
            (goldenFactor ((a :: w).flatMap subst).length (goldenSubstStart i)).get
                ⟨x, hxleft⟩ = goldenWord (goldenSubstStart i + x) := by
          simp [goldenFactor]
        by_cases hxb : x < b
        · have hxsub : x < (subst (goldenWord i)).length := by simpa [b] using hxb
          have hfixed := golden_word_substitution_fixed i ⟨x, hxsub⟩
          have hxgf : goldenWord (goldenSubstStart i + x) =
              ((subst (goldenWord i)).get ⟨x, hxsub⟩) := hfixed
          have hsource :
              ((a :: w).flatMap subst).get ⟨x, hxright⟩ =
                (subst (goldenWord i)).get ⟨x, hxsub⟩ := by
            have hxright' : x < (subst a ++ w.flatMap subst).length := by
              simpa [happ] using hxright
            have hxbA : x < (subst a).length := by simpa [ha, b] using hxb
            have hs := List.getElem_append_left (as := subst a)
              (bs := w.flatMap subst) hxbA (h' := hxright')
            simpa [happ, ha] using hs
          exact hgold.trans (hxgf.trans hsource.symm)
        · have hxb' : b ≤ x := by omega
          let y := x - b
          have hy : y < t := by simpa [t] using (show x - b < (w.flatMap subst).length by omega)
          have hnext := congrArg (fun z : List Bool => z[y]?) hi1
          have hnext' : goldenWord (goldenSubstStart (i + 1) + y) =
              (w.flatMap subst).get ⟨y, hy⟩ := by
            simp [goldenFactor, hy, t] at hnext
            have hy' : y < (List.map (fun a => (subst a).length) w).sum := by
              simpa [t] using hy
            simp only [hy', ↓reduceIte] at hnext
            rw [List.getElem?_eq_getElem hy] at hnext
            exact Option.some.inj hnext
          have hsource :
              ((a :: w).flatMap subst).get ⟨x, hxright⟩ =
                (w.flatMap subst).get ⟨y, hy⟩ := by
            have hxright' : x < (subst a ++ w.flatMap subst).length := by
              simpa [happ] using hxright
            have hxbA : (subst a).length ≤ x := by simpa [ha, b] using hxb'
            have hs := List.getElem_append_right (as := subst a)
              (bs := w.flatMap subst) hxbA (h₂ := hxright')
            simpa [happ, ha, b, y] using hs
          have hpos : goldenSubstStart i + b + y =
              goldenSubstStart (i + 1) + y := by omega
          have hxy : b + y = x := by omega
          calc
            _ = goldenWord (goldenSubstStart i + x) := hgold
            _ = goldenWord (goldenSubstStart i + b + y) := by
              congr 1
              omega
            _ = goldenWord (goldenSubstStart (i + 1) + y) := by rw [hpos]
            _ = (w.flatMap subst).get ⟨y, hy⟩ := hnext'
            _ = ((a :: w).flatMap subst).get ⟨x, hxright⟩ := hsource.symm

private theorem substitution_factor (i n : Nat) :
    goldenFactor ((goldenFactor n i).flatMap subst).length (goldenSubstStart i) =
      (goldenFactor n i).flatMap subst := by
  apply substitution_factor_of_pointwise i
  intro j hj
  simp only [goldenFactor, List.get_eq_getElem, List.getElem_ofFn]

/-! ### The lifting step and the Fibonacci tower -/

private theorem golden_cube_lift {u : List Bool} {i : Nat}
    (hcube : IsGoldenPowerFactor 3 u i) :
    IsGoldenPowerFactor 3 (u.flatMap subst) (goldenSubstStart i) := by
  unfold IsGoldenPowerFactor at hcube ⊢
  have hsub := substitution_factor i (3 * u.length)
  rw [hcube] at hsub
  rw [flatMap_wordPower] at hsub
  rw [length_wordPower] at hsub
  exact hsub

private theorem golden_fib_cube_iterate : ∀ k : Nat,
    ∃ i, IsGoldenPowerFactor 3 (fibWord (k + 2)) i := by
  intro k
  induction k with
  | zero =>
      refine ⟨5, ?_⟩
      have hword : fibWord 2 = [true, false, true] := by decide
      simpa [hword] using golden_cube_is_power_factor
  | succ k ih =>
      obtain ⟨i, hi⟩ := ih
      refine ⟨goldenSubstStart i, ?_⟩
      have hlift := golden_cube_lift hi
      simpa [fibWord] using hlift

/-! ### Public existence and exact length classification -/

theorem golden_fib_cube_exists (k : Nat) :
    ∃ i, IsGoldenPowerFactor 3 (fibWord (k + 2)) i := by
  exact golden_fib_cube_iterate k

theorem golden_cube_exists_of_fib_length {Q : Nat} (hQ : 4 ≤ Q) :
    ∃ i u, u ≠ [] ∧ u.length = Nat.fib Q ∧ IsGoldenPowerFactor 3 u i := by
  obtain ⟨k, rfl⟩ : ∃ k, Q = k + 4 := ⟨Q - 4, by omega⟩
  obtain ⟨i, hi⟩ := golden_fib_cube_exists (k := k)
  refine ⟨i, fibWord (k + 2), ?_, ?_, hi⟩
  · intro hnil
    have hlen := fibWord_length (k + 2)
    rw [hnil] at hlen
    have hpos : 0 < Nat.fib (k + 4) := Nat.fib_pos.mpr (by omega)
    exact (Nat.ne_of_gt hpos) hlen.symm
  · rw [fibWord_length]

theorem golden_cube_root_length_iff_fib {n : Nat} :
    (∃ i u, u ≠ [] ∧ u.length = n ∧ IsGoldenPowerFactor 3 u i) ↔
      ∃ Q, 4 ≤ Q ∧ n = Nat.fib Q := by
  constructor
  · rintro ⟨i, u, hu, hlen, hcube⟩
    obtain ⟨Q, hQ, hfib⟩ := golden_cube_root_length_eq_fib hu hcube
    exact ⟨Q, hQ, hlen.symm.trans hfib⟩
  · rintro ⟨Q, hQ, hlen⟩
    obtain ⟨i, u, hu, hufib, hcube⟩ := golden_cube_exists_of_fib_length hQ
    exact ⟨i, u, hu, hufib.trans hlen.symm, hcube⟩

/-! ### Regression anchors -/

private theorem golden_fib_cube_small :
    ∃ i, IsGoldenPowerFactor 3 (fibWord 2) i := by
  exact golden_fib_cube_exists 0

private theorem golden_fib_cube_small_decide :
    goldenFactor 9 5 = wordPower 3 (fibWord 2) := by
  decide

#print axioms golden_fib_cube_exists
#print axioms golden_cube_exists_of_fib_length
#print axioms golden_cube_root_length_iff_fib

end D5.S1.Words.Powers
