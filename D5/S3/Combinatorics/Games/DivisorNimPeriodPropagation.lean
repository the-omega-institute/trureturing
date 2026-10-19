/- GID: D5/S3/Combinatorics/Games/DivisorNimPeriodPropagation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimPeriodPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite mex recurrence blocks propagate equality and singleton boards have their native heap value. -/

import D5.S3.Combinatorics.Games.DivisorNimBoundOutcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

/-- Equal full lookback blocks and common forcing determine the same infinite tail. -/
theorem mex_forced_block_propagation (D : ℕ) (B : Finset ℕ)
    (hB : ∀ d ∈ B, 0 < d ∧ d ≤ D)
    (f g : ℕ → ℕ) (F : ℕ → Finset ℕ)
    (hblock : ∀ t, t < D → f t = g t)
    (hf : ∀ t, D ≤ t → f t = mex (F t ∪ B.image (fun d => f (t - d))))
    (hg : ∀ t, D ≤ t → g t = mex (F t ∪ B.image (fun d => g (t - d)))) :
    ∀ t, f t = g t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t < D
    · exact hblock t ht
    · rw [hf t (by omega), hg t (by omega)]
      congr 2
      apply Finset.image_congr
      intro d hd
      have hdB := hB d hd
      exact ih (t - d) (by omega)

/-- Every legal singleton removal yields exactly the preceding Grundy values. -/
theorem singleton_grundy : ∀ n, 0 < n → grundy ({n} : Position) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hvals : (moves ({n} : Position)).image grundy = Finset.range n := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_image.mp hv with ⟨Q, hQ, rfl⟩
        rcases moves_spec hQ with ⟨h, hh, d, hd, rfl⟩
        have he : h = n := by simpa using hh
        subst h
        have herase : ({n} : Position).erase n = 0 := by simp
        by_cases he : n - d = 0
        · simp only [successor, he, if_true, Multiset.erase_singleton,
            Multiset.add_zero, grundy_empty, Finset.mem_range]
          exact hn
        · have hs : successor ({n} : Position) n d = {n - d} := by
            simp [successor, he]
          rw [hs, ih (n - d) (by have := hd.1; omega) (by omega)]
          exact Finset.mem_range.mpr (by have := hd.1; omega)
      · intro hv
        have hvn := Finset.mem_range.mp hv
        have hd : legal ({n} : Position) n (n - v) := by
          exact ⟨by omega, by omega, by simp [dividesAll]⟩
        have hQ := successor_is_move (P := ({n} : Position)) (by simp) hd
        refine Finset.mem_image.mpr ⟨_, hQ, ?_⟩
        by_cases hv0 : v = 0
        · subst v
          simp [successor, grundy_empty]
        · have hs : successor ({n} : Position) n (n - v) = {v} := by
            simp [successor, Nat.sub_sub_self (by omega : v ≤ n), hv0]
          rw [hs, ih v hvn (by omega)]
    rw [grundy_eq, hvals]
    apply le_antisymm
    · by_contra h
      have := (mex_spec (Finset.range n)).2 n (by omega)
      simp at this
    · by_contra h
      exact (mex_spec (Finset.range n)).1 (Finset.mem_range.mpr (by omega))

end D5.S3.Combinatorics.Games.DivisorNimGrundy
