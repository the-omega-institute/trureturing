/- GID: D5/S1/Digit/Infinite/SevenCycleActualRecords
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleActualRecords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interior targets and uniform positive periodic error margins. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionFuture
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleActualRecords

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleCollisionData
open private golden_data budget_bounds from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private actual_phase_mod from D5.S1.Digit.Infinite.SevenCycleCollisionRecords
open private entry_bounds uniform_colors from D5.S1.Digit.Infinite.SevenCycleCollisionColors

/-- A record uses one error sequence and a uniform strict margin for every observation. -/
def strictRecord (Q : ℝ → Fin 6) (b : ℝ) (x : LegalDigits) (r : ℕ → Fin 6)
    (e : ℕ → ℝ) (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ ∀ j,
    |e j| ≤ b - epsilon ∧
    kappa (bitShift x (3 * j)) + e j ∈ stateInterval false ∧
    Q (kappa (bitShift x (3 * j)) + e j) = r j

private theorem cell_geometry (c : Fin 6) :
    -1 ≤ cellLower c ∧ cellLower c < cellUpper c ∧ cellUpper c ≤ 1 + t := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  fin_cases c <;> norm_num [cellLower, cellUpper, cuts, lambda] <;>
    (repeat' apply And.intro) <;> linarith only [ht2, hg, hglo, hghi]

private theorem interior_target (a b x r : ℝ) (hab : a < b) (hr : 0 < r)
    (hx : x ∈ Set.Ioo (a - r) (b + r)) :
    ∃ p : ℝ, p ∈ Set.Ioo a b ∧ |p - x| < r := by
  have h : max a (x - r) < min b (x + r) := by
    apply max_lt
    · apply lt_min hab
      linarith [hx.1]
    · apply lt_min
      · linarith [hx.2]
      · linarith
  obtain ⟨p, hp, hp'⟩ := exists_between h
  refine ⟨p, ⟨lt_of_le_of_lt (le_max_left _ _) hp,
    lt_of_lt_of_le hp' (min_le_left _ _)⟩, ?_⟩
  rw [abs_lt]
  have h1 := lt_of_le_of_lt (le_max_right _ _) hp
  have h2 := lt_of_lt_of_le hp' (min_le_right _ _)
  constructor <;> linarith

private theorem periodic_targets : ∃ p : Bool → Fin 7 → ℝ,
    (∀ b j, p b j ∈ Set.Ioo (cellLower (phaseColor j)) (cellUpper (phaseColor j))) ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ b j,
      |p b j - phase (if b then firstEntry else rivalEntry) j| ≤ budget - epsilon := by
  classical
  have hbeta : 0 < budget := budget_bounds.2.2.1
  have h (b : Bool) (j : Fin 7) :
      ∃ p : ℝ, p ∈ Set.Ioo (cellLower (phaseColor j)) (cellUpper (phaseColor j)) ∧
        |p - phase (if b then firstEntry else rivalEntry) j| < budget := by
    apply interior_target _ _ _ _ (cell_geometry _).2.1 hbeta
    by_cases hj : j = 0
    · subst j
      cases b
      · simpa [phase, phaseColor] using entry_bounds.2.2.2.1
      · simpa [phase, phaseColor] using entry_bounds.2.2.1
    · apply uniform_colors _ _ j hj
      cases b
      · exact entry_bounds.2.1
      · exact entry_bounds.1
  choose p hp he using h
  let d (i : Bool × Fin 7) : ℝ :=
    budget - |p i.1 i.2 - phase (if i.1 then firstEntry else rivalEntry) i.2|
  let epsilon := Finset.univ.inf' (Finset.univ_nonempty :
    (Finset.univ : Finset (Bool × Fin 7)).Nonempty) d
  have heps : 0 < epsilon := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    dsimp [d]
    linarith [he i.1 i.2]
  refine ⟨p, hp, epsilon, heps, ?_⟩
  intro b j
  have hd : epsilon ≤ d (b, j) :=
    Finset.inf'_le _ (Finset.mem_univ (b, j))
  dsimp [d] at hd
  linarith

private theorem interior_owned (Q : ℝ → Fin 6) (hQ : instrument Q)
    (c : Fin 6) (p : ℝ) (hp : p ∈ Set.Ioo (cellLower c) (cellUpper c)) :
    Q p = c := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  have hs : p ∈ stateInterval false := by
    have hc := cell_geometry c
    exact ⟨hc.1.trans hp.1.le, hp.2.le.trans hc.2.2⟩
  have h := hQ p hs
  generalize hd : Q p = d at h ⊢
  fin_cases c <;> fin_cases d <;>
    norm_num [cellLower, cellUpper, cuts, lambda] at hp h ⊢ <;>
      linarith only [hp.1, hp.2, h.1, h.2, ht2, hg, hglo, hghi]

private theorem periodic_actual_records (Q : ℝ → Fin 6) (hQ : instrument Q) :
    ∃ e : Bool → ℕ → ℝ, ∃ epsilon : ℝ,
      strictRecord Q budget (source true)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e true) epsilon ∧
      strictRecord Q budget (source false)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e false) epsilon := by
  obtain ⟨p, hp, epsilon, heps, he⟩ := periodic_targets
  let e (b : Bool) (j : ℕ) := p b ⟨j % 7, Nat.mod_lt _ (by decide)⟩ -
    kappa (bitShift (source b) (3 * j))
  have hr (b : Bool) : strictRecord Q budget (source b)
      (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e b) epsilon := by
    refine ⟨heps, ?_⟩
    intro j
    have hm := actual_phase_mod b j
    have hb : |e b j| ≤ budget - epsilon := by
      dsimp [e]
      rw [hm]
      exact he b _
    have hx : kappa (bitShift (source b) (3 * j)) + e b j =
        p b ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by dsimp [e]; ring
    rw [hx]
    refine ⟨hb, ?_, interior_owned Q hQ _ _ (hp b _)⟩
    have hc := cell_geometry (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
    exact ⟨hc.1.trans (hp b _).1.le, (hp b _).2.le.trans hc.2.2⟩
  exact ⟨e, epsilon, hr true, hr false⟩

end D5.S1.Digit.Infinite.SevenCycleActualRecords

