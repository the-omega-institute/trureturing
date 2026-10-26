/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualityProfile
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualityProfile
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: A unique peak forces a tent profile and endpoint troughs. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraStripRigidity

/-! Profile rigidity for the crossed equality case on an actual height array. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraEqualityProfile

open MiuraHeightEnvelope MiuraStripRigidity

variable {m n : ℕ}

/-- A row profile keeps the original array values and horizontal neighbours. -/
def profile (h : Cell m n → ℤ) (i : Fin m) : Cell 1 n → ℤ := fun v => h (i, v.2)

private theorem profile_isHeight {h : Cell m n → ℤ} (hh : IsHeight h) (i : Fin m) :
    IsHeight (profile h i) := by
  intro v u hu
  apply hh (i, v.2) (i, u.2)
  simp only [adj, gdist] at hu ⊢
  have := v.1.isLt
  have := u.1.isLt
  omega

/-- The finite maximum envelope turns a unique profile maximum into an exact
tent. This identity is used to exclude internal troughs. -/
private theorem unique_peak_tent {h : Cell m n → ℤ} (hh : IsHeight h) (i : Fin m)
    (p : Fin n) (hp : ∀ q : Fin n,
      IsStrictLocalMax (profile h i) (0, q) → q = p) (j : Fin n) :
    h (i, j) = h (i, p) - (((p.val : ℤ) - j.val).natAbs : ℤ) := by
  obtain ⟨⟨q, hq, heq⟩, _⟩ := envelope_max (profile_isHeight hh i) ((0, j) : Cell 1 n)
  have hzero : q.1 = (0 : Fin 1) := Subsingleton.elim _ _
  have hqcell : q = (0, q.2) := Prod.ext hzero rfl
  have hq' : IsStrictLocalMax (profile h i) (0, q.2) := hqcell ▸ hq
  have he : q.2 = p := hp q.2 hq'
  simpa only [profile, gdist, hzero, he, Fin.val_zero, sub_self, Int.natAbs_zero,
    zero_add] using heq

/-- If a row profile has a unique local maximum, all its local minima are at
physical column endpoints. Endpoints are included in the uniqueness premise. -/
theorem unique_profile_peak_minima_on_boundary {h : Cell m n → ℤ} (hh : IsHeight h)
    (i : Fin m)
    (hu : ∃! p : Fin n, IsStrictLocalMax (profile h i) (0, p))
    (j : Fin n) (hj : IsStrictLocalMin (profile h i) (0, j)) :
    j.val = 0 ∨ j.val + 1 = n := by
  obtain ⟨p, hp, hunique⟩ := hu
  have htent := unique_peak_tent hh i p (fun q hq => hunique q hq)
  by_contra hnot
  have hj0 : 0 < j.val := by omega
  have hj1 : j.val + 1 < n := by have := j.isLt; omega
  let l : Fin n := ⟨j.val - 1, by omega⟩
  let r : Fin n := ⟨j.val + 1, hj1⟩
  have hl := hj ((0, l) : Cell 1 n) (by simp only [adj, gdist, l]; omega)
  have hr := hj ((0, r) : Cell 1 n) (by simp only [adj, gdist, r]; omega)
  change h (i, l) = h (i, j) + 1 at hl
  change h (i, r) = h (i, j) + 1 at hr
  have hjt := htent j
  have hlt := htent l
  have hrt := htent r
  dsimp [l, r] at *
  omega

/-- Negating the actual array supplies the other sign of the first-reversal
lemma, including physical column endpoints. -/
private theorem first_reversal_has_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (i : Fin m) (hi0 : 0 < i.val) (hi1 : i.val + 1 < m)
    (hprev : ∀ j : Fin n,
      h (i, j) = h (⟨i.val - 1, by omega⟩, j) - 1)
    (hrev : ∃ j : Fin n, h (⟨i.val + 1, hi1⟩, j) = h (i, j) + 1) :
    ∃ j : Fin n, IsStrictLocalMin h (i, j) ∧
      h (⟨i.val + 1, hi1⟩, j) = h (i, j) + 1 := by
  have hn : IsHeight (fun v => -h v) := by
    intro v u hu
    simpa only [neg_sub_neg, abs_sub_comm] using hh v u hu
  obtain ⟨j, hj, hdown⟩ := first_reversal_has_maximum hn i hi0 hi1 (by
    intro j; have := hprev j; change -h (i, j) = -h (⟨i.val - 1, _⟩, j) + 1; omega) (by
    obtain ⟨j, hj⟩ := hrev
    exact ⟨j, by change -h (⟨i.val + 1, _⟩, j) = -h (i, j) - 1; omega⟩)
  refine ⟨j, ?_, ?_⟩
  · intro u hu
    have := hj u hu
    dsimp at this
    omega
  · change -h (⟨i.val + 1, _⟩, j) = -h (i, j) - 1 at hdown
    omega

/-- A first reversal out of a descending extrusion whose current profile has
one peak creates an actual minimum on a physical side. -/
theorem reversal_after_unique_peak_on_boundary {h : Cell m n → ℤ} (hh : IsHeight h)
    (i : Fin m) (hi0 : 0 < i.val) (hi1 : i.val + 1 < m)
    (hprev : ∀ j : Fin n,
      h (i, j) = h (⟨i.val - 1, by omega⟩, j) - 1)
    (hrev : ∃ j : Fin n, h (⟨i.val + 1, hi1⟩, j) = h (i, j) + 1)
    (hu : ∃! p : Fin n, IsStrictLocalMax (profile h i) (0, p)) :
    ∃ j : Fin n, (j.val = 0 ∨ j.val + 1 = n) ∧ IsStrictLocalMin h (i, j) := by
  obtain ⟨j, hj, _⟩ := first_reversal_has_minimum hh i hi0 hi1 hprev hrev
  have hprofile : IsStrictLocalMin (profile h i) (0, j) := by
    intro u hu
    apply hj (i, u.2)
    simp only [adj, gdist] at hu ⊢
    omega
  exact ⟨j, unique_profile_peak_minima_on_boundary hh i hu j hprofile, hj⟩

end D5.S3.Combinatorics.Geometry.MiuraEqualityProfile
