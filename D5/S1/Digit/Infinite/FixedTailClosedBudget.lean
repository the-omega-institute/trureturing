/- GID: D5/S1/Digit/Infinite/FixedTailClosedBudget
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/FixedTailClosedBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite affine endpoint certificate gives the least closed budget for all terminal values in two fixed interval hulls. -/

import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
import Mathlib.Data.Fintype.Lattice

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.FixedTailClosedBudget

private def intervalDistance (x l u : ℝ) : ℝ := max (l - x) (max 0 (x - u))

private def inBox (lo hi : Fin 2 → ℝ) (x : Fin 2 → ℝ) : Prop :=
  ∀ j, x j ∈ Set.Icc (lo j) (hi j)

private def value {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (x : Fin 2 → ℝ) (i : Fin m) : ℝ :=
  a i * x (source i) + b i

private theorem intervalDistance_nonneg (x l u : ℝ) : 0 ≤ intervalDistance x l u := by
  unfold intervalDistance
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem intervalDistance_bounds (x l u D : ℝ)
    (h : intervalDistance x l u ≤ D) :
    l - D ≤ x ∧ x ≤ u + D := by
  unfold intervalDistance at h
  have h₁ := (max_le_iff.mp h).1
  have h₂ := (max_le_iff.mp h).2
  have h₃ := (max_le_iff.mp h₂).2
  constructor <;> linarith

private theorem affine_endpoint_bound (a b lo hi l u x : ℝ) (hlo : lo ≤ hi)
    (hx : x ∈ Set.Icc lo hi) :
    intervalDistance (a * x + b) l u ≤
      max (intervalDistance (a * lo + b) l u)
        (intervalDistance (a * hi + b) l u) := by
  let D : ℝ := max (intervalDistance (a * lo + b) l u)
    (intervalDistance (a * hi + b) l u)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact (intervalDistance_nonneg _ _ _).trans (le_max_left _ _)
  have hleft : l - D ≤ a * lo + b ∧ a * lo + b ≤ u + D := by
    exact intervalDistance_bounds _ _ _ _ (le_max_left _ _)
  have hright : l - D ≤ a * hi + b ∧ a * hi + b ≤ u + D := by
    exact intervalDistance_bounds _ _ _ _ (le_max_right _ _)
  have hbetween : l - D ≤ a * x + b ∧ a * x + b ≤ u + D := by
    rcases hx with ⟨hxlo, hxhi⟩
    by_cases ha : 0 ≤ a
    · constructor <;> nlinarith
    · have ha' : a ≤ 0 := le_of_not_ge ha
      constructor <;> nlinarith
  change intervalDistance (a * x + b) l u ≤ D
  unfold intervalDistance
  apply max_le
  · linarith [hbetween.1]
  · apply max_le
    · exact hD
    · linarith [hbetween.2]

private theorem affine_endpoint_bound_for_slot
    {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ) (i : Fin m)
    (hlo : ∀ j, lo j ≤ hi j) (x : Fin 2 → ℝ) (hx : inBox lo hi x) :
    intervalDistance (value a b source x i) (left i) (right i) ≤
      max
        (intervalDistance (value a b source (fun j => lo j) i) (left i) (right i))
        (intervalDistance (value a b source (fun j => hi j) i) (left i) (right i)) := by
  apply affine_endpoint_bound (a i) (b i) (lo (source i)) (hi (source i))
    (left i) (right i) (x (source i)) (hlo (source i)) (hx (source i))

private def theta {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ) (hm : 0 < m) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i =>
    max
      (intervalDistance (value a b source (fun j => lo j) i) (left i) (right i))
      (intervalDistance (value a b source (fun j => hi j) i) (left i) (right i)))

private def closedAt {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (left right : Fin m → ℝ) (c : ℝ) (x : Fin 2 → ℝ) : Prop :=
  ∀ i, intervalDistance (value a b source x i) (left i) (right i) ≤ c

private def endpointAt {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ) (c : ℝ) : Prop :=
  ∀ i,
    intervalDistance (value a b source (fun j => lo j) i) (left i) (right i) ≤ c ∧
    intervalDistance (value a b source (fun j => hi j) i) (left i) (right i) ≤ c

/-- The complete finite endpoint certificate is the exact threshold for one fixed pair of
terminal interval hulls. The endpoint bound is obtained from affine branches, while the
finite supremum supplies the common budget for every slot at once. -/
theorem fixed_tail_closed_budget
    (m : ℕ) (hm : 0 < m) (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ)
    (hlo : ∀ j, lo j ≤ hi j) (hleft : ∀ i, left i ≤ right i) :
    let θ := theta a b source lo hi left right hm
    (0 ≤ θ) ∧
      (∀ c, 0 ≤ c →
        ((∃ x : Fin 2 → ℝ, inBox lo hi x ∧
            ∀ y : Fin 2 → ℝ, inBox lo hi y → closedAt a b source left right c y) ↔
          θ ≤ c) ∧
        (θ ≤ c → ∀ x : Fin 2 → ℝ, inBox lo hi x →
          ∀ y : Fin 2 → ℝ, inBox lo hi y → closedAt a b source left right c y)) := by
  dsimp only
  let θ := theta a b source lo hi left right hm
  have hθ_nonneg : 0 ≤ θ := by
    have hi0 : (⟨0, hm⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
    have h0 : 0 ≤ max
        (intervalDistance (value a b source (fun j => lo j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩))
        (intervalDistance (value a b source (fun j => hi j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩)) :=
      (intervalDistance_nonneg _ _ _).trans (le_max_left _ _)
    have hs : max
        (intervalDistance (value a b source (fun j => lo j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩))
        (intervalDistance (value a b source (fun j => hi j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩)) ≤ θ := by
      dsimp [θ, theta]
      exact Finset.le_sup' (fun i : Fin m =>
        max (intervalDistance (value a b source (fun j => lo j) i) (left i) (right i))
          (intervalDistance (value a b source (fun j => hi j) i) (left i) (right i))) hi0
    exact h0.trans hs
  have hendpoint_iff (c : ℝ) :
      (θ ≤ c ↔ endpointAt a b source lo hi left right c) := by
    constructor
    · intro hc i
      constructor
      · exact (le_max_left _ _).trans ((Finset.le_sup' _ (Finset.mem_univ i)).trans hc)
      · exact (le_max_right _ _).trans ((Finset.le_sup' _ (Finset.mem_univ i)).trans hc)
    · intro he
      dsimp [θ, theta]
      apply Finset.sup'_le
      intro i hi'
      exact max_le (he i).1 (he i).2
  refine ⟨hθ_nonneg, ?_⟩
  intro c hc
  constructor
  · constructor
    · rintro ⟨x, hx, hy⟩
      have he : endpointAt a b source lo hi left right c := by
        intro i
        constructor
        · exact (hy (fun j => lo j) (fun j => by simp [hlo j])) i
        · exact (hy (fun j => hi j) (fun j => by simp [hlo j])) i
      exact hendpoint_iff c |>.2 he
    · intro hcθ
      have he := hendpoint_iff c |>.1 hcθ
      let x : Fin 2 → ℝ := fun j => (lo j + hi j) / 2
      have hx : inBox lo hi x := by
        intro j
        dsimp [x]
        constructor <;> linarith [hlo j]
      refine ⟨x, hx, ?_⟩
      intro y hy i
      exact (affine_endpoint_bound_for_slot a b source lo hi left right i hlo y hy).trans
        (max_le (he i).1 (he i).2)
  · intro hcθ x hx y hy i
    have he := hendpoint_iff c |>.1 hcθ
    exact (affine_endpoint_bound_for_slot a b source lo hi left right
      i hlo y hy).trans (max_le (he i).1 (he i).2)

end D5.S1.Digit.Infinite.FixedTailClosedBudget
