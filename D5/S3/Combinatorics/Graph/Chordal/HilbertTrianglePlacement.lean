/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertTrianglePlacement
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-neighbor placement with two Hilbert reconstruction coefficients. -/

import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.ChordalResidualExtension
import D5.S3.Combinatorics.Graph.Chordal.HilbertTriangleCenter

compile_only_with_mathlib

/-! Omega original.

# Three-neighbor Hilbert insertion

One geometric placement proof is instantiated by the sharp two-piece
`259/200` closure and the independent one-interval `13/10` closure.
The tetrahedron bound here follows from the six edge bounds.
-/

namespace HilbertTriangleInsertion

open SimpleGraph.ChordalResidualExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem place_of_closure {R C : ℝ} (hnum : NumericalClosure R C)
    (r : Fin 3 → Fin 3 → E) (y : Fin 3 → E)
    (h : Neighborhood (Fin 3) r y R C 11) :
    ∃ z, Placement r y R C 11 z := by
  let x₀ := y 0 - y 1
  let x₁ := y 1 - y 2
  let x₂ := y 2 - y 0
  let d₀ := x₀ - r 0 1
  let d₁ := x₁ - r 1 2
  let d₂ := x₂ - r 2 0
  let S := ‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2
  have hsum : (r 0 1 + r 1 2 + r 2 0) + (d₀ + d₁ + d₂) = 0 := by
    dsimp [d₀, d₁, d₂, x₀, x₁, x₂]
    abel
  have htri : ‖r 0 1‖ ^ 2 + ‖r 1 2‖ ^ 2 + ‖r 2 0‖ ^ 2 -
      (2 / 3) * ‖r 0 1 + r 1 2 + r 2 0‖ ^ 2 ≤ C := by
    rw [h.skew 0 2, norm_neg, ← sub_eq_add_neg]
    exact h.tri 0 1 2
  have hdiam (i j : Fin 3) (t : ℝ) (ht : ‖r i j - (y i - y j)‖ ≤ t) :
      ‖y i - y j‖ ≤ R + t := by
    calc
      _ = ‖r i j - (r i j - (y i - y j))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖r i j‖ + ‖r i j - (y i - y j)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (h.edge i j) ht
  have hdiam₂ (i j : Fin 3) : ‖y i - y j‖ ^ 2 ≤ (R + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hdiam i j 1 (h.defect i j)) 2
  obtain ⟨c, q, hq, hc, hedge, hS⟩ := center_bounds y hdiam₂
  change (R + 1) ^ 2 / 4 < q → q * (6 * (R + 1) ^ 2 - S) ≤ ((R + 1) ^ 2) ^ 2 at hS
  have hd₀ : ‖d₀‖ ≤ 1 := (norm_sub_rev _ _).trans_le (h.defect 0 1)
  have hd₁ : ‖d₁‖ ≤ 1 := (norm_sub_rev _ _).trans_le (h.defect 1 2)
  have hd₂ : ‖d₂‖ ≤ 1 := (norm_sub_rev _ _).trans_le (h.defect 2 0)
  have hds₀ := pow_le_pow_left₀ (norm_nonneg _) hd₀ 2
  have hds₁ := pow_le_pow_left₀ (norm_nonneg _) hd₁ 2
  have hds₂ := pow_le_pow_left₀ (norm_nonneg _) hd₂ 2
  have hsum_of_defect (t : ℝ) (ht : 0 ≤ t) (ht₁ : t ≤ 1)
      (hd : ‖d₀‖ ^ 2 + ‖d₁‖ ^ 2 + ‖d₂‖ ^ 2 ≤ 2 + t ^ 2) :
      S ≤ C + 2 + t ^ 2 + 2 * Real.sqrt (C * (2 + t ^ 2)) := by
    have hT : 2 + t ^ 2 ≤ C := by
      nlinarith only [pow_le_pow_left₀ ht ht₁ 2, hnum.invariant_ge_three]
    have hh := centered_minkowski (r 0 1) (r 1 2) (r 2 0) d₀ d₁ d₂ hsum hd hT htri
    rw [show r 0 1 + d₀ = x₀ by dsimp [d₀]; abel,
      show r 1 2 + d₁ = x₁ by dsimp [d₁]; abel,
      show r 2 0 + d₂ = x₂ by dsimp [d₂]; abel] at hh
    dsimp [S]
    linarith only [hh]
  have hSnum := hsum_of_defect ‖d₀‖ (norm_nonneg _) hd₀ (by linarith only [hds₁, hds₂])
  have hrad := hnum.radius hq (norm_nonneg _) hd₀ (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by
      have := hnum.invariant_ge_three
      positivity)) hSnum hS
  have hnorm (i : Fin 3) : ‖y i - c‖ ≤ R :=
    (sq_le_sq₀ (norm_nonneg _) hnum.radius_nonneg).mp ((hc i).trans hrad)
  have bound (i j : Fin 3) (hij : i ≠ j)
      (hs : ‖d₀‖ ^ 2 + ‖d₁‖ ^ 2 + ‖d₂‖ ^ 2 ≤ 2 + ‖r i j - (y i - y j)‖ ^ 2) :
      ‖r i j‖ ^ 2 + ‖y j - c‖ ^ 2 + ‖y i - c‖ ^ 2 -
        (2 / 3) * ‖r i j - (y i - y j)‖ ^ 2 ≤ C := by
    let t := ‖r i j - (y i - y j)‖
    have hh := hsum_of_defect t (norm_nonneg _) (h.defect i j) hs
    have hside := pow_le_pow_left₀ (norm_nonneg _) (hdiam i j t le_rfl) 2
    have he : q * (4 * (R + 1) ^ 2 - (R + t) ^ 2) ≤ ((R + 1) ^ 2) ^ 2 := by
      exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hside _) hq).trans (hedge i j hij)
    have ht := hnum.child hq (norm_nonneg _) (h.defect i j) (Real.sqrt_nonneg _)
      (Real.sq_sqrt (by
        have := hnum.invariant_ge_three
        positivity)) hh hS he
    linarith only [ht, hc i, hc j, pow_le_pow_left₀ (norm_nonneg _) (h.edge i j) 2]
  have symm (i j : Fin 3) :
      ‖r j i - (y j - y i)‖ = ‖r i j - (y i - y j)‖ := by
    rw [h.skew i j, show -r i j - (y j - y i) = -(r i j - (y i - y j)) by abel, norm_neg]
  have sum₀ : ‖d₀‖ ^ 2 + ‖d₁‖ ^ 2 + ‖d₂‖ ^ 2 ≤ 2 + ‖r 0 1 - (y 0 - y 1)‖ ^ 2 := by
    have he : ‖d₀‖ = ‖r 0 1 - (y 0 - y 1)‖ := norm_sub_rev _ _
    rw [he]
    linarith only [hds₁, hds₂]
  have sum₁ : ‖d₀‖ ^ 2 + ‖d₁‖ ^ 2 + ‖d₂‖ ^ 2 ≤ 2 + ‖r 1 2 - (y 1 - y 2)‖ ^ 2 := by
    have he : ‖d₁‖ = ‖r 1 2 - (y 1 - y 2)‖ := norm_sub_rev _ _
    rw [he]
    linarith only [hds₀, hds₂]
  have sum₂ : ‖d₀‖ ^ 2 + ‖d₁‖ ^ 2 + ‖d₂‖ ^ 2 ≤ 2 + ‖r 2 0 - (y 2 - y 0)‖ ^ 2 := by
    have he : ‖d₂‖ = ‖r 2 0 - (y 2 - y 0)‖ := norm_sub_rev _ _
    rw [he]
    linarith only [hds₀, hds₁]
  refine ⟨c, ⟨hnorm, ?_, ?_⟩⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [h.skew.diagonal]
      have hh := hc i
      linarith only [hh, hrad, hnum.repeated_triangle]
    apply bound _ _ hij
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact sum₀
      | exact sum₁
      | exact sum₂
      | (rw [symm]; first | exact sum₀ | exact sum₁ | exact sum₂)
  · intro i j l
    have ht : ∀ x w, ‖r x w‖ ^ 2 ≤ R ^ 2 := fun x w =>
      pow_le_pow_left₀ (norm_nonneg _) (h.edge x w) 2
    have hR := hnum.tetrahedron_cap
    linarith only [ht i j, ht i l, ht j l, hc i, hc j, hc l, hrad, hR,
      sq_nonneg ‖holonomy r i j l‖, sq_nonneg ‖r i j - (y i - y j)‖,
      sq_nonneg ‖r i l - (y i - y l)‖, sq_nonneg ‖r j l - (y j - y l)‖]

/-- The original sharp two-piece placement API. -/
theorem place (r : Fin 3 → Fin 3 → E) (y : Fin 3 → E)
    (h : Neighborhood (Fin 3) r y R C 11) :
    ∃ z, Placement r y R C 11 z :=
  place_of_closure sharp_closure r y h

/-- Independent one-interval placement with triangle invariant `93/20`. -/
theorem ZeroSplit.place (r : Fin 3 → Fin 3 → E) (y : Fin 3 → E)
    (h : Neighborhood (Fin 3) r y ZeroSplit.R ZeroSplit.C 11) :
    ∃ z, Placement r y ZeroSplit.R ZeroSplit.C 11 z :=
  place_of_closure ZeroSplit.closure r y h

end HilbertTriangleInsertion
