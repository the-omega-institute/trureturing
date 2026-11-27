/- GID: D5/S3/Fourier/Concentration/DisjointSupportOccupationMass
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DisjointSupportOccupationMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential bounds for disjoint multinomial occupations. -/

import D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass

/-! A product bound for disjoint multinomial occupations. -/

set_option autoImplicit false
noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass (weight_factorials)

namespace D5.S3.Fourier.Concentration.DisjointSupportOccupationMass

variable {J : Type*} [Fintype J] [DecidableEq J]

private def scaledCoefficient (v : ℝ) (n : ℕ) : ℝ :=
  v ^ n / (n.factorial : ℝ)

private theorem scaled_weight (w : J → ℝ) (s : ℝ) {d : ℕ} {a : J → ℕ}
    (ha : a ∈ piAntidiag univ d) :
    s ^ d * monomialWeight w a = d.factorial * ∏ j, scaledCoefficient (s * w j) (a j) := by
  have hsum := (mem_piAntidiag.mp ha).1
  unfold scaledCoefficient
  rw [← weight_factorials (fun j => s * w j) d a hsum]
  have hs : (∏ j, s ^ a j) = s ^ d := by rw [prod_pow_eq_pow_sum, hsum]
  unfold monomialWeight
  simp only [mul_pow, prod_mul_distrib, hs]
  ring

def coordinateBox (d : ℕ) : Finset (ℕ × ℕ) :=
  (range (d + 1) ×ˢ range (d + 1)).filter fun p => p.1 = 0 ∨ p.2 = 0

private theorem sum_coordinateBox (x : ℝ) (d : ℕ) :
    (∑ p ∈ coordinateBox d, scaledCoefficient x p.1 * scaledCoefficient x p.2) =
      2 * (∑ k ∈ range (d + 1), scaledCoefficient x k) - 1 := by
  let R := range (d + 1)
  have hzero : 0 ∈ R := mem_range.mpr (Nat.succ_pos d)
  have hc : scaledCoefficient x 0 = 1 := by simp [scaledCoefficient]
  unfold coordinateBox
  change ∑ p ∈ (R ×ˢ R).filter _, _ = _
  simp only [sum_filter, sum_product]
  have h (a : ℕ) (ha : a ∈ R) :
      (∑ b ∈ R, if a = 0 ∨ b = 0 then
        scaledCoefficient x a * scaledCoefficient x b else 0) =
      (if a = 0 then ∑ b ∈ R, scaledCoefficient x b else scaledCoefficient x a) := by
    by_cases h0 : a = 0
    · simp [h0, hc]
    · simp [h0, hc, hzero]
  rw [sum_congr rfl h]
  have hrewrite (a : ℕ) :
      (if a = 0 then ∑ b ∈ R, scaledCoefficient x b else scaledCoefficient x a) =
        scaledCoefficient x a +
          (if a = 0 then (∑ b ∈ R, scaledCoefficient x b) - 1 else 0) := by
    by_cases ha : a = 0
    · simp [ha, hc]
    · simp [ha]
  simp_rw [hrewrite]
  rw [sum_add_distrib]
  simp only [sum_ite_eq', hzero, ite_true]
  ring

private theorem local_exponential_bound (x : ℝ) :
    2 * Real.exp x - 1 ≤ Real.exp (2 * x - (1 - Real.exp (-x)) ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg ((1 - Real.exp (-x)) ^ 2))
    (Real.exp_nonneg (2 * x))
  rw [← Real.exp_add] at h
  have he : Real.exp (2 * x) = Real.exp x ^ 2 := by
    rw [two_mul, Real.exp_add, sq]
  rw [he, Real.exp_neg] at h
  have hn := (Real.exp_pos x).ne'
  have hleft : Real.exp x ^ 2 * (1 - (1 - (Real.exp x)⁻¹) ^ 2) = 2 * Real.exp x - 1 := by
    field_simp
    ring
  rw [hleft] at h
  simpa only [sub_eq_add_neg, Real.exp_neg] using h

/-- The weight of ordered degree pairs whose occupation supports are disjoint. -/
def disjointMass (w : J → ℝ) (d : ℕ) : ℝ :=
  ∑ p ∈ (piAntidiag univ d ×ˢ piAntidiag univ d).filter
    (fun p : (J → ℕ) × (J → ℕ) => ∀ j, p.1 j = 0 ∨ p.2 j = 0),
    monomialWeight w p.1 * monomialWeight w p.2

/-- A coordinatewise exponential majorant for disjoint occupation pairs. -/
theorem scaled_disjoint_mass (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (d : ℕ) {s : ℝ}
    (hs : 0 ≤ s) :
    let envelope := fun x : ℝ => 2 * Real.exp x - 1
    let B := (d.factorial : ℝ) ^ 2 * ∏ j, envelope (s * w j)
    s ^ (2 * d) * disjointMass w d ≤ B ∧
      B ≤ (d.factorial : ℝ) ^ 2 *
        Real.exp (2 * s * (∑ j, w j) - ∑ j, (1 - Real.exp (-(s * w j))) ^ 2) := by
  dsimp only
  classical
  let P : Finset ((J → ℕ) × (J → ℕ)) := (piAntidiag univ d ×ˢ piAntidiag univ d).filter
    (fun p => ∀ j, p.1 j = 0 ∨ p.2 j = 0)
  let e : ((J → ℕ) × (J → ℕ)) ≃ (J → ℕ × ℕ) :=
    (Equiv.arrowProdEquivProdArrow J (fun _ => ℕ) (fun _ => ℕ)).symm
  let f (j : J) (p : ℕ × ℕ) := scaledCoefficient (s * w j) p.1 *
    scaledCoefficient (s * w j) p.2
  have hp (p) (hp : p ∈ P) :
      s ^ (2 * d) * (monomialWeight w p.1 * monomialWeight w p.2) =
        (d.factorial : ℝ) ^ 2 * ∏ j, f j (e p j) := by
    have hm := mem_product.mp (mem_filter.mp hp).1
    rw [two_mul, pow_add, mul_mul_mul_comm, scaled_weight w s hm.1, scaled_weight w s hm.2]
    change _ = (d.factorial : ℝ) ^ 2 * ∏ j,
      scaledCoefficient (s * w j) (p.1 j) * scaledCoefficient (s * w j) (p.2 j)
    rw [prod_mul_distrib]
    ring
  have hbox : P.map e.toEmbedding ⊆ Fintype.piFinset (fun _ : J => coordinateBox d) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hp
    have hm := mem_product.mp (mem_filter.mp ha).1
    have bound (u : J → ℕ) (hu : u ∈ piAntidiag univ d) (j : J) : u j < d + 1 := by
      rw [Nat.lt_succ_iff, ← (mem_piAntidiag.mp hu).1]
      exact single_le_sum (fun i _ => Nat.zero_le (u i)) (mem_univ j)
    apply Fintype.mem_piFinset.mpr
    intro j
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (bound _ hm.1 _),
      mem_range.mpr (bound _ hm.2 _)⟩, (mem_filter.mp ha).2 j⟩
  have hf (j : J) (p : ℕ × ℕ) : 0 ≤ f j p := by
    have h (k : ℕ) : 0 ≤ scaledCoefficient (s * w j) k :=
      div_nonneg (pow_nonneg (mul_nonneg hs (hw j)) k) (by positivity)
    exact mul_nonneg (h p.1) (h p.2)
  constructor
  · change s ^ (2 * d) * (∑ p ∈ P, monomialWeight w p.1 * monomialWeight w p.2) ≤ _
    rw [mul_sum, sum_congr rfl hp, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc
      _ = ∑ p ∈ P.map e.toEmbedding, ∏ j, f j (p j) := by rw [sum_map]; rfl
      _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : J => coordinateBox d), ∏ j, f j (p j) :=
        sum_le_sum_of_subset_of_nonneg hbox fun p _ _ => prod_nonneg fun j _ => hf j (p j)
      _ = ∏ j, ∑ p ∈ coordinateBox d, f j p := (prod_univ_sum _ _).symm
      _ ≤ _ := by
        apply prod_le_prod₀
        · exact fun j _ => sum_nonneg fun p _ => hf j p
        · intro j _
          dsimp [f]
          rw [sum_coordinateBox]
          have h := Real.sum_le_exp_of_nonneg (mul_nonneg hs (hw j)) (d + 1)
          dsimp only [scaledCoefficient]
          linarith
  · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc
      _ ≤ ∏ j, Real.exp (2 * (s * w j) - (1 - Real.exp (-(s * w j))) ^ 2) := by
        apply prod_le_prod₀
        · intro j _
          have h := Real.one_le_exp_iff.mpr (mul_nonneg hs (hw j))
          linarith
        · exact fun j _ => local_exponential_bound _
      _ = _ := by
        rw [← Real.exp_sum, sum_sub_distrib, mul_sum]
        congr 2
        apply sum_congr rfl
        intro j _
        ring

end D5.S3.Fourier.Concentration.DisjointSupportOccupationMass
