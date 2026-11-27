/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSignedRows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSignedRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Products of the switching signs along occupied edges determine which endpoint sign variables agree. Zero-sum exterior rows yield an opposite signed occupied neighbor. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisValuation

/-! Semantic proofs of the local signed input rows. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedRows

open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec cubeBitVec_xor_single)
open BalancedCriticalSpectrum (Q flip)
open Q9SharedContactCNF (Word Variable)
open Q9TightDistanceTwoCNF (support)
open Q9FiveAxisValuation
open Q9FiveAxisSignedNormalization (rupFlipSign)
open Q9FiveAxisExteriorPolarity (exists_opposite_contribution)
open private signValue from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisValuation

structure Signing (S : Finset (Q 9)) (s : Q 9 → ℤ) : Prop where
  units : ∀ x ∈ S, s x = 1 ∨ s x = -1
  off_support : ∀ x ∉ S, s x = 0
  exterior : ∀ x ∉ S, ∑ i : Fin 9, rupFlipSign i x * s (flip x i) = 0
  edge : ∀ x ∈ S, ∀ a : Fin 9, flip x a ∈ S → rupFlipSign a x = s x * s (flip x a)

private def step (w : Word) (i : Fin 9) : Word := w ^^^ BitVec.ofNat 9 (2 ^ i.val)

private theorem step_cube (w : Word) (i : Fin 9) :
    cubeBitVec 9 (step w i) = flip (cubeBitVec 9 w) i := cubeBitVec_xor_single w i

/-- The polarity variable means that the vertex is occupied and its sign
matches the requested polarity. -/
theorem polarity_iff {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ}
    (b : Bool) (w : Word) (p : Bool) (h : Signing (support C D b) (f b)) :
    valuation C D f (polarityIndex b w p) ↔
      valuation C D f (Variable.occupied b w).index ∧
        (valuation C D f (signIndex b w) ↔ p = true) := by
  rw [polarity_value, occupancy_value, sign_value]
  let x := cubeBitVec 9 w
  change signValue (f b) p x ↔ x ∈ support C D b ∧ (f b x = 1 ↔ p = true)
  by_cases hx : x ∈ support C D b
  · rcases h.units x hx with hs | hs <;> cases p <;> simp [signValue, hx, hs]
  · have hz := h.off_support x hx
    cases p <;> simp [signValue, hx, hz]

/-- A selected edge fixes whether its endpoint sign bits agree. -/
theorem edge_sign_iff {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ}
    (b : Bool) (w : Word) (i : Fin 9) (h : Signing (support C D b) (f b))
    (hx : valuation C D f (Variable.occupied b w).index)
    (hy : valuation C D f (Variable.occupied b (step w i)).index) :
    ((valuation C D f (signIndex b w)) ↔
      valuation C D f (signIndex b (step w i))) ↔ rupFlipSign i (cubeBitVec 9 w) = 1 := by
  rw [occupancy_value] at hx hy
  rw [sign_value, sign_value, step_cube] at ⊢
  rw [step_cube] at hy
  have he := h.edge _ hx i hy
  rcases h.units _ hx with hp | hp <;> rcases h.units _ hy with hq | hq <;>
    norm_num [he, hp, hq]

/-- At an exterior point, a neighbor with the specified signed contribution
forces an occupied neighbor contributing the opposite sign. -/
theorem opposite_neighbor {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ}
    (b : Bool) (w : Word) (i : Fin 9) (p : ℤ)
    (h : Signing (support C D b) (f b)) (hp : p = 1 ∨ p = -1)
    (hx : ¬ valuation C D f (Variable.occupied b w).index)
    (hi : rupFlipSign i (cubeBitVec 9 w) * f b (cubeBitVec 9 (step w i)) = p) :
    ∃ j : Fin 9, rupFlipSign j (cubeBitVec 9 w) * f b (cubeBitVec 9 (step w j)) = -p := by
  rw [occupancy_value] at hx
  rw [step_cube] at hi
  have hvalues (x : Q 9) : f b x = 0 ∨ f b x = 1 ∨ f b x = -1 := by
    by_cases hm : x ∈ support C D b
    · exact Or.inr (h.units x hm)
    · exact Or.inl (h.off_support x hm)
  have hne : f b (flip (cubeBitVec 9 w) i) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hi
    rcases hp with hp' | hp' <;> omega
  obtain ⟨j, hj⟩ := exists_opposite_contribution hvalues (h.exterior _ hx) i hne
  exact ⟨j, by simpa only [step_cube, hi] using hj⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedRows
