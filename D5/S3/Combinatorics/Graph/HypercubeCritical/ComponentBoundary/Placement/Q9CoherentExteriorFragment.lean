/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9CoherentExteriorFragment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9CoherentExteriorFragment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed face swaps transport two-term cancellation into agreement at the hub. Each coherent term requires a compensating term, and at equality every compensator has the opposite sign. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! Coherent exterior fragments force an equal number of compensating neighbors. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CoherentExteriorFragment

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply IsBalanced IsSwitching switchingVector)
open BalancedCubeComponentBoundary (directions mem_directions flip_injective)
open BalancedCubeGirth (gamma_anticommute)
open TwentyPointEightWord (gamma_square)
open Q9SignedFragmentBoundary (signedFragment card_add_abs_le)
open private fullRow_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary

open Classical in
private theorem exterior_row_zero {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) {v : Q 9} (hv : v ∉ C) :
    (∑ a ∈ directions C v, gamma a (switchingVector C σ) v) = 0 := by
  classical
  calc
    _ = signedFragment C σ v := by
      unfold signedFragment
      apply Finset.sum_congr rfl
      intro a ha
      rw [gamma_apply, switchingVector, ite_eq_left ((mem_directions C v a).mp ha)]
    _ = 0 := fullRow_zero hr hs v hv

/-- Applying the two face swaps transports midpoint cancellation into equality at the hub. -/
private theorem hub_terms_eq {f : Q 9 → ℝ} {h : Q 9} {a b : Fin 9}
    (hab : a ≠ b)
    (hrow : gamma a f (flip (flip h a) b) + gamma b f (flip (flip h a) b) = 0) :
    gamma a f h = gamma b f h := by
  have hzero : gamma a (gamma b (gamma a f + gamma b f)) h = 0 := by
    rw [gamma_apply a, gamma_apply b, Pi.add_apply, hrow, mul_zero, mul_zero]
  have hswap : gamma a (gamma b (gamma a f)) = -gamma b f := by
    rw [gamma_anticommute hab (gamma a f), gamma_square a f]
  have hdiff : -(gamma b f h) + gamma a f h = 0 := by
    simpa only [map_add, hswap, gamma_square b f, Pi.add_apply, Pi.neg_apply] using hzero
  linarith only [hdiff]

open Classical in
private theorem hub_align {C : Finset (Q 9)} {σ : Q 9 → ℝ} {h : Q 9} {i : Fin 9}
    {A : Finset (Fin 9)} (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ)
    (hfaces : ∀ j ∈ A, i ≠ j →
      flip (flip h i) j ∉ C ∧ directions C (flip (flip h i) j) = {i, j})
    (a : Fin 9) (ha : a ∈ A) :
    gamma a (switchingVector C σ) h = gamma i (switchingVector C σ) h := by
  by_cases he : i = a
  · rw [he]
  obtain ⟨hout, hdirs⟩ := hfaces a ha he
  have hrow := exterior_row_zero hr hs hout
  rw [hdirs, Finset.sum_pair he] at hrow
  exact (hub_terms_eq (f := switchingVector C σ) (h := h) he hrow).symm

open Classical in
private theorem hub_term_square {C : Finset (Q 9)} {σ : Q 9 → ℝ} {h : Q 9}
    (hs : IsSwitching C σ) (a : Fin 9) (ha : a ∈ directions C h) :
    (gamma a (switchingVector C σ) h) ^ 2 = 1 := by
  have hm := (mem_directions C h a).mp ha
  rw [gamma_apply, switchingVector, ite_eq_left hm, mul_pow,
    SupportedEigenSaturation.matrix_sq_of_adj (flip_adj h a),
    BalancedCriticalSpectrum.switching_sq hs hm, mul_one]

open Classical in
/-- Two-term cancellation at the other corners of the faces through a fixed
axis aligns all terms in the fragment at the exterior hub. Cancellation there
requires at least as many occupied directions outside the fragment. -/
theorem twice_card_le_directions_of_coherent_exterior_fragment
    {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {h : Q 9} (hh : h ∉ C) {i : Fin 9}
    {A : Finset (Fin 9)} (hi : i ∈ A) (hsub : A ⊆ directions C h)
    (hfaces : ∀ j ∈ A, i ≠ j →
      flip (flip h i) j ∉ C ∧ directions C (flip (flip h i) j) = {i, j}) :
    2 * A.card ≤ (directions C h).card := by
  classical
  obtain ⟨σ, hs⟩ := hb
  let f := switchingVector C σ
  have hleaf (a : Fin 9) (ha : a ∈ A) : flip h a ∈ C :=
    (mem_directions C h a).mp (hsub ha)
  have halign (a : Fin 9) (ha : a ∈ A) : gamma a f h = gamma i f h :=
    hub_align hr hs hfaces a ha
  let K := A.image (flip h)
  have hKC : K ⊆ C := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact hleaf a ha
  have hK : directions K h = A := by
    ext a
    rw [mem_directions]
    constructor
    · intro ha
      obtain ⟨b, hbA, he⟩ := Finset.mem_image.mp ha
      exact (flip_injective h he) ▸ hbA
    · intro ha
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hsum : signedFragment K σ h = (A.card : ℝ) * gamma i f h := by
    unfold signedFragment
    rw [hK]
    calc
      _ = ∑ a ∈ A, gamma a f h := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [gamma_apply, f, switchingVector, hleaf a ha]
      _ = ∑ _a ∈ A, gamma i f h := Finset.sum_congr rfl halign
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hunit : |gamma i f h| = 1 := by
    have hsign : |f (flip h i)| = 1 := by
      rcases hs.1 _ (hleaf i hi) with hs' | hs' <;>
        simp [f, switchingVector, hleaf i hi, hs']
    rw [gamma_apply, abs_mul, SupportedEigenSaturation.matrix_abs_of_adj (flip_adj h i),
      hsign, mul_one]
  have habs : |signedFragment K σ h| = (A.card : ℝ) := by
    rw [hsum, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), hunit, mul_one]
  have hreal : (2 : ℝ) * (A.card : ℝ) ≤ ((directions C h).card : ℝ) := calc
    2 * (A.card : ℝ) = (A.card : ℝ) + |signedFragment K σ h| := by rw [habs, two_mul]
    _ ≤ ((directions C h).card : ℝ) := by
      simpa only [hK] using card_add_abs_le hKC hr hs h hh
  exact_mod_cast hreal

#print axioms twice_card_le_directions_of_coherent_exterior_fragment

open Classical in
/-- Two opposite exterior corners of a face cannot both have exactly the
other two corners as their neighbors in the balanced cubic support. -/
theorem no_two_neighbor_pair_at_both_corners
    {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {h : Q 9} {i j : Fin 9} (hij : i ≠ j)
    (hh : h ∉ C) (hdirs : directions C h = {i, j})
    (hother : flip (flip h i) j ∉ C) :
    directions C (flip (flip h i) j) ≠ {i, j} := by
  intro he
  obtain ⟨σ, hs⟩ := hb
  have hrow := exterior_row_zero hr hs hother
  rw [he, Finset.sum_pair hij] at hrow
  have hagree := hub_terms_eq (h := h) hij hrow
  have hzero := exterior_row_zero hr hs hh
  rw [hdirs, Finset.sum_pair hij, ← hagree] at hzero
  have hunit := hub_term_square hs i (by rw [hdirs]; simp)
  have ht : gamma i (switchingVector C σ) h = 0 := by linarith only [hzero]
  rw [ht] at hunit
  norm_num at hunit

open Classical in
/-- When the exterior degree is twice the number of coherent directions,
every remaining direction has the opposite signed contribution. -/
theorem terms_eq_of_tight_coherent_exterior_fragment
    {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) {h : Q 9} (hh : h ∉ C) {i : Fin 9}
    {A : Finset (Fin 9)} (hi : i ∈ A) (hsub : A ⊆ directions C h)
    (hfaces : ∀ j ∈ A, i ≠ j →
      flip (flip h i) j ∉ C ∧ directions C (flip (flip h i) j) = {i, j})
    (htight : (directions C h).card = 2 * A.card) :
    ∀ a ∈ directions C h \ A,
      gamma a (switchingVector C σ) h = -(gamma i (switchingVector C σ) h) := by
  let B := directions C h \ A
  let t := fun a => gamma a (switchingVector C σ) h
  have hB : B.card = A.card := by
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    change B.card + A.card = _ at hcard
    omega
  have hsquare (a : Fin 9) (ha : a ∈ directions C h) : (t a) ^ 2 = 1 :=
    hub_term_square hs a ha
  have hpivot := hsquare i (hsub hi)
  have haSum : ∑ a ∈ A, t a = (A.card : ℝ) * t i := by
    calc
      _ = ∑ _a ∈ A, t i := Finset.sum_congr rfl (hub_align hr hs hfaces)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsum := exterior_row_zero hr hs hh
  change (∑ a ∈ directions C h, t a) = 0 at hsum
  rw [← Finset.sum_sdiff hsub, haSum] at hsum
  change (∑ a ∈ B, t a) + (A.card : ℝ) * t i = 0 at hsum
  have hbSum : ∑ a ∈ B, t a = -(A.card : ℝ) * t i := by linarith
  have hterms : ∑ a ∈ B, (t a * t i + 1) = 0 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hbSum, Finset.sum_const,
      nsmul_eq_mul, mul_one, hB]
    calc
      _ = -(A.card : ℝ) * (t i) ^ 2 + (A.card : ℝ) := by ring
      _ = 0 := by rw [hpivot]; ring
  have hpos (a : Fin 9) (ha : a ∈ B) : 0 ≤ t a * t i + 1 := by
    rcases sq_eq_one_iff.mp hpivot with hp | hp <;>
      rcases sq_eq_one_iff.mp (hsquare a (Finset.mem_sdiff.mp ha).1) with h | h <;>
      norm_num [h,hp]
  intro a ha
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hpos).mp hterms a ha
  change t a = - t i
  rcases sq_eq_one_iff.mp hpivot with h | h <;> rw [h] at hz ⊢ <;> linarith

#print axioms terms_eq_of_tight_coherent_exterior_fragment

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CoherentExteriorFragment
