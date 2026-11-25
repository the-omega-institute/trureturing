/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The signed cube identity bounds all unsigned direction energies on a balanced support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import Mathlib.Algebra.QuadraticDiscriminant

/-! For Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2, the signed
coordinate flips imply a joint quadratic constraint on edge counts.
A vector constant on both shores of a cut turns this into a two-variable
quadratic form in the shore values. The weighted cut argument is due to GPT-6 Pro. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedCutEnergy

open scoped BigOperators Matrix
open Finset
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open Q9IsotropicHuang (flipSign weightedAction weightedLinear weightedLinear_apply)
open Q9SignedContactCells (weighted_square)
open Q9WeightedBoundaryGram (signed signed_mulVec signed_transpose)
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

private theorem squared_norm_weighted (w : Fin 9 → ℝ) (f : Q 9 → ℝ) :
    (∑ x, (weightedLinear w f x) ^ 2) = (∑ i, w i ^ 2) * (∑ x, f x ^ 2) := by
  let A := signed w
  have h := Matrix.dotProduct_transpose_mulVec A (A *ᵥ f) f
  simp only [A, signed_transpose, signed_mulVec, weighted_square, dotProduct_smul, smul_eq_mul] at h
  simpa only [dotProduct, pow_two] using h

/-- The signed directional correlation of a vector and its coordinate flip. -/
private def signedCorrelation (f : Q 9 → ℝ) (i : Fin 9) : ℝ :=
  ∑ x, f x * (flipSign i x : ℝ) * f (flip x i)

private theorem sum_sq_signedCorrelation (f : Q 9 → ℝ) :
    (∑ i, signedCorrelation f i ^ 2) ≤ (∑ x, f x ^ 2) ^ 2 := by
  let w := signedCorrelation f
  let E : ℝ := ∑ x, f x ^ 2
  let D : ℝ := ∑ i, w i ^ 2
  have hsum : (∑ x, f x * weightedLinear w f x) = D := by
    simp only [weightedLinear_apply, weightedAction, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ x : Q 9, f x * (w i * (flipSign i x : ℝ) * f (flip x i))) = w i ^ 2
    calc
      _ = ∑ x : Q 9, w i * (f x * (flipSign i x : ℝ) * f (flip x i)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = w i ^ 2 := by
        rw [← Finset.mul_sum]
        change w i * w i = _
        ring
  have hnorm : (∑ x, (weightedLinear w f x) ^ 2) = D * E :=
    squared_norm_weighted w f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ f (weightedLinear w f)
  rw [hsum, hnorm] at hcs
  change D ^ 2 ≤ E * (D * E) at hcs
  change D ≤ E ^ 2
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
  rcases eq_or_lt_of_le hD with hzero | hpositive
  · rw [← hzero]
    exact sq_nonneg _
  · apply le_of_mul_le_mul_right _ hpositive
    calc
      D * D = D ^ 2 := by ring
      _ ≤ E * (D * E) := hcs
      _ = E ^ 2 * D := by ring

/-- On a balanced support, the ordinary coordinate correlations satisfy the same
joint bound as the signed cube. The vector may take arbitrary real values on
the selected vertices, so this applies to all two-shore test vectors at once. -/
theorem sum_sq_direction_correlation_le (C : Finset (Q 9)) (hb : IsBalanced C)
    (f : Q 9 → ℝ) (hf : ∀ x ∉ C, f x = 0) :
    (∑ i : Fin 9, (∑ x : Q 9, f x * f (flip x i)) ^ 2) ≤ (∑ x, f x ^ 2) ^ 2 := by
  obtain ⟨s, hs⟩ := hb
  let g : Q 9 → ℝ := fun x => s x * f x
  have hs_sq (x : Q 9) (hx : x ∈ C) : s x ^ 2 = 1 := by
    rcases hs.1 x hx with h | h <;> norm_num [h]
  have hsame (i : Fin 9) : signedCorrelation g i = ∑ x : Q 9, f x * f (flip x i) := by
    unfold signedCorrelation
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ C
    · by_cases hy : flip x i ∈ C
      · rw [flipSign_cast, hs.2 x hx (flip x i) hy (flip_adj x i)]
        calc
          _ = (s x ^ 2) * (s (flip x i) ^ 2) * (f x * f (flip x i)) := by
            dsimp only [g]
            ring
          _ = _ := by rw [hs_sq x hx, hs_sq _ hy, one_mul, one_mul]
      · simp [g, hf _ hy]
    · simp [g, hf _ hx]
  have hmass : (∑ x, g x ^ 2) = ∑ x, f x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ C
    · change (s x * f x) ^ 2 = _
      rw [mul_pow, hs_sq x hx, one_mul]
    · simp [g, hf _ hx]
  simpa only [hsame, hmass] using sum_sq_signedCorrelation g

/-- Count endpoints on the first shore whose flip lies on the second shore. -/
def directedPairCount (H K : Finset (Q 9)) (i : Fin 9) : ℕ :=
  (H.filter fun x => flip x i ∈ K).card

private theorem directedPairCount_symm (H K : Finset (Q 9)) (i : Fin 9) :
    directedPairCount H K i = directedPairCount K H i := by
  classical
  unfold directedPairCount
  refine Finset.card_bij (fun x _ => flip x i) ?_ ?_ ?_
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.2, by simpa only [
      BalancedCriticalSpectrum.flip_flip] using hx'.1⟩
  · intro x _ y _ h
    simpa only [BalancedCriticalSpectrum.flip_flip] using
      congrArg (fun z => BalancedCriticalSpectrum.flip z i) h
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact ⟨flip y i, Finset.mem_filter.mpr ⟨hy'.2, by simpa only [
      BalancedCriticalSpectrum.flip_flip] using hy'.1⟩, BalancedCriticalSpectrum.flip_flip y i⟩

private def constantOn (S : Finset (Q 9)) (u : ℝ) (x : Q 9) : ℝ :=
  if x ∈ S then u else 0

private theorem constantOn_correlation (H K : Finset (Q 9)) (s t : ℝ) (i : Fin 9) :
    (∑ x : Q 9, constantOn H s x * constantOn K t (flip x i)) =
      (directedPairCount H K i : ℝ) * (s * t) := by
  classical
  let U := H.filter fun x => flip x i ∈ K
  calc
    _ = ∑ x : Q 9, if x ∈ U then s * t else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ H <;> by_cases hy : flip x i ∈ K <;>
        simp [constantOn, U, hx, hy]
    _ = ∑ _ ∈ U, s * t := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = _ := by simp [U, directedPairCount, nsmul_eq_mul]

private theorem constantOn_norm (H K : Finset (Q 9)) (hd : Disjoint H K) (s t : ℝ) :
    (∑ x : Q 9, (constantOn H s x + constantOn K t x) ^ 2) =
      (H.card : ℝ) * s ^ 2 + (K.card : ℝ) * t ^ 2 := by
  classical
  have hsplit (x : Q 9) :
      (constantOn H s x + constantOn K t x) ^ 2 =
        (if x ∈ H then s ^ 2 else 0) + (if x ∈ K then t ^ 2 else 0) := by
    by_cases hx : x ∈ H
    · have hy : x ∉ K := fun hk => Finset.disjoint_left.mp hd hx hk
      simp [constantOn, hx, hy]
    · simp [constantOn, hx]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- Two disjoint shores in a balanced support obey one simultaneous quadratic
bound on their internal and crossing direction counts. -/
theorem cut_direction_energy (H K : Finset (Q 9)) (hd : Disjoint H K)
    (hb : IsBalanced (H ∪ K)) (s t : ℝ) :
    (∑ i : Fin 9, ((directedPairCount H H i : ℝ) * s ^ 2 +
      (directedPairCount K K i : ℝ) * t ^ 2 +
      2 * (directedPairCount H K i : ℝ) * s * t) ^ 2) ≤
      ((H.card : ℝ) * s ^ 2 + (K.card : ℝ) * t ^ 2) ^ 2 := by
  let f : Q 9 → ℝ := fun x => constantOn H s x + constantOn K t x
  have hf (x : Q 9) (hx : x ∉ H ∪ K) : f x = 0 := by
    have hh : x ∉ H := fun h => hx (Finset.mem_union_left _ h)
    have hk : x ∉ K := fun h => hx (Finset.mem_union_right _ h)
    simp [f, constantOn, hh, hk]
  have he (i : Fin 9) :
      (∑ x : Q 9, f x * f (flip x i)) =
        (directedPairCount H H i : ℝ) * s ^ 2 +
        (directedPairCount K K i : ℝ) * t ^ 2 +
        2 * (directedPairCount H K i : ℝ) * s * t := by
    simp only [f, add_mul, mul_add, Finset.sum_add_distrib, constantOn_correlation]
    rw [directedPairCount_symm K H i]
    ring
  have h := sum_sq_direction_correlation_le (H ∪ K) hb f hf
  simpa only [he, f, constantOn_norm H K hd s t] using h

/-- For a balanced cubic support with the same total count in every direction,
the cut edge counts obey the determinant inequality of a real quadratic form.
The two count assumptions use directed counts on internal edges and one
orientation on each crossing edge. -/
theorem cut_count_discriminant (H K : Finset (Q 9)) (hd : Disjoint H K)
    (hb : IsBalanced (H ∪ K))
    (haxis : ∀ i, (directedPairCount H H i : ℝ) + directedPairCount K K i +
      2 * directedPairCount H K i = ((H.card + K.card : ℕ) : ℝ) / 3)
    (hvalence : ∑ i : Fin 9, ((directedPairCount H H i : ℝ) + directedPairCount H K i) =
      3 * (H.card : ℝ)) :
    let a : ℝ := H.card
    let N : ℝ := (H.card + K.card : ℕ)
    let c (i : Fin 9) : ℝ := directedPairCount H K i
    let h (i : Fin 9) : ℝ := directedPairCount H H i + c i - a / 3
    let total := ∑ i, c i
    ((∑ i, h i * c i) - total * (N - 2 * a) / 6) ^ 2 ≤
      (total * N / 6 - ∑ i, h i ^ 2) * (total * N / 6 - ∑ i, c i ^ 2) := by
  dsimp only
  let a : ℝ := H.card
  let N : ℝ := (H.card + K.card : ℕ)
  let c (i : Fin 9) : ℝ := directedPairCount H K i
  let h (i : Fin 9) : ℝ := directedPairCount H H i + c i - a / 3
  let total := ∑ i, c i
  let A := total * N / 6 - ∑ i, h i ^ 2
  let B := (∑ i, h i * c i) - total * (N - 2 * a) / 6
  let D := total * N / 6 - ∑ i, c i ^ 2
  change B ^ 2 ≤ A * D
  have hzero : ∑ i, h i = 0 := by
    simp only [h, Finset.sum_sub_distrib, c, hvalence, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    change 3 * a - 9 * (a / 3) = 0
    ring
  have hquad (S : ℝ) : 0 ≤ A * (S * S) + (2 * B) * S + D := by
    let s := (S + 1) / 2
    let t := (S - 1) / 2
    let L := a * s ^ 2 + (K.card : ℝ) * t ^ 2
    have hr (i : Fin 9) :
        (directedPairCount H H i : ℝ) * s ^ 2 +
          (directedPairCount K K i : ℝ) * t ^ 2 +
          2 * (directedPairCount H K i : ℝ) * s * t = L / 3 + S * h i - c i := by
      have ht := haxis i
      push_cast at ht
      dsimp [L, h, a, c, s, t]
      linear_combination ((S - 1) / 2) ^ 2 * ht
    have hL : L = (N * (S ^ 2 + 1) - 2 * (N - 2 * a) * S) / 4 := by
      dsimp [L, N, a, s, t]
      push_cast
      ring
    have hn := cut_direction_energy H K hd hb s t
    simp only [hr] at hn
    change (∑ i, (L / 3 + S * h i - c i) ^ 2) ≤ L ^ 2 at hn
    have hpoint (i : Fin 9) :
        (L / 3 + S * h i - c i) ^ 2 =
          L ^ 2 / 9 + S ^ 2 * h i ^ 2 + c i ^ 2 -
          (2 * S) * (h i * c i) + ((2 * L * S) / 3) * h i - ((2 * L) / 3) * c i := by
      ring
    have hsum :
        (∑ i : Fin 9, (L / 3 + S * h i - c i) ^ 2) =
          L ^ 2 + S ^ 2 * (∑ i, h i ^ 2) + (∑ i, c i ^ 2) -
          (2 * S) * (∑ i, h i * c i) - ((2 * L) / 3) * total := by
      simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hzero]
      change 9 * (L ^ 2 / 9) + S ^ 2 * (∑ i, h i ^ 2) + (∑ i, c i ^ 2) -
        (2 * S) * (∑ i, h i * c i) + ((2 * L * S) / 3) * 0 - ((2 * L) / 3) * total = _
      ring
    rw [hsum, hL] at hn
    dsimp only [A, B, D]
    linarith only [hn]
  have he := discrim_le_zero hquad
  unfold discrim at he
  linarith only [he]

#print axioms sum_sq_direction_correlation_le
#print axioms cut_direction_energy
#print axioms cut_count_discriminant


private theorem sum_sq_ge_sum_sq_div_card (S : Finset (Fin 9)) (f : Fin 9 → ℝ) :
    (∑ i ∈ S, f i) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) f

private theorem three_directions_reduced_energy {a : ℝ} (M : Finset (Fin 9)) (hM : M.card = 3)
    (h c : Fin 9 → ℝ) (hc : ∀ i, c i = if i ∈ M then 3 else 0)
    (he : ((∑ i, h i * c i) - (∑ i, c i) * (90 - 2 * a) / 6) ^ 2 ≤
      ((∑ i, c i) * 90 / 6 - ∑ i, h i ^ 2) * ((∑ i, c i) * 90 / 6 - ∑ i, c i ^ 2)) :
    (∑ i, h i ^ 2) + ((∑ i ∈ M, h i) + a - 45) ^ 2 / 12 ≤ 135 := by
  have hsum (f : Fin 9 → ℝ) :
      (∑ i : Fin 9, if i ∈ M then f i else 0) = ∑ i ∈ M, f i := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc1 : (∑ i, c i) = 9 := by
    simp only [hc, hsum, Finset.sum_const, nsmul_eq_mul, hM]
    norm_num
  have hc2 : (∑ i, c i ^ 2) = 27 := by
    have eq i : c i ^ 2 = if i ∈ M then (9 : ℝ) else 0 := by
      rw [hc]
      split_ifs <;> norm_num
    simp only [eq, hsum, Finset.sum_const, nsmul_eq_mul, hM]
    norm_num
  have hdot : (∑ i, h i * c i) = 3 * ∑ i ∈ M, h i := by
    have eq i : h i * c i = if i ∈ M then 3 * h i else 0 := by
      rw [hc]
      split_ifs <;> ring
    simp only [eq, hsum, Finset.mul_sum]
  rw [hc1, hc2, hdot] at he
  nlinarith only [he]

/-- In a ninety-vertex balanced cubic component, a cut crossing three times
in each of three directions can have an odd shore missing an internal
direction only up to order 31 in a noncrossing direction, or 39 in a crossing
direction. The hypotheses express the cubic and uniform directional counts. -/
theorem cut_shore_capacity_of_nine_crossings (H K : Finset (Q 9))
    (hd : Disjoint H K) (hb : IsBalanced (H ∪ K))
    (hN : H.card + K.card = 90) (hodd : Odd H.card)
    (haxis : ∀ i, (directedPairCount H H i : ℝ) + directedPairCount K K i +
      2 * directedPairCount H K i = 30)
    (hvalence : ∑ i : Fin 9, ((directedPairCount H H i : ℝ) + directedPairCount H K i) =
      3 * (H.card : ℝ))
    (M : Finset (Fin 9)) (hM : M.card = 3)
    (hcross : ∀ i, directedPairCount H K i = if i ∈ M then 3 else 0)
    (j : Fin 9) (hmiss : directedPairCount H H j = 0) :
    H.card ≤ if j ∈ M then 39 else 31 := by
  let a : ℝ := H.card
  let c (i : Fin 9) : ℝ := directedPairCount H K i
  let h (i : Fin 9) : ℝ := directedPairCount H H i + c i - a / 3
  let x : ℝ := ∑ i ∈ M, h i
  have hp : Mᶜ.card = 6 := by
    simp [Finset.card_compl, hM]
  have hc (i : Fin 9) : c i = if i ∈ M then 3 else 0 := by
    dsimp only [c]
    rw [hcross]
    split_ifs <;> norm_num
  have hnorm : (∑ i, h i ^ 2) + (x + a - 45) ^ 2 / 12 ≤ 135 := by
    have haxis' i :
        (directedPairCount H H i : ℝ) + directedPairCount K K i +
          2 * directedPairCount H K i = ((H.card + K.card : ℕ) : ℝ) / 3 := by
      rw [hN]
      norm_num
      exact haxis i
    have he := cut_count_discriminant H K hd hb haxis' hvalence
    dsimp only at he
    rw [hN] at he
    exact three_directions_reduced_energy M hM h c hc he
  have hpartition (f : Fin 9 → ℝ) :
      (∑ i ∈ M, f i) + (∑ i ∈ Mᶜ, f i) = ∑ i, f i := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have hzero : ∑ i, h i = 0 := by
    simp only [h, c, Finset.sum_sub_distrib, hvalence, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change 3 * a - 9 * (a / 3) = 0
    ring
  have hcomp : ∑ i ∈ Mᶜ, h i = -x := by
    have he := hpartition h
    change x + (∑ i ∈ Mᶜ, h i) = ∑ i, h i at he
    rw [hzero] at he
    linarith only [he]
  have hj : h j = (if j ∈ M then 3 else 0) - a / 3 := by
    dsimp only [h]
    rw [hmiss, hc]
    norm_num
  have hmass := hpartition (fun i => h i ^ 2)
  obtain ⟨k, hk⟩ := hodd
  by_cases hm : j ∈ M
  · simp only [hm, ite_true] at hj ⊢
    have hcard : (M.erase j).card = 2 := by rw [Finset.card_erase_of_mem hm, hM]
    have hsum := Finset.sum_erase_add M h hm
    have hsq := Finset.sum_erase_add M (fun i => h i ^ 2) hm
    have hleft := sum_sq_ge_sum_sq_div_card (M.erase j) h
    have hright := sum_sq_ge_sum_sq_div_card Mᶜ h
    rw [hcard] at hleft
    rw [hp, hcomp] at hright
    norm_num only [Nat.cast_ofNat, neg_sq] at hright
    have hleft' : (x - 3 + a / 3) ^ 2 ≤ 2 * ∑ i ∈ M.erase j, h i ^ 2 := by
      have eq : (∑ i ∈ M.erase j, h i) = x - 3 + a / 3 := by
        rw [hj] at hsum
        change (∑ i ∈ M.erase j, h i) + (3 - a / 3) = x at hsum
        linarith only [hsum]
      simpa only [eq, Nat.cast_ofNat] using hleft
    have hbound : (3 - a / 3) ^ 2 + (x - 3 + a / 3) ^ 2 / 2 +
        x ^ 2 / 6 + (x + a - 45) ^ 2 / 12 ≤ 135 := by
      rw [hj] at hsq
      nlinarith only [hnorm, hmass, hsq, hleft', hright]
    by_contra hn
    have ha : 41 ≤ a := by
      change (41 : ℝ) ≤ (H.card : ℝ)
      exact_mod_cast (show 41 ≤ H.card by omega)
    nlinarith only [hbound, sq_nonneg (x - (7 - a / 3)), sq_nonneg (a - 41), ha]
  · simp only [hm, ite_false, zero_sub] at hj ⊢
    have hmem : j ∈ Mᶜ := Finset.mem_compl.mpr hm
    have hcard : (Mᶜ.erase j).card = 5 := by rw [Finset.card_erase_of_mem hmem, hp]
    have hsum := Finset.sum_erase_add Mᶜ h hmem
    have hsq := Finset.sum_erase_add Mᶜ (fun i => h i ^ 2) hmem
    have hleft := sum_sq_ge_sum_sq_div_card M h
    have hright := sum_sq_ge_sum_sq_div_card (Mᶜ.erase j) h
    rw [hM] at hleft
    rw [hcard] at hright
    have hright' : (a / 3 - x) ^ 2 ≤ 5 * ∑ i ∈ Mᶜ.erase j, h i ^ 2 := by
      have eq : (∑ i ∈ Mᶜ.erase j, h i) = a / 3 - x := by
        rw [hj, hcomp] at hsum
        linarith only [hsum]
      simpa only [eq, Nat.cast_ofNat] using hright
    have hbound : (a / 3) ^ 2 + (a / 3 - x) ^ 2 / 5 +
        x ^ 2 / 3 + (x + a - 45) ^ 2 / 12 ≤ 135 := by
      rw [hj] at hsq
      change x ^ 2 ≤ (3 : ℝ) * ∑ i ∈ M, h i ^ 2 at hleft
      nlinarith only [hnorm, hmass, hsq, hleft, hright']
    by_contra hn
    have ha : 33 ≤ a := by
      change (33 : ℝ) ≤ (H.card : ℝ)
      exact_mod_cast (show 33 ≤ H.card by omega)
    nlinarith only [hbound, sq_nonneg (x - (225 - a) / 37), sq_nonneg (a - 33), ha]

#print axioms cut_shore_capacity_of_nine_crossings

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedCutEnergy

