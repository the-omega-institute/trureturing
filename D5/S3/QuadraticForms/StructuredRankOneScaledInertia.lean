/- GID: D5/S3/QuadraticForms/StructuredRankOneScaledInertia
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/StructuredRankOneScaledInertia
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: Inertia of the scaled structured downdate A - t w wᵀ/Δ for every real t. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia

/-! The coefficient-dependent inertia of `M_t = A - t w wᵀ / Δ`, `w = A x`, `Δ = xᵀ A x ≠ 0`, for a
real symmetric `A` and every real `t`: `In(M_t) = In(A) - In([Δ]) + In([(1 - t) Δ])`.

admission_basis: escape-witness. Escape witnesses: upper_general and lower_general (block
congruences with an arbitrary corner `c` and pivot corner `d`), corner_inertia (inertia transfer
through the corner `d`), index_sum, and scaled_inertia (the sign analysis in `t`). Consumed
bind-only helpers: shifted_hermitian, index_congr. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.QuadraticForms.StructuredRankOneScaledInertia

open RHLinalg
open D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
open D5.S3.QuadraticForms.StructuredRankOneInertia

variable {ι : Type} [Fintype ι] [DecidableEq ι]


/-- The scaled structured downdate `A - t w wᵀ / Δ` with `w = A x` and `Δ = xᵀ A x`. -/
def scaledDowndate (A : Matrix ι ι ℝ) (x : ι → ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  A - (t * (pivot A x)⁻¹) • vecMulVec (A *ᵥ x) (A *ᵥ x)

private theorem upper_general (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) (c : ℝ) :
    let B := fromBlocks (1 : Matrix ι ι ℝ) (replicateCol Unit x) 0 1
    Bᴴ * fromBlocks A 0 0 (diagonal fun _ : Unit => c) * B =
      fromBlocks A (replicateCol Unit (A *ᵥ x)) (replicateRow Unit (A *ᵥ x))
        (diagonal fun _ : Unit => pivot A x + c) := by
  dsimp only
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hrow : replicateRow Unit x * A = replicateRow Unit (A *ᵥ x) := by
    rw [← replicateRow_vecMul, ← mulVec_transpose, hs]
  simp only [fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
    fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, conjTranspose_replicateCol, star_trivial,
    ← replicateCol_mulVec, hrow, replicateRow_mul_replicateCol]
  congr 1
  ext i j
  simp only [Matrix.add_apply, diagonal_apply_eq]
  change (A *ᵥ x) ⬝ᵥ x + c = pivot A x + c
  rw [dotProduct_comm]
  rfl

private theorem lower_general (A : Matrix ι ι ℝ) (x : ι → ℝ) (d : ℝ) (h : d ≠ 0) :
    let w := A *ᵥ x
    let B := fromBlocks (1 : Matrix ι ι ℝ) 0 (-d⁻¹ • replicateRow Unit w) 1
    Bᴴ * fromBlocks A (replicateCol Unit w) (replicateRow Unit w) (diagonal fun _ : Unit => d) * B =
      fromBlocks (A - d⁻¹ • vecMulVec w w) 0 0 (diagonal fun _ : Unit => d) := by
  dsimp only
  simp only [fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
    conjTranspose_smul, star_trivial, conjTranspose_replicateRow,
    fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [fromBlocks, mul_apply, Finset.mul_sum, Finset.sum_mul, vecMulVec, h, mul_assoc]
    <;> field_simp [h] <;> ring
  · simp [fromBlocks, mul_apply, h, mul_assoc]
    field_simp
    ring
  · simp [fromBlocks, mul_apply, h, mul_assoc]
    <;> field_simp <;> ring
  · simp [fromBlocks, mul_apply, h]


private theorem shifted_hermitian (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) (d : ℝ) :
    (A - d • vecMulVec (A *ᵥ x) (A *ᵥ x)).IsHermitian := by
  apply hA.sub
  rw [IsHermitian]
  ext i j
  simp [conjTranspose_apply, vecMulVec, mul_comm]

/-- Inertia transfer through the corner `d`. -/
private theorem corner_inertia (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) (d : ℝ) (h : d ≠ 0) :
    posIndex hA + (if 0 < d - pivot A x then 1 else 0) =
        posIndex (shifted_hermitian A hA x d⁻¹) + (if 0 < d then 1 else 0) ∧
    negIndex hA + (if d - pivot A x < 0 then 1 else 0) =
        negIndex (shifted_hermitian A hA x d⁻¹) + (if d < 0 then 1 else 0) := by
  let w := A *ᵥ x
  let c := d - pivot A x
  let U : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks (1 : Matrix ι ι ℝ) (replicateCol Unit x) 0 1
  let L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fromBlocks (1 : Matrix ι ι ℝ) 0 (-d⁻¹ • replicateRow Unit w) 1
  let E : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fromBlocks A (replicateCol Unit w) (replicateRow Unit w) (diagonal fun _ : Unit => d)
  have hU : IsUnit U.det := by simp [U]
  have hL : IsUnit L.det := by simp [L, det_fromBlocks_zero₁₂]
  have hE : E.IsHermitian := hA.fromBlocks (by simp [w, conjTranspose_replicateCol])
    (isHermitian_diagonal _)
  have hc : (diagonal fun _ : Unit => c).IsHermitian := isHermitian_diagonal _
  have hdd : (diagonal fun _ : Unit => d).IsHermitian := isHermitian_diagonal _
  have hbase := blockHermitian hA hc
  have hm := shifted_hermitian A hA x d⁻¹
  have hup : Uᴴ * fromBlocks A 0 0 (diagonal fun _ : Unit => c) * U = E := by
    have := upper_general A hA x c
    simp only [c, add_sub_cancel] at this
    exact this
  have heqU := congruence_counts hbase hE U hU hup
  have heqL := congruence_counts hE (blockHermitian hm hdd) L hL (lower_general A x d h)
  have hb0 := block_counts A _ hA hc
  have hbd := block_counts _ _ hm hdd
  have hd := diagonal_counts (fun _ : Unit => d)
  have hcc := diagonal_counts (fun _ : Unit => c)
  have hpd : posIndex hdd = if 0 < d then 1 else 0 := by
    split_ifs with hp <;> simpa [hp] using hd.1
  have hnd : negIndex hdd = if d < 0 then 1 else 0 := by
    split_ifs with hn <;> simpa [hn] using hd.2
  have hpc : posIndex hc = if 0 < c then 1 else 0 := by
    split_ifs with hp <;> simpa [hp] using hcc.1
  have hnc : negIndex hc = if c < 0 then 1 else 0 := by
    split_ifs with hn <;> simpa [hn] using hcc.2
  simp only [c] at hpc hnc
  constructor <;> omega


private theorem index_sum {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    zeroIndex hA + posIndex hA + negIndex hA = Fintype.card ι := by
  classical
  unfold zeroIndex posIndex negIndex
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => hA.eigenvalues i = 0)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i => ¬ hA.eigenvalues i = 0) (fun i => 0 < hA.eigenvalues i)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : (Finset.univ.filter fun i => ¬hA.eigenvalues i = 0 ∧ 0 < hA.eigenvalues i) =
      Finset.univ.filter fun i => 0 < hA.eigenvalues i :=
    Finset.filter_congr fun i _ => ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩
  have e2 : (Finset.univ.filter fun i => ¬hA.eigenvalues i = 0 ∧ ¬0 < hA.eigenvalues i) =
      Finset.univ.filter fun i => hA.eigenvalues i < 0 :=
    Finset.filter_congr fun i _ => ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) h.1,
      fun h => ⟨h.ne, not_lt.mpr h.le⟩⟩
  rw [e1, e2] at h2
  simp only [Finset.card_univ] at h1
  omega

private theorem index_congr {A B : Matrix ι ι ℝ} (hAB : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : posIndex hA = posIndex hB ∧ negIndex hA = negIndex hB := by
  subst hAB; exact ⟨rfl, rfl⟩

private theorem scaled_inertia (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ)
    (h : pivot A x ≠ 0) (t : ℝ) :
    ∃ hM : (scaledDowndate A x t).IsHermitian,
      posIndex hM + (if 0 < pivot A x then 1 else 0) =
          posIndex hA + (if 0 < (1 - t) * pivot A x then 1 else 0) ∧
      negIndex hM + (if pivot A x < 0 then 1 else 0) =
          negIndex hA + (if (1 - t) * pivot A x < 0 then 1 else 0) ∧
      zeroIndex hM = zeroIndex hA + (if t = 1 then 1 else 0) := by
  set Δ := pivot A x with hΔ
  have hM : (scaledDowndate A x t).IsHermitian := by
    simpa [scaledDowndate] using shifted_hermitian A hA x (t * Δ⁻¹)
  refine ⟨hM, ?_⟩
  suffices hpn : posIndex hM + (if 0 < Δ then 1 else 0) =
      posIndex hA + (if 0 < (1 - t) * Δ then 1 else 0) ∧
      negIndex hM + (if Δ < 0 then 1 else 0) =
      negIndex hA + (if (1 - t) * Δ < 0 then 1 else 0) by
    refine ⟨hpn.1, hpn.2, ?_⟩
    have s1 := index_sum hA
    have s2 := index_sum hM
    have key : (if 0 < (1 - t) * Δ then 1 else 0) + (if (1 - t) * Δ < 0 then 1 else 0) +
        (if t = 1 then 1 else 0) = (if 0 < Δ then 1 else 0) + (if Δ < 0 then 1 else 0) := by
      rcases lt_trichotomy Δ 0 with hd | hd | hd
      · rcases lt_trichotomy t 1 with ht | ht | ht
        · have : (1 - t) * Δ < 0 := mul_neg_of_pos_of_neg (by linarith) hd
          simp [hd, this, this.not_gt, ht.ne, not_lt.mpr hd.le]
        · subst ht; simp [hd, not_lt.mpr hd.le]
        · have : 0 < (1 - t) * Δ := mul_pos_of_neg_of_neg (by linarith) hd
          simp [hd, this, this.not_gt, ht.ne', not_lt.mpr hd.le]
      · exact absurd hd h
      · rcases lt_trichotomy t 1 with ht | ht | ht
        · have : 0 < (1 - t) * Δ := mul_pos (by linarith) hd
          simp [hd, this, this.not_gt, ht.ne, hd.not_gt]
        · subst ht; simp [hd, hd.not_gt]
        · have : (1 - t) * Δ < 0 := mul_neg_of_neg_of_pos (by linarith) hd
          simp [hd, this, this.not_gt, ht.ne', hd.not_gt]
    omega
  by_cases ht0 : t = 0
  · subst ht0
    have hA' : scaledDowndate A x 0 = A := by simp [scaledDowndate]
    have hp : posIndex hM = posIndex hA := index_congr hA' hM hA |>.1
    have hn : negIndex hM = negIndex hA := index_congr hA' hM hA |>.2
    simp only [sub_zero, one_mul, hp, hn, and_self]
  have hd : Δ / t ≠ 0 := div_ne_zero h ht0
  have hc := corner_inertia A hA x (Δ / t) hd
  have he : (Δ / t)⁻¹ = t * Δ⁻¹ := by rw [inv_div]; field_simp
  have hp : posIndex (shifted_hermitian A hA x (Δ / t)⁻¹) = posIndex hM := by
    simp only [he]; rfl
  have hn : negIndex (shifted_hermitian A hA x (Δ / t)⁻¹) = negIndex hM := by
    simp only [he]; rfl
  rw [hp, hn] at hc
  have hdiff : Δ / t - Δ = (1 - t) * Δ / t := by field_simp
  rw [← hΔ, hdiff] at hc
  -- sign bookkeeping
  have key : ∀ u : ℝ, (0 < u / t ↔ (0 < u ∧ 0 < t) ∨ (u < 0 ∧ t < 0)) ∧
      (u / t < 0 ↔ (0 < u ∧ t < 0) ∨ (u < 0 ∧ 0 < t)) := fun u =>
    ⟨div_pos_iff, div_neg_iff⟩
  simp only [(key _).1, (key _).2] at hc
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · have h1 : 0 < 1 - t := by linarith
    have e1 : (0 < (1 - t) * Δ ↔ 0 < Δ) := ⟨fun hh => pos_of_mul_pos_right hh h1.le,
      fun hh => mul_pos h1 hh⟩
    have e2 : ((1 - t) * Δ < 0 ↔ Δ < 0) := ⟨fun hh => neg_of_mul_neg_right hh h1.le,
      fun hh => mul_neg_of_pos_of_neg h1 hh⟩
    simp only [e1, e2, ht, ht.not_gt, and_true, and_false, or_false, false_or] at hc ⊢
    constructor <;> split_ifs at hc ⊢ <;> omega
  · simp only [ht, ht.not_gt, and_true, and_false, or_false, false_or] at hc ⊢
    exact ⟨by omega, by omega⟩


/-- Corollary 4 of Ma and Zhang on MathOverflow 513954: for a real symmetric `A`, a vector `x` with
`Δ = xᵀ A x ≠ 0`, `w = A x` and every real `t`, the matrix `M_t = A - t w wᵀ / Δ` is symmetric and
`In(M_t) = In(A) - In([Δ]) + In([(1 - t) Δ])` componentwise (stated additively); hence `t < 1`
preserves the inertia, `t = 1` is the structured downdate, and `t > 1` moves one eigenvalue from the
sign of `Δ` to the opposite sign without changing the nullity. -/
theorem result (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) (h : pivot A x ≠ 0) (t : ℝ) :
    ∃ hM : (scaledDowndate A x t).IsHermitian,
      (posIndex hM + (if 0 < pivot A x then 1 else 0) =
          posIndex hA + (if 0 < (1 - t) * pivot A x then 1 else 0) ∧
        negIndex hM + (if pivot A x < 0 then 1 else 0) =
          negIndex hA + (if (1 - t) * pivot A x < 0 then 1 else 0) ∧
        zeroIndex hM = zeroIndex hA + (if t = 1 then 1 else 0)) ∧
      (t < 1 → posIndex hM = posIndex hA ∧ negIndex hM = negIndex hA ∧
        zeroIndex hM = zeroIndex hA) ∧
      (1 < t → zeroIndex hM = zeroIndex hA ∧
        (0 < pivot A x → posIndex hM + 1 = posIndex hA ∧ negIndex hM = negIndex hA + 1) ∧
        (pivot A x < 0 → posIndex hM = posIndex hA + 1 ∧ negIndex hM + 1 = negIndex hA)) ∧
      scaledDowndate A x 1 = downdate A x := by
  obtain ⟨hM, hp, hn, hz⟩ := scaled_inertia A hA x h t
  refine ⟨hM, ⟨hp, hn, hz⟩, fun ht => ?_, fun ht => ?_, by simp [scaledDowndate, downdate]⟩
  · have h1 : 0 < 1 - t := by linarith
    have e1 : (0 < (1 - t) * pivot A x ↔ 0 < pivot A x) :=
      ⟨fun hh => pos_of_mul_pos_right hh h1.le, fun hh => mul_pos h1 hh⟩
    have e2 : ((1 - t) * pivot A x < 0 ↔ pivot A x < 0) :=
      ⟨fun hh => neg_of_mul_neg_right hh h1.le, fun hh => mul_neg_of_pos_of_neg h1 hh⟩
    simp only [e1, e2, ht.ne, if_false, add_zero] at hp hn hz
    exact ⟨by omega, by omega, hz⟩
  · have h1 : 1 - t < 0 := by linarith
    simp only [ht.ne', if_false, add_zero] at hz
    refine ⟨hz, fun hd => ?_, fun hd => ?_⟩
    · have a : ¬ (0 < (1 - t) * pivot A x) := (mul_neg_of_neg_of_pos h1 hd).not_gt
      have b : (1 - t) * pivot A x < 0 := mul_neg_of_neg_of_pos h1 hd
      simp only [hd, hd.not_gt, a, b, if_true, if_false] at hp hn
      exact ⟨by omega, by omega⟩
    · have a : 0 < (1 - t) * pivot A x := mul_pos_of_neg_of_neg h1 hd
      simp only [hd, hd.not_gt, a, a.not_gt, if_true, if_false] at hp hn
      exact ⟨by omega, by omega⟩

end D5.S3.QuadraticForms.StructuredRankOneScaledInertia
