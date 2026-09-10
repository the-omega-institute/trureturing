/- GID: D5/S3/Arith/GoldenResource/ChainBlockPencil
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/ChainBlockPencil
   mirror-E: none(waiver:general-matrix-family)
   anchors: []
   utility: none
   digest: Two endpoint-coupled chains have a length-independent positive mass bound. -/

import D5.S3.Arith.GoldenResource.TridiagonalChainInverse
import Mathlib.Algebra.Order.Star.Real

namespace D5.S3.Arith.GoldenResource.ChainBlockPencil

open Matrix TridiagonalChainInverse
open scoped BigOperators

noncomputable section

/-- Two chains of length `n + 1`, ordered first chain then second chain. -/
abbrev Hidden (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

/-- Two visible coordinates followed by the two hidden chains. -/
abbrev Total (n : ℕ) := Fin 2 ⊕ Hidden n

/-- Flattening the hidden coordinates gives precisely `2 * (n + 1)` coordinates. -/
def hiddenEquiv (n : ℕ) : Hidden n ≃ Fin (2 * (n + 1)) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The direct sum of two identical diagonal-four chains. -/
def hiddenBlock (n : ℕ) : Matrix (Hidden n) (Hidden n) ℝ :=
  fromBlocks (H (n + 1)) 0 0 (H (n + 1))

/-- Each visible coordinate couples with coefficient one to its chain's first vertex. -/
def B (n : ℕ) : Matrix (Fin 2) (Hidden n) ℝ :=
  fun i => if i = 0 then Pi.single (Sum.inl 0) 1 else Pi.single (Sum.inr 0) 1

/-- The mass matrix with identity visible block and unit endpoint couplings. -/
def K (n : ℕ) : Matrix (Total n) (Total n) ℝ :=
  fromBlocks 1 (B n) (B n)ᵀ (hiddenBlock n)

/-- Spatial coefficients; only the last vertex of the first chain is perturbed. -/
def spatialWeight (n : ℕ) (k b : ℝ) : Total n → ℝ :=
  Sum.elim (fun _ => k)
    (Sum.elim (fun i => k - if i = Fin.last n then b else 0) (fun _ => k))

/-- The spatial principal part, in the same coordinate order as the mass matrix. -/
def G (n : ℕ) (k b : ℝ) : Matrix (Total n) (Total n) ℝ :=
  diagonal (spatialWeight n k b)

private theorem coupled_chain_coercive (n : ℕ) (a : ℝ) (h : Fin (n + 1) → ℝ) :
    (1 / 3 : ℝ) * (a ^ 2 + ∑ i, h i ^ 2) ≤
      a ^ 2 + 2 * a * h 0 + h ⬝ᵥ (H (n + 1) *ᵥ h) := by
  have hc := chain_coercive n h
  have he : h 0 ^ 2 ≤ ∑ i, h i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (h i)) (Finset.mem_univ 0)
  have hs : 0 ≤ ∑ i, h i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy : -(2 / 3 : ℝ) * a ^ 2 - (3 / 2 : ℝ) * h 0 ^ 2 ≤ 2 * a * h 0 := by
    nlinarith [sq_nonneg (2 * a + 3 * h 0)]
  linarith

private theorem block_quadratic {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p p ℝ) (C : Matrix p q ℝ) (D : Matrix q q ℝ)
    (v : p → ℝ) (h : q → ℝ) :
    Sum.elim v h ⬝ᵥ (fromBlocks A C Cᵀ D *ᵥ Sum.elim v h) =
      v ⬝ᵥ (A *ᵥ v) + 2 * (v ⬝ᵥ (C *ᵥ h)) + h ⬝ᵥ (D *ᵥ h) := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim,
    dotProduct_add, dotProduct_transpose_mulVec]
  ring

private theorem coupling_mulVec (n : ℕ) (h : Hidden n → ℝ) :
    B n *ᵥ h = ![h (Sum.inl 0), h (Sum.inr 0)] := by
  ext i
  fin_cases i <;> simp [mulVec, B, single_dotProduct]

private theorem mass_energy (n : ℕ) (v : Fin 2 → ℝ)
    (h₁ h₂ : Fin (n + 1) → ℝ) :
    let x := Sum.elim v (Sum.elim h₁ h₂)
    x ⬝ᵥ (K n *ᵥ x) =
      (v 0 ^ 2 + 2 * v 0 * h₁ 0 + h₁ ⬝ᵥ (H (n + 1) *ᵥ h₁)) +
      (v 1 ^ 2 + 2 * v 1 * h₂ 0 + h₂ ⬝ᵥ (H (n + 1) *ᵥ h₂)) := by
  dsimp only
  rw [K, block_quadratic, one_mulVec, coupling_mulVec]
  have hh := block_quadratic (H (n + 1)) (0 : Matrix _ _ ℝ) (H (n + 1)) h₁ h₂
  simp only [transpose_zero, zero_mulVec, dotProduct_zero, mul_zero, add_zero] at hh
  rw [hiddenBlock, hh]
  simp only [dotProduct, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The mass lower bound one third is independent of the chain length. -/
theorem mass_coercive (n : ℕ) (x : Total n → ℝ) :
    (1 / 3 : ℝ) * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (K n *ᵥ x) := by
  let v := x ∘ Sum.inl
  let h₁ := x ∘ Sum.inr ∘ Sum.inl
  let h₂ := x ∘ Sum.inr ∘ Sum.inr
  have hx : x = Sum.elim v (Sum.elim h₁ h₂) := by
    funext i
    rcases i with i | (i | i) <;> rfl
  rw [hx, mass_energy]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two]
  have hfirst := coupled_chain_coercive n (v 0) h₁
  have hsecond := coupled_chain_coercive n (v 1) h₂
  linarith

private theorem mass_hermitian (n : ℕ) : (K n).IsHermitian := by
  apply IsHermitian.fromBlocks isHermitian_one
  · simp
  · exact IsHermitian.fromBlocks (chain_posDef (n + 1)).isHermitian
      (by simp) (chain_posDef (n + 1)).isHermitian

/-- The Loewner form of the uniform mass bound. -/
theorem mass_lower_bound (n : ℕ) : (K n - (1 / 3 : ℝ) • 1).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (mass_hermitian n).sub (isHermitian_one.smul (by simp))
  · intro x
    have hc := mass_coercive n x
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    simpa only [dotProduct, ← pow_two] using sub_nonneg.mpr hc

/-- Each mass matrix is positive definite. -/
theorem mass_posDef (n : ℕ) : (K n).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (mass_hermitian n)
  intro x hx
  have hs : 0 < ∑ i, x i ^ 2 := by
    apply Finset.sum_pos'
    · intro i _
      exact sq_nonneg _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hc := mass_coercive n x
  simpa only [star_trivial] using (show 0 < x ⬝ᵥ (K n *ᵥ x) by linarith)

private theorem spatial_weight_ge_one (n : ℕ) {k b : ℝ} (hk : 2 ≤ k) (hb : b ≤ 1)
    (i : Total n) : 1 ≤ spatialWeight n k b i := by
  rcases i with i | (i | i)
  · dsimp [spatialWeight]
    linarith
  · dsimp [spatialWeight]
    split_ifs <;> linarith
  · dsimp [spatialWeight]
    linarith

/-- The spatial lower bound one holds even for every real perturbation at most one. -/
theorem spatial_lower_bound (n : ℕ) {k b : ℝ} (hk : 2 ≤ k) (hb : b ≤ 1) :
    (G n k b - 1).PosSemidef := by
  rw [G, ← diagonal_one, diagonal_sub]
  apply PosSemidef.diagonal
  intro i
  exact sub_nonneg.mpr (spatial_weight_ge_one n hk hb i)

/-- The spatial quadratic bound is uniform in the chain length and perturbation. -/
theorem spatial_coercive (n : ℕ) {k b : ℝ} (hk : 2 ≤ k) (hb : b ≤ 1)
    (x : Total n → ℝ) : ∑ i, x i ^ 2 ≤ x ⬝ᵥ (G n k b *ᵥ x) := by
  have h := (spatial_lower_bound n hk hb).dotProduct_mulVec_nonneg x
  simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub] at h
  simpa only [dotProduct, ← pow_two] using sub_nonneg.mp h

/-- Each spatial matrix is positive definite under the uniform parameter bounds. -/
theorem spatial_posDef (n : ℕ) {k b : ℝ} (hk : 2 ≤ k) (hb : b ≤ 1) :
    (G n k b).PosDef := by
  rw [G, Matrix.posDef_diagonal_iff]
  intro i
  exact lt_of_lt_of_le (by norm_num) (spatial_weight_ge_one n hk hb i)

private theorem mass_entry (n : ℕ) (i j : Total n) :
    K n i j = -1 ∨ K n i j = 0 ∨ K n i j = 1 ∨ K n i j = 4 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals
    simp only [K, hiddenBlock, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, B, Matrix.transpose_apply,
      ite_apply, Pi.single_apply, Matrix.one_apply, chain_apply]
  all_goals (try split_ifs) <;> norm_num

/-- Integer parameters give integer entries uniformly bounded independently of length. -/
theorem coefficient_bounds (n : ℕ) {k b : ℤ} (hk : 2 ≤ k) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (i j : Total n) :
    ∃ a c : ℤ, K n i j = (a : ℝ) ∧ G n k b i j = (c : ℝ) ∧
      |a| ≤ max k 4 ∧ |c| ≤ max k 4 := by
  have hm : ∃ a : ℤ, K n i j = (a : ℝ) ∧ |a| ≤ max k 4 := by
    rcases mass_entry n i j with h | h | h | h
    · refine ⟨-1, by simpa using h, ?_⟩
      norm_num
    · exact ⟨0, by simpa using h, by norm_num⟩
    · exact ⟨1, by simpa using h, by norm_num⟩
    · exact ⟨4, by simpa using h, by norm_num⟩
  have hg : ∃ c : ℤ, G n k b i j = (c : ℝ) ∧ |c| ≤ max k 4 := by
    by_cases hij : i = j
    · subst j
      rcases i with i | (i | i)
      · exact ⟨k, by simp [G, spatialWeight], by rw [abs_le]; omega⟩
      · by_cases hi : i = Fin.last n
        · exact ⟨k - b, by simp [G, spatialWeight, hi], by rw [abs_le]; omega⟩
        · exact ⟨k, by simp [G, spatialWeight, hi], by rw [abs_le]; omega⟩
      · exact ⟨k, by simp [G, spatialWeight], by rw [abs_le]; omega⟩
    · exact ⟨0, by simp [G, Matrix.diagonal_apply_ne _ hij], by norm_num⟩
  obtain ⟨a, ha, hab⟩ := hm
  obtain ⟨c, hc, hcb⟩ := hg
  exact ⟨a, c, ha, hc, hab, hcb⟩

/-- The integer block family simultaneously has uniform mass, spatial, and entry bounds. -/
theorem uniform_pencil_bounds (n : ℕ) {k b : ℤ} (hk : 2 ≤ k)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    (K n - (1 / 3 : ℝ) • 1).PosSemidef ∧ (G n k b - 1).PosSemidef ∧
      ∀ i j : Total n, ∃ a c : ℤ, K n i j = (a : ℝ) ∧ G n k b i j = (c : ℝ) ∧
        |a| ≤ max k 4 ∧ |c| ≤ max k 4 := by
  exact ⟨mass_lower_bound n, spatial_lower_bound n (by exact_mod_cast hk)
    (by exact_mod_cast hb₁), coefficient_bounds n hk hb₀ hb₁⟩

#print axioms mass_coercive
#print axioms mass_lower_bound
#print axioms mass_posDef
#print axioms spatial_lower_bound
#print axioms spatial_coercive
#print axioms spatial_posDef
#print axioms coefficient_bounds
#print axioms uniform_pencil_bounds

end

end D5.S3.Arith.GoldenResource.ChainBlockPencil
