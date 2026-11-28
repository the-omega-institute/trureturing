import OmegaMath.Matrix.HomogeneousWordPowersRankOne

/-! Omega original.

First and second return estimates and the size-three upper bound with an invertible generator. -/

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

/-- Any eventually full size-three example with an invertible generator whose
seventh power is proper has a square-zero outer-product generator and exactly
one nonzero return among the first two. -/
theorem single_rank_one_return_of_pow_seven_ne_top
    (L : Submodule K Mat) (A : Matˣ) (hA : (A : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hseven : L ^ 7 ≠ ⊤) :
    ∃ u v : Fin 3 → K,
      L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat) ∧
      (Matrix.vecMulVec u v).rank = 1 ∧ v ⬝ᵥ u = 0 ∧
      (((v ⬝ᵥ ((A : Mat) *ᵥ u)) ≠ 0 ∧ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) = 0) ∨
       ((v ⬝ᵥ ((A : Mat) *ᵥ u)) = 0 ∧ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) ≠ 0)) := by
  classical
  obtain ⟨hL, hL2⟩ := finrank_eq_two_and_three_of_pow_seven_ne_top L A hA hfull hseven
  obtain ⟨B, hspan, hzero, hrank⟩ :=
    exists_rank_one_square_zero_of_finrank_two_and_three L A hA hfull hL hL2
  obtain ⟨u, v, rfl, h0, hreturn, hpair⟩ := rank_one_returns L hrank hzero hspan hfull
  refine ⟨u, v, hspan, hrank, h0, ?_⟩
  rcases hreturn with h1 | h2
  · exact Or.inl ⟨h1, by_contra fun h2 => hseven (hpair h1 h2)⟩
  · exact Or.inr ⟨by_contra fun h1 => hseven (hpair h1 h2), h2⟩

private theorem isUnit_of_span_columns (P : Mat)
    (h : Submodule.span K (Set.range P.col) = ⊤) : IsUnit P :=
  Matrix.mulVec_surjective_iff_isUnit.1
    (LinearMap.range_eq_top.1 ((Matrix.range_mulVecLin P).trans h))

private theorem periodic_outer_five_linearIndependent (x y z : K)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    LinearIndependent K ![
      (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
      x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 0) +
        y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 0) +
        z • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
      x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 2) +
        y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 1) +
        z • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
      (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 1),
      (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 2)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun₂ hg 0 0
  have h20 := congrFun₂ hg 2 0
  have h10 := congrFun₂ hg 1 0
  have h02 := congrFun₂ hg 0 2
  have h01 := congrFun₂ hg 0 1
  have h21 := congrFun₂ hg 2 1
  have h12 := congrFun₂ hg 1 2
  simp [Fin.sum_univ_succ, Matrix.stdBasis, Pi.single_apply] at h00 h20 h10 h02 h01 h21 h12
  have g1 : g 1 = 0 := by
    rcases hxy with hx | hy
    · exact h20.resolve_right hx
    · exact h10.resolve_right hy
  have g2 : g 2 = 0 := by
    rcases hxy with hx | hy
    · exact h02.resolve_right hx
    · exact h01.resolve_right hy
  have g0 : g 0 = 0 := by simpa [g1, g2] using h00
  have g3 : g 3 = 0 := by simpa using h21
  have g4 : g 4 = 0 := by simpa using h12
  intro i
  fin_cases i <;> assumption

/-- A nonzero first return and zero second return force at least five independent
matrices in the exact cube of an eventually full span with an invertible generator. -/
theorem five_le_finrank_cube_of_first_return
    (L : Submodule K Mat) (A : Matˣ) (u v : Fin 3 → K)
    (hL : L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (h0 : v ⬝ᵥ u = 0) (h1 : v ⬝ᵥ ((A : Mat) *ᵥ u) ≠ 0)
    (h2 : v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u) = 0) :
    5 ≤ Module.finrank K ↥(L ^ 3) := by
  classical
  let P : Mat := A
  let B := Matrix.vecMulVec u v
  let w (i : Fin 3) := P ^ (i : ℕ) *ᵥ u
  let r (j : Fin 3) := v ᵥ* P ^ (j : ℕ)
  have hu : u ≠ 0 := by rintro rfl; simp at h1
  have hv : v ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨U, hU⟩ := isUnit_of_span_columns (Matrix.of fun i j => w j i)
    (span_column_orbit L hu hL hfull)
  have hVunit : IsUnit (Matrix.of r : Mat) :=
    (Matrix.isUnit_transpose (Matrix.of r : Mat)).1 (isUnit_of_span_columns (Matrix.of r)ᵀ
      (span_row_orbit L hv hL hfull))
  obtain ⟨V, hV⟩ := hVunit
  have hcol (i : Fin 3) : (U : Mat).col i = w i := by rw [hU]; rfl
  have hrow (j : Fin 3) : (V : Mat).row j = r j := by rw [hV]; rfl
  let e := (U.mulLeftLinearEquiv K Mat).trans (V.mulRightLinearEquiv K)
  let b := (Matrix.stdBasis K (Fin 3) (Fin 3)).map e
  have hb (i j : Fin 3) : b (i, j) = Matrix.vecMulVec (w i) (r j) := by
    change e (Matrix.stdBasis K _ _ (i, j)) = _
    rw [Matrix.stdBasis_eq_single, Matrix.single_eq_single_vecMulVec_single]
    change (U : Mat) * Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) * (V : Mat) = _
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_single_one,
      Matrix.single_one_vecMul, hcol, hrow]
  have hP : P ∈ L := hL.symm ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hB : B ∈ L := hL.symm ▸ Submodule.subset_span (by simp [B])
  have hmul {m n : ℕ} {X Y : Mat} (hX : X ∈ L ^ m) (hY : Y ∈ L ^ n) :
      X * Y ∈ L ^ (m + n) := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hX hY
  have hB1 : B ∈ L ^ 1 := by simpa using hB
  have hB3 : B ∈ L ^ 3 := by
    let c : K := v ⬝ᵥ (P *ᵥ u)
    have hc : c ≠ 0 := h1
    have hw := hmul (hmul hB1 (Submodule.pow_mem_pow L hP 1)) hB1
    rw [return_product P u v 1, pow_one] at hw
    change c • B ∈ L ^ 3 at hw
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using (L ^ 3).smul_mem c⁻¹ hw
  have hword (i j : Fin 3) (hlen : (i : ℕ) + 1 + (j : ℕ) = 3) : b (i, j) ∈ L ^ 3 := by
    rw [hb, ← Matrix.vecMulVec_mul, ← Matrix.mul_vecMulVec]
    have hw := hmul (hmul (Submodule.pow_mem_pow L hP (i : ℕ)) hB1)
      (Submodule.pow_mem_pow L hP (j : ℕ))
    rwa [hlen] at hw
  -- Three cubic words and the padded generator occupy four distinct basis positions.
  let p : Fin 4 → Fin 3 × Fin 3 := ![(2, 0), (1, 1), (0, 2), (0, 0)]
  have hp : Function.Injective p := by
    change ∀ i j : Fin 4, p i = p j → i = j
    decide
  let W := Submodule.span K (Set.range (b ∘ p))
  have hdimW : Module.finrank K W = 4 := by
    simpa [W] using finrank_span_eq_card (b.linearIndependent.comp p hp)
  have hWL : W ≤ L ^ 3 := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hword 2 0 rfl
    · exact hword 1 1 rfl
    · exact hword 0 2 rfl
    · change b (0, 0) ∈ L ^ 3
      simpa [hb, w, r, B] using hB3
  let coord : (Fin 3 → K) →ₗ[K] K :=
    (LinearMap.proj 2).comp (↑U⁻¹ : Mat).mulVecLin
  have hcoord (i : Fin 3) : coord (w i) = (Pi.single i 1 : Fin 3 → K) 2 := by
    change ((↑U⁻¹ : Mat) *ᵥ w i) 2 = _
    rw [← hcol, ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let eval (k : Fin 3) : Mat →ₗ[K] K := coord.comp ((Matrix.mulVecBilin K K).flip (w k))
  have heval (i j k : Fin 3) :
      eval k (b (i, j)) = (r j ⬝ᵥ w k) * (Pi.single i 1 : Fin 3 → K) 2 := by
    change coord (b (i, j) *ᵥ w k) = _
    rw [hb, Matrix.vecMulVec_mulVec, op_smul_eq_smul, map_smul, hcoord, smul_eq_mul]
  have hker (k : Fin 3) (hk : v ⬝ᵥ w k = 0) : W ≤ (eval k).ker := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    change eval k (b (p i)) = 0
    fin_cases i
    · change eval k (b (2, 0)) = 0
      rw [heval]
      simpa [r] using hk
    · change eval k (b (1, 1)) = 0
      simp [heval]
    · change eval k (b (0, 2)) = 0
      simp [heval]
    · change eval k (b (0, 0)) = 0
      simp [heval]
  -- In the last column-orbit coordinate, only the outer product at (2, 0) contributes.
  -- Its row is v, which annihilates both u and A^2 u.
  have hnot : P ^ 3 ∉ W := by
    intro hW
    obtain ⟨x, y, hrel⟩ := third_power_eq P
    have htest0 : coord (P ^ 3 *ᵥ u) = 0 := by
      have ht := hker 0 (by simpa [w] using h0) hW
      change coord (P ^ 3 *ᵥ w 0) = 0 at ht
      simpa [w] using ht
    have hx : x = 0 := by
      have ht := htest0
      rw [hrel, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, map_add, map_add, map_smul, map_smul, map_smul] at ht
      have ht' : x • coord (w 2) + y • coord (w 1) + P.det • coord (w 0) = 0 := by
        simpa [w] using ht
      simpa [hcoord] using ht'
    have htest2 := hker 2 h2 hW
    change coord (P ^ 3 *ᵥ (P ^ 2 *ᵥ u)) = 0 at htest2
    rw [Matrix.mulVec_mulVec, ← pow_add] at htest2
    have h5 : P ^ 5 = y • P ^ 3 + P.det • P ^ 2 := by
      calc
        P ^ 5 = P ^ 3 * P ^ 2 := pow_add P 3 2
        _ = (y • P + P.det • (1 : Mat)) * P ^ 2 := by
          exact congrArg (· * P ^ 2) (by simpa [hx] using hrel)
        _ = y • P ^ 3 + P.det • P ^ 2 := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_succ']
    rw [h5, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      map_add, map_smul, map_smul] at htest2
    change y • coord (P ^ 3 *ᵥ u) + P.det • coord (w 2) = 0 at htest2
    have hd : P.det = 0 := by simpa [htest0, hcoord] using htest2
    exact (isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det P).1 A.isUnit)) hd
  let W' := W ⊔ Submodule.span K ({P ^ 3} : Set Mat)
  have hP3 : P ^ 3 ∈ W' := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have hlt : W < W' := lt_of_le_not_ge le_sup_left
    (fun h => hnot (h hP3))
  have hW'L : W' ≤ L ^ 3 := sup_le hWL
    ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.pow_mem_pow L hP 3))
  have hdim := (Submodule.finrank_lt_finrank_of_lt hlt).trans_le (Submodule.finrank_mono hW'L)
  omega

/-- A zero first return and nonzero second return give six independent
matrices in the exact fourth power, provided the characteristic-polynomial
coefficients do not both vanish. -/
theorem six_le_finrank_four_of_second_return
    (L : Submodule K Mat) (A : Matˣ) (u v : Fin 3 → K)
    (hL : L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (h0 : v ⬝ᵥ u = 0) (h1 : v ⬝ᵥ ((A : Mat) *ᵥ u) = 0)
    (h2 : v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u) ≠ 0)
    {x y : K} (hrel : (A : Mat) ^ 3 = x • (A : Mat) ^ 2 + y • (A : Mat) +
      (A : Mat).det • (1 : Mat)) (hxy : x ≠ 0 ∨ y ≠ 0) :
    6 ≤ Module.finrank K ↥(L ^ 4) := by
  classical
  let P : Mat := A
  let B := Matrix.vecMulVec u v
  let w (i : Fin 3) := P ^ (i : ℕ) *ᵥ u
  let r (j : Fin 3) := v ᵥ* P ^ (j : ℕ)
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h2
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨U, hU⟩ := isUnit_of_span_columns (Matrix.of fun i j => w j i)
    (span_column_orbit L hu hL hfull)
  have hVunit : IsUnit (Matrix.of r : Mat) :=
    (Matrix.isUnit_transpose (Matrix.of r : Mat)).1 (isUnit_of_span_columns (Matrix.of r)ᵀ
      (span_row_orbit L hv hL hfull))
  obtain ⟨V, hV⟩ := hVunit
  have hcol (i : Fin 3) : (U : Mat).col i = w i := by rw [hU]; rfl
  have hrow (j : Fin 3) : (V : Mat).row j = r j := by rw [hV]; rfl
  let e := (U.mulLeftLinearEquiv K Mat).trans (V.mulRightLinearEquiv K)
  let b := (Matrix.stdBasis K (Fin 3) (Fin 3)).map e
  have hb (i j : Fin 3) : b (i, j) = Matrix.vecMulVec (w i) (r j) := by
    change e (Matrix.stdBasis K _ _ (i, j)) = _
    rw [Matrix.stdBasis_eq_single, Matrix.single_eq_single_vecMulVec_single]
    change (U : Mat) * Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) * (V : Mat) = _
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_single_one,
      Matrix.single_one_vecMul, hcol, hrow]
  have hbcoord (i j a c : Fin 3) :
      (e.symm (b (a, c))) i j = if i = a ∧ j = c then 1 else 0 := by
    dsimp [b]
    by_cases hia : i = a <;> by_cases hjc : j = c <;>
      simp [Matrix.stdBasis, Pi.single_apply, hia, hjc]
  have hP : P ∈ L := hL.symm ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hP1 : P ∈ L ^ 1 := by simpa using hP
  have hB : B ∈ L := hL.symm ▸ Submodule.subset_span (by simp [B])
  have hmul {m n : ℕ} {X Y : Mat} (hX : X ∈ L ^ m) (hY : Y ∈ L ^ n) :
      X * Y ∈ L ^ (m + n) := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hX hY
  have hB1 : B ∈ L ^ 1 := by simpa using hB
  have hB4 : B ∈ L ^ 4 := by
    let c : K := v ⬝ᵥ (P ^ 2 *ᵥ u)
    have hc : c ≠ 0 := h2
    have hw := hmul (hmul hB1 (Submodule.pow_mem_pow L hP 2)) hB1
    rw [return_product P u v 2] at hw
    change c • B ∈ L ^ 4 at hw
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using (L ^ 4).smul_mem c⁻¹ hw
  have hqmem (i : Fin 5) :
      (![B, P ^ 3 * B, B * P ^ 3, P ^ 2 * B * P, P * B * P ^ 2] i) ∈ L ^ 4 := by
    fin_cases i
    · exact hB4
    · change P ^ 3 * B ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul (Submodule.pow_mem_pow L hP 3) hB1)
    · change B * P ^ 3 ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul hB1 (Submodule.pow_mem_pow L hP 3))
    · change P ^ 2 * B * P ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul (hmul (Submodule.pow_mem_pow L hP 2) hB1) hP1)
    · change P * B * P ^ 2 ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul (hmul hP1 hB1) (Submodule.pow_mem_pow L hP 2))
  let q : Fin 5 → Mat := ![B, P ^ 3 * B, B * P ^ 3, P ^ 2 * B * P, P * B * P ^ 2]
  have he00 : e.symm B = (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0) := by
    have h : B = b (0, 0) := by simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 0 <;> by_cases hjc : c = 0 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he20 : e.symm (P ^ 2 * B) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 0) := by
    have h : P ^ 2 * B = b (2, 0) := by
      change P ^ 2 * Matrix.vecMulVec u v = b (2, 0)
      rw [Matrix.mul_vecMulVec]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 2 <;> by_cases hjc : c = 0 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he10 : e.symm (P * B) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 0) := by
    have h : P * B = b (1, 0) := by
      change P * Matrix.vecMulVec u v = b (1, 0)
      rw [Matrix.mul_vecMulVec]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 1 <;> by_cases hjc : c = 0 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he02 : e.symm (B * P ^ 2) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 2) := by
    have h : B * P ^ 2 = b (0, 2) := by
      change Matrix.vecMulVec u v * P ^ 2 = b (0, 2)
      rw [Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 0 <;> by_cases hjc : c = 2 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he01 : e.symm (B * P) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 1) := by
    have h : B * P = b (0, 1) := by
      change Matrix.vecMulVec u v * P = b (0, 1)
      rw [Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 0 <;> by_cases hjc : c = 1 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he21 : e.symm (P ^ 2 * B * P) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 1) := by
    have h : P ^ 2 * B * P = b (2, 1) := by
      change P ^ 2 * Matrix.vecMulVec u v * P = b (2, 1)
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 2 <;> by_cases hjc : c = 1 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he12 : e.symm (P * B * P ^ 2) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 2) := by
    have h : P * B * P ^ 2 = b (1, 2) := by
      change P * Matrix.vecMulVec u v * P ^ 2 = b (1, 2)
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 1 <;> by_cases hjc : c = 2 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have hqrepr :
      (fun i => e.symm (q i)) = ![
        (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
        x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 0) +
          y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 0) +
          P.det • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
        x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 2) +
          y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 1) +
          P.det • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
        (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 1),
        (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 2)] := by
    funext i
    fin_cases i
    · ext a c
      change (e.symm B) a c = _
      rw [he00]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (P ^ 3 * B)) a c = _
      have hrelP : P ^ 3 = x • P ^ 2 + y • P + P.det • (1 : Mat) := by
        simpa [P] using hrel
      have h : P ^ 3 * B = x • (P ^ 2 * B) + y • (P * B) + P.det • B := by
        rw [hrelP]
        simp only [add_mul, smul_mul_assoc, one_mul]
      rw [h]
      simp only [map_add, map_smul, he20, he10, he00]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (B * P ^ 3)) a c = _
      have hrelP : P ^ 3 = x • P ^ 2 + y • P + P.det • (1 : Mat) := by
        simpa [P] using hrel
      have h : B * P ^ 3 = x • (B * P ^ 2) + y • (B * P) + P.det • B := by
        rw [hrelP]
        simp only [mul_add, mul_smul_comm, mul_one]
      rw [h]
      simp only [map_add, map_smul, he02, he01, he00]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (P ^ 2 * B * P)) a c = _
      rw [he21]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (P * B * P ^ 2)) a c = _
      rw [he12]
      simp [Matrix.stdBasis]
  have hq : LinearIndependent K q := by
    have hq' := periodic_outer_five_linearIndependent x y P.det hxy
    rw [← hqrepr] at hq'
    have hm := hq'.map' e.toLinearMap (by simp)
    simpa [Function.comp_def] using hm
  let W := Submodule.span K (Set.range q)
  have hdimW : Module.finrank K W = 5 := by
    simpa [W] using finrank_span_eq_card hq
  have hWL : W ≤ L ^ 4 := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact hqmem i
  have hrelP : P ^ 3 = x • P ^ 2 + y • P + P.det • (1 : Mat) := hrel
  let d := x ^ 2 + y
  let f := x * y + P.det
  have hfour : P ^ 4 = d • P ^ 2 + f • P + (x * P.det) • (1 : Mat) := by
    calc
      P ^ 4 = P ^ 3 * P := by rw [← pow_succ]
      _ = (x • P ^ 2 + y • P + P.det • (1 : Mat)) * P := by
        exact congrArg (· * P) hrelP
      _ = x • P ^ 3 + y • P ^ 2 + P.det • P := by
        simp only [add_mul, smul_mul_assoc, one_mul]
        rw [← pow_succ P 2, ← pow_two P]
      _ = _ := by
        rw [hrelP]
        simp only [smul_add, smul_smul, d, f, pow_two, add_smul]
        abel
  have hcoord (i : Fin 3) : (↑U⁻¹ : Mat) *ᵥ w i = Pi.single i 1 := by
    rw [← hcol, ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hcoord_mul (X : Mat) (a : Fin 3 → K) :
      (↑U⁻¹ : Mat) *ᵥ (X *ᵥ a) = e.symm X *ᵥ ((V : Mat) *ᵥ a) := by
    have he : (U : Mat) * e.symm X * (V : Mat) = X := e.apply_symm_apply X
    conv_lhs => rw [← he]
    simp only [Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul]
  let t := v ⬝ᵥ w 2
  have hVentry (i j : Fin 3) : ((V : Mat) *ᵥ w j) i =
      v ⬝ᵥ (P ^ ((i : ℕ) + (j : ℕ)) *ᵥ u) := by
    change (V : Mat).row i ⬝ᵥ w j = _
    rw [hrow]
    simp only [r, w, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← pow_add]
  have h1P : v ⬝ᵥ (P *ᵥ u) = 0 := h1
  have h3P : v ⬝ᵥ (P ^ 3 *ᵥ u) = x * t := by
    rw [hrelP]
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, h0, h1P, t, w]
  have hV0 : (V : Mat) *ᵥ w 0 = Pi.single 2 t := by
    funext i
    fin_cases i
    · simpa [Pi.single_apply] using hVentry 0 0 |>.trans (by simpa using h0)
    · simpa [Pi.single_apply] using hVentry 1 0 |>.trans (by simpa using h1P)
    · exact (hVentry 2 0).trans (by simp [Pi.single_apply, t, w])
  have hV1 : (V : Mat) *ᵥ w 1 - x • ((V : Mat) *ᵥ w 0) = Pi.single 1 t := by
    funext i
    change ((V : Mat) *ᵥ w 1) i - x * (((V : Mat) *ᵥ w 0) i) = _
    rw [hVentry, hV0]
    fin_cases i
    · change v ⬝ᵥ (P ^ 1 *ᵥ u) - x * (Pi.single 2 t : Fin 3 → K) 0 = _
      simp [h1P, Pi.single_apply]
    · change t - x * (Pi.single 2 t : Fin 3 → K) 1 = _
      simp [Pi.single_apply]
    · change (v ⬝ᵥ (P ^ 3 *ᵥ u)) - x * (Pi.single 2 t : Fin 3 → K) 2 = _
      simp [h3P, Pi.single_apply]
  have hw01 : P *ᵥ w 0 = w 1 := by simp [w]
  have hw02 : P ^ 2 *ᵥ w 0 = w 2 := by simp [w]
  have hw12 : P *ᵥ w 1 = w 2 := by simp [w, pow_two, Matrix.mulVec_mulVec]
  have hnot : P ^ 4 ∉ W := by
    intro hmem
    have hdiag (i : Fin 3) (hi : i ≠ 0) {X : Mat} (hX : X ∈ W) : e.symm X i i = 0 := by
      induction hX using Submodule.span_induction with
      | mem X hX =>
          obtain ⟨j, rfl⟩ := hX
          have h := congrFun₂ (congrFun hqrepr j) i i
          rw [h]
          fin_cases j <;> fin_cases i <;>
            simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply] at hi ⊢
      | zero => simp
      | add X Y _ _ hX hY => simp [hX, hY]
      | smul a X _ hX => simp [hX]
    have hd0 := congrFun (hcoord_mul (P ^ 4) (w 0)) 2
    simp only [hV0, Matrix.mulVec_single, op_smul_eq_smul, Pi.smul_apply, smul_eq_mul,
      Matrix.col_apply, hdiag 2 (by decide) hmem, mul_zero] at hd0
    have hd : d = 0 := by
      simp only [hfour, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        hw02, hw01, Matrix.mulVec_add, Matrix.mulVec_smul, hcoord] at hd0
      simpa [Pi.single_apply] using hd0
    have htest : ((↑U⁻¹ : Mat) *ᵥ (P ^ 4 *ᵥ w 1) -
        x • ((↑U⁻¹ : Mat) *ᵥ (P ^ 4 *ᵥ w 0))) 1 = 0 := by
      rw [hcoord_mul, hcoord_mul, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub, hV1,
        Matrix.mulVec_single]
      simp only [op_smul_eq_smul, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
        hdiag 1 (by decide) hmem, mul_zero]
    have hcoeff : x * P.det - x * f = 0 := by
      simp only [hfour, hd, zero_smul, zero_add, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hw12, hw01, Matrix.mulVec_add, Matrix.mulVec_smul, hcoord] at htest
      simpa [Pi.single_apply] using htest
    have hd' : x ^ 2 + y = 0 := hd
    have hy : y = 0 := by
      dsimp [f] at hcoeff
      have : y ^ 2 = 0 := by linear_combination y * hd' + hcoeff
      by_contra hy
      exact (pow_ne_zero 2 hy) this
    have hx : x = 0 := by
      rw [hy, add_zero] at hd'
      by_contra hx
      exact (pow_ne_zero 2 hx) hd'
    exact hxy.elim (· hx) (· hy)
  have hlt : W < L ^ 4 := lt_of_le_not_ge hWL
    (fun h => hnot (h (Submodule.pow_mem_pow L hP 4)))
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- In the invertible-generator case, a proper seventh power requires the
second return to be the unique nonzero return of order one or two. -/
theorem second_rank_one_return_of_pow_seven_ne_top
    (L : Submodule K Mat) (A : Matˣ) (hA : (A : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hseven : L ^ 7 ≠ ⊤) :
    ∃ u v : Fin 3 → K,
      L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat) ∧
      (Matrix.vecMulVec u v).rank = 1 ∧ v ⬝ᵥ u = 0 ∧
      (v ⬝ᵥ ((A : Mat) *ᵥ u)) = 0 ∧ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) ≠ 0 := by
  obtain ⟨u, v, hL, hrank, h0, hreturns⟩ :=
    single_rank_one_return_of_pow_seven_ne_top L A hA hfull hseven
  refine ⟨u, v, hL, hrank, h0, hreturns.resolve_left ?_⟩
  rintro ⟨h1, h2⟩
  have hdim := five_le_finrank_cube_of_first_return L A u v hL hfull h0 h1 h2
  exact hseven (pow_eq_top_of_finrank_add_le L A hA hfull (j := 3) (t := 4) (by decide)
    (by rw [finrank_matrix_three]; omega))

/-- When the cube of the invertible generator is scalar and the first two
pairings vanish, each exact power sends the starting vector into a single
line of its cyclic orbit. In particular every exact power is proper. -/
theorem pow_ne_top_of_periodic_second_return
    (L : Submodule K Mat) (A : Matˣ) (u v : Fin 3 → K)
    (hL : L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat))
    (h0 : v ⬝ᵥ u = 0) (h1 : v ⬝ᵥ ((A : Mat) *ᵥ u) = 0)
    (h2 : v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u) ≠ 0)
    (hcube : (A : Mat) ^ 3 = (A : Mat).det • (1 : Mat)) (n : ℕ) :
    L ^ n ≠ ⊤ := by
  classical
  let P : Mat := A
  let B := Matrix.vecMulVec u v
  let w (k : ℕ) := P ^ k *ᵥ u
  let W (k : ℕ) := Submodule.span K ({w k} : Set (Fin 3 → K))
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h2
  have hz : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P).mp A.isUnit |>.ne_zero
  have hw0 : w 0 = u := by simp [w]
  have hperiod (k : ℕ) : w (k + 3) = P.det • w k := by
    have hP : P ^ 3 = P.det • (1 : Mat) := hcube
    simp only [w, Nat.add_comm k 3, pow_add, hP, smul_mul_assoc, one_mul, Matrix.smul_mulVec]
  have hadvance : ∀ k : ℕ, ∃ c : K, B *ᵥ w k = c • w (k + 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hk : k < 3
        · interval_cases k
          · exact ⟨0, by simp [B, hw0, Matrix.vecMulVec_mulVec, h0]⟩
          · refine ⟨0, ?_⟩
            change Matrix.vecMulVec u v *ᵥ (P ^ 1 *ᵥ u) = _
            rw [Matrix.vecMulVec_mulVec, pow_one, h1]
            simp
          · refine ⟨(v ⬝ᵥ w 2) / P.det, ?_⟩
            rw [show 2 + 1 = 0 + 3 by decide, hperiod, hw0, smul_smul, div_mul_cancel₀ _ hz]
            change Matrix.vecMulVec u v *ᵥ w 2 = _
            rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
        · obtain ⟨c, hc⟩ := ih (k - 3) (by omega)
          refine ⟨c, ?_⟩
          rw [show k = (k - 3) + 3 by omega, hperiod, Matrix.mulVec_smul, hc,
            show k - 3 + 3 + 1 = (k - 3 + 1) + 3 by omega, hperiod,
            smul_comm P.det c]
  have hstep (k : ℕ) {X : Mat} (hX : X ∈ L) {x : Fin 3 → K} (hx : x ∈ W k) :
      X *ᵥ x ∈ W (k + 1) := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Matrix.mulVec_smul]
    apply (W (k + 1)).smul_mem
    rw [hL] at hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        rcases Set.mem_insert_iff.1 hX with rfl | hX
        · have hP : P *ᵥ w k = w (k + 1) := by
            simp only [w, pow_succ', Matrix.mulVec_mulVec]
          exact hP ▸ Submodule.mem_span_singleton_self _
        · obtain rfl := Set.mem_singleton_iff.1 hX
          obtain ⟨c, hc⟩ := hadvance k
          exact Submodule.mem_span_singleton.2 ⟨c, hc.symm⟩
    | zero => simp
    | add X Y _ _ hX hY => simpa only [Matrix.add_mulVec] using (W (k + 1)).add_mem hX hY
    | smul c X _ hX => simpa only [Matrix.smul_mulVec] using (W (k + 1)).smul_mem c hX
  have hwords (k : ℕ) : ∀ X ∈ L ^ k, X *ᵥ u ∈ W k := by
    induction k with
    | zero =>
        rw [pow_zero, Submodule.one_eq_span]
        intro X hX
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hX
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, ← hw0]
        exact (W 0).smul_mem c (Submodule.mem_span_singleton_self _)
    | succ k ih =>
        rw [pow_succ']
        intro X hX
        refine Submodule.mul_induction_on hX ?_ ?_
        · intro Y hY Z hZ
          rw [← Matrix.mulVec_mulVec]
          exact hstep k hY (ih Z hZ)
        · intro Y Z hY hZ
          simpa only [Matrix.add_mulVec] using (W (k + 1)).add_mem hY hZ
  intro htop
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  have hW : W n = ⊤ := by
    apply top_unique
    intro x _
    let X := Matrix.vecMulVec x (Pi.single i (u i)⁻¹)
    have hX : X ∈ L ^ n := htop.symm ▸ Submodule.mem_top
    have hx := hwords n X hX
    simpa [X, Matrix.vecMulVec_mulVec, single_dotProduct, inv_mul_cancel₀ hi] using hx
  have hdim : Module.finrank K (W n) ≤ 1 :=
    finrank_span_le_card ({w n} : Set (Fin 3 → K))
  rw [hW, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  omega

/-- An eventually full size-three matrix space containing an invertible matrix
has full seventh power. -/
theorem invertible_pow_seven_eq_top
    (L : Submodule K Mat) (A : Matˣ) (hA : (A : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) : L ^ 7 = ⊤ := by
  by_contra hseven
  obtain ⟨u, v, hL, _, h0, h1, h2⟩ :=
    second_rank_one_return_of_pow_seven_ne_top L A hA hfull hseven
  obtain ⟨x, y, hrel⟩ := third_power_eq (A : Mat)
  by_cases hxy : x ≠ 0 ∨ y ≠ 0
  · have hdim := six_le_finrank_four_of_second_return L A u v hL hfull h0 h1 h2 hrel hxy
    exact hseven (pow_eq_top_of_finrank_add_le L A hA hfull (j := 4) (t := 3) (by decide)
      (by rw [finrank_matrix_three]; omega))
  · have hx : x = 0 := by by_contra hx; exact hxy (Or.inl hx)
    have hy : y = 0 := by by_contra hy; exact hxy (Or.inr hy)
    have hcube : (A : Mat) ^ 3 = (A : Mat).det • (1 : Mat) := by
      simpa [hx, hy] using hrel
    obtain ⟨m, _, hm⟩ := hfull
    exact pow_ne_top_of_periodic_second_return L A u v hL h0 h1 h2 hcube m hm

end OmegaMath.HomogeneousWordPowers
