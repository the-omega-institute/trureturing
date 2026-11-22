/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian coefficient kernels of a rectangular stack of four matrices. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

/-! Spectral dimension bounds and Schur complement identities for four coefficient directions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Module Unitary
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel

open NativeRectangularBound (stackK)
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening (mix mix_apply)

/-- Compression of a coefficient matrix to the vertically stacked left factors. -/
def compression {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin b) (Fin b) ℂ :=
  (stackK X)ᴴ * kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X

theorem compression_star {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 4) (Fin 4) ℂ) : compression X Tᴴ = (compression X T)ᴴ := by
  simp only [compression, Matrix.kronecker, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem compression_add {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (T U : Matrix (Fin 4) (Fin 4) ℂ) :
    compression X (T + U) = compression X T + compression X U := by
  simp only [compression, Matrix.kronecker, Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

private theorem compression_smul {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (z : ℂ) (T : Matrix (Fin 4) (Fin 4) ℂ) :
    compression X (z • T) = z • compression X T := by
  simp only [compression, Matrix.smul_kronecker, Matrix.mul_smul, Matrix.smul_mul]

private theorem stack_mix {a b : ℕ} (B : Matrix (Fin 4) (Fin 4) ℂ)
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) :
    stackK (mix B X) = kronecker B (1 : Matrix (Fin a) (Fin a) ℂ) * stackK X := by
  classical
  ext ⟨r, i⟩ j
  simp [stackK, mix_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]

private theorem compression_mix {a b : ℕ} (B : Matrix (Fin 4) (Fin 4) ℂ)
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (T : Matrix (Fin 4) (Fin 4) ℂ) :
    compression (mix B X) T = compression X (Bᴴ * T * B) := by
  let I : Matrix (Fin a) (Fin a) ℂ := 1
  have hstar : (kronecker B I)ᴴ = kronecker Bᴴ I := by
    rw [Matrix.conjTranspose_kronecker]
    simp [I]
  simp only [compression, stack_mix, Matrix.conjTranspose_mul]
  change (stackK X)ᴴ * (kronecker B I)ᴴ * kronecker T I * (kronecker B I * stackK X) =
    (stackK X)ᴴ * kronecker (Bᴴ * T * B) I * stackK X
  rw [hstar]
  have hprod : kronecker Bᴴ I * kronecker T I * kronecker B I =
      kronecker (Bᴴ * T * B) I := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp [I]
  rw [← hprod]
  simp only [Matrix.mul_assoc]

private theorem diagonal_energy {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (e : Fin 4 → ℝ) (x : Fin b → ℂ)
    (h : compression X (diagonal (fun i => (e i : ℂ))) = 0) :
    ∑ i, (e i : ℂ) * (star (X i *ᵥ x) ⬝ᵥ (X i *ᵥ x)) = 0 := by
  have he := congrArg (fun A : Matrix (Fin b) (Fin b) ℂ => star x ⬝ᵥ (A *ᵥ x)) h
  rw [compression, NativeRectangularBound.stackK_compression] at he
  simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.cross_pairing, Matrix.diagonal_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Matrix.zero_mulVec, dotProduct_zero] at he
  exact he

private theorem nonpositive_stack_bound {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stackK X).mulVecLin)
    (e : Fin 4 → ℝ) (h : compression X (diagonal (fun i => (e i : ℂ))) = 0) :
    b ≤ Fintype.card {i // e i ≤ 0} * a := by
  classical
  let A : Matrix ({i // e i ≤ 0} × Fin a) (Fin b) ℂ := fun p j => X p.1.val p.2 j
  have hA : Function.Injective A.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change A *ᵥ x = 0 at hx
    have hnonpos (i : Fin 4) (hi : e i ≤ 0) : X i *ᵥ x = 0 := by
      ext p
      exact congrFun hx (⟨i, hi⟩, p)
    have hnonneg (i : Fin 4) : 0 ≤ (e i : ℂ) * (star (X i *ᵥ x) ⬝ᵥ (X i *ᵥ x)) := by
      by_cases hi : e i ≤ 0
      · simp [hnonpos i hi]
      · exact mul_nonneg (by exact_mod_cast (le_of_not_ge hi))
          (dotProduct_star_self_nonneg _)
    have hz := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)
    have hall (i : Fin 4) : X i *ᵥ x = 0 := by
      by_cases hi : e i ≤ 0
      · exact hnonpos i hi
      · exact dotProduct_star_self_eq_zero.mp
          ((mul_eq_zero.mp (hz.mp (diagonal_energy X e x h) i (Finset.mem_univ i))).resolve_left
            (Complex.ofReal_ne_zero.mpr (lt_of_not_ge hi).ne'))
    apply hinj
    ext ⟨i, p⟩
    change (X i *ᵥ x) p = (stackK X).mulVecLin 0 (i, p)
    rw [hall i, map_zero]
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_prod] using
    (LinearMap.finrank_le_finrank_of_injective hA)

private theorem eigenvalue_bound {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stackK X).mulVecLin)
    (T : Matrix (Fin 4) (Fin 4) ℂ) (hT : T.IsHermitian) (h : compression X T = 0) :
    b ≤ Fintype.card {i // hT.eigenvalues i ≤ 0} * a ∧
    b ≤ Fintype.card {i // 0 ≤ hT.eigenvalues i} * a := by
  classical
  let U : Matrix (Fin 4) (Fin 4) ℂ := hT.eigenvectorUnitary
  let E : Matrix (Fin 4) (Fin 4) ℂ := diagonal (fun i => (hT.eigenvalues i : ℂ))
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hT.eigenvectorUnitary
  have hT' : U * E * Uᴴ = T := by
    simpa [U, E, Matrix.IsHermitian.spectral_theorem, conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose] using hT.spectral_theorem.symm
  let Y := mix Uᴴ X
  have hY : Function.Injective (stackK Y).mulVecLin := by
    intro x y he
    apply hinj
    have he' := congrArg (fun u => kronecker U (1 : Matrix (Fin a) (Fin a) ℂ) *ᵥ u) he
    change kronecker U (1 : Matrix (Fin a) (Fin a) ℂ) *ᵥ (stackK Y *ᵥ x) =
      kronecker U (1 : Matrix (Fin a) (Fin a) ℂ) *ᵥ (stackK Y *ᵥ y) at he'
    simp only [Y, stack_mix, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.kronecker, ← Matrix.mul_kronecker_mul, hU, Matrix.one_mul,
      Matrix.one_kronecker_one, Matrix.one_mul] at he'
    exact he'
  have hE : compression Y E = 0 := by
    rw [Y, compression_mix, Matrix.conjTranspose_conjTranspose, hT', h]
  have hE' : compression Y (diagonal (fun i => ((-hT.eigenvalues i : ℝ) : ℂ))) = 0 := by
    rw [show diagonal (fun i => ((-hT.eigenvalues i : ℝ) : ℂ)) = (-1 : ℂ) • E by
      ext i j; simp [E, Matrix.diagonal_apply]]
    rw [compression_smul, hE, smul_zero]
  exact ⟨nonpositive_stack_bound Y hY hT.eigenvalues hE,
    by simpa using nonpositive_stack_bound Y hY (fun i => -hT.eigenvalues i) hE'⟩

private def corner (i : Fin 2) : Fin 4 := i.succ.succ

private def principal (i : Fin 2) : Fin 3 → Fin 4 := ![0, 1, corner i]

private theorem minor_det_zero (T : Matrix (Fin 4) (Fin 4) ℂ) (hT : T.rank ≤ 2)
    (i j : Fin 2) : (T.submatrix (principal i) (principal j)).det = 0 := by
  by_contra hn
  have hr := (Matrix.rank_submatrix_le T (principal i) (principal j)).trans hT
  rw [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin] at hr
  omega

private def signature : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1, -1, 0, 0]

private def topRow (T : Matrix (Fin 4) (Fin 4) ℂ) (r : Fin 2) (i : Fin 2) : ℂ :=
  T (Fin.castLE (by decide : 2 ≤ 4) r) (corner i)

private theorem hermitian_entry {T : Matrix (Fin 4) (Fin 4) ℂ} (hT : T.IsHermitian)
    (i j : Fin 4) : T i j = star (T j i) := by
  exact (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) hT.eq).symm

/-- The constant and linear terms of the Schur expression are read off from the
three-by-three minors at the two pencils with parameters one and minus one. -/
private theorem schur_entries (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hT : T.IsHermitian) (h : T.rank ≤ 2)
    (hp : (signature + T).rank ≤ 2) (hm : (signature - T).rank ≤ 2)
    (i j : Fin 2) :
    T (corner i) (corner j) = 0 ∧
      star (topRow T 0 i) * topRow T 0 j = star (topRow T 1 i) * topRow T 1 j := by
  have h0 := minor_det_zero T h i j
  have h₊ := minor_det_zero _ hp i j
  have h₋ := minor_det_zero _ hm i j
  have hi₀ : corner i ≠ 0 := by exact ne_of_gt (by simp [corner])
  have hi₁ : corner i ≠ 1 := by exact ne_of_gt (by simp [corner])
  have hj₀ : corner j ≠ 0 := by exact ne_of_gt (by simp [corner])
  have hj₁ : corner j ≠ 1 := by exact ne_of_gt (by simp [corner])
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, principal,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.add_apply, Matrix.sub_apply, signature, Matrix.diagonal_apply,
    hi₀, hi₁, hj₀, hj₁, Ne.symm hi₀, Ne.symm hi₁, Ne.symm hj₀, Ne.symm hj₁,
    ite_false] at h0 h₊ h₋
  have hs (r : Fin 2) : ![(1 : ℂ), -1, 0, 0] (corner r) = 0 := by
    fin_cases r <;> rfl
  simp [hs] at h₊ h₋
  have hC : T (corner i) (corner j) = 0 := by
    linear_combination -(h₊ - h₋) / 2 + h0
  refine ⟨hC, ?_⟩
  change star (T 0 (corner i)) * T 0 (corner j) =
      star (T 1 (corner i)) * T 1 (corner j)
  rw [← hermitian_entry hT (corner i) 0, ← hermitian_entry hT (corner i) 1]
  simp only [hC, mul_zero, zero_mul, sub_zero, zero_add, add_zero] at h₊ h₋
  linear_combination (h₊ + h₋) / 2

private theorem slope_of_row_gram (u v : Fin 2 → ℂ)
    (h : ∀ i j, star (u i) * u j = star (v i) * v j) :
    (u = 0 ∧ v = 0) ∨ ∃ z : ℂ, star z * z = 1 ∧ v = z • u := by
  classical
  by_cases hu : u = 0
  · refine Or.inl ⟨hu, ?_⟩
    ext j
    have h₀ := (h j j).symm
    rw [hu] at h₀
    simpa [mul_eq_zero] using h₀
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra! hh
      exact hu (funext hh)
    have hvi : v i ≠ 0 := by
      intro hv
      exact (mul_ne_zero (by simpa using hi) hi) (by simpa [hv] using h i i)
    have hsv : star (v i) ≠ 0 := by simpa using hvi
    let z := star (u i) / star (v i)
    have hrow : v = z • u := by
      ext j
      change v j = z * u j
      apply (eq_div_iff hsv).mpr
      simpa only [z, div_mul_eq_mul_div, mul_comm] using (h i j).symm
    have hi' := h i i
    rw [hrow] at hi'
    simp only [Pi.smul_apply, smul_eq_mul, star_mul] at hi'
    have hn := mul_ne_zero (show star (u i) ≠ 0 by simpa using hi) hi
    refine Or.inr ⟨z, ?_, hrow⟩
    apply mul_right_cancel₀ hn
    calc
      _ = star (z * u i) * (z * u i) := by simp only [star_mul]; ring
      _ = _ := by rw [← hi', one_mul]

private def detRows (u v : Fin 2 → ℂ) : ℂ := u 0 * v 1 - u 1 * v 0

private theorem row_det_zero (u v : Fin 2 → ℂ)
    (h : (u = 0 ∧ v = 0) ∨ ∃ z : ℂ, star z * z = 1 ∧ v = z • u) :
    detRows u v = 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨z, _, rfl⟩
  · simp [detRows]
  · simp only [detRows, Pi.smul_apply, smul_eq_mul]
    ring

private theorem slope_equal (u u' : Fin 2 → ℂ) (z z' : ℂ)
    (hdet : detRows u u' ≠ 0)
    (h : detRows (u + u') (z • u + z' • u') = 0) : z = z' := by
  have hmul : (z' - z) * detRows u u' = 0 := by
    convert h using 1
    simp only [detRows, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hdet)).symm

private theorem row_geometry (K : AddSubgroup (Matrix (Fin 4) (Fin 4) ℂ))
    (hJ : signature ∈ K) (hHerm : ∀ T ∈ K, T.IsHermitian)
    (hRank : ∀ T ∈ K, T.rank ≤ 2) :
    (∃ v : Fin 4 → ℂ, v ≠ 0 ∧ ∀ T ∈ K, T *ᵥ v = 0) ∨
    (∃ E : Matrix (Fin 4) (Fin 3) ℂ, E.rank = 3 ∧ ∀ T ∈ K, Eᴴ * T * E = 0) := by
  classical
  let u (T : Matrix (Fin 4) (Fin 4) ℂ) := topRow T 0
  let v (T : Matrix (Fin 4) (Fin 4) ℂ) := topRow T 1
  have hC (T) (hT : T ∈ K) (i j : Fin 2) : T (corner i) (corner j) = 0 :=
    (schur_entries T (hHerm T hT) (hRank T hT)
      (hRank _ (K.add_mem hJ hT)) (hRank _ (K.sub_mem hJ hT)) i j).1
  have hB (T) (hT : T ∈ K) :
      (u T = 0 ∧ v T = 0) ∨ ∃ z : ℂ, star z * z = 1 ∧ v T = z • u T :=
    slope_of_row_gram (u T) (v T) (fun i j =>
      (schur_entries T (hHerm T hT) (hRank T hT)
        (hRank _ (K.add_mem hJ hT)) (hRank _ (K.sub_mem hJ hT)) i j).2)
  have huv (T) (hT : T ∈ K) (hu : u T = 0) : v T = 0 := by
    rcases hB T hT with h | ⟨z, _, h⟩
    · exact h.2
    · simp [h, hu]
  have hfixed (A B) (hA : A ∈ K) (hB' : B ∈ K)
      (z z' : ℂ) (hz : v A = z • u A) (hz' : v B = z' • u B)
      (hab : detRows (u A) (u B) ≠ 0) : z = z' := by
    have h := row_det_zero _ _ (hB (A + B) (K.add_mem hA hB'))
    change detRows (u A + u B) (v A + v B) = 0 at h
    exact slope_equal _ _ z z' hab (by simpa [hz, hz'] using h)
  by_cases hind : ∃ A ∈ K, ∃ B ∈ K, detRows (u A) (u B) ≠ 0
  · obtain ⟨A, hA, B, hB', hAB⟩ := hind
    have huA : u A ≠ 0 := by intro h; exact hAB (by simp [h, detRows])
    have huB : u B ≠ 0 := by intro h; exact hAB (by simp [h, detRows])
    have hslope (T) (hT : T ∈ K) (huT : u T ≠ 0) : ∃ z : ℂ, v T = z • u T := by
      rcases hB T hT with h | ⟨z, _, h⟩
      · exact (huT h.1).elim
      · exact ⟨z, h⟩
    obtain ⟨z, hz⟩ := hslope A hA huA
    obtain ⟨z', hz'⟩ := hslope B hB' huB
    have heq := hfixed A B hA hB' z z' hz hz' hAB
    subst z'
    have hall (T) (hT : T ∈ K) : v T = z • u T := by
      by_cases huT : u T = 0
      · simp [huT, huv T hT huT]
      obtain ⟨w, hw⟩ := hslope T hT huT
      by_cases hAT : detRows (u A) (u T) = 0
      · have hBT : detRows (u B) (u T) ≠ 0 := by
          intro h
          have h0 : detRows (u A) (u B) * u T 0 = 0 := by
            dsimp only [detRows] at *
            linear_combination u B 0 * hAT - u A 0 * h
          have h1 : detRows (u A) (u B) * u T 1 = 0 := by
            dsimp only [detRows] at *
            linear_combination u B 1 * hAT - u A 1 * h
          apply huT
          ext i
          fin_cases i
          · exact (mul_eq_zero.mp h0).resolve_left hAB
          · exact (mul_eq_zero.mp h1).resolve_left hAB
        rwa [hfixed B T hB' hT z w hz' hw hBT]
      · rwa [hfixed A T hA hT z w hz hw hAT]
    right
    let E : Matrix (Fin 4) (Fin 3) ℂ := !![-star z, 0, 0; 1, 0, 0; 0, 1, 0; 0, 0, 1]
    have hEr : E.rank = 3 := by
      have hsub : E.submatrix Fin.succ id = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have hlow := Matrix.rank_submatrix_le E Fin.succ id
      rw [hsub, Matrix.rank_one, Fintype.card_fin] at hlow
      exact le_antisymm (by simpa using E.rank_le_card_width) hlow
    refine ⟨E, hEr, ?_⟩
    let q (T : Matrix (Fin 4) (Fin 4) ℂ) :=
      (z * star z) * T 0 0 - z * T 0 1 - star z * T 1 0 + T 1 1
    have hq_nonzero (T) (hT : T ∈ K) (huT : u T ≠ 0) : q T = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, u T i ≠ 0 := by
        by_contra! h; exact huT (funext h)
      have hvT := congrFun (hall T hT) i
      change T 1 (corner i) = z * T 0 (corner i) at hvT
      have h := minor_det_zero T (hRank T hT) i i
      simp only [Matrix.det_fin_three, Matrix.submatrix_apply, principal,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
      rw [hC T hT i i, hermitian_entry (hHerm T hT) (corner i) 0,
        hermitian_entry (hHerm T hT) (corner i) 1, hvT, star_mul] at h
      have hh : (star (u T i) * u T i) * q T = 0 := by
        dsimp [q, u, topRow]
        linear_combination -h
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by simpa using hi) hi)
    have hq (T) (hT : T ∈ K) : q T = 0 := by
      by_cases huT : u T = 0
      · have hu : u (T + A) ≠ 0 := by
          change u T + u A ≠ 0
          simpa [huT] using huA
        have h := hq_nonzero _ (K.add_mem hT hA) hu
        have h' := hq_nonzero _ hA huA
        dsimp [q] at h h' ⊢
        simp only [Matrix.add_apply] at h
        linear_combination h - h'
      · exact hq_nonzero T hT huT
    intro T hT
    have hc₀₀ := hC T hT 0 0
    have hc₀₁ := hC T hT 0 1
    have hc₁₀ := hC T hT 1 0
    have hc₁₁ := hC T hT 1 1
    have hv₀ := congrFun (hall T hT) 0
    have hv₁ := congrFun (hall T hT) 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [E, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.zero_apply, star_zero, star_one, star_neg, star_star,
        zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add] <;>
      first
      | exact hc₀₀
      | exact hc₀₁
      | exact hc₁₀
      | exact hc₁₁
      | simpa [u, v, topRow, corner] using hv₀
      | simpa [u, v, topRow, corner] using hv₁
      | linear_combination (hq T hT)
      | rw [hermitian_entry (hHerm T hT) 2 0, hermitian_entry (hHerm T hT) 2 1]
        have h := congrArg star hv₀
        simp only [u, v, topRow, corner, Pi.smul_apply, smul_eq_mul, star_mul] at h
        linear_combination h
      | rw [hermitian_entry (hHerm T hT) 3 0, hermitian_entry (hHerm T hT) 3 1]
        have h := congrArg star hv₁
        simp only [u, v, topRow, corner, Pi.smul_apply, smul_eq_mul, star_mul] at h
        linear_combination h
  · left
    by_cases hzero : ∀ T ∈ K, u T = 0
    · refine ⟨![0, 0, 1, 0], by simp, ?_⟩
      intro T hT
      have h₀ := congrFun (hzero T hT) 0
      have h₁ := congrFun (huv T hT (hzero T hT)) 0
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
        first | exact h₀ | exact h₁ | exact hC T hT 0 0 | exact hC T hT 1 0
    push_neg at hzero
    obtain ⟨A, hA, huA⟩ := hzero
    let w : Fin 4 → ℂ := ![0, 0, -(u A 1), u A 0]
    have hw : w ≠ 0 := by
      intro h
      have h₀ := congrFun h 3
      have h₁ := congrFun h 2
      apply huA
      ext i
      fin_cases i <;> simpa [w] using h₀ <;> simpa [w] using h₁
    refine ⟨w, hw, ?_⟩
    intro T hT
    have hdet : detRows (u A) (u T) = 0 := by
      by_contra h
      exact hind ⟨A, hA, T, hT, h⟩
    have hdet' : detRows (u A) (v T) = 0 := by
      rcases hB T hT with ⟨_, h⟩ | ⟨z, _, h⟩
      · simp [h, detRows]
      · rw [h]
        simp only [detRows, Pi.smul_apply, smul_eq_mul] at hdet ⊢
        linear_combination z * hdet
    ext i
    fin_cases i <;>
      simp only [Matrix.mulVec, dotProduct, w, Fin.sum_univ_four, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        mul_zero, zero_add, Pi.zero_apply]
    · dsimp [detRows, u, topRow, corner] at hdet
      linear_combination hdet
    · dsimp [detRows, v, topRow, corner] at hdet'
      linear_combination hdet'
    · rw [show T 2 2 = 0 from hC T hT 0 0, show T 2 3 = 0 from hC T hT 0 1]
      simp
    · rw [show T 3 2 = 0 from hC T hT 1 0, show T 3 3 = 0 from hC T hT 1 1]
      simp

private theorem positive_card_bound {a b : ℕ} (e : Fin 4 → ℝ) (k : ℕ)
    (hk : k ≤ 4) (hb : k * a < b)
    (h : b ≤ Fintype.card {i // e i ≤ 0} * a) :
    Fintype.card {i // 0 < e i} < 4 - k := by
  classical
  have hcard : k < Fintype.card {i // e i ≤ 0} := by
    by_contra! hle
    exact (not_le_of_gt hb) (h.trans (Nat.mul_le_mul_right a hle))
  have hc := Fintype.card_subtype_compl (fun i => e i ≤ 0)
  simp only [Fintype.card_fin, not_le] at hc
  omega

/-- The sign subspaces bound the rank of a Hermitian form with zero compression. -/
theorem hermitian_rank_bound {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stackK X).mulVecLin) (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hT : T.IsHermitian) (h : compression X T = 0) (k : ℕ) (hk : k ≤ 3)
    (hb : k * a < b) : T.rank < 2 * (4 - k) - 1 := by
  classical
  obtain ⟨hp, hn⟩ := eigenvalue_bound X hinj T hT h
  have hpos := positive_card_bound hT.eigenvalues k (by omega) hb hp
  have hneg := positive_card_bound (fun i => -hT.eigenvalues i) k (by omega) hb
    (by simpa using hn)
  let f : {i // hT.eigenvalues i ≠ 0} →
      {i // 0 < hT.eigenvalues i} ⊕ {i // 0 < -hT.eigenvalues i} :=
    fun i => if h : 0 < hT.eigenvalues i then Sum.inl ⟨i, h⟩ else
      Sum.inr ⟨i, by have := i.property; exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) this)⟩
  have hf : Function.Injective f := by
    let g : {i // 0 < hT.eigenvalues i} ⊕ {i // 0 < -hT.eigenvalues i} → Fin 4 :=
      Sum.elim Subtype.val Subtype.val
    intro i j hij
    apply Subtype.ext
    have he (r : {i // hT.eigenvalues i ≠ 0}) : g (f r) = r := by
      dsimp [f]
      split_ifs <;> rfl
    simpa only [he] using congrArg g hij
  have hr := Fintype.card_le_of_injective f hf
  rw [← hT.rank_eq_card_non_zero_eigs, Fintype.card_sum] at hr
  omega

private theorem no_semidefinite {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (hX : LinearIndependent ℂ X) (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hT : T.PosSemidef) (h : compression X T = 0) : T = 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT.nonneg
  change T = Bᴴ * B at hB
  have H := compression_mix B X 1
  rw [Matrix.mul_one, ← hB, h] at H
  have hs : stackK (mix B X) = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa [compression, Matrix.one_kronecker_one] using H
  have hzero (r : Fin 4) : ∑ s, B r s • X s = 0 := by
    change mix B X r = 0
    ext i j
    exact congrArg (fun S : Matrix (Fin 4 × Fin a) (Fin b) ℂ => S (r, i) j) hs
  have hB0 : B = 0 := by
    ext r s
    exact Fintype.linearIndependent_iff.mp hX (B r) (hzero r) s
  rw [hB, hB0]
  simp

private theorem kernel_signature {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (hX : LinearIndependent ℂ X) (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hT : T.IsHermitian) (h : compression X T = 0) (hnz : T ≠ 0) (hr : T.rank ≤ 2) :
    ∃ M : Matrix (Fin 4) (Fin 4) ℂ, IsUnit M ∧ Mᴴ * T * M = signature := by
  classical
  let e := hT.eigenvalues
  let U : Matrix (Fin 4) (Fin 4) ℂ := hT.eigenvectorUnitary
  have hU : IsUnit U := Unitary.isUnit_coe
  have hdiag : Uᴴ * T * U = diagonal (fun i => (e i : ℂ)) := by
    simpa [U, e, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hT.conjStarAlgAut_star_eigenvectorUnitary
  obtain ⟨i, hi⟩ : ∃ i, 0 < e i := by
    by_contra! hnone
    have hN : (-T).PosSemidef := by
      have hD : (diagonal (fun i => ((-e i : ℝ) : ℂ))).PosSemidef := by
        apply Matrix.posSemidef_diagonal_iff.mpr
        intro i
        exact_mod_cast neg_nonneg.mpr (hnone i)
      have hnegdiag : Uᴴ * (-T) * U = diagonal (fun i => ((-e i : ℝ) : ℂ)) := by
        rw [Matrix.mul_neg, Matrix.neg_mul, hdiag]
        ext i j
        simp [Matrix.diagonal_apply]
      rw [← hnegdiag] at hD
      have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hT.eigenvectorUnitary
      have hh := hD.conjTranspose_mul_mul_same Uᴴ
      simpa only [Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hUU,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_one] using hh
    have hn : compression X (-T) = 0 := by
      rw [← neg_one_smul ℂ T, compression_smul, h, smul_zero]
    exact hnz (neg_eq_zero.mp (no_semidefinite X hX (-T) hN hn))
  obtain ⟨j, hj⟩ : ∃ j, e j < 0 := by
    by_contra! hnone
    exact hnz (no_semidefinite X hX T (hT.posSemidef_iff_eigenvalues_nonneg.mpr hnone) h)
  have hij : i ≠ j := by rintro rfl; linarith
  let s := Equiv.swap 0 i
  let t := Equiv.swap 1 (s j)
  let p := t.trans s
  have hsj : s j ≠ 0 := by
    intro he
    have hj' := congrArg s he
    simp [s] at hj'
    exact hij hj'.symm
  have hp0 : p 0 = i := by
    simp [p, t, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) hsj.symm, s]
  have hp1 : p 1 = j := by simp [p, t, s]
  have hrest (r : Fin 4) (h0 : r ≠ 0) (h1 : r ≠ 1) : e (p r) = 0 := by
    by_contra hne
    let q : Fin 3 → {m // e m ≠ 0} := ![⟨i, hi.ne'⟩, ⟨j, hj.ne⟩, ⟨p r, hne⟩]
    have hr0 : p r ≠ i := by rw [← hp0]; exact fun h => h0 (p.injective h)
    have hr1 : p r ≠ j := by rw [← hp1]; exact fun h => h1 (p.injective h)
    have hq : Function.Injective q := by
      intro x y he
      have hh := congrArg Subtype.val he
      fin_cases x <;> fin_cases y <;> simp_all [q]
    have hc := Fintype.card_le_of_injective q hq
    rw [Fintype.card_fin, ← hT.rank_eq_card_non_zero_eigs] at hc
    omega
  let P : Matrix (Fin 4) (Fin 4) ℂ := (1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix id p
  have hPP : Pᴴ * P = 1 := by
    simp [P, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_one_equiv]
  have hP : IsUnit P := isUnit_iff_exists_inv'.mpr ⟨Pᴴ, hPP⟩
  let w : Fin 4 → ℝ := ![(Real.sqrt (e i))⁻¹, (Real.sqrt (-e j))⁻¹, 1, 1]
  let D := diagonal (fun r => (w r : ℂ))
  have hD : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    fin_cases r <;> simp [w, (Real.sqrt_pos.2 hi).ne', (Real.sqrt_pos.2 (neg_pos.mpr hj)).ne']
  refine ⟨U * P * D, (hU.mul hP).mul hD, ?_⟩
  have hD' : Dᴴ = D := by
    ext r s
    simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  have hperm : Pᴴ * diagonal (fun r => (e r : ℂ)) * P =
      diagonal (fun r => (e (p r) : ℂ)) := by
    simp [P, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_diagonal, Function.comp_def]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD']
  calc
    _ = D * (Pᴴ * (Uᴴ * T * U) * P) * D := by simp only [Matrix.mul_assoc]
    _ = signature := by
      rw [hdiag, hperm, D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext r
      fin_cases r
      · simp [w, hp0, signature]
        have h := Real.sq_sqrt hi.le
        field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hi).ne']
        exact_mod_cast h.symm
      · simp [w, hp1, signature]
        have h := Real.sq_sqrt (neg_nonneg.mpr hj.le)
        field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (neg_pos.mpr hj)).ne']
        exact_mod_cast (by linarith : e j = -(Real.sqrt (-e j)) ^ 2)
      · simp [w, signature, hrest 2 (by decide) (by decide)]
      · simp [w, signature, hrest 3 (by decide) (by decide)]

/-- The Hermitian kernel is zero, has a common kernel line, or has a neutral three-space. -/
theorem coefficient_geometry {a b : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (h : ∀ T, T.IsHermitian → compression X T = 0 → T.rank ≤ 2) :
    (∀ T, T.IsHermitian → compression X T = 0 → T = 0) ∨
    (∃ v : Fin 4 → ℂ, v ≠ 0 ∧ ∀ T, T.IsHermitian → compression X T = 0 → T *ᵥ v = 0) ∨
    (∃ E : Matrix (Fin 4) (Fin 3) ℂ, E.rank = 3 ∧
      ∀ T, T.IsHermitian → compression X T = 0 → Eᴴ * T * E = 0) := by
  classical
  by_cases hz : ∀ T, T.IsHermitian → compression X T = 0 → T = 0
  · exact Or.inl hz
  push_neg at hz
  obtain ⟨T, hT, hXT, hT0⟩ := hz
  obtain ⟨M, hM, hJ⟩ := kernel_signature X hX T hT hXT hT0 (h T hT hXT)
  let K : AddSubgroup (Matrix (Fin 4) (Fin 4) ℂ) :=
    { carrier := {S | S.IsHermitian ∧ compression X S = 0}
      zero_mem' := by simp [compression, Matrix.zero_kronecker, Matrix.IsHermitian]
      add_mem' := by
        rintro S U ⟨hh, hc⟩ ⟨hh', hc'⟩
        exact ⟨hh.add hh', by rw [compression_add, hc, hc', add_zero]⟩
      neg_mem' := by
        rintro S ⟨hh, hc⟩
        exact ⟨hh.neg, by rw [← neg_one_smul ℂ S, compression_smul, hc, smul_zero]⟩ }
  let f : Matrix (Fin 4) (Fin 4) ℂ →+ Matrix (Fin 4) (Fin 4) ℂ :=
    { toFun := fun S => Mᴴ * S * M
      map_zero' := by simp
      map_add' := by intro S U; simp [Matrix.mul_add, Matrix.add_mul] }
  have hJ' : signature ∈ K.map f := ⟨T, ⟨hT, hXT⟩, hJ⟩
  have hH (S) (hS : S ∈ K.map f) : S.IsHermitian := by
    rcases hS with ⟨S, ⟨hh, _⟩, rfl⟩
    change (Mᴴ * S * M)ᴴ = Mᴴ * S * M
    simp [Matrix.conjTranspose_mul, hh.eq, Matrix.mul_assoc]
  have hR (S) (hS : S ∈ K.map f) : S.rank ≤ 2 := by
    rcases hS with ⟨S, ⟨hh, hc⟩, rfl⟩
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans (h S hh hc))
  apply Or.inr
  rcases row_geometry (K.map f) hJ' hH hR with ⟨v, hv, hker⟩ | ⟨E, hE, hneutral⟩
  · left
    have hMi := Matrix.mulVec_injective_iff_isUnit.mpr hM
    have hMstar : IsUnit Mᴴ := hM.star
    have hMstarI := Matrix.mulVec_injective_iff_isUnit.mpr hMstar
    refine ⟨M *ᵥ v, fun hv' => hv (hMi (hv'.trans (Matrix.mulVec_zero M).symm)), ?_⟩
    intro S hS hXS
    have he := hker (f S) ⟨S, ⟨hS, hXS⟩, rfl⟩
    apply hMstarI
    simpa only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_zero] using he
  · right
    refine ⟨M * E, ?_, ?_⟩
    · rw [Matrix.rank_mul_eq_right_of_isUnit_det M E
        ((Matrix.isUnit_iff_isUnit_det _).mp hM), hE]
    · intro S hS hXS
      have he := hneutral (f S) ⟨S, ⟨hS, hXS⟩, rfl⟩
      simpa [f, Matrix.conjTranspose_mul, Matrix.mul_assoc] using he


end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
